/-
Copyright (c) 2021-2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

module

public import Lean.Meta.Tactic.Simp
public meta import Lean.Meta.Tactic.Simp
public import Smt.Preprocess.Basic
public meta import Smt.Preprocess.Basic
public import Smt.Preprocess.Embedding.Attribute
public meta import Smt.Preprocess.Embedding.Attribute
public import Smt.Preprocess.Embedding.Nat

public meta section

private def Lean.Expr.contains (e : Expr) (p : Expr → Bool) : Bool :=
  (e.find? p).isSome

namespace Smt.Preprocess

open Lean

def hasType (e : Expr) (p : Expr → Bool) : Bool :=
  match e with
  | .forallE _ t b _ => p t || hasType b p
  | _                => p e

def hasReturnType (e : Expr) (p : Expr → Bool) : Bool :=
  match e with
  | .forallE _ _ b _ => hasReturnType b p
  | _                => p e

/-- The facts about `Nat.toInt` and `Nat.fromInt` that the solver needs to reason about `Nat`.
See `Smt/Preprocess/Embedding/Nat.lean`. -/
def natFacts : Array Name := #[
  ``Nat.toInt_nonneg, ``Nat.toInt_fromInt_of_nonneg, ``Nat.fromInt_toInt, ``Nat.toInt_fromInt_of_nonpos
]

def usesNatCasts (e : Expr) : Bool :=
  e.contains fun
    | .const ``Nat.toInt _ | .const ``Nat.fromInt _ => true
    | _                                             => false

def embedding (mv : MVarId) (hs : Array Expr) : MetaM Result := mv.withContext do
  -- Find all free vars to revert in `hs` and `mv`. The type of the negated goal mentions the
  -- assigned metavariable of `Classical.byContradiction` unless a previous step instantiated it.
  let ts ← hs.mapM (Meta.inferType · >>= instantiateMVars)
  let ⟨_, _, fvs⟩ := (ts.push (← instantiateMVars (← mv.getType))).foldl Lean.collectFVars {}
  let fvs ← Meta.sortFVarIds fvs
  -- Check if we need to do anything. Casts between `Nat` and `Int` do not mention `Nat` itself.
  let bts := #[``Nat, ``Nat.cast, ``Int.toNat, ``Bool] ++
    if (← getEnv).contains `Real then #[``Rat] else #[]
  let fvts ← fvs.mapM FVarId.getType
  let isEmbedded (e : Expr) := e.isConst && bts.contains e.constName!
  if !(fvts ++ ts.push (← mv.getType)).any (·.contains isEmbedded) then
    return ⟨{}, hs, mv⟩
  -- Find the embedding simp theorems.
  let some thmsExt ← Meta.getSimpExtension? `embedding | throwError "embedding simp extension not found"
  let some procsExt ← Meta.Simp.getSimprocExtension? `embedding | throwError "embedding simproc extension not found"
  let simpTheorems := #[← thmsExt.getTheorems]
  let simpProcs := #[← procsExt.getSimprocs]
  -- Assert all hypotheses that are not free vars.
  let (hs₁, hs₂) := hs.partition Expr.isFVar
  let ts₂ ← hs₂.mapM Meta.inferType
  let as₂ : Array Meta.Hypothesis := (hs₂.zip ts₂).map fun (h, t) => { userName := .anonymous, type := t, value := h }
  let (fvs₂, mv) ← mv.assertHypotheses as₂
  -- Build map from new hypotheses to old ones.
  let inverseMap₁ : Std.HashMap Expr Expr := hs.foldl (init := {}) fun map h =>
    match hs₂.findIdx? (· == h) with
    | some idx => map.insert h (.fvar fvs₂[idx]!)
    | none => map.insert h h
  -- Revert free vars in `hs` and `mv`.
  let fvs := fvs ++ hs₁.map Expr.fvarId! ++ fvs₂
  let (fvs, mv) ← mv.revert fvs true
  -- Simplify the goal using the embedding theorems.
  let congrTheorems ← Meta.getSimpCongrTheorems
  let ctx ← Meta.Simp.mkContext { zeta := false, singlePass := true } simpTheorems congrTheorems
  let (some mv, _) ← Meta.simpTarget mv ctx simpProcs (mayCloseGoal := false) | throwError "[embedding] simplification failed"
  -- Extend `fvs` to account for the assumptions of `Rat` variables. `Nat` and `Bool` variables keep
  -- their types, so they have no assumptions.
  let ats := if (← getEnv).contains `Real then #[``Rat] else #[]
  let mut fvs' : Array (Option FVarId) := #[]
  for fv in fvs do
    fvs' := fvs'.push (some fv)
    let t ← fv.getType
    if hasReturnType t ((ats.map (.const · [])).contains ·) then
      fvs' := fvs'.push none
  -- Re-introduce all free vars (and their assumptions).
  let (fvs'', mv) ← mv.introNP fvs'.size
  -- Compose the final map from new free vars to old ones.
  -- We do not need to map assumptions. Since assumptions are auxiliary, we can always provide all
  -- of them to the SMT solver without affecting the unsat core.
  let (inverseMap₂, hs') := (fvs'.zip fvs'').foldl (init := ({}, #[])) fun (map, hs') (of, to) =>
    match of with
    | some of => (map.insert (.fvar of) (.fvar to), hs')
    | none    => (map, hs'.push (.fvar to))
  let inverseMap := compose inverseMap₁ inverseMap₂
  let hs' := hs' ++ hs.map fun h => inverseMap[h]?.getD h
  -- Add the facts about the casts between `Nat` and `Int` if the embedded hypotheses use them. Like
  -- the assumptions above, they are auxiliary, so they are not part of the map.
  let (hs', mv) ← mv.withContext do
    if !(← hs'.anyM fun h => return usesNatCasts (← Meta.inferType h)) then
      return (hs', mv)
    let as ← natFacts.mapM fun n => do
      let type ← Meta.inferType (mkConst n)
      return { userName := .mkSimple n.getString!, type, value := mkConst n }
    let (fvs, mv) ← mv.assertHypotheses as
    return (fvs.map Expr.fvar ++ hs', mv)
  let map := (inverse inverseMap).fold (init := {}) fun map k v => map.insert k #[v]
  return { map := map, hs := hs', mv }
where
  compose (m₁ m₂ : Std.HashMap Expr Expr) : Std.HashMap Expr Expr :=
    m₁.fold (init := m₂) fun map k v =>
      map.insert k (map[v]?.getD v)
  inverse (m : Std.HashMap Expr Expr) : Std.HashMap Expr Expr :=
    m.fold (init := {}) fun map k v =>
      map.insert v k

end Smt.Preprocess
