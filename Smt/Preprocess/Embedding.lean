/-
Copyright (c) 2021-2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

module

public import Lean.Meta.Tactic.Rename
public meta import Lean.Meta.Tactic.Rename
public import Lean.Meta.Tactic.Simp
public meta import Lean.Meta.Tactic.Simp
public import Qq
public meta import Qq
public import Smt.Preprocess.Basic
public meta import Smt.Preprocess.Basic
public import Smt.Preprocess.Embedding.Attribute
public meta import Smt.Preprocess.Embedding.Attribute
public import Smt.Preprocess.Embedding.Ite
public meta import Smt.Preprocess.Embedding.Ite
public import Smt.Preprocess.Embedding.Prop
public meta import Smt.Preprocess.Embedding.Prop
public import Smt.Preprocess.Embedding.Sort
public meta import Smt.Preprocess.Embedding.Sort

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

/-- Embed the types that SMT-LIB lacks (e.g., `Nat` and `Prop`) into ones it has (e.g., `Int` and
`Bool`) with the `embedding` theorems, which rewrite the goal after reverting the free variables and
hypotheses `hs`. Type variables in `Sort u` are lifted into `Type u` first (see `liftSorts`). -/
def embedTypes (mv : MVarId) (hs : Array Expr) : MetaM Result := mv.withContext do
  -- Find all free vars to revert in `hs` and `mv`.
  let ts ← hs.mapM Meta.inferType
  let ⟨_, _, fvs⟩ := (ts.push (← mv.getType)).foldl Lean.collectFVars {}
  -- Also revert the type variables in `Sort u` of their types, so that they can be lifted.
  let ⟨_, _, tvs⟩ := (← fvs.mapM FVarId.getType).foldl Lean.collectFVars {}
  let tvs ← tvs.filterM fun fv => return Embedding.isLiftableSort (← fv.getType)
  let fvs ← Meta.sortFVarIds (fvs ++ tvs.filter (!fvs.contains ·))
  -- Check if we need to do anything.
  let bts := if (← getEnv).contains `Real then  #[``Nat, ``Rat] else #[``Nat]
  let fvts ← fvs.mapM FVarId.getType
  let isEmbedded (e : Expr) := e.isProp || (bts.map (.const · [])).contains e
  if !(fvts ++ ts.push (← mv.getType)).any (·.contains isEmbedded) &&
      !fvts.any Embedding.isLiftableSort then
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
  let mv ← Embedding.liftSorts mv
  -- Simplify the goal using the embedding theorems.
  let congrTheorems ← Meta.getSimpCongrTheorems
  let ctx ← Meta.Simp.mkContext { zeta := false, singlePass := true } simpTheorems congrTheorems
  let (some mv, _) ← Meta.simpTarget mv ctx simpProcs (mayCloseGoal := false) | throwError "[embedding] simplification failed"
  -- Extend `fvs` to account for `nonneg` assumptions.
  let mut fvs' : Array (Option FVarId) := #[]
  for fv in fvs do
    fvs' := fvs'.push (some fv)
    let t ← fv.getType
    if hasReturnType t ((bts.map (.const · [])).contains ·) then
      fvs' := fvs'.push none
  -- Re-introduce all free vars (and their `nonneg` assumptions).
  let (fvs'', mv) ← mv.introNP fvs'.size
  -- Keep the names of the free vars, which the embedding theorems may have changed.
  let mut mv := mv
  for (of, to) in fvs'.zip fvs'' do
    if let some of := of then
      if let some d := (← getLCtx).find? of then
        mv ← mv.rename to d.userName
  -- Compose the final map from new free vars to old ones.
  -- We do not need to map `nonneg` assumptions. Since `nonneg` assumptions are auxiliary,
  -- We can always provide all of them to the SMT solver without affecting the unsat core.
  let (inverseMap₂, hs') := (fvs'.zip fvs'').foldl (init := ({}, #[])) fun (map, hs') (of, to) =>
    match of with
    | some of => (map.insert (.fvar of) (.fvar to), hs')
    | none    => (map, hs'.push (.fvar to))
  let inverseMap := compose inverseMap₁ inverseMap₂
  let hs' := hs' ++ hs.map fun h => inverseMap[h]?.getD h
  let map := (inverse inverseMap).fold (init := {}) fun map k v => map.insert k #[v]
  -- The inverse may map a new hypothesis to the intermediate free var asserted for it above; map it
  -- to the hypothesis it comes from instead.
  let map := hs.foldl (init := map) fun map h => map.insert (inverseMap[h]?.getD h) #[h]
  return { map := map, hs := hs', mv }
where
  compose (m₁ m₂ : Std.HashMap Expr Expr) : Std.HashMap Expr Expr :=
    m₁.fold (init := m₂) fun map k v =>
      map.insert k (map[v]?.getD v)
  inverse (m : Std.HashMap Expr Expr) : Std.HashMap Expr Expr :=
    m.fold (init := {}) fun map k v =>
      map.insert v k

open Qq in
/-- Turn every hypothesis `h : p` in `hs` into a hypothesis `h' : b = true`, where `b` is the Boolean
formula obtained from `p` with the `smt_decide` theorems (see `Smt.Preprocess.Embedding.Prop`).
Hypotheses in `hs` that are not proofs (e.g., definitions) are kept as they are. -/
def embedProps (mv : MVarId) (hs : Array Expr) : MetaM Result := do
  let some thmsExt ← Meta.getSimpExtension? `smt_decide | throwError "smt_decide simp extension not found"
  let some procsExt ← Meta.Simp.getSimprocExtension? `smt_decide
    | throwError "smt_decide simproc extension not found"
  let simprocs := #[← procsExt.getSimprocs]
  let ctx ← mv.withContext do
    Meta.Simp.mkContext { zeta := false, beta := true, eta := true, proj := false, iota := false }
      (simpTheorems := #[← thmsExt.getTheorems]) (congrTheorems := ← Meta.getSimpCongrTheorems)
  let mut mv := mv
  let mut map : Std.HashMap Expr (Array Expr) := {}
  let mut hs' := #[]
  -- The propositional hypotheses that the Boolean ones replace.
  let mut olds := #[]
  for h in hs do
    let (h', mv') ← mv.withContext do
      let p ← instantiateMVars (← Meta.inferType h)
      unless ← Meta.isProp p do return (h, mv)
      let p : Q(Prop) ← pure p
      let h : Q($p) ← pure h
      let hb : Q(@decide $p (Classical.propDecidable $p) = true) :=
        q(Eq.mpr (@decide_eq_true_eq $p (Classical.propDecidable $p)) $h)
      let (r, _) ← Meta.simp q(@decide $p (Classical.propDecidable $p) = true) ctx simprocs
      let hb ← match r.proof? with
        | none => pure hb
        | some e => Meta.mkEqMP e hb
      let n ← if h.isFVar then h.fvarId!.getUserName else mkFreshUserName `h
      let mv ← mv.assert n r.expr hb
      let (fv, mv) ← mv.intro1P
      return (.fvar fv, mv)
    if h' != h && h.isFVar then
      olds := olds.push h.fvarId!
    mv := mv'
    hs' := hs'.push h'
    map := map.insert h' #[h]
  mv ← mv.tryClearMany olds
  return { map, hs := hs', mv }

/-- Embed the goal `mv` and the hypotheses `hs` into SMT-LIB's logic: embed the types that SMT-LIB
lacks into ones it has (see `embedTypes`), and turn the hypotheses into Boolean formulas (see
`embedProps`). -/
def embedding (mv : MVarId) (hs : Array Expr) : MetaM Result := do
  let r₁ ← embedTypes mv hs
  let r₂ ← embedProps r₁.mv r₁.hs
  -- Map the final hypotheses to the original ones.
  let map := r₂.map.fold (init := r₁.map) fun map k v =>
    map.insert k (v.map fun x => r₁.map.getD x #[x]).flatten
  return { r₂ with map }

end Smt.Preprocess
