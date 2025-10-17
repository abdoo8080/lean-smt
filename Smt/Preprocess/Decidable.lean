/-
Copyright (c) 2021-2024 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

import Lean
import Smt.Preprocess.Basic

namespace Smt.Preprocess

theorem classical_ite_congr {α : Sort u} {c₁ c₂ : Prop} {h₁ : Decidable c₁} {t₁ t₂ e₁ e₂ : α}
    (hc : c₁ = c₂) (ht : t₁ = t₂) (he : e₁ = e₂) :
    @ite α c₁ h₁ t₁ e₁ = @ite α c₂ (Classical.propDecidable c₂) t₂ e₂ := by
  grind

open Lean

def replaceIteDecidableInst (e : Expr) : MetaM Expr := do
  go #[] e
where
  go (xs : Array Expr) (e : Expr) : MetaM Expr := do
  match e with
  | mkApp3 (.const ``ite us) α c (.app (.const ``Classical.propDecidable []) _) =>
    let α ← go xs α
    let c ← go xs c
    match ← Meta.synthInstance? (.app (.const ``Decidable []) (c.instantiateRev xs)) with
    | some h => return mkApp3 (.const ``ite us) α c h
    | none    => return e
  | .app f a         =>
    let f ← go xs f
    let a ← go xs a
    return e.updateApp! f a
  | .lam n t b bi     =>
    let t ← go xs t
    Meta.withLocalDecl n bi (t.instantiateRev xs) fun x => do
      Meta.mkLambdaFVars #[x] (← go (xs.push x) b) false false false false
  | .forallE n t b bi =>
    let t ← go xs t
    Meta.withLocalDecl n bi (t.instantiateRev xs) fun x => do
      Meta.mkForallFVars #[x] (← go (xs.push x) b)  false false false
  | .letE n t v b nd  =>
    let t ← go xs t
    let v ← go xs v
    Meta.withLetDecl n t v (nondep := nd) fun x => do
      Meta.mkLetFVars #[x] (← go (xs.push x) b) false false
  | .proj _ _ b      =>
    return e.updateProj! (← go xs b)
  | .mdata _ a       =>
    return e.updateMData! (← go xs a)
  | _                =>
    return e

def mkEqIteDecidableInst (e : Expr) : MetaM Expr := do
  let e' ← replaceIteDecidableInst e
  Meta.mkAppM ``Eq #[e, e']

def containsClassicalPropDecidable (e : Expr) : Bool :=
  (Expr.const ``Classical.propDecidable []).occurs e

def replaceIteInst (mv : MVarId) (hs : Array Expr) : MetaM Result := mv.withContext do
  let t ← instantiateMVars (← mv.getType)
  let ts ← hs.mapM (Meta.inferType · >>= instantiateMVars)
  if !(containsClassicalPropDecidable t || ts.any containsClassicalPropDecidable) then
    return { map := Std.HashMap.insertMany ∅ (hs.zip (hs.map .singleton)), hs, mv }
  let simpTheorems ← #[``eq_self, ``classical_ite_congr].foldlM (·.addConst ·) {}
  let simpTheorems := #[simpTheorems]
  let congrTheorems := {}
  let ctx ← Meta.Simp.mkContext {} simpTheorems congrTheorems
  let (hs', mv') ← replaceIteInstLocalDecls mv hs.toList ctx #[]
  let mv' ← replaceIteInstTarget mv' ctx
  return { map := Std.HashMap.insertMany ∅ (hs'.zip (hs.map .singleton)), hs := hs', mv := mv' }
where
  replaceIteInstLocalDecls mv hs ctx hs' := do match hs with
    | [] => return (hs', mv)
    | h :: hs =>
      let type ← Meta.inferType h
      let eq ← mkEqIteDecidableInst (← instantiateMVars type)
      let (_, l, r) := eq.eq?.get!
      if l == r then
        replaceIteInstLocalDecls mv hs ctx (hs'.push h)
      else
        let (res, _) ← Meta.simp eq ctx
        let h' := mkApp4 (.const ``Eq.mp [0]) l r (mkOfEqTrue eq (← res.getProof)) h
        if let .some fv := h.fvarId? then
          let res ← mv.replace fv h' (.some r)
          let hs' := hs'.map res.subst.apply
          let hs := hs.map res.subst.apply
          res.mvarId.withContext (replaceIteInstLocalDecls res.mvarId hs ctx (hs'.push (.fvar res.fvarId)))
        else
          replaceIteInstLocalDecls mv hs ctx (hs'.push h')
      termination_by hs.length
  replaceIteInstTarget mv ctx := mv.withContext do
    let eq ← mkEqIteDecidableInst (← instantiateMVars (← mv.getType))
    let (res, _) ← Meta.simp eq ctx
    if res.expr.isTrue then
      mv.replaceTargetEq eq.appArg! (mkOfEqTrue eq (← res.getProof))
    else
      return mv
  mkOfEqTrue p hpt :=
    mkApp2 (.const ``of_eq_true []) p hpt

end Smt.Preprocess
