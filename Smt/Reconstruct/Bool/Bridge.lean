/-
Copyright (c) 2021-2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

module

public import Lean.Meta.Basic
public meta import Lean.Meta.Basic
public import Qq
public meta import Qq
public import Smt.Reconstruct.Bool.Core
public meta import Smt.Reconstruct.Bool.Core

public meta section

namespace Smt.Reconstruct.Bool

open Lean Qq

/-- The Boolean atom `decide p` of the proposition `p`, with a synthesized instance of `Decidable p`, or a
classical one. -/
def decideOf (p : Expr) : MetaM Expr := do
  let inst ← match ← Meta.synthInstance? (mkApp (.const ``Decidable []) p) with
    | some inst => pure inst
    | none => pure (mkApp (.const ``Classical.propDecidable []) p)
  return mkApp2 (.const ``Decidable.decide []) p inst

/-- The instance of `DecidableEq α` that Boolean formulas decide `a = b` with for `a b : α`: the exact
one for SMT-LIB's builtin sorts, and otherwise a synthesized one, or a classical one. -/
def decEqInst (α : Expr) : MetaM Expr := do
  if α.isConstOf ``Bool then return .const ``instDecidableEqBool []
  if α.isConstOf ``Int then return .const ``Int.instDecidableEq []
  if α.isConstOf ``String then return .const ``instDecidableEqString []
  if α.isConstOf `Real then return .const `Real.decidableEq []
  if let some w := α.app1? ``BitVec then return mkApp (.const ``instDecidableEqBitVec []) w
  let u ← Meta.getLevel α
  if let some inst ← Meta.synthInstance? (mkApp (.const ``DecidableEq [u]) α) then return inst
  return mkApp (.const ``Classical.typeDecidableEq [u]) α

/-- The instance `decEqInst α a b` of `Decidable (a = b)` with which Boolean formulas decide
`a = b`. -/
def eqInst (α a b : Expr) : MetaM Expr := do
  return mkApp2 (← decEqInst α) a b

/-- The Boolean formula `decide (a = b)` of `a = b` for `a b : α`, with the instance `decEqInst α a b`. -/
def mkDecideEq (α a b : Expr) : MetaM Expr := do
  return mkApp2 (.const ``Decidable.decide []) (← Meta.mkEq a b) (← eqInst α a b)

/-- The type `α`, the sides `a` and `b`, and the instance of `Decidable (a = b)` of the Boolean
formula `decide (a = b)` of an equality (see `mkDecideEq`). -/
def getEq? (e : Expr) : Option (Expr × Expr × Expr × Expr) := Id.run do
  if let some (p, inst) := e.app2? ``Decidable.decide then
    if let some (α, a, b) := p.eq? then
      return some (α, a, b, inst)
  return none

/-- Return the proposition `p` denoted by the Boolean formula `b` (see the table in
`Smt.Reconstruct.Bool.Core`) and a proof of `(b = true) = p`. The proof is `none` if `p` is
`b = true`. -/
partial def toProp (b : Expr) : MetaM (Expr × Option Expr) := do
  if b.isConstOf ``Bool.true then
    return (q(True), some q(true_eq_true_eq))
  if b.isConstOf ``Bool.false then
    return (q(False), some q(false_eq_true_eq))
  if let some x := b.app1? ``not then
    let x : Q(Bool) ← pure x
    let (p, h) ← toProp x
    let p : Q(Prop) ← pure p
    let h : Q(($x = true) = $p) ← pure (h.getD q(Eq.refl ($x = true)))
    return (q(¬$p), some q(not_eq_true_eq $h))
  if let some (x, y) := b.app2? ``and then
    let ⟨_, _, p, q, hx, hy⟩ ← binary x y
    return (q($p ∧ $q), some q(and_eq_true_eq $hx $hy))
  if let some (x, y) := b.app2? ``or then
    let ⟨_, _, p, q, hx, hy⟩ ← binary x y
    return (q($p ∨ $q), some q(or_eq_true_eq $hx $hy))
  if let some (x, y) := b.app2? ``xor then
    let ⟨_, _, p, q, hx, hy⟩ ← binary x y
    return (q(XOr $p $q), some q(xor_eq_true_eq $hx $hy))
  if let some (x, y) := b.app2? ``Bool.imp then
    let ⟨_, _, p, q, hx, hy⟩ ← binary x y
    return (q($p → $q), some q(imp_eq_true_eq $hx $hy))
  if let some (p, inst) := b.app2? ``decide then
    -- An equality of Boolean formulas denotes the equality of their propositions.
    if let some (α, x, y) := p.eq? then
      if α.isConstOf ``Bool then
        let ⟨_, _, p, q, hx, hy⟩ ← binary x y
        return (q($p = $q),
          some (mkAppN (.const ``decide_bool_eq_true_eq []) #[p, q, x, y, inst, hx, hy]))
    return (p, some (mkApp2 (.const ``decide_eq_true_eq []) p inst))
  if let some (x, y) := b.app2? `Int.blt then
    return ← comparison (mkApp2 (.const `Int.blt_eq_true []) x y)
  if let some (x, y) := b.app2? `Int.ble then
    return ← comparison (mkApp2 (.const `Int.ble_eq_true []) x y)
  if let some (x, y) := b.app2? `Int.bgt then
    return ← comparison (mkApp2 (.const `Int.bgt_eq_true []) x y)
  if let some (x, y) := b.app2? `Int.bge then
    return ← comparison (mkApp2 (.const `Int.bge_eq_true []) x y)
  if let some (x, y) := b.app2? `Rat.blt then
    return ← comparison (mkApp2 (.const `Rat.blt_eq_true []) x y)
  if let some (x, y) := b.app2? `Rat.ble then
    return ← comparison (mkApp2 (.const `Rat.ble_eq_true []) x y)
  if let some (x, y) := b.app2? `Rat.bgt then
    return ← comparison (mkApp2 (.const `Rat.bgt_eq_true []) x y)
  if let some (x, y) := b.app2? `Rat.bge then
    return ← comparison (mkApp2 (.const `Rat.bge_eq_true []) x y)
  if let some (x, y) := b.app2? `Real.blt then
    return ← comparison (mkApp2 (.const `Real.blt_eq_true []) x y)
  if let some (x, y) := b.app2? `Real.ble then
    return ← comparison (mkApp2 (.const `Real.ble_eq_true []) x y)
  if let some (x, y) := b.app2? `Real.bgt then
    return ← comparison (mkApp2 (.const `Real.bgt_eq_true []) x y)
  if let some (x, y) := b.app2? `Real.bge then
    return ← comparison (mkApp2 (.const `Real.bge_eq_true []) x y)
  if let some (w, x, y) := b.app3? ``BitVec.ult then
    return ← comparison (mkApp (.const ``propext []) (mkApp3 (.const ``BitVec.ult_iff_lt []) w x y))
  if let some (w, x, y) := b.app3? ``BitVec.ule then
    return ← comparison (mkApp (.const ``propext []) (mkApp3 (.const ``BitVec.ule_iff_le []) w x y))
  if let some (w, x, y) := b.app3? `BitVec.ugt then
    return ← comparison (mkApp (.const ``propext []) (mkApp3 (.const `BitVec.ugt_iff_gt []) w x y))
  if let some (w, x, y) := b.app3? `BitVec.uge then
    return ← comparison (mkApp (.const ``propext []) (mkApp3 (.const `BitVec.uge_iff_ge []) w x y))
  if b.isAppOfArity ``Bool.forall 2 || b.isAppOfArity ``Bool.exists 2 then
    let α := b.getArg! 0
    let u ← Meta.getLevel α
    let f := b.getArg! 1
    let (n, bi) := match f with
      | .lam n _ _ bi => (n, bi)
      | _ => (`x, .default)
    return ← Meta.withLocalDecl n bi α fun x => do
      let fx := f.beta #[x]
      let (p, h?) ← toProp fx
      let h ← match h? with
        | some h => pure h
        | none => Meta.mkEqRefl (← Meta.mkEq fx q(true))
      let lp ← Meta.mkLambdaFVars #[x] p
      let hx ← Meta.mkLambdaFVars #[x] h
      if b.isAppOfArity ``Bool.forall 2 then
        return (← Meta.mkForallFVars #[x] p,
                some (mkAppN (.const ``forall_eq_true_eq [u]) #[α, f, lp, hx]))
      else
        return (mkApp2 (.const ``Exists [u]) α lp,
                some (mkAppN (.const ``exists_eq_true_eq [u]) #[α, f, lp, hx]))
  return (← Meta.mkEq b q(true), none)
where
  /-- The proposition `p` and the proof `h : (b = true) = p` of a comparison `b`. -/
  comparison (h : Expr) : MetaM (Expr × Option Expr) := do
    let some (_, _, p) := (← Meta.inferType h).eq? | throwError "expected an equality{indentExpr h}"
    return (p, some h)
  binary (x y : Expr) :
      MetaM ((x : Q(Bool)) × (y : Q(Bool)) × (p : Q(Prop)) × (q : Q(Prop)) ×
             Q(($x = true) = $p) × Q(($y = true) = $q)) := do
    let x : Q(Bool) ← pure x
    let y : Q(Bool) ← pure y
    let (p, hx) ← toProp x
    let (q, hy) ← toProp y
    return ⟨x, y, p, q, hx.getD q(Eq.refl ($x = true)), hy.getD q(Eq.refl ($y = true))⟩

end Smt.Reconstruct.Bool
