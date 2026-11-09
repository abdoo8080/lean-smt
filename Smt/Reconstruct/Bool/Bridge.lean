/-
Copyright (c) 2021-2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

module

public import Lean.Meta.Basic
public meta import Lean.Meta.Basic
public import Lean.Meta.SynthInstance
public meta import Lean.Meta.SynthInstance
public import Qq
public meta import Qq
public import Smt.Reconstruct.Bool.Core
public meta import Smt.Reconstruct.Bool.Core

public meta section

namespace Smt

open Lean Qq

/-- The canonical Boolean reflection of the proposition `p`: `decide p` with the `Decidable`
instance found by type class resolution, or `Classical.propDecidable p` if there is none.
Preprocessing and reconstruction both build atoms with this function, so that the formulas
reconstructed from cvc5's proofs are syntactically equal to the hypotheses they come from. -/
def mkDecide (p : Expr) : MetaM Expr := do
  return mkApp2 (mkConst ``Decidable.decide) p (← mkDecidableInst p)
where
  /-- The `Decidable p` instance of `mkDecide p`. -/
  mkDecidableInst (p : Expr) : MetaM Expr := do
    let inst? ← try Meta.synthInstance? (mkApp (mkConst ``Decidable) p) catch _ => pure none
    return inst?.getD (mkApp (mkConst ``Classical.propDecidable) p)

/-- The `Decidable p` instance of the canonical Boolean reflection `mkDecide p` of `p`. -/
def mkDecidableInst (p : Expr) : MetaM Expr :=
  mkDecide.mkDecidableInst p

namespace Reconstruct.Bool

mutual

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
  if let some (x, y) := b.app2? ``Bool.smtImp then
    let ⟨_, _, p, q, hx, hy⟩ ← binary x y
    return (q($p → $q), some q(smtImp_eq_true_eq $hx $hy))
  if b.isAppOfArity ``cond 4 && (b.getArg! 0).isConstOf ``Bool then
    let c : Q(Bool) ← pure (b.getArg! 1)
    let ⟨x, y, q, r, hx, hy⟩ ← binary (b.getArg! 2) (b.getArg! 3)
    let (p, hc) ← toProp c
    let p : Q(Prop) ← pure p
    let hc : Q(($c = true) = $p) ← pure (hc.getD q(Eq.refl ($c = true)))
    let inst : Q(Decidable $p) ← mkDecidableInst p
    return (q(@ite Prop $p $inst $q $r), some q(@cond_eq_true_eq $c $x $y $p $q $r $inst $hc $hx $hy))
  if let some (p, inst) := b.app2? ``Decidable.decide then
    if let some (α, x, y) := p.eq? then
      if α.isConstOf ``Bool then
        let ⟨x, y, p, q, hx, hy⟩ ← binary x y
        let inst : Q(Decidable ($x = $y)) ← pure inst
        return (q($p = $q), some q(@decide_eq_eq_true_eq $p $q $x $y $inst $hx $hy))
    let p : Q(Prop) ← pure p
    let inst : Q(Decidable $p) ← pure inst
    let (q, h?) ← toPropP p
    let q : Q(Prop) ← pure q
    let h : Q($p = $q) ← pure (h?.getD q(Eq.refl $p))
    return (q, some q(@decide_eq_true_eq_of_eq $p $q $inst $h))
  return (← Meta.mkEq b q(true), none)
where
  binary (x y : Expr) :
      MetaM ((x : Q(Bool)) × (y : Q(Bool)) × (p : Q(Prop)) × (q : Q(Prop)) ×
             Q(($x = true) = $p) × Q(($y = true) = $q)) := do
    let x : Q(Bool) ← pure x
    let y : Q(Bool) ← pure y
    let (p, hx) ← toProp x
    let (q, hy) ← toProp y
    return ⟨x, y, p, q, hx.getD q(Eq.refl ($x = true)), hy.getD q(Eq.refl ($y = true))⟩

/-- Return the proposition denoted by the proposition `p`, which is `b = true` or a quantifier
over such propositions, and a proof that they are equal (`none` if they are the same). -/
partial def toPropP (p : Expr) : MetaM (Expr × Option Expr) := do
  if let some (α, b, t) := p.eq? then
    if α.isConstOf ``Bool && t.isConstOf ``Bool.true then
      return ← toProp b
  match p with
  | .forallE n t r bi =>
    -- Reconstructed quantifiers are over SMT-LIB sorts, so this is a quantifier (possibly over an
    -- unused variable) rather than an implication.
    Meta.withLocalDecl n bi t fun x => do
      let (q, h?) ← toPropP (r.instantiate1 x)
      let some h := h? | return (p, none)
      let u ← Meta.getLevel t
      let lp ← Meta.mkLambdaFVars #[x] (r.instantiate1 x)
      let lq ← Meta.mkLambdaFVars #[x] q
      let hx ← Meta.mkLambdaFVars #[x] h
      let q' ← Meta.mkForallFVars #[x] q
      return (q', some (mkApp4 (.const ``forall_congr [u]) t lp lq hx))
  | _ =>
    if let some (α, lp) := p.app2? ``Exists then
      let .lam n t r bi := lp | return (p, none)
      return ← Meta.withLocalDecl n bi t fun x => do
        let (q, h?) ← toPropP (r.instantiate1 x)
        let some h := h? | return (p, none)
        let u ← Meta.getLevel α
        let lq ← Meta.mkLambdaFVars #[x] q
        let hx ← Meta.mkLambdaFVars #[x] h
        return (mkApp2 (.const ``Exists [u]) α lq,
                some (mkApp4 (.const ``exists_congr_eq [u]) α lp lq hx))
    return (p, none)

end

end Smt.Reconstruct.Bool
