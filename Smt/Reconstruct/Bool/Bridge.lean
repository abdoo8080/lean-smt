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
  if let some p := b.app1? ``smtDecide then
    let p : Q(Prop) ← pure p
    return (p, some q(@smtDecide_eq_true $p))
  if b.isAppOfArity ``smtEq 3 then
    let α := b.getArg! 0
    let (x, y) := (b.getArg! 1, b.getArg! 2)
    if α.isConstOf ``Bool then
      let ⟨_, _, p, q, hx, hy⟩ ← binary x y
      return (q($p = $q), some q(smtEq_bool_eq_true_eq $hx $hy))
    let u ← Meta.getLevel α
    return (← Meta.mkEq x y, some (mkApp3 (.const ``smtEq_eq_true [u]) α x y))
  if b.isAppOfArity ``smtLt 4 then
    let #[α, inst, x, y] := b.getAppArgs | unreachable!
    let u ← Meta.getDecLevel α
    return (mkApp4 (.const ``LT.lt [u]) α inst x y, some (mkApp4 (.const ``smtLt_eq_true [u]) α x y inst))
  if b.isAppOfArity ``smtLe 4 then
    let #[α, inst, x, y] := b.getAppArgs | unreachable!
    let u ← Meta.getDecLevel α
    return (mkApp4 (.const ``LE.le [u]) α inst x y, some (mkApp4 (.const ``smtLe_eq_true [u]) α x y inst))
  if b.isAppOfArity ``smtGt 4 then
    let #[α, inst, x, y] := b.getAppArgs | unreachable!
    let u ← Meta.getDecLevel α
    return (mkApp4 (.const ``GT.gt [u]) α inst x y, some (mkApp4 (.const ``smtGt_eq_true [u]) α x y inst))
  if b.isAppOfArity ``smtGe 4 then
    let #[α, inst, x, y] := b.getAppArgs | unreachable!
    let u ← Meta.getDecLevel α
    return (mkApp4 (.const ``GE.ge [u]) α inst x y, some (mkApp4 (.const ``smtGe_eq_true [u]) α x y inst))
  if b.isAppOfArity ``smtForall 2 || b.isAppOfArity ``smtExists 2 then
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
      if b.isAppOfArity ``smtForall 2 then
        return (← Meta.mkForallFVars #[x] p,
                some (mkAppN (.const ``smtForall_eq_true_eq [u]) #[α, f, lp, hx]))
      else
        return (mkApp2 (.const ``Exists [u]) α lp,
                some (mkAppN (.const ``smtExists_eq_true_eq [u]) #[α, f, lp, hx]))
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

end Smt.Reconstruct.Bool
