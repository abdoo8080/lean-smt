/-
Copyright (c) 2021-2025 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

import Qq
import Smt.Reconstruct.Rat.Polynorm

namespace Smt.Reconstruct.Rat

open Lean Qq

open PolyNorm in
def PolyNorm.Monomial.toExpr (m : Monomial) (ppCtx : Var → Q(Rat)) : Q(Rat) :=
  if h : m.vars = [] then
    toExprCoeff m.coeff
  else
    if m.coeff = 1 then
      (m.vars.drop 1).foldl (fun acc v => q($acc * $(ppCtx v))) (ppCtx (m.vars.head h))
    else
      m.vars.foldl (fun acc v => q($acc * $(ppCtx v))) (toExprCoeff m.coeff)
where
  toExprCoeff (c : Rat) : Q(Rat) :=
  let num : Q(Rat) := mkRatLit c.num.natAbs
  if c.den == 1 then
    if c.num ≥ 0 then
      q($num)
    else
      q(-$num)
  else
    let den : Q(Rat) := mkRatLit c.den
    if c.num ≥ 0 then
      q($num / $den)
    else
      q(-$num / $den)
  mkRatLit (n : Nat) : Q(Rat) :=
    let l : Q(Nat) := Lean.mkRawNatLit n
    q(OfNat.ofNat $l)

def PolyNorm.Polynomial.toExpr (p : Polynomial) (ppCtx : Var → Q(Rat)) : Q(Rat) :=
  go p
where
  go : Polynomial → Q(Rat)
    | [] => q(0)
    | [m] => m.toExpr ppCtx
    | m :: ms =>q($(m.toExpr ppCtx) + $(go ms))

abbrev PolyM := StateT (Array Q(Int) × Array Q(Rat)) MetaM

def getRatIndex (e : Q(Rat)) : PolyM Nat := do
  let ⟨is, rs⟩ ← get
  if let some i := rs.findIdx? (· == e) then
    return i
  else
    let size := rs.size
    set (is, rs.push e)
    return size

def getIntIndex (e : Q(Int)) : PolyM Nat := do
  let ⟨is, rs⟩ ← get
  if let some i := is.findIdx? (· == e) then
    return i
  else
    let size := is.size
    set (is.push e, rs)
    return size

partial def toRatConst (e : Q(Rat)) : PolyM Rat := do
  match e with
  | ~q(OfNat.ofNat $n) => pure n.rawNatLit?.get!
  | ~q(-$x) => pure (-(← toRatConst x))
  | ~q($x + $y) => pure ((← toRatConst x) + (← toRatConst y))
  | ~q($x - $y) => pure ((← toRatConst x) - (← toRatConst y))
  | ~q($x * $y) => pure ((← toRatConst x) * (← toRatConst y))
  | ~q($x / $y) => pure ((← toRatConst x) / (← toRatConst y))
  | e => throwError "[poly_norm] expected a rational number, got {e}"

partial def toQPolyNormIntExpr (e : Q(Int)) : PolyM Q(PolyNorm.IntExpr) := do
  match e with
  | ~q(OfNat.ofNat $n) => pure q(.val (@OfNat.ofNat Int $n _))
  | ~q(-$x) => pure q(.neg $(← toQPolyNormIntExpr x))
  | ~q($x + $y) => pure q(.add $(← toQPolyNormIntExpr x) $(← toQPolyNormIntExpr y))
  | ~q($x - $y) => pure q(.sub $(← toQPolyNormIntExpr x) $(← toQPolyNormIntExpr y))
  | ~q($x * $y) => pure q(.mul $(← toQPolyNormIntExpr x) $(← toQPolyNormIntExpr y))
  | e => let v : Nat ← getIntIndex e; pure q(.var $v)

partial def toQPolyNormRatExpr (e : Q(Rat)) : PolyM Q(PolyNorm.RatExpr) := do
  match e with
  | ~q(OfNat.ofNat $n) => pure q(.val (@OfNat.ofNat Rat $n _))
  | ~q(-$x) => pure q(.neg $(← toQPolyNormRatExpr x))
  | ~q($x + $y) => pure q(.add $(← toQPolyNormRatExpr x) $(← toQPolyNormRatExpr y))
  | ~q($x - $y) => pure q(.sub $(← toQPolyNormRatExpr x) $(← toQPolyNormRatExpr y))
  | ~q($x * $y) => pure q(.mul $(← toQPolyNormRatExpr x) $(← toQPolyNormRatExpr y))
  | ~q($x / $y) => pure q(.divConst $(← toQPolyNormRatExpr x) $(PolyNorm.Monomial.toExpr.toExprCoeff (← toRatConst y)))
  | ~q(($x : Int)) => pure q(.cast $(← toQPolyNormIntExpr x))
  | e => let v : Nat ← getRatIndex e; pure q(.var $v)

def polyNorm (mv : MVarId) : MetaM Unit := do
  let some (_, l, r) := (← mv.getType).eq?
    | throwError "[poly_norm] expected an equality, got {← mv.getType}"
  let (l, (is, rs)) ← (toQPolyNormRatExpr l).run (#[], #[])
  let (r, (is, rs)) ← (toQPolyNormRatExpr r).run (is, rs)
  let is : Q(Array Int) ← pure (is.foldl (fun acc e => q(«$acc».push $e)) q(#[]))
  let rs : Q(Array Rat) ← pure (rs.foldl (fun acc e => q(«$acc».push $e)) q(#[]))
  let ictx : Q(PolyNorm.IntContext) := q((«$is».getD · 0))
  let rctx : Q(PolyNorm.RatContext) := q((«$rs».getD · 0))
  let h : Q(«$l».toPolynomial = «$r».toPolynomial) := .app q(@Eq.refl.{1} PolyNorm.Polynomial) q(«$l».toPolynomial)
  mv.assign q(@PolyNorm.RatExpr.denote_eq_from_toPolynomial_eq $ictx $rctx $l $r $h)

def nativePolyNorm (mv : MVarId) : MetaM Unit := do
  let some (_, l, r) := (← mv.getType).eq?
    | throwError "[poly_norm] expected an equality, got {← mv.getType}"
  let (l, (is, rs)) ← (toQPolyNormRatExpr l).run (#[], #[])
  let (r, (is, rs)) ← (toQPolyNormRatExpr r).run (is, rs)
  let is : Q(Array Int) ← pure (is.foldl (fun acc e => q(«$acc».push $e)) q(#[]))
  let rs : Q(Array Rat) ← pure (rs.foldl (fun acc e => q(«$acc».push $e)) q(#[]))
  let ictx : Q(PolyNorm.IntContext) := q((«$is».getD · 0))
  let rctx : Q(PolyNorm.RatContext) := q((«$rs».getD · 0))
  let h ← nativeDecide q(«$l».toPolynomial = «$r».toPolynomial)
  mv.assign q(@PolyNorm.RatExpr.denote_eq_from_toPolynomial_eq $ictx $rctx $l $r $h)
where
  nativeDecide (p : Q(Prop)) : MetaM Q($p) := do
    let hp : Q(Decidable $p) ← Meta.synthInstance q(Decidable $p)
    let auxDeclName ← mkNativeAuxDecl `_nativePolynorm q(Bool) q(decide $p)
    let b : Q(Bool) := .const auxDeclName []
    return .app q(@of_decide_eq_true $p $hp) (.app q(Lean.ofReduceBool $b true) q(Eq.refl true))
  mkNativeAuxDecl (baseName : Name) (type value : Expr) : MetaM Name := do
    let auxName ← Lean.mkAuxName baseName 1
    let decl := Declaration.defnDecl {
      name := auxName, levelParams := [], type, value
      hints := .abbrev
      safety := .safe
    }
    addAndCompile decl
    pure auxName

namespace Tactic

syntax (name := polyNorm) "poly_norm" : tactic

open Lean.Elab Tactic in
@[tactic polyNorm] def evalPolyNorm : Tactic := fun _ =>
  withMainContext do
    let mv ← Tactic.getMainGoal
    Rat.polyNorm mv
    replaceMainGoal []

syntax (name := nativePolyNorm) "native_poly_norm" : tactic

open Lean.Elab Tactic in
@[tactic nativePolyNorm] def evalNativePolyNorm : Tactic := fun _ =>
  withMainContext do
    let mv ← Tactic.getMainGoal
    Rat.nativePolyNorm mv
    replaceMainGoal []

end Smt.Reconstruct.Rat.Tactic

example (x y z : Rat) : 1 * (x + y) * z / 4 = 1 / (2 * 2) * (z * y + x * z) := by
  poly_norm

example (x y : Int) (z : Rat) : 1 * (↑x + ↑y) * z / 4 = 1 / (2 * 2) * (z * ↑y + ↑x * z) := by
  poly_norm

example (x y : Int) (z : Rat) : 1 * ↑(x + y) * z / 4 = 1 / (2 * 2) * (z * ↑y + ↑x * z) := by
  native_poly_norm
