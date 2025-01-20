/-
Copyright (c) 2021-2024 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

import Smt.Reconstruct.Real.Polynorm

namespace Smt.Reconstruct.Real

open Lean Qq

abbrev PolyM := StateT (Array Q(Int) × Array Q(Real)) MetaM

def getRealIndex (e : Q(Real)) : PolyM Nat := do
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

partial def toRealValExpr (e : Q(Real)) : PolyM Q(PolyNorm.RealValExpr) := do
  match e with
  | ~q(@OfNat.ofNat _ _ (@instOfNatAtLeastTwo _ _ _ instNatAtLeastTwo)) =>
    let some n := (e.getArg! 1).rawNatLit? | throwError "[poly_norm] expected a raw natural number, got {e}"
    pure q(.val (@OfNat.ofNat Rat $n _))
  | ~q(0)       => pure q(.val 0)
  | ~q(1)       => pure q(.val 1)
  | ~q(-$x) => pure q(.neg $(← toRealValExpr x))
  | ~q($x + $y) => pure q(.add $(← toRealValExpr x) $(← toRealValExpr y))
  | ~q($x - $y) => pure q(.sub $(← toRealValExpr x) $(← toRealValExpr y))
  | ~q($x * $y) => pure q(.mul $(← toRealValExpr x) $(← toRealValExpr y))
  | ~q($x / $y) => pure q(.div $(← toRealValExpr x) $(← toRealValExpr y))
  | e => throwError "[poly_norm] expected a rational number, got {e}"

partial def toQPolyNormIntExpr (e : Q(Int)) : PolyM Q(PolyNorm.IntExpr) := do
  match e with
  | ~q(OfNat.ofNat $n) => pure q(.val (@OfNat.ofNat Int $n _))
  | ~q(-$x) => pure q(.neg $(← toQPolyNormIntExpr x))
  | ~q($x + $y) => pure q(.add $(← toQPolyNormIntExpr x) $(← toQPolyNormIntExpr y))
  | ~q($x - $y) => pure q(.sub $(← toQPolyNormIntExpr x) $(← toQPolyNormIntExpr y))
  | ~q($x * $y) => pure q(.mul $(← toQPolyNormIntExpr x) $(← toQPolyNormIntExpr y))
  | e => let v : Nat ← getIntIndex e; pure q(.var $v)

partial def toQPolyNormRealExpr (e : Q(Real)) : PolyM Q(PolyNorm.RealExpr) := do
  match e with
  | ~q(@OfNat.ofNat _ _ (@instOfNatAtLeastTwo _ _ _ instNatAtLeastTwo)) =>
    let some n := (e.getArg! 1).rawNatLit? | throwError "[poly_norm] expected a raw natural number, got {e}"
    pure q(.val (@OfNat.ofNat Rat $n _))
  | ~q(0)       => pure q(.val 0)
  | ~q(1)       => pure q(.val 1)
  | ~q(-$x) => pure q(.neg $(← toQPolyNormRealExpr x))
  | ~q($x + $y) => pure q(.add $(← toQPolyNormRealExpr x) $(← toQPolyNormRealExpr y))
  | ~q($x - $y) => pure q(.sub $(← toQPolyNormRealExpr x) $(← toQPolyNormRealExpr y))
  | ~q($x * $y) => pure q(.mul $(← toQPolyNormRealExpr x) $(← toQPolyNormRealExpr y))
  | ~q($x / $y) => pure q(.divConst $(← toQPolyNormRealExpr x) $(← toRealValExpr y))
  | ~q(($x : Int)) => pure q(.cast $(← toQPolyNormIntExpr x))
  | e => let v : Nat ← getRealIndex e; pure q(.var $v)

def polyNorm (mv : MVarId) : MetaM Unit := do
  let some (_, l, r) := (← mv.getType).eq?
    | throwError "[poly_norm] expected an equality, got {← mv.getType}"
  let (l, (is, rs)) ← (toQPolyNormRealExpr l).run (#[], #[])
  let (r, (is, rs)) ← (toQPolyNormRealExpr r).run (is, rs)
  let is : Q(Array Int) ← pure (is.foldl (fun acc e => q(«$acc».push $e)) q(#[]))
  let rs : Q(Array Real) ← pure (rs.foldl (fun acc e => q(«$acc».push $e)) q(#[]))
  let ictx : Q(PolyNorm.IntContext) := q((«$is».getD · 0))
  let rctx : Q(PolyNorm.RealContext) := q((«$rs».getD · 0))
  let h : Q(«$l».toPolynomial = «$r».toPolynomial) := .app q(@Eq.refl.{1} PolyNorm.Polynomial) q(«$l».toPolynomial)
  mv.assign q(@PolyNorm.RealExpr.denote_eq_from_toPolynomial_eq $ictx $rctx $l $r $h)

def nativePolyNorm (mv : MVarId) : MetaM Unit := do
  let some (_, l, r) := (← mv.getType).eq?
    | throwError "[poly_norm] expected an equality, got {← mv.getType}"
  let (l, (is, rs)) ← (toQPolyNormRealExpr l).run (#[], #[])
  let (r, (is, rs)) ← (toQPolyNormRealExpr r).run (is, rs)
  let is : Q(Array Int) ← pure (is.foldl (fun acc e => q(«$acc».push $e)) q(#[]))
  let rs : Q(Array Real) ← pure (rs.foldl (fun acc e => q(«$acc».push $e)) q(#[]))
  let ictx : Q(PolyNorm.IntContext) := q((«$is».getD · 0))
  let rctx : Q(PolyNorm.RealContext) := q((«$rs».getD · 0))
  let h ← nativeDecide q(«$l».toPolynomial = «$r».toPolynomial)
  mv.assign q(@PolyNorm.RealExpr.denote_eq_from_toPolynomial_eq $ictx $rctx $l $r $h)
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

def traceArithNormNum (r : Except Exception Unit) : MetaM MessageData :=
  return match r with
  | .ok _ => m!"{checkEmoji}"
  | _     => m!"{bombEmoji}"

open Mathlib.Meta.NormNum in
def normNum (mv : MVarId) : MetaM Unit := withTraceNode `smt.reconstruct.normNum traceArithNormNum do
  if let some (_, mv) ← normNumAt mv (← Meta.Simp.mkContext) #[] true false then
    throwError "[norm_num]: could not prove {← mv.getType}"

namespace Tactic

syntax (name := polyNorm) "poly_norm" : tactic

open Lean.Elab Tactic in
@[tactic polyNorm] def evalPolyNorm : Tactic := fun _ =>
  withMainContext do
    let mv ← Tactic.getMainGoal
    Real.polyNorm mv
    replaceMainGoal []

syntax (name := nativePolyNorm) "native_poly_norm" : tactic

open Lean.Elab Tactic in
@[tactic nativePolyNorm] def evalNativePolyNorm : Tactic := fun _ =>
  withMainContext do
    let mv ← Tactic.getMainGoal
    Real.nativePolyNorm mv
    replaceMainGoal []

end Smt.Reconstruct.Real.Tactic

example (x y z : Real) : 1 * (x + y) * z / 4 = 1 / (2 * 2) * (z * y + x * z) := by
  poly_norm

example (x y : Int) (z : Real) : 1 * (↑x + ↑y) * z / 4 = 1 / (2 * 2) * (z * ↑y + ↑x * z) := by
  poly_norm

example (x y : Int) (z : Real) : 1 * ↑(x + y) * z / 4 = 1 / (2 * 2) * (z * ↑y + ↑x * z) := by
  native_poly_norm
