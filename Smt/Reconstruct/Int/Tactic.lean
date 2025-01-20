/-
Copyright (c) 2021-2024 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed, Harun Khan
-/

import Qq
import Smt.Reconstruct.Int.Polynorm

private theorem Int.neg_congr {x y : Int} (h : x = y) : -x = -y := by
  simp [h]

private theorem Int.add_congr {x₁ x₂ y₁ y₂ : Int} (h₁ : x₁ = x₂) (h₂ : y₁ = y₂) : x₁ + y₁ = x₂ + y₂ := by
  simp [h₁, h₂]

private theorem Int.sub_congr {x₁ x₂ y₁ y₂ : Int} (h₁ : x₁ = x₂) (h₂ : y₁ = y₂) : x₁ - y₁ = x₂ - y₂ := by
  simp [h₁, h₂]

private theorem Int.mul_congr {x₁ x₂ y₁ y₂ : Int} (h₁ : x₁ = x₂) (h₂ : y₁ = y₂) : x₁ * y₁ = x₂ * y₂ := by
  simp [h₁, h₂]

namespace Smt.Reconstruct.Int

open Lean Qq

open PolyNorm in
def PolyNorm.Monomial.toExpr (m : Monomial) (ppCtx : Var → Q(Int)) : Q(Int) :=
  if h : m.vars = [] then
    toExprCoeff m.coeff
  else
    if m.coeff = 1 then
      (m.vars.drop 1).foldl (fun acc v => q($acc * $(ppCtx v))) (ppCtx (m.vars.head h))
    else
      m.vars.foldl (fun acc v => q($acc * $(ppCtx v))) (toExprCoeff m.coeff)
where
  toExprCoeff (c : Int) : Q(Int) :=
    let l : Q(Nat) := Lean.mkRawNatLit c.natAbs
    if c ≥ 0 then
      q(OfNat.ofNat $l : Int)
    else
      q(-OfNat.ofNat $l : Int)

def PolyNorm.Polynomial.toExpr (p : Polynomial) (ppCtx : Var → Q(Int)) : Q(Int) :=
  go p
where
  go : Polynomial → Q(Int)
    | [] => q(0)
    | [m] => m.toExpr ppCtx
    | m :: ms =>q($(m.toExpr ppCtx) + $(go ms))

partial def genCtx (e : Q(Int)) : StateT (Array Q(Int) × Std.HashSet Q(Int)) MetaM Unit := do
  if !(← get).snd.contains e then
    go
    modify fun (es, cache) => (es, cache.insert e)
where
  go : StateT (Array Q(Int) × Std.HashSet Q(Int)) MetaM Unit := do
  match e with
  | ~q(OfNat.ofNat $x) => pure ()
  | ~q(-$x)            => genCtx x
  | ~q($x + $y)        => genCtx x >>= fun _ => genCtx y
  | ~q($x - $y)        => genCtx x >>= fun _ => genCtx y
  | ~q($x * $y)        => genCtx x >>= fun _ => genCtx y
  | _                  => if !(← get).fst.contains e then modify fun (es, cache) => (es.push e, cache)

partial def toQPolyNormExpr (ctx : Q(PolyNorm.Context)) (es : Array Q(Int)) (e : Q(Int)) (cache : Std.HashMap Expr (Expr × Expr)) :
  MetaM (Std.HashMap Expr (Expr × Expr) × (o : Q(PolyNorm.Expr)) × Q(«$o».denote $ctx = $e)) := do
  match cache.get? e with
  | some (e, h) => return ⟨cache, e, h⟩
  | none   =>
    let ⟨cache, o, h⟩ ← go
    return ⟨cache.insert e (o, h), o, h⟩
where
  go : MetaM (Std.HashMap Expr (Expr × Expr) × (o : Q(PolyNorm.Expr)) × Q(«$o».denote $ctx = $e)) := do match e with
    | ~q(OfNat.ofNat $x) =>
      pure ⟨cache, q(.val (@OfNat.ofNat Int $x _)), q(rfl)⟩
    | ~q(-$x) =>
      let ⟨cache, o, h⟩ ← toQPolyNormExpr ctx es x cache
      pure ⟨cache, q(.neg $o), q(Int.neg_congr $h)⟩
    | ~q($x + $y) =>
      let ⟨cache, ox, hx⟩ ← toQPolyNormExpr ctx es x cache
      let ⟨cache, oy, hy⟩ ← toQPolyNormExpr ctx es y cache
      pure ⟨cache, q(.add $ox $oy), q(Int.add_congr $hx $hy)⟩
    | ~q($x - $y) =>
      let ⟨cache, ox, hx⟩ ← toQPolyNormExpr ctx es x cache
      let ⟨cache, oy, hy⟩ ← toQPolyNormExpr ctx es y cache
      pure ⟨cache, q(.sub $ox $oy), q(Int.sub_congr $hx $hy)⟩
    | ~q($x * $y) =>
      let ⟨cache, ox, hx⟩ ← toQPolyNormExpr ctx es x cache
      let ⟨cache, oy, hy⟩ ← toQPolyNormExpr ctx es y cache
      pure ⟨cache, q(.mul $ox $oy), q(Int.mul_congr $hx $hy)⟩
    | _ =>
      let some v := (es.findIdx? (· == e)) | throwError "variable not found"
      pure ⟨cache, q(.var $v), .app q(@Eq.refl Int) e⟩

def polyNorm (mv : MVarId) : MetaM Unit := do
  let some (_, (l : Q(Int)), (r : Q(Int))) := (← mv.getType).eq?
    | throwError "[poly_norm] expected an equality, got {← mv.getType}"
  let (_, (es, _)) ← (genCtx l >>= fun _ => genCtx r).run (#[], {})
  let is : Q(Array Int) ← pure (es.foldl (fun acc e => q(«$acc».push $e)) q(#[]))
  let ctx : Q(PolyNorm.Context) ← pure q((«$is».getD · 0))
  let ⟨cache, el, _⟩ ← toQPolyNormExpr ctx es l {}
  let ⟨_, er, _⟩ ← toQPolyNormExpr ctx es r cache
  let hp : Q(«$el».toPolynomial = «$er».toPolynomial) := (.app q(@Eq.refl PolyNorm.Polynomial) q(«$el».toPolynomial))
  let he := q(@PolyNorm.Expr.denote_eq_from_toPolynomial_eq $ctx $el $er $hp)
  mv.assign he
where
  logPolynomial (e : Q(PolyNorm.Expr)) (es : Array Q(Int)) := do
    let p ← unsafe Meta.evalExpr PolyNorm.Expr q(PolyNorm.Expr) e
    let ppCtx := (es.getD · q(0))
    logInfo m!"poly := {PolyNorm.Polynomial.toExpr p.toPolynomial ppCtx}"

def nativePolyNorm (mv : MVarId) : MetaM Unit := do
  let some (_, (l : Q(Int)), (r : Q(Int))) := (← mv.getType).eq?
    | throwError "[poly_norm] expected an equality, got {← mv.getType}"
  let (_, (es, _)) ← (genCtx l >>= fun _ => genCtx r).run (#[], {})
  let is : Q(List Int) ← pure (es.foldr (fun e acc => q($e :: $acc)) q([]))
  let ctx : Q(PolyNorm.Context) ← pure q((«$is».getD · 0))
  let ⟨cache, el, _⟩ ← toQPolyNormExpr ctx es l {}
  let ⟨_, er, _⟩ ← toQPolyNormExpr ctx es r cache
  let hp ← nativeDecide q(«$el».toPolynomial = «$er».toPolynomial)
  let he := q(@PolyNorm.Expr.denote_eq_from_toPolynomial_eq $ctx $el $er $hp)
  mv.assign he
where
  logPolynomial (e : Q(PolyNorm.Expr)) (es : Array Q(Int)) := do
    let p ← unsafe Meta.evalExpr PolyNorm.Expr q(PolyNorm.Expr) e
    let ppCtx := (es.getD · q(0))
    logInfo m!"poly := {PolyNorm.Polynomial.toExpr p.toPolynomial ppCtx}"
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
    Int.polyNorm mv
    replaceMainGoal []

syntax (name := nativePolyNorm) "native_poly_norm" : tactic

open Lean.Elab Tactic in
@[tactic nativePolyNorm] def evalNativePolyNorm : Tactic := fun _ =>
  withMainContext do
    let mv ← Tactic.getMainGoal
    Int.nativePolyNorm mv
    replaceMainGoal []

end Smt.Reconstruct.Int.Tactic

example (x y z : Int) : 1 * (x + y) * z  = z * y + x * z := by
  poly_norm

example (x y z : Int) : 1 * (x + y) * z  = z * y + x * z := by
  native_poly_norm
