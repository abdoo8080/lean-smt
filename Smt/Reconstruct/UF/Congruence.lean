/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomaz Gomes Mascarenhas
-/

module

public import Lean
public meta import Lean
public import Qq
public meta import Qq

public import Smt.Reconstruct.Bool.Bridge
public meta import Smt.Reconstruct.Bool.Bridge

public meta section

/-!
# Congruence over `Bool.eq`

The proof of an SMT equality `(= a b)` is a proof of `Bool.eq a b`, where equalities of `a b : α`
are decided by `Smt.Reconstruct.Bool.decEqInst α`, so congruence is proved with the theorems
`Bool.eq.congr` and friends, instantiated with these instances.
-/

namespace Smt.Reconstruct.UF

open Lean Elab Tactic
open Qq

/-- A proof of `Bool.eq a a`. -/
def mkBoolEqRefl (a : Expr) : MetaM Expr := do
  let α ← Meta.inferType a
  return mkApp3 (.const ``Bool.eq.refl [← Meta.getLevel α]) α (← Bool.decEqInst α) a

/-- A proof of `Bool.eq (f a) (g b)` from the proofs `hf` of `Bool.eq f g` and `h` of
`Bool.eq a b`. -/
def mkBoolEqCongr (f g a b hf h : Expr) : MetaM Expr := do
  let fType ← Meta.inferType f
  let some (α, β) := fType.arrow?
    | throwError "[smt_congr]: expected a function, got{indentExpr f}"
  let inst ← Bool.decEqInst fType
  return mkAppN (.const ``Bool.eq.congr [← Meta.getLevel α, ← Meta.getLevel β])
    #[α, β, ← Bool.decEqInst α, ← Bool.decEqInst β, a, b, inst, f, g, hf, h]

/-- A proof of `Bool.eq (f a) (f b)` from the proof `h` of `Bool.eq a b`. -/
def mkBoolEqCongrArg (f a b h : Expr) : MetaM Expr := do
  let some (α, β) := (← Meta.inferType f).arrow?
    | throwError "[smt_congr]: expected a function, got{indentExpr f}"
  return mkAppN (.const ``Bool.eq.congrArg [← Meta.getLevel α, ← Meta.getLevel β])
    #[α, β, ← Bool.decEqInst α, ← Bool.decEqInst β, a, b, f, h]

/-- A proof of `(b = true) = p`, where `p` is the proposition that a Lean function is passed for the
Boolean `b`: `p` if `b` is the atom `decide p`, and `b = true` otherwise. -/
def mkPropOfBoolEq (b : Expr) : MetaM Expr := do
  if let some (p, hp) := b.app2? ``Decidable.decide then
    return mkApp2 (.const ``decide_eq_true_eq []) p hp
  Meta.mkEqRefl (← Meta.mkEq b (.const ``Bool.true []))

/-- Congruence of the application `l` of `f` to its last `hs.size` arguments `a₁ … aₙ` and the
application `r` of `f` to `b₁ … bₙ`. Each `hs[i]` is a triple `(cᵢ, dᵢ, hᵢ)` of the reconstructions
of SMT-LIB arguments and a proof of `Bool.eq cᵢ dᵢ`, where `aᵢ` is `cᵢ` (and `bᵢ` is `dᵢ`), except
that Lean functions that take a proposition are passed one for the Boolean `cᵢ` (see
`mkPropOfBoolEq`). -/
def smtCongrUF (l r : Expr) (hs : Array (Expr × Expr × Expr)) : MetaM Expr := do
  let n := hs.size
  let f := l.getBoundedAppFn n
  let mut f₁ := f
  let mut f₂ := f
  let mut h ← mkBoolEqRefl f
  for a₁ in l.getBoundedAppArgs n, a₂ in r.getBoundedAppArgs n, (c₁, c₂, hc) in hs do
    let some (α, _) := (← Meta.inferType f₁).arrow?
      | throwError "[smt_congr]: expected a function, got{indentExpr f₁}"
    let ha ← if α.isProp then
        pure (mkAppN (.const ``Bool.eq.prop_congr [])
          #[← Bool.decEqInst α, c₁, c₂, a₁, a₂, ← mkPropOfBoolEq c₁, ← mkPropOfBoolEq c₂, hc])
      else pure hc
    h ← mkBoolEqCongr f₁ f₂ a₁ a₂ h ha
    f₁ := .app f₁ a₁
    f₂ := .app f₂ a₂
  return h

/-- Congruence of `op (… (op x₁ x₂) …) xₙ` for the left-associative operator `op`, where the `xᵢ`
are the first components of the triples `hs` (see `smtCongrUF`). -/
def smtCongrLeftAssocOp (op : Expr) (hs : Array (Expr × Expr × Expr)) : MetaM Expr := do
  let (x₁, y₁, h₁) := hs[0]!
  let mut x := x₁
  let mut y := y₁
  let mut h := h₁
  for (x₂, y₂, h₂) in hs[1:] do
    h ← mkBoolEqCongr (.app op x) (.app op y) x₂ y₂ (← mkBoolEqCongrArg op x y h) h₂
    x := mkApp2 op x x₂
    y := mkApp2 op y y₂
  return h

/-- Congruence of `op x₁ (… (op xₙ₋₁ xₙ))` for the right-associative operator `op`, where the `xᵢ`
are the first components of the triples `hs` (see `smtCongrUF`). -/
def smtCongrRightAssocOp (op : Expr) (hs : Array (Expr × Expr × Expr)) : MetaM Expr := do
  let (xₙ, yₙ, hₙ) := hs[hs.size - 1]!
  let mut x := xₙ
  let mut y := yₙ
  let mut h := hₙ
  for (x₁, y₁, h₁) in hs[:hs.size - 1].toArray.reverse do
    h ← mkBoolEqCongr (.app op x₁) (.app op y₁) x y (← mkBoolEqCongrArg op x₁ y₁ h₁) h
    x := mkApp2 op x₁ x
    y := mkApp2 op y₁ y
  return h

/-- A proof of `Bool.eq l r` by congruence from the triples `hs` (see `smtCongrUF`). -/
partial def smtCongr (l r : Expr) (hs : Array (Expr × Expr × Expr)) : MetaM Expr := do
  let lp := l.app2? ``Decidable.decide
  let rq := r.app2? ``Decidable.decide
  if let (some (p, hp), some (q, hq)) := (lp, rq) then
    -- Atoms, e.g., equalities and applications of Lean predicates, are reconstructed as `decide p`.
    let h ← smtCongr p q hs
    let inst ← Bool.decEqInst (.sort 0)
    return mkAppN (.const ``Bool.eq.decide_congr []) #[inst, p, q, hp, hq, h]
  else if l.isAppOfArity ``not 1 && hs.size == 2 then
    -- `(distinct a b)` is reconstructed as `!decide (a = b)`.
    mkBoolEqCongrArg (.const ``not []) l.appArg! r.appArg! (← smtCongr l.appArg! r.appArg! hs)
  else if isLeftAssocOp l.getAppFn.constName && hs.size > 2 then
    smtCongrLeftAssocOp l.appFn!.appFn! hs
  else if isRightAssocOp l.getAppFn.constName && hs.size > 2 then
    smtCongrRightAssocOp l.appFn!.appFn! hs
  else
    smtCongrUF l r hs
where
  isLeftAssocOp (n : Name) : Bool :=
    n == ``HAdd.hAdd || n == ``HSub.hSub || n == ``HMul.hMul || n == ``HDiv.hDiv || n == ``HMod.hMod
  isRightAssocOp (n : Name) : Bool :=
    n == ``and || n == ``or || n == ``xor || n == ``Bool.imp

namespace Tactic

/-- `smtCongr [h₁, …, hₙ]` proves `Bool.eq l r` by congruence from the hypotheses
`hᵢ : Bool.eq aᵢ bᵢ` for the arguments of `l` and `r`. -/
syntax (name := smtCongr) "smtCongr"  ("[" term,* "]")? : tactic

/-- The sides of a goal or hypothesis `Bool.eq a b`. -/
def getBoolEq! (e : Expr) : MetaM (Expr × Expr) := do
  let some (_, lhs, _) := (← Meta.whnfR e).eq? | throwNotBoolEq
  let some (p, _) := lhs.app2? ``Decidable.decide | throwNotBoolEq
  let some (_, a, b) := p.eq? | throwNotBoolEq
  return (a, b)
where
  throwNotBoolEq {α} : MetaM α := throwError "[smtCongr]: expected `Bool.eq a b`, got{indentExpr e}"

@[tactic smtCongr] def evalSmtCongr : Tactic := fun stx => withMainContext do
  let `(tactic| smtCongr [ $[$hs],* ]) := stx | throwError "[smtCongr]: invalid syntax"
  let hs ← hs.mapM fun h => do
    let h ← elabTerm h none
    let (a, b) ← getBoolEq! (← Meta.inferType h)
    return (a, b, h)
  let mv ← getMainGoal
  let (l, r) ← getBoolEq! (← mv.getType)
  mv.assign (← UF.smtCongr l r hs)
  replaceMainGoal []

example (a b c d : Int) : Bool.eq a b → Bool.eq c d → Bool.eq (a + c) (b + d) := by
  intros h₁ h₂
  smtCongr [h₁, h₂]

example (a b c d e f : Int) : Bool.eq a b → Bool.eq c d → Bool.eq e f →
    Bool.eq (a + c + e) (b + d + f) := by
  intros h₁ h₂ h₃
  smtCongr [h₁, h₂, h₃]

example (g : Int → Int → Int → Int) (a b c d e f : Int) : Bool.eq a b → Bool.eq c d → Bool.eq e f →
    Bool.eq (g a c e) (g b d f) := by
  intros h₁ h₂ h₃
  smtCongr [h₁, h₂, h₃]

example (a b c d e f : Bool) : Bool.eq a b → Bool.eq c d → Bool.eq e f →
    Bool.eq (a && (c && e)) (b && (d && f)) := by
  intros h₁ h₂ h₃
  smtCongr [h₁, h₂, h₃]

example {α : Type} [DecidableEq α] (c₁ c₂ : Bool) (x₁ x₂ y₁ y₂ : α) (h₁ : Bool.eq c₁ c₂)
    (h₂ : Bool.eq x₁ x₂) (h₃ : Bool.eq y₁ y₂) : Bool.eq (cond c₁ x₁ y₁) (cond c₂ x₂ y₂) := by
  smtCongr [h₁, h₂, h₃]

example (a b c d : Int) (h₁ : Bool.eq a b) (h₂ : Bool.eq c d) :
    Bool.eq (decide (a = c)) (decide (b = d)) := by
  smtCongr [h₁, h₂]

example (f : Prop → Int) (a b : Bool) (h : Bool.eq a b) :
    Bool.eq (f (a = true)) (f (b = true)) := by
  smtCongr [h]

example (f : Prop → Int) (p q : Prop) [Decidable p] [Decidable q]
    (h : Bool.eq (decide p) (decide q)) : Bool.eq (f p) (f q) := by
  smtCongr [h]

end Smt.Reconstruct.UF.Tactic
