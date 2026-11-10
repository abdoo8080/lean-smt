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

public import Smt.Reconstruct.Bool.Lemmas
public meta import Smt.Reconstruct.Bool.Lemmas
public import Smt.Reconstruct.Prop.Core
public meta import Smt.Reconstruct.Prop.Core

public section

namespace Smt.Reconstruct.UF

theorem ite_congr' {α} [Decidable c₁] [Decidable c₂] {x₁ x₂ y₁ y₂ : α} (h₁ : c₁ = c₂) (h₂ : x₁ = x₂) (h₃ : y₁ = y₂) : ite c₁ x₁ y₁ = ite c₂ x₂ y₂ := by
  congr

end Smt.Reconstruct.UF

public meta section

namespace Smt.Reconstruct.UF

open Lean Elab Tactic
open Qq

def smtCongrArrow (mv : MVarId) (hs : Array Expr) : MetaM Unit := do
  let f := fun h₁ h₂ => do
    let (_, (a₁ : Q(Prop)), (b₁ : Q(Prop))) := (← Meta.inferType h₁).eq?.get!
    let (_, (a₂ : Q(Prop)), (b₂ : Q(Prop))) := (← Meta.inferType h₂).eq?.get!
    let h₁ : Q($a₁ = $b₁) ← pure h₁
    let h₂ : Q($a₂ = $b₂) ← pure h₂
    return (q(implies_congr $h₁ $h₂))
  let h ← hs[:hs.size - 1].foldrM f hs[hs.size - 1]!
  mv.assign h

def smtCongrIte (mv : MVarId) (e₁ e₂ : Expr) (hs : Array Expr) : MetaM Unit := do
  let as₁ := e₁.getAppArgs
  let as₂ := e₂.getAppArgs
  let u ← Meta.getLevel as₁[0]!
  let α : Q(Sort u) ← pure as₁[0]!
  let (c₁, c₂) : Q(Prop) × Q(Prop) := (as₁[1]!, as₂[1]!)
  let (_, _) : Q(Decidable $c₁) × Q(Decidable $c₂) := (as₁[2]!, as₂[2]!)
  let (x₁, x₂) : Q($α) × Q($α) := (as₁[3]!, as₂[3]!)
  let (y₁, y₂) : Q($α) × Q($α) := (as₁[4]!, as₂[4]!)
  let h₁ : Q($c₁ = $c₂) ← pure hs[0]!
  let h₂ : Q($x₁ = $x₂) ← pure hs[1]!
  let h₃ : Q($y₁ = $y₂) ← pure hs[2]!
  mv.assign q(ite_congr' (α := $α) $h₁ $h₂ $h₃)

def smtCongrUF (mv : MVarId) (e₁ e₂ : Expr) (hs : Array Expr) : MetaM Unit := do
  let n := hs.size
  let f := e₁.getBoundedAppFn n
  let hs := (e₁.getBoundedAppArgs n).zip ((e₂.getBoundedAppArgs n).zip hs)
  let buildProof := fun (f₁, f₂, h₁) (a₁, a₂, h₂) => do
    let some (α, β) := (← Meta.inferType f₁).arrow? | throwError "[smt_congr]: expected function type"
    let .sort u ← Meta.inferType α | throwError "[smt_congr]: expected the type of {α} to be a sort"
    let .sort v ← Meta.inferType β | throwError "[smt_congr]: expected the type of {β} to be a sort"
    let α : Q(Sort u) ← pure α
    let β : Q(Sort v) ← pure β
    let a₁ : Q($α) ← pure a₁
    let a₂ : Q($α) ← pure a₂
    let f₁ : Q($α → $β) ← pure f₁
    let f₂ : Q($α → $β) ← pure f₂
    let h₁ : Q($f₁ = $f₂) ← pure h₁
    let h₂ : Q($a₁ = $a₂) ← propArgEq α h₂
    return (q($f₁ $a₁), q($f₂ $a₂), q(congr $h₁ $h₂))
  let (_, _, h) ← hs.foldlM buildProof (f, f, ← Meta.mkEqRefl f)
  mv.assign h
where
  /-- A proposition passed to a Lean function is an SMT-LIB Boolean `b`, reconstructed as `p` if `b`
  is `smtDecide p` and as `b = true` otherwise. Turn the proof `h : b₁ = b₂` of the equality of the
  Booleans into a proof of the equality of the propositions. -/
  propArgEq (α : Expr) (h : Expr) : MetaM Expr := do
    if !α.isProp then return h
    let some (γ, b₁, b₂) := (← Meta.inferType h).eq? | return h
    if !γ.isConstOf ``Bool then return h
    let b₁ : Q(Bool) ← pure b₁
    let b₂ : Q(Bool) ← pure b₂
    let h : Q($b₁ = $b₂) ← pure h
    match b₁.app1? ``smtDecide, b₂.app1? ``smtDecide with
    | some p, some q =>
      let p : Q(Prop) ← pure p
      let q : Q(Prop) ← pure q
      let h : Q(smtDecide $p = smtDecide $q) ← pure h
      return q(Smt.Reconstruct.Bool.eq_of_smtDecide_eq $h)
    | _, _ => return q(congrArg (· = true) $h)

def smtCongrLeftAssocOp (mv : MVarId) (op : Expr) (hs : Array Expr) : MetaM Unit := do
  let ((α : Q(Type)), _) := (← Meta.inferType op).arrow?.get!
  let op : (Q($α → $α → $α)) ← pure op
  let (_, x₁, x₂) := (← Meta.inferType hs[0]!).eq?.get!
  let f := fun ((x₁ : Q($α)), (x₂ : Q($α)), (h₁ : Q($x₁ = $x₂))) h₂ => do
    let (_, (y₁ : Q($α)), (y₂ : Q($α))) := (← Meta.inferType h₂).eq?.get!
    let h₂ : Q($y₁ = $y₂) ← pure h₂
    return (q($op $x₁ $y₁), q($op $x₂ $y₂), q(congr (congrArg $op $h₁) $h₂))
  let (_, _, h) ← hs[1:].foldlM f (x₁, x₂, hs[0]!)
  mv.assign h

def smtCongrRightAssocOp (mv : MVarId) (op : Expr) (hs : Array Expr) : MetaM Unit := do
  let ((α : Q(Type)), _) := (← Meta.inferType op).arrow?.get!
  let op : (Q($α → $α → $α)) ← pure op
  let (_, y₁, y₂) := (← Meta.inferType hs[hs.size - 1]!).eq?.get!
  let f := fun h₁ ((y₁ : Q($α)), (y₂ : Q($α)), (h₂ : Q($y₁ = $y₂))) => do
    let (_, (x₁ : Q($α)), (x₂ : Q($α))) := (← Meta.inferType h₁).eq?.get!
    let h₁ : Q($x₁ = $x₂) ← pure h₁
    return (q($op $x₁ $y₁), q($op $x₂ $y₂), q(congr (congrArg $op $h₁) $h₂))
  let (_, _, h) ← hs[:hs.size - 1].foldrM f (y₁, y₂, hs[hs.size - 1]!)
  mv.assign h

partial def smtCongr (mv : MVarId) (hs : Array Expr) : MetaM Unit := mv.withContext do
  let some (_, l, r) := (← mv.getType).eq? | throwError "[smt_congr]: target is not an equality: {← mv.getType}"
  if l.isArrow then
    smtCongrArrow mv hs
  else if l.isAppOfArity ``smtDecide 1 then
    -- Applications of Lean predicates `p a` are reconstructed as `smtDecide (p a)`.
    let p : Q(Prop) ← pure l.appArg!
    let q : Q(Prop) ← pure r.appArg!
    let h : Q($p = $q) ← Meta.mkFreshExprMVar q($p = $q)
    smtCongr h.mvarId! hs
    mv.assign q(congrArg smtDecide $h)
  else if l.isAppOfArity ``not 1 && hs.size == 2 then
    -- `(distinct a b)` is reconstructed as `!smtEq a b`.
    let b₁ : Q(Bool) ← pure l.appArg!
    let b₂ : Q(Bool) ← pure r.appArg!
    let h : Q($b₁ = $b₂) ← Meta.mkFreshExprMVar q($b₁ = $b₂)
    smtCongrUF h.mvarId! b₁ b₂ hs
    mv.assign q(congrArg not $h)
  else if l.isAppOf ``ite then
    smtCongrIte mv l r hs
  else if isLeftAssocOp l.getAppFn.constName then
    smtCongrLeftAssocOp mv l.appFn!.appFn! hs
  else if isRightAssocOp l.getAppFn.constName && l.getAppNumArgs == 2 then
    smtCongrRightAssocOp mv l.appFn!.appFn! hs
  else
    smtCongrUF mv l r hs
where
  isLeftAssocOp (n : Name) : Bool :=
    n == ``HAdd.hAdd || n == ``HSub.hSub || n == ``HMul.hMul || n == ``HDiv.hDiv || n == ``HMod.hMod ||
    n == ``HAnd.hAnd || n == ``HOr.hOr || n == ``HXor.hXor
  isRightAssocOp (n : Name) : Bool :=
    n == ``And || n == ``Or || n == ``Iff || n == ``XOr ||
    n == ``and || n == ``or || n == ``xor || n == ``Bool.smtImp

namespace Tactic

syntax (name := smtCongr) "smtCongr"  ("[" term,* "]")? : tactic

def termToSyntax : Term → TacticM Syntax := fun t => pure t

def parseSmtCongr : Syntax → TacticM (Array Expr)
  | `(tactic| smtCongr  [ $[$hs],* ]) => withMainContext do
    let hs' : Array Syntax ← hs.mapM termToSyntax
    hs'.mapM (elabTerm · none)
  | _ => throwError "[smtCongr]: invalid Syntax"

@[tactic smtCongr] def evalSmtCongr : Tactic := fun stx => do
  let es ← parseSmtCongr stx
  UF.smtCongr (← getMainGoal) es

example (a b c d : Int) : a = b → c = d → a + c = b + d := by
  intros h₁ h₂
  smtCongr [h₁, h₂]

example (a b c d e f : Int) : a = b → c = d → e = f → a + c + e = b + d + f := by
  intros h₁ h₂ h₃
  smtCongr [h₁, h₂, h₃]

example (g : Int → Int → Int → Int) (a b c d e f : Int) : a = b → c = d → e = f → g a c e = g b d f := by
  intros h₁ h₂ h₃
  smtCongr [h₁, h₂, h₃]

example (a b c d : Prop) : a = b → c = d → (a ∧ c) = (b ∧ d) := by
  intros h₁ h₂
  smtCongr [h₁, h₂]

example (a b c d e f : Prop) : a = b → c = d → e = f → (a ∧ c ∧ e) = (b ∧ d ∧ f) := by
  intros h₁ h₂ h₃
  smtCongr [h₁, h₂, h₃]

example (a b c d e f : Prop) : a = b → c = d → e = f → (a → c → e) = (b → d → f) := by
  intros h₁ h₂ h₃
  smtCongr [h₁, h₂, h₃]

example [Decidable c₁] [Decidable c₂] {x₁ x₂ y₁ y₂ : α} (h₁ : c₁ = c₂) (h₂ : x₁ = x₂) (h₃ : y₁ = y₂) : ite c₁ x₁ y₁ = ite c₂ x₂ y₂ := by
  smtCongr [h₁, h₂, h₃]

end Smt.Reconstruct.UF.Tactic
