/-
Copyright (c) 2021-2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

module

public import Lean.Meta.Tactic.Simp
public meta import Lean.Meta.Tactic.Simp
public import Qq
public meta import Qq
public import Smt.Preprocess.Embedding.Attribute
public meta import Smt.Preprocess.Embedding.Attribute
public import Smt.Reconstruct.Bool.Core
public meta import Smt.Reconstruct.Bool.Core

/-!
# Embedding propositions into Booleans

SMT-LIB's `Bool` sort is Lean's `Bool`: translation and proof reconstruction work with Boolean
formulas, and a proof of a formula `b` is a proof of `b = true`. The embedding turns propositions
into Booleans in two steps (see `Smt.Preprocess.embedding`):

1. The `embedding` theorems turn propositional variables `x : Prop` into Boolean ones `x : Bool`,
   whose occurrences become `x = true`, and likewise for the arguments and results of functions.
2. The `smt_decide` theorems turn every hypothesis `h : p` into `h' : b = true`, where the Boolean
   formula `b` is obtained by pushing `smtDecide p` into the connectives, quantifiers, and atoms of
   `p`:

| proposition    | Boolean formula                          |
|----------------|------------------------------------------|
| `¬p`, `p ∧ q`, `p ∨ q` | `!b`, `b₁ && b₂`, `b₁ \|\| b₂`   |
| `p → q`        | `b₁.smtImp b₂`                           |
| `p ↔ q`, `p = q` | `smtEq b₁ b₂`                          |
| `b = true`     | `b`                                      |
| `x = y`, `x < y`, … | `smtEq x y`, `smtLt x y`, …         |
| `∀ x, p x`     | `smtForall fun x => b x`                 |
| `∃ x, p x`     | `smtExists fun x => b x`                 |
| `if p then x else y` | `cond b x y`                       |
| `decide p`     | `b`                                      |
| other atom `p` | `smtDecide p`                            |

These are the Boolean formulas that proof reconstruction builds from SMT-LIB terms, so that the
formulas it reconstructs from cvc5's proofs are syntactically equal to the hypotheses.
-/

public section

namespace Smt.Preprocess.Embedding

/-! ### Propositional variables and functions -/

@[embedding ↓]
theorem forall_prop_as_bool {p : Prop → Prop} : (∀ x : Prop, p x) ↔ (∀ x : Bool, p (x = true)) :=
  ⟨fun h x => h _, fun h x => by
    have hx := h (smtDecide x)
    rwa [smtDecide_eq_true] at hx⟩

@[embedding ↓]
theorem exists_prop_as_bool {p : Prop → Prop} : (∃ x : Prop, p x) ↔ (∃ x : Bool, p (x = true)) :=
  ⟨fun ⟨x, hx⟩ => ⟨smtDecide x, by rwa [smtDecide_eq_true]⟩, fun ⟨_, hx⟩ => ⟨_, hx⟩⟩

@[embedding ↓]
theorem forall_prop_in_as_bool₁ {p : (Prop → α₁) → Prop} :
    (∀ f : Prop → α₁, p f) ↔ (∀ f : Bool → α₁, p fun x => f (smtDecide x)) := by
  constructor
  · intro h f
    apply h
  · intro h f
    have hf := h fun x => f (x = true)
    simp only [smtDecide_eq_true] at hf
    exact hf

@[embedding ↓]
theorem forall_prop_in_as_bool₂ {p : (α₁ → Prop → α₂) → Prop} :
    (∀ f : α₁ → Prop → α₂, p f) ↔ (∀ f : α₁ → Bool → α₂, p fun a₁ x => f a₁ (smtDecide x)) := by
  constructor
  · intro h f
    apply h
  · intro h f
    have hf := h fun a₁ x => f a₁ (x = true)
    simp only [smtDecide_eq_true] at hf
    exact hf

@[embedding ↓]
theorem forall_prop_in_as_bool₃ {p : (α₁ → α₂ → Prop → α₃) → Prop} :
    (∀ f : α₁ → α₂ → Prop → α₃, p f) ↔
    (∀ f : α₁ → α₂ → Bool → α₃, p fun a₁ a₂ x => f a₁ a₂ (smtDecide x)) := by
  constructor
  · intro h f
    apply h
  · intro h f
    have hf := h fun a₁ a₂ x => f a₁ a₂ (x = true)
    simp only [smtDecide_eq_true] at hf
    exact hf

@[embedding ↓]
theorem forall_prop_in_as_bool₄ {p : (α₁ → α₂ → α₃ → Prop → α₄) → Prop} :
    (∀ f : α₁ → α₂ → α₃ → Prop → α₄, p f) ↔
    (∀ f : α₁ → α₂ → α₃ → Bool → α₄, p fun a₁ a₂ a₃ x => f a₁ a₂ a₃ (smtDecide x)) := by
  constructor
  · intro h f
    apply h
  · intro h f
    have hf := h fun a₁ a₂ a₃ x => f a₁ a₂ a₃ (x = true)
    simp only [smtDecide_eq_true] at hf
    exact hf

@[embedding ↓]
theorem forall_prop_in_as_bool₅ {p : (α₁ → α₂ → α₃ → α₄ → Prop → α₅) → Prop} :
    (∀ f : α₁ → α₂ → α₃ → α₄ → Prop → α₅, p f) ↔
    (∀ f : α₁ → α₂ → α₃ → α₄ → Bool → α₅, p fun a₁ a₂ a₃ a₄ x => f a₁ a₂ a₃ a₄ (smtDecide x)) := by
  constructor
  · intro h f
    apply h
  · intro h f
    have hf := h fun a₁ a₂ a₃ a₄ x => f a₁ a₂ a₃ a₄ (x = true)
    simp only [smtDecide_eq_true] at hf
    exact hf

@[embedding ↓]
theorem forall_prop_in_as_bool₆ {p : (α₁ → α₂ → α₃ → α₄ → α₅ → Prop → α₆) → Prop} :
    (∀ f : α₁ → α₂ → α₃ → α₄ → α₅ → Prop → α₆, p f) ↔
    (∀ f : α₁ → α₂ → α₃ → α₄ → α₅ → Bool → α₆,
      p fun a₁ a₂ a₃ a₄ a₅ x => f a₁ a₂ a₃ a₄ a₅ (smtDecide x)) := by
  constructor
  · intro h f
    apply h
  · intro h f
    have hf := h fun a₁ a₂ a₃ a₄ a₅ x => f a₁ a₂ a₃ a₄ a₅ (x = true)
    simp only [smtDecide_eq_true] at hf
    exact hf

@[embedding ↓]
theorem forall_prop_out_as_bool₁ {p : (α₁ → Prop) → Prop} :
    (∀ f : α₁ → Prop, p f) ↔ (∀ f : α₁ → Bool, p fun a₁ => f a₁ = true) := by
  constructor
  · intro h f
    apply h
  · intro h f
    have hf := h fun a₁ => smtDecide (f a₁)
    simp only [smtDecide_eq_true] at hf
    exact hf

@[embedding ↓]
theorem forall_prop_out_as_bool₂ {p : (α₁ → α₂ → Prop) → Prop} :
    (∀ f : α₁ → α₂ → Prop, p f) ↔ (∀ f : α₁ → α₂ → Bool, p fun a₁ a₂ => f a₁ a₂ = true) := by
  constructor
  · intro h f
    apply h
  · intro h f
    have hf := h fun a₁ a₂ => smtDecide (f a₁ a₂)
    simp only [smtDecide_eq_true] at hf
    exact hf

@[embedding ↓]
theorem forall_prop_out_as_bool₃ {p : (α₁ → α₂ → α₃ → Prop) → Prop} :
    (∀ f : α₁ → α₂ → α₃ → Prop, p f) ↔
    (∀ f : α₁ → α₂ → α₃ → Bool, p fun a₁ a₂ a₃ => f a₁ a₂ a₃ = true) := by
  constructor
  · intro h f
    apply h
  · intro h f
    have hf := h fun a₁ a₂ a₃ => smtDecide (f a₁ a₂ a₃)
    simp only [smtDecide_eq_true] at hf
    exact hf

@[embedding ↓]
theorem forall_prop_out_as_bool₄ {p : (α₁ → α₂ → α₃ → α₄ → Prop) → Prop} :
    (∀ f : α₁ → α₂ → α₃ → α₄ → Prop, p f) ↔
    (∀ f : α₁ → α₂ → α₃ → α₄ → Bool, p fun a₁ a₂ a₃ a₄ => f a₁ a₂ a₃ a₄ = true) := by
  constructor
  · intro h f
    apply h
  · intro h f
    have hf := h fun a₁ a₂ a₃ a₄ => smtDecide (f a₁ a₂ a₃ a₄)
    simp only [smtDecide_eq_true] at hf
    exact hf

@[embedding ↓]
theorem forall_prop_out_as_bool₅ {p : (α₁ → α₂ → α₃ → α₄ → α₅ → Prop) → Prop} :
    (∀ f : α₁ → α₂ → α₃ → α₄ → α₅ → Prop, p f) ↔
    (∀ f : α₁ → α₂ → α₃ → α₄ → α₅ → Bool, p fun a₁ a₂ a₃ a₄ a₅ => f a₁ a₂ a₃ a₄ a₅ = true) := by
  constructor
  · intro h f
    apply h
  · intro h f
    have hf := h fun a₁ a₂ a₃ a₄ a₅ => smtDecide (f a₁ a₂ a₃ a₄ a₅)
    simp only [smtDecide_eq_true] at hf
    exact hf

@[embedding ↓]
theorem forall_prop_out_as_bool₆ {p : (α₁ → α₂ → α₃ → α₄ → α₅ → α₆ → Prop) → Prop} :
    (∀ f : α₁ → α₂ → α₃ → α₄ → α₅ → α₆ → Prop, p f) ↔
    (∀ f : α₁ → α₂ → α₃ → α₄ → α₅ → α₆ → Bool,
      p fun a₁ a₂ a₃ a₄ a₅ a₆ => f a₁ a₂ a₃ a₄ a₅ a₆ = true) := by
  constructor
  · intro h f
    apply h
  · intro h f
    have hf := h fun a₁ a₂ a₃ a₄ a₅ a₆ => smtDecide (f a₁ a₂ a₃ a₄ a₅ a₆)
    simp only [smtDecide_eq_true] at hf
    exact hf

/-! ### Propositions as Boolean formulas -/

universe u

variable {p q : Prop} {α : Sort u} {β : Type u}

@[smt_decide ↓] theorem smtDecide_True : smtDecide True = true := by simp [smtDecide]
@[smt_decide ↓] theorem smtDecide_False : smtDecide False = false := by simp [smtDecide]

@[smt_decide ↓] theorem smtDecide_not : smtDecide (¬p) = !smtDecide p := by
  apply Bool.eq_iff_iff.mpr; simp
@[smt_decide ↓] theorem smtDecide_and : smtDecide (p ∧ q) = (smtDecide p && smtDecide q) := by
  apply Bool.eq_iff_iff.mpr; simp
@[smt_decide ↓] theorem smtDecide_or : smtDecide (p ∨ q) = (smtDecide p || smtDecide q) := by
  apply Bool.eq_iff_iff.mpr; simp
@[smt_decide ↓] theorem smtDecide_imp : smtDecide (p → q) = (smtDecide p).smtImp (smtDecide q) := by
  apply Bool.eq_iff_iff.mpr; simp
theorem smtDecide_eq_smtDecide : (smtDecide p = smtDecide q) ↔ (p ↔ q) := by
  rw [Bool.eq_iff_iff, smtDecide_eq_true, smtDecide_eq_true]

@[smt_decide ↓] theorem smtDecide_iff : smtDecide (p ↔ q) = smtEq (smtDecide p) (smtDecide q) := by
  apply Bool.eq_iff_iff.mpr; rw [smtDecide_eq_true, smtEq_eq_true, smtDecide_eq_smtDecide]
@[smt_decide ↓ high] theorem smtDecide_prop_eq :
    smtDecide (p = q) = smtEq (smtDecide p) (smtDecide q) := by
  apply Bool.eq_iff_iff.mpr; rw [smtDecide_eq_true, smtEq_eq_true, smtDecide_eq_smtDecide]
  exact ⟨fun h => h ▸ Iff.rfl, propext⟩

@[smt_decide ↓ high] theorem smtDecide_bool_eq_true {b : Bool} : smtDecide (b = true) = b := by
  cases b <;> simp
@[smt_decide ↓ high] theorem smtDecide_bool_eq_false {b : Bool} : smtDecide (b = false) = !b := by
  cases b <;> simp
@[smt_decide ↓ high] theorem smtDecide_true_eq_bool {b : Bool} : smtDecide (true = b) = b := by
  cases b <;> simp
@[smt_decide ↓ high] theorem smtDecide_false_eq_bool {b : Bool} : smtDecide (false = b) = !b := by
  cases b <;> simp

@[smt_decide ↓] theorem smtDecide_eq {a b : α} : smtDecide (a = b) = smtEq a b := rfl
@[smt_decide ↓] theorem smtDecide_ne {a b : α} : smtDecide (a ≠ b) = !smtEq a b := by
  apply Bool.eq_iff_iff.mpr; simp
@[smt_decide ↓] theorem smtDecide_lt [LT β] {x y : β} : smtDecide (x < y) = smtLt x y := rfl
@[smt_decide ↓] theorem smtDecide_le [LE β] {x y : β} : smtDecide (x ≤ y) = smtLe x y := rfl
@[smt_decide ↓] theorem smtDecide_gt [LT β] {x y : β} : smtDecide (x > y) = smtGt x y := rfl
@[smt_decide ↓] theorem smtDecide_ge [LE β] {x y : β} : smtDecide (x ≥ y) = smtGe x y := rfl

@[smt_decide ↓] theorem smtDecide_ite {c : Prop} {h : Decidable c} :
    smtDecide (@ite Prop c h p q) = cond (smtDecide c) (smtDecide p) (smtDecide q) := by
  by_cases hc : c
  · simp [hc]
  · simp [hc]

attribute [smt_decide ↓] decide_eq_smtDecide

theorem smtDecide_forall {P : α → Prop} : smtDecide (∀ x, P x) = smtForall fun x => smtDecide (P x) := by
  simp only [smtForall, smtDecide_eq_true]

theorem smtDecide_exists {P : α → Prop} : smtDecide (∃ x, P x) = smtExists fun x => smtDecide (P x) := by
  simp only [smtExists, smtDecide_eq_true]

theorem smtDecide_forall_prop {P : Prop → Prop} :
    smtDecide (∀ x, P x) = smtDecide (∀ x : Bool, P (x = true)) := by
  rw [propext forall_prop_as_bool]

theorem smtDecide_exists_prop {P : Prop → Prop} :
    smtDecide (∃ x, P x) = smtDecide (∃ x : Bool, P (x = true)) := by
  rw [propext exists_prop_as_bool]

theorem ite_eq_cond {c : Prop} {h : Decidable c} {x y : α} :
    @ite α c h x y = cond (smtDecide c) x y := by
  by_cases hc : c
  · simp [hc]
  · simp [hc]

end Smt.Preprocess.Embedding

public meta section

namespace Smt.Preprocess.Embedding

open Lean Meta Simp Qq

/-- Turn `smtDecide (∀ x, p x)` into `smtForall fun x => smtDecide (p x)`. Propositional variables
`x : Prop` become Boolean ones, and quantifiers over proofs are atoms. -/
simproc ↓ [smt_decide] smtDecideForall (smtDecide _) := fun e => do
  let_expr smtDecide p := e | return .continue
  let .forallE n t body bi := p | return .continue
  -- `p → q` is an implication, see `smtDecide_imp`.
  if !body.hasLooseBVars && (← isProp t) then return .continue
  let lp := Expr.lam n t body bi
  if t.isProp then
    let lp : Q(Prop → Prop) ← pure lp
    return .visit { expr := q(smtDecide (∀ x : Bool, $lp (x = true))),
                    proof? := q(smtDecide_forall_prop (P := $lp)) }
  if ← isProp t then return .continue
  let u ← getLevel t
  let lb := Expr.lam n t (mkApp (.const ``smtDecide []) body) bi
  return .visit { expr := mkApp2 (.const ``smtForall [u]) t lb,
                  proof? := mkApp2 (.const ``smtDecide_forall [u]) t lp }

/-- Turn `smtDecide (∃ x, p x)` into `smtExists fun x => smtDecide (p x)`. Propositional variables
`x : Prop` become Boolean ones, and quantifiers over proofs are atoms. -/
simproc ↓ [smt_decide] smtDecideExists (smtDecide (Exists _)) := fun e => do
  let_expr smtDecide p := e | return .continue
  let_expr Exists t lp := p | return .continue
  let .lam n _ body bi := lp | return .continue
  if t.isProp then
    let lp : Q(Prop → Prop) ← pure lp
    return .visit { expr := q(smtDecide (∃ x : Bool, $lp (x = true))),
                    proof? := q(smtDecide_exists_prop (P := $lp)) }
  if ← isProp t then return .continue
  let u ← getLevel t
  let lb := Expr.lam n t (mkApp (.const ``smtDecide []) body) bi
  return .visit { expr := mkApp2 (.const ``smtExists [u]) t lb,
                  proof? := mkApp2 (.const ``smtDecide_exists [u]) t lp }

/-- Replace `if c then x else y` by `cond (smtDecide c) x y` for non-propositional `x` and `y`. -/
simproc ↓ [smt_decide] iteToCond (ite _ _ _) := fun e => do
  let_expr ite α c h x y := e | return .continue
  if α.isProp then return .continue
  let u ← getLevel α
  return .visit { expr := mkApp4 (.const ``cond [u]) α (mkApp (.const ``smtDecide []) c) x y,
                  proof? := mkAppN (.const ``ite_eq_cond [u]) #[α, c, h, x, y] }

end Smt.Preprocess.Embedding
