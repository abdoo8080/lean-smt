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
public meta import Smt.Reconstruct.Bool.Bridge
public import Smt.Reconstruct.BitVec.Core
public import Smt.Reconstruct.Int.Core

/-!
# Embedding propositions into Booleans

SMT-LIB's `Bool` sort is Lean's `Bool`: translation and proof reconstruction work with Boolean
formulas, and a proof of a formula `b` is a proof of `b = true`. The embedding turns propositions
into Booleans in two steps (see `Smt.Preprocess.embedding`):

1. The `embedding` theorems turn propositional variables `x : Prop` into Boolean ones `x : Bool`,
   whose occurrences become `x = true`, and likewise for the arguments and results of functions.
2. The `smt_decide` theorems turn every hypothesis `h : p` into `h' : b = true`, where the Boolean
   formula `b` is obtained by pushing `decide p` into the connectives, quantifiers, and atoms of `p`:

| proposition    | Boolean formula                          |
|----------------|------------------------------------------|
| `¬p`, `p ∧ q`, `p ∨ q` | `!b`, `b₁ && b₂`, `b₁ \|\| b₂`   |
| `p → q`        | `b₁.imp b₂`                              |
| `p ↔ q`, `p = q` | `b₁ == b₂`                             |
| `b = true`     | `b`                                      |
| `x = y`, `x ≠ y` | `x == y`, `!(x == y)`                  |
| `∀ x, p x`     | `Bool.forall fun x => b x`               |
| `∃ x, p x`     | `Bool.exists fun x => b x`               |
| `if p then x else y` | `cond b x y`                       |
| other atom `p` | `decide p`                               |

The equalities `x == y` and the atoms `decide p` use the same instances as proof reconstruction (see
`Smt.Reconstruct.Bool.mkBEq` and `Smt.Reconstruct.Bool.decideOf`).

These are the Boolean formulas that proof reconstruction builds from SMT-LIB terms, so that the
formulas it reconstructs from cvc5's proofs are syntactically equal to the hypotheses.
-/

public section

namespace Smt.Preprocess.Embedding

/-! ### Propositional variables and functions -/

@[embedding ↓]
theorem forall_prop_as_bool {p : Prop → Prop} : (∀ x : Prop, p x) ↔ (∀ x : Bool, p (x = true)) :=
  ⟨fun h x => h _, fun h x => by
    have hx := h (@decide x (Classical.propDecidable x))
    rwa [@decide_eq_true_eq x (Classical.propDecidable x)] at hx⟩

@[embedding ↓]
theorem exists_prop_as_bool {p : Prop → Prop} : (∃ x : Prop, p x) ↔ (∃ x : Bool, p (x = true)) :=
  ⟨fun ⟨x, hx⟩ => ⟨@decide x (Classical.propDecidable x), by rwa [@decide_eq_true_eq x (Classical.propDecidable x)]⟩,
   fun ⟨_, hx⟩ => ⟨_, hx⟩⟩

@[embedding ↓]
theorem forall_prop_in_as_bool₁ {p : (Prop → α₁) → Prop} :
    (∀ f : Prop → α₁, p f) ↔ (∀ f : Bool → α₁, p fun x => f (@decide x (Classical.propDecidable x))) := by
  constructor
  · intro h f
    apply h
  · intro h f
    have hf := h fun x => f (x = true)
    simp only [decide_eq_true_eq] at hf
    exact hf

@[embedding ↓]
theorem forall_prop_in_as_bool₂ {p : (α₁ → Prop → α₂) → Prop} :
    (∀ f : α₁ → Prop → α₂, p f) ↔ (∀ f : α₁ → Bool → α₂, p fun a₁ x => f a₁ (@decide x (Classical.propDecidable x))) := by
  constructor
  · intro h f
    apply h
  · intro h f
    have hf := h fun a₁ x => f a₁ (x = true)
    simp only [decide_eq_true_eq] at hf
    exact hf

@[embedding ↓]
theorem forall_prop_in_as_bool₃ {p : (α₁ → α₂ → Prop → α₃) → Prop} :
    (∀ f : α₁ → α₂ → Prop → α₃, p f) ↔
    (∀ f : α₁ → α₂ → Bool → α₃, p fun a₁ a₂ x => f a₁ a₂ (@decide x (Classical.propDecidable x))) := by
  constructor
  · intro h f
    apply h
  · intro h f
    have hf := h fun a₁ a₂ x => f a₁ a₂ (x = true)
    simp only [decide_eq_true_eq] at hf
    exact hf

@[embedding ↓]
theorem forall_prop_in_as_bool₄ {p : (α₁ → α₂ → α₃ → Prop → α₄) → Prop} :
    (∀ f : α₁ → α₂ → α₃ → Prop → α₄, p f) ↔
    (∀ f : α₁ → α₂ → α₃ → Bool → α₄, p fun a₁ a₂ a₃ x => f a₁ a₂ a₃ (@decide x (Classical.propDecidable x))) := by
  constructor
  · intro h f
    apply h
  · intro h f
    have hf := h fun a₁ a₂ a₃ x => f a₁ a₂ a₃ (x = true)
    simp only [decide_eq_true_eq] at hf
    exact hf

@[embedding ↓]
theorem forall_prop_in_as_bool₅ {p : (α₁ → α₂ → α₃ → α₄ → Prop → α₅) → Prop} :
    (∀ f : α₁ → α₂ → α₃ → α₄ → Prop → α₅, p f) ↔
    (∀ f : α₁ → α₂ → α₃ → α₄ → Bool → α₅, p fun a₁ a₂ a₃ a₄ x => f a₁ a₂ a₃ a₄ (@decide x (Classical.propDecidable x))) := by
  constructor
  · intro h f
    apply h
  · intro h f
    have hf := h fun a₁ a₂ a₃ a₄ x => f a₁ a₂ a₃ a₄ (x = true)
    simp only [decide_eq_true_eq] at hf
    exact hf

@[embedding ↓]
theorem forall_prop_in_as_bool₆ {p : (α₁ → α₂ → α₃ → α₄ → α₅ → Prop → α₆) → Prop} :
    (∀ f : α₁ → α₂ → α₃ → α₄ → α₅ → Prop → α₆, p f) ↔
    (∀ f : α₁ → α₂ → α₃ → α₄ → α₅ → Bool → α₆,
      p fun a₁ a₂ a₃ a₄ a₅ x => f a₁ a₂ a₃ a₄ a₅ (@decide x (Classical.propDecidable x))) := by
  constructor
  · intro h f
    apply h
  · intro h f
    have hf := h fun a₁ a₂ a₃ a₄ a₅ x => f a₁ a₂ a₃ a₄ a₅ (x = true)
    simp only [decide_eq_true_eq] at hf
    exact hf

@[embedding ↓]
theorem forall_prop_out_as_bool₁ {p : (α₁ → Prop) → Prop} :
    (∀ f : α₁ → Prop, p f) ↔ (∀ f : α₁ → Bool, p fun a₁ => f a₁ = true) := by
  constructor
  · intro h f
    apply h
  · intro h f
    have hf := h fun a₁ => @decide (f a₁) (Classical.propDecidable _)
    simp only [decide_eq_true_eq] at hf
    exact hf

@[embedding ↓]
theorem forall_prop_out_as_bool₂ {p : (α₁ → α₂ → Prop) → Prop} :
    (∀ f : α₁ → α₂ → Prop, p f) ↔ (∀ f : α₁ → α₂ → Bool, p fun a₁ a₂ => f a₁ a₂ = true) := by
  constructor
  · intro h f
    apply h
  · intro h f
    have hf := h fun a₁ a₂ => @decide (f a₁ a₂) (Classical.propDecidable _)
    simp only [decide_eq_true_eq] at hf
    exact hf

@[embedding ↓]
theorem forall_prop_out_as_bool₃ {p : (α₁ → α₂ → α₃ → Prop) → Prop} :
    (∀ f : α₁ → α₂ → α₃ → Prop, p f) ↔
    (∀ f : α₁ → α₂ → α₃ → Bool, p fun a₁ a₂ a₃ => f a₁ a₂ a₃ = true) := by
  constructor
  · intro h f
    apply h
  · intro h f
    have hf := h fun a₁ a₂ a₃ => @decide (f a₁ a₂ a₃) (Classical.propDecidable _)
    simp only [decide_eq_true_eq] at hf
    exact hf

@[embedding ↓]
theorem forall_prop_out_as_bool₄ {p : (α₁ → α₂ → α₃ → α₄ → Prop) → Prop} :
    (∀ f : α₁ → α₂ → α₃ → α₄ → Prop, p f) ↔
    (∀ f : α₁ → α₂ → α₃ → α₄ → Bool, p fun a₁ a₂ a₃ a₄ => f a₁ a₂ a₃ a₄ = true) := by
  constructor
  · intro h f
    apply h
  · intro h f
    have hf := h fun a₁ a₂ a₃ a₄ => @decide (f a₁ a₂ a₃ a₄) (Classical.propDecidable _)
    simp only [decide_eq_true_eq] at hf
    exact hf

@[embedding ↓]
theorem forall_prop_out_as_bool₅ {p : (α₁ → α₂ → α₃ → α₄ → α₅ → Prop) → Prop} :
    (∀ f : α₁ → α₂ → α₃ → α₄ → α₅ → Prop, p f) ↔
    (∀ f : α₁ → α₂ → α₃ → α₄ → α₅ → Bool, p fun a₁ a₂ a₃ a₄ a₅ => f a₁ a₂ a₃ a₄ a₅ = true) := by
  constructor
  · intro h f
    apply h
  · intro h f
    have hf := h fun a₁ a₂ a₃ a₄ a₅ => @decide (f a₁ a₂ a₃ a₄ a₅) (Classical.propDecidable _)
    simp only [decide_eq_true_eq] at hf
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
    have hf := h fun a₁ a₂ a₃ a₄ a₅ a₆ => @decide (f a₁ a₂ a₃ a₄ a₅ a₆) (Classical.propDecidable _)
    simp only [decide_eq_true_eq] at hf
    exact hf

/-! ### Propositions as Boolean formulas

The theorems push `decide` into propositions. Their right-hand sides decide propositions classically;
then the simproc `decideInstance` replaces the classical instances by synthesized ones, and the
simproc `decideEq` decides equalities with `==`. -/

universe u

variable {p q : Prop} {α : Sort u}

@[smt_decide ↓] theorem decide_True' {h : Decidable True} : @decide True h = true := by simp
@[smt_decide ↓] theorem decide_False' {h : Decidable False} : @decide False h = false := by simp

@[smt_decide ↓] theorem decide_not' {h : Decidable (¬p)} :
    @decide (¬p) h = !@decide p (Classical.propDecidable p) := by
  apply Bool.eq_iff_iff.mpr; simp
@[smt_decide ↓] theorem decide_and' {h : Decidable (p ∧ q)} :
    @decide (p ∧ q) h = (@decide p (Classical.propDecidable p) && @decide q (Classical.propDecidable q)) := by
  apply Bool.eq_iff_iff.mpr; simp
@[smt_decide ↓] theorem decide_or' {h : Decidable (p ∨ q)} :
    @decide (p ∨ q) h = (@decide p (Classical.propDecidable p) || @decide q (Classical.propDecidable q)) := by
  apply Bool.eq_iff_iff.mpr; simp
@[smt_decide ↓] theorem decide_imp' {h : Decidable (p → q)} :
    @decide (p → q) h = (@decide p (Classical.propDecidable p)).imp (@decide q (Classical.propDecidable q)) := by
  apply Bool.eq_iff_iff.mpr; simp
@[smt_decide ↓] theorem decide_iff' {h : Decidable (p ↔ q)} :
    @decide (p ↔ q) h = (@decide p (Classical.propDecidable p) == @decide q (Classical.propDecidable q)) := by
  apply Bool.eq_iff_iff.mpr; simp
@[smt_decide ↓ high] theorem decide_prop_eq {h : Decidable (p = q)} :
    @decide (p = q) h = (@decide p (Classical.propDecidable p) == @decide q (Classical.propDecidable q)) := by
  apply Bool.eq_iff_iff.mpr; simp only [decide_eq_true_eq, beq_iff_eq, decide_eq_decide]
  exact ⟨fun h => h ▸ Iff.rfl, propext⟩

@[smt_decide ↓ high] theorem decide_bool_eq_true {b : Bool} {h : Decidable (b = true)} :
    @decide (b = true) h = b := by
  cases b <;> simp
@[smt_decide ↓ high] theorem decide_bool_eq_false {b : Bool} {h : Decidable (b = false)} :
    @decide (b = false) h = !b := by
  cases b <;> simp
@[smt_decide ↓ high] theorem decide_true_eq_bool {b : Bool} {h : Decidable (true = b)} :
    @decide (true = b) h = b := by
  cases b <;> simp
@[smt_decide ↓ high] theorem decide_false_eq_bool {b : Bool} {h : Decidable (false = b)} :
    @decide (false = b) h = !b := by
  cases b <;> simp

@[smt_decide ↓] theorem decide_ne' {a b : α} {h : Decidable (a ≠ b)} :
    @decide (a ≠ b) h = !@decide (a = b) (Classical.propDecidable (a = b)) := by
  apply Bool.eq_iff_iff.mpr; simp

@[smt_decide ↓] theorem decide_ite' {c : Prop} {hc : Decidable c} {h : Decidable (@ite Prop c hc p q)} :
    @decide (@ite Prop c hc p q) h =
      cond (@decide c hc) (@decide p (Classical.propDecidable p)) (@decide q (Classical.propDecidable q)) := by
  by_cases hc : c
  · simp [hc]
  · simp [hc]

theorem decide_forall' {P : α → Prop} {h : Decidable (∀ x, P x)} :
    @decide (∀ x, P x) h = Bool.forall fun x => @decide (P x) (Classical.propDecidable _) := by
  apply Bool.eq_iff_iff.mpr; simp only [decide_eq_true_eq, Bool.forall_eq_true]

theorem decide_exists' {P : α → Prop} {h : Decidable (∃ x, P x)} :
    @decide (∃ x, P x) h = Bool.exists fun x => @decide (P x) (Classical.propDecidable _) := by
  apply Bool.eq_iff_iff.mpr; simp only [decide_eq_true_eq, Bool.exists_eq_true]

theorem decide_forall_prop {P : Prop → Prop} {h : Decidable (∀ x, P x)} :
    @decide (∀ x, P x) h = @decide (∀ x : Bool, P (x = true)) (Classical.propDecidable _) := by
  apply Bool.eq_iff_iff.mpr; simp only [decide_eq_true_eq]; exact forall_prop_as_bool

theorem decide_exists_prop {P : Prop → Prop} {h : Decidable (∃ x, P x)} :
    @decide (∃ x, P x) h = @decide (∃ x : Bool, P (x = true)) (Classical.propDecidable _) := by
  apply Bool.eq_iff_iff.mpr; simp only [decide_eq_true_eq]; exact exists_prop_as_bool

/-! Comparisons are decided with the Boolean comparisons that reconstruct SMT-LIB's comparisons. The
ones on rationals and reals are in `Smt.Preprocess.Embedding.Prop.Rat` and
`Smt.Preprocess.Embedding.Prop.Real`. -/

section

variable {x y : Int}

@[smt_decide ↓] theorem decide_int_lt {h : Decidable (x < y)} : @decide (x < y) h = x.blt y :=
  decide_eq_decide.mpr Iff.rfl
@[smt_decide ↓] theorem decide_int_le {h : Decidable (x ≤ y)} : @decide (x ≤ y) h = x.ble y :=
  decide_eq_decide.mpr Iff.rfl
@[smt_decide ↓] theorem decide_int_gt {h : Decidable (x > y)} : @decide (x > y) h = x.bgt y :=
  decide_eq_decide.mpr Iff.rfl
@[smt_decide ↓] theorem decide_int_ge {h : Decidable (x ≥ y)} : @decide (x ≥ y) h = x.bge y :=
  decide_eq_decide.mpr Iff.rfl

end

section

variable {w : Nat} {x y : BitVec w}

@[smt_decide ↓] theorem decide_bitVec_lt {h : Decidable (x < y)} : @decide (x < y) h = x.ult y := by
  rw [BitVec.ult_eq_decide_lt]; exact decide_eq_decide.mpr Iff.rfl
@[smt_decide ↓] theorem decide_bitVec_le {h : Decidable (x ≤ y)} : @decide (x ≤ y) h = x.ule y := by
  rw [BitVec.ule_eq_decide_le]; exact decide_eq_decide.mpr Iff.rfl
@[smt_decide ↓] theorem decide_bitVec_gt {h : Decidable (x > y)} : @decide (x > y) h = x.ugt y := by
  rw [BitVec.ugt, BitVec.ult_eq_decide_lt]; exact decide_eq_decide.mpr Iff.rfl
@[smt_decide ↓] theorem decide_bitVec_ge {h : Decidable (x ≥ y)} : @decide (x ≥ y) h = x.uge y := by
  rw [BitVec.uge, BitVec.ule_eq_decide_le]; exact decide_eq_decide.mpr Iff.rfl

end

theorem decide_eq_beq {β : Type u} [inst : DecidableEq β] {a b : β} {h : Decidable (a = b)} :
    @decide (a = b) h = @BEq.beq β (@instBEqOfDecidableEq β inst) a b := by
  apply Bool.eq_iff_iff.mpr; simp

theorem decide_instance {p : Prop} (h h' : Decidable p) : @decide p h = @decide p h' :=
  congrArg (@decide p) (Subsingleton.elim h h')

theorem ite_eq_cond {c : Prop} {h : Decidable c} {x y : α} :
    @ite α c h x y = cond (@decide c h) x y :=
  (Bool.cond_decide c x y).symm

end Smt.Preprocess.Embedding

public meta section

namespace Smt.Preprocess.Embedding

open Lean Meta Simp Qq

/-- Turn `decide (∀ x, p x)` into `Bool.forall fun x => decide (p x)`. Propositional variables
`x : Prop` become Boolean ones, and quantifiers over proofs are atoms. -/
simproc ↓ [smt_decide] decideForall (decide _) := fun e => do
  let_expr Decidable.decide p h := e | return .continue
  let .forallE n t body bi := p | return .continue
  -- `p → q` is an implication, see `decide_imp'`.
  if !body.hasLooseBVars && (← isProp t) then return .continue
  let lp := Expr.lam n t body bi
  if t.isProp then
    let lp : Q(Prop → Prop) ← pure lp
    return .visit { expr := q(@decide (∀ x : Bool, $lp (x = true)) (Classical.propDecidable _)),
                    proof? := mkApp2 (.const ``decide_forall_prop []) lp h }
  if ← isProp t then return .continue
  let u ← getLevel t
  let lb := Expr.lam n t (mkApp2 (.const ``Decidable.decide []) body
    (mkApp (.const ``Classical.propDecidable []) body)) bi
  return .visit { expr := mkApp2 (.const ``Bool.forall [u]) t lb,
                  proof? := mkApp3 (.const ``decide_forall' [u]) t lp h }

/-- Turn `decide (∃ x, p x)` into `Bool.exists fun x => decide (p x)`. Propositional variables
`x : Prop` become Boolean ones, and quantifiers over proofs are atoms. -/
simproc ↓ [smt_decide] decideExists (decide (Exists _)) := fun e => do
  let_expr Decidable.decide p h := e | return .continue
  let_expr Exists t lp := p | return .continue
  let .lam n _ body bi := lp | return .continue
  if t.isProp then
    let lp : Q(Prop → Prop) ← pure lp
    return .visit { expr := q(@decide (∃ x : Bool, $lp (x = true)) (Classical.propDecidable _)),
                    proof? := mkApp2 (.const ``decide_exists_prop []) lp h }
  if ← isProp t then return .continue
  let u ← getLevel t
  let lb := Expr.lam n t (mkApp2 (.const ``Decidable.decide []) body
    (mkApp (.const ``Classical.propDecidable []) body)) bi
  return .visit { expr := mkApp2 (.const ``Bool.exists [u]) t lb,
                  proof? := mkApp3 (.const ``decide_exists' [u]) t lp h }

/-- Decide equalities `a = b` of data with `a == b`, with the same instances as proof reconstruction
(see `Smt.Reconstruct.Bool.mkBEq`). Equalities of propositions and Booleans `b = true` are handled by
the theorems above. -/
simproc ↓ [smt_decide] decideEq (decide (_ = _)) := fun e => do
  let_expr Decidable.decide p h := e | return .continue
  let_expr Eq β a b := p | return .continue
  if β.isProp || (← isProp β) then return .continue
  if β.isConstOf ``Bool && (a.isConstOf ``true || a.isConstOf ``false || b.isConstOf ``true ||
      b.isConstOf ``false) then
    return .continue
  -- `decide (a = b)` for `β : Sort u`, see `decideInstance`
  let some u := (← getLevel β).dec | return .continue
  let inst ← Smt.Reconstruct.Bool.decEqInst β
  return .visit { expr := ← Smt.Reconstruct.Bool.mkBEq β a b,
                  proof? := mkAppN (.const ``decide_eq_beq [u]) #[β, inst, a, b, h] }

/-- Replace the instance of an atom `decide p` by a synthesized one, as in proof reconstruction (see
`Smt.Reconstruct.Bool.decideOf`). -/
simproc ↑ [smt_decide] decideInstance (decide _) := fun e => do
  let_expr Decidable.decide p h := e | return .continue
  let some inst ← synthInstance? (mkApp (.const ``Decidable []) p) | return .continue
  if inst == h then return .continue
  return .done { expr := mkApp2 (.const ``Decidable.decide []) p inst,
                 proof? := mkApp3 (.const ``decide_instance []) p h inst }

/-- Replace `if c then x else y` by `cond (decide c) x y` for non-propositional `x` and `y`. -/
simproc ↓ [smt_decide] iteToCond (ite _ _ _) := fun e => do
  let_expr ite α c h x y := e | return .continue
  if α.isProp then return .continue
  let u ← getLevel α
  return .visit { expr := mkApp4 (.const ``cond [u]) α (mkApp2 (.const ``Decidable.decide []) c h) x y,
                  proof? := mkAppN (.const ``ite_eq_cond [u]) #[α, c, h, x, y] }

end Smt.Preprocess.Embedding
