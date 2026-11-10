/-
Copyright (c) 2021-2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

module

public import Smt.Reconstruct.Prop.Core

@[expose] public section

/-!
# Booleans as the target of proof reconstruction

SMT-LIB's `Bool` sort is reconstructed as Lean's `Bool`, and a proof of an SMT formula `φ` is a
proof of `⟦φ⟧ = true`. This file defines the SMT-LIB operators that Lean lacks as Boolean
functions, and the lemmas that relate a Boolean formula `b` to the proposition `p` with
`(b = true) = p` that the theory-specific reconstruction (arithmetic, bit-vectors, …) reasons about.

SMT-LIB's `=`, `<`, `<=`, `>`, `>=`, `forall`, and `exists` are `smtEq`, `smtLt`, `smtLe`, `smtGt`,
`smtGe`, `smtForall`, and `smtExists`, and other atoms whose Lean counterparts are propositions are
`smtDecide p`. They decide their propositions classically, so they carry no `Decidable` instances.

The proposition associated with a Boolean formula mirrors its structure:

| Boolean formula     | proposition         |
|---------------------|---------------------|
| `true`, `false`     | `True`, `False`     |
| `!b`                | `¬p`                |
| `b₁ && b₂`          | `p₁ ∧ p₂`           |
| `b₁ \|\| b₂`        | `p₁ ∨ p₂`           |
| `xor b₁ b₂`         | `XOr p₁ p₂`         |
| `b₁.smtImp b₂`      | `p₁ → p₂`           |
| `smtEq b₁ b₂`       | `p₁ = p₂`           |
| `smtEq x y`         | `x = y`             |
| `smtLt x y`, …      | `x < y`, …          |
| `smtForall b`       | `∀ x, p x`          |
| `smtExists b`       | `∃ x, p x`          |
| `smtDecide q`       | `q`                 |
| other `b`           | `b = true`          |
-/

universe u

/-- `true` iff the proposition `p` holds. Atoms whose Lean counterparts are propositions without an
SMT operator below, e.g., applications of Lean predicates, are reconstructed as `smtDecide p`. -/
noncomputable def smtDecide (p : Prop) : Bool := @decide p (Classical.propDecidable p)

/-- SMT-LIB's `=`. -/
noncomputable def smtEq {α : Sort u} (a b : α) : Bool := smtDecide (a = b)

/-- SMT-LIB's `<`, and `bvult`. -/
noncomputable def smtLt {α : Type u} [LT α] (a b : α) : Bool := smtDecide (a < b)

/-- SMT-LIB's `<=`, and `bvule`. -/
noncomputable def smtLe {α : Type u} [LE α] (a b : α) : Bool := smtDecide (a ≤ b)

/-- SMT-LIB's `>`, and `bvugt`. -/
noncomputable def smtGt {α : Type u} [LT α] (a b : α) : Bool := smtDecide (a > b)

/-- SMT-LIB's `>=`, and `bvuge`. -/
noncomputable def smtGe {α : Type u} [LE α] (a b : α) : Bool := smtDecide (a ≥ b)

/-- SMT-LIB's `forall` over one variable. `(forall ((x T) (y U)) F)` is `smtForall fun x => smtForall
fun y => F`. -/
noncomputable def smtForall {α : Sort u} (p : α → Bool) : Bool := smtDecide (∀ x, p x = true)

/-- SMT-LIB's `exists` over one variable. -/
noncomputable def smtExists {α : Sort u} (p : α → Bool) : Bool := smtDecide (∃ x, p x = true)

section

variable {p q : Prop} {α : Sort u} {β : Type u} {a b : α} {x y : β}

@[simp] theorem smtDecide_eq_true : (smtDecide p = true) = p := by simp [smtDecide]
@[simp] theorem smtEq_eq_true : (smtEq a b = true) = (a = b) := smtDecide_eq_true
@[simp] theorem smtLt_eq_true [LT β] : (smtLt x y = true) = (x < y) := smtDecide_eq_true
@[simp] theorem smtLe_eq_true [LE β] : (smtLe x y = true) = (x ≤ y) := smtDecide_eq_true
@[simp] theorem smtGt_eq_true [LT β] : (smtGt x y = true) = (x > y) := smtDecide_eq_true
@[simp] theorem smtGe_eq_true [LE β] : (smtGe x y = true) = (x ≥ y) := smtDecide_eq_true
@[simp] theorem smtForall_eq_true {f : α → Bool} : (smtForall f = true) = ∀ x, f x = true :=
  smtDecide_eq_true
@[simp] theorem smtExists_eq_true {f : α → Bool} : (smtExists f = true) = ∃ x, f x = true :=
  smtDecide_eq_true

@[simp] theorem smtDecide_eq_false : (smtDecide p = false) = ¬p := by simp [smtDecide]
@[simp] theorem smtEq_eq_false : (smtEq a b = false) = ¬(a = b) := smtDecide_eq_false
@[simp] theorem smtLt_eq_false [LT β] : (smtLt x y = false) = ¬(x < y) := smtDecide_eq_false
@[simp] theorem smtLe_eq_false [LE β] : (smtLe x y = false) = ¬(x ≤ y) := smtDecide_eq_false
@[simp] theorem smtGt_eq_false [LT β] : (smtGt x y = false) = ¬(x > y) := smtDecide_eq_false
@[simp] theorem smtGe_eq_false [LE β] : (smtGe x y = false) = ¬(x ≥ y) := smtDecide_eq_false
@[simp] theorem smtForall_eq_false {f : α → Bool} : (smtForall f = false) = ¬∀ x, f x = true :=
  smtDecide_eq_false
@[simp] theorem smtExists_eq_false {f : α → Bool} : (smtExists f = false) = ¬∃ x, f x = true :=
  smtDecide_eq_false

theorem eq_of_smtEq (h : smtEq a b = true) : a = b := Eq.mp smtEq_eq_true h
theorem smtEq_of_eq (h : a = b) : smtEq a b = true := Eq.mpr smtEq_eq_true h

theorem decide_eq_smtDecide {h : Decidable p} : @decide p h = smtDecide p := by
  unfold smtDecide; congr

/-! The operators of decidable propositions evaluate to their decisions. -/

theorem smtDecide_eq_decide [Decidable p] : smtDecide p = decide p := decide_eq_smtDecide.symm
theorem smtEq_eq_decide [Decidable (a = b)] : smtEq a b = decide (a = b) := smtDecide_eq_decide
theorem smtLt_eq_decide [LT β] [Decidable (x < y)] : smtLt x y = decide (x < y) :=
  smtDecide_eq_decide
theorem smtLe_eq_decide [LE β] [Decidable (x ≤ y)] : smtLe x y = decide (x ≤ y) :=
  smtDecide_eq_decide
theorem smtGt_eq_decide [LT β] [Decidable (x > y)] : smtGt x y = decide (x > y) :=
  smtDecide_eq_decide
theorem smtGe_eq_decide [LE β] [Decidable (x ≥ y)] : smtGe x y = decide (x ≥ y) :=
  smtDecide_eq_decide

end

namespace Bool

/-- Boolean implication, the reconstruction of SMT-LIB's `=>`. -/
def smtImp (a b : Bool) : Bool := !a || b

/-- n-ary conjunction. Like cvc5's n-ary `and`, it has no trailing `true`: `andN [a] = a` and
`andN [a, b, c] = a && (b && c)`. -/
def andN : List Bool → Bool
  | []      => true
  | b :: [] => b
  | b :: bs => b && andN bs

/-- n-ary disjunction. Like cvc5's n-ary `or`, it has no trailing `false`: `orN [a] = a` and
`orN [a, b, c] = a || (b || c)`. -/
def orN : List Bool → Bool
  | []      => false
  | b :: [] => b
  | b :: bs => b || orN bs

/-- `impliesN [b₁, …, bₙ] q` is `b₁ = true → ⋯ → bₙ = true → q`. -/
def impliesN : List Bool → Prop → Prop
  | [],      q => q
  | b :: bs, q => b = true → impliesN bs q

@[simp] theorem smtImp_eq_true {a b : Bool} : (a.smtImp b = true) = (a = true → b = true) := by
  cases a <;> cases b <;> simp [smtImp]

@[simp] theorem andN_cons_append : andN (b :: bs) = (b && andN bs) := by
  cases bs <;> simp [andN]

@[simp] theorem andN_append : andN (bs₁ ++ bs₂) = (andN bs₁ && andN bs₂) := by
  induction bs₁ with
  | nil => simp [andN]
  | cons b bs₁ ih => simp [ih, Bool.and_assoc]

@[simp] theorem orN_cons_append : orN (b :: bs) = (b || orN bs) := by
  cases bs <;> simp [orN]

@[simp] theorem orN_append : orN (bs₁ ++ bs₂) = (orN bs₁ || orN bs₂) := by
  induction bs₁ with
  | nil => simp [orN]
  | cons b bs₁ ih => simp [ih, Bool.or_assoc]

theorem andN_eq_true {bs : List Bool} : (andN bs = true) = ∀ b ∈ bs, b = true := by
  induction bs with
  | nil => simp [andN]
  | cons b bs ih => simp [ih]

theorem orN_eq_true {bs : List Bool} : (orN bs = true) = ∃ b ∈ bs, b = true := by
  induction bs with
  | nil => simp [orN]
  | cons b bs ih => simp [ih]

end Bool

namespace Smt.Reconstruct.Bool

/-! ### From Boolean formulas to propositions -/

theorem true_eq_true_eq : (true = true) = True := eq_self true

theorem false_eq_true_eq : (false = true) = False := by simp

theorem not_eq_true_eq {b : Bool} (h : (b = true) = p) : ((!b) = true) = ¬p := by
  subst h; cases b <;> simp

theorem and_eq_true_eq {b₁ b₂ : Bool} (h₁ : (b₁ = true) = p₁) (h₂ : (b₂ = true) = p₂) :
    ((b₁ && b₂) = true) = (p₁ ∧ p₂) := by
  subst h₁ h₂; simp

theorem or_eq_true_eq {b₁ b₂ : Bool} (h₁ : (b₁ = true) = p₁) (h₂ : (b₂ = true) = p₂) :
    ((b₁ || b₂) = true) = (p₁ ∨ p₂) := by
  subst h₁ h₂; simp

theorem xor_iff_not_iff {p q : Prop} : XOr p q ↔ ¬(p ↔ q) :=
  ⟨fun h => h.elim (fun hp hnq h => hnq (h.mp hp)) (fun hnp hq h => hnp (h.mpr hq)),
   fun h => (Classical.em p).elim
     (fun hp => .inl hp (fun hq => h ⟨fun _ => hq, fun _ => hp⟩))
     (fun hnp => .inr hnp (Classical.byContradiction fun hnq =>
       h ⟨fun hp => absurd hp hnp, fun hq => absurd hq hnq⟩))⟩

theorem xor_eq_true_eq {b₁ b₂ : Bool} (h₁ : (b₁ = true) = p₁) (h₂ : (b₂ = true) = p₂) :
    ((xor b₁ b₂) = true) = XOr p₁ p₂ := by
  subst h₁ h₂; apply propext; rw [xor_iff_not_iff]; cases b₁ <;> cases b₂ <;> simp

theorem smtImp_eq_true_eq {b₁ b₂ : Bool} (h₁ : (b₁ = true) = p₁) (h₂ : (b₂ = true) = p₂) :
    ((b₁.smtImp b₂) = true) = (p₁ → p₂) := by
  subst h₁ h₂; simp

theorem smtDecide_eq_true_eq {p q : Prop} (h : p = q) : (smtDecide p = true) = q :=
  h ▸ smtDecide_eq_true

theorem smtEq_bool_eq_true_eq {b₁ b₂ : Bool} (h₁ : (b₁ = true) = p₁) (h₂ : (b₂ = true) = p₂) :
    (smtEq b₁ b₂ = true) = (p₁ = p₂) := by
  subst h₁ h₂; cases b₁ <;> cases b₂ <;> simp

theorem smtForall_eq_true_eq {α : Sort u} {f : α → Bool} {p : α → Prop}
    (h : ∀ x, (f x = true) = p x) : (smtForall f = true) = ∀ x, p x := by
  simp only [smtForall_eq_true]; exact forall_congr h

theorem smtExists_eq_true_eq {α : Sort u} {f : α → Bool} {p : α → Prop}
    (h : ∀ x, (f x = true) = p x) : (smtExists f = true) = ∃ x, p x := by
  simp only [smtExists_eq_true]; exact propext (exists_congr (h · ▸ Iff.rfl))

theorem exists_congr_eq {p q : α → Prop} (h : ∀ a, p a = q a) : (∃ a, p a) = (∃ a, q a) :=
  propext (exists_congr (h · ▸ Iff.rfl))

end Smt.Reconstruct.Bool
