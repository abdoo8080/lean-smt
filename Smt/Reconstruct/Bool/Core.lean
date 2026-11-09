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
proof of `⟦φ⟧ = true`. This file defines the Boolean operators that Lean lacks, and the lemmas that
relate a Boolean formula `b` to the proposition `p` with `(b = true) = p` that the theory-specific
reconstruction (arithmetic, bit-vectors, …) reasons about.

The proposition associated with a Boolean formula mirrors its structure:

| Boolean formula     | proposition         |
|---------------------|---------------------|
| `true`, `false`     | `True`, `False`     |
| `!b`                | `¬p`                |
| `b₁ && b₂`          | `p₁ ∧ p₂`           |
| `b₁ \|\| b₂`        | `p₁ ∨ p₂`           |
| `xor b₁ b₂`         | `XOr p₁ p₂`         |
| `b₁.smtImp b₂`      | `p₁ → p₂`           |
| `cond c b₁ b₂`      | `ite p p₁ p₂`       |
| `decide (b₁ = b₂)`  | `p₁ = p₂`           |
| `decide (∀ x, b x = true)` | `∀ x, p x`   |
| `decide (∃ x, b x = true)` | `∃ x, p x`   |
| `decide q`          | `q`                 |
| other `b`           | `b = true`          |
-/

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

theorem decide_eq_true_eq_of_eq {p q : Prop} [Decidable p] (h : p = q) : (decide p = true) = q :=
  h ▸ decide_eq_true_eq

theorem decide_eq_eq_true_eq {b₁ b₂ : Bool} [Decidable (b₁ = b₂)]
    (h₁ : (b₁ = true) = p₁) (h₂ : (b₂ = true) = p₂) : (decide (b₁ = b₂) = true) = (p₁ = p₂) := by
  subst h₁ h₂; cases b₁ <;> cases b₂ <;> simp

theorem cond_eq_true_eq {c x y : Bool} {p q r : Prop} [Decidable p] (hc : (c = true) = p) (hx : (x = true) = q)
    (hy : (y = true) = r) : (cond c x y = true) = ite p q r := by
  subst hc hx hy; cases c <;> simp

theorem exists_congr_eq {p q : α → Prop} (h : ∀ a, p a = q a) : (∃ a, p a) = (∃ a, q a) :=
  propext (exists_congr (h · ▸ Iff.rfl))

end Smt.Reconstruct.Bool
