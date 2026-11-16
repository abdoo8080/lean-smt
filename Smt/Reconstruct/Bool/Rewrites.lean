/-
Copyright (c) 2021-2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

module

public import Smt.Reconstruct.Bool.Core

@[expose] public section

/-!
# cvc5's Boolean, `ite`, and equality rewrite rules over `Bool`

Each theorem states a rewrite `Bool.eq ⟦lhs⟧ ⟦rhs⟧` between the reconstructions of the two sides of
a cvc5 rewrite rule, i.e., the proof `decide (⟦lhs⟧ = ⟦rhs⟧) = true` of the SMT formula
`(= lhs rhs)`. So are the conditions of conditional rewrites.
-/

namespace Smt.Reconstruct.Bool

universe u

-- https://github.com/cvc5/cvc5/blob/main/src/theory/booleans/rewrites

section

variable {t s x y w c z y₁ y₂ z₁ : Bool} {xs ys zs : List Bool}

theorem bool_double_not_elim : Bool.eq (!!t) t := Bool.eq.of_eq <| Bool.not_not t
theorem bool_not_true (h : Bool.eq t false) : Bool.eq (!t) true :=
  Bool.eq.of_eq <| by simp [h.to_eq]
theorem bool_not_false (h : Bool.eq t true) : Bool.eq (!t) false :=
  Bool.eq.of_eq <| by simp [h.to_eq]

theorem bool_eq_true : Bool.eq (decide (t = true)) t := Bool.eq.of_eq <| by cases t <;> rfl
theorem bool_eq_false : Bool.eq (decide (t = false)) (!t) := Bool.eq.of_eq <| by cases t <;> rfl
theorem bool_eq_nrefl : Bool.eq (decide (t = !t)) false := Bool.eq.of_eq <| by cases t <;> rfl

theorem bool_impl_false1 : Bool.eq (t.imp false) (!t) := Bool.eq.of_eq <| by cases t <;> rfl
theorem bool_impl_false2 : Bool.eq (false.imp t) true := Bool.eq.of_eq <| rfl
theorem bool_impl_true1 : Bool.eq (t.imp true) true := Bool.eq.of_eq <| by cases t <;> rfl
theorem bool_impl_true2 : Bool.eq (true.imp t) t := Bool.eq.of_eq <| rfl
theorem bool_impl_elim : Bool.eq (t.imp s) (!t || s) := Bool.eq.of_eq <| rfl

theorem bool_dual_impl_eq : Bool.eq (t.imp s && s.imp t) (decide (t = s)) := by
  apply Bool.eq.of_eq
  cases t <;> cases s <;> rfl

theorem bool_and_conf : Bool.eq (Bool.andN (xs ++ w :: (ys ++ (!w) :: zs))) false := by
  apply Bool.eq.of_eq
  cases w <;> simp
theorem bool_and_conf2 : Bool.eq (Bool.andN (xs ++ (!w) :: (ys ++ w :: zs))) false := by
  apply Bool.eq.of_eq
  cases w <;> simp
theorem bool_or_taut : Bool.eq (Bool.orN (xs ++ w :: (ys ++ (!w) :: zs))) true := by
  apply Bool.eq.of_eq
  cases w <;> simp
theorem bool_or_taut2 : Bool.eq (Bool.orN (xs ++ (!w) :: (ys ++ w :: zs))) true := by
  apply Bool.eq.of_eq
  cases w <;> simp

theorem bool_or_de_morgan :
    Bool.eq (!Bool.orN (x :: y :: zs)) (Bool.andN [!x, !Bool.orN (y :: zs)]) := by
  apply Bool.eq.of_eq
  simp [Bool.andN]
theorem bool_implies_de_morgan : Bool.eq (!x.imp y) (Bool.andN [x, !y]) := by
  apply Bool.eq.of_eq
  cases x <;> cases y <;> rfl
theorem bool_and_de_morgan :
    Bool.eq (!Bool.andN (x :: y :: zs)) (Bool.orN [!x, !Bool.andN (y :: zs)]) := by
  apply Bool.eq.of_eq
  simp [Bool.orN]

theorem bool_or_and_distrib :
    Bool.eq (Bool.orN (Bool.andN (y₁ :: y₂ :: ys) :: z₁ :: zs))
      (Bool.andN [Bool.orN (y₁ :: z₁ :: zs), Bool.orN (Bool.andN (y₂ :: ys) :: z₁ :: zs)]) := by
  apply Bool.eq.of_eq
  simp only [Bool.orN_cons_append, Bool.andN_cons_append, Bool.andN]
  generalize Bool.andN ys = a
  generalize Bool.orN zs = b
  cases y₁ <;> cases y₂ <;> cases z₁ <;> cases a <;> cases b <;> rfl

theorem bool_implies_or_distrib :
    Bool.eq ((Bool.orN (y₁ :: y₂ :: ys)).imp z)
      (Bool.andN [y₁.imp z, (Bool.orN (y₂ :: ys)).imp z]) := by
  apply Bool.eq.of_eq
  simp only [Bool.orN_cons_append, Bool.andN]
  generalize Bool.orN ys = a
  cases y₁ <;> cases y₂ <;> cases z <;> cases a <;> rfl

theorem bool_xor_refl : Bool.eq (xor x x) false := Bool.eq.of_eq <| by cases x <;> rfl
theorem bool_xor_nrefl : Bool.eq (xor x (!x)) true := Bool.eq.of_eq <| by cases x <;> rfl
theorem bool_xor_false : Bool.eq (xor x false) x := Bool.eq.of_eq <| by cases x <;> rfl
theorem bool_xor_true : Bool.eq (xor x true) (!x) := Bool.eq.of_eq <| by cases x <;> rfl
theorem bool_xor_comm : Bool.eq (xor x y) (xor y x) :=
  Bool.eq.of_eq <| by cases x <;> cases y <;> rfl
theorem bool_xor_elim : Bool.eq (xor x y) (decide ((!x) = y)) :=
  Bool.eq.of_eq <| by cases x <;> cases y <;> rfl
theorem bool_not_xor_elim : Bool.eq (!xor x y) (decide (x = y)) :=
  Bool.eq.of_eq <| by cases x <;> cases y <;> rfl

theorem bool_not_eq_elim1 : Bool.eq (!decide (x = y)) (decide ((!x) = y)) :=
  Bool.eq.of_eq <| by cases x <;> cases y <;> rfl
theorem bool_not_eq_elim2 : Bool.eq (!decide (x = y)) (decide (x = !y)) :=
  Bool.eq.of_eq <| by cases x <;> cases y <;> rfl

theorem ite_neg_branch (h : Bool.eq x (!y)) : Bool.eq (cond c x y) (decide (c = x)) := by
  apply Bool.eq.of_eq
  have h := h.to_eq; subst h; cases c <;> cases y <;> rfl

theorem ite_then_true : Bool.eq (cond c true x) (c || x) := Bool.eq.of_eq <| by cases c <;> rfl
theorem ite_else_false : Bool.eq (cond c x false) (c && x) :=
  Bool.eq.of_eq <| by cases c <;> cases x <;> rfl
theorem ite_then_false : Bool.eq (cond c false x) (!c && x) := Bool.eq.of_eq <| by cases c <;> rfl
theorem ite_else_true : Bool.eq (cond c x true) (!c || x) :=
  Bool.eq.of_eq <| by cases c <;> cases x <;> rfl

theorem ite_then_lookahead_self : Bool.eq (cond c c x) (cond c true x) :=
  Bool.eq.of_eq <| by cases c <;> rfl
theorem ite_else_lookahead_self : Bool.eq (cond c x c) (cond c x false) :=
  Bool.eq.of_eq <| by cases c <;> rfl
theorem ite_then_lookahead_not_self : Bool.eq (cond c (!c) x) (cond c false x) :=
  Bool.eq.of_eq <| by cases c <;> rfl
theorem ite_else_lookahead_not_self : Bool.eq (cond c x (!c)) (cond c x true) :=
  Bool.eq.of_eq <| by cases c <;> rfl

theorem ite_expand : Bool.eq (cond c x y) ((!c || x) && (c || y)) := by
  apply Bool.eq.of_eq
  cases c <;> cases x <;> cases y <;> rfl

theorem bool_not_ite_elim : Bool.eq (!cond c x y) (cond c (!x) (!y)) :=
  Bool.eq.of_eq <| by cases c <;> rfl

end

-- https://github.com/cvc5/cvc5/blob/main/src/theory/builtin/rewrites

section

variable {α : Sort u} [DecidableEq α] {c : Bool}

theorem ite_true_cond {x y : α} : Bool.eq (cond true x y) x := Bool.eq.of_eq <| rfl
theorem ite_false_cond {x y : α} : Bool.eq (cond false x y) y := Bool.eq.of_eq <| rfl
theorem ite_not_cond {x y : α} : Bool.eq (cond (!c) x y) (cond c y x) :=
  Bool.eq.of_eq <| by cases c <;> rfl
theorem ite_eq_branch {x : α} : Bool.eq (cond c x x) x := Bool.eq.of_eq <| by cases c <;> rfl

theorem ite_then_lookahead {x y z : α} : Bool.eq (cond c (cond c x y) z) (cond c x z) :=
  Bool.eq.of_eq <| by cases c <;> rfl
theorem ite_else_lookahead {x y z : α} : Bool.eq (cond c x (cond c y z)) (cond c x z) :=
  Bool.eq.of_eq <| by cases c <;> rfl
theorem ite_then_neg_lookahead {x y z : α} : Bool.eq (cond c (cond (!c) x y) z) (cond c y z) := by
  apply Bool.eq.of_eq
  cases c <;> rfl
theorem ite_else_neg_lookahead {x y z : α} : Bool.eq (cond c x (cond (!c) y z)) (cond c x y) := by
  apply Bool.eq.of_eq
  cases c <;> rfl

end

-- https://github.com/cvc5/cvc5/blob/main/src/theory/uf/rewrites

/-! The theorems about equalities decide them with the instance of a `DecidableEq α`, which proof
reconstruction instantiates with `Smt.Reconstruct.Bool.decEqInst α`. -/

section

variable {α : Sort u} [DecidableEq α]

theorem eq_refl {t : α} : Bool.eq (decide (t = t)) true := Bool.eq.of_eq <| decide_eq_true rfl

theorem eq_symm {t s : α} : Bool.eq (decide (t = s)) (decide (s = t)) :=
  Bool.eq.of_eq <| decide_eq_decide.mpr ⟨Eq.symm, Eq.symm⟩

theorem eq_cond_deq {t s r : α} (h : Bool.eq (decide (s = r)) false) :
    Bool.eq (decide (decide (t = s) = decide (t = r))) (!decide (t = s) && !decide (t = r)) :=
  Bool.eq.of_eq <| by
  have hsr : s ≠ r := by simpa using h.to_eq
  by_cases hts : t = s
  · subst hts; simp [hsr]
  · by_cases htr : t = r
    · subst htr; simp [hts]
    · simp [hts, htr]

theorem eq_ite_lift {c : Bool} {t s r : α} :
    Bool.eq (decide (cond c t s = r)) (cond c (decide (t = r)) (decide (s = r))) :=
  Bool.eq.of_eq <| by cases c <;> rfl

end

end Smt.Reconstruct.Bool
