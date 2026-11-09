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

Each theorem states a rewrite `⟦lhs⟧ = ⟦rhs⟧` between the reconstructions of the two sides of a
cvc5 rewrite rule. Reconstruction turns it into a proof of `decide (⟦lhs⟧ = ⟦rhs⟧) = true`.
-/

namespace Smt.Reconstruct.Bool

-- https://github.com/cvc5/cvc5/blob/main/src/theory/booleans/rewrites

section

variable {t s x y w c z y₁ y₂ z₁ : Bool} {xs ys zs : List Bool}

theorem bool_double_not_elim : (!!t) = t := Bool.not_not t
theorem bool_not_true (h : t = false) : (!t) = true := by simp [h]
theorem bool_not_false (h : t = true) : (!t) = false := by simp [h]

theorem bool_eq_true [Decidable (t = true)] : decide (t = true) = t := Bool.decide_eq_true
theorem bool_eq_false [Decidable (t = false)] : decide (t = false) = !t := Bool.decide_eq_false
theorem bool_eq_nrefl [Decidable (t = !t)] : decide (t = !t) = false := by cases t <;> simp

theorem bool_impl_false1 : t.smtImp false = !t := by cases t <;> rfl
theorem bool_impl_false2 : false.smtImp t = true := rfl
theorem bool_impl_true1 : t.smtImp true = true := by cases t <;> rfl
theorem bool_impl_true2 : true.smtImp t = t := rfl
theorem bool_impl_elim : t.smtImp s = (!t || s) := rfl

theorem bool_dual_impl_eq [Decidable (t = s)] : (t.smtImp s && s.smtImp t) = decide (t = s) := by
  cases t <;> cases s <;> simp [Bool.smtImp]

theorem bool_and_conf : Bool.andN (xs ++ w :: (ys ++ (!w) :: zs)) = false := by
  cases w <;> simp
theorem bool_and_conf2 : Bool.andN (xs ++ (!w) :: (ys ++ w :: zs)) = false := by
  cases w <;> simp
theorem bool_or_taut : Bool.orN (xs ++ w :: (ys ++ (!w) :: zs)) = true := by
  cases w <;> simp
theorem bool_or_taut2 : Bool.orN (xs ++ (!w) :: (ys ++ w :: zs)) = true := by
  cases w <;> simp

theorem bool_or_de_morgan :
    (!Bool.orN (x :: y :: zs)) = Bool.andN [!x, !Bool.orN (y :: zs)] := by
  simp [Bool.andN]
theorem bool_implies_de_morgan : (!x.smtImp y) = Bool.andN [x, !y] := by
  cases x <;> cases y <;> rfl
theorem bool_and_de_morgan :
    (!Bool.andN (x :: y :: zs)) = Bool.orN [!x, !Bool.andN (y :: zs)] := by
  simp [Bool.orN]

theorem bool_or_and_distrib :
    Bool.orN (Bool.andN (y₁ :: y₂ :: ys) :: z₁ :: zs) =
      Bool.andN [Bool.orN (y₁ :: z₁ :: zs), Bool.orN (Bool.andN (y₂ :: ys) :: z₁ :: zs)] := by
  simp only [Bool.orN_cons_append, Bool.andN_cons_append, Bool.andN]
  generalize Bool.andN ys = a
  generalize Bool.orN zs = b
  cases y₁ <;> cases y₂ <;> cases z₁ <;> cases a <;> cases b <;> rfl

theorem bool_implies_or_distrib :
    (Bool.orN (y₁ :: y₂ :: ys)).smtImp z =
      Bool.andN [y₁.smtImp z, (Bool.orN (y₂ :: ys)).smtImp z] := by
  simp only [Bool.orN_cons_append, Bool.andN]
  generalize Bool.orN ys = a
  cases y₁ <;> cases y₂ <;> cases z <;> cases a <;> rfl

theorem bool_xor_refl : xor x x = false := by cases x <;> rfl
theorem bool_xor_nrefl : xor x (!x) = true := by cases x <;> rfl
theorem bool_xor_false : xor x false = x := by cases x <;> rfl
theorem bool_xor_true : xor x true = !x := by cases x <;> rfl
theorem bool_xor_comm : xor x y = xor y x := by cases x <;> cases y <;> rfl
theorem bool_xor_elim [Decidable ((!x) = y)] : xor x y = decide ((!x) = y) := by
  cases x <;> cases y <;> simp
theorem bool_not_xor_elim [Decidable (x = y)] : (!xor x y) = decide (x = y) := by
  cases x <;> cases y <;> simp

theorem bool_not_eq_elim1 [Decidable (x = y)] [Decidable ((!x) = y)] :
    (!decide (x = y)) = decide ((!x) = y) := by
  cases x <;> cases y <;> simp
theorem bool_not_eq_elim2 [Decidable (x = y)] [Decidable (x = !y)] :
    (!decide (x = y)) = decide (x = !y) := by
  cases x <;> cases y <;> simp

theorem ite_neg_branch [Decidable (c = x)] (h : x = !y) : cond c x y = decide (c = x) := by
  subst h; cases c <;> cases y <;> simp

theorem ite_then_true : cond c true x = (c || x) := by cases c <;> rfl
theorem ite_else_false : cond c x false = (c && x) := by cases c <;> cases x <;> rfl
theorem ite_then_false : cond c false x = (!c && x) := by cases c <;> rfl
theorem ite_else_true : cond c x true = (!c || x) := by cases c <;> cases x <;> rfl

theorem ite_then_lookahead_self : cond c c x = cond c true x := by cases c <;> rfl
theorem ite_else_lookahead_self : cond c x c = cond c x false := by cases c <;> rfl
theorem ite_then_lookahead_not_self : cond c (!c) x = cond c false x := by cases c <;> rfl
theorem ite_else_lookahead_not_self : cond c x (!c) = cond c x true := by cases c <;> rfl

theorem ite_expand : cond c x y = ((!c || x) && (c || y)) := by
  cases c <;> cases x <;> cases y <;> rfl

theorem bool_not_ite_elim : (!cond c x y) = cond c (!x) (!y) := by cases c <;> rfl

end

-- https://github.com/cvc5/cvc5/blob/main/src/theory/builtin/rewrites

section

variable {c : Bool}

theorem ite_true_cond {x y : α} : cond true x y = x := rfl
theorem ite_false_cond {x y : α} : cond false x y = y := rfl
theorem ite_not_cond {x y : α} : cond (!c) x y = cond c y x := by cases c <;> rfl
theorem ite_eq_branch {x : α} : cond c x x = x := by cases c <;> rfl

theorem ite_then_lookahead {x y z : α} : cond c (cond c x y) z = cond c x z := by cases c <;> rfl
theorem ite_else_lookahead {x y z : α} : cond c x (cond c y z) = cond c x z := by cases c <;> rfl
theorem ite_then_neg_lookahead {x y z : α} : cond c (cond (!c) x y) z = cond c y z := by
  cases c <;> rfl
theorem ite_else_neg_lookahead {x y z : α} : cond c x (cond (!c) y z) = cond c x y := by
  cases c <;> rfl

end

-- https://github.com/cvc5/cvc5/blob/main/src/theory/uf/rewrites

theorem eq_refl {t : α} [Decidable (t = t)] : decide (t = t) = true := decide_eq_true rfl

theorem eq_symm {t s : α} [Decidable (t = s)] [Decidable (s = t)] :
    decide (t = s) = decide (s = t) := by
  rw [decide_eq_decide]; exact ⟨Eq.symm, Eq.symm⟩

theorem eq_cond_deq {t s r : α} [Decidable (s = r)] [Decidable (t = s)] [Decidable (t = r)]
    (h : decide (s = r) = false) :
    decide (decide (t = s) = decide (t = r)) = (!decide (t = s) && !decide (t = r)) := by
  have hsr : s ≠ r := of_decide_eq_false h
  by_cases hts : t = s
  · subst hts; simp [hsr]
  · by_cases htr : t = r
    · subst htr; simp [hts]
    · simp [hts, htr]

theorem eq_ite_lift {c : Bool} {t s r : α} [Decidable (cond c t s = r)] [Decidable (t = r)]
    [Decidable (s = r)] : decide (cond c t s = r) = cond c (decide (t = r)) (decide (s = r)) := by
  cases c <;> simp

theorem distinct_binary_elim {t s : α} [Decidable (t = s)] :
    (!decide (t = s)) = !decide (t = s) := rfl

end Smt.Reconstruct.Bool
