/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

module

public import Smt.Reconstruct.Bool.Core
public import Smt.Reconstruct.Int.Core

@[expose] public section

namespace Smt.Reconstruct.Int.Rewrite

open Function

-- https://github.com/cvc5/cvc5/blob/main/src/theory/arith/rewrites

/-! The rewrites are stated over the reconstructions of SMT-LIB terms: `(< t s)` is `t.blt s`, `(<= t s)`
is `t.ble s`, `(> t s)` is `t.bgt s`, `(>= t s)` is `t.bge s`, `(= t s)` is `decide (t = s)`, and
`(ite c t s)` is `cond c t s`. A rewrite `(= lhs rhs)` is stated as `Bool.eq lhs rhs`, and so are
the conditions of conditional rewrites, e.g., `Bool.eq (decide (s = 0)) false`. -/

variable {t s x y : Int}

theorem div_total : Bool.eq (decide (s = 0)) false → Bool.eq (t / s) (t / s) :=
  const _ (Bool.eq.refl _)
theorem div_total_one : Bool.eq (t / 1) t :=
  Bool.eq.of_eq <| Int.ediv_one t
theorem div_total_zero : Bool.eq (t / 0) 0 :=
  Bool.eq.of_eq <| Int.ediv_zero t

theorem div_total_neg : Bool.eq (s.blt 0) true → Bool.eq (t / s) (-(t / -s)) :=
  const _ (Bool.eq.of_eq (Int.ediv_neg t s ▸ Int.neg_neg _ ▸ rfl))

theorem mod_total : Bool.eq (decide (s = 0)) false → Bool.eq (t % s) (t % s) :=
  const _ (Bool.eq.refl _)
theorem mod_total_one : Bool.eq (t % 1) 0 :=
  Bool.eq.of_eq <| Int.emod_one t
theorem mod_total_zero : Bool.eq (t % 0) t :=
  Bool.eq.of_eq <| Int.emod_zero t

theorem mod_total_neg : Bool.eq (s.blt 0) true → Bool.eq (t % s) (t % -s) :=
  const _ (Bool.eq.of_eq (Int.emod_neg t s ▸ rfl))

-- Eliminations

theorem elim_gt : Bool.eq (t.bgt s) (!t.ble s) := by
  apply Bool.eq.of_eq
  simp only [Int.bgt, Int.ble, ← decide_not]; apply decide_eq_decide.mpr; omega
theorem elim_lt : Bool.eq (t.blt s) (!t.bge s) := by
  apply Bool.eq.of_eq
  simp only [Int.blt, Int.bge, ← decide_not]; apply decide_eq_decide.mpr; omega
theorem elim_gt_add_one : Bool.eq (t.bgt s) (t.bge (s + 1)) := by
  apply Bool.eq.of_eq
  simp only [Int.bgt, Int.bge]; apply decide_eq_decide.mpr; omega
theorem elim_lt_add_one : Bool.eq (t.blt s) (s.bge (t + 1)) := by
  apply Bool.eq.of_eq
  simp only [Int.blt, Int.bge]; apply decide_eq_decide.mpr; omega
theorem elim_leq : Bool.eq (t.ble s) (s.bge t) :=
  Bool.eq.of_eq <| rfl

theorem leq_norm : Bool.eq (t.ble s) (!t.bge (s + 1)) := by
  apply Bool.eq.of_eq
  simp only [Int.ble, Int.bge, ← decide_not]; apply decide_eq_decide.mpr; omega

theorem geq_tighten : Bool.eq (!t.bge s) (s.bge (t + 1)) := by
  apply Bool.eq.of_eq
  simp only [Int.bge, ← decide_not]; apply decide_eq_decide.mpr; omega

theorem geq_norm1 : Bool.eq (t.bge s) ((t - s).bge 0) := by
  apply Bool.eq.of_eq
  simp only [Int.bge]; apply decide_eq_decide.mpr; omega

theorem eq_elim : Bool.eq (decide (t = s)) (t.bge s && t.ble s) := by
  apply Bool.eq.of_eq
  simp only [Int.bge, Int.ble, ← Bool.decide_and]; apply decide_eq_decide.mpr; omega

theorem mod_over_mod : Bool.eq (decide (c = 0)) false →
    Bool.eq (Int.addN (ts ++ r % c :: ss) % c) (Int.addN (ts ++ r :: ss) % c) := by
  intro _
  apply Bool.eq.of_eq
  simp only [Int.addN_append, Int.addN_cons_append, Int.emod_add_cancel_left,
    Int.emod_add_cancel_right, Int.emod_emod]

/-- SMT-LIB's `(_ divisible n)` has no Boolean counterpart in Lean, so it is decided. -/
theorem divisible_elim {n t : Int} (_ : Bool.eq (decide (n = 0)) false) :
    Bool.eq (decide (n ∣ t)) (decide (t % n = 0)) :=
  Bool.eq.of_eq <| decide_eq_decide.mpr Int.dvd_iff_emod_eq_zero

-- Absolute value comparisons

theorem abs_eq : Bool.eq (decide (x.abs = y.abs)) (decide (x = y) || decide (x = -y)) := by
  apply Bool.eq.of_eq
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, Bool.or_eq_true]
  cases hx : decide (x < 0) <;> cases hy : decide (y < 0) <;> simp_all [Int.abs] <;> omega

theorem abs_gt : Bool.eq (x.abs.bgt y.abs)
    (cond (x.bge 0) (cond (y.bge 0) (x.bgt y) (x.bgt (-y)))
      (cond (y.bge 0) ((-x).bgt y) ((-x).bgt (-y)))) := by
  apply Bool.eq.of_eq
  apply Bool.eq_iff_iff.mpr
  cases hx : x.bge 0 <;> cases hy : y.bge 0 <;>
    simp only [Int.bge_eq_true, Int.bge_eq_false, Int.bgt_eq_true, Bool.cond_true, Bool.cond_false] at * <;>
    simp only [Int.abs] <;> split <;> split <;> omega

-- ITE lifting

theorem geq_ite_lift {c : Bool} {t s r : Int} :
    Bool.eq ((cond c t s).bge r) (cond c (t.bge r) (s.bge r)) := by
  apply Bool.eq.of_eq
  cases c <;> rfl

theorem leq_ite_lift {c : Bool} {t s r : Int} :
    Bool.eq ((cond c t s).ble r) (cond c (t.ble r) (s.ble r)) := by
  apply Bool.eq.of_eq
  cases c <;> rfl

-- min/max rules

theorem min_lt1 : Bool.eq ((cond (t.blt s) t s).ble t) true := by
  apply Bool.eq.of_eq
  cases h : t.blt s <;> simp_all <;> omega

theorem min_lt2 : Bool.eq ((cond (t.blt s) t s).ble s) true := by
  apply Bool.eq.of_eq
  cases h : t.blt s <;> simp_all <;> omega

theorem max_geq1 : Bool.eq ((cond (t.bge s) t s).bge t) true := by
  apply Bool.eq.of_eq
  cases h : t.bge s <;> simp_all <;> omega

theorem max_geq2 : Bool.eq ((cond (t.bge s) t s).bge s) true := by
  apply Bool.eq.of_eq
  cases h : t.bge s <;> simp_all <;> omega

end Smt.Reconstruct.Int.Rewrite
