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
`(ite c t s)` is `cond c t s`. The conditions of conditional rewrites are equations, e.g.,
`decide (s = 0) = false`. -/

variable {t s x y : Int}

theorem div_total : decide (s = 0) = false → t / s = t / s :=
  const _ rfl
theorem div_total_one : t / 1 = t :=
  Int.ediv_one t
theorem div_total_zero : t / 0 = 0 :=
  Int.ediv_zero t

theorem div_total_neg : s.blt 0 = true → t / s = -(t / -s) :=
  const _ (Int.ediv_neg t s ▸ Int.neg_neg _ ▸ rfl)

theorem mod_total : decide (s = 0) = false → t % s = t % s :=
  const _ rfl
theorem mod_total_one : t % 1 = 0 :=
  Int.emod_one t
theorem mod_total_zero : t % 0 = t :=
  Int.emod_zero t

theorem mod_total_neg : s.blt 0 = true → t % s = t % -s :=
  const _ (Int.emod_neg t s ▸ rfl)

-- Eliminations

theorem elim_gt : t.bgt s = !t.ble s := by
  simp only [Int.bgt, Int.ble, ← decide_not]; apply decide_eq_decide.mpr; omega
theorem elim_lt : t.blt s = !t.bge s := by
  simp only [Int.blt, Int.bge, ← decide_not]; apply decide_eq_decide.mpr; omega
theorem elim_gt_add_one : t.bgt s = t.bge (s + 1) := by
  simp only [Int.bgt, Int.bge]; apply decide_eq_decide.mpr; omega
theorem elim_lt_add_one : t.blt s = s.bge (t + 1) := by
  simp only [Int.blt, Int.bge]; apply decide_eq_decide.mpr; omega
theorem elim_leq : t.ble s = s.bge t :=
  rfl

theorem leq_norm : t.ble s = !t.bge (s + 1) := by
  simp only [Int.ble, Int.bge, ← decide_not]; apply decide_eq_decide.mpr; omega

theorem geq_tighten : (!t.bge s) = s.bge (t + 1) := by
  simp only [Int.bge, ← decide_not]; apply decide_eq_decide.mpr; omega

theorem geq_norm1 : t.bge s = (t - s).bge 0 := by
  simp only [Int.bge]; apply decide_eq_decide.mpr; omega

theorem eq_elim : decide (t = s) = (t.bge s && t.ble s) := by
  simp only [Int.bge, Int.ble, ← Bool.decide_and]; apply decide_eq_decide.mpr; omega

theorem mod_over_mod : decide (c = 0) = false → Int.addN (ts ++ r % c :: ss) % c = Int.addN (ts ++ r :: ss) % c := by
  simp only [Int.addN_append, Int.addN_cons_append, Int.emod_add_cancel_left, Int.emod_add_cancel_right, Int.emod_emod, implies_true]

/-- SMT-LIB's `(_ divisible n)` has no Boolean counterpart in Lean, so it is decided. -/
theorem divisible_elim {n t : Int} (_ : decide (n = 0) = false) :
    decide (n ∣ t) = decide (t % n = 0) :=
  decide_eq_decide.mpr Int.dvd_iff_emod_eq_zero

-- Absolute value comparisons

theorem abs_eq : decide (x.abs = y.abs) = (decide (x = y) || decide (x = -y)) := by
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, Bool.or_eq_true]
  cases hx : decide (x < 0) <;> cases hy : decide (y < 0) <;> simp_all [Int.abs] <;> omega

theorem abs_gt : x.abs.bgt y.abs =
    cond (x.bge 0) (cond (y.bge 0) (x.bgt y) (x.bgt (-y))) (cond (y.bge 0) ((-x).bgt y) ((-x).bgt (-y))) := by
  apply Bool.eq_iff_iff.mpr
  cases hx : x.bge 0 <;> cases hy : y.bge 0 <;>
    simp only [Int.bge_eq_true, Int.bge_eq_false, Int.bgt_eq_true, Bool.cond_true, Bool.cond_false] at * <;>
    simp only [Int.abs] <;> split <;> split <;> omega

-- ITE lifting

theorem geq_ite_lift {c : Bool} {t s r : Int} : (cond c t s).bge r = cond c (t.bge r) (s.bge r) := by
  cases c <;> rfl

theorem leq_ite_lift {c : Bool} {t s r : Int} : (cond c t s).ble r = cond c (t.ble r) (s.ble r) := by
  cases c <;> rfl

-- min/max rules

theorem min_lt1 : (cond (t.blt s) t s).ble t = true := by
  cases h : t.blt s <;> simp_all <;> omega

theorem min_lt2 : (cond (t.blt s) t s).ble s = true := by
  cases h : t.blt s <;> simp_all <;> omega

theorem max_geq1 : (cond (t.bge s) t s).bge t = true := by
  cases h : t.bge s <;> simp_all <;> omega

theorem max_geq2 : (cond (t.bge s) t s).bge s = true := by
  cases h : t.bge s <;> simp_all <;> omega

end Smt.Reconstruct.Int.Rewrite
