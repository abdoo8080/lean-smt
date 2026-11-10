/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

module

public import Smt.Reconstruct.Bool.Core
public import Smt.Reconstruct.Int.Core
public import Smt.Reconstruct.Real.Core
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

@[expose] public section

namespace Smt.Reconstruct.Real.Rewrite

open Function

-- https://github.com/cvc5/cvc5/blob/main/src/theory/arith/rewrites

/-! The rewrites are stated over the reconstructions of SMT-LIB terms (see
`Smt.Reconstruct.Int.Rewrite`). -/

-- `==` is the reconstruction of SMT-LIB's `=` (see `Smt.Reconstruct.Bool.mkBEq`).
attribute [local instance high] instBEqOfDecidableEq

variable {t s x y : Real}

theorem div_total_zero : x / 0 = 0 :=
  div_zero x

-- Eliminations

theorem elim_gt : t.bgt s = !t.ble s := by
  simp only [Real.bgt, Real.ble, ← decide_not]; exact decide_eq_decide.mpr not_le.symm
theorem elim_lt : t.blt s = !t.bge s := by
  simp only [Real.blt, Real.bge, ← decide_not]; exact decide_eq_decide.mpr not_le.symm
theorem elim_leq : t.ble s = s.bge t :=
  decide_eq_decide.mpr Iff.rfl

theorem geq_norm1 : t.bge s = (t - s).bge 0 :=
  decide_eq_decide.mpr ⟨sub_nonneg_of_le, le_of_sub_nonneg⟩

theorem eq_elim : (t == s) = (t.bge s && t.ble s) := by
  simp only [Real.bge, Real.ble, ← Bool.decide_and]; exact decide_eq_decide.mpr (Iff.symm antisymm_iff)

theorem eq_conflict {t : Int} {c : Real} (hcc : ((⌊c⌋ : Real) == c) = false) : ((t : Real) == c) = false := by
  simp only [beq_eq_false_iff_ne] at *
  intro htc
  have hcc : ⌊c⌋ < c := (le_iff_eq_or_lt.mp (Int.floor_le c)).resolve_left hcc
  cases Int.lt_trichotomy t ⌊c⌋ <;> rename_i htcf
  · have hntc : ↑t ≠ c := (lt_iff_le_and_ne.mp (lt_trans (Int.cast_lt.mpr htcf) hcc)).right
    contradiction
  · cases htcf <;> rename_i htcf
    · simp_all
    · have h : c < t := by
        apply @lt_of_lt_of_le _ _ _
        · apply ((Int.floor_eq_iff (z := ⌊c⌋) (a := c)).mp rfl).right
        · rewrite [← Int.cast_one, ← Int.cast_add, Int.cast_le]
          exact htcf
      simp_all

theorem geq_tighten {t : Int} {c : Real} {cc : Int} (hc : ((⌊c⌋ : Real) == c) = false) (hcc : cc = ⌊c⌋ + 1) : (t : Real).bge c = t.bge cc := by
  apply Bool.eq_iff_iff.mpr
  rw [Real.bge_eq_true, Int.bge_eq_true]
  simp only [hcc, ge_iff_le, le_iff_eq_or_lt, ← Int.floor_lt]
  have h : ↑t ≠ c := by simpa using eq_conflict (t := t) hc
  apply Iff.intro <;> intro hct
  · have h := hct.resolve_left h.symm
    omega
  · omega

-- Absolute value comparisons

theorem abs_eq : (|x| == |y|) = (x == y || x == -y) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, Bool.or_eq_true]
  exact abs_eq_abs

theorem abs_gt : |x|.bgt |y| =
    cond (x.bge 0) (cond (y.bge 0) (x.bgt y) (x.bgt (-y))) (cond (y.bge 0) ((-x).bgt y) ((-x).bgt (-y))) := by
  cases hx : x.bge 0 <;> cases hy : y.bge 0 <;>
    simp only [Real.bge_eq_true, Real.bge_eq_false, Bool.cond_true, Bool.cond_false] at hx hy ⊢
  · rw [abs_eq_neg_self.mpr (le_of_not_ge hx), abs_eq_neg_self.mpr (le_of_not_ge hy)]
  · rw [abs_eq_neg_self.mpr (le_of_not_ge hx), abs_eq_self.mpr hy]
  · rw [abs_eq_self.mpr hx, abs_eq_neg_self.mpr (le_of_not_ge hy)]
  · rw [abs_eq_self.mpr hx, abs_eq_self.mpr hy]

-- ITE lifting

theorem geq_ite_lift {c : Bool} {t s r : Real} : (cond c t s).bge r = cond c (t.bge r) (s.bge r) := by
  cases c <;> rfl

theorem leq_ite_lift {c : Bool} {t s r : Real} : (cond c t s).ble r = cond c (t.ble r) (s.ble r) := by
  cases c <;> rfl

-- min/max rules

theorem min_lt1 : (cond (t.blt s) t s).ble t = true := by
  cases h : t.blt s <;> simp_all

theorem min_lt2 : (cond (t.blt s) t s).ble s = true := by
  cases h : t.blt s <;> simp_all [le_of_lt]

theorem max_geq1 : (cond (t.bge s) t s).bge t = true := by
  cases h : t.bge s <;> simp_all [le_of_lt]

theorem max_geq2 : (cond (t.bge s) t s).bge s = true := by
  cases h : t.bge s <;> simp_all

theorem arith_sine_zero : Real.sin 0 = 0 := Real.sin_zero
theorem arith_sine_pi2 : Real.sin ((1/2) * Real.pi) = 1 := by
  have : 1 / 2 * Real.pi = Real.pi / 2 := one_div_mul_eq_div 2 Real.pi
  rw [this]
  exact Real.sin_pi_div_two

theorem arith_cosine_elim (x : Real) : Real.cos x = Real.sin ((1/2) * Real.pi - x) := by
  have : 1 / 2 * Real.pi = Real.pi / 2 := one_div_mul_eq_div 2 Real.pi
  rw [this]
  exact Eq.symm (Real.sin_pi_div_two_sub x)

theorem arith_tangent_elim (x : Real) : Real.tan x = Real.sin x / Real.cos x := Real.tan_eq_sin_div_cos x
theorem arith_cotangent_elim (x : Real) : Real.cot x = Real.cos x / Real.sin x := Real.cot_eq_cos_div_sin x

-- TODO: Secant and cosecant. There is no definition for those in mathlib. Should we define our own?

end Smt.Reconstruct.Real.Rewrite
