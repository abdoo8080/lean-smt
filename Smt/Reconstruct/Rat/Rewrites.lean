/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed, Harun Khan
-/

module

public import Smt.Reconstruct.Bool.Core
public import Smt.Reconstruct.Rat.Lemmas

@[expose] public section

namespace Smt.Reconstruct.Rat.Rewrite

open Function

-- https://github.com/cvc5/cvc5/blob/main/src/theory/arith/rewrites

/-! The rewrites are stated over the reconstructions of SMT-LIB terms (see
`Smt.Reconstruct.Int.Rewrite`). -/

variable {t s x y : Rat}

theorem div_total_zero : Bool.eq (t / 0) 0 :=
  Bool.eq.of_eq <| Rat.div_def t 0 ▸ Rat.inv_zero.symm ▸ Rat.mul_zero t

-- Eliminations

theorem elim_gt : Bool.eq (t.bgt s) (!t.ble s) := by
  apply Bool.eq.of_eq
  apply Bool.eq_iff_iff.mpr
  rw [Bool.not_eq_true', Rat.ble_eq_false]
  exact Rat.not_le.symm
theorem elim_lt : Bool.eq (t.blt s) (!t.bge s) := by
  apply Bool.eq.of_eq
  apply Bool.eq_iff_iff.mpr
  rw [Bool.not_eq_true', Rat.bge_eq_false]
  exact Rat.not_le.symm
theorem elim_leq : Bool.eq (t.ble s) (s.bge t) :=
  Bool.eq.of_eq <| rfl

theorem geq_norm1 : Bool.eq (t.bge s) ((t - s).bge 0) := by
  apply Bool.eq.of_eq
  apply Bool.eq_iff_iff.mpr
  rw [Rat.bge_eq_true, Rat.bge_eq_true]
  exact Rat.le_iff_sub_nonneg s t

theorem eq_elim : Bool.eq (decide (t = s)) (t.bge s && t.ble s) := by
  apply Bool.eq.of_eq
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_eq, Bool.and_eq_true, Rat.bge_eq_true, Rat.ble_eq_true, ge_iff_le, And.comm]
  exact Rat.le_antisymm_iff

theorem eq_conflict {t : Int} {c : Rat} (hcc : Bool.eq (decide ((c.floor : Rat) = c)) false) :
    Bool.eq (decide ((t : Rat) = c)) false := by
  apply Bool.eq.of_eq
  have hcc := hcc.to_eq
  simp only [decide_eq_false_iff_not] at *
  intro htc
  have hcc : c.floor < c := (Rat.le_iff_eq_or_lt.mp (Rat.floor_le_self c)).resolve_right hcc
  cases Int.lt_trichotomy t c.floor <;> rename_i htcf
  · have hntc : ↑t ≠ c := (Rat.lt_iff_le_and_ne.mp (Rat.lt_trans (Rat.cast_lt2 htcf) hcc)).right
    contradiction
  · cases htcf <;> rename_i htcf
    · simp_all
    · have h : c < t := by
        apply @Rat.lt_of_lt_of_le _ _ _
        · exact Rat.self_le_floor_add_one c
        · exact Rat.cast_le2 htcf
      simp_all [Rat.lt_irrefl]

set_option warn.sorry false in
theorem geq_tighten {t : Int} {c : Rat} {cc : Int}
    (hc : Bool.eq (decide ((c.floor : Rat) = c)) false) (hcc : Bool.eq cc (c.floor + 1)) :
    Bool.eq ((t : Rat).bge c) (t.bge cc) := by
  apply Bool.eq.of_eq
  have hcc := hcc.to_eq
  have Int.floor_lt {z : Int} {a : Rat} : a.floor < z ↔ a < ↑z := sorry
  apply Bool.eq_iff_iff.mpr
  rw [Rat.bge_eq_true, Int.bge_eq_true]
  simp only [hcc, ge_iff_le, Rat.le_iff_eq_or_lt, ← Int.floor_lt]
  have h : ↑t ≠ c := by simpa [decide_eq_false_iff_not] using (eq_conflict (t := t) hc).to_eq
  apply Iff.intro <;> intro hct
  · have h := hct.resolve_right h.symm
    omega
  · omega

-- Absolute value comparisons

set_option warn.sorry false in
theorem abs_eq : Bool.eq (decide (x.abs = y.abs)) (decide (x = y) || decide (x = -y)) := by
  apply Bool.eq.of_eq
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, Bool.or_eq_true]
  cases hx : decide (x < 0) <;> cases hy : decide (y < 0) <;> simp_all [Rat.abs] <;> sorry

set_option warn.sorry false in
theorem abs_gt : Bool.eq (x.abs.bgt y.abs)
    (cond (x.bge 0) (cond (y.bge 0) (x.bgt y) (x.bgt (-y)))
      (cond (y.bge 0) ((-x).bgt y) ((-x).bgt (-y)))) := by
  apply Bool.eq.of_eq
  sorry

-- ITE lifting

theorem geq_ite_lift {c : Bool} {t s r : Rat} :
    Bool.eq ((cond c t s).bge r) (cond c (t.bge r) (s.bge r)) := by
  apply Bool.eq.of_eq
  cases c <;> rfl

theorem leq_ite_lift {c : Bool} {t s r : Rat} :
    Bool.eq ((cond c t s).ble r) (cond c (t.ble r) (s.ble r)) := by
  apply Bool.eq.of_eq
  cases c <;> rfl

-- min/max rules

theorem min_lt1 : Bool.eq ((cond (t.blt s) t s).ble t) true := by
  apply Bool.eq.of_eq
  cases h : t.blt s
  · rw [Bool.cond_false, Rat.ble_eq_true]; rw [Rat.blt_eq_false] at h; exact Rat.not_lt.mp h
  · rw [Bool.cond_true, Rat.ble_eq_true]; exact Rat.le_refl

theorem min_lt2 : Bool.eq ((cond (t.blt s) t s).ble s) true := by
  apply Bool.eq.of_eq
  cases h : t.blt s
  · rw [Bool.cond_false, Rat.ble_eq_true]; exact Rat.le_refl
  · rw [Bool.cond_true, Rat.ble_eq_true]; exact Rat.le_of_lt h

theorem max_geq1 : Bool.eq ((cond (t.bge s) t s).bge t) true := by
  apply Bool.eq.of_eq
  cases h : t.bge s
  · rw [Bool.cond_false, Rat.bge_eq_true]; rw [Rat.bge_eq_false] at h; exact Rat.le_of_not_le h
  · rw [Bool.cond_true, Rat.bge_eq_true]; exact Rat.le_refl

theorem max_geq2 : Bool.eq ((cond (t.bge s) t s).bge s) true := by
  apply Bool.eq.of_eq
  cases h : t.bge s
  · rw [Bool.cond_false, Rat.bge_eq_true]; exact Rat.le_refl
  · rw [Bool.cond_true]; exact h

end Smt.Reconstruct.Rat.Rewrite
