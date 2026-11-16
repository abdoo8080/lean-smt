/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomaz Gomes Mascarenhas, Abdalrhman Mohamed
-/

module

public import Smt.Reconstruct.Bool.Core
public import Smt.Reconstruct.Int.Core
public import Smt.Reconstruct.Real.Core
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

@[expose] public section

namespace Smt.Reconstruct.Real

/-! The lemmas used by proof reconstruction are stated over the reconstructions of SMT-LIB formulas
(see `Smt.Reconstruct.Int`): a proof of a formula `b` is a proof of `b = true`, except that a proof
of an equality `(= t s)` is a proof of `t = s`. -/

variable {a b c d x₁ x₂ y₁ y₂ : Real}

theorem sum_ub₁ (h₁ : a.blt b = true) (h₂ : c.blt d = true) : (a + c).blt (b + d) = true := by
  simp only [Real.blt_eq_true] at *; linarith

theorem sum_ub₂ (h₁ : a.blt b = true) (h₂ : c.ble d = true) : (a + c).blt (b + d) = true := by
  simp only [Real.blt_eq_true, Real.ble_eq_true] at *; linarith

theorem sum_ub₃ (h₁ : a.blt b = true) (h₂ : Bool.eq c d) : (a + c).blt (b + d) = true := by
  have h₂ := h₂.to_eq; simp only [Real.blt_eq_true] at *; linarith

theorem sum_ub₄ (h₁ : a.ble b = true) (h₂ : c.blt d = true) : (a + c).blt (b + d) = true := by
  simp only [Real.blt_eq_true, Real.ble_eq_true] at *; linarith

theorem sum_ub₅ (h₁ : a.ble b = true) (h₂ : c.ble d = true) : (a + c).ble (b + d) = true := by
  simp only [Real.ble_eq_true] at *; linarith

theorem sum_ub₆ (h₁ : a.ble b = true) (h₂ : Bool.eq c d) : (a + c).ble (b + d) = true := by
  have h₂ := h₂.to_eq; simp only [Real.ble_eq_true] at *; linarith

theorem sum_ub₇ (h₁ : Bool.eq a b) (h₂ : c.blt d = true) : (a + c).blt (b + d) = true := by
  have h₁ := h₁.to_eq; simp only [Real.blt_eq_true] at *; linarith

theorem sum_ub₈ (h₁ : Bool.eq a b) (h₂ : c.ble d = true) : (a + c).ble (b + d) = true := by
  have h₁ := h₁.to_eq; simp only [Real.ble_eq_true] at *; linarith

theorem sum_ub₉ (h₁ : Bool.eq a b) (h₂ : Bool.eq c d) : Bool.eq (a + c) (b + d) := by
  apply Bool.eq.of_eq
  rw [h₁.to_eq, h₂.to_eq]

theorem ble_of_eq (h : Bool.eq a b) : a.ble b = true := by
  simp only [Real.ble_eq_true]; exact le_of_eq h.to_eq

theorem mul_abs₁ (h₁ : Bool.eq |x₁| |y₁|) (h₂ : Bool.eq |x₂| |y₂|) :
    Bool.eq |x₁ * x₂| |y₁ * y₂| := by
  apply Bool.eq.of_eq
  rw [abs_mul x₁ x₂, abs_mul y₁ y₂, h₁.to_eq, h₂.to_eq]

theorem mul_abs₂ (h₁ : |x₁|.bgt |y₁| = true)
    (h₂ : (decide (|x₂| = |y₂|) && !decide (|x₂| = 0)) = true) :
    |x₁ * x₂|.bgt |y₁ * y₂| = true := by
  simp only [Real.bgt_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
    decide_eq_false_iff_not] at *
  rw [abs_mul, abs_mul]
  apply mul_lt_mul h₁ (le_of_eq h₂.left.symm) _ (abs_nonneg x₁)
  rewrite [← h₂.left]
  exact lt_of_le_of_ne (abs_nonneg x₂) (Ne.symm h₂.right)

theorem mul_abs₃ (h₁ : |x₁|.bgt |y₁| = true) (h₂ : |x₂|.bgt |y₂| = true) : |x₁ * x₂|.bgt |y₁ * y₂| = true := by
  simp only [Real.bgt_eq_true] at *
  rw [abs_mul, abs_mul]
  apply mul_lt_mul' (le_of_lt h₁) h₂ (abs_nonneg y₂)
  cases Decidable.eq_or_lt_of_le (abs_nonneg y₁) <;> rename_i h
  · rewrite [h]; exact h₁
  · exact lt_trans h h₁

theorem int_tight_ub {i : Int} (h : (i : Real).blt c = true) : i.ble (⌈c⌉ - 1) = true := by
  simp only [Real.blt_eq_true, Int.ble_eq_true] at *
  exact Int.le_of_lt_add_one (Int.sub_add_cancel _ _ ▸ Int.lt_ceil.mpr h)

theorem int_tight_lb {i : Int} (h : (i : Real).bgt c = true) : i.bge (⌊c⌋ + 1) = true := by
  simp only [Real.bgt_eq_true, Int.bge_eq_true] at *
  exact Int.add_one_le_of_lt (Int.floor_lt.mpr h)

theorem trichotomy₁ (h₁ : a.ble b = true) (h₂ : (!decide (a = b)) = true) : a.blt b = true := by
  simp only [Real.ble_eq_true, Real.blt_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at *
  exact lt_of_le_of_ne h₁ h₂

theorem trichotomy₂ (h₁ : a.ble b = true) (h₂ : a.bge b = true) : Bool.eq a b := by
  apply Bool.eq.of_eq
  simp only [Real.ble_eq_true, Real.bge_eq_true] at *
  exact le_antisymm h₁ h₂

theorem trichotomy₃ (h₁ : (!decide (a = b)) = true) (h₂ : a.ble b = true) : a.blt b = true :=
  trichotomy₁ h₂ h₁

theorem trichotomy₄ (h₁ : (!decide (a = b)) = true) (h₂ : a.bge b = true) : a.bgt b = true := by
  simp only [Real.bge_eq_true, Real.bgt_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at *
  exact lt_of_le_of_ne h₂ (Ne.symm h₁)

theorem trichotomy₅ (h₁ : a.bge b = true) (h₂ : a.ble b = true) : Bool.eq a b := by
  apply Bool.eq.of_eq
  simp only [Real.ble_eq_true, Real.bge_eq_true] at *
  exact le_antisymm h₂ h₁

theorem trichotomy₆ (h₁ : a.bge b = true) (h₂ : (!decide (a = b)) = true) : a.bgt b = true := by
  simp only [Real.bge_eq_true, Real.bgt_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at *
  exact lt_of_le_of_ne h₁ (Ne.symm h₂)

theorem abs_elim {x : Real} : Bool.eq |x| (cond (x.blt 0) (-x) x) := by
  apply Bool.eq.of_eq
  rw [Real.blt, Bool.cond_decide]
  cases abs_cases x <;> rename_i h <;> split <;> linarith

theorem lt_eq_sub_lt_zero : (a < b) = (a - b < 0) := by
  apply propext
  constructor
  · apply sub_neg_of_lt
  · apply lt_of_sub_neg

theorem le_eq_sub_le_zero : (a ≤ b) = (a - b ≤ 0) := by
  apply propext
  constructor
  · exact sub_nonpos_of_le
  · exact le_of_sub_nonpos

theorem eq_eq_sub_eq_zero : (a = b) = (a - b = 0) := by
  simp only [sub_eq_zero]

theorem ge_eq_sub_ge_zero : (a ≥ b) = (a - b ≥ 0) := by
  simp only [ge_iff_le, eq_iff_iff]
  constructor
  · exact sub_nonneg_of_le
  · exact le_of_sub_nonneg

theorem gt_eq_sub_gt_zero : (a > b) = (a - b > 0) := by
  simp only [gt_iff_lt, eq_iff_iff]
  constructor
  · exact sub_pos_of_lt
  · exact lt_of_sub_pos

/-! The signs of the constants of `lt_of_sub_eq_pos` and its variants are proved by `norm_num`. -/

theorem blt_of_lt {a b : Real} (h : a < b) : a.blt b = true := decide_eq_true h
theorem bgt_of_gt {a b : Real} (h : a > b) : a.bgt b = true := decide_eq_true h
theorem not_decide_eq_of_ne {a b : Real} (h : a ≠ b) : (!decide (a = b)) = true := by simp [h]

theorem lt_of_sub_eq_pos {c₁ c₂ : Real} (hc₁ : c₁.bgt 0 = true) (hc₂ : c₂.bgt 0 = true) (h : Bool.eq (c₁ * (a₁ - a₂)) (c₂ * (b₁ - b₂))) : Bool.eq (a₁.blt a₂) (b₁.blt b₂) := by
  apply Bool.eq.of_eq
  have h := h.to_eq
  simp only [Real.bgt_eq_true] at hc₁ hc₂
  have {c x y : Real} (hc : c > 0) : (c * (x - y) < 0) = (x - y < 0) := by
    rw (config := { occs := .pos [1] }) [← mul_zero c, mul_lt_mul_iff_right₀ hc]
  simp only [Real.blt]; apply decide_eq_decide.mpr; apply Iff.of_eq
  rw [lt_eq_sub_lt_zero, @lt_eq_sub_lt_zero b₁, ← this hc₁, ← this hc₂, h]

theorem lt_of_sub_eq_neg {c₁ c₂ : Real} (hc₁ : c₁.blt 0 = true) (hc₂ : c₂.blt 0 = true) (h : Bool.eq (c₁ * (a₁ - a₂)) (c₂ * (b₁ - b₂))) : Bool.eq (a₁.blt a₂) (b₁.blt b₂) := by
  apply Bool.eq.of_eq
  have h := h.to_eq
  simp only [Real.blt_eq_true] at hc₁ hc₂
  rewrite [← mul_right_inj' (by norm_num : (-1 : Real) ≠ 0), ← mul_assoc (-1), ← mul_assoc (-1)] at h
  exact (lt_of_sub_eq_pos (by simp only [Real.bgt_eq_true]; linarith) (by simp only [Real.bgt_eq_true]; linarith) (Bool.eq.of_eq h)).to_eq

theorem le_of_sub_eq_pos {c₁ c₂ : Real} (hc₁ : c₁.bgt 0 = true) (hc₂ : c₂.bgt 0 = true) (h : Bool.eq (c₁ * (a₁ - a₂)) (c₂ * (b₁ - b₂))) : Bool.eq (a₁.ble a₂) (b₁.ble b₂) := by
  apply Bool.eq.of_eq
  have h := h.to_eq
  simp only [Real.bgt_eq_true] at hc₁ hc₂
  have {c x y : Real} (hc : c > 0) : (c * (x - y) ≤ 0) = (x - y ≤ 0) := by
    rw (config := { occs := .pos [1] }) [← mul_zero c, mul_le_mul_iff_right₀ hc]
  simp only [Real.ble]; apply decide_eq_decide.mpr; apply Iff.of_eq
  rw [le_eq_sub_le_zero, @le_eq_sub_le_zero b₁, ← this hc₁, ← this hc₂, h]

theorem le_of_sub_eq_neg {c₁ c₂ : Real} (hc₁ : c₁.blt 0 = true) (hc₂ : c₂.blt 0 = true) (h : Bool.eq (c₁ * (a₁ - a₂)) (c₂ * (b₁ - b₂))) : Bool.eq (a₁.ble a₂) (b₁.ble b₂) := by
  apply Bool.eq.of_eq
  have h := h.to_eq
  simp only [Real.blt_eq_true] at hc₁ hc₂
  rewrite [← mul_right_inj' (by norm_num : (-1 : Real) ≠ 0), ← mul_assoc (-1), ← mul_assoc (-1)] at h
  exact (le_of_sub_eq_pos (by simp only [Real.bgt_eq_true]; linarith) (by simp only [Real.bgt_eq_true]; linarith) (Bool.eq.of_eq h)).to_eq

theorem eq_of_sub_eq {c₁ c₂ : Real} (hc₁ : (!decide (c₁ = 0)) = true) (hc₂ : (!decide (c₂ = 0)) = true) (h : Bool.eq (c₁ * (a₁ - a₂)) (c₂ * (b₁ - b₂))) : Bool.eq (decide (a₁ = a₂)) (decide (b₁ = b₂)) := by
  apply Bool.eq.of_eq
  have h := h.to_eq
  simp only [Bool.not_eq_true', decide_eq_false_iff_not] at hc₁ hc₂
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_eq, decide_eq_true_eq]
  apply Iff.intro
  · intro ha
    rewrite [ha, sub_self, mul_zero, eq_comm, mul_eq_zero] at h
    have h := h.resolve_left hc₂
    exact eq_of_sub_eq_zero h
  · intro hb
    rewrite [hb, sub_self, mul_zero, mul_eq_zero] at h
    have h := h.resolve_left hc₁
    exact eq_of_sub_eq_zero h

theorem ge_of_sub_eq_pos {c₁ c₂ : Real} (hc₁ : c₁.bgt 0 = true) (hc₂ : c₂.bgt 0 = true) (h : Bool.eq (c₁ * (a₁ - a₂)) (c₂ * (b₁ - b₂))) : Bool.eq (a₁.bge a₂) (b₁.bge b₂) := by
  apply Bool.eq.of_eq
  have h := h.to_eq
  simp only [Real.bgt_eq_true] at hc₁ hc₂
  have {c x y : Real} (hc : c > 0) : (c * (x - y) ≥ 0) = (x - y ≥ 0) := by
    rw (config := { occs := .pos [1] }) [← mul_zero c, ge_iff_le, mul_le_mul_iff_right₀ hc]
  simp only [Real.bge]; apply decide_eq_decide.mpr; apply Iff.of_eq
  rw [ge_eq_sub_ge_zero, @ge_eq_sub_ge_zero b₁, ← this hc₁, ← this hc₂, h]

theorem ge_of_sub_eq_neg {c₁ c₂ : Real} (hc₁ : c₁.blt 0 = true) (hc₂ : c₂.blt 0 = true) (h : Bool.eq (c₁ * (a₁ - a₂)) (c₂ * (b₁ - b₂))) : Bool.eq (a₁.bge a₂) (b₁.bge b₂) := by
  apply Bool.eq.of_eq
  have h := h.to_eq
  simp only [Real.blt_eq_true] at hc₁ hc₂
  rewrite [← mul_right_inj' (by norm_num : (-1 : Real) ≠ 0), ← mul_assoc (-1), ← mul_assoc (-1)] at h
  exact (ge_of_sub_eq_pos (by simp only [Real.bgt_eq_true]; linarith) (by simp only [Real.bgt_eq_true]; linarith) (Bool.eq.of_eq h)).to_eq

theorem gt_of_sub_eq_pos {c₁ c₂ : Real} (hc₁ : c₁.bgt 0 = true) (hc₂ : c₂.bgt 0 = true) (h : Bool.eq (c₁ * (a₁ - a₂)) (c₂ * (b₁ - b₂))) : Bool.eq (a₁.bgt a₂) (b₁.bgt b₂) := by
  apply Bool.eq.of_eq
  have h := h.to_eq
  simp only [Real.bgt_eq_true] at hc₁ hc₂
  have {c x y : Real} (hc : c > 0) : (c * (x - y) > 0) = (x - y > 0) := by
    rw (config := { occs := .pos [1] }) [← mul_zero c, gt_iff_lt, mul_lt_mul_iff_right₀ hc]
  simp only [Real.bgt]; apply decide_eq_decide.mpr; apply Iff.of_eq
  rw [gt_eq_sub_gt_zero, @gt_eq_sub_gt_zero b₁, ← this hc₁, ← this hc₂, h]

theorem gt_of_sub_eq_neg {c₁ c₂ : Real} (hc₁ : c₁.blt 0 = true) (hc₂ : c₂.blt 0 = true) (h : Bool.eq (c₁ * (a₁ - a₂)) (c₂ * (b₁ - b₂))) : Bool.eq (a₁.bgt a₂) (b₁.bgt b₂) := by
  apply Bool.eq.of_eq
  have h := h.to_eq
  simp only [Real.blt_eq_true] at hc₁ hc₂
  rewrite [← mul_right_inj' (by norm_num : (-1 : Real) ≠ 0), ← mul_assoc (-1), ← mul_assoc (-1)] at h
  exact (gt_of_sub_eq_pos (by simp only [Real.bgt_eq_true]; linarith) (by simp only [Real.bgt_eq_true]; linarith) (Bool.eq.of_eq h)).to_eq

theorem cast_blt {a b : Int} : a.blt b = (a : Real).blt b :=
  decide_eq_decide.mpr Int.cast_lt.symm

theorem cast_ble {a b : Int} : a.ble b = (a : Real).ble b :=
  decide_eq_decide.mpr Int.cast_le.symm

theorem cast_bgt {a b : Int} : a.bgt b = (a : Real).bgt b :=
  decide_eq_decide.mpr Int.cast_lt.symm

theorem cast_bge {a b : Int} : a.bge b = (a : Real).bge b :=
  decide_eq_decide.mpr Int.cast_le.symm

theorem cast_decide_eq {a b : Int} : decide (a = b) = decide ((a : Real) = b) :=
  decide_eq_decide.mpr Int.cast_inj.symm

theorem lt_of_sub_eq_pos_int_left {a₁ a₂ : Int} {b₁ b₂ c₁ c₂ : Real} (hc₁ : c₁.bgt 0 = true) (hc₂ : c₂.bgt 0 = true) (h : Bool.eq (c₁ * ↑(a₁ - a₂)) (c₂ * (b₁ - b₂))) : Bool.eq (a₁.blt a₂) (b₁.blt b₂) := by
  apply Bool.eq.of_eq
  have h := h.to_eq
  rw [Int.cast_sub] at h
  rw [cast_blt]
  exact (lt_of_sub_eq_pos hc₁ hc₂ (Bool.eq.of_eq h)).to_eq

theorem lt_of_sub_eq_neg_int_left {a₁ a₂ : Int} {b₁ b₂ c₁ c₂ : Real} (hc₁ : c₁.blt 0 = true) (hc₂ : c₂.blt 0 = true) (h : Bool.eq (c₁ * ↑(a₁ - a₂)) (c₂ * (b₁ - b₂))) : Bool.eq (a₁.blt a₂) (b₁.blt b₂) := by
  apply Bool.eq.of_eq
  have h := h.to_eq
  rw [Int.cast_sub] at h
  rw [cast_blt]
  exact (lt_of_sub_eq_neg hc₁ hc₂ (Bool.eq.of_eq h)).to_eq

theorem le_of_sub_eq_pos_int_left {a₁ a₂ : Int} {b₁ b₂ c₁ c₂ : Real} (hc₁ : c₁.bgt 0 = true) (hc₂ : c₂.bgt 0 = true) (h : Bool.eq (c₁ * ↑(a₁ - a₂)) (c₂ * (b₁ - b₂))) : Bool.eq (a₁.ble a₂) (b₁.ble b₂) := by
  apply Bool.eq.of_eq
  have h := h.to_eq
  rw [Int.cast_sub] at h
  rw [cast_ble]
  exact (le_of_sub_eq_pos hc₁ hc₂ (Bool.eq.of_eq h)).to_eq

theorem le_of_sub_eq_neg_int_left {a₁ a₂ : Int} {b₁ b₂ c₁ c₂ : Real} (hc₁ : c₁.blt 0 = true) (hc₂ : c₂.blt 0 = true) (h : Bool.eq (c₁ * ↑(a₁ - a₂)) (c₂ * (b₁ - b₂))) : Bool.eq (a₁.ble a₂) (b₁.ble b₂) := by
  apply Bool.eq.of_eq
  have h := h.to_eq
  rw [Int.cast_sub] at h
  rw [cast_ble]
  exact (le_of_sub_eq_neg hc₁ hc₂ (Bool.eq.of_eq h)).to_eq

theorem eq_of_sub_eq_int_left {a₁ a₂ : Int} {b₁ b₂ c₁ c₂ : Real} (hc₁ : (!decide (c₁ = 0)) = true) (hc₂ : (!decide (c₂ = 0)) = true) (h : Bool.eq (c₁ * ↑(a₁ - a₂)) (c₂ * (b₁ - b₂))) : Bool.eq (decide (a₁ = a₂)) (decide (b₁ = b₂)) := by
  apply Bool.eq.of_eq
  have h := h.to_eq
  rw [Int.cast_sub] at h
  rw [cast_decide_eq]
  exact (eq_of_sub_eq hc₁ hc₂ (Bool.eq.of_eq h)).to_eq

theorem ge_of_sub_eq_pos_int_left {a₁ a₂ : Int} {b₁ b₂ c₁ c₂ : Real} (hc₁ : c₁.bgt 0 = true) (hc₂ : c₂.bgt 0 = true) (h : Bool.eq (c₁ * ↑(a₁ - a₂)) (c₂ * (b₁ - b₂))) : Bool.eq (a₁.bge a₂) (b₁.bge b₂) := by
  apply Bool.eq.of_eq
  have h := h.to_eq
  rw [Int.cast_sub] at h
  rw [cast_bge]
  exact (ge_of_sub_eq_pos hc₁ hc₂ (Bool.eq.of_eq h)).to_eq

theorem ge_of_sub_eq_neg_int_left {a₁ a₂ : Int} {b₁ b₂ c₁ c₂ : Real} (hc₁ : c₁.blt 0 = true) (hc₂ : c₂.blt 0 = true) (h : Bool.eq (c₁ * ↑(a₁ - a₂)) (c₂ * (b₁ - b₂))) : Bool.eq (a₁.bge a₂) (b₁.bge b₂) := by
  apply Bool.eq.of_eq
  have h := h.to_eq
  rw [Int.cast_sub] at h
  rw [cast_bge]
  exact (ge_of_sub_eq_neg hc₁ hc₂ (Bool.eq.of_eq h)).to_eq

theorem gt_of_sub_eq_pos_int_left {a₁ a₂ : Int} {b₁ b₂ c₁ c₂ : Real} (hc₁ : c₁.bgt 0 = true) (hc₂ : c₂.bgt 0 = true) (h : Bool.eq (c₁ * ↑(a₁ - a₂)) (c₂ * (b₁ - b₂))) : Bool.eq (a₁.bgt a₂) (b₁.bgt b₂) := by
  apply Bool.eq.of_eq
  have h := h.to_eq
  rw [Int.cast_sub] at h
  rw [cast_bgt]
  exact (gt_of_sub_eq_pos hc₁ hc₂ (Bool.eq.of_eq h)).to_eq

theorem gt_of_sub_eq_neg_int_left {a₁ a₂ : Int} {b₁ b₂ c₁ c₂ : Real} (hc₁ : c₁.blt 0 = true) (hc₂ : c₂.blt 0 = true) (h : Bool.eq (c₁ * ↑(a₁ - a₂)) (c₂ * (b₁ - b₂))) : Bool.eq (a₁.bgt a₂) (b₁.bgt b₂) := by
  apply Bool.eq.of_eq
  have h := h.to_eq
  rw [Int.cast_sub] at h
  rw [cast_bgt]
  exact (gt_of_sub_eq_neg hc₁ hc₂ (Bool.eq.of_eq h)).to_eq

theorem lt_of_sub_eq_pos_int_right {a₁ a₂ : Real} {b₁ b₂ : Int} {c₁ c₂ : Real} (hc₁ : c₁.bgt 0 = true) (hc₂ : c₂.bgt 0 = true) (h : Bool.eq (c₁ * (a₁ - a₂)) (c₂ * ↑(b₁ - b₂))) : Bool.eq (a₁.blt a₂) (b₁.blt b₂) := by
  apply Bool.eq.of_eq
  have h := h.to_eq
  rw [Int.cast_sub] at h
  rw [cast_blt]
  exact (lt_of_sub_eq_pos hc₁ hc₂ (Bool.eq.of_eq h)).to_eq

theorem lt_of_sub_eq_neg_int_right {a₁ a₂ : Real} {b₁ b₂ : Int} {c₁ c₂ : Real} (hc₁ : c₁.blt 0 = true) (hc₂ : c₂.blt 0 = true) (h : Bool.eq (c₁ * (a₁ - a₂)) (c₂ * ↑(b₁ - b₂))) : Bool.eq (a₁.blt a₂) (b₁.blt b₂) := by
  apply Bool.eq.of_eq
  have h := h.to_eq
  rw [Int.cast_sub] at h
  rw [cast_blt]
  exact (lt_of_sub_eq_neg hc₁ hc₂ (Bool.eq.of_eq h)).to_eq

theorem le_of_sub_eq_pos_int_right {a₁ a₂ : Real} {b₁ b₂ : Int} {c₁ c₂ : Real} (hc₁ : c₁.bgt 0 = true) (hc₂ : c₂.bgt 0 = true) (h : Bool.eq (c₁ * (a₁ - a₂)) (c₂ * ↑(b₁ - b₂))) : Bool.eq (a₁.ble a₂) (b₁.ble b₂) := by
  apply Bool.eq.of_eq
  have h := h.to_eq
  rw [Int.cast_sub] at h
  rw [cast_ble]
  exact (le_of_sub_eq_pos hc₁ hc₂ (Bool.eq.of_eq h)).to_eq

theorem le_of_sub_eq_neg_int_right {a₁ a₂ : Real} {b₁ b₂ : Int} {c₁ c₂ : Real} (hc₁ : c₁.blt 0 = true) (hc₂ : c₂.blt 0 = true) (h : Bool.eq (c₁ * (a₁ - a₂)) (c₂ * ↑(b₁ - b₂))) : Bool.eq (a₁.ble a₂) (b₁.ble b₂) := by
  apply Bool.eq.of_eq
  have h := h.to_eq
  rw [Int.cast_sub] at h
  rw [cast_ble]
  exact (le_of_sub_eq_neg hc₁ hc₂ (Bool.eq.of_eq h)).to_eq

theorem eq_of_sub_eq_int_right {a₁ a₂ : Real} {b₁ b₂ : Int} {c₁ c₂ : Real} (hc₁ : (!decide (c₁ = 0)) = true) (hc₂ : (!decide (c₂ = 0)) = true) (h : Bool.eq (c₁ * (a₁ - a₂)) (c₂ * ↑(b₁ - b₂))) : Bool.eq (decide (a₁ = a₂)) (decide (b₁ = b₂)) := by
  apply Bool.eq.of_eq
  have h := h.to_eq
  rw [Int.cast_sub] at h
  rw [cast_decide_eq]
  exact (eq_of_sub_eq hc₁ hc₂ (Bool.eq.of_eq h)).to_eq

theorem ge_of_sub_eq_pos_int_right {a₁ a₂ : Real} {b₁ b₂ : Int} {c₁ c₂ : Real} (hc₁ : c₁.bgt 0 = true) (hc₂ : c₂.bgt 0 = true) (h : Bool.eq (c₁ * (a₁ - a₂)) (c₂ * ↑(b₁ - b₂))) : Bool.eq (a₁.bge a₂) (b₁.bge b₂) := by
  apply Bool.eq.of_eq
  have h := h.to_eq
  rw [Int.cast_sub] at h
  rw [cast_bge]
  exact (ge_of_sub_eq_pos hc₁ hc₂ (Bool.eq.of_eq h)).to_eq

theorem ge_of_sub_eq_neg_int_right {a₁ a₂ : Real} {b₁ b₂ : Int} {c₁ c₂ : Real} (hc₁ : c₁.blt 0 = true) (hc₂ : c₂.blt 0 = true) (h : Bool.eq (c₁ * (a₁ - a₂)) (c₂ * ↑(b₁ - b₂))) : Bool.eq (a₁.bge a₂) (b₁.bge b₂) := by
  apply Bool.eq.of_eq
  have h := h.to_eq
  rw [Int.cast_sub] at h
  rw [cast_bge]
  exact (ge_of_sub_eq_neg hc₁ hc₂ (Bool.eq.of_eq h)).to_eq

theorem gt_of_sub_eq_pos_int_right {a₁ a₂ : Real} {b₁ b₂ : Int} {c₁ c₂ : Real} (hc₁ : c₁.bgt 0 = true) (hc₂ : c₂.bgt 0 = true) (h : Bool.eq (c₁ * (a₁ - a₂)) (c₂ * ↑(b₁ - b₂))) : Bool.eq (a₁.bgt a₂) (b₁.bgt b₂) := by
  apply Bool.eq.of_eq
  have h := h.to_eq
  rw [Int.cast_sub] at h
  rw [cast_bgt]
  exact (gt_of_sub_eq_pos hc₁ hc₂ (Bool.eq.of_eq h)).to_eq

theorem gt_of_sub_eq_neg_int_right {a₁ a₂ : Real} {b₁ b₂ : Int} {c₁ c₂ : Real} (hc₁ : c₁.blt 0 = true) (hc₂ : c₂.blt 0 = true) (h : Bool.eq (c₁ * (a₁ - a₂)) (c₂ * ↑(b₁ - b₂))) : Bool.eq (a₁.bgt a₂) (b₁.bgt b₂) := by
  apply Bool.eq.of_eq
  have h := h.to_eq
  rw [Int.cast_sub] at h
  rw [cast_bgt]
  exact (gt_of_sub_eq_neg hc₁ hc₂ (Bool.eq.of_eq h)).to_eq

theorem mul_sign₁ (ha : a.blt 0 = true) (hb : b.blt 0 = true) : (a * b).bgt 0 = true := by
  simp only [Real.blt_eq_true, Real.bgt_eq_true] at *
  exact mul_pos_of_neg_of_neg ha hb

theorem mul_sign₃ (ha : a.blt 0 = true) (hb : b.bgt 0 = true) : (a * b).blt 0 = true := by
  simp only [Real.blt_eq_true, Real.bgt_eq_true] at *
  exact mul_neg_of_neg_of_pos ha hb

theorem mul_sign₄ (ha : a.bgt 0 = true) (hb : b.blt 0 = true) : (a * b).blt 0 = true := by
  simp only [Real.blt_eq_true, Real.bgt_eq_true] at *
  exact mul_neg_of_pos_of_neg ha hb

theorem mul_sign₆ (ha : a.bgt 0 = true) (hb : b.bgt 0 = true) : (a * b).bgt 0 = true := by
  simp only [Real.bgt_eq_true] at *
  exact mul_pos ha hb

theorem mul_sign₀ (ha : (!decide (a = 0)) = true) : (a * a).bgt 0 = true := by
  simp only [Bool.not_eq_true', decide_eq_false_iff_not, Real.bgt_eq_true] at *
  exact mul_self_pos.mpr ha

theorem mul_sign₂ (ha : a.blt 0 = true) (hb : (!decide (b = 0)) = true) :
    (a * b * b).blt 0 = true := by
  simp only [Real.blt_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at *
  rw [mul_assoc]
  exact mul_neg_of_neg_of_pos ha (mul_self_pos.mpr hb)

theorem mul_sign₅ (ha : a.bgt 0 = true) (hb : (!decide (b = 0)) = true) :
    (a * b * b).bgt 0 = true := by
  simp only [Real.bgt_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at *
  rw [mul_assoc]
  exact mul_pos ha (mul_self_pos.mpr hb)

theorem mul_pos_lt : ((c.bgt 0 && a.blt b).imp ((c * a).blt (c * b))) = true := by
  simp only [Bool.imp_eq_true, Bool.and_eq_true, Real.bgt_eq_true, Real.blt_eq_true]
  exact fun h => mul_lt_mul_of_pos_left h.2 h.1

theorem mul_pos_le : ((c.bgt 0 && a.ble b).imp ((c * a).ble (c * b))) = true := by
  simp only [Bool.imp_eq_true, Bool.and_eq_true, Real.bgt_eq_true, Real.ble_eq_true]
  exact fun h => mul_le_mul_of_nonneg_left h.2 (le_of_lt h.1)

theorem mul_pos_gt : ((c.bgt 0 && a.bgt b).imp ((c * a).bgt (c * b))) = true := by
  simp only [Bool.imp_eq_true, Bool.and_eq_true, Real.bgt_eq_true]
  exact fun h => mul_lt_mul_of_pos_left h.2 h.1

theorem mul_pos_ge : ((c.bgt 0 && a.bge b).imp ((c * a).bge (c * b))) = true := by
  simp only [Bool.imp_eq_true, Bool.and_eq_true, Real.bgt_eq_true, Real.bge_eq_true]
  exact fun h => mul_le_mul_of_nonneg_left h.2 (le_of_lt h.1)

theorem mul_pos_eq : ((c.bgt 0 && decide (a = b)).imp (decide (c * a = c * b))) = true := by
  simp only [Bool.imp_eq_true, Bool.and_eq_true, Real.bgt_eq_true, decide_eq_true_eq]
  intro h
  rw [h.2]

theorem mul_neg_lt : ((c.blt 0 && a.blt b).imp ((c * a).bgt (c * b))) = true := by
  simp only [Bool.imp_eq_true, Bool.and_eq_true, Real.blt_eq_true, Real.bgt_eq_true]
  exact fun h => mul_lt_mul_of_neg_left h.2 h.1

theorem mul_neg_le : ((c.blt 0 && a.ble b).imp ((c * a).bge (c * b))) = true := by
  simp only [Bool.imp_eq_true, Bool.and_eq_true, Real.blt_eq_true, Real.ble_eq_true, Real.bge_eq_true]
  exact fun h => mul_le_mul_of_nonpos_left h.2 (le_of_lt h.1)

theorem mul_neg_gt : ((c.blt 0 && a.bgt b).imp ((c * a).blt (c * b))) = true := by
  simp only [Bool.imp_eq_true, Bool.and_eq_true, Real.blt_eq_true, Real.bgt_eq_true]
  exact fun h => mul_lt_mul_of_neg_left h.2 h.1

theorem mul_neg_ge : ((c.blt 0 && a.bge b).imp ((c * a).ble (c * b))) = true := by
  simp only [Bool.imp_eq_true, Bool.and_eq_true, Real.blt_eq_true, Real.bge_eq_true, Real.ble_eq_true]
  exact fun h => mul_le_mul_of_nonpos_left h.2 (le_of_lt h.1)

theorem mul_neg_eq : ((c.blt 0 && decide (a = b)).imp (decide (c * a = c * b))) = true := by
  simp only [Bool.imp_eq_true, Bool.and_eq_true, Real.blt_eq_true, decide_eq_true_eq]
  intro h
  rw [h.2]

theorem mul_tangent_mp_lower (h : x * y ≤ b * x + a * y - a * b)
  : x ≤ a ∧ y ≥ b ∨ x ≥ a ∧ y ≤ b := by
  match lt_trichotomy (x - a) 0, lt_trichotomy (y - b) 0 with
  | Or.inl xaNeg,           Or.inl ybNeg           =>
    nlinarith
  | Or.inl xaNeg,           Or.inr (Or.inl ybZero) =>
    have xaNeg' := le_of_lt xaNeg
    simp at xaNeg'
    have ybZero' := ge_of_eq ybZero
    simp at ybZero'
    exact Or.inl (And.intro xaNeg' ybZero')
  | Or.inl xaNeg,           Or.inr (Or.inr ybPos)  =>
    have xaNeg' := le_of_lt xaNeg
    simp at xaNeg'
    have ybPos' := le_of_lt ybPos
    simp at ybPos'
    exact Or.inl (And.intro xaNeg' ybPos')
  | Or.inr (Or.inl xaZero), Or.inl ybNeg           =>
    have xaZero' := ge_of_eq xaZero
    simp at xaZero'
    have ybNeg' := le_of_lt ybNeg
    simp at ybNeg'
    exact Or.inr (And.intro xaZero' ybNeg')
  | Or.inr (Or.inl xaZero), Or.inr (Or.inl ybZero) =>
    have xaZero' := le_of_eq xaZero
    simp at xaZero'
    have ybZero' := ge_of_eq ybZero
    simp at ybZero'
    exact Or.inl (And.intro xaZero' ybZero')
  | Or.inr (Or.inl xaZero), Or.inr (Or.inr ybPos)  =>
    have xaZero' := le_of_eq xaZero
    simp at xaZero'
    have ybPos' := le_of_lt ybPos
    simp at ybPos'
    exact Or.inl (And.intro xaZero' ybPos')
  | Or.inr (Or.inr xaPos),  Or.inl ybNeg           =>
    have xaPos' := le_of_lt xaPos
    simp at xaPos'
    have ybNeg' := le_of_lt ybNeg
    simp at ybNeg'
    exact Or.inr (And.intro xaPos' ybNeg')
  | Or.inr (Or.inr xaPos),  Or.inr (Or.inl ybZero) =>
    have xaPos' := le_of_lt xaPos
    simp at xaPos'
    have ybZero' := le_of_eq ybZero
    simp at ybZero'
    exact Or.inr (And.intro xaPos' ybZero')
  | Or.inr (Or.inr xaPos),  Or.inr (Or.inr ybPos)  =>
    nlinarith

theorem mul_tangent_mpr_lower (h : x ≤ a ∧ y ≥ b ∨ x ≥ a ∧ y ≤ b)
  : x * y ≤ b * x + a * y - a * b := by
  match h with
  | Or.inl (And.intro h₁ h₂) => nlinarith
  | Or.inr (And.intro h₁ h₂) => nlinarith

theorem mul_tangent_lower :
  x * y ≤ b * x + a * y - a * b ↔ x ≤ a ∧ y ≥ b ∨ x ≥ a ∧ y ≤ b :=
  ⟨mul_tangent_mp_lower, mul_tangent_mpr_lower⟩

theorem mul_tangent_lower_eq {x y : Real} :
    Bool.eq ((x * y).ble (b * x + a * y - a * b)) (x.ble a && y.bge b || x.bge a && y.ble b) :=
    Bool.eq.of_eq <| by
  apply Bool.eq_iff_iff.mpr
  simp only [Real.ble_eq_true, Real.bge_eq_true, Bool.or_eq_true, Bool.and_eq_true]
  exact mul_tangent_lower

theorem mul_tangent_mp_upper (h : x * y ≥ b * x + a * y - a * b)
  : x ≤ a ∧ y ≤ b ∨ x ≥ a ∧ y ≥ b := by
  match lt_trichotomy (x - a) 0, lt_trichotomy (y - b) 0 with
  | Or.inl xaNeg,           Or.inl ybNeg           =>
    have xaNeg' := le_of_lt xaNeg
    simp at xaNeg'
    have ybNeg' := le_of_lt ybNeg
    simp at ybNeg'
    exact Or.inl (And.intro xaNeg' ybNeg')
  | Or.inl xaNeg,           Or.inr (Or.inl ybZero) =>
    have xaNeg' := le_of_lt xaNeg
    simp at xaNeg'
    have ybZero' := le_of_eq ybZero
    simp at ybZero'
    exact Or.inl (And.intro xaNeg' ybZero')
  | Or.inl xaNeg,           Or.inr (Or.inr ybPos)  =>
    nlinarith
  | Or.inr (Or.inl xaZero), Or.inl ybNeg           =>
    have xaZero' := le_of_eq xaZero
    simp at xaZero'
    have ybNeg' := le_of_lt ybNeg
    simp at ybNeg'
    exact Or.inl (And.intro xaZero' ybNeg')
  | Or.inr (Or.inl xaZero), Or.inr (Or.inl ybZero) =>
    have xaZero' := le_of_eq xaZero
    simp at xaZero'
    have ybZero' := le_of_eq ybZero
    simp at ybZero'
    exact Or.inl (And.intro xaZero' ybZero')
  | Or.inr (Or.inl xaZero), Or.inr (Or.inr ybPos)  =>
    have xaZero' := ge_of_eq xaZero
    simp at xaZero'
    have ybPos' := le_of_lt ybPos
    simp at ybPos'
    exact Or.inr (And.intro xaZero' ybPos')
  | Or.inr (Or.inr xaPos),  Or.inl ybNeg           =>
    nlinarith
  | Or.inr (Or.inr xaPos),  Or.inr (Or.inl ybZero) =>
    have xaPos' := le_of_lt xaPos
    simp at xaPos'
    have ybZero' := ge_of_eq ybZero
    simp at ybZero'
    exact Or.inr (And.intro xaPos' ybZero')
  | Or.inr (Or.inr xaPos),  Or.inr (Or.inr ybPos)  =>
    have xaPos' := le_of_lt xaPos
    simp at xaPos'
    have ybPos' := le_of_lt ybPos
    simp at ybPos'
    exact Or.inr (And.intro xaPos' ybPos')

theorem mul_tangent_mpr_upper (h : x ≤ a ∧ y ≤ b ∨ x ≥ a ∧ y ≥ b)
  : x * y ≥ b * x + a * y - a * b := by
  match h with
  | Or.inl (And.intro h₁ h₂) => nlinarith
  | Or.inr (And.intro h₁ h₂) => nlinarith

theorem mul_tangent_upper
  : x * y ≥ b * x + a * y - a * b ↔ x ≤ a ∧ y ≤ b ∨ x ≥ a ∧ y ≥ b :=
  ⟨mul_tangent_mp_upper, mul_tangent_mpr_upper⟩

theorem mul_tangent_upper_eq {x y : Real} :
    Bool.eq ((x * y).bge (b * x + a * y - a * b)) (x.ble a && y.ble b || x.bge a && y.bge b) :=
    Bool.eq.of_eq <| by
  apply Bool.eq_iff_iff.mpr
  simp only [Real.ble_eq_true, Real.bge_eq_true, Bool.or_eq_true, Bool.and_eq_true]
  exact mul_tangent_upper

end Smt.Reconstruct.Real
