/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomaz Gomes Mascarenhas, Abdalrhman Mohamed
-/

module

public import Smt.Reconstruct.Bool.Core
public import Smt.Reconstruct.Int.Core

@[expose] public section

private theorem Int.mul_eq_zero_left {x y : Int} (hx : x ≠ 0) (hxy : x * y = 0) : y = 0 := by
  rewrite [Int.mul_eq_zero] at hxy
  exact hxy.resolve_left hx

namespace Smt.Reconstruct.Int

/-! The lemmas are stated over the reconstructions of SMT-LIB formulas (see
`Smt.Reconstruct.Int.Rewrite`): a proof of a formula `b` is a proof of `b = true`, except that a
proof of an equality `(= t s)` is a proof of `t = s`. -/

-- `==` is the reconstruction of SMT-LIB's `=` (see `Smt.Reconstruct.Bool.mkBEq`).
attribute [local instance high] instBEqOfDecidableEq

variable {a b c d x₁ x₂ y₁ y₂ : Int}

theorem sum_ub₁ (h₁ : a.blt b = true) (h₂ : c.blt d = true) : (a + c).blt (b + d) = true := by
  simp only [Int.blt_eq_true] at *; omega

theorem sum_ub₂ (h₁ : a.blt b = true) (h₂ : c.ble d = true) : (a + c).blt (b + d) = true := by
  simp only [Int.blt_eq_true, Int.ble_eq_true] at *; omega

theorem sum_ub₃ (h₁ : a.blt b = true) (h₂ : c = d) : (a + c).blt (b + d) = true := by
  simp only [Int.blt_eq_true] at *; omega

theorem sum_ub₄ (h₁ : a.ble b = true) (h₂ : c.blt d = true) : (a + c).blt (b + d) = true := by
  simp only [Int.blt_eq_true, Int.ble_eq_true] at *; omega

theorem sum_ub₅ (h₁ : a.ble b = true) (h₂ : c.ble d = true) : (a + c).ble (b + d) = true := by
  simp only [Int.ble_eq_true] at *; omega

theorem sum_ub₆ (h₁ : a.ble b = true) (h₂ : c = d) : (a + c).ble (b + d) = true := by
  simp only [Int.ble_eq_true] at *; omega

theorem sum_ub₇ (h₁ : a = b) (h₂ : c.blt d = true) : (a + c).blt (b + d) = true := by
  simp only [Int.blt_eq_true] at *; omega

theorem sum_ub₈ (h₁ : a = b) (h₂ : c.ble d = true) : (a + c).ble (b + d) = true := by
  simp only [Int.ble_eq_true] at *; omega

theorem sum_ub₉ (h₁ : a = b) (h₂ : c = d) : a + c = b + d := by
  rw [h₁, h₂]

theorem ble_of_eq (h : a = b) : a.ble b = true := by
  simp only [Int.ble_eq_true]; omega

theorem mul_abs₁ (h₁ : x₁.abs = y₁.abs) (h₂ : x₂.abs = y₂.abs) : (x₁ * x₂).abs = (y₁ * y₂).abs := by
  rw [Int.abs_mul x₁ x₂, Int.abs_mul y₁ y₂, h₁, h₂]

theorem mul_abs₂ (h₁ : x₁.abs.bgt y₁.abs = true) (h₂ : (x₂.abs == y₂.abs && !(x₂.abs == 0)) = true) :
    (x₁ * x₂).abs.bgt (y₁ * y₂).abs = true := by
  simp only [Int.bgt_eq_true, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', beq_eq_false_iff_ne] at *
  rewrite [Int.abs_mul, Int.abs_mul]
  apply Int.mul_lt_mul h₁ (Int.le_of_eq h₂.left.symm) _ (Int.abs_nonneg x₁)
  rewrite [← h₂.left]
  exact Int.lt_of_le_of_ne (Int.abs_nonneg x₂) h₂.right.symm

theorem mul_abs₃ (h₁ : x₁.abs.bgt y₁.abs = true) (h₂ : x₂.abs.bgt y₂.abs = true) :
    (x₁ * x₂).abs.bgt (y₁ * y₂).abs = true := by
  simp only [Int.bgt_eq_true] at *
  rw [Int.abs_mul, Int.abs_mul]
  apply Int.mul_lt_mul' (Int.le_of_lt h₁) h₂ (Int.abs_nonneg y₂)
  cases Int.le_iff_eq_or_lt.mp (Int.abs_nonneg y₁) <;> rename_i h
  · rewrite [h]; exact h₁
  · exact Int.lt_trans h h₁

theorem int_tight_ub {i : Int} (h : i.blt c = true) : i.ble (c - 1) = true := by
  simp only [Int.blt_eq_true, Int.ble_eq_true] at *; omega

theorem int_tight_lb {i : Int} (h : i.bgt c = true) : i.bge (c + 1) = true := by
  simp only [Int.bgt_eq_true, Int.bge_eq_true] at *; omega

theorem trichotomy₁ (h₁ : a.ble b = true) (h₂ : (!(a == b)) = true) : a.blt b = true := by
  simp only [Int.ble_eq_true, Int.blt_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne] at *; omega

theorem trichotomy₂ (h₁ : a.ble b = true) (h₂ : a.bge b = true) : a = b := by
  simp only [Int.ble_eq_true, Int.bge_eq_true] at *; omega

theorem trichotomy₃ (h₁ : (!(a == b)) = true) (h₂ : a.ble b = true) : a.blt b = true := by
  simp only [Int.ble_eq_true, Int.blt_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne] at *; omega

theorem trichotomy₄ (h₁ : (!(a == b)) = true) (h₂ : a.bge b = true) : a.bgt b = true := by
  simp only [Int.bge_eq_true, Int.bgt_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne] at *; omega

theorem trichotomy₅ (h₁ : a.bge b = true) (h₂ : a.ble b = true) : a = b := by
  simp only [Int.ble_eq_true, Int.bge_eq_true] at *; omega

theorem trichotomy₆ (h₁ : a.bge b = true) (h₂ : (!(a == b)) = true) : a.bgt b = true := by
  simp only [Int.bge_eq_true, Int.bgt_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne] at *; omega

theorem abs_elim {x : Int} : x.abs = cond (x.blt 0) (-x) x := by
  rw [Int.blt, Bool.cond_decide]; rfl

theorem lt_eq_sub_lt_zero : (a < b) = (a - b < 0) := by
  apply propext
  constructor
  · apply Int.sub_neg_of_lt
  · apply Int.lt_of_sub_neg

theorem le_eq_sub_le_zero : (a ≤ b) = (a - b ≤ 0) := by
  apply propext
  constructor
  · exact Int.sub_nonpos_of_le
  · exact Int.le_of_sub_nonpos

theorem eq_eq_sub_eq_zero : (a = b) = (a - b = 0) := by
  simp only [Int.sub_eq_zero]

theorem ge_eq_sub_ge_zero : (a ≥ b) = (a - b ≥ 0) := by
  simp only [ge_iff_le, eq_iff_iff]
  constructor
  · exact Int.sub_nonneg_of_le
  · exact Int.le_of_sub_nonneg

theorem gt_eq_sub_gt_zero : (a > b) = (a - b > 0) := by
  simp only [gt_iff_lt, eq_iff_iff]
  constructor
  · exact Int.sub_pos_of_lt
  · exact Int.lt_of_sub_pos

theorem lt_of_sub_eq_pos {c₁ c₂ : Int} (hc₁ : c₁.bgt 0 = true) (hc₂ : c₂.bgt 0 = true) (h : c₁ * (a₁ - a₂) = c₂ * (b₁ - b₂)) : a₁.blt a₂ = b₁.blt b₂ := by
  simp only [Int.bgt_eq_true] at hc₁ hc₂
  have {c x y : Int} (hc : c > 0) : (c * (x - y) < 0) = (x - y < 0) := by
    rw (config := { occs := .pos [1] }) [← Int.mul_zero c, Int.mul_lt_mul_left hc]
  simp only [Int.blt]; apply decide_eq_decide.mpr; apply Iff.of_eq
  rw [lt_eq_sub_lt_zero, @lt_eq_sub_lt_zero b₁, ← this hc₁, ← this hc₂, h]

theorem lt_of_sub_eq_neg {c₁ c₂ : Int} (hc₁ : c₁.blt 0 = true) (hc₂ : c₂.blt 0 = true) (h : c₁ * (a₁ - a₂) = c₂ * (b₁ - b₂)) : a₁.blt a₂ = b₁.blt b₂ := by
  simp only [Int.blt_eq_true] at hc₁ hc₂
  rewrite [← Int.mul_eq_mul_left_iff (by decide : -1 ≠ 0), ← Int.mul_assoc (-1), ← Int.mul_assoc (-1)] at h
  apply lt_of_sub_eq_pos (by simp only [Int.bgt_eq_true]; omega) (by simp only [Int.bgt_eq_true]; omega) h

theorem le_of_sub_eq_pos {c₁ c₂ : Int} (hc₁ : c₁.bgt 0 = true) (hc₂ : c₂.bgt 0 = true) (h : c₁ * (a₁ - a₂) = c₂ * (b₁ - b₂)) : a₁.ble a₂ = b₁.ble b₂ := by
  simp only [Int.bgt_eq_true] at hc₁ hc₂
  have {c x y : Int} (hc : c > 0) : (c * (x - y) ≤ 0) = (x - y ≤ 0) := by
    rw (config := { occs := .pos [1] }) [← Int.mul_zero c, Int.mul_le_mul_left hc]
  simp only [Int.ble]; apply decide_eq_decide.mpr; apply Iff.of_eq
  rw [le_eq_sub_le_zero, @le_eq_sub_le_zero b₁, ← this hc₁, ← this hc₂, h]

theorem le_of_sub_eq_neg {c₁ c₂ : Int} (hc₁ : c₁.blt 0 = true) (hc₂ : c₂.blt 0 = true) (h : c₁ * (a₁ - a₂) = c₂ * (b₁ - b₂)) : a₁.ble a₂ = b₁.ble b₂ := by
  simp only [Int.blt_eq_true] at hc₁ hc₂
  rewrite [← Int.mul_eq_mul_left_iff (by decide : -1 ≠ 0), ← Int.mul_assoc (-1), ← Int.mul_assoc (-1)] at h
  apply le_of_sub_eq_pos (by simp only [Int.bgt_eq_true]; omega) (by simp only [Int.bgt_eq_true]; omega) h

theorem eq_of_sub_eq {c₁ c₂ : Int} (hc₁ : (!(c₁ == 0)) = true) (hc₂ : (!(c₂ == 0)) = true) (h : c₁ * (a₁ - a₂) = c₂ * (b₁ - b₂)) : (a₁ == a₂) = (b₁ == b₂) := by
  simp only [Bool.not_eq_true', beq_eq_false_iff_ne] at hc₁ hc₂
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq]
  apply Iff.intro
  · intro ha
    rewrite [ha, Int.sub_self, Int.mul_zero, eq_comm, Int.mul_eq_zero] at h
    omega
  · intro hb
    rewrite [hb, Int.sub_self, Int.mul_zero, Int.mul_eq_zero] at h
    omega

theorem ge_of_sub_eq_pos {c₁ c₂ : Int} (hc₁ : c₁.bgt 0 = true) (hc₂ : c₂.bgt 0 = true) (h : c₁ * (a₁ - a₂) = c₂ * (b₁ - b₂)) : a₁.bge a₂ = b₁.bge b₂ := by
  simp only [Int.bgt_eq_true] at hc₁ hc₂
  have {c x y : Int} (hc : c > 0) : (c * (x - y) ≥ 0) = (x - y ≥ 0) := by
    rw (config := { occs := .pos [1] }) [← Int.mul_zero c, ge_iff_le, Int.mul_le_mul_left hc]
  simp only [Int.bge]; apply decide_eq_decide.mpr; apply Iff.of_eq
  rw [ge_eq_sub_ge_zero, @ge_eq_sub_ge_zero b₁, ← this hc₁, ← this hc₂, h]

theorem ge_of_sub_eq_neg {c₁ c₂ : Int} (hc₁ : c₁.blt 0 = true) (hc₂ : c₂.blt 0 = true) (h : c₁ * (a₁ - a₂) = c₂ * (b₁ - b₂)) : a₁.bge a₂ = b₁.bge b₂ := by
  simp only [Int.blt_eq_true] at hc₁ hc₂
  rewrite [← Int.mul_eq_mul_left_iff (by decide : -1 ≠ 0), ← Int.mul_assoc (-1), ← Int.mul_assoc (-1)] at h
  apply ge_of_sub_eq_pos (by simp only [Int.bgt_eq_true]; omega) (by simp only [Int.bgt_eq_true]; omega) h

theorem gt_of_sub_eq_pos {c₁ c₂ : Int} (hc₁ : c₁.bgt 0 = true) (hc₂ : c₂.bgt 0 = true) (h : c₁ * (a₁ - a₂) = c₂ * (b₁ - b₂)) : a₁.bgt a₂ = b₁.bgt b₂ := by
  simp only [Int.bgt_eq_true] at hc₁ hc₂
  have {c x y : Int} (hc : c > 0) : (c * (x - y) > 0) = (x - y > 0) := by
    rw (config := { occs := .pos [1] }) [← Int.mul_zero c, gt_iff_lt, Int.mul_lt_mul_left hc]
  simp only [Int.bgt]; apply decide_eq_decide.mpr; apply Iff.of_eq
  rw [gt_eq_sub_gt_zero, @gt_eq_sub_gt_zero b₁, ← this hc₁, ← this hc₂, h]

theorem gt_of_sub_eq_neg {c₁ c₂ : Int} (hc₁ : c₁.blt 0 = true) (hc₂ : c₂.blt 0 = true) (h : c₁ * (a₁ - a₂) = c₂ * (b₁ - b₂)) : a₁.bgt a₂ = b₁.bgt b₂ := by
  simp only [Int.blt_eq_true] at hc₁ hc₂
  rewrite [← Int.mul_eq_mul_left_iff (by decide : -1 ≠ 0), ← Int.mul_assoc (-1), ← Int.mul_assoc (-1)] at h
  apply gt_of_sub_eq_pos (by simp only [Int.bgt_eq_true]; omega) (by simp only [Int.bgt_eq_true]; omega) h

theorem mul_sign₁ (ha : a.blt 0 = true) (hb : b.blt 0 = true) : (a * b).bgt 0 = true := by
  simp only [Int.blt_eq_true, Int.bgt_eq_true] at *
  have h := Int.mul_lt_mul_of_neg_right ha hb
  simp at h
  exact h

theorem mul_sign₃ (ha : a.blt 0 = true) (hb : b.bgt 0 = true) : (a * b).blt 0 = true := by
  simp only [Int.blt_eq_true, Int.bgt_eq_true] at *
  have h := Int.mul_lt_mul_of_pos_right ha hb
  simp at h
  exact h

theorem mul_sign₄ (ha : a.bgt 0 = true) (hb : b.blt 0 = true) : (a * b).blt 0 = true := by
  simp only [Int.blt_eq_true, Int.bgt_eq_true] at *
  have h := Int.mul_lt_mul_of_pos_left hb ha
  simp at h
  exact h

theorem mul_sign₆ (ha : a.bgt 0 = true) (hb : b.bgt 0 = true) : (a * b).bgt 0 = true := by
  simp only [Int.bgt_eq_true] at *
  have h := Int.mul_lt_mul_of_pos_left hb ha
  simp at h
  exact h

theorem mul_sign₀ (ha : (!(a == 0)) = true) : (a * a).bgt 0 = true := by
  simp only [Bool.not_eq_true', beq_eq_false_iff_ne] at ha
  match Int.lt_trichotomy a 0 with
  | .inl hn         => exact mul_sign₁ (by simpa using hn) (by simpa using hn)
  | .inr (.inl hz)  => exact absurd hz ha
  | .inr (.inr hp)  => exact mul_sign₆ (by simpa using hp) (by simpa using hp)

theorem mul_sign₂ (ha : a.blt 0 = true) (hb : (!(b == 0)) = true) : (a * b * b).blt 0 = true := by
  simp only [Bool.not_eq_true', beq_eq_false_iff_ne] at hb
  match Int.lt_trichotomy b 0 with
  | .inl hn         => exact mul_sign₄ (mul_sign₁ ha (by simpa using hn)) (by simpa using hn)
  | .inr (.inl hz)  => exact absurd hz hb
  | .inr (.inr hp)  => exact mul_sign₃ (mul_sign₃ ha (by simpa using hp)) (by simpa using hp)

theorem mul_sign₅ (ha : a.bgt 0 = true) (hb : (!(b == 0)) = true) : (a * b * b).bgt 0 = true := by
  simp only [Bool.not_eq_true', beq_eq_false_iff_ne] at hb
  match Int.lt_trichotomy b 0 with
  | .inl hn         => exact mul_sign₁ (mul_sign₄ ha (by simpa using hn)) (by simpa using hn)
  | .inr (.inl hz)  => exact absurd hz hb
  | .inr (.inr hp)  => exact mul_sign₆ (mul_sign₆ ha (by simpa using hp)) (by simpa using hp)

theorem mul_pos_lt : ((c.bgt 0 && a.blt b).imp ((c * a).blt (c * b))) = true := by
  simp only [Bool.imp_eq_true, Bool.and_eq_true, Int.bgt_eq_true, Int.blt_eq_true]
  exact fun h => Int.mul_lt_mul_of_pos_left h.2 h.1

theorem mul_pos_le : ((c.bgt 0 && a.ble b).imp ((c * a).ble (c * b))) = true := by
  simp only [Bool.imp_eq_true, Bool.and_eq_true, Int.bgt_eq_true, Int.ble_eq_true]
  exact fun h => Int.mul_le_mul_of_nonneg_left h.2 (Int.le_of_lt h.1)

theorem mul_pos_gt : ((c.bgt 0 && a.bgt b).imp ((c * a).bgt (c * b))) = true := by
  simp only [Bool.imp_eq_true, Bool.and_eq_true, Int.bgt_eq_true]
  exact fun h => Int.mul_lt_mul_of_pos_left h.2 h.1

theorem mul_pos_ge : ((c.bgt 0 && a.bge b).imp ((c * a).bge (c * b))) = true := by
  simp only [Bool.imp_eq_true, Bool.and_eq_true, Int.bgt_eq_true, Int.bge_eq_true]
  exact fun h => Int.mul_le_mul_of_nonneg_left h.2 (Int.le_of_lt h.1)

theorem mul_pos_eq : ((c.bgt 0 && a == b).imp (c * a == c * b)) = true := by
  simp only [Bool.imp_eq_true, Bool.and_eq_true, Int.bgt_eq_true, beq_iff_eq]
  exact fun h => by rw [h.2]

theorem mul_neg_lt : ((c.blt 0 && a.blt b).imp ((c * a).bgt (c * b))) = true := by
  simp only [Bool.imp_eq_true, Bool.and_eq_true, Int.blt_eq_true, Int.bgt_eq_true]
  exact fun h => Int.mul_lt_mul_of_neg_left h.2 h.1

theorem mul_neg_le : ((c.blt 0 && a.ble b).imp ((c * a).bge (c * b))) = true := by
  simp only [Bool.imp_eq_true, Bool.and_eq_true, Int.blt_eq_true, Int.ble_eq_true, Int.bge_eq_true]
  exact fun h => Int.mul_le_mul_of_nonpos_left (Int.le_of_lt h.1) h.2

theorem mul_neg_gt : ((c.blt 0 && a.bgt b).imp ((c * a).blt (c * b))) = true := by
  simp only [Bool.imp_eq_true, Bool.and_eq_true, Int.blt_eq_true, Int.bgt_eq_true]
  exact fun h => Int.mul_lt_mul_of_neg_left h.2 h.1

theorem mul_neg_ge : ((c.blt 0 && a.bge b).imp ((c * a).ble (c * b))) = true := by
  simp only [Bool.imp_eq_true, Bool.and_eq_true, Int.blt_eq_true, Int.bge_eq_true, Int.ble_eq_true]
  exact fun h => Int.mul_le_mul_of_nonpos_left (Int.le_of_lt h.1) h.2

theorem mul_neg_eq : ((c.blt 0 && a == b).imp (c * a == c * b)) = true := by
  simp only [Bool.imp_eq_true, Bool.and_eq_true, Int.blt_eq_true, beq_iff_eq]
  exact fun h => by rw [h.2]

end Smt.Reconstruct.Int
