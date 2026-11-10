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
# Lemmas for cvc5's normalization of bit-vector polynomials

`BV_POLY_NORM_EQ` proves `(x₁ = x₂) = (y₁ = y₂)` from `cx * (x₁ - x₂) = cy * (y₁ - y₂)`, where the
scaling factors `cx` and `cy` are odd, and hence invertible modulo `2 ^ w`.
-/

namespace BitVec

theorem odd_mul_eq_zero {c z : BitVec w} (hc : c.getLsbD 0 = true) : (c * z = 0#w) = (z = 0#w) := by
  apply propext
  constructor
  · intro h
    have h' := congrArg BitVec.toNat h
    simp only [toNat_mul, toNat_ofNat, Nat.zero_mod] at h'
    have hodd : c.toNat % 2 = 1 := by
      simpa [getLsbD, Nat.testBit_zero] using hc
    have hcop : Nat.Coprime (2 ^ w) c.toNat := by
      apply Nat.Coprime.pow_left
      rw [Nat.Coprime, Nat.gcd_rec, hodd]
      rfl
    have hz := hcop.dvd_of_dvd_mul_left (Nat.dvd_of_mod_eq_zero h')
    apply eq_of_toNat_eq
    simp only [toNat_ofNat, Nat.zero_mod]
    exact Nat.eq_zero_of_dvd_of_lt hz z.isLt
  · intro h
    rw [h, BitVec.mul_zero]

theorem sub_eq_zero_iff {x y : BitVec w} : (x - y = 0#w) = (x = y) := by
  apply propext
  constructor
  · intro h
    rw [← BitVec.sub_add_cancel (x := x) (y := y), h, BitVec.zero_add]
  · intro h
    rw [h, BitVec.sub_self]

theorem poly_norm_eq {x₁ x₂ y₁ y₂ cx cy : BitVec w} (hx : cx.getLsbD 0 = true)
    (hy : cy.getLsbD 0 = true) (h : cx * (x₁ - x₂) = cy * (y₁ - y₂)) : (x₁ = x₂) = (y₁ = y₂) := by
  have e₁ : (x₁ = x₂) = (cx * (x₁ - x₂) = 0#w) := by
    rw [odd_mul_eq_zero hx, sub_eq_zero_iff]
  have e₂ : (y₁ = y₂) = (cy * (y₁ - y₂) = 0#w) := by
    rw [odd_mul_eq_zero hy, sub_eq_zero_iff]
  rw [e₁, e₂, h]

end BitVec
