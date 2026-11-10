/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomaz Mascarenhas
-/

/-
Implementation of:
https://cvc5.github.io/docs/cvc5-1.0.2/proofs/proof_rules.html#_CPPv4N4cvc58internal6PfRule27ARITH_TRANS_SINE_TANGENT_PIE
-/

module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.Complex.Exponential
public import Smt.Reconstruct.Bool.Core
public import Smt.Reconstruct.Real.Core

@[expose] public section

open Real

namespace Smt.Reconstruct.Real.TransFns

theorem arithTransSineTangentPi₁ : ∀ (t : ℝ),
    t > - Real.pi → sin t > - Real.pi - t := by
  intros t ht
  set ε := Real.pi + t
  have e_pos : 0 < ε := neg_lt_iff_pos_add'.mp ht
  have te : t = -Real.pi + ε := eq_neg_add_of_add_eq rfl
  rw [te]
  have : sin (-Real.pi + ε) = - Real.sin ε :=
    by rw [add_comm, <- sub_eq_add_neg]; exact sin_sub_pi ε
  rw [this]
  simp only [sub_add_cancel_left, gt_iff_lt, neg_lt_neg_iff]
  exact sin_lt e_pos

theorem arithTransSineTangentPi₂ : ∀ (t : ℝ),
    t < Real.pi → sin t < Real.pi - t := by
  intros t ht
  set ε := Real.pi - t
  have e_pos : 0 < ε := sub_pos.mpr ht
  have te : t = Real.pi - ε := Eq.symm (sub_sub_self π t)
  rw [te]
  have : sin (Real.pi - ε) = sin ε := sin_pi_sub ε
  rw [this]
  exact sin_lt e_pos

theorem arithTransSineTangentPi : ∀ (t : ℝ),
    ((t.bgt ((-1) * Real.pi)).imp ((sin t).bgt ((-1) * Real.pi - t)) &&
      (t.blt Real.pi).imp ((sin t).blt (Real.pi - t))) = true := fun t =>
  by simp only [Bool.and_eq_true, Bool.imp_eq_true, Real.bgt_eq_true, Real.blt_eq_true]
     simp only [neg_mul, one_mul, gt_iff_lt]
     exact ⟨arithTransSineTangentPi₁ t, arithTransSineTangentPi₂ t⟩

end Smt.Reconstruct.Real.TransFns
