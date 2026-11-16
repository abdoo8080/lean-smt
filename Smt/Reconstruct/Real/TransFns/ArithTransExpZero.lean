/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomaz Mascarenhas
-/

/-
Implementation of:
https://cvc5.github.io/docs/cvc5-1.0.2/proofs/proof_rules.html#_CPPv4N4cvc58internal6PfRule20ARITH_TRANS_EXP_ZEROE
-/

module

public import Mathlib.Analysis.Complex.Exponential
public import Smt.Reconstruct.Bool.Core
public import Smt.Reconstruct.Real.Core

@[expose] public section

namespace Smt.Reconstruct.Real.TransFns

theorem arithTransExpZero (t : ℝ) :
    t = 0 ↔ Real.exp t = 1 := by
  apply Iff.intro
  · intro h; rw [h]; simp
  · intro h; simp at h; assumption

theorem arithTransExpZeroEq (t : ℝ) :
    Bool.eq (decide (t = 0)) (decide (Real.exp t = 1)) := by
  apply Bool.eq.of_eq
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  exact arithTransExpZero t

end Smt.Reconstruct.Real.TransFns
