/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomaz Mascarenhas
-/

/-
Implementation of:
https://cvc5.github.io/docs/cvc5-1.0.2/proofs/proof_rules.html#_CPPv4N4cvc58internal6PfRule29ARITH_TRANS_SINE_TANGENT_ZEROE
-/

module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.Complex.Exponential
public import Smt.Reconstruct.Bool.Core
public import Smt.Reconstruct.Real.Core

@[expose] public section

open Real

namespace Smt.Reconstruct.Real.TransFns

theorem sin_neg' : ∀ (t : ℝ), sin t = - sin (-t) := by
  intro t
  rw [sin_neg t]
  simp

theorem arithTransSinTangentZero : ∀ (t : ℝ),
    ((t.bgt 0).imp ((sin t).blt t) && (t.blt 0).imp ((sin t).bgt t)) = true := by
  intro t
  simp only [Bool.and_eq_true, Bool.imp_eq_true, Real.bgt_eq_true, Real.blt_eq_true]
  apply And.intro
  · exact sin_lt
  · intro ht
    rw [sin_neg']
    apply lt_neg.mpr
    apply sin_lt
    linarith

end Smt.Reconstruct.Real.TransFns
