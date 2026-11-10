/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomaz Mascarenhas
-/

/-
Implementation of:
https://cvc5.github.io/docs/cvc5-1.0.2/proofs/proof_rules.html#_CPPv4N4cvc58internal6PfRule23ARITH_TRANS_SINE_BOUNDSE
-/

module

public import Mathlib.Analysis.Complex.Trigonometric
public import Smt.Reconstruct.Bool.Core
public import Smt.Reconstruct.Real.Core

@[expose] public section

open Real

namespace Smt.Reconstruct.Real.TransFns

theorem arithTransSineBounds : ∀ (t : ℝ), ((sin t).ble 1 && (sin t).bge (-1)) = true := by
  intro t
  simp only [Bool.and_eq_true, Real.ble_eq_true, Real.bge_eq_true]
  apply And.intro
  · exact sin_le_one t
  · exact neg_one_le_sin t

end Smt.Reconstruct.Real.TransFns
