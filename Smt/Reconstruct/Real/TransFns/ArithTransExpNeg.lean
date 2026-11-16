/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomaz Mascarenhas
-/

/-
Implementation of:
https://cvc5.github.io/docs/cvc5-1.0.2/proofs/proof_rules.html#_CPPv4N4cvc58internal6PfRule19ARITH_TRANS_EXP_NEGE
-/

module

public import Mathlib.Analysis.Complex.Exponential
public import Smt.Reconstruct.Bool.Core
public import Smt.Reconstruct.Real.Core

@[expose] public section

namespace Smt.Reconstruct.Real.TransFns

theorem arithTransExpNeg (t : ℝ) : t < 0 ↔ Real.exp t < 1 :=
  Iff.comm.mp Real.exp_lt_one_iff

theorem arithTransExpNeg' (t : ℝ) : Bool.eq (t.blt 0) ((Real.exp t).blt 1) :=
  Bool.eq.of_eq (decide_eq_decide.mpr (arithTransExpNeg t))

end Smt.Reconstruct.Real.TransFns
