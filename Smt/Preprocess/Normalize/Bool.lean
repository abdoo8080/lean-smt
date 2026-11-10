/-
Copyright (c) 2021-2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

module

public import Smt.Preprocess.Normalize.Attribute

@[expose] public section

/-! Boolean tests of equality decide propositions, which the embedding turns into SMT-LIB's `=`. -/

namespace Smt.Preprocess.Normalize

@[smt_normalize ↓]
theorem beq_eq_decide [BEq α] [LawfulBEq α] {x y : α} :
    (x == y) = @decide (x = y) (Classical.propDecidable _) := by
  apply Bool.eq_iff_iff.mpr; simp

@[smt_normalize ↓]
theorem bne_eq_not_decide [BEq α] [LawfulBEq α] {x y : α} :
    (x != y) = !@decide (x = y) (Classical.propDecidable _) := by
  apply Bool.eq_iff_iff.mpr; simp

end Smt.Preprocess.Normalize
