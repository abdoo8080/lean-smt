/-
Copyright (c) 2021-2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

module

public import Smt.Preprocess.Normalize.Attribute

@[expose] public section

/-! The unsigned comparisons of bit-vectors decide `<` and `≤`, which are SMT-LIB's `bvult` and
`bvule`. -/

attribute [smt_normalize ↓] BitVec.ult_eq_decide_lt BitVec.ule_eq_decide_le
