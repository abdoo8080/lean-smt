/-
Copyright (c) 2021-2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

module

public import Smt.Preprocess.Embedding.Attribute
public meta import Smt.Preprocess.Embedding.Attribute
public import Smt.Reconstruct.Real.Core

@[expose] public section

/-! Comparisons of reals are decided with the Boolean comparisons that reconstruct SMT-LIB's
comparisons on reals (see `Smt.Preprocess.Embedding.Prop`). -/

namespace Smt.Preprocess.Embedding

variable {x y : Real}

@[smt_decide ↓] theorem decide_real_lt {h : Decidable (x < y)} : @decide (x < y) h = x.blt y :=
  decide_eq_decide.mpr Iff.rfl
@[smt_decide ↓] theorem decide_real_le {h : Decidable (x ≤ y)} : @decide (x ≤ y) h = x.ble y :=
  decide_eq_decide.mpr Iff.rfl
@[smt_decide ↓] theorem decide_real_gt {h : Decidable (x > y)} : @decide (x > y) h = x.bgt y :=
  decide_eq_decide.mpr Iff.rfl
@[smt_decide ↓] theorem decide_real_ge {h : Decidable (x ≥ y)} : @decide (x ≥ y) h = x.bge y :=
  decide_eq_decide.mpr Iff.rfl

end Smt.Preprocess.Embedding
