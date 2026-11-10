/-
Copyright (c) 2021-2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

module

public import Smt.Preprocess.Embedding.Attribute
public meta import Smt.Preprocess.Embedding.Attribute
public import Smt.Reconstruct.Rat.Core

@[expose] public section

/-! Comparisons of rationals, which represent SMT-LIB's reals with `Smt.Rat`, are decided with the
Boolean comparisons that reconstruct SMT-LIB's comparisons on reals (see
`Smt.Preprocess.Embedding.Prop`). -/

namespace Smt.Preprocess.Embedding

variable {x y : Rat}

@[smt_decide ↓] theorem decide_rat_lt {h : Decidable (x < y)} : @decide (x < y) h = x.blt y := by
  apply Bool.eq_iff_iff.mpr; rw [decide_eq_true_eq, Rat.blt_eq_true]
@[smt_decide ↓] theorem decide_rat_le {h : Decidable (x ≤ y)} : @decide (x ≤ y) h = x.ble y :=
  decide_eq_decide.mpr Iff.rfl
@[smt_decide ↓] theorem decide_rat_gt {h : Decidable (x > y)} : @decide (x > y) h = x.bgt y :=
  decide_eq_decide.mpr Iff.rfl
@[smt_decide ↓] theorem decide_rat_ge {h : Decidable (x ≥ y)} : @decide (x ≥ y) h = x.bge y :=
  decide_eq_decide.mpr Iff.rfl

end Smt.Preprocess.Embedding
