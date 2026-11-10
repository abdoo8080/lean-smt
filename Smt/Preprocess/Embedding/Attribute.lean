/-
Copyright (c) 2021-2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

module

public import Lean.Meta.Tactic.Simp.RegisterCommand
public meta import Lean.Meta.Tactic.Simp.RegisterCommand

public meta section

/-- Theorems that embed types that SMT-LIB lacks (e.g., `Nat` and `Prop`) into ones it has (e.g., `Int`
and `Bool`). -/
register_simp_attr embedding

/-- Theorems that push `smtDecide p` into the proposition `p`, which turns hypotheses into Boolean
formulas (see `Smt.Preprocess.Embedding.Prop`). -/
register_simp_attr smt_decide
