/-
Copyright (c) 2021-2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed, George Pîrlea
-/

module

public import Smt.Preprocess.Embedding.Attribute
public meta import Smt.Preprocess.Embedding.Attribute

-- Note: not `@[expose]`d; nothing here needs to unfold downstream, and exposing the `simproc`s
-- below would forbid them from using the `private` helpers in this module.
public section

/-! When the embedding rewrites the condition of an `ite`, use the condition's own `Decidable`
instance (if it has one) instead of casting the old instance. -/

namespace Smt.Preprocess.Embedding

theorem ite_congr' {α} [Decidable c₁] [Decidable c₂] {x₁ x₂ y₁ y₂ : α} (h₁ : c₁ = c₂) (h₂ : x₁ = x₂) (h₃ : y₁ = y₂) : ite c₁ x₁ y₁ = ite c₂ x₂ y₂ := by
  congr

public meta section

open Lean in
@[match_pattern] private def mkApp12 (f a b c d e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ : Expr) := mkApp8 (mkApp4 f a b c d) e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈

open Lean Meta Simp in
simproc ↓ [embedding] IteCongrSimproc (ite _ _ _) := fun e => do
  let mkApp5 (.const ``ite [u]) α c hc t e := e | return .continue
  let cr ← simp c
  let ct ← simp t
  let ce ← simp e
  if cr.expr == c && ct.expr == t && ce.expr == e then return .continue
  let chc' := .app (.const ``Classical.propDecidable []) cr.expr
  let hc' ← if cr.expr == c then pure hc
            else Meta.synthInstance? (.app (.const ``Decidable []) cr.expr) >>= pure ∘ (Option.getD · chc')
  let expr := mkApp5 (.const ``ite [u]) α cr.expr hc' ct.expr ce.expr
  let proof := mkApp12 (.const ``ite_congr' [u]) c cr.expr α hc hc' t ct.expr e ce.expr (← cr.getProof) (← ct.getProof) (← ce.getProof)
  return .done { expr, proof? := some proof }

end

end Smt.Preprocess.Embedding
