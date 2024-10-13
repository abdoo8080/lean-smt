/-
Copyright (c) 2021-2024 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

import Mathlib.Algebra.Group.Defs

import Auto.Tactic
import Smt

open Lean in
def smtSolverFunc (ls : Array Auto.Lemma) : MetaM Expr := do
  let f l := do
    let userName ← mkFreshUserName `h
    let type ← Auto.Lam2D.approxSimpNF l.type
    let value := l.proof
    return { userName, type, value }
  let hs ← ls.mapM f
  let h ← Meta.mkFreshExprMVar (Expr.const ``False [])
  let (fvs, mv) ← h.mvarId!.assertHypotheses hs
  mv.withContext do
    let hs := fvs.map (.fvar ·)
    _ ← Smt.smt mv hs.toList
    -- Note: auto should allow solvers to export new goals to users
    -- for mv in mvs do
    --   logInfo m!"new : {mv}"
    instantiateMVars h

set_option auto.native true
attribute [rebind Auto.Native.solverFunc] smtSolverFunc

example {α : Type} (x : α) : List.head? [x] = .some x := by
  have h₂ : ∀ (x : α) (ys : _), List.head? (x :: ys) = .some x := fun _ _ => rfl
  auto

example {α : Type} (x y : α) : [x] ++ [y] = [x, y] := by
  -- Invoke definition unfolding
  have h : ∀ (x y : List α), x ++ y = x.append y := fun _ _ => rfl
  auto [h] d[List.append]

variable {G : Type} [Group G]

theorem inverse' : ∀ (a : G), a * a⁻¹ = 1 := by
  auto [mul_assoc, one_mul, inv_mul_cancel]

theorem identity' : ∀ (a : G), a * 1 = a := by
  auto [mul_assoc, one_mul, inv_mul_cancel, inverse']

theorem unique_identity (e : G) : (∀ z, e * z = z) → e = 1 := by
  auto [mul_assoc, one_mul, inv_mul_cancel]

-- TODO: pre-process Nat away
-- example {α : Type} (x y : α) : List.get? [x, y] 1 = .some y := by
  -- auto d[List.get?]
