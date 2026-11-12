/-
Copyright (c) 2021-2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

module

public import Lean.Meta.AppBuilder
public meta import Lean.Meta.AppBuilder
public import Smt.Reconstruct.Bool.Core
public meta import Smt.Reconstruct.Bool.Core

public meta section

namespace Smt.Reconstruct.Bool

open Lean

/-- The instance of `Decidable p` that Boolean formulas decide `p` with: the default one, i.e., a
synthesized one, or a classical one if there is none. -/
def decideInst (p : Expr) : MetaM Expr := do
  match ← Meta.synthInstance? (mkApp (.const ``Decidable []) p) with
  | some inst => return inst
  | none => return mkApp (.const ``Classical.propDecidable []) p

/-- The Boolean atom `decide p` of the proposition `p`, with the instance `decideInst p`. -/
def decideOf (p : Expr) : MetaM Expr := do
  return mkApp2 (.const ``Decidable.decide []) p (← decideInst p)

/-- The instance of `DecidableEq α` that Boolean formulas decide `a = b` with for `a b : α`: the exact
one for SMT-LIB's builtin sorts, and otherwise a synthesized one, or a classical one. -/
def decEqInst (α : Expr) : MetaM Expr := do
  if α.isConstOf ``Bool then return .const ``instDecidableEqBool []
  if α.isConstOf ``Int then return .const ``Int.instDecidableEq []
  if α.isConstOf ``String then return .const ``instDecidableEqString []
  if α.isConstOf `Real then return .const `Real.decidableEq []
  if let some w := α.app1? ``BitVec then return mkApp (.const ``instDecidableEqBitVec []) w
  let u ← Meta.getLevel α
  if let some inst ← Meta.synthInstance? (mkApp (.const ``DecidableEq [u]) α) then return inst
  return mkApp (.const ``Classical.typeDecidableEq [u]) α

/-- The instance `decEqInst α a b` of `Decidable (a = b)` with which Boolean formulas decide
`a = b`. -/
def eqInst (α a b : Expr) : MetaM Expr := do
  return mkApp2 (← decEqInst α) a b

/-- The Boolean formula `decide (a = b)` of `a = b` for `a b : α`, with the instance `decEqInst α a b`. -/
def mkDecideEq (α a b : Expr) : MetaM Expr := do
  return mkApp2 (.const ``Decidable.decide []) (← Meta.mkEq a b) (← eqInst α a b)

/-- The type `α`, the sides `a` and `b`, and the instance of `Decidable (a = b)` of the Boolean
formula `decide (a = b)` of an equality (see `mkDecideEq`). -/
def getEq? (e : Expr) : Option (Expr × Expr × Expr × Expr) := Id.run do
  if let some (p, inst) := e.app2? ``Decidable.decide then
    if let some (α, a, b) := p.eq? then
      return some (α, a, b, inst)
  return none

end Smt.Reconstruct.Bool
