/-
Copyright (c) 2021-2022 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed, Wojciech Nawrocki
-/

module

public import Smt.Recognizers
public meta import Smt.Recognizers
public import Smt.Translate
public meta import Smt.Translate

public meta section

/-!
# Translation of Booleans

Lean's `Bool` is SMT-LIB's `Bool`. Propositions are embedded into Booleans: a hypothesis `p` is
turned into `b = true`, where `b` is a Boolean formula such as `x.blt y && decide (x = y)` (see
`Smt.Preprocess.Embedding.Prop` and `Smt.Reconstruct.Bool.Core`). So `b = true` is translated as `b`,
and `decide p` as `p`.
-/

namespace Smt.Translate.Bool

open Lean Translator Term

@[smt_translate] def translateType : Translator := fun e => match e with
  | .const ``Bool _ => return symbolT "Bool"
  | _               => return none

@[smt_translate] def translateBool : Translator := fun e => do
  if let .const ``true _ := e then
    return symbolT "true"
  else if let .const ``false _ := e then
    return symbolT "false"
  else if let .some b := e.app1? ``not then
    return appT (symbolT "not") (← applyTranslators! b)
  else if let some (a, b) := e.app2? ``and then
    return mkApp2 (symbolT "and") (← applyTranslators! a) (← applyTranslators! b)
  else if let some (a, b) := e.app2? ``or then
    return mkApp2 (symbolT "or") (← applyTranslators! a) (← applyTranslators! b)
  else if let some (a, b) := e.app2? ``xor then
    return mkApp2 (symbolT "xor") (← applyTranslators! a) (← applyTranslators! b)
  else if let some (a, b) := e.app2? `Bool.imp then
    return mkApp2 (symbolT "=>") (← applyTranslators! a) (← applyTranslators! b)
  else if let some (p, _) := e.app2? ``Decidable.decide then
    return some (← applyTranslators! p)
  else if e.isAppOfArity `Bool.forall 2 || e.isAppOfArity `Bool.exists 2 then
    -- `Bool.forall fun x => b` is `∀ x, b = true`, and `Bool.exists` likewise.
    let α := e.getArg! 0
    let (n, bi) := match e.getArg! 1 with
      | .lam n _ _ bi => (n, bi)
      | _ => (`x, .default)
    let p ← Meta.withLocalDecl n bi α fun x => do
      let b := (e.getArg! 1).beta #[x]
      let b ← Meta.mkEq b (.const ``Bool.true [])
      if e.isAppOfArity `Bool.forall 2 then Meta.mkForallFVars #[x] b
      else Meta.mkAppM ``Exists #[← Meta.mkLambdaFVars #[x] b]
    return some (← applyTranslators! p)
  else if e.isAppOfArity ``cond 4 then
    return mkApp3 (symbolT "ite") (← applyTranslators! (e.getArg! 1)) (← applyTranslators! (e.getArg! 2))
                  (← applyTranslators! (e.getArg! 3))
  else if let some (_, x, y) := e.beq? then
    return mkApp2 (symbolT "=") (← applyTranslators! x) (← applyTranslators! y)
  else if let some (_, x, y) := e.bne? then
    return mkApp2 (symbolT "distinct") (← applyTranslators! x) (← applyTranslators! y)
  else
    return none

@[smt_translate] def translateProp : Translator := fun e => do
  if let some (.const ``Bool _, a, b) := e.eq? then
    -- `b = true` is the proposition that the Boolean formula `b` holds.
    if b.isConstOf ``true then
      return some (← applyTranslators! a)
    if b.isConstOf ``false then
      return appT (symbolT "not") (← applyTranslators! a)
    return mkApp2 (symbolT "=") (← applyTranslators! a) (← applyTranslators! b)
  else
    return none

end Smt.Translate.Bool
