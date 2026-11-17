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

namespace Smt.Translate.Nat

open Lean Expr
open Translator Term

private def mkNat : Lean.Expr :=
  .const ``Nat []

/-- `Nat` is the SMT-LIB datatype
`(declare-datatypes ((Nat 0)) (((Nat.zero) (Nat.succ (Nat.succ.n Nat)))))`
that the query builder declares for the `Nat` inductive type. The `embedding` step rewrites `Nat`
operations into `Int` ones through the uninterpreted casts `Nat.toInt` and `Nat.fromInt` (see
`Smt/Preprocess/Embedding/Nat.lean`), so only literals and constructors can reach this translator,
e.g., when the `embedding` step is disabled. -/
@[smt_translate] def translateNat : Translator := fun e => do
  if let some n := e.natLitOf? mkNat then
    modify fun st => { st with depConstants := st.depConstants.insert `Nat.fromInt }
    return appT (symbolT "Nat.fromInt") (literalT (toString n))
  else if let .const ``Nat.zero _ := e then
    modify fun st => { st with depConstants := st.depConstants.insert ``Nat }
    return symbolT "Nat.zero"
  else if let some n := e.app1? ``Nat.succ then
    modify fun st => { st with depConstants := st.depConstants.insert ``Nat }
    return appT (symbolT "Nat.succ") (← applyTranslators! n)
  else
    return none

end Smt.Translate.Nat
