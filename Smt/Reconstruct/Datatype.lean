/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harun Khan
-/

module

public import Smt.Reconstruct
public meta import Smt.Reconstruct

public meta section

namespace Smt.Reconstruct.Datatype

open Lean Meta Qq

/-- Names of types that already have dedicated sort/term/proof reconstructors
and should not be handled by the generic datatype reconstructor. -/
private def builtinTypeNames : Std.HashSet Name :=
  Std.HashSet.ofList [
    ``Bool, `Prop, ``True, ``False,
    ``Or, ``And, ``Iff, ``Exists,
    ``Nat, ``Int, `Rat, `Real,
    ``String, ``BitVec
  ]

/-- Return `true` when the name (or its prefix for a constructor) belongs to a
type with dedicated built-in reconstruction support. -/
private def isBuiltinName (n : Name) : Bool :=
  builtinTypeNames.contains n ||
  -- Also catch constructor names like `Bool.true`, `Nat.zero`, etc.
  match n with
  | .str p _ => builtinTypeNames.contains p
  | _ => false

-- Strip SMT-LIB2 pipe quoting (|name|) from a symbol if present.
private def stripSMTPipes (s : String) : String :=
  if s.startsWith "|" && s.endsWith "|" then (s.drop 1 |>.dropEnd 1).toString else s

private def getFVarOrConstExpr! (n : String) : ReconstructM Expr := do
  match (← read).userNames[n]? with
  | some e => return e
  | none   => match (← getLCtx).findFromUserName? n.toName with
    | some d => return d.toExpr
    | none   =>
      let c ← getConstInfo n.toName
      return .const c.name (c.numLevelParams.repeat (.zero :: ·) [])

@[smt_sort_reconstruct] def reconstructDatatypeSort : SortReconstructor := fun s => do
  match s.getKind! with
  | .DATATYPE_SORT =>
    let name := s.getDatatype!.getName!
    if isBuiltinName name.toName then return none
    getFVarOrConstExpr! name
  | _ => return none

@[smt_term_reconstruct] def reconstructDatatypeTerm : TermReconstructor := fun t => do
  match t.getKind! with
  | .APPLY_CONSTRUCTOR =>
    -- t[0]! is the constructor symbol. It has INTERNAL_KIND in cvc5 (even for non-zero-arity),
    -- so we look it up by name instead of calling reconstructTerm recursively.
    -- toString may include SMT-LIB pipe escaping (e.g., "|mynat'.succ|"), so strip it.
    let ctorName := stripSMTPipes t[0]!.toString
    if isBuiltinName ctorName.toName then return none
    let mut curr ← getFVarOrConstExpr! ctorName
    for i in [1:t.getNumChildren] do
      curr := .app curr (← reconstructTerm t[i]!)
    return curr
  | _ => return none

/-- A proof of `(t == s) = F` for applications `t` and `s` of constructors, where `F` is the
conjunction of the equalities of their fields, by the injectivity of the constructors. Returns `none`
if that fails. -/
private def proveConsEq (l r : Expr) : MetaM (Option Expr) := do
  let mut thms : SimpTheorems := {}
  for n in [``beq_iff_eq, ``decide_eq_true_eq, ``Bool.and_eq_true] do
    thms ← thms.addConst n
  let env ← getEnv
  for c in l.getUsedConstants do
    if isCtor env c && env.contains (c ++ `injEq) then
      thms ← thms.addConst (c ++ `injEq)
  let ctx ← Simp.mkContext {} #[thms]
  -- `(l = true) ↔ (r = true)`
  let h ← mkFreshExprMVar (mkApp2 (.const ``Iff []) (← mkEq l (.const ``true [])) (← mkEq r (.const ``true [])))
  try
    if let (some mv, _) ← simpTarget h.mvarId! ctx then
      _ ← mv.apply (.const ``Iff.rfl [])
    return some (← mkAppM ``Iff.mpr #[← mkAppOptM ``Bool.eq_iff_iff #[l, r], ← instantiateMVars h])
  catch _ =>
    return none
where
  isCtor (env : Environment) (c : Name) : Bool :=
    match env.find? c with
    | some (.ctorInfo _) => true
    | _ => false

/-- Build a Lean proof of `¬(t = s)` where `t` and `s` are distinct constructors.
Uses the `noConfusion` principle: `fun h : t = s => noConfusion False t s h`. -/
private def proveDistinctValues (t s : Expr) : MetaM Expr := do
  let α ← inferType t
  let .const αName _ := α.getAppFn
    | throwError "Smt.Reconstruct.Datatype: expected inductive type, got {α}"
  let ncName := αName ++ `noConfusion
  let heq ← mkEq t s
  withLocalDeclD `h heq fun h => do
    let nc ← mkAppOptM ncName #[some (mkConst ``False), some t, some s, some h]
    mkLambdaFVars #[h] nc

def reconstructRewrite (pf : cvc5.Proof) : ReconstructM (Option Expr) := do
  match pf.getRewriteRule! with
  | .MACRO_DT_CONS_EQ
  | .DT_CONS_EQ
  | .DT_CONS_EQ_CLASH =>
    let result := pf.getResult
    let sort := result[0]![0]!.getSort!
    if sort.getKind! == .DATATYPE_SORT && isBuiltinName sort.getDatatype!.getName!.toName then
      return none
    if result[1]!.getKind! == .CONST_BOOLEAN && !result[1]!.getBooleanValue! then
      -- Distinct constructors: `(t == s) = false`.
      let (_, t, s, inst) ← getEq! (← reconstructTerm result[0]!)
      addEqThm pf.getResult (mkApp3 (.const ``decide_eq_false []) (← mkEq t s) inst (← proveDistinctValues t s))
    else
      -- `(= (= (C t₁ … tₙ) (C s₁ … sₙ)) (and (= t₁ s₁) … (= tₙ sₙ)))`
      let (_, l, r, _) ← getEq! (← reconstructTerm result)
      let some h ← proveConsEq l r | return none
      addEqThm result h
  | _ => return none

@[smt_proof_reconstruct] def reconstructDatatypeProof : ProofReconstructor := fun pf => do
  match pf.getRule with
  | .DSL_REWRITE
  | .THEORY_REWRITE => reconstructRewrite pf
  | .DISTINCT_VALUES =>
    let sort := pf.getArguments[0]!.getSort!
    if sort.getKind! == .DATATYPE_SORT && isBuiltinName sort.getDatatype!.getName!.toName then
      return none
    -- `(not (= t s))` is reconstructed as `!(t == s)`.
    let (_, t, s, inst) ← getEq! (← reconstructTerm pf.getResult[0]!)
    let p ← mkEq t s
    let h := mkApp3 (.const ``decide_eq_false []) p inst (← proveDistinctValues t s)
    -- `(!decide (t = s)) = !false`
    let b := .const ``Bool []
    addThm (← reconstructProofType pf.getResult)
      (mkAppN (.const ``congrArg [1, 1]) #[b, b, mkApp2 (.const ``decide []) p inst, .const ``Bool.false [], .const ``not [], h])
  | _ => return none

end Smt.Reconstruct.Datatype
