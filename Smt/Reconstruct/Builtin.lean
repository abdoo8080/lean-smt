/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

module

public import Lean.Meta.Native
public meta import Lean.Meta.Native
public import Smt.Reconstruct
public meta import Smt.Reconstruct
public import Smt.Reconstruct.Bool.Lemmas
public meta import Smt.Reconstruct.Bool.Lemmas
public import Smt.Reconstruct.Bool.Rewrites
public meta import Smt.Reconstruct.Bool.Rewrites
public import Smt.Reconstruct.Builtin.AC
public meta import Smt.Reconstruct.Builtin.AC
public import Smt.Reconstruct.Builtin.Lemmas
public meta import Smt.Reconstruct.Builtin.Lemmas
public import Smt.Reconstruct.Builtin.Tactic
public meta import Smt.Reconstruct.Builtin.Tactic

public meta section

namespace Smt.Reconstruct.Builtin

open Lean Qq

@[smt_sort_reconstruct] def reconstructBuiltinSort : SortReconstructor := fun s => do match s.getKind! with
  | .FUNCTION_SORT =>
    let ct ← reconstructSort s.getFunctionCodomainSort!
    let f := fun s a => do
      let t ← reconstructSort s
      return .forallE .anonymous t a .default
    let t ← s.getFunctionDomainSorts!.foldrM f ct
    return t
  | _              => return none

def getFVarExpr! (n : Name) : MetaM Expr := do
  match (← getLCtx).findFromUserName? n with
  | some d => return d.toExpr
  | none   => throwError "unknown free variable '{n}'"

def getFVarOrConstExpr! (n : String) : ReconstructM Expr := do
  match (← read).userNames[n]? with
  | some e => return e
  | none   => match (← getLCtx).findFromUserName? n.toName with
    | some d => return d.toExpr
    | none   =>
      let c ← getConstInfo n.toName
      return .const c.name (c.numLevelParams.repeat (.zero :: ·) [])

/-- The Boolean `decide p` of a proposition `p : Prop`, and `e` itself otherwise. A Lean constant
or free variable `p : Prop` (e.g., a propositional variable of the goal) is an SMT-LIB constant of
sort `Bool`. -/
def toBoolIfProp (e : Expr) : MetaM Expr := do
  if (← Meta.inferType e).isProp then Bool.decideOf e else return e

/-- The reconstruction of `(distinct x₁ … xₙ)` for `xᵢ : α`: the conjunction of `!(xᵢ == xⱼ)` for
`i < j`, in the same order as cvc5's elimination of `distinct`. -/
def buildDistinct (α : Expr) (xs : List Expr) : MetaM Expr :=
  go xs
where
  go : List Expr → MetaM Expr
  | [] => return .const ``true []
  | [_] => return .const ``true []
  | [x, y] => return mkApp (.const ``not []) (← Bool.mkBEq α x y)
  | x :: ys => do
    ys.foldrM (fun y acc => do return mkApp2 (.const ``and []) (mkApp (.const ``not []) (← Bool.mkBEq α x y)) acc)
      (← go ys)

@[smt_term_reconstruct] def reconstructBuiltin : TermReconstructor := fun t => do match t.getKind! with
  | .VARIABLE => getFVarExpr! (getVariableName t)
  | .CONSTANT => toBoolIfProp (← getFVarOrConstExpr! t.getSymbol!)
  | .EQUAL =>
    let α ← reconstructSort t[0]!.getSort!
    Bool.mkBEq α (← reconstructTerm t[0]!) (← reconstructTerm t[1]!)
  | .DISTINCT =>
    let α ← reconstructSort t[0]!.getSort!
    let xs ← t.getChildren.mapM reconstructTerm
    buildDistinct α xs.toList
  | .ITE =>
    let (u, (α : Q(Sort u))) ← reconstructSortLevelAndSort t.getSort!
    let c : Q(Bool) ← reconstructTerm t[0]!
    let x : Q($α) ← reconstructTerm t[1]!
    let y : Q($α) ← reconstructTerm t[2]!
    return q(cond $c $x $y)
  | .SKOLEM => match t.getSkolemId! with
    | .PURIFY => reconstructTerm t.getSkolemIndices![0]!
    | _ => return none
  | _ => return none
where
  getVariableName (t : cvc5.Term) : Name :=
    if t.hasSymbol! then
      if t.getSymbol!.toName == .anonymous then
        Name.mkSimple t.getSymbol!
      else
        t.getSymbol!.toName
    else Name.num `x t.getId!

def reconstructRewrite (pf : cvc5.Proof) : ReconstructM (Option Expr) := do
  match pf.getRewriteRule! with
  | .DISTINCT_ELIM =>
    let t : Q(Bool) ← reconstructTerm pf.getResult[0]!
    addEqThm pf.getResult q(Eq.refl $t)
  | .ITE_TRUE_COND =>
    let (u, (α : Q(Sort u))) ← reconstructSortLevelAndSort pf.getArguments[1]!.getSort!
    let x : Q($α) ← reconstructTerm pf.getArguments[1]!
    let y : Q($α) ← reconstructTerm pf.getArguments[2]!
    addEqThm pf.getResult q(Bool.ite_true_cond (x := $x) (y := $y))
  | .ITE_FALSE_COND =>
    let (u, (α : Q(Sort u))) ← reconstructSortLevelAndSort pf.getArguments[1]!.getSort!
    let x : Q($α) ← reconstructTerm pf.getArguments[1]!
    let y : Q($α) ← reconstructTerm pf.getArguments[2]!
    addEqThm pf.getResult q(Bool.ite_false_cond (x := $x) (y := $y))
  | .ITE_NOT_COND =>
    let c : Q(Bool) ← reconstructTerm pf.getArguments[1]!
    let (u, (α : Q(Sort u))) ← reconstructSortLevelAndSort pf.getArguments[2]!.getSort!
    let x : Q($α) ← reconstructTerm pf.getArguments[2]!
    let y : Q($α) ← reconstructTerm pf.getArguments[3]!
    addEqThm pf.getResult q(Bool.ite_not_cond (c := $c) (x := $x) (y := $y))
  | .ITE_EQ_BRANCH =>
    let c : Q(Bool) ← reconstructTerm pf.getArguments[1]!
    let (u, (α : Q(Sort u))) ← reconstructSortLevelAndSort pf.getArguments[2]!.getSort!
    let x : Q($α) ← reconstructTerm pf.getArguments[2]!
    addEqThm pf.getResult q(Bool.ite_eq_branch (c := $c) (x := $x))
  | .ITE_THEN_LOOKAHEAD =>
    let c : Q(Bool) ← reconstructTerm pf.getArguments[1]!
    let (u, (α : Q(Sort u))) ← reconstructSortLevelAndSort pf.getArguments[2]!.getSort!
    let x : Q($α) ← reconstructTerm pf.getArguments[2]!
    let y : Q($α) ← reconstructTerm pf.getArguments[3]!
    let z : Q($α) ← reconstructTerm pf.getArguments[4]!
    addEqThm pf.getResult q(Bool.ite_then_lookahead (c := $c) (x := $x) (y := $y) (z := $z))
  | .ITE_ELSE_LOOKAHEAD =>
    let c : Q(Bool) ← reconstructTerm pf.getArguments[1]!
    let (u, (α : Q(Sort u))) ← reconstructSortLevelAndSort pf.getArguments[2]!.getSort!
    let x : Q($α) ← reconstructTerm pf.getArguments[2]!
    let y : Q($α) ← reconstructTerm pf.getArguments[3]!
    let z : Q($α) ← reconstructTerm pf.getArguments[4]!
    addEqThm pf.getResult q(Bool.ite_else_lookahead (c := $c) (x := $x) (y := $y) (z := $z))
  | .ITE_THEN_NEG_LOOKAHEAD =>
    let c : Q(Bool) ← reconstructTerm pf.getArguments[1]!
    let (u, (α : Q(Sort u))) ← reconstructSortLevelAndSort pf.getArguments[2]!.getSort!
    let x : Q($α) ← reconstructTerm pf.getArguments[2]!
    let y : Q($α) ← reconstructTerm pf.getArguments[3]!
    let z : Q($α) ← reconstructTerm pf.getArguments[4]!
    addEqThm pf.getResult q(Bool.ite_then_neg_lookahead (c := $c) (x := $x) (y := $y) (z := $z))
  | .ITE_ELSE_NEG_LOOKAHEAD =>
    let c : Q(Bool) ← reconstructTerm pf.getArguments[1]!
    let (u, (α : Q(Sort u))) ← reconstructSortLevelAndSort pf.getArguments[2]!.getSort!
    let x : Q($α) ← reconstructTerm pf.getArguments[2]!
    let y : Q($α) ← reconstructTerm pf.getArguments[3]!
    let z : Q($α) ← reconstructTerm pf.getArguments[4]!
    addEqThm pf.getResult q(Bool.ite_else_neg_lookahead (c := $c) (x := $x) (y := $y) (z := $z))
  | _ => return none

@[smt_proof_reconstruct] def reconstructBuiltinProof : ProofReconstructor := fun pf => do match pf.getRule with
  | .ASSUME =>
    let p ← reconstructProofType pf.getArguments[0]!
    match (← findAssumWithType? p) with
    | none   => throwError "no assumption of type\n\t{p}\nfound in local context"
    | some a => return a
  | .SCOPE =>
    -- A scope without assumptions concludes the conclusion of its premise.
    if pf.getArguments.isEmpty then
      return ← reconstructProof pf.getChildren[0]!
    let ps : Q(List Bool) ← reconstructTerms pf.getArguments
    let as ← pf.getArguments.mapM (fun _ => return Name.num `a (← incCount))
    let q : Q(Bool) ← reconstructTerm pf.getChildren[0]!.getResult
    let h₁ : Q(Bool.impliesN $ps ($q = true)) ← Meta.mkFreshExprMVar q(Bool.impliesN $ps ($q = true))
    let (fvs, mv) ← h₁.mvarId!.introN as.size as.toList
    withNewProofCache $ mv.withContext do
      let h₂ : Q($q = true) ← withAssums (fvs.map Expr.fvar) (reconstructProof pf.getChildren[0]!)
      mv.assign h₂
    -- A scope over a refutation concludes `(not (and F₁ … Fₙ))`, other scopes conclude
    -- `(=> (and F₁ … Fₙ) F)`.
    let r := pf.getChildren[0]!.getResult
    if r.getKind! == .CONST_BOOLEAN && !r.getBooleanValue! then
      let h₁ : Q(Bool.impliesN $ps (false = true)) ← pure h₁
      addThm (← reconstructProofType pf.getResult) q(Bool.scopes_false $h₁)
    else
      addThm (← reconstructProofType pf.getResult) q(Bool.scopes $h₁)
  | .EVALUATE =>
    if pf.getResult[0]! == pf.getResult[1]! then
      let t ← reconstructTerm pf.getResult[0]!
      addEqThm pf.getResult (← Meta.mkEqRefl t)
    else
      -- `t == t'` evaluates to `true`, unless it involves noncomputable functions, e.g., of reals.
      let b : Q(Bool) ← reconstructTerm pf.getResult
      if ← usesNoncomputable b then
        return none
      let hb : Q($b = true) ← if ← useNative then nativeDecide b
        else pure (mkApp2 (.const ``Eq.refl [1]) (.const ``Bool []) (.const ``Bool.true []))
      addThm q($b = true) hb
  | .ACI_NORM =>
    addEqTac pf.getResult Meta.AC.rewriteUnnormalizedTop
  | .ABSORB =>
    let e ← reconstructTerm pf.getResult[0]!
    let z ← reconstructTerm pf.getResult[1]!
    let op := e.appFn!.appFn!
    let tac := if ← useNative then nativeAbsorb else absorb
    addEqTac pf.getResult (tac · z op)
  | .ENCODE_EQ_INTRO =>
    let (u, (α : Q(Sort u))) ← reconstructSortLevelAndSort pf.getResult[0]!.getSort!
    let y : Q($α) ← reconstructTerm pf.getResult[1]!
    addEqThm pf.getResult q(Eq.refl $y)
  | .DSL_REWRITE
  | .THEORY_REWRITE => reconstructRewrite pf
  | .ITE_ELIM1 =>
    let c : Q(Bool) ← reconstructTerm pf.getChildren[0]!.getResult[0]!
    let p : Q(Bool) ← reconstructTerm pf.getChildren[0]!.getResult[1]!
    let q : Q(Bool) ← reconstructTerm pf.getChildren[0]!.getResult[2]!
    let h : Q(cond $c $p $q = true) ← reconstructProof pf.getChildren[0]!
    addThm (← reconstructProofType pf.getResult) q(Bool.ite_elim1 $h)
  | .ITE_ELIM2 =>
    let c : Q(Bool) ← reconstructTerm pf.getChildren[0]!.getResult[0]!
    let p : Q(Bool) ← reconstructTerm pf.getChildren[0]!.getResult[1]!
    let q : Q(Bool) ← reconstructTerm pf.getChildren[0]!.getResult[2]!
    let h : Q(cond $c $p $q = true) ← reconstructProof pf.getChildren[0]!
    addThm (← reconstructProofType pf.getResult) q(Bool.ite_elim2 $h)
  | .NOT_ITE_ELIM1 =>
    let c : Q(Bool) ← reconstructTerm pf.getChildren[0]!.getResult[0]![0]!
    let p : Q(Bool) ← reconstructTerm pf.getChildren[0]!.getResult[0]![1]!
    let q : Q(Bool) ← reconstructTerm pf.getChildren[0]!.getResult[0]![2]!
    let hn : Q((!cond $c $p $q) = true) ← reconstructProof pf.getChildren[0]!
    addThm (← reconstructProofType pf.getResult) q(Bool.not_ite_elim1 $hn)
  | .NOT_ITE_ELIM2 =>
    let c : Q(Bool) ← reconstructTerm pf.getChildren[0]!.getResult[0]![0]!
    let p : Q(Bool) ← reconstructTerm pf.getChildren[0]!.getResult[0]![1]!
    let q : Q(Bool) ← reconstructTerm pf.getChildren[0]!.getResult[0]![2]!
    let hn : Q((!cond $c $p $q) = true) ← reconstructProof pf.getChildren[0]!
    addThm (← reconstructProofType pf.getResult) q(Bool.not_ite_elim2 $hn)
  | .CNF_ITE_POS1 =>
    let c : Q(Bool) ← reconstructTerm pf.getArguments[0]![0]!
    let p : Q(Bool) ← reconstructTerm pf.getArguments[0]![1]!
    let q : Q(Bool) ← reconstructTerm pf.getArguments[0]![2]!
    addThm (← reconstructProofType pf.getResult) q(Bool.cnf_ite_pos1 $c $p $q)
  | .CNF_ITE_POS2 =>
    let c : Q(Bool) ← reconstructTerm pf.getArguments[0]![0]!
    let p : Q(Bool) ← reconstructTerm pf.getArguments[0]![1]!
    let q : Q(Bool) ← reconstructTerm pf.getArguments[0]![2]!
    addThm (← reconstructProofType pf.getResult) q(Bool.cnf_ite_pos2 $c $p $q)
  | .CNF_ITE_POS3 =>
    let c : Q(Bool) ← reconstructTerm pf.getArguments[0]![0]!
    let p : Q(Bool) ← reconstructTerm pf.getArguments[0]![1]!
    let q : Q(Bool) ← reconstructTerm pf.getArguments[0]![2]!
    addThm (← reconstructProofType pf.getResult) q(Bool.cnf_ite_pos3 $c $p $q)
  | .CNF_ITE_NEG1 =>
    let c : Q(Bool) ← reconstructTerm pf.getArguments[0]![0]!
    let p : Q(Bool) ← reconstructTerm pf.getArguments[0]![1]!
    let q : Q(Bool) ← reconstructTerm pf.getArguments[0]![2]!
    addThm (← reconstructProofType pf.getResult) q(Bool.cnf_ite_neg1 $c $p $q)
  | .CNF_ITE_NEG2 =>
    let c : Q(Bool) ← reconstructTerm pf.getArguments[0]![0]!
    let p : Q(Bool) ← reconstructTerm pf.getArguments[0]![1]!
    let q : Q(Bool) ← reconstructTerm pf.getArguments[0]![2]!
    addThm (← reconstructProofType pf.getResult) q(Bool.cnf_ite_neg2 $c $p $q)
  | .CNF_ITE_NEG3 =>
    let c : Q(Bool) ← reconstructTerm pf.getArguments[0]![0]!
    let p : Q(Bool) ← reconstructTerm pf.getArguments[0]![1]!
    let q : Q(Bool) ← reconstructTerm pf.getArguments[0]![2]!
    addThm (← reconstructProofType pf.getResult) q(Bool.cnf_ite_neg3 $c $p $q)
  | .SKOLEM_INTRO =>
    let (u, (α : Q(Sort u))) ← reconstructSortLevelAndSort pf.getResult[0]!.getSort!
    let t : Q($α) ← reconstructTerm pf.getResult[1]!
    addEqThm pf.getResult q(Eq.refl $t)
  | _ => return none
where
  /-- A proof of `b = true` by native evaluation of `b`. -/
  nativeDecide (b : Q(Bool)) : MetaM Q($b = true) := do
    match ← Meta.nativeEqTrue `Smt.eval b with
    | .notTrue =>
      throwError m!"[smt_eval] evaluated that{indentExpr b}\nis false"
    | .success h => return h

end Smt.Reconstruct.Builtin
