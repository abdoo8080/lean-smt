/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

module

public import Smt.Reconstruct
public meta import Smt.Reconstruct
public import Smt.Reconstruct.UF.Congruence
public meta import Smt.Reconstruct.UF.Congruence
public import Smt.Reconstruct.Bool.Lemmas
public meta import Smt.Reconstruct.Bool.Lemmas
public import Smt.Reconstruct.Bool.Rewrites
public meta import Smt.Reconstruct.Bool.Rewrites

public meta section

namespace Smt.Reconstruct.UF

open Lean Qq

def getFVarOrConstExpr! (n : String) : ReconstructM Expr := do
  match (← read).userNames[n]? with
  | some e => return e
  | none   => match (← getLCtx).findFromUserName? n.toName with
    | some d => return d.toExpr
    | none   =>
      let c ← getConstInfo n.toName
      return .const c.name (c.numLevelParams.repeat (.zero :: ·) [])

@[smt_sort_reconstruct] def reconstructUS : SortReconstructor := fun s => do match s.getKind! with
  | .UNINTERPRETED_SORT => getFVarOrConstExpr! s.getSymbol!
  | _ =>
    if s.isInstantiated then
      if let some ctor := s.getUninterpretedSortConstructor? then
        let base ← reconstructSort ctor
        let params ← s.getInstantiatedParameters!.mapM reconstructSort
        return some (mkAppN base params)
      else
        return none
    else
      return none

/-- The proposition `p` of the Boolean atom `decide p`, and `b = true` for other Booleans `b`.
Used to pass an SMT-LIB argument of sort `Bool` to a Lean function that takes a proposition. -/
def ofBool (b : Expr) : MetaM Expr := do
  if let some (p, _) := b.app2? ``Decidable.decide then return p
  Meta.mkEq b (.const ``Bool.true [])

@[smt_term_reconstruct] def reconstructUF : TermReconstructor := fun t => do match t.getKind! with
  | .APPLY_UF =>
    -- Lean functions may take and return propositions, which SMT-LIB treats as Booleans.
    let mut curr ← reconstructTerm t[0]!
    for i in [1:t.getNumChildren] do
      let arg ← reconstructTerm t[i]!
      let arg ← match ← Meta.whnf (← Meta.inferType curr) with
        | .forallE _ d _ _ => if d.isProp then ofBool arg else pure arg
        | _ => pure arg
      curr := .app curr arg
    if (← Meta.inferType curr).isProp then Bool.decideOf curr else return curr
  | .UNINTERPRETED_SORT_VALUE =>
    let some n := (← read).sortCard[t.getSort!]? | throwError "unknown sort {t.getSort!}"
    let s := t.toString
    let endPos := (s.rawEndPos - t.getSort!.toString).decreaseBy 2
    let endPos := s.pos! (if endPos.dec.get? s == some '|' then endPos.dec else endPos)
    let startPos := (endPos.revFind? (· != '_')).get!
    let i : Nat := (s.extract startPos endPos).toNat!
    if h : i < n then
      let i : Fin n := ⟨i, h⟩
      return toExpr i
    else
      throwError "index {i} is out of bounds for uninterpreted sort of cardinality {n}"
  | .SKOLEM =>
    match t.getSkolemId! with
    | .GROUND_TERM =>
      let (u, (α : Q(Sort u))) ← reconstructSortLevelAndSort t.getSort!
      let hα : Q(Nonempty $α) ← Meta.synthInstance q(Nonempty $α)
      return q(Classical.choice $hα)
    | _ => return none
  | _ => return none

def reconstructRewrite (pf : cvc5.Proof) : ReconstructM (Option Expr) := do
  match pf.getRewriteRule! with
  | .EQ_REFL =>
    let (u, (α : Q(Sort u))) ← reconstructSortLevelAndSort pf.getArguments[1]!.getSort!
    let _ : Q(DecidableEq $α) ← Bool.decEqInst α
    let t : Q($α) ← reconstructTerm pf.getArguments[1]!
    addThm (← reconstructProofType pf.getResult) q(Bool.eq_refl (t := $t))
  | .EQ_SYMM =>
    let (u, (α : Q(Sort u))) ← reconstructSortLevelAndSort pf.getArguments[1]!.getSort!
    let _ : Q(DecidableEq $α) ← Bool.decEqInst α
    let t : Q($α) ← reconstructTerm pf.getArguments[1]!
    let s : Q($α) ← reconstructTerm pf.getArguments[2]!
    addThm (← reconstructProofType pf.getResult) q(Bool.eq_symm (t := $t) (s := $s))
  | .EQ_COND_DEQ =>
    let (u, (α : Q(Sort u))) ← reconstructSortLevelAndSort pf.getArguments[1]!.getSort!
    let _ : Q(DecidableEq $α) ← Bool.decEqInst α
    let t : Q($α) ← reconstructTerm pf.getArguments[1]!
    let s : Q($α) ← reconstructTerm pf.getArguments[2]!
    let r : Q($α) ← reconstructTerm pf.getArguments[3]!
    let h : Q(Bool.eq (decide ($s = $r)) false) ← reconstructProof pf.getChildren[0]!
    addThm (← reconstructProofType pf.getResult) q(Bool.eq_cond_deq (t := $t) $h)
  | .EQ_ITE_LIFT =>
    let c : Q(Bool) ← reconstructTerm pf.getArguments[1]!
    let (u, (α : Q(Sort u))) ← reconstructSortLevelAndSort pf.getArguments[2]!.getSort!
    let _ : Q(DecidableEq $α) ← Bool.decEqInst α
    let t : Q($α) ← reconstructTerm pf.getArguments[2]!
    let s : Q($α) ← reconstructTerm pf.getArguments[3]!
    let r : Q($α) ← reconstructTerm pf.getArguments[4]!
    addThm (← reconstructProofType pf.getResult)
      q(Bool.eq_ite_lift (c := $c) (t := $t) (s := $s) (r := $r))
  | .DISTINCT_BINARY_ELIM =>
    let t : Q(Bool) ← reconstructTerm pf.getResult[0]!
    addThm (← reconstructProofType pf.getResult) q(Bool.eq.refl $t)
  | _ => return none

/-- The triples of the reconstructions of the sides of the equalities that `pfs` prove, and their
proofs, for congruence (see `smtCongr`). -/
def reconstructCongrPremises (pfs : Array cvc5.Proof) :
    ReconstructM (Array (Expr × Expr × Expr)) :=
  pfs.mapM fun pf => do
    let a ← reconstructTerm pf.getResult[0]!
    let b ← reconstructTerm pf.getResult[1]!
    return (a, b, ← reconstructProof pf)

@[smt_proof_reconstruct] def reconstructUFProof : ProofReconstructor := fun pf => do match pf.getRule with
  | .DSL_REWRITE => reconstructRewrite pf
  | .REFL =>
    let (u, (α : Q(Sort u))) ← reconstructSortLevelAndSort pf.getArguments[0]!.getSort!
    let _ : Q(DecidableEq $α) ← Bool.decEqInst α
    let a : Q($α) ← reconstructTerm pf.getArguments[0]!
    addThm (← reconstructProofType pf.getResult) q(Bool.eq.refl $a)
  | .SYMM =>
    if pf.getResult.getKind! == .EQUAL then
      let (u, (α : Q(Sort u))) ← reconstructSortLevelAndSort pf.getResult[0]!.getSort!
      let _ : Q(DecidableEq $α) ← Bool.decEqInst α
      let a : Q($α) ← reconstructTerm pf.getResult[1]!
      let b : Q($α) ← reconstructTerm pf.getResult[0]!
      let h : Q(Bool.eq $a $b) ← reconstructProof pf.getChildren[0]!
      addThm (← reconstructProofType pf.getResult) q(Bool.eq.symm $h)
    else
      let (u, (α : Q(Sort u))) ← reconstructSortLevelAndSort pf.getResult[0]![0]!.getSort!
      let _ : Q(DecidableEq $α) ← Bool.decEqInst α
      let a : Q($α) ← reconstructTerm pf.getResult[0]![1]!
      let b : Q($α) ← reconstructTerm pf.getResult[0]![0]!
      let h : Q((!decide ($a = $b)) = true) ← reconstructProof pf.getChildren[0]!
      addThm (← reconstructProofType pf.getResult) q(Bool.not_decide_eq_symm $h)
  | .TRANS =>
    let cpfs := pf.getChildren
    let (u, (α : Q(Sort u))) ← reconstructSortLevelAndSort cpfs[0]!.getResult[0]!.getSort!
    let _ : Q(DecidableEq $α) ← Bool.decEqInst α
    let a : Q($α) ← reconstructTerm cpfs[0]!.getResult[0]!
    let mut curr ← reconstructProof cpfs[0]!
    for i in [1:cpfs.size] do
      let b : Q($α) ← reconstructTerm cpfs[i]!.getResult[0]!
      let c : Q($α) ← reconstructTerm cpfs[i]!.getResult[1]!
      let hab : Q(Bool.eq $a $b) := curr
      let hbc : Q(Bool.eq $b $c) ← reconstructProof cpfs[i]!
      curr := q(Bool.eq.trans $hab $hbc)
    addThm (← reconstructProofType pf.getResult) curr
  | .CONG =>
    let k := pf.getResult[0]!.getKind!
    if k == .FORALL || k == .EXISTS || k == .WITNESS || k == .LAMBDA || k == .SET_COMPREHENSION then
      return none
    let l ← reconstructTerm pf.getResult[0]!
    let r ← reconstructTerm pf.getResult[1]!
    let hs ← reconstructCongrPremises pf.getChildren
    addThm (← reconstructProofType pf.getResult) (← smtCongr l r hs)
  | .NARY_CONG =>
    let l ← reconstructTerm pf.getResult[0]!
    let r ← reconstructTerm pf.getResult[1]!
    let hs ← reconstructCongrPremises pf.getChildren
    addThm (← reconstructProofType pf.getResult) (← smtCongr l r hs)
  | .HO_CONG =>
    let mut f ← reconstructTerm pf.getChildren[0]!.getResult[0]!
    let mut g ← reconstructTerm pf.getChildren[0]!.getResult[1]!
    let mut h ← reconstructProof pf.getChildren[0]!
    for (a, b, hab) in ← reconstructCongrPremises pf.getChildren[1:] do
      h ← mkBoolEqCongr f g a b h hab
      f := .app f a
      g := .app g b
    addThm (← reconstructProofType pf.getResult) h
  | _ => return none

end Smt.Reconstruct.UF
