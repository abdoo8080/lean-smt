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
public import Smt.Reconstruct.UF.Rewrites
public meta import Smt.Reconstruct.UF.Rewrites

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
    let α ← reconstructSort pf.getArguments[1]!.getSort!
    let t ← reconstructTerm pf.getArguments[1]!
    addEqThm pf.getResult
      (mkApp3 (.const ``Bool.eq_refl [← Meta.getLevel α]) α t (← Bool.eqInst α t t))
  | .EQ_SYMM =>
    let α ← reconstructSort pf.getArguments[1]!.getSort!
    let t ← reconstructTerm pf.getArguments[1]!
    let s ← reconstructTerm pf.getArguments[2]!
    addEqThm pf.getResult (mkAppN (.const ``Bool.eq_symm [← Meta.getLevel α])
      #[α, t, s, ← Bool.eqInst α t s, ← Bool.eqInst α s t])
  | .EQ_COND_DEQ =>
    let α ← reconstructSort pf.getArguments[1]!.getSort!
    let t ← reconstructTerm pf.getArguments[1]!
    let s ← reconstructTerm pf.getArguments[2]!
    let r ← reconstructTerm pf.getArguments[3]!
    -- `(s == r) = false`
    let h ← reconstructEqProof pf.getChildren[0]!
    addEqThm pf.getResult (mkAppN (.const ``Bool.eq_cond_deq [← Meta.getLevel α])
      #[α, t, s, r, ← Bool.eqInst α s r, ← Bool.eqInst α t s, ← Bool.eqInst α t r, h])
  | .EQ_ITE_LIFT =>
    let c ← reconstructTerm pf.getArguments[1]!
    let α ← reconstructSort pf.getArguments[2]!.getSort!
    let t ← reconstructTerm pf.getArguments[2]!
    let s ← reconstructTerm pf.getArguments[3]!
    let r ← reconstructTerm pf.getArguments[4]!
    let u ← Meta.getLevel α
    let cts := mkApp4 (.const ``cond [u]) α c t s
    addEqThm pf.getResult (mkAppN (.const ``Bool.eq_ite_lift [u])
      #[α, c, t, s, r, ← Bool.eqInst α cts r, ← Bool.eqInst α t r, ← Bool.eqInst α s r])
  | .DISTINCT_BINARY_ELIM =>
    let t : Q(Bool) ← reconstructTerm pf.getResult[0]!
    addEqThm pf.getResult q(Eq.refl $t)
  | _ => return none

@[smt_proof_reconstruct] def reconstructUFProof : ProofReconstructor := fun pf => do match pf.getRule with
  | .DSL_REWRITE => reconstructRewrite pf
  | .REFL =>
    let (u, (α : Q(Sort u))) ← reconstructSortLevelAndSort pf.getArguments[0]!.getSort!
    let a : Q($α) ← reconstructTerm pf.getArguments[0]!
    addEqThm pf.getResult q(Eq.refl $a)
  | .SYMM =>
    if pf.getResult.getKind! == .EQUAL then
      let (u, (α : Q(Sort u))) ← reconstructSortLevelAndSort pf.getResult[0]!.getSort!
      let a : Q($α) ← reconstructTerm pf.getResult[1]!
      let b : Q($α) ← reconstructTerm pf.getResult[0]!
      let h : Q($a = $b) ← reconstructEqProof pf.getChildren[0]!
      addEqThm pf.getResult q(Eq.symm $h)
    else
      let α ← reconstructSort pf.getResult[0]![0]!.getSort!
      let a ← reconstructTerm pf.getResult[0]![1]!
      let b ← reconstructTerm pf.getResult[0]![0]!
      -- `(!(a == b)) = true`
      let h ← reconstructProof pf.getChildren[0]!
      addThm (← reconstructProofType pf.getResult)
        (mkAppN (.const ``Bool.not_decide_eq_symm [← Meta.getLevel α])
          #[α, a, b, ← Bool.eqInst α a b, ← Bool.eqInst α b a, h])
  | .TRANS =>
    let cpfs := pf.getChildren
    let (u, (α : Q(Sort u))) ← reconstructSortLevelAndSort cpfs[0]!.getResult[0]!.getSort!
    let a : Q($α) ← reconstructTerm cpfs[0]!.getResult[0]!
    let mut curr ← reconstructEqProof cpfs[0]!
    for i in [1:cpfs.size] do
      let b : Q($α) ← reconstructTerm cpfs[i]!.getResult[0]!
      let c : Q($α) ← reconstructTerm cpfs[i]!.getResult[1]!
      let hab : Q($a = $b) := curr
      let hbc : Q($b = $c) ← reconstructEqProof cpfs[i]!
      curr := q(Eq.trans $hab $hbc)
    addEqThm pf.getResult curr
  | .CONG =>
    let k := pf.getResult[0]!.getKind!
    if k == .FORALL || k == .EXISTS || k == .WITNESS || k == .LAMBDA || k == .SET_COMPREHENSION then
      return none
    let assums ← pf.getChildren.mapM reconstructEqProof
    addEqTac pf.getResult (smtCongr · assums)
  | .NARY_CONG =>
    let assums ← pf.getChildren.mapM reconstructEqProof
    addEqTac pf.getResult (smtCongr · assums)
  | .HO_CONG =>
    let f ← reconstructTerm pf.getChildren[0]!.getResult[0]!
    let g ← reconstructTerm pf.getChildren[0]!.getResult[0]!
    let hfg ← reconstructEqProof pf.getChildren[0]!
    let hs := pf.getChildren[1:]
    let buildProof := fun (f₁, f₂, h₁) cpf => do
      let some (α, β) := (← Meta.inferType f₁).arrow? | throwError "[ho_congr]: expected function type"
      let .sort u ← Meta.inferType α | throwError "[ho_congr]: expected the type of {α} to be a sort"
      let .sort v ← Meta.inferType β | throwError "[ho_congr]: expected the type of {β} to be a sort"
      let α : Q(Sort u) ← pure α
      let β : Q(Sort v) ← pure β
      let a₁ : Q($α) ← reconstructTerm cpf.getResult[0]!
      let a₂ : Q($α) ← reconstructTerm cpf.getResult[1]!
      let f₁ : Q($α → $β) ← pure f₁
      let f₂ : Q($α → $β) ← pure f₂
      let h₁ : Q($f₁ = $f₂) ← pure h₁
      let h₂ : Q($a₁ = $a₂) ← reconstructEqProof cpf
      return (q($f₁ $a₁), q($f₂ $a₂), q(congr $h₁ $h₂))
    let (_, _, h) ← hs.foldlM buildProof (f, g, hfg)
    addEqThm pf.getResult h
  | _ => return none

end Smt.Reconstruct.UF
