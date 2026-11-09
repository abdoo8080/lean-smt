/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

module

public import Smt.Reconstruct
public meta import Smt.Reconstruct
public import Smt.Reconstruct.Builtin.AC
public meta import Smt.Reconstruct.Builtin.AC
public import Smt.Reconstruct.Bool.Lemmas
public meta import Smt.Reconstruct.Bool.Lemmas
public import Smt.Reconstruct.Bool.Rewrites
public meta import Smt.Reconstruct.Bool.Rewrites
public import Smt.Reconstruct.Prop.Lemmas
public meta import Smt.Reconstruct.Prop.Lemmas

public meta section

/-!
# Reconstruction of propositional logic

SMT-LIB's `Bool` sort is reconstructed as Lean's `Bool`, its connectives as Boolean operators, and a
proof of a formula `φ` as a proof of `⟦φ⟧ = true`.
-/

namespace Smt.Reconstruct.Prop

open Lean Qq

@[smt_sort_reconstruct] def reconstructPropSort : SortReconstructor := fun s => do match s.getKind! with
  | .BOOLEAN_SORT => return q(Bool)
  | _             => return none

@[smt_term_reconstruct] def reconstructProp : TermReconstructor := fun t => do match t.getKind! with
  | .CONST_BOOLEAN => return if t.getBooleanValue! then q(true) else q(false)
  | .NOT =>
    let b : Q(Bool) ← reconstructTerm t[0]!
    return q(!$b)
  | .IMPLIES => rightAssocOp q(Bool.smtImp) t
  | .AND => rightAssocOp q(and) t
  | .OR => rightAssocOp q(or) t
  | .XOR => rightAssocOp q(xor) t
  | _ => return none
where
  rightAssocOp (op : Expr) (t : cvc5.Term) : ReconstructM Expr := do
    let mut curr ← reconstructTerm t[t.getNumChildren - 1]!
    for i in [1:t.getNumChildren] do
      curr := mkApp2 op (← reconstructTerm t[t.getNumChildren - i - 1]!) curr
    return curr

def reconstructRewrite (pf : cvc5.Proof) : ReconstructM (Option Expr) := do
  match pf.getRewriteRule! with
  | .BOOL_DOUBLE_NOT_ELIM =>
    let t : Q(Bool) ← reconstructTerm pf.getArguments[1]!
    addEqThm pf.getResult q(Bool.bool_double_not_elim (t := $t))
  | .BOOL_NOT_TRUE =>
    let t : Q(Bool) ← reconstructTerm pf.getArguments[1]!
    let h : Q($t = false) ← reconstructEqProof pf.getChildren[0]!
    addEqThm pf.getResult q(Bool.bool_not_true (t := $t) $h)
  | .BOOL_NOT_FALSE =>
    let t : Q(Bool) ← reconstructTerm pf.getArguments[1]!
    let h : Q($t = true) ← reconstructEqProof pf.getChildren[0]!
    addEqThm pf.getResult q(Bool.bool_not_false (t := $t) $h)
  | .BOOL_EQ_TRUE =>
    let t : Q(Bool) ← reconstructTerm pf.getArguments[1]!
    addEqThm pf.getResult q(Bool.bool_eq_true (t := $t))
  | .BOOL_EQ_FALSE =>
    let t : Q(Bool) ← reconstructTerm pf.getArguments[1]!
    addEqThm pf.getResult q(Bool.bool_eq_false (t := $t))
  | .BOOL_EQ_NREFL =>
    let t : Q(Bool) ← reconstructTerm pf.getArguments[1]!
    addEqThm pf.getResult q(Bool.bool_eq_nrefl (t := $t))
  | .BOOL_IMPL_FALSE1 =>
    let t : Q(Bool) ← reconstructTerm pf.getArguments[1]!
    addEqThm pf.getResult q(Bool.bool_impl_false1 (t := $t))
  | .BOOL_IMPL_FALSE2 =>
    let t : Q(Bool) ← reconstructTerm pf.getArguments[1]!
    addEqThm pf.getResult q(Bool.bool_impl_false2 (t := $t))
  | .BOOL_IMPL_TRUE1 =>
    let t : Q(Bool) ← reconstructTerm pf.getArguments[1]!
    addEqThm pf.getResult q(Bool.bool_impl_true1 (t := $t))
  | .BOOL_IMPL_TRUE2 =>
    let t : Q(Bool) ← reconstructTerm pf.getArguments[1]!
    addEqThm pf.getResult q(Bool.bool_impl_true2 (t := $t))
  | .BOOL_IMPL_ELIM =>
    let t : Q(Bool) ← reconstructTerm pf.getArguments[1]!
    let s : Q(Bool) ← reconstructTerm pf.getArguments[2]!
    addEqThm pf.getResult q(Bool.bool_impl_elim (t := $t) (s := $s))
  | .BOOL_DUAL_IMPL_EQ =>
    let t : Q(Bool) ← reconstructTerm pf.getArguments[1]!
    let s : Q(Bool) ← reconstructTerm pf.getArguments[2]!
    addEqThm pf.getResult q(Bool.bool_dual_impl_eq (t := $t) (s := $s))
  | .BOOL_AND_CONF =>
    let xs : Q(List Bool) ← reconstructTerms pf.getArguments[1]!.getChildren
    let w : Q(Bool) ← reconstructTerm pf.getArguments[2]!
    let ys : Q(List Bool) ← reconstructTerms pf.getArguments[3]!.getChildren
    let zs : Q(List Bool) ← reconstructTerms pf.getArguments[4]!.getChildren
    addEqThm pf.getResult q(Bool.bool_and_conf (xs := $xs) (w := $w) (ys := $ys) (zs := $zs))
  | .BOOL_AND_CONF2 =>
    let xs : Q(List Bool) ← reconstructTerms pf.getArguments[1]!.getChildren
    let w : Q(Bool) ← reconstructTerm pf.getArguments[2]!
    let ys : Q(List Bool) ← reconstructTerms pf.getArguments[3]!.getChildren
    let zs : Q(List Bool) ← reconstructTerms pf.getArguments[4]!.getChildren
    addEqThm pf.getResult q(Bool.bool_and_conf2 (xs := $xs) (w := $w) (ys := $ys) (zs := $zs))
  | .BOOL_OR_TAUT =>
    let xs : Q(List Bool) ← reconstructTerms pf.getArguments[1]!.getChildren
    let w : Q(Bool) ← reconstructTerm pf.getArguments[2]!
    let ys : Q(List Bool) ← reconstructTerms pf.getArguments[3]!.getChildren
    let zs : Q(List Bool) ← reconstructTerms pf.getArguments[4]!.getChildren
    addEqThm pf.getResult q(Bool.bool_or_taut (xs := $xs) (w := $w) (ys := $ys) (zs := $zs))
  | .BOOL_OR_TAUT2 =>
    let xs : Q(List Bool) ← reconstructTerms pf.getArguments[1]!.getChildren
    let w : Q(Bool) ← reconstructTerm pf.getArguments[2]!
    let ys : Q(List Bool) ← reconstructTerms pf.getArguments[3]!.getChildren
    let zs : Q(List Bool) ← reconstructTerms pf.getArguments[4]!.getChildren
    addEqThm pf.getResult q(Bool.bool_or_taut2 (xs := $xs) (w := $w) (ys := $ys) (zs := $zs))
  | .BOOL_OR_DE_MORGAN =>
    let x : Q(Bool) ← reconstructTerm pf.getArguments[1]!
    let y : Q(Bool) ← reconstructTerm pf.getArguments[2]!
    let zs : Q(List Bool) ← reconstructTerms pf.getArguments[3]!.getChildren
    addEqThm pf.getResult q(Bool.bool_or_de_morgan (x := $x) (y := $y) (zs := $zs))
  | .BOOL_IMPLIES_DE_MORGAN =>
    let x : Q(Bool) ← reconstructTerm pf.getArguments[1]!
    let y : Q(Bool) ← reconstructTerm pf.getArguments[2]!
    addEqThm pf.getResult q(Bool.bool_implies_de_morgan (x := $x) (y := $y))
  | .BOOL_AND_DE_MORGAN =>
    let x : Q(Bool) ← reconstructTerm pf.getArguments[1]!
    let y : Q(Bool) ← reconstructTerm pf.getArguments[2]!
    let zs : Q(List Bool) ← reconstructTerms pf.getArguments[3]!.getChildren
    addEqThm pf.getResult q(Bool.bool_and_de_morgan (x := $x) (y := $y) (zs := $zs))
  | .BOOL_OR_AND_DISTRIB =>
    let y₁ : Q(Bool) ← reconstructTerm pf.getArguments[1]!
    let y₂ : Q(Bool) ← reconstructTerm pf.getArguments[2]!
    let ys : Q(List Bool) ← reconstructTerms pf.getArguments[3]!.getChildren
    let z₁ : Q(Bool) ← reconstructTerm pf.getArguments[4]!
    let zs : Q(List Bool) ← reconstructTerms pf.getArguments[5]!.getChildren
    addEqThm pf.getResult
      q(Bool.bool_or_and_distrib (y₁ := $y₁) (y₂ := $y₂) (ys := $ys) (z₁ := $z₁) (zs := $zs))
  | .BOOL_IMPLIES_OR_DISTRIB =>
    let y₁ : Q(Bool) ← reconstructTerm pf.getArguments[1]!
    let y₂ : Q(Bool) ← reconstructTerm pf.getArguments[2]!
    let ys : Q(List Bool) ← reconstructTerms pf.getArguments[3]!.getChildren
    let z : Q(Bool) ← reconstructTerm pf.getArguments[4]!
    addEqThm pf.getResult
      q(Bool.bool_implies_or_distrib (y₁ := $y₁) (y₂ := $y₂) (ys := $ys) (z := $z))
  | .BOOL_XOR_REFL =>
    let x : Q(Bool) ← reconstructTerm pf.getArguments[1]!
    addEqThm pf.getResult q(Bool.bool_xor_refl (x := $x))
  | .BOOL_XOR_NREFL =>
    let x : Q(Bool) ← reconstructTerm pf.getArguments[1]!
    addEqThm pf.getResult q(Bool.bool_xor_nrefl (x := $x))
  | .BOOL_XOR_FALSE =>
    let x : Q(Bool) ← reconstructTerm pf.getArguments[1]!
    addEqThm pf.getResult q(Bool.bool_xor_false (x := $x))
  | .BOOL_XOR_TRUE =>
    let x : Q(Bool) ← reconstructTerm pf.getArguments[1]!
    addEqThm pf.getResult q(Bool.bool_xor_true (x := $x))
  | .BOOL_XOR_COMM =>
    let x : Q(Bool) ← reconstructTerm pf.getArguments[1]!
    let y : Q(Bool) ← reconstructTerm pf.getArguments[2]!
    addEqThm pf.getResult q(Bool.bool_xor_comm (x := $x) (y := $y))
  | .BOOL_XOR_ELIM =>
    let x : Q(Bool) ← reconstructTerm pf.getArguments[1]!
    let y : Q(Bool) ← reconstructTerm pf.getArguments[2]!
    addEqThm pf.getResult q(Bool.bool_xor_elim (x := $x) (y := $y))
  | .BOOL_NOT_XOR_ELIM =>
    let x : Q(Bool) ← reconstructTerm pf.getArguments[1]!
    let y : Q(Bool) ← reconstructTerm pf.getArguments[2]!
    addEqThm pf.getResult q(Bool.bool_not_xor_elim (x := $x) (y := $y))
  | .BOOL_NOT_EQ_ELIM1 =>
    let x : Q(Bool) ← reconstructTerm pf.getArguments[1]!
    let y : Q(Bool) ← reconstructTerm pf.getArguments[2]!
    addEqThm pf.getResult q(Bool.bool_not_eq_elim1 (x := $x) (y := $y))
  | .BOOL_NOT_EQ_ELIM2 =>
    let x : Q(Bool) ← reconstructTerm pf.getArguments[1]!
    let y : Q(Bool) ← reconstructTerm pf.getArguments[2]!
    addEqThm pf.getResult q(Bool.bool_not_eq_elim2 (x := $x) (y := $y))
  | .ITE_NEG_BRANCH =>
    let c : Q(Bool) ← reconstructTerm pf.getArguments[1]!
    let x : Q(Bool) ← reconstructTerm pf.getArguments[2]!
    let y : Q(Bool) ← reconstructTerm pf.getArguments[3]!
    let h : Q($x = !$y) ← reconstructEqProof pf.getChildren[0]!
    addEqThm pf.getResult q(Bool.ite_neg_branch (c := $c) (x := $x) (y := $y) $h)
  | .ITE_THEN_TRUE =>
    let c : Q(Bool) ← reconstructTerm pf.getArguments[1]!
    let x : Q(Bool) ← reconstructTerm pf.getArguments[2]!
    addEqThm pf.getResult q(Bool.ite_then_true (c := $c) (x := $x))
  | .ITE_ELSE_FALSE =>
    let c : Q(Bool) ← reconstructTerm pf.getArguments[1]!
    let x : Q(Bool) ← reconstructTerm pf.getArguments[2]!
    addEqThm pf.getResult q(Bool.ite_else_false (c := $c) (x := $x))
  | .ITE_THEN_FALSE =>
    let c : Q(Bool) ← reconstructTerm pf.getArguments[1]!
    let x : Q(Bool) ← reconstructTerm pf.getArguments[2]!
    addEqThm pf.getResult q(Bool.ite_then_false (c := $c) (x := $x))
  | .ITE_ELSE_TRUE =>
    let c : Q(Bool) ← reconstructTerm pf.getArguments[1]!
    let x : Q(Bool) ← reconstructTerm pf.getArguments[2]!
    addEqThm pf.getResult q(Bool.ite_else_true (c := $c) (x := $x))
  | .ITE_THEN_LOOKAHEAD_SELF =>
    let c : Q(Bool) ← reconstructTerm pf.getArguments[1]!
    let x : Q(Bool) ← reconstructTerm pf.getArguments[2]!
    addEqThm pf.getResult q(Bool.ite_then_lookahead_self (c := $c) (x := $x))
  | .ITE_ELSE_LOOKAHEAD_SELF =>
    let c : Q(Bool) ← reconstructTerm pf.getArguments[1]!
    let x : Q(Bool) ← reconstructTerm pf.getArguments[2]!
    addEqThm pf.getResult q(Bool.ite_else_lookahead_self (c := $c) (x := $x))
  | .ITE_THEN_LOOKAHEAD_NOT_SELF =>
    let c : Q(Bool) ← reconstructTerm pf.getArguments[1]!
    let x : Q(Bool) ← reconstructTerm pf.getArguments[2]!
    addEqThm pf.getResult q(Bool.ite_then_lookahead_not_self (c := $c) (x := $x))
  | .ITE_ELSE_LOOKAHEAD_NOT_SELF =>
    let c : Q(Bool) ← reconstructTerm pf.getArguments[1]!
    let x : Q(Bool) ← reconstructTerm pf.getArguments[2]!
    addEqThm pf.getResult q(Bool.ite_else_lookahead_not_self (c := $c) (x := $x))
  | .ITE_EXPAND =>
    let c : Q(Bool) ← reconstructTerm pf.getArguments[1]!
    let x : Q(Bool) ← reconstructTerm pf.getArguments[2]!
    let y : Q(Bool) ← reconstructTerm pf.getArguments[3]!
    addEqThm pf.getResult q(Bool.ite_expand (c := $c) (x := $x) (y := $y))
  | .BOOL_NOT_ITE_ELIM =>
    let c : Q(Bool) ← reconstructTerm pf.getArguments[1]!
    let x : Q(Bool) ← reconstructTerm pf.getArguments[2]!
    let y : Q(Bool) ← reconstructTerm pf.getArguments[3]!
    addEqThm pf.getResult q(Bool.bool_not_ite_elim (c := $c) (x := $x) (y := $y))
  | _ => return none

def nary (k : cvc5.Kind) (c : cvc5.Term) : Array cvc5.Term := Id.run do
  if c.getKind! != k then
    return #[c]
  let mut cs := #[]
  for cc in c do
    cs := cs.push cc
  return cs

def reclausify (c : Array cvc5.Term) (l : cvc5.Term) : Array cvc5.Term :=
  if c == nary .OR l then #[l] else c

def clausify (c l : cvc5.Term) : Array cvc5.Term :=
  reclausify (nary .OR c) l

private def isNotOf (t₁ t₂ : cvc5.Term) : Bool :=
  t₁.getKind! == .NOT && t₁[0]! == t₂

def getResolutionResult (c₁ c₂ : Array cvc5.Term) (pol l : cvc5.Term) : Array cvc5.Term := Id.run do
  let l₁ := if pol.getBooleanValue! then (· == l) else (isNotOf · l)
  let l₂ := if pol.getBooleanValue! then (isNotOf · l) else (· == l)
  return c₁.eraseP l₁ ++ c₂.eraseP l₂

/-- The Boolean formulas `ts` as a list. -/
def reconstructBools (ts : Array cvc5.Term) : ReconstructM Q(List Bool) :=
  ts.foldrM (init := q([])) fun t bs => do
    let b : Q(Bool) ← reconstructTerm t
    return q($b :: $bs)

def reconstructResolution (c₁ c₂ : Array cvc5.Term) (pol l : cvc5.Term) (hps hqs : Expr) : ReconstructM Expr := do
  let ps : Q(List Bool) ← reconstructBools c₁
  let qs : Q(List Bool) ← reconstructBools c₂
  let hps : Q(Bool.orN $ps = true) ← pure hps
  let hqs : Q(Bool.orN $qs = true) ← pure hqs
  let (i?, j?) := if pol.getBooleanValue!
    then (c₁.finIdxOf? l, c₂.findFinIdx? (isNotOf · l))
    else (c₁.findFinIdx? (isNotOf · l), c₂.finIdxOf? l)
  if let (some ⟨i, _⟩, some ⟨j, _⟩) := (i?, j?) then
    let hi : Q($i < «$ps».length) := .app q(@of_decide_eq_true ($i < «$ps».length) _) q(Eq.refl true)
    let hj : Q($j < «$qs».length) := .app q(@of_decide_eq_true ($j < «$qs».length) _) q(Eq.refl true)
    let hij : Q($ps[$i] = !$qs[$j]) :=
      if pol.getBooleanValue! then .app q(fun b => Eq.symm (Bool.not_not b)) q($ps[$i])
      else .app q(@Eq.refl Bool) q($ps[$i])
    return q(Bool.orN_resolution $hps $hqs $hi $hj $hij)
  else
    return q(Bool.orN_append_left (qs := $qs) $hps)

def reconstructChainResolution (cs as : Array cvc5.Term) (ps : Array Expr) : ReconstructM Expr := do
  let mut cc := nary .OR cs[0]!
  let mut cp := ps[0]!
  for i in [1:cs.size] do
    let pol := as[0]![i - 1]!
    let l := as[1]![i - 1]!
    cc := reclausify cc l
    cp ← reconstructResolution cc (clausify cs[i]! l) pol l cp ps[i]!
    cc := getResolutionResult cc (clausify cs[i]! l) pol l
  return cp

@[smt_proof_reconstruct] def reconstructPropProof : ProofReconstructor := fun pf => do match pf.getRule with
  | .DSL_REWRITE => reconstructRewrite pf
  | .ITE_EQ =>
    let (u, (α : Q(Sort u))) ← reconstructSortLevelAndSort pf.getArguments[0]![1]!.getSort!
    let c : Q(Bool) ← reconstructTerm pf.getArguments[0]![0]!
    let x : Q($α) ← reconstructTerm pf.getArguments[0]![1]!
    let y : Q($α) ← reconstructTerm pf.getArguments[0]![2]!
    let h₁ : Q(Decidable (cond $c $x $y = $x)) ← mkDecidableInst q(cond $c $x $y = $x)
    let h₂ : Q(Decidable (cond $c $x $y = $y)) ← mkDecidableInst q(cond $c $x $y = $y)
    addThm (← reconstructProofType pf.getResult) q(@Bool.ite_eq $α $c $x $y $h₁ $h₂)
  | .RESOLUTION =>
    let p := pf.getArguments[0]!
    let l := pf.getArguments[1]!
    let c₁ := clausify pf.getChildren[0]!.getResult l
    let c₂ := clausify pf.getChildren[1]!.getResult l
    let hps ← reconstructProof pf.getChildren[0]!
    let hqs ← reconstructProof pf.getChildren[1]!
    addThm (← reconstructProofType pf.getResult) (← reconstructResolution c₁ c₂ p l hps hqs)
  | .CHAIN_RESOLUTION =>
    let cs := pf.getChildren.map (·.getResult)
    let as := pf.getArguments
    let ps ← pf.getChildren.mapM reconstructProof
    addThm (← reconstructProofType pf.getResult) (← reconstructChainResolution cs as ps)
  | .FACTORING =>
    let p : Q(Bool) ← reconstructTerm pf.getChildren[0]!.getResult
    let q : Q(Bool) ← reconstructTerm pf.getResult
    let hp : Q($p = true) ← reconstructProof pf.getChildren[0]!
    let hpq : Q($p = $q) ← Meta.mkFreshExprMVar q($p = $q)
    Meta.AC.rewriteUnnormalizedTop hpq.mvarId!
    addThm q($q = true) q(Bool.eq_resolve' $hp $hpq)
  | .REORDERING =>
    let p : Q(Bool) ← reconstructTerm pf.getChildren[0]!.getResult
    let q : Q(Bool) ← reconstructTerm pf.getResult
    let hp : Q($p = true) ← reconstructProof pf.getChildren[0]!
    let hpq : Q($p = $q) ← Meta.mkFreshExprMVar q($p = $q)
    Meta.AC.rewriteUnnormalizedTop hpq.mvarId!
    addThm q($q = true) q(Bool.eq_resolve' $hp $hpq)
  | .SPLIT =>
    let q : Q(Bool) ← reconstructTerm pf.getArguments[0]!
    addThm (← reconstructProofType pf.getResult) q(Bool.or_not_self $q)
  | .EQ_RESOLVE =>
    let p : Q(Bool) ← reconstructTerm pf.getChildren[0]!.getResult
    let q : Q(Bool) ← reconstructTerm pf.getResult
    let hp : Q($p = true) ← reconstructProof pf.getChildren[0]!
    let hpq : Q($p = $q) ← reconstructEqProof pf.getChildren[1]!
    addThm q($q = true) q(Bool.eq_resolve' $hp $hpq)
  | .MODUS_PONENS =>
    let p : Q(Bool) ← reconstructTerm pf.getChildren[0]!.getResult
    let q : Q(Bool) ← reconstructTerm pf.getResult
    let hp : Q($p = true) ← reconstructProof pf.getChildren[0]!
    let hpq : Q(Bool.smtImp $p $q = true) ← reconstructProof pf.getChildren[1]!
    addThm q($q = true) q(Bool.modus_ponens $hp $hpq)
  | .NOT_NOT_ELIM =>
    let p : Q(Bool) ← reconstructTerm pf.getResult
    let hnnp : Q((!!$p) = true) ← reconstructProof pf.getChildren[0]!
    addThm q($p = true) q(Bool.not_not_elim $hnnp)
  | .CONTRA =>
    let p : Q(Bool) ← reconstructTerm pf.getChildren[0]!.getResult
    let hp : Q($p = true) ← reconstructProof pf.getChildren[0]!
    let hnp : Q((!$p) = true) ← reconstructProof pf.getChildren[1]!
    addThm q(false = true) q(Bool.contradiction $hp $hnp)
  | .AND_ELIM =>
    let ps : Q(List Bool) ← reconstructBools (nary .AND pf.getChildren[0]!.getResult)
    let i : Nat := pf.getArguments[0]!.getIntegerValue!.toNat
    let hi : Q($i < «$ps».length) ← Meta.mkDecideProof q($i < «$ps».length)
    let hps : Q(Bool.andN $ps = true) ← reconstructProof pf.getChildren[0]!
    addThm (← reconstructProofType pf.getResult) q(Bool.and_elim $hps $i $hi)
  | .AND_INTRO =>
    let cpfs := pf.getChildren
    let q : Q(Bool) ← reconstructTerm cpfs.back!.getResult
    let hq : Q($q = true) ← reconstructProof cpfs.back!
    let f := fun pf ⟨q, hq⟩ => do
      let p : Q(Bool) ← reconstructTerm pf.getResult
      let hp : Q($p = true) ← reconstructProof pf
      return ⟨q($p && $q), q(Bool.and_intro $hp $hq)⟩
    let ⟨q, hq⟩ ← cpfs.pop.foldrM f (⟨q, hq⟩ : Σ q : Q(Bool), Q($q = true))
    addThm q($q = true) hq
  | .NOT_OR_ELIM =>
    let ps : Q(List Bool) ← reconstructBools (nary .OR pf.getChildren[0]!.getResult[0]!)
    let i : Nat := pf.getArguments[0]!.getIntegerValue!.toNat
    let hi : Q($i < «$ps».length) ← Meta.mkDecideProof q($i < «$ps».length)
    let hnps : Q((!Bool.orN $ps) = true) ← reconstructProof pf.getChildren[0]!
    addThm (← reconstructProofType pf.getResult) q(Bool.not_or_elim $hnps $i $hi)
  | .IMPLIES_ELIM =>
    let p : Q(Bool) ← reconstructTerm pf.getChildren[0]!.getResult[0]!
    let q : Q(Bool) ← reconstructTerm pf.getChildren[0]!.getResult[1]!
    let hpq : Q(Bool.smtImp $p $q = true) ← reconstructProof pf.getChildren[0]!
    addThm (← reconstructProofType pf.getResult) q(Bool.implies_elim $hpq)
  | .NOT_IMPLIES_ELIM1 =>
    let p : Q(Bool) ← reconstructTerm pf.getResult
    let q : Q(Bool) ← reconstructTerm pf.getChildren[0]!.getResult[0]![1]!
    let hnpq : Q((!Bool.smtImp $p $q) = true) ← reconstructProof pf.getChildren[0]!
    addThm q($p = true) q(Bool.not_implies_elim1 $hnpq)
  | .NOT_IMPLIES_ELIM2 =>
    let p : Q(Bool) ← reconstructTerm pf.getChildren[0]!.getResult[0]![0]!
    let q : Q(Bool) ← reconstructTerm pf.getResult[0]!
    let hnpq : Q((!Bool.smtImp $p $q) = true) ← reconstructProof pf.getChildren[0]!
    addThm (← reconstructProofType pf.getResult) q(Bool.not_implies_elim2 $hnpq)
  | .EQUIV_ELIM1 =>
    let p : Q(Bool) ← reconstructTerm pf.getResult[0]![0]!
    let q : Q(Bool) ← reconstructTerm pf.getResult[1]!
    let hpq : Q(decide ($p = $q) = true) ← reconstructProof pf.getChildren[0]!
    addThm (← reconstructProofType pf.getResult) q(Bool.equiv_elim1 $hpq)
  | .EQUIV_ELIM2 =>
    let p : Q(Bool) ← reconstructTerm pf.getResult[0]!
    let q : Q(Bool) ← reconstructTerm pf.getResult[1]![0]!
    let hpq : Q(decide ($p = $q) = true) ← reconstructProof pf.getChildren[0]!
    addThm (← reconstructProofType pf.getResult) q(Bool.equiv_elim2 $hpq)
  | .NOT_EQUIV_ELIM1 =>
    let p : Q(Bool) ← reconstructTerm pf.getResult[0]!
    let q : Q(Bool) ← reconstructTerm pf.getResult[1]!
    let hnpq : Q((!decide ($p = $q)) = true) ← reconstructProof pf.getChildren[0]!
    addThm (← reconstructProofType pf.getResult) q(Bool.not_equiv_elim1 $hnpq)
  | .NOT_EQUIV_ELIM2 =>
    let p : Q(Bool) ← reconstructTerm pf.getResult[0]![0]!
    let q : Q(Bool) ← reconstructTerm pf.getResult[1]![0]!
    let hnpq : Q((!decide ($p = $q)) = true) ← reconstructProof pf.getChildren[0]!
    addThm (← reconstructProofType pf.getResult) q(Bool.not_equiv_elim2 $hnpq)
  | .XOR_ELIM1 =>
    let p : Q(Bool) ← reconstructTerm pf.getResult[0]!
    let q : Q(Bool) ← reconstructTerm pf.getResult[1]!
    let hpq : Q(xor $p $q = true) ← reconstructProof pf.getChildren[0]!
    addThm (← reconstructProofType pf.getResult) q(Bool.xor_elim1 $hpq)
  | .XOR_ELIM2 =>
    let p : Q(Bool) ← reconstructTerm pf.getResult[0]![0]!
    let q : Q(Bool) ← reconstructTerm pf.getResult[1]![0]!
    let hpq : Q(xor $p $q = true) ← reconstructProof pf.getChildren[0]!
    addThm (← reconstructProofType pf.getResult) q(Bool.xor_elim2 $hpq)
  | .NOT_XOR_ELIM1 =>
    let p : Q(Bool) ← reconstructTerm pf.getResult[0]!
    let q : Q(Bool) ← reconstructTerm pf.getResult[1]![0]!
    let hnpq : Q((!xor $p $q) = true) ← reconstructProof pf.getChildren[0]!
    addThm (← reconstructProofType pf.getResult) q(Bool.not_xor_elim1 $hnpq)
  | .NOT_XOR_ELIM2 =>
    let p : Q(Bool) ← reconstructTerm pf.getResult[0]![0]!
    let q : Q(Bool) ← reconstructTerm pf.getResult[1]!
    let hnpq : Q((!xor $p $q) = true) ← reconstructProof pf.getChildren[0]!
    addThm (← reconstructProofType pf.getResult) q(Bool.not_xor_elim2 $hnpq)
  | .NOT_AND =>
    let ps : Q(List Bool) ← reconstructBools pf.getChildren[0]!.getResult[0]!.getChildren
    let hnps : Q((!Bool.andN $ps) = true) ← reconstructProof pf.getChildren[0]!
    addThm (← reconstructProofType pf.getResult) q(Bool.not_and $hnps)
  | .CNF_AND_POS =>
    let ps : Q(List Bool) ← reconstructBools pf.getArguments[0]!.getChildren
    let i : Nat := pf.getArguments[1]!.getIntegerValue!.toNat
    addThm (← reconstructProofType pf.getResult) q(Bool.cnf_and_pos $ps $i)
  | .CNF_AND_NEG =>
    let ps : Q(List Bool) ← reconstructBools pf.getArguments[0]!.getChildren
    addThm (← reconstructProofType pf.getResult) q(Bool.cnf_and_neg $ps)
  | .CNF_OR_POS =>
    let ps : Q(List Bool) ← reconstructBools pf.getArguments[0]!.getChildren
    addThm (← reconstructProofType pf.getResult) q(Bool.cnf_or_pos $ps)
  | .CNF_OR_NEG =>
    let ps : Q(List Bool) ← reconstructBools pf.getArguments[0]!.getChildren
    let i : Nat := pf.getArguments[1]!.getIntegerValue!.toNat
    addThm (← reconstructProofType pf.getResult) q(Bool.cnf_or_neg $ps $i)
  | .CNF_IMPLIES_POS =>
    let p : Q(Bool) ← reconstructTerm pf.getArguments[0]![0]!
    let q : Q(Bool) ← reconstructTerm pf.getArguments[0]![1]!
    addThm (← reconstructProofType pf.getResult) q(Bool.cnf_implies_pos $p $q)
  | .CNF_IMPLIES_NEG1 =>
    let p : Q(Bool) ← reconstructTerm pf.getArguments[0]![0]!
    let q : Q(Bool) ← reconstructTerm pf.getArguments[0]![1]!
    addThm (← reconstructProofType pf.getResult) q(Bool.cnf_implies_neg1 $p $q)
  | .CNF_IMPLIES_NEG2 =>
    let p : Q(Bool) ← reconstructTerm pf.getArguments[0]![0]!
    let q : Q(Bool) ← reconstructTerm pf.getArguments[0]![1]!
    addThm (← reconstructProofType pf.getResult) q(Bool.cnf_implies_neg2 $p $q)
  | .CNF_EQUIV_POS1 =>
    let p : Q(Bool) ← reconstructTerm pf.getArguments[0]![0]!
    let q : Q(Bool) ← reconstructTerm pf.getArguments[0]![1]!
    addThm (← reconstructProofType pf.getResult) q(Bool.cnf_equiv_pos1 $p $q)
  | .CNF_EQUIV_POS2 =>
    let p : Q(Bool) ← reconstructTerm pf.getArguments[0]![0]!
    let q : Q(Bool) ← reconstructTerm pf.getArguments[0]![1]!
    addThm (← reconstructProofType pf.getResult) q(Bool.cnf_equiv_pos2 $p $q)
  | .CNF_EQUIV_NEG1 =>
    let p : Q(Bool) ← reconstructTerm pf.getArguments[0]![0]!
    let q : Q(Bool) ← reconstructTerm pf.getArguments[0]![1]!
    addThm (← reconstructProofType pf.getResult) q(Bool.cnf_equiv_neg1 $p $q)
  | .CNF_EQUIV_NEG2 =>
    let p : Q(Bool) ← reconstructTerm pf.getArguments[0]![0]!
    let q : Q(Bool) ← reconstructTerm pf.getArguments[0]![1]!
    addThm (← reconstructProofType pf.getResult) q(Bool.cnf_equiv_neg2 $p $q)
  | .CNF_XOR_POS1 =>
    let p : Q(Bool) ← reconstructTerm pf.getArguments[0]![0]!
    let q : Q(Bool) ← reconstructTerm pf.getArguments[0]![1]!
    addThm (← reconstructProofType pf.getResult) q(Bool.cnf_xor_pos1 $p $q)
  | .CNF_XOR_POS2 =>
    let p : Q(Bool) ← reconstructTerm pf.getArguments[0]![0]!
    let q : Q(Bool) ← reconstructTerm pf.getArguments[0]![1]!
    addThm (← reconstructProofType pf.getResult) q(Bool.cnf_xor_pos2 $p $q)
  | .CNF_XOR_NEG1 =>
    let p : Q(Bool) ← reconstructTerm pf.getArguments[0]![0]!
    let q : Q(Bool) ← reconstructTerm pf.getArguments[0]![1]!
    addThm (← reconstructProofType pf.getResult) q(Bool.cnf_xor_neg1 $p $q)
  | .CNF_XOR_NEG2 =>
    let p : Q(Bool) ← reconstructTerm pf.getArguments[0]![0]!
    let q : Q(Bool) ← reconstructTerm pf.getArguments[0]![1]!
    addThm (← reconstructProofType pf.getResult) q(Bool.cnf_xor_neg2 $p $q)
  | .TRUE_INTRO =>
    let p : Q(Bool) ← reconstructTerm pf.getResult[0]!
    let hp : Q($p = true) ← reconstructProof pf.getChildren[0]!
    addThm (← reconstructProofType pf.getResult) q(Bool.true_intro $hp)
  | .TRUE_ELIM =>
    let p : Q(Bool) ← reconstructTerm pf.getResult
    let hp : Q(decide ($p = true) = true) ← reconstructProof pf.getChildren[0]!
    addThm q($p = true) q(Bool.true_elim $hp)
  | .FALSE_INTRO =>
    let p : Q(Bool) ← reconstructTerm pf.getResult[0]!
    let hnp : Q((!$p) = true) ← reconstructProof pf.getChildren[0]!
    addThm (← reconstructProofType pf.getResult) q(Bool.false_intro $hnp)
  | .FALSE_ELIM =>
    let p : Q(Bool) ← reconstructTerm pf.getResult[0]!
    let hnp : Q(decide ($p = false) = true) ← reconstructProof pf.getChildren[0]!
    addThm (← reconstructProofType pf.getResult) q(Bool.false_elim $hnp)
  | _ => return none

end Smt.Reconstruct.Prop
