/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed, Tomaz Gomes Mascarenhas
-/

module

public import Smt.Reconstruct
public meta import Smt.Reconstruct
public import Smt.Reconstruct.Bool.Rewrites
public meta import Smt.Reconstruct.Bool.Rewrites
public import Smt.Reconstruct.Real.Lemmas
public meta import Smt.Reconstruct.Real.Lemmas
public import Smt.Reconstruct.Real.Polynorm
public meta import Smt.Reconstruct.Real.Polynorm
public import Smt.Reconstruct.Real.Rewrites
public meta import Smt.Reconstruct.Real.Rewrites
public import Smt.Reconstruct.Real.TransFns
public meta import Smt.Reconstruct.Real.TransFns
public import Smt.Reconstruct.Rewrite
public meta import Smt.Reconstruct.Rewrite

public meta section

namespace Smt.Reconstruct.Real

open Lean Qq

@[smt_sort_reconstruct] def reconstructRealSort : SortReconstructor := fun s => do match s.getKind! with
  | .REAL_SORT => return q(Real)
  | _          => return none

@[smt_term_reconstruct] def reconstructReal : TermReconstructor := fun t => do match t.getKind! with
  | .SKOLEM => match t.getSkolemId! with
    | .DIV_BY_ZERO => return q(fun (x : Real) => x / 0)
    | .TRANSCENDENTAL_PURIFY_ARG =>
      let .app _ x ← reconstructTerm t.getSkolemIndices![0]! | return none
      let x : Q(Real) := x
      let s : Q(Real) := q(Classical.epsilon (TransFns.shift_prop_part $x))
      let y : Q(Real) := q(Classical.epsilon (TransFns.shift_prop $x $s))
      return y
    | .TRANSCENDENTAL_SINE_PHASE_SHIFT =>
      let X : Q(Real) ← reconstructTerm t.getSkolemIndices![0]!
      let s : Q(Real) := q(Classical.epsilon (TransFns.shift_prop_part $X))
      return s
    | _ => return none
  | .CONST_RATIONAL =>
    let c : Rat := t.getRationalValue!
    let num : Q(Real) := mkRealLit c.num.natAbs
    if c.den == 1 then
      if c.num ≥ 0 then
        return q($num)
      else
        return q(-$num)
    else
      let den : Q(Real) := mkRealLit c.den
      if c.num ≥ 0 then
        return q($num / $den)
      else
        return q(-$num / $den)
  | .NEG =>
    if t.getSort!.isInteger then return none
    let x : Q(Real) ← reconstructTerm t[0]!
    return q(-$x)
  | .SUB =>
    if t.getSort!.isInteger then return none
    leftAssocOp q(@HSub.hSub Real Real Real _) t
  | .ADD =>
    if t.getSort!.isInteger then return none
    leftAssocOp q(@HAdd.hAdd Real Real Real _) t
  | .MULT =>
    if t.getSort!.isInteger then return none
    leftAssocOp q(@HMul.hMul Real Real Real _) t
  | .DIVISION =>
    leftAssocOp q(@HDiv.hDiv Real Real Real _) t
  | .DIVISION_TOTAL =>
    leftAssocOp q(@HDiv.hDiv Real Real Real _) t
  | .ABS =>
    if t.getSort!.isInteger then return none
    let x : Q(Real) ← reconstructTerm t[0]!
    return q(|$x|)
  | .LEQ =>
    if t[0]!.getSort!.isInteger then return none
    let x : Q(Real) ← reconstructTerm t[0]!
    let y : Q(Real) ← reconstructTerm t[1]!
    return q(Real.ble $x $y)
  | .LT =>
    if t[0]!.getSort!.isInteger then return none
    let x : Q(Real) ← reconstructTerm t[0]!
    let y : Q(Real) ← reconstructTerm t[1]!
    return q(Real.blt $x $y)
  | .GEQ =>
    if t[0]!.getSort!.isInteger then return none
    let x : Q(Real) ← reconstructTerm t[0]!
    let y : Q(Real) ← reconstructTerm t[1]!
    return q(Real.bge $x $y)
  | .GT =>
    if t[0]!.getSort!.isInteger then return none
    let x : Q(Real) ← reconstructTerm t[0]!
    let y : Q(Real) ← reconstructTerm t[1]!
    return q(Real.bgt $x $y)
  | .TO_REAL =>
    let x : Q(Int) ← reconstructTerm t[0]!
    return q($x : Real)
  | .TO_INTEGER =>
    let x : Q(Real) ← reconstructTerm t[0]!
    return q(⌊$x⌋)
  | .IS_INTEGER =>
    let x : Q(Real) ← reconstructTerm t[0]!
    Bool.mkDecideEq q(Real) x q((⌊$x⌋ : Real))
  | .EXPONENTIAL =>
    if t.getSort!.isInteger then return none
    let x : Q(Real) ← reconstructTerm t[0]!
    return q(Real.exp $x)
  | .SINE =>
    if t.getSort!.isInteger then return none
    let x : Q(Real) ← reconstructTerm t[0]!
    return q(Real.sin $x)
  | .COSINE =>
    if t.getSort!.isInteger then return none
    let x : Q(Real) ← reconstructTerm t[0]!
    return q(Real.cos $x)
  | .TANGENT =>
    if t.getSort!.isInteger then return none
    let x : Q(Real) ← reconstructTerm t[0]!
    return q(Real.tan $x)
  | .COTANGENT =>
    if t.getSort!.isInteger then return none
    let x : Q(Real) ← reconstructTerm t[0]!
    return q(Real.cot $x)
  | .PI => return q(Real.pi)
  | _ => return none
where
  mkRealLit (n : Nat) : Q(Real) := match n with
    | 0     => q(0 : Real)
    | 1     => q(1 : Real)
    | n' + 1 + 1 =>
      let h : Q(Nat.AtLeastTwo $n) := mkApp2 q(@Nat.instAtLeastTwoHAddOfNat) (toExpr (n' + 1)) q(@Nat.instNeZeroSucc $n')
      let h := mkApp3 q(@instOfNatAtLeastTwo Real) (mkRawNatLit n) q(Real.instNatCast) h
      mkApp2 q(@OfNat.ofNat Real) (mkRawNatLit n) h
  leftAssocOp (op : Expr) (t : cvc5.Term) : ReconstructM Expr := do
    let mut curr ← reconstructTerm t[0]!
    for i in [1:t.getNumChildren] do
      curr := mkApp2 op curr (← reconstructTerm t[i]!)
    return curr

def reconstructRewrite (pf : cvc5.Proof) : ReconstructM (Option Expr) := do
  match pf.getRewriteRule! with
  | .ARITH_POW_ELIM =>
    if (pf.getResult[0]!)[0]!.getSort!.isInteger then return none
    let x : Q(Real) ← reconstructTerm (pf.getResult[0]!)[0]!
    let c : Nat := (pf.getResult[0]!)[1]!.getIntegerValue!.toNat
    let y : Q(Real) ← reconstructTerm pf.getResult[1]!
    let mut h : Q($x ^ $c = $y) := .app q(@Eq.refl Real) y
    if c > 0 then
      let qPow : Q(Real) := c.repeat (fun acc => q($acc * $x)) (.bvar 0)
      let p : Q(Real → Prop) := .lam `x q(Real) q($qPow = $y) .default
      h := .app q(Eq.subst (motive := $p) (one_mul $x).symm) h
    addEqThm pf.getResult h
  | .ARITH_DIV_TOTAL_ZERO_REAL =>
    let x : Q(Real) ← reconstructTerm pf.getArguments[1]!
    addEqThm pf.getResult q(@Rewrite.div_total_zero $x)
  | .ARITH_ELIM_GT =>
    if pf.getArguments[1]!.getSort!.isInteger then return none
    let t : Q(Real) ← reconstructTerm pf.getArguments[1]!
    let s : Q(Real) ← reconstructTerm pf.getArguments[2]!
    addEqThm pf.getResult q(@Rewrite.elim_gt $t $s)
  | .ARITH_ELIM_LT =>
    if pf.getArguments[1]!.getSort!.isInteger then return none
    let t : Q(Real) ← reconstructTerm pf.getArguments[1]!
    let s : Q(Real) ← reconstructTerm pf.getArguments[2]!
    addEqThm pf.getResult q(@Rewrite.elim_lt $t $s)
  | .ARITH_ELIM_LEQ =>
    if pf.getArguments[1]!.getSort!.isInteger then return none
    let t : Q(Real) ← reconstructTerm pf.getArguments[1]!
    let s : Q(Real) ← reconstructTerm pf.getArguments[2]!
    addEqThm pf.getResult q(@Rewrite.elim_leq $t $s)
  | .ARITH_GEQ_NORM1_REAL =>
    let t : Q(Real) ← reconstructTerm pf.getArguments[1]!
    let s : Q(Real) ← reconstructTerm pf.getArguments[2]!
    addEqThm pf.getResult q(@Rewrite.geq_norm1 $t $s)
  | .ARITH_EQ_ELIM_REAL =>
    let t : Q(Real) ← reconstructTerm pf.getArguments[1]!
    let s : Q(Real) ← reconstructTerm pf.getArguments[2]!
    addEqThm pf.getResult q(@Rewrite.eq_elim $t $s)
  | .ARITH_INT_EQ_CONFLICT =>
    let t : Q(Int) ← reconstructTerm pf.getArguments[1]!
    let c : Q(Real) ← reconstructTerm pf.getArguments[2]!
    let h : Q(decide ((⌊$c⌋ : Real) = $c) = false) ← reconstructEqProof pf.getChildren[0]!
    addEqThm pf.getResult q(@Rewrite.eq_conflict $t $c $h)
  | .ARITH_INT_GEQ_TIGHTEN =>
    let t : Q(Int) ← reconstructTerm pf.getArguments[1]!
    let c : Q(Real) ← reconstructTerm pf.getArguments[2]!
    let cc : Q(Int) ← reconstructTerm pf.getArguments[3]!
    let hc : Q(decide ((⌊$c⌋ : Real) = $c) = false) ← reconstructEqProof pf.getChildren[0]!
    let hcc : Q($cc = ⌊$c⌋ + 1) ← reconstructEqProof pf.getChildren[1]!
    addEqThm pf.getResult q(@Rewrite.geq_tighten $t $c $cc $hc $hcc)
  | .ARITH_ABS_EQ =>
    if pf.getArguments[1]!.getSort!.isInteger then return none
    let x : Q(Real) ← reconstructTerm pf.getArguments[1]!
    let y : Q(Real) ← reconstructTerm pf.getArguments[2]!
    addEqThm pf.getResult q(@Rewrite.abs_eq $x $y)
  | .ARITH_ABS_REAL_GT =>
    let x : Q(Real) ← reconstructTerm pf.getArguments[1]!
    let y : Q(Real) ← reconstructTerm pf.getArguments[2]!
    addEqThm pf.getResult q(@Rewrite.abs_gt $x $y)
  | .ARITH_GEQ_ITE_LIFT =>
    if pf.getArguments[2]!.getSort!.isInteger then return none
    let c : Q(Bool) ← reconstructTerm pf.getArguments[1]!
    let t : Q(Real) ← reconstructTerm pf.getArguments[2]!
    let s : Q(Real) ← reconstructTerm pf.getArguments[3]!
    let r : Q(Real) ← reconstructTerm pf.getArguments[4]!
    addEqThm pf.getResult q(@Rewrite.geq_ite_lift $c $t $s $r)
  | .ARITH_LEQ_ITE_LIFT =>
    if pf.getArguments[2]!.getSort!.isInteger then return none
    let c : Q(Bool) ← reconstructTerm pf.getArguments[1]!
    let t : Q(Real) ← reconstructTerm pf.getArguments[2]!
    let s : Q(Real) ← reconstructTerm pf.getArguments[3]!
    let r : Q(Real) ← reconstructTerm pf.getArguments[4]!
    addEqThm pf.getResult q(@Rewrite.leq_ite_lift $c $t $s $r)
  | .ARITH_MIN_LT1 =>
    if pf.getArguments[1]!.getSort!.isInteger then return none
    let t : Q(Real) ← reconstructTerm pf.getArguments[1]!
    let s : Q(Real) ← reconstructTerm pf.getArguments[2]!
    addEqThm pf.getResult q(@Rewrite.min_lt1 $t $s)
  | .ARITH_MIN_LT2 =>
    if pf.getArguments[1]!.getSort!.isInteger then return none
    let t : Q(Real) ← reconstructTerm pf.getArguments[1]!
    let s : Q(Real) ← reconstructTerm pf.getArguments[2]!
    addEqThm pf.getResult q(@Rewrite.min_lt2 $t $s)
  | .ARITH_MAX_GEQ1 =>
    if pf.getArguments[1]!.getSort!.isInteger then return none
    let t : Q(Real) ← reconstructTerm pf.getArguments[1]!
    let s : Q(Real) ← reconstructTerm pf.getArguments[2]!
    addEqThm pf.getResult q(@Rewrite.max_geq1 $t $s)
  | .ARITH_MAX_GEQ2 =>
    if pf.getArguments[1]!.getSort!.isInteger then return none
    let t : Q(Real) ← reconstructTerm pf.getArguments[1]!
    let s : Q(Real) ← reconstructTerm pf.getArguments[2]!
    addEqThm pf.getResult q(@Rewrite.max_geq2 $t $s)
  | .ARITH_SINE_ZERO =>
    addEqThm pf.getResult q(Rewrite.arith_sine_zero)
  | .ARITH_SINE_PI2 =>
    addEqThm pf.getResult q(Rewrite.arith_sine_pi2)
  | .ARITH_COSINE_ELIM =>
    if pf.getArguments[1]!.getSort!.isInteger then return none
    let t : Q(Real) ← reconstructTerm pf.getArguments[1]!
    addEqThm pf.getResult q(Rewrite.arith_cosine_elim $t)
  | .ARITH_TANGENT_ELIM =>
    if pf.getArguments[1]!.getSort!.isInteger then return none
    let t : Q(Real) ← reconstructTerm pf.getArguments[1]!
    addEqThm pf.getResult q(Rewrite.arith_tangent_elim $t)
  | .ARITH_COTANGENT_ELIM =>
    if pf.getArguments[1]!.getSort!.isInteger then return none
    let t : Q(Real) ← reconstructTerm pf.getArguments[1]!
    addEqThm pf.getResult q(Rewrite.arith_cotangent_elim $t)
  | _ => return none

def reconstructSumUB (pf : cvc5.Proof) : ReconstructM (Option Expr) := do
  let f := fun (ks, ls, rs, hs) p => do
    let l : Q(Real) ← reconstructTerm p.getResult[0]!
    let r : Q(Real) ← reconstructTerm p.getResult[1]!
    let lsl := q($ls + $l)
    let rsr := q($rs + $r)
    let k := p.getResult.getKind!
    if ks == .LT && k == .LT then
      let hs : Q(Real.blt $ls $rs = true) := hs
      let h : Q(Real.blt $l $r = true) ← reconstructProof p
      return (.LT, lsl, rsr, q(Real.sum_ub₁ $hs $h))
    else if ks == .LT && k == .LEQ then
      let hs : Q(Real.blt $ls $rs = true) := hs
      let h : Q(Real.ble $l $r = true) ← reconstructProof p
      return (.LT, lsl, rsr, q(Real.sum_ub₂ $hs $h))
    else if ks == .LT && k == .EQUAL then
      let hs : Q(Real.blt $ls $rs = true) := hs
      let h : Q($l = $r) ← reconstructEqProof p
      return (.LT, lsl, rsr, q(Real.sum_ub₃ $hs $h))
    else if ks == .LEQ && k == .LT then
      let hs : Q(Real.ble $ls $rs = true) := hs
      let h : Q(Real.blt $l $r = true) ← reconstructProof p
      return (.LT, lsl, rsr, q(Real.sum_ub₄ $hs $h))
    else if ks == .LEQ && k == .LEQ then
      let hs : Q(Real.ble $ls $rs = true) := hs
      let h : Q(Real.ble $l $r = true) ← reconstructProof p
      return (.LEQ, lsl, rsr, q(Real.sum_ub₅ $hs $h))
    else if ks == .LEQ && k == .EQUAL then
      let hs : Q(Real.ble $ls $rs = true) := hs
      let h : Q($l = $r) ← reconstructEqProof p
      return (.LEQ, lsl, rsr, q(Real.sum_ub₆ $hs $h))
    else if ks == .EQUAL && k == .LT then
      let hs : Q($ls = $rs) := hs
      let h : Q(Real.blt $l $r = true) ← reconstructProof p
      return (.LT, lsl, rsr, q(Real.sum_ub₇ $hs $h))
    else if ks == .EQUAL && k == .LEQ then
      let hs : Q($ls = $rs) := hs
      let h : Q(Real.ble $l $r = true) ← reconstructProof p
      return (.LEQ, lsl, rsr, q(Real.sum_ub₈ $hs $h))
    else if ks == .EQUAL && k == .EQUAL then
      let hs : Q($ls = $rs) := hs
      let h : Q($l = $r) ← reconstructEqProof p
      return (.EQUAL, lsl, rsr, q(Real.sum_ub₉ $hs $h))
    else
      throwError "[sum_ub]: invalid kinds: {ks}, {k}"
  let k := pf.getChildren[0]!.getResult.getKind!
  let ls : Q(Real) ← reconstructTerm pf.getChildren[0]!.getResult[0]!
  let rs : Q(Real) ← reconstructTerm pf.getChildren[0]!.getResult[1]!
  let hs ← reconstructRelProof pf.getChildren[0]!
  let (ks, ls, rs, hs) ← pf.getChildren[1:].foldlM f (k, ls, rs, hs)
  if ks == .EQUAL then
    let hs : Q($ls = $rs) := hs
    addThm (← reconstructProofType pf.getResult) q(Real.ble_of_eq $hs)
  else
    addThm (← reconstructProofType pf.getResult) hs

def reconstructMulAbsComparison (pf : cvc5.Proof) : ReconstructM (Option Expr) := do
  let f := fun (ks, ls, rs, hs) p => do
    let k := p.getResult.getKind!
    if ks == .EQUAL && k == .EQUAL then
      let l : Q(Real) ← reconstructTerm (p.getResult[0]!)[0]!
      let r : Q(Real) ← reconstructTerm (p.getResult[1]!)[0]!
      let hs : Q(|$ls| = |$rs|) := hs
      let h : Q(|$l| = |$r|) ← reconstructEqProof p
      return (.EQUAL, q($ls * $l), q($rs * $r), q(Real.mul_abs₁ $hs $h))
    else if ks == .GT && k == .AND then
      let l : Q(Real) ← reconstructTerm ((p.getResult[0]!)[0]!)[0]!
      let r : Q(Real) ← reconstructTerm ((p.getResult[0]!)[1]!)[0]!
      let hs : Q(Real.bgt |$ls| |$rs| = true) := hs
      let h ← reconstructProof p
      return (.GT, q($ls * $l), q($rs * $r), mkApp6 (.const ``Real.mul_abs₂ []) ls l rs r hs h)
    else if ks == .GT && k == .GT then
      let l : Q(Real) ← reconstructTerm (p.getResult[0]!)[0]!
      let r : Q(Real) ← reconstructTerm (p.getResult[1]!)[0]!
      let hs : Q(Real.bgt |$ls| |$rs| = true) := hs
      let h : Q(Real.bgt |$l| |$r| = true) ← reconstructProof p
      return (.GT, q($ls * $l), q($rs * $r), q(Real.mul_abs₃ $hs $h))
    else
      throwError "[mul_abs]: invalid kinds: {ks}, {k}"
  let k := pf.getChildren[0]!.getResult.getKind!
  let ls : Q(Real) ← reconstructTerm (pf.getChildren[0]!.getResult[0]!)[0]!
  let rs : Q(Real) ← reconstructTerm (pf.getChildren[0]!.getResult[1]!)[0]!
  let hs ← reconstructRelProof pf.getChildren[0]!
  let (ks, _, _, hs) ← pf.getChildren[1:].foldlM f (k, ls, rs, hs)
  if ks == .EQUAL then
    addEqThm pf.getResult hs
  else
    addThm (← reconstructProofType pf.getResult) hs

def reconstructMulSign (pf : cvc5.Proof) : ReconstructM (Option Expr) := do
  let ts := if pf.getResult[0]!.getKind! == .AND then pf.getResult[0]!.getChildren else #[pf.getResult[0]!]
  let mut hs : Array (Name × (Array Expr → ReconstructM Expr)) := #[]
  let mut map : Std.HashMap cvc5.Term Nat := {}
  for h : i in [0:ts.size] do
    let t := ts[i]
    let p ← reconstructProofType t
    hs := hs.push (Name.num `a i, fun _ => return p)
    map := map.insert (if t.getKind! == .NOT then (t[0]!)[0]! else t[0]!) i
  let t := pf.getResult[1]!
  let vs := if t[0]!.getKind! == .CONST_INTEGER then t[1]!.getChildren else t[0]!.getChildren
  let ps : Q(List Bool) ← reconstructTerms ts
  let q : Q(Bool) ← reconstructTerm t
  let h : Q(Bool.impliesN $ps ($q = true)) ← Meta.withLocalDeclsD hs fun hs => do
    let h : Q($q = true) ← if ts[map[vs[0]!]!]!.getKind! == .NOT then
        let a : Q(Real) ← reconstructTerm vs[0]!
        let ha := hs[map[vs[0]!]!]!
        go vs ts hs map .GT q($a * $a) (mkApp2 (.const ``Real.mul_sign₀ []) a ha) 2
      else
        let a : Q(Real) ← reconstructTerm vs[0]!
        go vs ts hs map ts[map[vs[0]!]!]!.getKind! a hs[map[vs[0]!]!]! 1
    Meta.mkLambdaFVars hs h
  addThm (← reconstructProofType pf.getResult) q(Bool.scopes $h)
where
  go vs ts hs map (ka : cvc5.Kind) (a : Q(Real)) (ha : Expr) i : ReconstructM Expr := do
    if hi : i < vs.size then
      let b : Q(Real) ← reconstructTerm vs[i]
      let k : cvc5.Kind := ts[map[vs[i]]!]!.getKind!
      let hb := hs[map[vs[i]]!]!
      if ka == .LT && k == .LT then
        go vs ts hs map .GT q($a * $b) (mkApp4 (.const ``Real.mul_sign₁ []) a b ha hb) (i + 1)
      else if ka == .LT && k == .NOT then
        go vs ts hs map .LT q($a * $b * $b) (mkApp4 (.const ``Real.mul_sign₂ []) a b ha hb) (i + 2)
      else if ka == .LT && k == .GT then
        go vs ts hs map .LT q($a * $b) (mkApp4 (.const ``Real.mul_sign₃ []) a b ha hb) (i + 1)
      else if ka == .GT && k == .LT then
        go vs ts hs map .LT q($a * $b) (mkApp4 (.const ``Real.mul_sign₄ []) a b ha hb) (i + 1)
      else if ka == .GT && k == .NOT then
        go vs ts hs map .GT q($a * $b * $b) (mkApp4 (.const ``Real.mul_sign₅ []) a b ha hb) (i + 2)
      else if ka == .GT && k == .GT then
        go vs ts hs map .GT q($a * $b) (mkApp4 (.const ``Real.mul_sign₆ []) a b ha hb) (i + 1)
      else
        throwError "[mul_sign]: invalid kinds: {ka}, {k}"
    else
      return ha

def reconstructArithPolyNormRel (pf : cvc5.Proof) : ReconstructM (Option Expr) := do
  let lcx : Rat := (pf.getChildren[0]!.getResult[0]!)[0]!.getRationalValue!
  let cx : Q(Real) ← reconstructTerm (pf.getChildren[0]!.getResult[0]!)[0]!
  let cy : Q(Real) ← reconstructTerm (pf.getChildren[0]!.getResult[1]!)[0]!
  let x₁ : Q(Real) ← reconstructTerm (pf.getResult[0]!)[0]!
  let x₂ : Q(Real) ← reconstructTerm (pf.getResult[0]!)[1]!
  let y₁ : Q(Real) ← reconstructTerm (pf.getResult[1]!)[0]!
  let y₂ : Q(Real) ← reconstructTerm (pf.getResult[1]!)[1]!
  let h : Q($cx * ($x₁ - $x₂) = $cy * ($y₁ - $y₂)) ← reconstructEqProof pf.getChildren[0]!
  let k := pf.getResult[0]!.getKind!
  -- The signs of the constants are proved by `norm_num`, since the comparisons of reals are
  -- noncomputable.
  let sign (c : Q(Real)) : MetaM Expr := do
    if k == .EQUAL then
      let h ← Meta.mkFreshExprMVar q($c ≠ 0)
      Real.normNum h.mvarId!
      let h : Q($c ≠ 0) := h
      return q(Real.not_decide_eq_of_ne $h)
    else if lcx > 0 then
      let h ← Meta.mkFreshExprMVar q($c > 0)
      Real.normNum h.mvarId!
      let h : Q($c > 0) := h
      return q(Real.bgt_of_gt $h)
    else
      let h ← Meta.mkFreshExprMVar q($c < 0)
      Real.normNum h.mvarId!
      let h : Q($c < 0) := h
      return q(Real.blt_of_lt $h)
  let hcx ← sign cx
  let hcy ← sign cy
  let n ← getThmName k (pf.getResult[0]!)[0]!.getSort!.isInteger (pf.getResult[1]!)[0]!.getSort!.isInteger (lcx > 0)
  addEqThm pf.getResult (mkApp9 (.const n []) x₁ x₂ y₁ y₂ cx cy hcx hcy h)
where
  getThmName (k : cvc5.Kind) (il ir sign : Bool) : ReconstructM Name :=
    if k == .LT && il == false && ir == false && sign == true then pure ``Real.lt_of_sub_eq_pos
    else if k == .LT && il == false && ir == false && sign == false then pure ``Real.lt_of_sub_eq_neg
    else if k == .LT && il == false && ir == true && sign == true then pure ``Real.lt_of_sub_eq_pos_int_right
    else if k == .LT && il == false && ir == true && sign == false then pure ``Real.lt_of_sub_eq_neg_int_right
    else if k == .LT && il == true && ir == false && sign == true then pure ``Real.lt_of_sub_eq_pos_int_left
    else if k == .LT && il == true && ir == false && sign == false then pure ``Real.lt_of_sub_eq_neg_int_left
    else if k == .LEQ && il == false && ir == false && sign == true then pure ``Real.le_of_sub_eq_pos
    else if k == .LEQ && il == false && ir == false && sign == false then pure ``Real.le_of_sub_eq_neg
    else if k == .LEQ && il == false && ir == true && sign == true then pure ``Real.le_of_sub_eq_pos_int_right
    else if k == .LEQ && il == false && ir == true && sign == false then pure ``Real.le_of_sub_eq_neg_int_right
    else if k == .LEQ && il == true && ir == false && sign == true then pure ``Real.le_of_sub_eq_pos_int_left
    else if k == .LEQ && il == true && ir == false && sign == false then pure ``Real.le_of_sub_eq_neg_int_left
    else if k == .EQUAL && il == false && ir == false then pure ``Real.eq_of_sub_eq
    else if k == .EQUAL && il == false && ir == true then pure ``Real.eq_of_sub_eq_int_right
    else if k == .EQUAL && il == true && ir == false then pure ``Real.eq_of_sub_eq_int_left
    else if k == .GEQ && il == false && ir == false && sign == true then pure ``Real.ge_of_sub_eq_pos
    else if k == .GEQ && il == false && ir == false && sign == false then pure ``Real.ge_of_sub_eq_neg
    else if k == .GEQ && il == false && ir == true && sign == true then pure ``Real.ge_of_sub_eq_pos_int_right
    else if k == .GEQ && il == false && ir == true && sign == false then pure ``Real.ge_of_sub_eq_neg_int_right
    else if k == .GEQ && il == true && ir == false && sign == true then pure ``Real.ge_of_sub_eq_pos_int_left
    else if k == .GEQ && il == true && ir == false && sign == false then pure ``Real.ge_of_sub_eq_neg_int_left
    else if k == .GT && il == false && ir == false && sign == true then pure ``Real.gt_of_sub_eq_pos
    else if k == .GT && il == false && ir == false && sign == false then pure ``Real.gt_of_sub_eq_neg
    else if k == .GT && il == false && ir == true && sign == true then pure ``Real.gt_of_sub_eq_pos_int_right
    else if k == .GT && il == false && ir == true && sign == false then pure ``Real.gt_of_sub_eq_neg_int_right
    else if k == .GT && il == true && ir == false && sign == true then pure ``Real.gt_of_sub_eq_pos_int_left
    else if k == .GT && il == true && ir == false && sign == false then pure ``Real.gt_of_sub_eq_neg_int_left
    else throwError "[arith_poly_norm_rel]: invalid combination of kind, integer operands, and sign: {k}, {il}, {ir}, {sign}"

@[smt_proof_reconstruct] def reconstructRealProof : ProofReconstructor := fun pf => do match pf.getRule with
  | .EVALUATE =>
    -- Computable evaluations are reconstructed by evaluation (see `Smt.Reconstruct.Builtin`).
    if !(← usesNoncomputable (← reconstructTerm pf.getResult)) then
      return none
    addEqTac pf.getResult normNumAbs
  | .DSL_REWRITE
  | .THEORY_REWRITE => reconstructRewrite pf
  | .ARITH_SUM_UB =>
    if pf.getResult[0]!.getSort!.isInteger then return none
    reconstructSumUB pf
  | .ARITH_MULT_ABS_COMPARISON =>
    if pf.getResult[0]!.getSort!.isInteger then return none
    reconstructMulAbsComparison pf
  | .INT_TIGHT_UB =>
    if pf.getChildren[0]!.getResult[1]!.getSort!.isInteger then return none
    let i : Q(Int) ← reconstructTerm pf.getChildren[0]!.getResult[0]!
    let c : Q(Real) ← reconstructTerm pf.getChildren[0]!.getResult[1]!
    let h : Q(Real.blt $i $c = true) ← reconstructProof pf.getChildren[0]!
    addThm (← reconstructProofType pf.getResult) q(@Real.int_tight_ub $c $i $h)
  | .INT_TIGHT_LB =>
    if pf.getChildren[0]!.getResult[1]!.getSort!.isInteger then return none
    let i : Q(Int) ← reconstructTerm pf.getChildren[0]!.getResult[0]!
    let c : Q(Real) ← reconstructTerm pf.getChildren[0]!.getResult[1]!
    let h : Q(Real.bgt $i $c = true) ← reconstructProof pf.getChildren[0]!
    addThm (← reconstructProofType pf.getResult) q(@Real.int_tight_lb $c $i $h)
  | .ARITH_TRICHOTOMY =>
    if pf.getResult[0]!.getSort!.isInteger then return none
    let x : Q(Real) ← reconstructTerm pf.getResult[0]!
    let c : Q(Real) ← reconstructTerm pf.getResult[1]!
    let k₁ := pf.getChildren[0]!.getResult.getKind!
    let k₂ := pf.getChildren[1]!.getResult.getKind!
    let h₁ ← reconstructProof pf.getChildren[0]!
    let h₂ ← reconstructProof pf.getChildren[1]!
    if k₁ == .LEQ && k₂ == .NOT then
      addThm (← reconstructProofType pf.getResult) (mkApp4 (.const ``Real.trichotomy₁ []) x c h₁ h₂)
    else if k₁ == .LEQ && k₂ == .GEQ then
      addEqThm pf.getResult (mkApp4 (.const ``Real.trichotomy₂ []) x c h₁ h₂)
    else if k₁ == .NOT && k₂ == .LEQ then
      addThm (← reconstructProofType pf.getResult) (mkApp4 (.const ``Real.trichotomy₃ []) x c h₁ h₂)
    else if k₁ == .NOT && k₂ == .GEQ then
      addThm (← reconstructProofType pf.getResult) (mkApp4 (.const ``Real.trichotomy₄ []) x c h₁ h₂)
    else if k₁ == .GEQ && k₂ == .LEQ then
      addEqThm pf.getResult (mkApp4 (.const ``Real.trichotomy₅ []) x c h₁ h₂)
    else if k₁ == .GEQ && k₂ == .NOT then
      addThm (← reconstructProofType pf.getResult) (mkApp4 (.const ``Real.trichotomy₆ []) x c h₁ h₂)
    else
      return none
  | .ARITH_REDUCTION =>
    if pf.getArguments[0]!.getSort!.isInteger then return none
    if pf.getArguments[0]!.getKind! == .ABS then
      let x : Q(Real) ← reconstructTerm (pf.getArguments[0]!)[0]!
      addEqThm pf.getResult q(@Real.abs_elim $x)
    else
      return none
  | .ARITH_POLY_NORM =>
    if pf.getResult[0]!.getSort!.isInteger then return none
    let tac := if ← useNative then Real.nativePolyNorm else Real.polyNorm
    addEqTac pf.getResult tac
  | .ARITH_POLY_NORM_REL =>
    if (pf.getChildren[0]!.getResult[0]!)[0]!.getSort!.isInteger then return none
    reconstructArithPolyNormRel pf
  | .ARITH_MULT_SIGN =>
    if (pf.getResult[1]!)[0]!.getSort!.isInteger then return none
    reconstructMulSign pf
  | .ARITH_MULT_POS =>
    if pf.getArguments[0]!.getSort!.isInteger then return none
    let m : Q(Real) ← reconstructTerm pf.getArguments[0]!
    let l : Q(Real) ← reconstructTerm (pf.getArguments[1]!)[0]!
    let r : Q(Real) ← reconstructTerm (pf.getArguments[1]!)[1]!
    let n ← match pf.getArguments[1]!.getKind! with
      | .LT => pure ``Real.mul_pos_lt
      | .LEQ => pure ``Real.mul_pos_le
      | .EQUAL => pure ``Real.mul_pos_eq
      | .GEQ => pure ``Real.mul_pos_ge
      | .GT => pure ``Real.mul_pos_gt
      | _ => return none
    addThm (← reconstructProofType pf.getResult) (mkApp3 (.const n []) l r m)
  | .ARITH_MULT_NEG =>
    if pf.getArguments[0]!.getSort!.isInteger then return none
    let m : Q(Real) ← reconstructTerm pf.getArguments[0]!
    let l : Q(Real) ← reconstructTerm (pf.getArguments[1]!)[0]!
    let r : Q(Real) ← reconstructTerm (pf.getArguments[1]!)[1]!
    let n ← match pf.getArguments[1]!.getKind! with
      | .LT => pure ``Real.mul_neg_lt
      | .LEQ => pure ``Real.mul_neg_le
      | .EQUAL => pure ``Real.mul_neg_eq
      | .GEQ => pure ``Real.mul_neg_ge
      | .GT => pure ``Real.mul_neg_gt
      | _ => return none
    addThm (← reconstructProofType pf.getResult) (mkApp3 (.const n []) l r m)
  | .ARITH_MULT_TANGENT =>
    let x : Q(Real) ← reconstructTerm pf.getArguments[0]!
    let y : Q(Real) ← reconstructTerm pf.getArguments[1]!
    let a : Q(Real) ← reconstructTerm pf.getArguments[2]!
    let b : Q(Real) ← reconstructTerm pf.getArguments[3]!
    if pf.getArguments[4]!.getBooleanValue! == false then
      addEqThm pf.getResult q(@Real.mul_tangent_lower_eq $a $b $x $y)
    else
      addEqThm pf.getResult q(@Real.mul_tangent_upper_eq $a $b $x $y)
  | .ARITH_TRANS_PI =>
    -- The conclusion is `(and (>= real.pi l) (<= real.pi u))`.
    let l : Q(Real) ← reconstructTerm (pf.getResult[0]!)[1]!
    let u : Q(Real) ← reconstructTerm (pf.getResult[1]!)[1]!
    let h ← Meta.mkFreshExprMVar q(Real.pi ≥ $l ∧ Real.pi ≤ $u)
    TransFns.arithTransPiTac h.mvarId!
    let h : Q(Real.pi ≥ $l ∧ Real.pi ≤ $u) := h
    addThm (← reconstructProofType pf.getResult) q(TransFns.arithTransPi_of $h)
  | .ARITH_TRANS_EXP_ZERO =>
    let t : Q(Real) ← reconstructTerm pf.getArguments[0]!
    addEqThm pf.getResult q(TransFns.arithTransExpZeroEq $t)
  | .ARITH_TRANS_SINE_SHIFT =>
    let x : Q(Real) ← reconstructTerm pf.getArguments[0]!
    addThm (← reconstructProofType pf.getResult) q(TransFns.arithTransSineShift₁ $x)
  | .ARITH_TRANS_EXP_POSITIVITY =>
    let t : Q(Real) ← reconstructTerm pf.getArguments[0]!
    addThm (← reconstructProofType pf.getResult) q(TransFns.arithTransExpPositivity $t)
  | .ARITH_TRANS_SINE_TANGENT_PI =>
    let t : Q(Real) ← reconstructTerm pf.getArguments[0]!
    addThm (← reconstructProofType pf.getResult) q(TransFns.arithTransSineTangentPi $t)
  | .ARITH_TRANS_SINE_TANGENT_ZERO =>
    let t : Q(Real) ← reconstructTerm pf.getArguments[0]!
    addThm (← reconstructProofType pf.getResult) q(TransFns.arithTransSinTangentZero $t)
  | .ARITH_TRANS_EXP_SUPER_LIN =>
    let t : Q(Real) ← reconstructTerm pf.getArguments[0]!
    addThm (← reconstructProofType pf.getResult) q(TransFns.arithTransExpSuperLin $t)
  | .ARITH_TRANS_EXP_NEG =>
    let t : Q(Real) ← reconstructTerm pf.getArguments[0]!
    addEqThm pf.getResult q(TransFns.arithTransExpNeg' $t)
  | .ARITH_TRANS_SINE_BOUNDS =>
    let t : Q(Real) ← reconstructTerm pf.getArguments[0]!
    addThm (← reconstructProofType pf.getResult) q(TransFns.arithTransSineBounds $t)
  | .ARITH_TRANS_EXP_APPROX_BELOW =>
    let d : Nat := pf.getArguments[0]!.getIntegerValue!.natAbs
    let c : Q(Real) ← reconstructTerm pf.getArguments[1]!
    let t : Q(Real) ← reconstructTerm pf.getArguments[1]!
    let w : Q(Real) ← reconstructTerm (pf.getResult[1]!)[1]! -- rational value of the taylor polynomial

    let poly_deg : Q(Nat) := q((2 : Nat) * $d - 1)
    let goal : Q(Prop) := q(TransFns.expTaylor $poly_deg $c = $w)
    let goal_pf : Q($goal) ← Meta.mkFreshExprMVar (some goal)
    normNumFactorial goal_pf.mvarId!

    let poly_deg_is_odd : Q(Prop) := q($poly_deg = 2 * ($d - 1) + 1)
    let poly_deg_is_odd_pf : Q($poly_deg_is_odd) ← Meta.mkFreshExprMVar (some poly_deg_is_odd)
    Real.normNum poly_deg_is_odd_pf.mvarId!

    let proof := q(TransFns.arithTransExpApproxBelowComp $t $c $w (2 * $d - 1) ($d - 1) $goal_pf $poly_deg_is_odd_pf)
    addThm (← reconstructProofType pf.getResult) proof
  | .ARITH_TRANS_EXP_APPROX_ABOVE_POS =>
    let d : Nat := pf.getArguments[0]!.getIntegerValue!.natAbs
    let t : Q(Real) ← reconstructTerm pf.getArguments[1]!
    let l : Q(Real) ← reconstructTerm pf.getArguments[2]!
    let u : Q(Real) ← reconstructTerm pf.getArguments[3]!
    let eval_l : Q(Real) ← reconstructTerm ((pf.getResult[1]!)[1]!)[0]!
    let eval_u : Q(Real) ← reconstructTerm (((((pf.getResult[1]!)[1]!)[1]!)[0]!)[0]!)[1]!
    let real_d : Q(Nat) := q($d - 1)

    let goal_l : Q(Prop) := q($eval_l = TransFns.expTaylor $real_d $l / (1 - $l ^ ($real_d + 1) / ($real_d + 1).factorial))
    let goal_l_pf : Q($goal_l) ← Meta.mkFreshExprMVar (some goal_l)
    normNumFactorial goal_l_pf.mvarId!

    let goal_u : Q(Prop) := q($eval_u = TransFns.expTaylor $real_d $u / (1 - $u ^ ($real_d + 1) / ($real_d + 1).factorial))
    let goal_u_pf : Q($goal_u) ← Meta.mkFreshExprMVar (some goal_u)
    normNumFactorial goal_u_pf.mvarId!

    let goal_l_nonneg : Q(Prop) := q(0 ≤ $l)
    let goal_l_nonneg_pf : Q($goal_l_nonneg) ← Meta.mkFreshExprMVar (some goal_l_nonneg)
    normNumFactorial goal_l_nonneg_pf.mvarId!

    let goal_bound_u : Q(Prop) := q($u ^ ($real_d + 1) < Nat.factorial ($real_d + 1))
    let goal_bound_u_pf : Q($goal_bound_u) ← Meta.mkFreshExprMVar (some goal_bound_u)
    normNumFactorial goal_bound_u_pf.mvarId!

    let proof := q(TransFns.arithTransExpApproxAbovePosComp ($d - 1) $l $u $t $eval_l $eval_u $goal_l_nonneg_pf $goal_bound_u_pf $goal_l_pf $goal_u_pf)
    addThm (← reconstructProofType pf.getResult) proof
  | .ARITH_TRANS_EXP_APPROX_ABOVE_NEG =>
    let eval_l : Q(Real) ← reconstructTerm ((pf.getResult[1]!)[1]!)[0]!
    let eval_u : Q(Real) ← reconstructTerm (((((pf.getResult[1]!)[1]!)[1]!)[0]!)[0]!)[1]!
    let d_nat : Nat := pf.getArguments[0]!.getIntegerValue!.natAbs
    let t : Q(Real) ← reconstructTerm pf.getArguments[1]!
    let l : Q(Real) ← reconstructTerm pf.getArguments[2]!
    let u : Q(Real) ← reconstructTerm pf.getArguments[3]!
    let d_half : Q(Nat) := q(Nat.div $d_nat 2)

    let goal_l : Q(Prop) := q(TransFns.expTaylor $d_nat $l = $eval_l)
    let goal_l_pf : Q($goal_l) ← Meta.mkFreshExprMVar (some goal_l)
    normNumFactorial goal_l_pf.mvarId!

    let goal_u : Q(Prop) := q(TransFns.expTaylor $d_nat $u = $eval_u)
    let goal_u_pf : Q($goal_u) ← Meta.mkFreshExprMVar (some goal_u)
    normNumFactorial goal_u_pf.mvarId!

    let goal_deg : Q(Prop) := q($d_nat = 2 * $d_half)
    let goal_deg_pf : Q($goal_deg) ← Meta.mkFreshExprMVar (some goal_deg)
    normNumFactorial goal_deg_pf.mvarId!

    let uNeg : Q(Prop) := q($u < 0)
    let uNeg_pf : Q($uNeg) ← Meta.mkFreshExprMVar (some uNeg)
    Real.normNum uNeg_pf.mvarId!

    let proof := q(TransFns.arithTransExpApproxAboveNegComp $d_nat (Nat.div $d_nat 2) $l $u $t $eval_l $eval_u $goal_l_pf $goal_u_pf $goal_deg_pf $uNeg_pf)
    addThm (← reconstructProofType pf.getResult) proof
  | .ARITH_TRANS_SINE_APPROX_BELOW_NEG =>
    let d : Nat := pf.getArguments[0]!.getIntegerValue!.natAbs
    let t : Q(Real) ← reconstructTerm pf.getArguments[1]!
    let c : Q(Real) ← reconstructTerm pf.getArguments[2]!
    let lb : Q(Real) ← reconstructTerm pf.getArguments[3]!
    let ub : Q(Real) ← reconstructTerm pf.getArguments[4]!
    let eval_c : Q(Real) ← reconstructTerm (pf.getResult[1]!)[1]!
    let real_d : Q(Nat) := q($d - 1)
    let d_half : Q(Nat) := q(Nat.div $real_d 2)

    let goal_deg : Q(Prop) := q($real_d = 2 * $d_half + 1)
    let goal_deg_pf : Q($goal_deg) ← Meta.mkFreshExprMVar (some goal_deg)
    normNumFactorial goal_deg_pf.mvarId!

    let goal_l_bound : Q(Prop) := q(-Real.pi ≤ $lb)
    let goal_l_bound_pf : Q($goal_l_bound) ← Meta.mkFreshExprMVar (some goal_l_bound)
    Mathlib.Tactic.Linarith.linarith false [.const `Real.pi_gt_d20 [], .const `Real.pi_lt_d20 []] (g := goal_l_bound_pf.mvarId!)

    let ub_bound : Q(Prop) := q($ub ≤ 0)
    let ub_bound_pf : Q($ub_bound) ← Meta.mkFreshExprMVar (some ub_bound)
    -- linarith [pi_gt_d20, pi_lt_d20] at ubBound_pf
    Mathlib.Tactic.Linarith.linarith false [.const `Real.pi_gt_d20 [], .const `Real.pi_lt_d20 []] (g := ub_bound_pf.mvarId!)

    let goal_c : Q(Prop) := q($eval_c = TransFns.sinTaylor $real_d $c - ($c ^ ($real_d + 1) / ($real_d + 1).factorial))
    let goal_c_pf : Q($goal_c) ← Meta.mkFreshExprMVar (some goal_c)
    normNumFactorial goal_c_pf.mvarId!

    let goal_if : Q(Prop) := q($c = if -Real.pi/2 < $lb then $lb else if - Real.pi/2 < $ub then -Real.pi/2 else $ub)
    let goal_if_pf : Q($goal_if) ← Meta.mkFreshExprMVar (some goal_if)
    let some [if1, if2] ← Meta.splitTarget? goal_if_pf.mvarId! | throwError "split 1"
    let some [if3, if4] ← Meta.splitTarget? if2 | throwError "split 2"

    Mathlib.Tactic.Linarith.linarith false [.const `Real.pi_gt_d20 [], .const `Real.pi_lt_d20 []] (g := if1)
    Mathlib.Tactic.Linarith.linarith false [.const `Real.pi_gt_d20 [], .const `Real.pi_lt_d20 []] (g := if3)
    Mathlib.Tactic.Linarith.linarith false [.const `Real.pi_gt_d20 [], .const `Real.pi_lt_d20 []] (g := if4)

    let proof := q(TransFns.arithTransSineApproxBelowNegComp ($d - 1) (Nat.div ($d - 1) 2) $lb $ub $t $c $eval_c $goal_deg_pf $goal_c_pf $goal_l_bound_pf $ub_bound_pf $goal_if_pf)
    addThm (← reconstructProofType pf.getResult) proof
  | .ARITH_TRANS_SINE_APPROX_ABOVE_NEG =>
    let d : Nat := pf.getArguments[0]!.getIntegerValue!.natAbs
    let t : Q(Real) ← reconstructTerm pf.getArguments[1]!
    let lb : Q(Real) ← reconstructTerm pf.getArguments[2]!
    let ub : Q(Real) ← reconstructTerm pf.getArguments[3]!
    let l : Q(Real) ← reconstructTerm pf.getArguments[4]!
    let u : Q(Real) ← reconstructTerm pf.getArguments[5]!
    let real_d : Q(Nat) := q($d - 1)
    let d_half : Q(Nat) := q(Nat.div $real_d 2)

    let goal_deg : Q(Prop) := q($real_d = 2 * $d_half + 1)
    let goal_deg_pf : Q($goal_deg) ← Meta.mkFreshExprMVar (some goal_deg)
    normNumFactorial goal_deg_pf.mvarId!

    let ubNonpos : Q(Prop) := q($ub ≤ 0)
    let ubNonpos_pf : Q($ubNonpos) ← Meta.mkFreshExprMVar (some ubNonpos)
    Real.normNum ubNonpos_pf.mvarId!

    let lbBound : Q(Prop) := q(-Real.pi ≤ $lb)
    let lbBound_pf : Q($lbBound) ← Meta.mkFreshExprMVar (some lbBound)
    -- linarith [pi_gt_d20, pi_lt_d20] at ubBound_pf
    Mathlib.Tactic.Linarith.linarith false [.const `Real.pi_gt_d20 [], .const `Real.pi_lt_d20 []] (g := lbBound_pf.mvarId!)

    let goal_l : Q(Prop) := q($l = TransFns.sinTaylor $real_d $lb + ($lb ^ ($real_d + 1) / ($real_d + 1).factorial))
    let goal_l_pf : Q($goal_l) ← Meta.mkFreshExprMVar (some goal_l)
    normNumFactorial goal_l_pf.mvarId!

    let goal_u : Q(Prop) := q($u = TransFns.sinTaylor $real_d $ub + ($ub ^ ($real_d + 1) / ($real_d + 1).factorial))
    let goal_u_pf : Q($goal_u) ← Meta.mkFreshExprMVar (some goal_u)
    normNumFactorial goal_u_pf.mvarId!

    let proof := q(TransFns.arithTransSineApproxAboveNegComp ($d - 1) (Nat.div ($d - 1) 2) $lb $ub $t $l $u $goal_deg_pf $ubNonpos_pf $lbBound_pf $goal_l_pf $goal_u_pf)
    addThm (← reconstructProofType pf.getResult) proof
  | .ARITH_TRANS_SINE_APPROX_BELOW_POS =>
    let d : Nat := pf.getArguments[0]!.getIntegerValue!.natAbs
    let t : Q(Real) ← reconstructTerm pf.getArguments[1]!
    let lb : Q(Real) ← reconstructTerm pf.getArguments[2]!
    let ub : Q(Real) ← reconstructTerm pf.getArguments[3]!
    let l : Q(Real) ← reconstructTerm pf.getArguments[4]!
    let u : Q(Real) ← reconstructTerm pf.getArguments[5]!
    let real_d : Q(Nat) := q($d - 1)

    let lbNonneg : Q(Prop) := q(0 ≤ $lb)
    let lbNonneg_pf : Q($lbNonneg) ← Meta.mkFreshExprMVar (some lbNonneg)
    Real.normNum lbNonneg_pf.mvarId!

    let ubBound : Q(Prop) := q($ub ≤ Real.pi)
    let ubBound_pf : Q($ubBound) ← Meta.mkFreshExprMVar (some ubBound)
    -- linarith [pi_gt_d20, pi_lt_d20] at ubBound_pf
    Mathlib.Tactic.Linarith.linarith false [.const `Real.pi_gt_d20 [], .const `Real.pi_lt_d20 []] (g := ubBound_pf.mvarId!)

    let goal_l : Q(Prop) := q($l = TransFns.sinTaylor $real_d $lb - ($lb ^ ($real_d + 1) / ($real_d + 1).factorial))
    let goal_l_pf : Q($goal_l) ← Meta.mkFreshExprMVar (some goal_l)
    normNumFactorial goal_l_pf.mvarId!

    let goal_u : Q(Prop) := q($u = TransFns.sinTaylor $real_d $ub - ($ub ^ ($real_d + 1) / ($real_d + 1).factorial))
    let goal_u_pf : Q($goal_u) ← Meta.mkFreshExprMVar (some goal_u)
    normNumFactorial goal_u_pf.mvarId!

    let proof := q(TransFns.arithTransSineApproxBelowPosComp ($d - 1) $t $lb $ub $l $u $lbNonneg_pf $ubBound_pf $goal_l_pf $goal_u_pf)
    addThm (← reconstructProofType pf.getResult) proof
  | .ARITH_TRANS_SINE_APPROX_ABOVE_POS =>
    let d : Nat := pf.getArguments[0]!.getIntegerValue!.natAbs
    let t : Q(Real) ← reconstructTerm pf.getArguments[1]!
    let c : Q(Real) ← reconstructTerm pf.getArguments[2]!
    let lb : Q(Real) ← reconstructTerm pf.getArguments[3]!
    let ub : Q(Real) ← reconstructTerm pf.getArguments[4]!
    let eval_c : Q(Real) ← reconstructTerm (pf.getResult[1]!)[1]!
    let real_d : Q(Nat) := q($d - 1)
    let d_half : Q(Nat) := q(Nat.div $real_d 2)

    let goal_deg : Q(Prop) := q($real_d = 2 * $d_half + 1)
    let goal_deg_pf : Q($goal_deg) ← Meta.mkFreshExprMVar (some goal_deg)
    normNumFactorial goal_deg_pf.mvarId!

    let goal_l_nonneg : Q(Prop) := q(0 ≤ $lb)
    let goal_l_nonneg_pf : Q($goal_l_nonneg) ← Meta.mkFreshExprMVar (some goal_l_nonneg)
    Mathlib.Tactic.Linarith.linarith false [.const `Real.pi_gt_d20 [], .const `Real.pi_lt_d20 []] (g := goal_l_nonneg_pf.mvarId!)

    let ubBound : Q(Prop) := q($ub ≤ Real.pi)
    let ubBound_pf : Q($ubBound) ← Meta.mkFreshExprMVar (some ubBound)
    -- linarith [pi_gt_d20, pi_lt_d20] at ubBound_pf
    Mathlib.Tactic.Linarith.linarith false [.const `Real.pi_gt_d20 [], .const `Real.pi_lt_d20 []] (g := ubBound_pf.mvarId!)

    let goal_c : Q(Prop) := q($eval_c = TransFns.sinTaylor $real_d $c + ($c ^ ($real_d + 1) / ($real_d + 1).factorial))
    let goal_c_pf : Q($goal_c) ← Meta.mkFreshExprMVar (some goal_c)
    normNumFactorial goal_c_pf.mvarId!

    let goal_if : Q(Prop) := q($c = if $ub < Real.pi/2 then $ub else if $lb < Real.pi/2 then Real.pi/2 else $lb)
    let goal_if_pf : Q($goal_if) ← Meta.mkFreshExprMVar (some goal_if)
    let some [if1, if2] ← Meta.splitTarget? goal_if_pf.mvarId! | throwError "split 1"
    let some [if3, if4] ← Meta.splitTarget? if2 | throwError "split 2"

    Mathlib.Tactic.Linarith.linarith false [.const `Real.pi_gt_d20 [], .const `Real.pi_lt_d20 []] (g := if1)
    Mathlib.Tactic.Linarith.linarith false [.const `Real.pi_gt_d20 [], .const `Real.pi_lt_d20 []] (g := if3)
    Mathlib.Tactic.Linarith.linarith false [.const `Real.pi_gt_d20 [], .const `Real.pi_lt_d20 []] (g := if4)

    let proof := q(TransFns.arithTransSineApproxAbovePosComp ($d - 1) (Nat.div ($d - 1) 2) $lb $ub $t $c $eval_c $goal_deg_pf $goal_l_nonneg_pf $ubBound_pf $goal_c_pf $goal_if_pf)
    addThm (← reconstructProofType pf.getResult) proof
  | _ => return none
where
normNumFactorial (mv : MVarId) : MetaM Unit := withTraceNode `smt.reconstruct.normNum traceArithNormNum do
  let simpTheorems : Meta.SimpTheorems ← Meta.getSimpTheorems
  let simpTheorems ← simpTheorems.addDeclToUnfold `Nat.factorial
  let ctx ← Meta.Simp.mkContext (simpTheorems := #[simpTheorems])
  let remainingGoal? ← (Mathlib.Tactic.transformAtTarget (fun e ctx ↦ Mathlib.Meta.NormNum.deriveSimp ctx (useSimp := true) (e := e)) "norm_num" (ifUnchanged := .silent) mv).run ctx
  match remainingGoal? with
  | .some _ => throwError "[norm_num]: could not prove {← mv.getType}"
  | .none => pure ()
normNumAbs (mv : MVarId) : MetaM Unit := withTraceNode `smt.reconstruct.normNum traceArithNormNum do
  let simpTheorems : Meta.SimpTheorems ← Meta.getSimpTheorems
  let simpTheorems ← simpTheorems.addDeclToUnfold `abs
  let ctx ← Meta.Simp.mkContext (simpTheorems := #[simpTheorems])
  let remainingGoal? ← (Mathlib.Tactic.transformAtTarget (fun e ctx ↦ Mathlib.Meta.NormNum.deriveSimp ctx (useSimp := true) (e := e)) "norm_num" (ifUnchanged := .silent) mv).run ctx
  match remainingGoal? with
  | .some _ => throwError "[norm_num]: could not prove {← mv.getType}"
  | .none => pure ()
