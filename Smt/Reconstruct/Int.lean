/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

module

public import Smt.Reconstruct
public meta import Smt.Reconstruct
public import Smt.Reconstruct.Bool.Lemmas
public meta import Smt.Reconstruct.Bool.Lemmas
public import Smt.Reconstruct.Int.Core
public meta import Smt.Reconstruct.Int.Core
public import Smt.Reconstruct.Int.Lemmas
public meta import Smt.Reconstruct.Int.Lemmas
public import Smt.Reconstruct.Int.Polynorm
public meta import Smt.Reconstruct.Int.Polynorm
public import Smt.Reconstruct.Int.Rewrites
public meta import Smt.Reconstruct.Int.Rewrites

public meta section

namespace Smt.Reconstruct.Int

open Lean
open Qq

@[smt_sort_reconstruct] def reconstructIntSort : SortReconstructor := fun s => do match s.getKind! with
  | .INTEGER_SORT => return q(Int)
  | _             => return none

@[smt_term_reconstruct] def reconstructInt : TermReconstructor := fun t => do match t.getKind! with
  | .SKOLEM => match t.getSkolemId! with
    | .INT_DIV_BY_ZERO => return q(fun (x : Int) => x / 0)
    | .MOD_BY_ZERO => return q(fun (x : Int) => x % 0)
    | _ => return none
  | .CONST_INTEGER =>
    let x : Int := t.getIntegerValue!
    let x' : Q(Nat) := mkRawNatLit x.natAbs
    if x ≥ 0 then
      return q(OfNat.ofNat $x' : Int)
    else
      return q(-(OfNat.ofNat $x' : Int))
  | .NEG =>
    if !t.getSort!.isInteger then return none
    let x : Q(Int) ← reconstructTerm t[0]!
    return q(-$x)
  | .SUB =>
    if !t.getSort!.isInteger then return none
    leftAssocOp q(@HSub.hSub Int Int Int _) t
  | .ADD =>
    if !t.getSort!.isInteger then return none
    leftAssocOp q(@HAdd.hAdd Int Int Int _) t
  | .MULT =>
    if !t.getSort!.isInteger then return none
    leftAssocOp q(@HMul.hMul Int Int Int _) t
  | .INTS_DIVISION =>
    leftAssocOp q(@HDiv.hDiv Int Int Int _) t
  | .INTS_DIVISION_TOTAL =>
    leftAssocOp q(@HDiv.hDiv Int Int Int _) t
  | .INTS_MODULUS =>
    let x : Q(Int) ← reconstructTerm t[0]!
    let y : Q(Int) ← reconstructTerm t[1]!
    return q($x % $y)
  | .INTS_MODULUS_TOTAL =>
    let x : Q(Int) ← reconstructTerm t[0]!
    let y : Q(Int) ← reconstructTerm t[1]!
    return q($x % $y)
  | .ABS =>
    if !t.getSort!.isInteger then return none
    let x : Q(Int) ← reconstructTerm t[0]!
    return q(«$x».abs)
  | .POW2 =>
    let x : Q(Int) ← reconstructTerm t[0]!
    return q((if $x < 0 then 0 else 2 ^ «$x».toNat : Int))
  | .LEQ =>
    if !t[0]!.getSort!.isInteger then return none
    let x : Q(Int) ← reconstructTerm t[0]!
    let y : Q(Int) ← reconstructTerm t[1]!
    return q(Int.ble $x $y)
  | .LT =>
    if !t[0]!.getSort!.isInteger then return none
    let x : Q(Int) ← reconstructTerm t[0]!
    let y : Q(Int) ← reconstructTerm t[1]!
    return q(Int.blt $x $y)
  | .GEQ =>
    if !t[0]!.getSort!.isInteger then return none
    let x : Q(Int) ← reconstructTerm t[0]!
    let y : Q(Int) ← reconstructTerm t[1]!
    return q(Int.bge $x $y)
  | .GT =>
    if !t[0]!.getSort!.isInteger then return none
    let x : Q(Int) ← reconstructTerm t[0]!
    let y : Q(Int) ← reconstructTerm t[1]!
    return q(Int.bgt $x $y)
  | _ => return none
where
  leftAssocOp (op : Expr) (t : cvc5.Term) : ReconstructM Expr := do
    let mut curr ← reconstructTerm t[0]!
    for i in [1:t.getNumChildren] do
      curr := mkApp2 op curr (← reconstructTerm t[i]!)
    return curr

def reconstructRewrite (pf : cvc5.Proof) : ReconstructM (Option Expr) := do
  match pf.getRewriteRule! with
  | .ARITH_POW_ELIM =>
    if !pf.getResult[0]![0]!.getSort!.isInteger then return none
    let x : Q(Int) ← reconstructTerm pf.getResult[0]![0]!
    let c : Q(Nat) ← reconstructTerm pf.getResult[0]![1]!
    addThm (← reconstructProofType pf.getResult) q(Bool.eq.refl ($x ^ $c))
  | .ARITH_INT_DIV_TOTAL =>
    let t : Q(Int) ← reconstructTerm pf.getArguments[1]!
    let s : Q(Int) ← reconstructTerm pf.getArguments[2]!
    let h : Q(Bool.eq (decide ($s = 0)) false) ← reconstructProof pf.getChildren[0]!
    addThm (← reconstructProofType pf.getResult) q(@Rewrite.div_total $t $s $h)
  | .ARITH_INT_DIV_TOTAL_ONE =>
    let t : Q(Int) ← reconstructTerm pf.getArguments[1]!
    addThm (← reconstructProofType pf.getResult) q(@Rewrite.div_total_one $t)
  | .ARITH_INT_DIV_TOTAL_ZERO =>
    let t : Q(Int) ← reconstructTerm pf.getArguments[1]!
    addThm (← reconstructProofType pf.getResult) q(@Rewrite.div_total_zero $t)
  | .ARITH_INT_DIV_TOTAL_NEG =>
    let t : Q(Int) ← reconstructTerm pf.getArguments[1]!
    let s : Q(Int) ← reconstructTerm pf.getArguments[2]!
    let h : Q(Bool.eq (Int.blt $s 0) true) ← reconstructProof pf.getChildren[0]!
    addThm (← reconstructProofType pf.getResult) q(@Rewrite.div_total_neg $t $s $h)
  | .ARITH_INT_MOD_TOTAL =>
    let t : Q(Int) ← reconstructTerm pf.getArguments[1]!
    let s : Q(Int) ← reconstructTerm pf.getArguments[2]!
    let h : Q(Bool.eq (decide ($s = 0)) false) ← reconstructProof pf.getChildren[0]!
    addThm (← reconstructProofType pf.getResult) q(@Rewrite.mod_total $t $s $h)
  | .ARITH_INT_MOD_TOTAL_ONE =>
    let t : Q(Int) ← reconstructTerm pf.getArguments[1]!
    addThm (← reconstructProofType pf.getResult) q(@Rewrite.mod_total_one $t)
  | .ARITH_INT_MOD_TOTAL_ZERO =>
    let t : Q(Int) ← reconstructTerm pf.getArguments[1]!
    addThm (← reconstructProofType pf.getResult) q(@Rewrite.mod_total_zero $t)
  | .ARITH_INT_MOD_TOTAL_NEG =>
    let t : Q(Int) ← reconstructTerm pf.getArguments[1]!
    let s : Q(Int) ← reconstructTerm pf.getArguments[2]!
    let h : Q(Bool.eq (Int.blt $s 0) true) ← reconstructProof pf.getChildren[0]!
    addThm (← reconstructProofType pf.getResult) q(@Rewrite.mod_total_neg $t $s $h)
  | .ARITH_ELIM_GT =>
    if !pf.getArguments[1]!.getSort!.isInteger then return none
    let t : Q(Int) ← reconstructTerm pf.getArguments[1]!
    let s : Q(Int) ← reconstructTerm pf.getArguments[2]!
    addThm (← reconstructProofType pf.getResult) q(@Rewrite.elim_gt $t $s)
  | .ARITH_ELIM_LT =>
    if !pf.getArguments[1]!.getSort!.isInteger then return none
    let t : Q(Int) ← reconstructTerm pf.getArguments[1]!
    let s : Q(Int) ← reconstructTerm pf.getArguments[2]!
    addThm (← reconstructProofType pf.getResult) q(@Rewrite.elim_lt $t $s)
  | .ARITH_ELIM_INT_GT =>
    let t : Q(Int) ← reconstructTerm pf.getArguments[1]!
    let s : Q(Int) ← reconstructTerm pf.getArguments[2]!
    addThm (← reconstructProofType pf.getResult) q(@Rewrite.elim_gt_add_one $t $s)
  | .ARITH_ELIM_INT_LT =>
    let t : Q(Int) ← reconstructTerm pf.getArguments[1]!
    let s : Q(Int) ← reconstructTerm pf.getArguments[2]!
    addThm (← reconstructProofType pf.getResult) q(@Rewrite.elim_lt_add_one $t $s)
  | .ARITH_ELIM_LEQ =>
    if !pf.getArguments[1]!.getSort!.isInteger then return none
    let t : Q(Int) ← reconstructTerm pf.getArguments[1]!
    let s : Q(Int) ← reconstructTerm pf.getArguments[2]!
    addThm (← reconstructProofType pf.getResult) q(@Rewrite.elim_leq $t $s)
  | .ARITH_LEQ_NORM =>
    let t : Q(Int) ← reconstructTerm pf.getArguments[1]!
    let s : Q(Int) ← reconstructTerm pf.getArguments[2]!
    addThm (← reconstructProofType pf.getResult) q(@Rewrite.leq_norm $t $s)
  | .ARITH_GEQ_TIGHTEN =>
    let t : Q(Int) ← reconstructTerm pf.getArguments[1]!
    let s : Q(Int) ← reconstructTerm pf.getArguments[2]!
    addThm (← reconstructProofType pf.getResult) q(@Rewrite.geq_tighten $t $s)
  | .ARITH_GEQ_NORM1_INT =>
    let t : Q(Int) ← reconstructTerm pf.getArguments[1]!
    let s : Q(Int) ← reconstructTerm pf.getArguments[2]!
    addThm (← reconstructProofType pf.getResult) q(@Rewrite.geq_norm1 $t $s)
  | .ARITH_EQ_ELIM_INT =>
    let t : Q(Int) ← reconstructTerm pf.getArguments[1]!
    let s : Q(Int) ← reconstructTerm pf.getArguments[2]!
    addThm (← reconstructProofType pf.getResult) q(@Rewrite.eq_elim $t $s)
  | .ARITH_MOD_OVER_MOD =>
    let c : Q(Int) ← reconstructTerm pf.getArguments[1]!
    let ts : Q(List Int) ← reconstructTerms pf.getArguments[2]!.getChildren
    let r : Q(Int) ← reconstructTerm pf.getArguments[3]!
    let ss : Q(List Int) ← reconstructTerms pf.getArguments[4]!.getChildren
    let h : Q(Bool.eq (decide ($c = 0)) false) ← reconstructProof pf.getChildren[0]!
    addThm (← reconstructProofType pf.getResult) q(@Rewrite.mod_over_mod $c $ts $r $ss $h)
  | .ARITH_DIVISIBLE_ELIM =>
    let n : Q(Int) ← reconstructTerm pf.getArguments[1]!
    let t : Q(Int) ← reconstructTerm pf.getArguments[2]!
    let h : Q(Bool.eq (decide ($n = 0)) false) ← reconstructProof pf.getChildren[0]!
    addThm (← reconstructProofType pf.getResult) q(@Rewrite.divisible_elim $n $t $h)
  | .ARITH_ABS_EQ =>
    if !pf.getArguments[1]!.getSort!.isInteger then return none
    let x : Q(Int) ← reconstructTerm pf.getArguments[1]!
    let y : Q(Int) ← reconstructTerm pf.getArguments[2]!
    addThm (← reconstructProofType pf.getResult) q(@Rewrite.abs_eq $x $y)
  | .ARITH_ABS_INT_GT =>
    let x : Q(Int) ← reconstructTerm pf.getArguments[1]!
    let y : Q(Int) ← reconstructTerm pf.getArguments[2]!
    addThm (← reconstructProofType pf.getResult) q(@Rewrite.abs_gt $x $y)
  | .ARITH_GEQ_ITE_LIFT =>
    if !pf.getArguments[2]!.getSort!.isInteger then return none
    let c : Q(Bool) ← reconstructTerm pf.getArguments[1]!
    let t : Q(Int) ← reconstructTerm pf.getArguments[2]!
    let s : Q(Int) ← reconstructTerm pf.getArguments[3]!
    let r : Q(Int) ← reconstructTerm pf.getArguments[4]!
    addThm (← reconstructProofType pf.getResult) q(@Rewrite.geq_ite_lift $c $t $s $r)
  | .ARITH_LEQ_ITE_LIFT =>
    if !pf.getArguments[2]!.getSort!.isInteger then return none
    let c : Q(Bool) ← reconstructTerm pf.getArguments[1]!
    let t : Q(Int) ← reconstructTerm pf.getArguments[2]!
    let s : Q(Int) ← reconstructTerm pf.getArguments[3]!
    let r : Q(Int) ← reconstructTerm pf.getArguments[4]!
    addThm (← reconstructProofType pf.getResult) q(@Rewrite.leq_ite_lift $c $t $s $r)
  | .ARITH_MIN_LT1 =>
    if !pf.getArguments[1]!.getSort!.isInteger then return none
    let t : Q(Int) ← reconstructTerm pf.getArguments[1]!
    let s : Q(Int) ← reconstructTerm pf.getArguments[2]!
    addThm (← reconstructProofType pf.getResult) q(@Rewrite.min_lt1 $t $s)
  | .ARITH_MIN_LT2 =>
    if !pf.getArguments[1]!.getSort!.isInteger then return none
    let t : Q(Int) ← reconstructTerm pf.getArguments[1]!
    let s : Q(Int) ← reconstructTerm pf.getArguments[2]!
    addThm (← reconstructProofType pf.getResult) q(@Rewrite.min_lt2 $t $s)
  | .ARITH_MAX_GEQ1 =>
    if !pf.getArguments[1]!.getSort!.isInteger then return none
    let t : Q(Int) ← reconstructTerm pf.getArguments[1]!
    let s : Q(Int) ← reconstructTerm pf.getArguments[2]!
    addThm (← reconstructProofType pf.getResult) q(@Rewrite.max_geq1 $t $s)
  | .ARITH_MAX_GEQ2 =>
    if !pf.getArguments[1]!.getSort!.isInteger then return none
    let t : Q(Int) ← reconstructTerm pf.getArguments[1]!
    let s : Q(Int) ← reconstructTerm pf.getArguments[2]!
    addThm (← reconstructProofType pf.getResult) q(@Rewrite.max_geq2 $t $s)
  | _ => return none

def reconstructSumUB (pf : cvc5.Proof) : ReconstructM (Option Expr) := do
  let f := fun (ks, ls, rs, hs) p => do
    let l : Q(Int) ← reconstructTerm p.getResult[0]!
    let r : Q(Int) ← reconstructTerm p.getResult[1]!
    let lsl := q($ls + $l)
    let rsr := q($rs + $r)
    let k := p.getResult.getKind!
    if ks == .LT && k == .LT then
      let hs : Q(Int.blt $ls $rs = true) := hs
      let h : Q(Int.blt $l $r = true) ← reconstructProof p
      return (.LT, lsl, rsr, q(Int.sum_ub₁ $hs $h))
    else if ks == .LT && k == .LEQ then
      let hs : Q(Int.blt $ls $rs = true) := hs
      let h : Q(Int.ble $l $r = true) ← reconstructProof p
      return (.LT, lsl, rsr, q(Int.sum_ub₂ $hs $h))
    else if ks == .LT && k == .EQUAL then
      let hs : Q(Int.blt $ls $rs = true) := hs
      let h : Q(Bool.eq $l $r) ← reconstructProof p
      return (.LT, lsl, rsr, q(Int.sum_ub₃ $hs $h))
    else if ks == .LEQ && k == .LT then
      let hs : Q(Int.ble $ls $rs = true) := hs
      let h : Q(Int.blt $l $r = true) ← reconstructProof p
      return (.LT, lsl, rsr, q(Int.sum_ub₄ $hs $h))
    else if ks == .LEQ && k == .LEQ then
      let hs : Q(Int.ble $ls $rs = true) := hs
      let h : Q(Int.ble $l $r = true) ← reconstructProof p
      return (.LEQ, lsl, rsr, q(Int.sum_ub₅ $hs $h))
    else if ks == .LEQ && k == .EQUAL then
      let hs : Q(Int.ble $ls $rs = true) := hs
      let h : Q(Bool.eq $l $r) ← reconstructProof p
      return (.LEQ, lsl, rsr, q(Int.sum_ub₆ $hs $h))
    else if ks == .EQUAL && k == .LT then
      let hs : Q(Bool.eq $ls $rs) := hs
      let h : Q(Int.blt $l $r = true) ← reconstructProof p
      return (.LT, lsl, rsr, q(Int.sum_ub₇ $hs $h))
    else if ks == .EQUAL && k == .LEQ then
      let hs : Q(Bool.eq $ls $rs) := hs
      let h : Q(Int.ble $l $r = true) ← reconstructProof p
      return (.LEQ, lsl, rsr, q(Int.sum_ub₈ $hs $h))
    else if ks == .EQUAL && k == .EQUAL then
      let hs : Q(Bool.eq $ls $rs) := hs
      let h : Q(Bool.eq $l $r) ← reconstructProof p
      return (.EQUAL, lsl, rsr, q(Int.sum_ub₉ $hs $h))
    else
      throwError "[sum_ub]: invalid kinds: {ks}, {k}"
  let k := pf.getChildren[0]!.getResult.getKind!
  let ls : Q(Int) ← reconstructTerm pf.getChildren[0]!.getResult[0]!
  let rs : Q(Int) ← reconstructTerm pf.getChildren[0]!.getResult[1]!
  let hs ← reconstructProof pf.getChildren[0]!
  let (ks, ls, rs, hs) ← pf.getChildren[1:].foldlM f (k, ls, rs, hs)
  if ks == .EQUAL then
    let hs : Q(Bool.eq $ls $rs) := hs
    addThm (← reconstructProofType pf.getResult) q(Int.ble_of_eq $hs)
  else
    addThm (← reconstructProofType pf.getResult) hs

def reconstructMulAbsComparison (pf : cvc5.Proof) : ReconstructM (Option Expr) := do
  let f := fun (ks, ls, rs, hs) p => do
    let k := p.getResult.getKind!
    if ks == .EQUAL && k == .EQUAL then
      let l : Q(Int) ← reconstructTerm p.getResult[0]![0]!
      let r : Q(Int) ← reconstructTerm p.getResult[1]![0]!
      let hs : Q(Bool.eq «$ls».abs «$rs».abs) := hs
      let h : Q(Bool.eq «$l».abs «$r».abs) ← reconstructProof p
      return (.EQUAL, q($ls * $l), q($rs * $r), q(Int.mul_abs₁ $hs $h))
    else if ks == .GT && k == .AND then
      let l : Q(Int) ← reconstructTerm p.getResult[0]![0]![0]!
      let r : Q(Int) ← reconstructTerm p.getResult[0]![1]![0]!
      let hs : Q(Int.bgt «$ls».abs «$rs».abs = true) := hs
      let h ← reconstructProof p
      return (.GT, q($ls * $l), q($rs * $r), mkApp6 (.const ``Int.mul_abs₂ []) ls l rs r hs h)
    else if ks == .GT && k == .GT then
      let l : Q(Int) ← reconstructTerm p.getResult[0]![0]!
      let r : Q(Int) ← reconstructTerm p.getResult[1]![0]!
      let hs : Q(Int.bgt «$ls».abs «$rs».abs = true) := hs
      let h : Q(Int.bgt «$l».abs «$r».abs = true) ← reconstructProof p
      return (.GT, q($ls * $l), q($rs * $r), q(Int.mul_abs₃ $hs $h))
    else
      throwError "[mul_abs]: invalid kinds: {ks}, {k}"
  let k := pf.getChildren[0]!.getResult.getKind!
  let ls : Q(Int) ← reconstructTerm pf.getChildren[0]!.getResult[0]![0]!
  let rs : Q(Int) ← reconstructTerm pf.getChildren[0]!.getResult[1]![0]!
  let hs ← reconstructProof pf.getChildren[0]!
  let (ks, _, _, hs) ← pf.getChildren[1:].foldlM f (k, ls, rs, hs)
  addThm (← reconstructProofType pf.getResult) hs

def reconstructMulSign (pf : cvc5.Proof) : ReconstructM (Option Expr) := do
  let ts := if pf.getResult[0]!.getKind! == .AND then pf.getResult[0]!.getChildren else #[pf.getResult[0]!]
  let mut hs : Array (Name × (Array Expr → ReconstructM Expr)) := #[]
  let mut map : Std.HashMap cvc5.Term Nat := {}
  for h : i in [0:ts.size] do
    let t := ts[i]
    let p ← reconstructProofType t
    hs := hs.push (Name.num `a i, fun _ => return p)
    map := map.insert (if t.getKind! == .NOT then t[0]![0]! else t[0]!) i
  let t := pf.getResult[1]!
  let vs := if t[0]!.getKind! == .CONST_INTEGER then t[1]!.getChildren else t[0]!.getChildren
  let ps : Q(List Bool) ← reconstructTerms ts
  let q : Q(Bool) ← reconstructTerm t
  let h : Q(Bool.impliesN $ps ($q = true)) ← Meta.withLocalDeclsD hs fun hs => do
    let h : Q($q = true) ← if ts[map[vs[0]!]!]!.getKind! == .NOT then
        let a : Q(Int) ← reconstructTerm vs[0]!
        let ha := hs[map[vs[0]!]!]!
        go vs ts hs map .GT q($a * $a) (mkApp2 (.const ``Int.mul_sign₀ []) a ha) 2
      else
        let a : Q(Int) ← reconstructTerm vs[0]!
        go vs ts hs map ts[map[vs[0]!]!]!.getKind! a hs[map[vs[0]!]!]! 1
    Meta.mkLambdaFVars hs h
  addThm (← reconstructProofType pf.getResult) q(Bool.scopes $h)
where
  go vs ts hs map (ka : cvc5.Kind) (a : Q(Int)) (ha : Expr) i : ReconstructM Expr := do
    if hi : i < vs.size then
      let b : Q(Int) ← reconstructTerm vs[i]
      let k : cvc5.Kind := ts[map[vs[i]]!]!.getKind!
      let hb := hs[map[vs[i]]!]!
      if ka == .LT && k == .LT then
        go vs ts hs map .GT q($a * $b) (mkApp4 (.const ``Int.mul_sign₁ []) a b ha hb) (i + 1)
      else if ka == .LT && k == .NOT then
        go vs ts hs map .LT q($a * $b * $b) (mkApp4 (.const ``Int.mul_sign₂ []) a b ha hb) (i + 2)
      else if ka == .LT && k == .GT then
        go vs ts hs map .LT q($a * $b) (mkApp4 (.const ``Int.mul_sign₃ []) a b ha hb) (i + 1)
      else if ka == .GT && k == .LT then
        go vs ts hs map .LT q($a * $b) (mkApp4 (.const ``Int.mul_sign₄ []) a b ha hb) (i + 1)
      else if ka == .GT && k == .NOT then
        go vs ts hs map .GT q($a * $b * $b) (mkApp4 (.const ``Int.mul_sign₅ []) a b ha hb) (i + 2)
      else if ka == .GT && k == .GT then
        go vs ts hs map .GT q($a * $b) (mkApp4 (.const ``Int.mul_sign₆ []) a b ha hb) (i + 1)
      else
        throwError "[mul_sign]: invalid kinds: {ka}, {k}"
    else
      return ha

def reconstructArithPolyNormRel (pf : cvc5.Proof) : ReconstructM (Option Expr) := do
  let cx : Int ← pure pf.getChildren[0]!.getResult[0]![0]!.getIntegerValue!
  let cy : Int ← pure pf.getChildren[0]!.getResult[1]![0]!.getIntegerValue!
  let x₁ : Q(Int) ← reconstructTerm pf.getResult[0]![0]!
  let x₂ : Q(Int) ← reconstructTerm pf.getResult[0]![1]!
  let y₁ : Q(Int) ← reconstructTerm pf.getResult[1]![0]!
  let y₂ : Q(Int) ← reconstructTerm pf.getResult[1]![1]!
  let h : Q(Bool.eq ($cx * ($x₁ - $x₂)) ($cy * ($y₁ - $y₂))) ← reconstructProof pf.getChildren[0]!
  let k := pf.getResult[0]!.getKind!
  -- The signs of the constants are decided by evaluation.
  let hc := q(Eq.refl true)
  let n ← getThmName k (cx > 0)
  addThm (← reconstructProofType pf.getResult)
    (mkApp9 (.const n []) x₁ x₂ y₁ y₂ q($cx) q($cy) hc hc h)
where
  getThmName (k : cvc5.Kind) (sign : Bool) : ReconstructM Name :=
    if k == .LT && sign == true then pure ``Int.lt_of_sub_eq_pos
    else if k == .LT && sign == false then pure ``Int.lt_of_sub_eq_neg
    else if k == .LEQ && sign == true then pure ``Int.le_of_sub_eq_pos
    else if k == .LEQ && sign == false then pure ``Int.le_of_sub_eq_neg
    else if k == .EQUAL then pure ``Int.eq_of_sub_eq
    else if k == .GEQ && sign == true then pure ``Int.ge_of_sub_eq_pos
    else if k == .GEQ && sign == false then pure ``Int.ge_of_sub_eq_neg
    else if k == .GT && sign == true then pure ``Int.gt_of_sub_eq_pos
    else if k == .GT && sign == false then pure ``Int.gt_of_sub_eq_neg
    else throwError "[arith_poly_norm_rel]: invalid combination of kind and sign: {k}, {sign}"

@[smt_proof_reconstruct] def reconstructIntProof : ProofReconstructor := fun pf => do match pf.getRule with
  | .DSL_REWRITE
  | .THEORY_REWRITE => reconstructRewrite pf
  | .ARITH_SUM_UB =>
    if !pf.getResult[0]!.getSort!.isInteger then return none
    reconstructSumUB pf
  | .ARITH_MULT_ABS_COMPARISON =>
    if !pf.getResult[0]!.getSort!.isInteger then return none
    reconstructMulAbsComparison pf
  | .INT_TIGHT_UB =>
    if !pf.getChildren[0]!.getResult[1]!.getSort!.isInteger then return none
    let i : Q(Int) ← reconstructTerm pf.getChildren[0]!.getResult[0]!
    let c : Q(Int) ← reconstructTerm pf.getChildren[0]!.getResult[1]!
    let h : Q(Int.blt $i $c = true) ← reconstructProof pf.getChildren[0]!
    addThm (← reconstructProofType pf.getResult) q(@Int.int_tight_ub $c $i $h)
  | .INT_TIGHT_LB =>
    if !pf.getChildren[0]!.getResult[1]!.getSort!.isInteger then return none
    let i : Q(Int) ← reconstructTerm pf.getChildren[0]!.getResult[0]!
    let c : Q(Int) ← reconstructTerm pf.getChildren[0]!.getResult[1]!
    let h : Q(Int.bgt $i $c = true) ← reconstructProof pf.getChildren[0]!
    addThm (← reconstructProofType pf.getResult) q(@Int.int_tight_lb $c $i $h)
  | .ARITH_TRICHOTOMY =>
    if !pf.getResult[0]!.getSort!.isInteger then return none
    let x : Q(Int) ← reconstructTerm pf.getResult[0]!
    let c : Q(Int) ← reconstructTerm pf.getResult[1]!
    let k₁ := pf.getChildren[0]!.getResult.getKind!
    let k₂ := pf.getChildren[1]!.getResult.getKind!
    let h₁ ← reconstructProof pf.getChildren[0]!
    let h₂ ← reconstructProof pf.getChildren[1]!
    if k₁ == .LEQ && k₂ == .NOT then
      addThm (← reconstructProofType pf.getResult) (mkApp4 (.const ``Int.trichotomy₁ []) x c h₁ h₂)
    else if k₁ == .LEQ && k₂ == .GEQ then
      addThm (← reconstructProofType pf.getResult) (mkApp4 (.const ``Int.trichotomy₂ []) x c h₁ h₂)
    else if k₁ == .NOT && k₂ == .LEQ then
      addThm (← reconstructProofType pf.getResult) (mkApp4 (.const ``Int.trichotomy₃ []) x c h₁ h₂)
    else if k₁ == .NOT && k₂ == .GEQ then
      addThm (← reconstructProofType pf.getResult) (mkApp4 (.const ``Int.trichotomy₄ []) x c h₁ h₂)
    else if k₁ == .GEQ && k₂ == .LEQ then
      addThm (← reconstructProofType pf.getResult) (mkApp4 (.const ``Int.trichotomy₅ []) x c h₁ h₂)
    else if k₁ == .GEQ && k₂ == .NOT then
      addThm (← reconstructProofType pf.getResult) (mkApp4 (.const ``Int.trichotomy₆ []) x c h₁ h₂)
    else
      return none
  | .ARITH_REDUCTION =>
    if !pf.getArguments[0]!.getSort!.isInteger then return none
    if pf.getArguments[0]!.getKind! == .ABS then
      let x : Q(Int) ← reconstructTerm pf.getArguments[0]![0]!
      addThm (← reconstructProofType pf.getResult) q(@Int.abs_elim $x)
    else
      return none
  | .ARITH_POLY_NORM =>
    if !pf.getResult[0]!.getSort!.isInteger then return none
    let tac := if ← useNative then Int.nativePolyNorm else Int.polyNorm
    addTac (← reconstructProofType pf.getResult) (decideTac tac)
  | .ARITH_POLY_NORM_REL =>
    if !pf.getChildren[0]!.getResult[0]![0]!.getSort!.isInteger then return none
    reconstructArithPolyNormRel pf
  | .ARITH_MULT_SIGN =>
    if !pf.getResult[1]![0]!.getSort!.isInteger then return none
    reconstructMulSign pf
  | .ARITH_MULT_POS =>
    if !pf.getArguments[0]!.getSort!.isInteger then return none
    let m : Q(Int) ← reconstructTerm pf.getArguments[0]!
    let l : Q(Int) ← reconstructTerm pf.getArguments[1]![0]!
    let r : Q(Int) ← reconstructTerm pf.getArguments[1]![1]!
    let n ← match pf.getArguments[1]!.getKind! with
      | .LT => pure ``Int.mul_pos_lt
      | .LEQ => pure ``Int.mul_pos_le
      | .EQUAL => pure ``Int.mul_pos_eq
      | .GEQ => pure ``Int.mul_pos_ge
      | .GT => pure ``Int.mul_pos_gt
      | _ => return none
    addThm (← reconstructProofType pf.getResult) (mkApp3 (.const n []) l r m)
  | .ARITH_MULT_NEG =>
    if !pf.getArguments[0]!.getSort!.isInteger then return none
    let m : Q(Int) ← reconstructTerm pf.getArguments[0]!
    let l : Q(Int) ← reconstructTerm pf.getArguments[1]![0]!
    let r : Q(Int) ← reconstructTerm pf.getArguments[1]![1]!
    let n ← match pf.getArguments[1]!.getKind! with
      | .LT => pure ``Int.mul_neg_lt
      | .LEQ => pure ``Int.mul_neg_le
      | .EQUAL => pure ``Int.mul_neg_eq
      | .GEQ => pure ``Int.mul_neg_ge
      | .GT => pure ``Int.mul_neg_gt
      | _ => return none
    addThm (← reconstructProofType pf.getResult) (mkApp3 (.const n []) l r m)
  | _ => return none

end Smt.Reconstruct.Int
