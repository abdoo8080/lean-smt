/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

module

public import Smt.Reconstruct
public meta import Smt.Reconstruct
public import Smt.Reconstruct.Bool.Rewrites
public meta import Smt.Reconstruct.Bool.Rewrites
public import Smt.Reconstruct.Builtin.Lemmas
public meta import Smt.Reconstruct.Builtin.Lemmas
public import Smt.Reconstruct.Rat.Core
public meta import Smt.Reconstruct.Rat.Core
public import Smt.Reconstruct.Rat.Lemmas
public meta import Smt.Reconstruct.Rat.Lemmas
public import Smt.Reconstruct.Rat.Polynorm
public meta import Smt.Reconstruct.Rat.Polynorm
public import Smt.Reconstruct.Rat.Rewrites
public meta import Smt.Reconstruct.Rat.Rewrites

public meta section

namespace Smt.Reconstruct.Rat

open Lean Qq

@[smt_sort_reconstruct] def reconstructRatSort : SortReconstructor := fun s => do match s.getKind! with
  | .REAL_SORT => return q(Rat)
  | _          => return none

@[smt_term_reconstruct] def reconstructRat : TermReconstructor := fun t => do match t.getKind! with
  | .SKOLEM => match t.getSkolemId! with
    | .DIV_BY_ZERO => return q(fun (x : Rat) => x / 0)
    | _ => return none
  | .CONST_RATIONAL =>
    let c : Rat := t.getRationalValue!
    let num : Q(Rat) := mkRatLit c.num.natAbs
    if c.den == 1 then
      if c.num ≥ 0 then
        return q($num)
      else
        return q(-$num)
    else
      let den : Q(Rat) := mkRatLit c.den
      if c.num ≥ 0 then
        return q($num / $den)
      else
        return q(-$num / $den)
  | .NEG =>
    if t.getSort!.isInteger then return none
    let x : Q(Rat) ← reconstructTerm t[0]!
    return q(-$x)
  | .SUB =>
    if t.getSort!.isInteger then return none
    leftAssocOp q(@HSub.hSub Rat Rat Rat _) t
  | .ADD =>
    if t.getSort!.isInteger then return none
    leftAssocOp q(@HAdd.hAdd Rat Rat Rat _) t
  | .MULT =>
    if t.getSort!.isInteger then return none
    leftAssocOp q(@HMul.hMul Rat Rat Rat _) t
  | .DIVISION =>
    leftAssocOp q(@HDiv.hDiv Rat Rat Rat _) t
  | .DIVISION_TOTAL =>
    leftAssocOp q(@HDiv.hDiv Rat Rat Rat _) t
  | .ABS =>
    if t.getSort!.isInteger then return none
    let x : Q(Rat) ← reconstructTerm t[0]!
    return q(«$x».abs)
  | .LEQ =>
    if t[0]!.getSort!.isInteger then return none
    let x : Q(Rat) ← reconstructTerm t[0]!
    let y : Q(Rat) ← reconstructTerm t[1]!
    return q(smtLe $x $y)
  | .LT =>
    if t[0]!.getSort!.isInteger then return none
    let x : Q(Rat) ← reconstructTerm t[0]!
    let y : Q(Rat) ← reconstructTerm t[1]!
    return q(smtLt $x $y)
  | .GEQ =>
    if t[0]!.getSort!.isInteger then return none
    let x : Q(Rat) ← reconstructTerm t[0]!
    let y : Q(Rat) ← reconstructTerm t[1]!
    return q(smtGe $x $y)
  | .GT =>
    if t[0]!.getSort!.isInteger then return none
    let x : Q(Rat) ← reconstructTerm t[0]!
    let y : Q(Rat) ← reconstructTerm t[1]!
    return q(smtGt $x $y)
  | .TO_REAL =>
    let x : Q(Int) ← reconstructTerm t[0]!
    return q($x : Rat)
  | .TO_INTEGER =>
    let x : Q(Rat) ← reconstructTerm t[0]!
    return q(«$x».floor)
  | .IS_INTEGER =>
    let x : Q(Rat) ← reconstructTerm t[0]!
    return q(smtEq $x («$x».floor : Rat))
  | _ => return none
where
  mkRatLit (n : Nat) : Q(Rat) :=
    let lit : Q(Nat) := Lean.mkRawNatLit n
    q(OfNat.ofNat $lit)
  leftAssocOp (op : Expr) (t : cvc5.Term) : ReconstructM Expr := do
    let mut curr ← reconstructTerm t[0]!
    for i in [1:t.getNumChildren] do
      curr := mkApp2 op curr (← reconstructTerm t[i]!)
    return curr

def reconstructRewrite (pf : cvc5.Proof) : ReconstructM (Option Expr) := do
  match pf.getRewriteRule! with
  | .ARITH_POW_ELIM =>
    if pf.getResult[0]![0]!.getSort!.isInteger then return none
    let x : Q(Rat) ← reconstructTerm pf.getResult[0]![0]!
    let c : Q(Nat) ← reconstructTerm pf.getResult[0]![1]!
    addPropThm pf.getResult q(Eq.refl ($x ^ $c))
  | .ARITH_DIV_TOTAL_ZERO_REAL =>
    let x : Q(Rat) ← reconstructTerm pf.getArguments[1]!
    addPropThm pf.getResult q(@Rewrite.div_total_zero $x)
  | .ARITH_ELIM_GT =>
    if pf.getArguments[1]!.getSort!.isInteger then return none
    let t : Q(Rat) ← reconstructTerm pf.getArguments[1]!
    let s : Q(Rat) ← reconstructTerm pf.getArguments[2]!
    addPropThm pf.getResult q(@Rewrite.elim_gt $t $s)
  | .ARITH_ELIM_LT =>
    if pf.getArguments[1]!.getSort!.isInteger then return none
    let t : Q(Rat) ← reconstructTerm pf.getArguments[1]!
    let s : Q(Rat) ← reconstructTerm pf.getArguments[2]!
    addPropThm pf.getResult q(@Rewrite.elim_lt $t $s)
  | .ARITH_ELIM_LEQ =>
    if pf.getArguments[1]!.getSort!.isInteger then return none
    let t : Q(Rat) ← reconstructTerm pf.getArguments[1]!
    let s : Q(Rat) ← reconstructTerm pf.getArguments[2]!
    addPropThm pf.getResult q(@Rewrite.elim_leq $t $s)
  | .ARITH_GEQ_NORM1_REAL =>
    let t : Q(Rat) ← reconstructTerm pf.getArguments[1]!
    let s : Q(Rat) ← reconstructTerm pf.getArguments[2]!
    addPropThm pf.getResult q(@Rewrite.geq_norm1 $t $s)
  | .ARITH_EQ_ELIM_REAL =>
    let t : Q(Rat) ← reconstructTerm pf.getArguments[1]!
    let s : Q(Rat) ← reconstructTerm pf.getArguments[2]!
    addPropThm pf.getResult q(@Rewrite.eq_elim $t $s)
  | .ARITH_INT_EQ_CONFLICT =>
    let t : Q(Int) ← reconstructTerm pf.getArguments[1]!
    let c : Q(Rat) ← reconstructTerm pf.getArguments[2]!
    let h : Q((↑«$c».floor = $c) = False) ← reconstructPropProof pf.getChildren[0]!
    addPropThm pf.getResult q(@Rewrite.eq_conflict $t $c $h)
  | .ARITH_INT_GEQ_TIGHTEN =>
    let t : Q(Int) ← reconstructTerm pf.getArguments[1]!
    let c : Q(Rat) ← reconstructTerm pf.getArguments[2]!
    let cc : Q(Int) ← reconstructTerm pf.getArguments[3]!
    let hc : Q((↑«$c».floor = $c) = False) ← reconstructPropProof pf.getChildren[0]!
    let hcc : Q($cc = Int.addN [«$c».floor, 1]) ← reconstructPropProof pf.getChildren[1]!
    addPropThm pf.getResult q(@Rewrite.geq_tighten $t $c $cc $hc $hcc)
  | .ARITH_ABS_EQ =>
    if pf.getArguments[1]!.getSort!.isInteger then return none
    let x : Q(Rat) ← reconstructTerm pf.getArguments[1]!
    let y : Q(Rat) ← reconstructTerm pf.getArguments[2]!
    addPropThm pf.getResult q(@Rewrite.abs_eq $x $y)
  | .ARITH_ABS_REAL_GT =>
    let x : Q(Rat) ← reconstructTerm pf.getArguments[1]!
    let y : Q(Rat) ← reconstructTerm pf.getArguments[2]!
    addEqThm pf.getResult q(@Rewrite.abs_gt_cond $x $y)
  | .ARITH_GEQ_ITE_LIFT =>
    if pf.getArguments[2]!.getSort!.isInteger then return none
    let c : Q(Bool) ← reconstructTerm pf.getArguments[1]!
    let t : Q(Rat) ← reconstructTerm pf.getArguments[2]!
    let s : Q(Rat) ← reconstructTerm pf.getArguments[3]!
    let r : Q(Rat) ← reconstructTerm pf.getArguments[4]!
    addEqThm pf.getResult q(@Bool.geq_cond_lift Rat _ $c $t $s $r)
  | .ARITH_LEQ_ITE_LIFT =>
    if pf.getArguments[2]!.getSort!.isInteger then return none
    let c : Q(Bool) ← reconstructTerm pf.getArguments[1]!
    let t : Q(Rat) ← reconstructTerm pf.getArguments[2]!
    let s : Q(Rat) ← reconstructTerm pf.getArguments[3]!
    let r : Q(Rat) ← reconstructTerm pf.getArguments[4]!
    addEqThm pf.getResult q(@Bool.leq_cond_lift Rat _ $c $t $s $r)
  | .ARITH_MIN_LT1 =>
    if pf.getArguments[1]!.getSort!.isInteger then return none
    let t : Q(Rat) ← reconstructTerm pf.getArguments[1]!
    let s : Q(Rat) ← reconstructTerm pf.getArguments[2]!
    addEqThm pf.getResult q(@Rewrite.min_lt1_cond $t $s)
  | .ARITH_MIN_LT2 =>
    if pf.getArguments[1]!.getSort!.isInteger then return none
    let t : Q(Rat) ← reconstructTerm pf.getArguments[1]!
    let s : Q(Rat) ← reconstructTerm pf.getArguments[2]!
    addEqThm pf.getResult q(@Rewrite.min_lt2_cond $t $s)
  | .ARITH_MAX_GEQ1 =>
    if pf.getArguments[1]!.getSort!.isInteger then return none
    let t : Q(Rat) ← reconstructTerm pf.getArguments[1]!
    let s : Q(Rat) ← reconstructTerm pf.getArguments[2]!
    addEqThm pf.getResult q(@Rewrite.max_geq1_cond $t $s)
  | .ARITH_MAX_GEQ2 =>
    if pf.getArguments[1]!.getSort!.isInteger then return none
    let t : Q(Rat) ← reconstructTerm pf.getArguments[1]!
    let s : Q(Rat) ← reconstructTerm pf.getArguments[2]!
    addEqThm pf.getResult q(@Rewrite.max_geq2_cond $t $s)
  | _ => return none

def reconstructSumUB (pf : cvc5.Proof) : ReconstructM (Option Expr) := do
  let f := fun (ks, ls, rs, hs) p => do
    let l : Q(Rat) ← reconstructTerm p.getResult[0]!
    let r : Q(Rat) ← reconstructTerm p.getResult[1]!
    let lsl := q($ls + $l)
    let rsr := q($rs + $r)
    let k := p.getResult.getKind!
    if ks == .LT && k == .LT then
      let hs : Q($ls < $rs) := hs
      let h : Q($l < $r) ← reconstructPropProof p
      return (.LT, lsl, rsr, q(Rat.sum_ub₁ $hs $h))
    else if ks == .LT && k == .LEQ then
      let hs : Q($ls < $rs) := hs
      let h : Q($l ≤ $r) ← reconstructPropProof p
      return (.LT, lsl, rsr, q(Rat.sum_ub₂ $hs $h))
    else if ks == .LT && k == .EQUAL then
      let hs : Q($ls < $rs) := hs
      let h : Q($l = $r) ← reconstructPropProof p
      return (.LT, lsl, rsr, q(Rat.sum_ub₃ $hs $h))
    else if ks == .LEQ && k == .LT then
      let hs : Q($ls ≤ $rs) := hs
      let h : Q($l < $r) ← reconstructPropProof p
      return (.LT, lsl, rsr, q(Rat.sum_ub₄ $hs $h))
    else if ks == .LEQ && k == .LEQ then
      let hs : Q($ls ≤ $rs) := hs
      let h : Q($l ≤ $r) ← reconstructPropProof p
      return (.LEQ, lsl, rsr, q(Rat.sum_ub₅ $hs $h))
    else if ks == .LEQ && k == .EQUAL then
      let hs : Q($ls ≤ $rs) := hs
      let h : Q($l = $r) ← reconstructPropProof p
      return (.LEQ, lsl, rsr, q(Rat.sum_ub₆ $hs $h))
    else if ks == .EQUAL && k == .LT then
      let hs : Q($ls = $rs) := hs
      let h : Q($l < $r) ← reconstructPropProof p
      return (.LT, lsl, rsr, q(Rat.sum_ub₇ $hs $h))
    else if ks == .EQUAL && k == .LEQ then
      let hs : Q($ls = $rs) := hs
      let h : Q($l ≤ $r) ← reconstructPropProof p
      return (.LEQ, lsl, rsr, q(Rat.sum_ub₈ $hs $h))
    else if ks == .EQUAL && k == .EQUAL then
      let hs : Q($ls = $rs) := hs
      let h : Q($l = $r) ← reconstructPropProof p
      return (.EQUAL, lsl, rsr, q(Rat.sum_ub₉ $hs $h))
    else
      throwError "[sum_ub]: invalid kinds: {ks}, {k}"
  let k := pf.getChildren[0]!.getResult.getKind!
  let ls : Q(Rat) ← reconstructTerm pf.getChildren[0]!.getResult[0]!
  let rs : Q(Rat) ← reconstructTerm pf.getChildren[0]!.getResult[1]!
  let hs ← reconstructPropProof pf.getChildren[0]!
  let (ks, ls, rs, hs) ← pf.getChildren[1:].foldlM f (k, ls, rs, hs)
  if ks == .EQUAL then
    let hs : Q($ls = $rs) := hs
    addPropThm pf.getResult q(Rat.le_of_eq $hs)
  else
    addPropThm pf.getResult hs

def reconstructMulAbsComparison (pf : cvc5.Proof) : ReconstructM (Option Expr) := do
  let f := fun (ks, ls, rs, hs) p => do
    let k := p.getResult.getKind!
    if ks == .EQUAL && k == .EQUAL then
      let l : Q(Rat) ← reconstructTerm p.getResult[0]![0]!
      let r : Q(Rat) ← reconstructTerm p.getResult[1]![0]!
      let lsl := q($ls * $l)
      let rsr := q($rs * $r)
      let hs : Q(«$ls».abs = «$rs».abs) := hs
      let h : Q(«$l».abs = «$r».abs) ← reconstructPropProof p
      return (.EQUAL, lsl, rsr, q(Rat.mul_abs₁ $hs $h))
    else if ks == .GT && k == .AND then
      let l : Q(Rat) ← reconstructTerm p.getResult[0]![0]![0]!
      let r : Q(Rat) ← reconstructTerm p.getResult[0]![1]![0]!
      let lsl := q($ls * $l)
      let rsr := q($rs * $r)
      let hs : Q(«$ls».abs > «$rs».abs) := hs
      let h : Q(«$l».abs = «$r».abs ∧ «$l».abs ≠ 0) ← reconstructPropProof p
      return (.GT, lsl, rsr, q(Rat.mul_abs₂ $hs $h))
    else if ks == .GT && k == .GT then
      let l : Q(Rat) ← reconstructTerm p.getResult[0]![0]!
      let r : Q(Rat) ← reconstructTerm p.getResult[1]![0]!
      let lsl := q($ls * $l)
      let rsr := q($rs * $r)
      let hs : Q(«$ls».abs > «$rs».abs) := hs
      let h : Q(«$l».abs > «$r».abs) ← reconstructPropProof p
      return (.GT, lsl, rsr, q(Rat.mul_abs₃ $hs $h))
    else
      throwError "[mul_abs]: invalid kinds: {ks}, {k}"
  let k := pf.getChildren[0]!.getResult.getKind!
  let ls : Q(Rat) ← reconstructTerm pf.getChildren[0]!.getResult[0]![0]!
  let rs : Q(Rat) ← reconstructTerm pf.getChildren[0]!.getResult[1]![0]!
  let hs ← reconstructPropProof pf.getChildren[0]!
  let (_, _, _, hs) ← pf.getChildren[1:].foldlM f (k, ls, rs, hs)
  addPropThm pf.getResult hs

def reconstructMulSign (pf : cvc5.Proof) : ReconstructM (Option Expr) := do
  let ts := if pf.getResult[0]!.getKind! == .AND then pf.getResult[0]!.getChildren else #[pf.getResult[0]!]
  let mut hs : Array (Name × (Array Expr → ReconstructM Expr)) := #[]
  let mut map : Std.HashMap cvc5.Term Nat := {}
  for h : i in [0:ts.size] do
    let t := ts[i]
    let p : Q(Prop) ← reconstructProp t
    hs := hs.push (Name.num `a i, fun _ => return p)
    map := map.insert (if t.getKind! == .NOT then t[0]![0]! else t[0]!) i
  let t := pf.getResult[1]!
  let vs := if t[0]!.getKind! == .CONST_INTEGER then t[1]!.getChildren else t[0]!.getChildren
  let f t ps := do
    let p : Q(Prop) ← reconstructProp t
    return q($p :: $ps)
  let ps : Q(List Prop) ← ts.foldrM f q([])
  let q : Q(Prop) ← reconstructProp t
  let h : Q(impliesN $ps $q) ← Meta.withLocalDeclsD hs fun hs => do
    let h : Q($q) ← if ts[map[vs[0]!]!]!.getKind! == .NOT then
        let a : Q(Rat) ← reconstructTerm vs[0]!
        let ha : Q($a ≠ 0) := hs[map[vs[0]!]!]!
        go vs ts hs map .GT q($a * $a) q(Rat.mul_sign₀ $ha) 2
      else
        let a : Q(Rat) ← reconstructTerm vs[0]!
        go vs ts hs map ts[map[vs[0]!]!]!.getKind! a hs[map[vs[0]!]!]! 1
    Meta.mkLambdaFVars hs h
  addPropThm pf.getResult q(Builtin.scopes $h)
where
  go vs ts hs map (ka : cvc5.Kind) (a : Q(Rat)) (ha : Expr) i : ReconstructM Expr := do
    if hi : i < vs.size then
      let b : Q(Rat) ← reconstructTerm vs[i]
      let k : cvc5.Kind := ts[map[vs[i]]!]!.getKind!
      if ka == .LT && k == .LT then
        let ha : Q($a < 0) := ha
        let hb : Q($b < 0) := hs[map[vs[i]]!]!
        go vs ts hs map .GT q($a * $b) q(Rat.mul_sign₁ $ha $hb) (i + 1)
      else if ka == .LT && k == .NOT then
        let ha : Q($a < 0) := ha
        let hb : Q($b ≠ 0) := hs[map[vs[i]]!]!
        go vs ts hs map .LT q($a * $b * $b) q(Rat.mul_sign₂ $ha $hb) (i + 2)
      else if ka == .LT && k == .GT then
        let ha : Q($a < 0) := ha
        let hb : Q($b > 0) := hs[map[vs[i]]!]!
        go vs ts hs map .LT q($a * $b) q(Rat.mul_sign₃ $ha $hb) (i + 1)
      else if ka == .GT && k == .LT then
        let ha : Q($a > 0) := ha
        let hb : Q($b < 0) := hs[map[vs[i]]!]!
        go vs ts hs map .LT q($a * $b) q(Rat.mul_sign₄ $ha $hb) (i + 1)
      else if ka == .GT && k == .NOT then
        let ha : Q($a > 0) := ha
        let hb : Q($b ≠ 0) := hs[map[vs[i]]!]!
        go vs ts hs map .GT q($a * $b * $b) q(Rat.mul_sign₅ $ha $hb) (i + 2)
      else if ka == .GT && k == .GT then
        let ha : Q($a > 0) := ha
        let hb : Q($b > 0) := hs[map[vs[i]]!]!
        go vs ts hs map .GT q($a * $b) q(Rat.mul_sign₆ $ha $hb) (i + 1)
      else
        throwError "[mul_sign]: invalid kinds: {ka}, {k}"
    else
      return ha

def reconstructArithPolyNormRel (pf : cvc5.Proof) : ReconstructM (Option Expr) := do
  let lcx : Rat := pf.getChildren[0]!.getResult[0]![0]!.getRationalValue!
  let cx : Q(Rat) ← reconstructTerm pf.getChildren[0]!.getResult[0]![0]!
  let cy : Q(Rat) ← reconstructTerm pf.getChildren[0]!.getResult[1]![0]!
  let x₁ : Q(Rat) ← reconstructTerm pf.getResult[0]![0]!
  let x₂ : Q(Rat) ← reconstructTerm pf.getResult[0]![1]!
  let y₁ : Q(Rat) ← reconstructTerm pf.getResult[1]![0]!
  let y₂ : Q(Rat) ← reconstructTerm pf.getResult[1]![1]!
  let h : Q($cx * ($x₁ - $x₂) = $cy * ($y₁ - $y₂)) ← reconstructPropProof pf.getChildren[0]!
  let k := pf.getResult[0]!.getKind!
  let (hcx, hcy) :=
    if k == .EQUAL then (q(@of_decide_eq_true ($cx ≠ 0) _), q(@of_decide_eq_true ($cy ≠ 0) _))
    else if lcx > 0 then (q(@of_decide_eq_true ($cx > 0) _), q(@of_decide_eq_true ($cy > 0) _))
    else (q(@of_decide_eq_true ($cx < 0) _), q(@of_decide_eq_true ($cy < 0) _))
  let hcx := .app hcx q(Eq.refl true)
  let hcy := .app hcy q(Eq.refl true)
  let n ← getThmName k pf.getResult[0]![0]!.getSort!.isInteger pf.getResult[1]![0]!.getSort!.isInteger (lcx > 0)
  addPropThm pf.getResult (mkApp9 (.const n []) x₁ x₂ y₁ y₂ cx cy hcx hcy h)
where
  getThmName (k : cvc5.Kind) (il ir sign : Bool) : ReconstructM Name :=
    if k == .LT && il == false && ir == false && sign == true then pure ``Rat.lt_of_sub_eq_pos
    else if k == .LT && il == false && ir == false && sign == false then pure ``Rat.lt_of_sub_eq_neg
    else if k == .LT && il == false && ir == true && sign == true then pure ``Rat.lt_of_sub_eq_pos_int_right
    else if k == .LT && il == false && ir == true && sign == false then pure ``Rat.lt_of_sub_eq_neg_int_right
    else if k == .LT && il == true && ir == false && sign == true then pure ``Rat.lt_of_sub_eq_pos_int_left
    else if k == .LT && il == true && ir == false && sign == false then pure ``Rat.lt_of_sub_eq_neg_int_left
    else if k == .LEQ && il == false && ir == false && sign == true then pure ``Rat.le_of_sub_eq_pos
    else if k == .LEQ && il == false && ir == false && sign == false then pure ``Rat.le_of_sub_eq_neg
    else if k == .LEQ && il == false && ir == true && sign == true then pure ``Rat.le_of_sub_eq_pos_int_right
    else if k == .LEQ && il == false && ir == true && sign == false then pure ``Rat.le_of_sub_eq_neg_int_right
    else if k == .LEQ && il == true && ir == false && sign == true then pure ``Rat.le_of_sub_eq_pos_int_left
    else if k == .LEQ && il == true && ir == false && sign == false then pure ``Rat.le_of_sub_eq_neg_int_left
    else if k == .EQUAL && il == false && ir == false then pure ``Rat.eq_of_sub_eq
    else if k == .EQUAL && il == false && ir == true then pure ``Rat.eq_of_sub_eq_int_right
    else if k == .EQUAL && il == true && ir == false then pure ``Rat.eq_of_sub_eq_int_left
    else if k == .GEQ && il == false && ir == false && sign == true then pure ``Rat.ge_of_sub_eq_pos
    else if k == .GEQ && il == false && ir == false && sign == false then pure ``Rat.ge_of_sub_eq_neg
    else if k == .GEQ && il == false && ir == true && sign == true then pure ``Rat.ge_of_sub_eq_pos_int_right
    else if k == .GEQ && il == false && ir == true && sign == false then pure ``Rat.ge_of_sub_eq_neg_int_right
    else if k == .GEQ && il == true && ir == false && sign == true then pure ``Rat.ge_of_sub_eq_pos_int_left
    else if k == .GEQ && il == true && ir == false && sign == false then pure ``Rat.ge_of_sub_eq_neg_int_left
    else if k == .GT && il == false && ir == false && sign == true then pure ``Rat.gt_of_sub_eq_pos
    else if k == .GT && il == false && ir == false && sign == false then pure ``Rat.gt_of_sub_eq_neg
    else if k == .GT && il == false && ir == true && sign == true then pure ``Rat.gt_of_sub_eq_pos_int_right
    else if k == .GT && il == false && ir == true && sign == false then pure ``Rat.gt_of_sub_eq_neg_int_right
    else if k == .GT && il == true && ir == false && sign == true then pure ``Rat.gt_of_sub_eq_pos_int_left
    else if k == .GT && il == true && ir == false && sign == false then pure ``Rat.gt_of_sub_eq_neg_int_left
    else throwError "[arith_poly_norm_rel]: invalid combination of kind, integer operands, and sign: {k}, {il}, {ir}, {sign}"

@[smt_proof_reconstruct] def reconstructRatProof : ProofReconstructor := fun pf => do match pf.getRule with
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
    let c : Q(Rat) ← reconstructTerm pf.getChildren[0]!.getResult[1]!
    let h : Q($i < $c) ← reconstructPropProof pf.getChildren[0]!
    addPropThm pf.getResult q(@Rat.int_tight_ub $c $i $h)
  | .INT_TIGHT_LB =>
    if pf.getChildren[0]!.getResult[1]!.getSort!.isInteger then return none
    let i : Q(Int) ← reconstructTerm pf.getChildren[0]!.getResult[0]!
    let c : Q(Rat) ← reconstructTerm pf.getChildren[0]!.getResult[1]!
    let h : Q($i > $c) ← reconstructPropProof pf.getChildren[0]!
    addPropThm pf.getResult q(@Rat.int_tight_lb $c $i $h)
  | .ARITH_TRICHOTOMY =>
    if pf.getResult[0]!.getSort!.isInteger then return none
    let x : Q(Rat) ← reconstructTerm pf.getResult[0]!
    let c : Q(Rat) ← reconstructTerm pf.getResult[1]!
    let k₁ := pf.getChildren[0]!.getResult.getKind!
    let k₂ := pf.getChildren[1]!.getResult.getKind!
    if k₁ == .LEQ && k₂ == .NOT then
      let h₁ : Q($x ≤ $c) ← reconstructPropProof pf.getChildren[0]!
      let h₂ : Q($x ≠ $c) ← reconstructPropProof pf.getChildren[1]!
      addPropThm pf.getResult q(Rat.trichotomy₁ $h₁ $h₂)
    else if k₁ == .LEQ && k₂ == .GEQ then
      let h₁ : Q($x ≤ $c) ← reconstructPropProof pf.getChildren[0]!
      let h₂ : Q($x ≥ $c) ← reconstructPropProof pf.getChildren[1]!
      addPropThm pf.getResult q(Rat.trichotomy₂ $h₁ $h₂)
    else if k₁ == .NOT && k₂ == .LEQ then
      let h₁ : Q($x ≠ $c) ← reconstructPropProof pf.getChildren[0]!
      let h₂ : Q($x ≤ $c) ← reconstructPropProof pf.getChildren[1]!
      addPropThm pf.getResult q(Rat.trichotomy₃ $h₁ $h₂)
    else if k₁ == .NOT && k₂ == .GEQ then
      let h₁ : Q($x ≠ $c) ← reconstructPropProof pf.getChildren[0]!
      let h₂ : Q($x ≥ $c) ← reconstructPropProof pf.getChildren[1]!
      addPropThm pf.getResult q(Rat.trichotomy₄ $h₁ $h₂)
    else if k₁ == .GEQ && k₂ == .LEQ then
      let h₁ : Q($x ≥ $c) ← reconstructPropProof pf.getChildren[0]!
      let h₂ : Q($x ≤ $c) ← reconstructPropProof pf.getChildren[1]!
      addPropThm pf.getResult q(Rat.trichotomy₅ $h₁ $h₂)
    else if k₁ == .GEQ && k₂ == .NOT then
      let h₁ : Q($x ≥ $c) ← reconstructPropProof pf.getChildren[0]!
      let h₂ : Q($x ≠ $c) ← reconstructPropProof pf.getChildren[1]!
      addPropThm pf.getResult q(Rat.trichotomy₆ $h₁ $h₂)
    else
      return none
  | .ARITH_REDUCTION =>
    if pf.getArguments[0]!.getSort!.isInteger then return none
    if pf.getArguments[0]!.getKind! == .ABS then
      let x : Q(Rat) ← reconstructTerm pf.getArguments[0]![0]!
      addPropThm pf.getResult q(@Rat.abs_elim_cond $x)
    else
      return none
  | .ARITH_POLY_NORM =>
    if pf.getResult[0]!.getSort!.isInteger then return none
    let tac := if ← useNative then Rat.nativePolyNorm else Rat.polyNorm
    addPropTac pf.getResult tac
  | .ARITH_POLY_NORM_REL =>
    if pf.getChildren[0]!.getResult[0]![0]!.getSort!.isInteger then return none
    reconstructArithPolyNormRel pf
  | .ARITH_MULT_SIGN =>
    if pf.getResult[1]![0]!.getSort!.isInteger then return none
    reconstructMulSign pf
  | .ARITH_MULT_POS =>
    if pf.getArguments[0]!.getSort!.isInteger then return none
    let m : Q(Rat) ← reconstructTerm pf.getArguments[0]!
    let l : Q(Rat) ← reconstructTerm pf.getArguments[1]![0]!
    let r : Q(Rat) ← reconstructTerm pf.getArguments[1]![1]!
    match pf.getArguments[1]!.getKind! with
    | .LT =>
      addPropThm pf.getResult q(@Rat.mul_pos_lt $l $r $m)
    | .LEQ =>
      addPropThm pf.getResult q(@Rat.mul_pos_le $l $r $m)
    | .EQUAL =>
      addPropThm pf.getResult q(@Rat.mul_pos_eq $l $r $m)
    | .GEQ =>
      addPropThm pf.getResult q(@Rat.mul_pos_ge $l $r $m)
    | .GT =>
      addPropThm pf.getResult q(@Rat.mul_pos_gt $l $r $m)
    | _ => return none
  | .ARITH_MULT_NEG =>
    if pf.getArguments[0]!.getSort!.isInteger then return none
    let m : Q(Rat) ← reconstructTerm pf.getArguments[0]!
    let l : Q(Rat) ← reconstructTerm pf.getArguments[1]![0]!
    let r : Q(Rat) ← reconstructTerm pf.getArguments[1]![1]!
    match pf.getArguments[1]!.getKind! with
    | .LT =>
      addPropThm pf.getResult q(@Rat.mul_neg_lt $l $r $m)
    | .LEQ =>
      addPropThm pf.getResult q(@Rat.mul_neg_le $l $r $m)
    | .EQUAL =>
      addPropThm pf.getResult q(@Rat.mul_neg_eq $l $r $m)
    | .GEQ =>
      addPropThm pf.getResult q(@Rat.mul_neg_ge $l $r $m)
    | .GT =>
      addPropThm pf.getResult q(@Rat.mul_neg_gt $l $r $m)
    | _ => return none
  | .ARITH_MULT_TANGENT =>
    let x : Q(Rat) ← reconstructTerm pf.getArguments[0]!
    let y : Q(Rat) ← reconstructTerm pf.getArguments[1]!
    let a : Q(Rat) ← reconstructTerm pf.getArguments[2]!
    let b : Q(Rat) ← reconstructTerm pf.getArguments[3]!
    if pf.getArguments[4]!.getBooleanValue! == false then
      addPropThm pf.getResult q(@Rat.mul_tangent_lower_eq $a $b $x $y)
    else
      addPropThm pf.getResult q(@Rat.mul_tangent_upper_eq $a $b $x $y)
  | _ => return none

end Smt.Reconstruct.Rat
