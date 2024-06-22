/-
Copyright (c) 2021-2024 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

import Mathlib.Data.Real.Basic

import Lean
import Qq

namespace Smt.Reconstruct.Real.PolyNorm

abbrev Var := Nat

def Context := Var → Real

structure Monomial where
  coeff : Rat
  vars : List Var
deriving Inhabited, Repr

namespace Monomial

open Qq in
def toExpr (m : Monomial) (ppCtx : Var → Q(Rat)) : Q(Rat) :=
  if h : m.vars = [] then
    toExprCoeff m.coeff
  else
    if m.coeff = 1 then
      (m.vars.drop 1).foldl (fun acc v => q($acc * $(ppCtx v))) (ppCtx (m.vars.head h))
    else
      m.vars.foldl (fun acc v => q($acc * $(ppCtx v))) (toExprCoeff m.coeff)
where
  toExprCoeff (c : Rat) : Q(Rat) :=
  let num : Q(Rat) := mkRatLit c.num.natAbs
  if c.den == 1 then
    if c.num ≥ 0 then
      q($num)
    else
      q(-$num)
  else
    let den : Q(Rat) := mkRatLit c.den
    if c.num ≥ 0 then
      q($num / $den)
    else
      q(-$num / $den)
  mkRatLit (n : Nat) : Q(Rat) :=
    let l : Q(Nat) := Lean.mkRawNatLit n
    q(OfNat.ofNat $l)

def neg (m : Monomial) : Monomial :=
  { m with coeff := -m.coeff }

def add (m₁ m₂ : Monomial) (_ : m₁.vars = m₂.vars) : Monomial :=
  { coeff := m₁.coeff + m₂.coeff, vars := m₁.vars }

-- Invariant: monomial variables remain sorted.
def mul (m₁ m₂ : Monomial) : Monomial :=
  let coeff := m₁.coeff * m₂.coeff
  let vars := m₁.vars.foldr insert m₂.vars
  { coeff, vars }
where
  insert (x : Var) : List Var → List Var
    | [] => [x]
    | y :: ys => if x ≤ y then x :: y :: ys else y :: insert x ys

def divConst (m : Monomial) (c : Rat) : Monomial :=
  { m with coeff := m.coeff / c }

def denote (ctx : Context) (m : Monomial) : Real :=
  m.coeff * m.vars.foldl (fun acc v => acc * ctx v) 1

theorem denote_neg {m : Monomial} : m.neg.denote ctx = -m.denote ctx := by
  simp only [neg, denote, neg_mul_eq_neg_mul]
  sorry

theorem denote_mul {m₁ m₂ : Monomial} : (m₁.mul m₂).denote ctx = m₁.denote ctx * m₂.denote ctx :=
  sorry

theorem denote_divConst {m : Monomial} : (m.divConst c).denote ctx = m.denote ctx / c :=
  sorry

end Monomial

abbrev Polynomial := List Monomial

namespace Polynomial

open Qq in
def toExpr (p : Polynomial) (ppCtx : Var → Q(Real)) : Q(Real) :=
  go p
where
  go : Polynomial → Q(Real)
    | [] => q(0)
    | [m] => m.toExpr ppCtx
    | m :: ms =>q($(m.toExpr ppCtx) + $(go ms))

def neg (p : Polynomial) : Polynomial :=
  p.map Monomial.neg

-- NOTE: implementation merges monomials with same variables.
-- Invariant: monomials remain sorted.
def add (p q : Polynomial) : Polynomial :=
  p.foldr insert q
where
  insert (m : Monomial) : Polynomial → Polynomial
    | [] => [m]
    | n :: ns =>
      if m.vars < n.vars then
        m :: n :: ns
      else if h : m.vars = n.vars then
        let m' := m.add n h
        if m'.coeff = 0 then ns else m' :: ns
      else
        n :: insert m ns

def sub (p q : Polynomial) : Polynomial :=
  p.add q.neg

-- Invariant: monomials remain sorted.
def mulMonomial (m : Monomial) (p : Polynomial) : Polynomial :=
  p.foldr (fun n acc => Polynomial.add [m.mul n] acc) []

-- Invariant: monomials remain sorted.
def mul (p q : Polynomial) : Polynomial :=
  p.foldl (fun acc m => (q.mulMonomial m).add acc) []

def divConst (p : Polynomial) (c : Rat) : Polynomial :=
  p.map (·.divConst c)

def denote (ctx : Context) (p : Polynomial) : Real :=
  p.foldl (fun acc m => acc + m.denote ctx) 0

theorem denote_neg {p : Polynomial} : p.neg.denote ctx = -p.denote ctx :=
  sorry

theorem denote_add {p q : Polynomial} : (p.add q).denote ctx = p.denote ctx + q.denote ctx :=
  sorry

theorem denote_sub {p q : Polynomial} : (p.sub q).denote ctx = p.denote ctx - q.denote ctx := by
  simp only [sub, denote_neg, denote_add, sub_eq_add_neg]

theorem denote_mulMonomial {p : Polynomial} : (p.mulMonomial m).denote ctx = m.denote ctx * p.denote ctx :=
  sorry

theorem denote_mul {p q : Polynomial} : (p.mul q).denote ctx = p.denote ctx * q.denote ctx :=
  sorry

theorem denote_divConst {p : Polynomial} : (p.divConst c).denote ctx = p.denote ctx / c := by
  sorry

end Polynomial

inductive Expr where
  | val (v : Rat)
  | var (v : Nat)
  | neg (a : Expr)
  | add (a b : Expr)
  | sub (a b : Expr)
  | mul (a b : Expr)
  | divConst (a : Expr) (c : Rat)
deriving Inhabited, Repr

namespace Expr

def toPolynomial : Expr → Polynomial
  | val v => if v = 0 then [] else [{ coeff := v, vars := [] }]
  | var v => [{ coeff := 1, vars := [v] }]
  | neg a => a.toPolynomial.neg
  | add a b => Polynomial.add a.toPolynomial b.toPolynomial
  | sub a b => Polynomial.sub a.toPolynomial b.toPolynomial
  | mul a b => Polynomial.mul a.toPolynomial b.toPolynomial
  | divConst a c => Polynomial.divConst a.toPolynomial c

def denote (ctx : Context) : Expr → Real
  | val v => v
  | var v => ctx v
  | neg a => -a.denote ctx
  | add a b => a.denote ctx + b.denote ctx
  | sub a b => a.denote ctx - b.denote ctx
  | mul a b => a.denote ctx * b.denote ctx
  | divConst a c => a.denote ctx * (1 / c : Rat)

theorem denote_toPolynomial {e : Expr} : e.denote ctx = e.toPolynomial.denote ctx := by
  induction e with
  | val v =>
    simp only [denote, toPolynomial]
    split <;> rename_i hv
    · rewrite [hv]; norm_num; rfl
    · simp [Polynomial.denote, Monomial.denote]
  | var v =>
    simp [denote, toPolynomial, Polynomial.denote, Monomial.denote]
  | neg a ih =>
    simp only [denote, toPolynomial, Polynomial.denote_neg, ih]
  | add a b ih₁ ih₂ =>
    simp only [denote, toPolynomial, Polynomial.denote_add, ih₁, ih₂]
  | sub a b ih₁ ih₂ =>
    simp only [denote, toPolynomial, Polynomial.denote_sub, ih₁, ih₂]
  | mul a b ih₁ ih₂ =>
    simp only [denote, toPolynomial, Polynomial.denote_mul, ih₁, ih₂]
  | divConst a c ih =>
    simp only [denote, toPolynomial, Polynomial.denote_divConst, ih]
    norm_num
    rfl

theorem denote_eq_from_toPolynomial_eq {e₁ e₂ : Expr} (h : e₁.toPolynomial = e₂.toPolynomial) : e₁.denote ctx = e₂.denote ctx := by
  rw [denote_toPolynomial, denote_toPolynomial, h]

end PolyNorm.Expr

open Lean hiding Rat
open Qq

abbrev PolyM := StateT (Array Q(Real)) MetaM

def getIndex (e : Q(Real)) : PolyM Nat := do
  let es ← get
  if let some i := es.findIdx? (· == e) then
    return i
  else
    let size := es.size
    set (es.push e)
    return size

partial def toRatConst (e : Q(Real)) : PolyM Rat := do
  match e with
  | ~q(0) => pure 0
  | ~q(1) => pure 1
  | ~q(@OfNat.ofNat _ _ (@instOfNatAtLeastTwo _ _ _ instNatAtLeastTwo)) =>
    pure (e.getArg! 1).rawNatLit?.get!
  | ~q(-$x) => pure (-(← toRatConst x))
  | ~q($x + $y) => pure ((← toRatConst x) + (← toRatConst y))
  | ~q($x - $y) => pure ((← toRatConst x) - (← toRatConst y))
  | ~q($x * $y) => pure ((← toRatConst x) * (← toRatConst y))
  | ~q($x / $y) => pure ((← toRatConst x) / (← toRatConst y))
  | e => throwError "[poly_norm] a expected Real number, got {e}"

partial def toArithExpr (e : Q(Real)) : PolyM Q(PolyNorm.Expr) := do
  match e with
  | ~q(0) => pure q(.val (@OfNat.ofNat Rat 0 _))
  | ~q(1) => pure q(.val (@OfNat.ofNat Rat 1 _))
  | ~q(@OfNat.ofNat _ _ (@instOfNatAtLeastTwo _ _ _ instNatAtLeastTwo)) =>
    let n : Q(Nat) := (e.getArg! 1); pure q(.val (@OfNat.ofNat Rat $n _))
  | ~q(-$x) => pure q(.neg $(← toArithExpr x))
  | ~q($x + $y) => pure q(.add $(← toArithExpr x) $(← toArithExpr y))
  | ~q($x - $y) => pure q(.sub $(← toArithExpr x) $(← toArithExpr y))
  | ~q($x * $y) => pure q(.mul $(← toArithExpr x) $(← toArithExpr y))
  | ~q($x / $y) => pure q(.divConst $(← toArithExpr x) $(PolyNorm.Monomial.toExpr.toExprCoeff (← toRatConst y)))
  | e => let v : Nat ← getIndex e; pure q(.var $v)

def polyNorm (mv : MVarId) : MetaM Unit := do
  let some (_, l, r) := (← mv.getType).eq?
    | throwError "[poly_norm] expected an equality, got {← mv.getType}"
  let (l, es) ← (toArithExpr l).run #[]
  let (r, es) ← (toArithExpr r).run es
  let is : Q(Array Real) := es.foldl (fun acc e => q(«$acc».push $e)) q(#[])
  let ctx : Q(PolyNorm.Context) := q(fun v => if h : v < «$is».size then $is[v] else 0)
  let h : Q(«$l».toPolynomial = «$r».toPolynomial) := .app q(@Eq.refl.{1} PolyNorm.Polynomial) q(«$l».toPolynomial)
  mv.assign q(@PolyNorm.Expr.denote_eq_from_toPolynomial_eq $ctx $l $r $h)
where
  logPolynomial (e : Q(PolyNorm.Expr)) (es : Array Q(Real)) := do
  let p ← unsafe Meta.evalExpr PolyNorm.Expr q(PolyNorm.Expr) e
  let ppCtx := fun v => if h : v < es.size then es[v] else q(0)
  logInfo m!"poly := {PolyNorm.Polynomial.toExpr p.toPolynomial ppCtx}"

namespace Tactic

syntax (name := polyNorm) "poly_norm" : tactic

open Lean.Elab Tactic in
@[tactic polyNorm] def evalPolyNorm : Tactic := fun _ =>
  withMainContext do
    let mv ← Tactic.getMainGoal
    Real.polyNorm mv
    replaceMainGoal []

end Smt.Reconstruct.Real.Tactic

example (x y z : Real) : 1 * (x + y) * z / 4  = 1/(2 * 2) * (z * y + x * z) := by
  poly_norm
