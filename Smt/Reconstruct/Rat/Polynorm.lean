/-
Copyright (c) 2021-2024 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed, Harun Khan
-/

import Smt.Reconstruct.Rat.Core

namespace Smt.Reconstruct.Rat.PolyNorm

structure Var where
  type : Bool
  val  : Nat
deriving DecidableEq, Repr

instance : LE Var where
  le v₁ v₂ := v₁.type < v₂.type ∨ (v₁.type = v₂.type ∧ v₁.val ≤ v₂.val)

instance : LT Var where
  lt v₁ v₂ := v₁.type < v₂.type ∨ (v₁.type = v₂.type ∧ v₁.val < v₂.val)

instance (v₁ v₂ : Var) : Decidable (v₁ ≤ v₂) :=
  if h : v₁.type < v₂.type ∨ (v₁.type = v₂.type ∧ v₁.val ≤ v₂.val) then isTrue h else isFalse h

instance (v₁ v₂ : Var) : Decidable (v₁ < v₂) :=
  if h : v₁.type < v₂.type ∨ (v₁.type = v₂.type ∧ v₁.val < v₂.val) then isTrue h else isFalse h

def Context := Var → Rat

def IntContext := Nat → Int
def RatContext := Nat → Rat

structure Monomial where
  coeff : Rat
  vars : List Var
deriving Inhabited, Repr, DecidableEq

namespace Monomial

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

def denote (ctx : Context) (m : Monomial) : Rat :=
  m.coeff * m.vars.foldl (fun acc v => acc * ctx v) 1

theorem denote_neg {m : Monomial} : m.neg.denote ctx = -m.denote ctx := by
  simp only [neg, denote, Rat.neg_mul_eq_neg_mul]

section

variable {op : α → α → α}

-- Can be generalized to `List.foldl_assoc`.
theorem foldl_assoc {g : β → α} (assoc : ∀ a b c, op (op a b) c = op a (op b c)) (z1 z2 : α):
  List.foldl (fun z a => op z (g a)) (op z1 z2) l =
  op z1 (List.foldl (fun z a => op z (g a)) z2 l) := by
  induction l generalizing z1 z2 with
  | nil => rfl
  | cons y ys ih =>
    simp only [List.foldl_cons, ih, assoc]

theorem foldr_assoc {g : β → α} (assoc : ∀ a b c, op (op a b) c = op a (op b c)) (z1 z2 : α):
  List.foldr (fun z a => op a (g z)) (op z1 z2) l =
  op z1 (List.foldr (fun z a => op a (g z)) z2 l) := by
  induction l generalizing z1 z2 with
  | nil => rfl
  | cons y ys ih =>
    simp only [List.foldr_cons, ih, assoc]

end
-- Can be generalized.
theorem foldl_mul_insert {ctx : Context} :
  List.foldl (fun z a => z * (ctx a)) 1 (mul.insert y ys) =
  (ctx y) * List.foldl (fun z a => z * (ctx a)) 1 ys := by
  induction ys with
  | nil => simp [List.foldl]
  | cons x ys ih =>
    by_cases h : y ≤ x
    · simp [mul.insert, h, foldl_assoc Rat.mul_assoc (ctx y) (ctx x), Rat.mul_assoc]
    · simp only [mul.insert, h, List.foldl_cons, ite_false, Rat.mul_comm,
                 foldl_assoc Rat.mul_assoc, ih]
      rw [← Rat.mul_assoc, Rat.mul_comm (ctx x) (ctx y), Rat.mul_assoc]

theorem denote_add {m n : Monomial} (h : m.vars = n.vars) :
  (m.add n h).denote ctx = m.denote ctx + n.denote ctx := by
  simp only [add, denote, Rat.add_mul, h]

theorem denote_mul {m₁ m₂ : Monomial} : (m₁.mul m₂).denote ctx = m₁.denote ctx * m₂.denote ctx := by
  simp only [denote, mul, Rat.mul_assoc]; congr 1
  rw [← Rat.mul_assoc, Rat.mul_comm _ m₂.coeff, Rat.mul_assoc]; congr 1
  induction m₁.vars with
  | nil => simp [Rat.mul_assoc]
  | cons y ys ih =>
    simp [foldl_mul_insert, ←foldl_assoc Rat.mul_assoc, ih]

theorem denote_divConst {m : Monomial} : (m.divConst c).denote ctx = m.denote ctx / c := by
  simp only [denote, divConst, Rat.mul_div_right_comm]

end Monomial

abbrev Polynomial := List Monomial

namespace Polynomial

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

def denote (ctx : Context) (p : Polynomial) : Rat :=
  p.foldl (fun acc m => acc + m.denote ctx) 0

theorem foldl_add_insert (ctx : Context) :
  List.foldl (fun z a => z + (Monomial.denote ctx a)) 0 (add.insert m p) =
  (Monomial.denote ctx m) + List.foldl (fun z a => z + (Monomial.denote ctx a)) 0 p := by
  induction p with
  | nil => simp [add.insert]
  | cons n p ih =>
    simp only [add.insert]
    split <;> rename_i hlt <;> simp only [List.foldl_cons, Rat.add_comm 0, Monomial.foldl_assoc Rat.add_assoc]
    · split <;> rename_i heq
      · split <;> rename_i hneq
        · rw [←Rat.add_assoc, Rat.add_comm, ←Monomial.denote_add heq]
          simp [Monomial.denote, hneq]
        · simp only [List.foldl_cons, Rat.add_comm 0, Monomial.foldl_assoc Rat.add_assoc, Monomial.denote_add, heq, Rat.add_assoc]
      · simp only [List.foldl_cons, Rat.add_comm 0, ih, Monomial.foldl_assoc Rat.add_assoc]
        rw [←Rat.add_assoc, Rat.add_comm (Monomial.denote ctx n), Rat.add_assoc]

theorem denote_neg {p : Polynomial} : p.neg.denote ctx = -p.denote ctx := by
  simp only [denote, neg]
  induction p with
  | nil => simp
  | cons m p ih =>
    simp only [List.foldl_cons, Rat.add_comm 0, Monomial.foldl_assoc Rat.add_assoc, Rat.neg_add, ←ih, List.map, Monomial.denote_neg]

theorem denote_add {p q : Polynomial} : (p.add q).denote ctx = p.denote ctx + q.denote ctx := by
  simp only [denote, add]
  induction p with
  | nil => simp [add.insert]
  | cons x ys ih =>
    simp only [List.foldr_cons, List.foldl_cons, Rat.add_comm 0, Monomial.foldl_assoc Rat.add_assoc, Rat.add_assoc]
    rw [← ih, foldl_add_insert]

theorem denote_sub {p q : Polynomial} : (p.sub q).denote ctx = p.denote ctx - q.denote ctx := by
  sorry

theorem denote_mulMonomial {p : Polynomial} : (p.mulMonomial m).denote ctx = m.denote ctx * p.denote ctx := by
  simp only [denote, mulMonomial, add]
  induction p with
  | nil => simp
  | cons n p ih =>
    simp only [List.foldl_cons, List.foldr_cons, Rat.add_comm 0, Monomial.foldl_assoc Rat.add_assoc, Rat.mul_add, ←ih]
    simp [foldl_add_insert, Monomial.denote_mul]

theorem denote_cons {p : List Monomial} {ctx : Context} : denote ctx (m :: p) = m.denote ctx + denote ctx p := by
  simp only [denote, List.foldl_cons, Rat.add_comm 0, Monomial.foldl_assoc Rat.add_assoc]

theorem denote_nil_add : denote ctx (p.add []) = denote ctx p := by
  induction p with
  | nil => simp [add]
  | cons n p ih =>
    simp [denote_add, List.foldr_cons, denote_cons, ih, show denote ctx [] = 0 by rfl]

theorem denote_add_insert {g : Monomial → Polynomial} :
  denote ctx (List.foldl (fun acc m => (g m).add acc) n p) = denote ctx n + denote ctx (List.foldl (fun acc m => (g m).add acc) [] p) := by
  revert n
  induction p with
  | nil => simp [denote]
  | cons k p ih =>
    intro n
    simp only [List.foldl_cons, List.foldr, @ih n]
    rw [ih, @ih ((g k).add []), ← Rat.add_assoc, denote_nil_add, denote_add, Rat.add_comm _ (denote ctx n)]

theorem denote_foldl {g : Monomial → Polynomial} :
  denote ctx (List.foldl (fun acc m => ((g m).add (acc))) [] p) = List.foldl (fun acc m => (g m).denote ctx + acc) 0 p := by
  induction p with
  | nil => simp [denote]
  | cons n p ih =>
    simp only [List.foldl_cons, Rat.add_comm, List.foldr] at *
    rw [Rat.add_comm 0, Monomial.foldl_assoc Rat.add_assoc, ←ih, denote_add_insert, denote_nil_add]

theorem denote_mul {p q : Polynomial} : (p.mul q).denote ctx = p.denote ctx * q.denote ctx :=by
  simp only [mul]
  induction p with
  | nil => simp [denote]
  | cons n p ih =>
    simp only [List.foldl_cons, denote_cons, Rat.add_mul, ← ih]
    rw [denote_foldl, denote_add_insert, ←denote_mulMonomial, denote_nil_add, denote_foldl]

theorem denote_divConst {p : Polynomial} : (p.divConst c).denote ctx = p.denote ctx / c := by
  simp only [denote, divConst]
  induction p with
  | nil => simp [Rat.zero_div]
  | cons x ys ih =>
    simp only [List.map_cons, List.foldl_cons, Rat.add_comm 0, Monomial.foldl_assoc Rat.add_assoc]
    rw [Monomial.denote_divConst, ih, Rat.add_div]

end Polynomial

inductive IntExpr where
  | val (v : Int)
  | var (v : Nat)
  | neg (a : IntExpr)
  | add (a b : IntExpr)
  | sub (a b : IntExpr)
  | mul (a b : IntExpr)
deriving Inhabited, Repr

namespace IntExpr

def toPolynomial : IntExpr → Polynomial
  | .val v => if v = 0 then [] else [{ coeff := v, vars := [] }]
  | .var v => [{ coeff := 1, vars := [⟨false, v⟩] }]
  | .neg a => a.toPolynomial.neg
  | .add a b => Polynomial.add a.toPolynomial b.toPolynomial
  | .sub a b => Polynomial.sub a.toPolynomial b.toPolynomial
  | .mul a b => Polynomial.mul a.toPolynomial b.toPolynomial

def denote (ctx : IntContext) : IntExpr → Int
  | .val v => v
  | .var v => ctx v
  | .neg a => -a.denote ctx
  | .add a b => a.denote ctx + b.denote ctx
  | .sub a b => a.denote ctx - b.denote ctx
  | .mul a b => a.denote ctx * b.denote ctx

theorem denote_toPolynomial {rctx : RatContext} {e : IntExpr} : e.denote ictx = e.toPolynomial.denote (fun ⟨b, n⟩ => if b then rctx n else ictx n) := sorry

end IntExpr

inductive RatExpr where
  | val (v : Rat)
  | var (v : Nat)
  | neg (a : RatExpr)
  | add (a b : RatExpr)
  | sub (a b : RatExpr)
  | mul (a b : RatExpr)
  | divConst (a : RatExpr) (c : Rat)
  | cast (a : IntExpr)
deriving Inhabited, Repr

namespace RatExpr

def toPolynomial : RatExpr → Polynomial
  | .val v => if v = 0 then [] else [{ coeff := v, vars := [] }]
  | .var v => [{ coeff := 1, vars := [⟨true, v⟩] }]
  | .neg a => a.toPolynomial.neg
  | .add a b => Polynomial.add a.toPolynomial b.toPolynomial
  | .sub a b => Polynomial.sub a.toPolynomial b.toPolynomial
  | .mul a b => Polynomial.mul a.toPolynomial b.toPolynomial
  | .divConst a c => Polynomial.divConst a.toPolynomial c
  | .cast a => a.toPolynomial

def denote (ictx : IntContext) (rctx : RatContext)  : RatExpr → Rat
  | .val v => v
  | .var v => rctx v
  | .neg a => -a.denote ictx rctx
  | .add a b => a.denote ictx rctx + b.denote ictx rctx
  | .sub a b => a.denote ictx rctx - b.denote ictx rctx
  | .mul a b => a.denote ictx rctx * b.denote ictx rctx
  | .divConst a c => a.denote ictx rctx / c
  | .cast a => a.denote ictx

theorem denote_toPolynomial {e : RatExpr} : e.denote ictx rctx = e.toPolynomial.denote (fun ⟨b, n⟩ => if b then rctx n else ictx n) := by
  induction e with
  | val v =>
    simp only [denote, toPolynomial]
    split <;> rename_i hv
    · rewrite [hv]; rfl
    · sorry
  | var v =>
    simp [denote, toPolynomial, Polynomial.denote, Monomial.denote]
    sorry
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
  | cast a =>
    simpa only [denote] using IntExpr.denote_toPolynomial

theorem denote_eq_from_toPolynomial_eq {e₁ e₂ : RatExpr} (h : e₁.toPolynomial = e₂.toPolynomial) : e₁.denote ictx rctx = e₂.denote ictx rctx := by
  rw [denote_toPolynomial, denote_toPolynomial, h]

end Smt.Reconstruct.Rat.PolyNorm.RatExpr
