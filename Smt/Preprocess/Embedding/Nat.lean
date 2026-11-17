/-
Copyright (c) 2021-2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

module

public import Smt.Preprocess.Embedding.Attribute
public meta import Smt.Preprocess.Embedding.Attribute

/-!
# Embedding `Nat` into `Int` without eliminating it

`Nat` is sent to the SMT solver as a datatype:
```smt2
(declare-datatypes ((Nat 0)) (((Nat.zero) (Nat.succ (Nat.succ.n Nat)))))
```
Variables, quantifiers, function arguments and results, and datatype fields of type `Nat` keep the
type `Nat`. The `embedding` step only rewrites `Nat` operations, literals, and (in)equalities into
their `Int` versions, using the casts `Nat.toInt` and `Nat.fromInt`. For example, `x + y ≤ z`
becomes `(Nat.fromInt (x.toInt + y.toInt)).toInt ≤ z.toInt`. Truncated subtraction needs no special
case: `Nat.fromInt` maps negative integers to `0`.

The solver receives the casts as uninterpreted functions, together with the facts below (proved in
Lean, and added as hypotheses by the `embedding` step, so the final step of the reconstruction
discharges them like any other hypothesis):
```lean
Nat.toInt_nonneg            : ∀ n, 0 ≤ n.toInt
Nat.toInt_fromInt_of_nonneg : ∀ x, 0 ≤ x → (Nat.fromInt x).toInt = x
Nat.fromInt_toInt           : ∀ n, Nat.fromInt n.toInt = n
Nat.toInt_fromInt_of_nonpos : ∀ x, x ≤ 0 → (Nat.fromInt x).toInt = 0
```
The first three facts make `Nat.toInt` a bijection between the datatype and the non-negative
integers, with `Nat.fromInt` as its inverse. The fourth fact fixes `Nat.fromInt` on non-positive
integers, which truncated subtraction (e.g., `x - y ≤ x`) relies on.

We do not send the recursive definitions of the casts (as `define-fun-rec`s or as their equation
lemmas): their unfolding (`Nat.fromInt x = Nat.succ (Nat.fromInt (x - 1))`) is a matching loop for
quantifier instantiation, which makes cvc5 time out on goals it otherwise proves instantly, and spin
forever (instead of returning `unknown`) on satisfiable queries.
-/

public section

/-- Cast a natural number into an integer, by structural recursion on the `Nat` datatype. -/
def Nat.toInt (n : Nat) : Int := match n with
  | .zero   => 0
  | .succ n => Nat.toInt n + 1

/-- Cast an integer into a natural number, mapping non-positive integers to `0`. -/
def Nat.fromInt (x : Int) : Nat :=
  if x ≤ 0 then .zero else .succ (Nat.fromInt (x - 1))
termination_by x.natAbs

namespace Nat

theorem toInt_eq_natCast (n : Nat) : n.toInt = (n : Int) := by
  induction n with
  | zero      => rfl
  | succ n ih => rw [Nat.toInt, ih, Int.natCast_succ]

theorem fromInt_eq_toNat (x : Int) : Nat.fromInt x = x.toNat := by
  fun_induction Nat.fromInt x with
  | case1 x h    => exact (Int.toNat_of_nonpos h).symm
  | case2 x h ih => rw [ih]; omega

-- Prevent `isDefEq` from evaluating the casts (e.g., on large literals).
attribute [irreducible] Nat.toInt

/-! ## Facts about the casts sent to the solver -/

theorem toInt_nonneg (n : Nat) : 0 ≤ n.toInt := by
  rw [toInt_eq_natCast]
  exact Int.natCast_nonneg n

theorem toInt_fromInt_of_nonneg (x : Int) : 0 ≤ x → (Nat.fromInt x).toInt = x := by
  intro h
  rw [toInt_eq_natCast, fromInt_eq_toNat]
  exact Int.toNat_of_nonneg h

theorem fromInt_toInt (n : Nat) : Nat.fromInt n.toInt = n := by
  rw [toInt_eq_natCast, fromInt_eq_toNat]
  exact Int.toNat_natCast n

theorem toInt_fromInt_of_nonpos (x : Int) : x ≤ 0 → (Nat.fromInt x).toInt = 0 := by
  intro h
  rw [toInt_eq_natCast, fromInt_eq_toNat]
  omega

end Nat

namespace Smt.Preprocess.Embedding.Nat

/-! ## Rewrites of `Nat` into `Int` -/

attribute [embedding ↓] Nat.zero_eq Nat.succ_eq_add_one Nat.pred_eq_sub_one

-- Casts

@[embedding ↓]
theorem natCast_eq_toInt (n : Nat) : (n : Int) = n.toInt :=
  (Nat.toInt_eq_natCast n).symm

@[embedding ↓]
theorem toNat_eq_fromInt (x : Int) : x.toNat = Nat.fromInt x :=
  (Nat.fromInt_eq_toNat x).symm

-- Literals. Bare literals are rewritten by the `natLitEqFromInt` simproc below. Literals under
-- `Nat.toInt` are rewritten first (simp rewrites top-down). `no_index` is needed because simp
-- indexes numerals as literals.

theorem ofNat_eq_fromInt (n : Nat) : (OfNat.ofNat n : Nat) = Nat.fromInt (OfNat.ofNat n : Int) := by
  rw [Nat.fromInt_eq_toNat]
  rfl

@[embedding ↓]
theorem toInt_ofNat (n : Nat) : Nat.toInt (no_index (OfNat.ofNat n)) = (OfNat.ofNat n : Int) := by
  rw [Nat.toInt_eq_natCast]
  rfl

-- (In)equalities

@[embedding ↓]
theorem eq_eq_toInt_eq (a b : Nat) : (a = b) = (a.toInt = b.toInt) := by
  simp only [Nat.toInt_eq_natCast, Int.natCast_inj]

@[embedding ↓]
theorem ne_eq_toInt_ne (a b : Nat) : (a ≠ b) = (a.toInt ≠ b.toInt) := by
  simp only [Nat.toInt_eq_natCast, ne_eq, Int.natCast_inj]

@[embedding ↓]
theorem le_eq_toInt_le (a b : Nat) : (a ≤ b) = (a.toInt ≤ b.toInt) := by
  simp only [Nat.toInt_eq_natCast, Int.ofNat_le]

@[embedding ↓]
theorem lt_eq_toInt_lt (a b : Nat) : (a < b) = (a.toInt < b.toInt) := by
  simp only [Nat.toInt_eq_natCast, Int.ofNat_lt]

@[embedding ↓]
theorem ge_eq_toInt_ge (a b : Nat) : (a ≥ b) = (a.toInt ≥ b.toInt) := by
  simp only [Nat.toInt_eq_natCast, ge_iff_le, Int.ofNat_le]

@[embedding ↓]
theorem gt_eq_toInt_gt (a b : Nat) : (a > b) = (a.toInt > b.toInt) := by
  simp only [Nat.toInt_eq_natCast, gt_iff_lt, Int.ofNat_lt]

-- Operations under `Nat.toInt`. These hold without a round trip through `Nat.fromInt`, except for
-- subtraction, which is truncated. Without them, nonlinear goals (e.g., the `a * b + ...` example
-- in `Test/Unit/Embedding.lean`) get proofs too large to reconstruct.
--
-- The order of the rewrites is fixed by the traversal, not by priorities: simp tries the ↓
-- lemmas on `(a + b).toInt` before it visits `a + b`, so `toInt_add` applies before
-- `add_eq_fromInt` below could (priorities only order lemmas for the same term). So a term that
-- another lemma rewrites into an operation or a literal only after its parent was visited needs a
-- lemma of its own here: `Nat.zero`, `Nat.succ` (rewritten by `Nat.zero_eq` and
-- `Nat.succ_eq_add_one`), and `ite`, whose branches are visited as `Nat` terms.

@[embedding ↓]
theorem toInt_zero : Nat.zero.toInt = 0 := by
  rw [Nat.toInt_eq_natCast]
  rfl

@[embedding ↓]
theorem toInt_succ (n : Nat) : n.succ.toInt = n.toInt + 1 := by
  simp only [Nat.toInt_eq_natCast, Int.natCast_succ]

@[embedding ↓]
theorem toInt_ite [Decidable c] (a b : Nat) :
    (if c then a else b).toInt = if c then a.toInt else b.toInt :=
  apply_ite Nat.toInt c a b

@[embedding ↓]
theorem toInt_add (a b : Nat) : (a + b).toInt = a.toInt + b.toInt := by
  simp only [Nat.toInt_eq_natCast, Int.natCast_add]

@[embedding ↓]
theorem toInt_mul (a b : Nat) : (a * b).toInt = a.toInt * b.toInt := by
  simp only [Nat.toInt_eq_natCast, Int.natCast_mul]

@[embedding ↓]
theorem toInt_div (a b : Nat) : (a / b).toInt = a.toInt / b.toInt := by
  simp only [Nat.toInt_eq_natCast, Int.natCast_ediv]

@[embedding ↓]
theorem toInt_mod (a b : Nat) : (a % b).toInt = a.toInt % b.toInt := by
  simp only [Nat.toInt_eq_natCast, Int.natCast_emod]

-- Operations elsewhere, e.g., in arguments of functions and constructors.

@[embedding ↓]
theorem add_eq_fromInt (a b : Nat) : a + b = Nat.fromInt (a.toInt + b.toInt) := by
  rw [Nat.toInt_eq_natCast, Nat.toInt_eq_natCast, Nat.fromInt_eq_toNat]
  omega

@[embedding ↓]
theorem sub_eq_fromInt (a b : Nat) : a - b = Nat.fromInt (a.toInt - b.toInt) := by
  rw [Nat.toInt_eq_natCast, Nat.toInt_eq_natCast, Nat.fromInt_eq_toNat]
  omega

@[embedding ↓]
theorem mul_eq_fromInt (a b : Nat) : a * b = Nat.fromInt (a.toInt * b.toInt) := by
  rw [Nat.toInt_eq_natCast, Nat.toInt_eq_natCast, Nat.fromInt_eq_toNat, ← Int.natCast_mul,
    Int.toNat_natCast]

@[embedding ↓]
theorem div_eq_fromInt (a b : Nat) : a / b = Nat.fromInt (a.toInt / b.toInt) := by
  rw [Nat.toInt_eq_natCast, Nat.toInt_eq_natCast, Nat.fromInt_eq_toNat, ← Int.natCast_ediv,
    Int.toNat_natCast]

@[embedding ↓]
theorem mod_eq_fromInt (a b : Nat) : a % b = Nat.fromInt (a.toInt % b.toInt) := by
  rw [Nat.toInt_eq_natCast, Nat.toInt_eq_natCast, Nat.fromInt_eq_toNat, ← Int.natCast_emod,
    Int.toNat_natCast]

end Smt.Preprocess.Embedding.Nat

public meta section

namespace Smt.Preprocess.Embedding.Nat

open Lean Meta Simp

/-- Rewrite each `Nat` literal `n` into `Nat.fromInt (n : Int)`. Simp indexes numerals as literals,
so no pattern matches every `Nat` literal: this simproc is tried on every term. Unlike a `no_index`
simp lemma, it creates no metavariables on each attempt. Those would shift the ids of the free
variables that the `embedding` step creates, and hence reorder the SMT-LIB declarations of goals
without `Nat` operations. -/
simproc ↓ [embedding] natLitEqFromInt (_) := fun e => do
  let_expr OfNat.ofNat α n inst := e | return .continue
  unless α.isConstOf ``Nat && n.isRawNatLit && inst.isAppOfArity ``instOfNatNat 1 do
    return .continue
  let i := mkApp3 (.const ``OfNat.ofNat [0]) (.const ``Int []) n (.app (.const ``instOfNat []) n)
  let proof := .app (.const ``ofNat_eq_fromInt []) n
  return .done { expr := .app (.const ``Nat.fromInt []) i, proof? := some proof }

end Smt.Preprocess.Embedding.Nat
