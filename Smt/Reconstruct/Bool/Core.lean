/-
Copyright (c) 2021-2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

module

public import Smt.Reconstruct.Prop.Core

@[expose] public section

/-!
# Booleans as the target of proof reconstruction

SMT-LIB's `Bool` sort is reconstructed as Lean's `Bool`, and a proof of an SMT formula `φ` is a
proof of `⟦φ⟧ = true`. SMT-LIB's operators are reconstructed as Lean's computable Boolean functions,
so that closed formulas evaluate unless they involve reals, quantifiers, or undecidable atoms:

| SMT-LIB                     | Lean                            |
|-----------------------------|---------------------------------|
| `true`, `false`             | `true`, `false`                 |
| `not`, `and`, `or`, `xor`   | `!`, `&&`, `\|\|`, `^^`         |
| `=>`                        | `Bool.imp`                      |
| `=`, `distinct`             | `decide (a = b)`, `!decide (a = b)` |
| `<`, `<=`, `>`, `>=`        | `x.blt y`, `x.ble y`, `x.bgt y`, `x.bge y` |
| `ite`                       | `cond`                          |
| `forall`, `exists`          | `Bool.forall`, `Bool.exists`    |
| other atoms                 | `decide p`                      |

`decide (a = b)` uses `inst a b`, where `inst` is the `DecidableEq` instance of SMT-LIB's builtin
sorts, and otherwise a synthesized or classical one. The comparisons are `Int.blt` and friends on
integers, rationals, and reals, and `BitVec.ult` and friends on bit-vectors. `decide p` uses a
synthesized instance of `Decidable p`, or a classical one.

The theorems of proof reconstruction are stated over these Boolean formulas: a proof of a formula
`b` is a proof of `b = true`, a proof of an equality `(= t s)` is usually a proof of `t = s`, and
rewrites are equations between Booleans or terms.
-/

universe u

/-- `true` iff `p x` holds for all `x`: SMT-LIB's `forall` over one variable.
`(forall ((x T) (y U)) F)` is `Bool.forall fun x => Bool.forall fun y => F`. -/
noncomputable def Bool.forall {α : Sort u} (p : α → Bool) : Bool :=
  @decide (∀ x, p x = true) (Classical.propDecidable _)

/-- `true` iff `p x` holds for some `x`: SMT-LIB's `exists` over one variable. -/
noncomputable def Bool.exists {α : Sort u} (p : α → Bool) : Bool :=
  @decide (∃ x, p x = true) (Classical.propDecidable _)

section

variable {α : Sort u} {f : α → Bool}

@[simp] theorem Bool.forall_eq_true : (Bool.forall f = true) = ∀ x, f x = true :=
  @decide_eq_true_eq _ (Classical.propDecidable _)
@[simp] theorem Bool.exists_eq_true : (Bool.exists f = true) = ∃ x, f x = true :=
  @decide_eq_true_eq _ (Classical.propDecidable _)
@[simp] theorem Bool.forall_eq_false : (Bool.forall f = false) = ¬∀ x, f x = true :=
  propext (@decide_eq_false_iff_not _ (Classical.propDecidable _))
@[simp] theorem Bool.exists_eq_false : (Bool.exists f = false) = ¬∃ x, f x = true :=
  propext (@decide_eq_false_iff_not _ (Classical.propDecidable _))

end

namespace Bool

/-- Boolean implication, the reconstruction of SMT-LIB's `=>`. -/
def imp (a b : Bool) : Bool := !a || b

/-- n-ary conjunction. Like cvc5's n-ary `and`, it has no trailing `true`: `andN [a] = a` and
`andN [a, b, c] = a && (b && c)`. -/
def andN : List Bool → Bool
  | []      => true
  | b :: [] => b
  | b :: bs => b && andN bs

/-- n-ary disjunction. Like cvc5's n-ary `or`, it has no trailing `false`: `orN [a] = a` and
`orN [a, b, c] = a || (b || c)`. -/
def orN : List Bool → Bool
  | []      => false
  | b :: [] => b
  | b :: bs => b || orN bs

/-- `impliesN [b₁, …, bₙ] q` is `b₁ = true → ⋯ → bₙ = true → q`. -/
def impliesN : List Bool → Prop → Prop
  | [],      q => q
  | b :: bs, q => b = true → impliesN bs q

@[simp] theorem imp_eq_true {a b : Bool} : (a.imp b = true) = (a = true → b = true) := by
  cases a <;> cases b <;> simp [imp]

@[simp] theorem andN_cons_append : andN (b :: bs) = (b && andN bs) := by
  cases bs <;> simp [andN]

@[simp] theorem andN_append : andN (bs₁ ++ bs₂) = (andN bs₁ && andN bs₂) := by
  induction bs₁ with
  | nil => simp [andN]
  | cons b bs₁ ih => simp [ih, Bool.and_assoc]

@[simp] theorem orN_cons_append : orN (b :: bs) = (b || orN bs) := by
  cases bs <;> simp [orN]

@[simp] theorem orN_append : orN (bs₁ ++ bs₂) = (orN bs₁ || orN bs₂) := by
  induction bs₁ with
  | nil => simp [orN]
  | cons b bs₁ ih => simp [ih, Bool.or_assoc]

theorem andN_eq_true {bs : List Bool} : (andN bs = true) = ∀ b ∈ bs, b = true := by
  induction bs with
  | nil => simp [andN]
  | cons b bs ih => simp [ih]

theorem orN_eq_true {bs : List Bool} : (orN bs = true) = ∃ b ∈ bs, b = true := by
  induction bs with
  | nil => simp [orN]
  | cons b bs ih => simp [ih]

end Bool

namespace Smt.Reconstruct.Bool

/-! ### Boolean formulas as propositions -/

theorem not_eq_true_eq_not {b : Bool} : ((!b) = true) = ¬(b = true) := by
  cases b <;> simp

theorem decide_bool_eq_eq {a b : Bool} {h : Decidable (a = b)} :
    (@decide (a = b) h = true) = ((a = true) = (b = true)) := by
  cases a <;> cases b <;> simp

end Smt.Reconstruct.Bool
