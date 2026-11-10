/-
Copyright (c) 2021-2024 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

module

public import Smt.Reconstruct.Bool.Core

@[expose] public section

/-!
# Lemmas for cvc5's bit-blasting steps

cvc5 bit-blasts a bit-vector `x` of width `n` into the bit-vector `cons xₙ₋₁ (… (cons x₀ nil))` of
its bits, where each bit `xᵢ` is a Boolean formula.
-/

namespace BitVec

def bb (x : BitVec w) : BitVec w :=
  (iunfoldr (fun i _ => ((), x.getLsbD i)) ()).snd

theorem self_eq_bb (x : BitVec w) : x = x.bb := by
  unfold bb
  rw [iunfoldr_replace_snd (λ _ => ()) (init:=rfl)]
  intro i
  rfl

theorem cons_eq_cons {a b : Bool} {xs ys : BitVec w} : (cons a xs = cons b ys) = (xs = ys ∧ a = b) := by
  apply propext
  constructor
  · intro h
    exact ⟨by simpa using congrArg (setWidth w) h, by simpa using congrArg BitVec.msb h⟩
  · intro ⟨hxy, hab⟩
    rw [hxy, hab]

/-! cvc5 compares bit-vectors bit by bit from their least significant bits:
`smtEq x y = (smtEq x₀ y₀ && (… && smtEq xₙ₋₁ yₙ₋₁))`. -/

theorem smtEq_cons_cons (a b : Bool) (xs ys : BitVec w) :
    smtEq (cons a xs) (cons b ys) = (smtEq xs ys && smtEq a b) := by
  apply Bool.eq_iff_iff.mpr
  simp only [smtEq_eq_true, Bool.and_eq_true, cons_eq_cons]

theorem smtEq_cons_cons_and (a b acc : Bool) (xs ys : BitVec w) :
    (smtEq (cons a xs) (cons b ys) && acc) = (smtEq xs ys && (smtEq a b && acc)) := by
  rw [smtEq_cons_cons, Bool.and_assoc]

theorem smtEq_nil_nil_and (acc : Bool) : (smtEq nil nil && acc) = acc := by
  rw [smtEq_of_eq rfl, Bool.true_and]

theorem not_nil : ~~~nil = nil := eq_nil _

theorem nil_and_nil : nil &&& nil = nil := eq_nil _

theorem nil_or_nil : nil ||| nil = nil := eq_nil _

theorem nil_xor_nil : nil ^^^ nil = nil := eq_nil _

/-! cvc5 compares bit-vectors from their least significant bits: `x < y` for bit-vectors of width
`1` is `!x₀ && y₀`, and `cons a xs < cons b ys` is `smtEq a b && xs < ys || !a && b`. -/

theorem cons_lt_cons {a b : Bool} {xs ys : BitVec w} :
    (cons a xs < cons b ys) = ((a = b ∧ xs < ys) ∨ (a = false ∧ b = true)) := by
  apply propext
  simp only [lt_def, toNat_cons']
  have hx := xs.isLt
  have hy := ys.isLt
  generalize 2 ^ w = N at hx hy
  cases a <;> cases b <;> simp [Nat.shiftLeft_eq] <;> omega

theorem cons_le_cons {a b : Bool} {xs ys : BitVec w} :
    (cons a xs ≤ cons b ys) = ((a = b ∧ xs ≤ ys) ∨ (a = false ∧ b = true)) := by
  apply propext
  simp only [le_def, toNat_cons']
  have hx := xs.isLt
  have hy := ys.isLt
  generalize 2 ^ w = N at hx hy
  cases a <;> cases b <;> simp [Nat.shiftLeft_eq] <;> omega

theorem smtLt_cons_nil (a b : Bool) : smtLt (cons a nil) (cons b nil) = (!a && b) := by
  apply Bool.eq_iff_iff.mpr
  simp only [smtLt_eq_true, cons_lt_cons]
  cases a <;> cases b <;> simp

theorem smtLt_cons_cons (a b : Bool) (xs ys : BitVec w) :
    smtLt (cons a xs) (cons b ys) = (smtEq a b && smtLt xs ys || !a && b) := by
  apply Bool.eq_iff_iff.mpr
  simp only [smtLt_eq_true, cons_lt_cons, Bool.or_eq_true, Bool.and_eq_true, smtEq_eq_true,
    Bool.not_eq_true']

theorem smtLe_cons_nil (a b : Bool) : smtLe (cons a nil) (cons b nil) = (!a && b || smtEq a b) := by
  apply Bool.eq_iff_iff.mpr
  simp only [smtLe_eq_true, cons_le_cons]
  cases a <;> cases b <;> simp

theorem smtLe_cons_cons (a b : Bool) (xs ys : BitVec w) :
    smtLe (cons a xs) (cons b ys) = (smtEq a b && smtLe xs ys || !a && b) := by
  apply Bool.eq_iff_iff.mpr
  simp only [smtLe_eq_true, cons_le_cons, Bool.or_eq_true, Bool.and_eq_true, smtEq_eq_true,
    Bool.not_eq_true']

/-! The signed comparisons compare the sign bits, and then the other bits as unsigned numbers. -/

theorem slt_cons_nil (a b : Bool) : (cons a nil).slt (cons b nil) = (a && !b) := by
  cases a <;> cases b <;> rfl

theorem slt_cons_cons (a b : Bool) (xs ys : BitVec w) :
    (cons a xs).slt (cons b ys) = (smtEq a b && smtLt xs ys || a && !b) := by
  rw [slt_eq_ult, msb_cons, msb_cons, ult_eq_decide_lt, decide_eq_smtDecide]
  change _ = (smtEq a b && smtLt xs ys || a && !b)
  rw [show smtDecide (cons a xs < cons b ys) = smtLt (cons a xs) (cons b ys) from rfl, smtLt_cons_cons]
  cases a <;> cases b <;> simp [smtEq_eq_decide]

theorem sle_cons_nil (a b : Bool) : (cons a nil).sle (cons b nil) = (smtEq a b || a && !b) := by
  cases a <;> cases b <;> simp [smtEq_eq_decide] <;> rfl

theorem sle_cons_cons (a b : Bool) (xs ys : BitVec w) :
    (cons a xs).sle (cons b ys) = (smtEq a b && smtLe xs ys || a && !b) := by
  have h : smtLe xs ys = !smtLt ys xs := by
    apply Bool.eq_iff_iff.mpr
    simp only [smtLe_eq_true, Bool.not_eq_true', smtLt_eq_false]
    exact BitVec.not_lt.symm
  rw [sle_eq_not_slt, slt_cons_cons, h]
  cases a <;> cases b <;> simp [smtEq_eq_decide]

/-- Carry function for bitwise addition. -/
def adcb' (x y c : Bool) : Bool × Bool := (x && y || Bool.xor x y && c, (Bool.xor (Bool.xor x y) c))

theorem adcb_eq_adcb' : adcb = adcb' := by
  funext x y c
  cases x <;> cases y <;> cases c <;> rfl

/-- Bitwise addition implemented via a ripple carry adder. -/
def adc' (x y : BitVec w) : Bool → Bool × BitVec w :=
  iunfoldr fun (i : Fin w) c => adcb' (x.getLsbD i) (y.getLsbD i) c

theorem adc_eq_adc' : @adc = @adc' := by
  funext x y c
  rw [adc, adc', adcb_eq_adcb']

theorem add_eq_adc' (x y : BitVec w) : x + y = (adc' x y false).snd := by
  rw [add_eq_adc, adc_eq_adc']

/-- cvc5 negates `x` by adding `~~~x`, `0`, and the carry `true`. -/
theorem neg_eq_adc' (x : BitVec w) : -x = (adc' (~~~x) 0#w true).snd := by
  rw [← adc_eq_adc', adc_spec, BitVec.neg_eq_not_add, BitVec.add_zero]
  congr 1
  apply eq_of_toNat_eq
  cases w <;> simp

end BitVec
