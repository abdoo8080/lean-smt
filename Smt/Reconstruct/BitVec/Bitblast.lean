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
`decide (x = y) = (decide (x₀ = y₀) && (… && decide (xₙ₋₁ = yₙ₋₁)))`. -/

theorem decide_eq_cons_cons (a b : Bool) (xs ys : BitVec w) :
    decide (cons a xs = cons b ys) = (decide (xs = ys) && decide (a = b)) := by
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, Bool.and_eq_true, cons_eq_cons]

theorem decide_eq_cons_cons_and (a b acc : Bool) (xs ys : BitVec w) :
    (decide (cons a xs = cons b ys) && acc) = (decide (xs = ys) && (decide (a = b) && acc)) := by
  rw [decide_eq_cons_cons, Bool.and_assoc]

theorem decide_eq_nil_nil_and (acc : Bool) : (decide (nil = nil) && acc) = acc := by
  rw [decide_eq_true rfl, Bool.true_and]

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

end BitVec
