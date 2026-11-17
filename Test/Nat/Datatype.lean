import Smt

/-! `Nat` is a datatype in SMT-LIB, so datatypes with `Nat` fields, including inductive ones, are
translated faithfully. See `Smt/Preprocess/Embedding/Nat.lean`. -/

inductive Shape where
  | circle (r : Nat)
  | rect (w h : Nat)

example (r w h : Nat) : Shape.circle r ≠ Shape.rect w h := by
  smt

example (perimeter : Shape → Nat) (h : ∀ w h, perimeter (.rect w h) = 2 * (w + h)) (w : Nat) :
    perimeter (.rect w w) = 4 * w := by
  smt [h]

inductive NatList where
  | nil
  | cons (head : Nat) (tail : NatList)

example (x : Nat) (xs : NatList) : NatList.cons (x + 1) xs ≠ .nil := by
  smt

example (len : NatList → Nat) (hnil : len .nil = 0)
    (hcons : ∀ x xs, len (.cons x xs) = len xs + 1) (x y : Nat) :
    len (.cons x (.cons y .nil)) = 2 := by
  smt [hnil, hcons]

def NatList.sum : NatList → Nat
  | .nil       => 0
  | .cons x xs => x + xs.sum

def NatList.append : NatList → NatList → NatList
  | .nil,       ys => ys
  | .cons x xs, ys => .cons x (xs.append ys)

example : NatList.sum (.cons 1 (.cons 2 .nil)) = 3 := by
  smt [NatList.sum]

theorem NatList.sum_append (xs ys : NatList) : (xs.append ys).sum = xs.sum + ys.sum := by
  induction xs with
  | nil          => smt [NatList.sum, NatList.append]
  | cons x xs ih => smt [NatList.sum, NatList.append, ih]

/-! Quantifiers and functions over `Nat` keep the type `Nat`. -/

example (f : Nat → Nat) (h : ∀ x, f x > x) : ∀ x, f (f x) > x + 1 := by
  smt [h]

-- Fails: refuting `∀ y : Nat, y.toInt ≤ x.toInt` requires the witness `Nat.fromInt (x.toInt + 1)`,
-- which quantifier instantiation does not find. Counterexample-guided instantiation would, but only
-- for quantifiers over `Int`.
example (x : Nat) : ∃ y : Nat, y > x := by
  smt

/-! Casts between `Nat` and `Int`. -/

example (n : Nat) (x : Int) (h : x = n) : x ≥ 0 := by
  smt [h]

example (x : Int) (h : x ≥ 0) : (x.toNat : Int) = x := by
  smt [h]

example (x : Int) (h : x < 0) : x.toNat = 0 := by
  smt [h]
