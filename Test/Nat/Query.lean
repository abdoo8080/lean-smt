import Smt

/-! The shapes of the queries for `Nat` (see `Smt/Preprocess/Embedding/Nat.lean`): `Nat.toInt` is
pushed through operations, except subtraction and `Nat`-sorted positions, which keep `Nat.fromInt`. -/

example (x y : Nat) : x + y ≥ x := by
  smt_show

example (x y : Nat) : x - y ≤ x := by
  smt_show

example (f : Nat → Nat) (x : Nat) : f (x + 1) ≥ 0 := by
  smt_show

example (c : Bool) (x y : Nat) : (if c then x + 1 else y) ≥ x := by
  smt_show

example (x : Nat) : Nat.succ x > Nat.zero := by
  smt_show -normalize
