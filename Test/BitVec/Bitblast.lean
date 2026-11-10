import Smt

/-! cvc5 bit-blasts bit-vectors into their bits, which are Lean's `Bool`s. -/

-- `bvult`, `bvule`, `bvugt`, and `bvuge`
example (x y z : BitVec 4) (h₁ : x < y) (h₂ : y < z) : x < z := by smt [h₁, h₂]
example (x y : BitVec 4) (h : x.ult y = true) : x ≠ y := by smt [h]
example (x y : BitVec 4) (h₁ : x.ule y = true) (h₂ : y.ule x = true) : x = y := by smt [h₁, h₂]
example (x y z : BitVec 8) (h₁ : x ≤ y) (h₂ : y ≤ z) : x ≤ z := by smt [h₁, h₂]
example (x y z : BitVec 4) (h₁ : x > y) (h₂ : y > z) : x > z := by smt [h₁, h₂]
example (x y z : BitVec 4) (h₁ : x ≥ y) (h₂ : y ≥ z) : x ≥ z := by smt [h₁, h₂]
example (x y : BitVec 1) (h : x < y) : x = 0#1 := by smt [h]

-- `bvslt` and `bvsle`
example (x y z : BitVec 4) (h₁ : x.slt y = true) (h₂ : y.slt z = true) : x.slt z = true := by
  smt [h₁, h₂]
example (x y z : BitVec 4) (h₁ : x.sle y = true) (h₂ : y.sle z = true) : x.sle z = true := by
  smt [h₁, h₂]
example (x y : BitVec 4) (h : x.slt y = true) : y.slt x = false := by smt [h]
example (x y : BitVec 4) (h₁ : x.slt 0#4 = true) (h₂ : y.slt 0#4 = false) : y < x := by
  smt [h₁, h₂]

-- `bvnot`, `bvand`, `bvor`, and `bvxor`
example (x y : BitVec 4) (h : x &&& y = 15#4) : x = 15#4 := by smt [h]
example (x y : BitVec 4) (h : x ||| y = 0#4) : x = 0#4 := by smt [h]
example (x y : BitVec 4) (h : x ^^^ y = 0#4) : x = y := by smt [h]
example (x : BitVec 4) (h : ~~~x = 0#4) : x = 15#4 := by smt [h]
example (x y z : BitVec 4) (h : x &&& y &&& z = 15#4) : z = 15#4 := by smt [h]

-- `bvadd` and `bvneg`
example (x y : BitVec 4) (h : x + y = 3#4) (hx : x = 1#4) : y = 2#4 := by smt [h, hx]
example (x y z : BitVec 4) (h₁ : x + y + z = 0#4) (h₂ : x &&& y &&& z = 15#4) : False := by
  smt [h₁, h₂]
example (x y : BitVec 8) (h : x - y = 0#8) : x = y := by smt [h]

-- Terms whose operators are not bit-vector operators
example (x y : BitVec 4) (c : Bool) (h : (if c then x else y) = 3#4) (hc : c = true) : x = 3#4 := by
  smt [h, hc]
example (f : BitVec 4 → BitVec 4) (x : BitVec 4) (h : f x < 1#4) : f x = 0#4 := by smt [h]
