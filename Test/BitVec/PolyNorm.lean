import Smt

/-! cvc5 normalizes bit-vector polynomials modulo `2 ^ w`. -/

example (x y : BitVec 4) : x - y + y = x := by smt
example (x y : BitVec 8) : 3#8 * x + 5#8 * y = 5#8 * y + x + x + x := by smt
example (x y : BitVec 4) (h : x.ule y = true) (h' : y.ule x = true) : x = y := by smt [h, h']
example (x : BitVec 4) : x.sle x = true := by smt
