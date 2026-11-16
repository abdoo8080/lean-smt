import Smt

-- cvc5 proves this with `ARITH_MULT_ABS_COMPARISON` steps whose second premise is
-- `|b| = |b| ∧ b ≠ 0`.
example (a b c : Int) (h₁ : a > c) (h₂ : c > 0) (h₃ : b > 0) : a * b > c * b := by
  smt [h₁, h₂, h₃]
