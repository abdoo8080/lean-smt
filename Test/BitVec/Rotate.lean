import Smt

/-! The normalization step rewrites rotations by `Nat` literals into rotations by bit-vector
literals, which the embedding of `Nat` leaves intact (see `Smt/Preprocess/Normalize/BitVec.lean`). -/

example (x y : BitVec 8) : x.rotateLeft 3 = y.rotateRight 11 := by
  smt_show
