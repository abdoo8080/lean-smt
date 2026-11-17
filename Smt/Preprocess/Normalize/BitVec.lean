/-
Copyright (c) 2021-2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

module

public import Smt.Preprocess.Normalize.Attribute
public import Smt.Reconstruct.BitVec.Core

/-!
SMT-LIB needs numerals in bit-vector literals and in the indices of rotations, but the embedding of
`Nat` rewrites `Nat` literals into `Nat.fromInt` applications (see
`Smt/Preprocess/Embedding/Nat.lean`). So we rewrite the bit-vector operators that take `Nat` literals
into ones that take bit-vector literals, whose numerals simp never visits. `no_index` is needed
because simp indexes numerals as literals.
-/

@[expose] public section

namespace BitVec

@[smt_normalize ↓]
theorem ofNat_eq_ofNat_lit : BitVec.ofNat w (no_index (OfNat.ofNat n)) = (OfNat.ofNat n : BitVec w) :=
  rfl

/-- The amount is a bit-vector of width `n`, which represents `n` exactly. -/
@[smt_normalize ↓]
theorem rotateLeft_eq_smtRotateLeft (x : BitVec w) :
    x.rotateLeft (no_index (OfNat.ofNat n)) = x.smtRotateLeft (OfNat.ofNat n : BitVec n) := by
  rw [smtRotateLeft, ofNat_eq_ofNat, toNat_ofNat, Nat.mod_eq_of_lt Nat.lt_two_pow_self]
  rfl

/-- The amount is a bit-vector of width `n`, which represents `n` exactly. -/
@[smt_normalize ↓]
theorem rotateRight_eq_smtRotateRight (x : BitVec w) :
    x.rotateRight (no_index (OfNat.ofNat n)) = x.smtRotateRight (OfNat.ofNat n : BitVec n) := by
  rw [smtRotateRight, ofNat_eq_ofNat, toNat_ofNat, Nat.mod_eq_of_lt Nat.lt_two_pow_self]
  rfl

end BitVec
