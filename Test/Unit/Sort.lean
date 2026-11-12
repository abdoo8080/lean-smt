import Smt

/-! Type variables in `Sort u` are lifted into `Type u` (see `Smt.Preprocess.Embedding.Sort`). -/

universe u v

example {U : Sort u} {f : U → U → U} {a b c d : U} : a = b → c = d → f a c = f b d := by
  smt

example {U : Sort u} {V : Sort v} {f : U → V} {a b : U} : a = b → f a = f b := by
  smt

example {U : Sort u} {f : U → Int} {a b : U} : a = b → f a + 1 = f b + 1 := by
  smt

example {U : Sort u} {f : Int → U} {a b : Int} : a = b → f a = f b := by
  smt

example {U : Sort u} {c : Prop} [Decidable c] {a b : U} :
    (if c then a else b) = a ∨ (if c then a else b) = b := by
  smt

example {U : Sort u} [Nonempty U] {p : U → Prop} {a : U} : (∀ x, p x) → p a := by
  smt

example {U : Sort u} {p : U → Prop} : (∃ x, p x) → ¬∀ x, ¬p x := by
  smt

-- Auto-bound implicits are in `Sort u_1`.

example {f : U → U} {a : U} (h : ∀ x, f x = x) : f (f a) = a := by
  smt [h]

example {p : U → U → Prop} : (∀ x y, p x y) = (∀ y x, p x y) := by
  smt
