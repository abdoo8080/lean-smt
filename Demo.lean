import Smt

#check True

set_option trace.smt.translate.query true in
set_option trace.smt.translate.expr true in
set_option trace.smt true in
set_option trace.smt.solve true in
set_option trace.smt.reconstruct.proof true in
theorem modus_ponens {p q : Prop} : p → (p → q) → q := by
  smt

example {U : Type} [Nonempty U] {a b c d : U} {f : U → U → U} {p1 p2 p3 : Prop} :
  ¬¬(a = b → c = d → p1 ∧ True → ¬p1 ∨ p2 ∧ p3 → ¬p3 ∨ ¬f a c = f b d → False) := by
  smt

variable {G : Type} [Nonempty G] (op : G → G → G) (inv : G → G) (e : G)

axiom assoc   : ∀ a b c, op a (op b c) = op (op a b) c
axiom inverse : ∀ a, op (inv a) a = e
axiom ident   : ∀ a, op e a = a

theorem inverse' : ∀ a, op a (inv a) = e := by
  smt [assoc op, inverse op inv e, ident op e]

theorem identity' : ∀ a, op a e = a := by
  smt [assoc op, inverse op inv e, ident op e, inverse' op inv e]

theorem unique_identity e' : (∀ z, op e' z = z) → e' = e := by
  smt [assoc op, inverse op inv e, ident op e]

example (b c a v0 v1 : Int) (h1 : v0 = 5*a) (h2 : v1 = 3*b)
    (h3 : v0 + v1 + c = 10) : v0 + 5 + (v1 - 3) + (c - 2) = 10 := by
  smt [h1, h2, h3]

example (h : (1 : Int) < 0) (g : ¬ (37 : Int) < 42) (_k : True) (l : (-7 : Int) < 5): (3 : Int) < 7 := by
  smt [h, g, _k, l]

example (u v r s t : Int) (h : 0 < u*(t*v + t*r + s)) : 0 < (t*(r + v) + s)*3*u := by
  smt [h]

example (A B : Int) (h : 0 < 8 * A * B) : 0 < A*B := by
  smt [h]

example (A B : Int) (h : 0 < A * B) : 0 < A*8*B := by
  smt [h]

example (u v x y A B : Int)
(a : 0 < A)
(a_1 : 0 <= 1 - A)
(a_2 : 0 <= B - 1)
(a_3 : 0 <= B - x)
(a_4 : 0 <= B - y)
(a_5 : 0 <= u)
(a_6 : 0 <= v)
(a_7 : 0 < A - u)
(a_8 : 0 < A - v) :
 (0 < A * A)
-> (0 <= A * (1 - A))
-> (0 <= A * (B - 1))
-> (0 <= A * (B - x))
-> (0 <= A * (B - y))
-> (0 <= A * u)
-> (0 <= A * v)
-> (0 < A * (A - u))
-> (0 < A * (A - v))
-> (0 <= (1 - A) * A)
-> (0 <= (1 - A) * (1 - A))
-> (0 <= (1 - A) * (B - 1))
-> (0 <= (1 - A) * (B - x))
-> (0 <= (1 - A) * (B - y))
-> (0 <= (1 - A) * u)
-> (0 <= (1 - A) * v)
-> (0 <= (1 - A) * (A - u))
-> (0 <= (1 - A) * (A - v))
-> (0 <= (B - 1) * A)
-> (0 <= (B - 1) * (1 - A))
-> (0 <= (B - 1) * (B - 1))
-> (0 <= (B - 1) * (B - x))
-> (0 <= (B - 1) * (B - y))
-> (0 <= (B - 1) * u)
-> (0 <= (B - 1) * v)
-> (0 <= (B - 1) * (A - u))
-> (0 <= (B - 1) * (A - v))
-> (0 <= (B - x) * A)
-> (0 <= (B - x) * (1 - A))
-> (0 <= (B - x) * (B - 1))
-> (0 <= (B - x) * (B - x))
-> (0 <= (B - x) * (B - y))
-> (0 <= (B - x) * u)
-> (0 <= (B - x) * v)
-> (0 <= (B - x) * (A - u))
-> (0 <= (B - x) * (A - v))
-> (0 <= (B - y) * A)
-> (0 <= (B - y) * (1 - A))
-> (0 <= (B - y) * (B - 1))
-> (0 <= (B - y) * (B - x))
-> (0 <= (B - y) * (B - y))
-> (0 <= (B - y) * u)
-> (0 <= (B - y) * v)
-> (0 <= (B - y) * (A - u))
-> (0 <= (B - y) * (A - v))
-> (0 <= u * A)
-> (0 <= u * (1 - A))
-> (0 <= u * (B - 1))
-> (0 <= u * (B - x))
-> (0 <= u * (B - y))
-> (0 <= u * u)
-> (0 <= u * v)
-> (0 <= u * (A - u))
-> (0 <= u * (A - v))
-> (0 <= v * A)
-> (0 <= v * (1 - A))
-> (0 <= v * (B - 1))
-> (0 <= v * (B - x))
-> (0 <= v * (B - y))
-> (0 <= v * u)
-> (0 <= v * v)
-> (0 <= v * (A - u))
-> (0 <= v * (A - v))
-> (0 < (A - u) * A)
-> (0 <= (A - u) * (1 - A))
-> (0 <= (A - u) * (B - 1))
-> (0 <= (A - u) * (B - x))
-> (0 <= (A - u) * (B - y))
-> (0 <= (A - u) * u)
-> (0 <= (A - u) * v)
-> (0 < (A - u) * (A - u))
-> (0 < (A - u) * (A - v))
-> (0 < (A - v) * A)
-> (0 <= (A - v) * (1 - A))
-> (0 <= (A - v) * (B - 1))
-> (0 <= (A - v) * (B - x))
-> (0 <= (A - v) * (B - y))
-> (0 <= (A - v) * u)
-> (0 <= (A - v) * v)
-> (0 < (A - v) * (A - u))
-> (0 < (A - v) * (A - v))
->
 u * y + v * x + u * v < 3 * A * B := by
  smt [a, a_1, a_2, a_3, a_4, a_5, a_6, a_7, a_8]
