/-
Copyright (c) 2021-2024 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

module

public import Smt.Reconstruct.Bool.Core
public import Smt.Reconstruct.Prop.Core

@[expose] public section

namespace Smt.Reconstruct.Bool

/-! ### Proof rules of propositional logic over `Bool`

The proof of an SMT formula `φ` is a proof of `⟦φ⟧ = true`. The n-ary formulas below match cvc5's
n-ary terms definitionally, e.g., `Bool.andN [a, b, c]` is `a && (b && c)`. -/

theorem orN_eq_true_iff_mem {bs : List Bool} : Bool.orN bs = true ↔ true ∈ bs := by
  simp [Bool.orN_eq_true]

theorem andN_eq_true_iff {bs : List Bool} : Bool.andN bs = true ↔ ∀ b ∈ bs, b = true := by
  simp [Bool.andN_eq_true]

theorem orN_eq_false_iff {bs : List Bool} : Bool.orN bs = false ↔ ∀ b ∈ bs, b = false := by
  induction bs with
  | nil => simp [Bool.orN]
  | cons b bs ih => simp [ih]

theorem andN_eq_false_iff_mem {bs : List Bool} : Bool.andN bs = false ↔ false ∈ bs := by
  induction bs with
  | nil => simp [Bool.andN]
  | cons b bs ih => cases b <;> simp [ih]

theorem eq_resolve' {p q : Bool} (hp : p = true) (hpq : p = q) : q = true := hpq ▸ hp

theorem modus_ponens {p q : Bool} (hp : p = true) (hpq : p.smtImp q = true) : q = true := by
  cases p <;> cases q <;> simp_all [Bool.smtImp]

theorem not_not_elim {p : Bool} (h : (!!p) = true) : p = true := by simpa using h

theorem contradiction {p : Bool} (hp : p = true) (hnp : (!p) = true) : false = true := by
  simp_all

theorem and_intro {p q : Bool} (hp : p = true) (hq : q = true) : (p && q) = true := by
  simp [hp, hq]

theorem and_elim {ps : List Bool} (hps : Bool.andN ps = true) (i : Nat) (hi : i < ps.length) :
    ps[i] = true :=
  andN_eq_true_iff.mp hps _ (List.getElem_mem hi)

theorem not_or_elim {ps : List Bool} (hps : (!Bool.orN ps) = true) (i : Nat) (hi : i < ps.length) :
    (!ps[i]) = true := by
  have h := orN_eq_false_iff.mp (by simpa using hps) _ (List.getElem_mem hi)
  simp [h]

theorem implies_elim {p q : Bool} (h : p.smtImp q = true) : (!p || q) = true := h

theorem not_implies_elim1 {p q : Bool} (h : (!p.smtImp q) = true) : p = true := by
  cases p <;> cases q <;> simp_all [Bool.smtImp]

theorem not_implies_elim2 {p q : Bool} (h : (!p.smtImp q) = true) : (!q) = true := by
  cases p <;> cases q <;> simp_all [Bool.smtImp]

theorem equiv_elim1 {p q : Bool} (h : smtEq p q = true) : (!p || q) = true := by
  cases eq_of_smtEq h; cases p <;> rfl

theorem equiv_elim2 {p q : Bool} (h : smtEq p q = true) : (p || !q) = true := by
  cases eq_of_smtEq h; cases p <;> rfl

theorem not_equiv_elim1 {p q : Bool} (h : (!smtEq p q) = true) :
    (p || q) = true := by
  cases p <;> cases q <;> simp_all

theorem not_equiv_elim2 {p q : Bool} (h : (!smtEq p q) = true) :
    (!p || !q) = true := by
  cases p <;> cases q <;> simp_all

theorem xor_elim1 {p q : Bool} (h : xor p q = true) : (p || q) = true := by
  cases p <;> cases q <;> simp_all

theorem xor_elim2 {p q : Bool} (h : xor p q = true) : (!p || !q) = true := by
  cases p <;> cases q <;> simp_all

theorem not_xor_elim1 {p q : Bool} (h : (!xor p q) = true) : (p || !q) = true := by
  cases p <;> cases q <;> simp_all

theorem not_xor_elim2 {p q : Bool} (h : (!xor p q) = true) : (!p || q) = true := by
  cases p <;> cases q <;> simp_all

theorem not_and {ps : List Bool} (h : (!Bool.andN ps) = true) : Bool.orN (ps.map not) = true := by
  have h' : Bool.andN ps = false := by simpa using h
  rw [andN_eq_false_iff_mem] at h'
  rw [orN_eq_true_iff_mem, List.mem_map]
  exact ⟨false, h', rfl⟩

theorem cnf_and_pos (ps : List Bool) (i : Nat) : (!Bool.andN ps || ps.getD i true) = true := by
  cases h : Bool.andN ps
  · rfl
  · simp only [Bool.not_true, Bool.false_or, List.getD_eq_getElem?_getD]
    rcases Nat.lt_or_ge i ps.length with hi | hi
    · rw [List.getElem?_eq_getElem hi]
      exact andN_eq_true_iff.mp h _ (List.getElem_mem hi)
    · rw [List.getElem?_eq_none hi]; rfl

theorem cnf_and_neg (ps : List Bool) : Bool.orN (Bool.andN ps :: ps.map not) = true := by
  rw [orN_eq_true_iff_mem]
  cases h : Bool.andN ps
  · rw [andN_eq_false_iff_mem] at h
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨false, h, rfl⟩)
  · exact List.mem_cons_self

theorem cnf_or_pos (ps : List Bool) : Bool.orN ((!Bool.orN ps) :: ps) = true := by
  rw [orN_eq_true_iff_mem]
  cases h : Bool.orN ps
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ (orN_eq_true_iff_mem.mp h)

theorem cnf_or_neg (ps : List Bool) (i : Nat) : (Bool.orN ps || !ps.getD i false) = true := by
  cases h : Bool.orN ps
  · simp only [Bool.false_or, List.getD_eq_getElem?_getD]
    rcases Nat.lt_or_ge i ps.length with hi | hi
    · rw [List.getElem?_eq_getElem hi]
      simp [orN_eq_false_iff.mp h _ (List.getElem_mem hi)]
    · rw [List.getElem?_eq_none hi]; rfl
  · rfl

theorem cnf_implies_pos (p q : Bool) : (!p.smtImp q || (!p || q)) = true := by
  cases p <;> cases q <;> rfl
theorem cnf_implies_neg1 (p q : Bool) : (p.smtImp q || p) = true := by
  cases p <;> cases q <;> rfl
theorem cnf_implies_neg2 (p q : Bool) : (p.smtImp q || !q) = true := by
  cases p <;> cases q <;> rfl

theorem cnf_equiv_pos1 (p q : Bool) : (!smtEq p q || (!p || q)) = true := by
  cases p <;> cases q <;> simp
theorem cnf_equiv_pos2 (p q : Bool) : (!smtEq p q || (p || !q)) = true := by
  cases p <;> cases q <;> simp
theorem cnf_equiv_neg1 (p q : Bool) : (smtEq p q || (p || q)) = true := by
  cases p <;> cases q <;> simp
theorem cnf_equiv_neg2 (p q : Bool) : (smtEq p q || (!p || !q)) = true := by
  cases p <;> cases q <;> simp

theorem cnf_xor_pos1 (p q : Bool) : (!xor p q || (p || q)) = true := by cases p <;> cases q <;> rfl
theorem cnf_xor_pos2 (p q : Bool) : (!xor p q || (!p || !q)) = true := by cases p <;> cases q <;> rfl
theorem cnf_xor_neg1 (p q : Bool) : (xor p q || (!p || q)) = true := by cases p <;> cases q <;> rfl
theorem cnf_xor_neg2 (p q : Bool) : (xor p q || (p || !q)) = true := by cases p <;> cases q <;> rfl

theorem true_intro {p : Bool} (h : p = true) : smtEq p true = true := smtEq_of_eq h
theorem true_elim {p : Bool} (h : smtEq p true = true) : p = true := eq_of_smtEq h
theorem false_intro {p : Bool} (h : (!p) = true) : smtEq p false = true :=
  smtEq_of_eq (by simpa using h)
theorem false_elim {p : Bool} (h : smtEq p false = true) : (!p) = true := by
  simp [eq_of_smtEq h]

theorem orN_append_left {ps qs : List Bool} (hps : Bool.orN ps = true) :
    Bool.orN (ps ++ qs) = true := by
  simp [hps]

theorem orN_resolution {ps qs : List Bool} {i j : Nat} (hps : Bool.orN ps = true)
    (hqs : Bool.orN qs = true) (hi : i < ps.length) (hj : j < qs.length) (hij : ps[i] = !qs[j]) :
    Bool.orN (ps.eraseIdx i ++ qs.eraseIdx j) = true := by
  rw [orN_eq_true_iff_mem, List.mem_append]
  rw [orN_eq_true_iff_mem, List.mem_iff_getElem] at hps hqs
  cases h : ps[i]
  · obtain ⟨k, hk, hpk⟩ := hps
    refine .inl (List.mem_eraseIdx_iff_getElem.mpr ⟨k, hk, fun hki => ?_, hpk⟩)
    subst hki; simp_all
  · obtain ⟨k, hk, hqk⟩ := hqs
    refine .inr (List.mem_eraseIdx_iff_getElem.mpr ⟨k, hk, fun hkj => ?_, hqk⟩)
    subst hkj; simp_all

/-! ### Scopes and the final contradiction -/

theorem scopes {ps : List Bool} {q : Bool} (h : Bool.impliesN ps (q = true)) :
    (Bool.andN ps).smtImp q = true := by
  induction ps with
  | nil => simpa [Bool.impliesN, Bool.andN] using h
  | cons p ps ih =>
    simp only [Bool.impliesN] at h
    simp only [Bool.andN_cons_append, Bool.smtImp_eq_true, Bool.and_eq_true, and_imp]
    intro hp hps
    simpa [hps] using ih (h hp)

theorem scopes_false {ps : List Bool} (h : Bool.impliesN ps (false = true)) :
    (!Bool.andN ps) = true := by
  simpa [Bool.smtImp] using scopes h

theorem implies_false_of_not_and {ps : List Bool} (h : (!Bool.andN ps) = true) :
    Bool.impliesN ps False := by
  induction ps with
  | nil => simp [Bool.andN] at h
  | cons p ps ih =>
    intro hp
    cases ps with
    | nil => simp_all [Bool.andN]
    | cons q qs => exact ih (by simpa [hp] using h)

/-! ### `ite` over `Bool` conditions, reconstructed as `cond` -/

theorem ite_eq {α} (c : Bool) (x y : α) : cond c (smtEq (cond c x y) x) (smtEq (cond c x y) y) = true := by
  cases c <;> simp

theorem ite_elim1 {c p q : Bool} (h : cond c p q = true) : (!c || p) = true := by
  cases c <;> simp_all
theorem ite_elim2 {c p q : Bool} (h : cond c p q = true) : (c || q) = true := by
  cases c <;> simp_all
theorem not_ite_elim1 {c p q : Bool} (h : (!cond c p q) = true) : (!c || !p) = true := by
  cases c <;> simp_all
theorem not_ite_elim2 {c p q : Bool} (h : (!cond c p q) = true) : (c || !q) = true := by
  cases c <;> simp_all

theorem cnf_ite_pos1 (c p q : Bool) : (!cond c p q || (!c || p)) = true := by
  cases c <;> cases p <;> cases q <;> rfl
theorem cnf_ite_pos2 (c p q : Bool) : (!cond c p q || (c || q)) = true := by
  cases c <;> cases p <;> cases q <;> rfl
theorem cnf_ite_pos3 (c p q : Bool) : (!cond c p q || (p || q)) = true := by
  cases c <;> cases p <;> cases q <;> rfl
theorem cnf_ite_neg1 (c p q : Bool) : (cond c p q || (!c || !p)) = true := by
  cases c <;> cases p <;> cases q <;> rfl
theorem cnf_ite_neg2 (c p q : Bool) : (cond c p q || (c || !q)) = true := by
  cases c <;> cases p <;> cases q <;> rfl
theorem cnf_ite_neg3 (c p q : Bool) : (cond c p q || (!p || !q)) = true := by
  cases c <;> cases p <;> cases q <;> rfl

/-! ### Equality -/

theorem not_smtEq_symm {α} {a b : α} (h : (!smtEq a b) = true) : (!smtEq b a) = true := by
  simp only [Bool.not_eq_eq_eq_not, Bool.not_true, smtEq_eq_false] at h ⊢
  exact Ne.symm h

theorem eq_of_smtDecide_eq {p q : Prop} (h : smtDecide p = smtDecide q) : p = q := by
  rw [← smtDecide_eq_true (p := p), ← smtDecide_eq_true (p := q), h]

theorem not_eq_true_of_not {b : Bool} (h : ¬b = true) : (!b) = true := by simpa using h

end Smt.Reconstruct.Bool
