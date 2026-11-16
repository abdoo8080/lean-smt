/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomaz Gomes Mascarenhas
-/

module

public import Smt.Reconstruct.Bool.Core
public import Smt.Reconstruct.Prop.Core

@[expose] public section

namespace Smt.Reconstruct.Quant

/-! ### Quantifiers over Boolean formulas -/

theorem forall_elim {α : Sort u} {p : α → Bool} (h : Bool.forall p = true) (x : α) : p x = true :=
  (Bool.forall_eq_true ▸ h) x

theorem forall_intro {α : Sort u} {p : α → Bool} (h : ∀ x, p x = true) : Bool.forall p = true :=
  Bool.forall_eq_true ▸ h

theorem forall_congr_bool {α : Sort u} {p q : α → Bool} (h : ∀ x, Bool.eq (p x) (q x)) :
    Bool.eq (Bool.forall p) (Bool.forall q) :=
  Bool.eq.of_eq (congrArg Bool.forall (funext fun x => (h x).to_eq))

theorem exists_congr_bool {α : Sort u} {p q : α → Bool} (h : ∀ x, Bool.eq (p x) (q x)) :
    Bool.eq (Bool.exists p) (Bool.exists q) :=
  Bool.eq.of_eq (congrArg Bool.exists (funext fun x => (h x).to_eq))

theorem bool_eq_of_imp {a b : Bool} (h₁ : a = true → b = true) (h₂ : b = true → a = true) :
    Bool.eq a b :=
  Bool.eq.of_eq (Bool.eq_iff_iff.mpr ⟨h₁, h₂⟩)

theorem exists_eq_not_forall {α : Sort u} {p q : α → Bool} (h : ∀ x, Bool.eq (p x) (!q x)) :
    Bool.eq (Bool.exists p) (!Bool.forall q) := by
  apply Bool.eq.of_eq
  apply Bool.eq_iff_iff.mpr
  simp [Bool.exists_eq_true, Bool.forall_eq_false, fun x => (h x).to_eq]

theorem forall_const_bool (α : Sort u) [Nonempty α] {b c : Bool} (h : Bool.eq b c) :
    Bool.eq (Bool.forall (fun _ : α => b)) c := by
  apply Bool.eq.of_eq
  have h := h.to_eq
  subst h
  apply Bool.eq_iff_iff.mpr
  rw [Bool.forall_eq_true]
  exact ⟨fun h => h (Classical.ofNonempty), fun h _ => h⟩

/-- A list in any universe: `List (α → Bool)` needs `α : Type u`, but the variables of quantifiers
may be in `Sort u`. Mainly for `miniscope_andN`. -/
inductive PList (α : Sort u) where
  | nil : PList α
  | cons (head : α) (tail : PList α) : PList α

def PList.map {α : Sort u} {β : Sort v} (f : α → β) : PList α → PList β
  | .nil      => .nil
  | .cons h t => .cons (f h) (map f t)

def PList.toList {α : Type u} : PList α → List α
  | .nil      => []
  | .cons h t => h :: toList t

theorem miniscope_andN {α : Sort u} {ps : PList (α → Bool)} :
    Bool.eq (Bool.forall (fun x => Bool.andN (ps.map (· x)).toList))
      (Bool.andN (ps.map Bool.forall).toList) := by
  apply Bool.eq.of_eq
  induction ps with
  | nil =>
    apply Bool.eq_iff_iff.mpr
    simp [PList.map, PList.toList, Bool.andN]
  | cons p ps ih =>
    simp only [PList.map, PList.toList, Bool.andN_cons_append, ← ih]
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.forall_eq_true, Bool.and_eq_true]
    exact forall_and

theorem miniscope_orN {α : Sort u} {ps : List Bool} {q : α → Bool} {rs : List Bool} :
    Bool.eq (Bool.forall (fun x => Bool.orN (ps ++ q x :: rs)))
      (Bool.orN (ps ++ Bool.forall q :: rs)) := by
  apply Bool.eq.of_eq
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.forall_eq_true, Bool.orN_eq_true, List.mem_append, List.mem_cons]
  constructor
  · intro h
    by_cases hp : ∃ b, (b ∈ ps ∨ b ∈ rs) ∧ b = true
    · obtain ⟨b, hb, hbt⟩ := hp
      exact ⟨b, hb.elim Or.inl (Or.inr ∘ Or.inr), hbt⟩
    · refine ⟨Bool.forall q, Or.inr (Or.inl rfl), ?_⟩
      rw [Bool.forall_eq_true]
      intro x
      obtain ⟨b, hb, hbt⟩ := h x
      rcases hb with hb | hb | hb
      · exact absurd ⟨b, Or.inl hb, hbt⟩ hp
      · exact hb ▸ hbt
      · exact absurd ⟨b, Or.inr hb, hbt⟩ hp
  · rintro ⟨b, hb, hbt⟩ x
    rcases hb with hb | hb | hb
    · exact ⟨b, Or.inl hb, hbt⟩
    · subst hb
      rw [Bool.forall_eq_true] at hbt
      exact ⟨q x, Or.inr (Or.inl rfl), hbt x⟩
    · exact ⟨b, Or.inr (Or.inr hb), hbt⟩

theorem forall_skolem {α : Sort u} [h : Nonempty α] {p : α → Bool} (hp : (!Bool.forall p) = true) :
    (!p (@Classical.epsilon α h (fun x => ¬p x = true))) = true := by
  have hp : ¬∀ x, p x = true := fun h' => by simp [Eq.mpr Bool.forall_eq_true h'] at hp
  have hx : ∃ x, ¬p x = true := Classical.not_forall.mp hp
  simpa using Classical.epsilon_spec hx

theorem var_elim_eq_bool {α : Sort u} [DecidableEq α] {t : α} :
    Bool.eq (Bool.forall (fun x => !decide (x = t))) false := by
  apply Bool.eq.of_eq
  rw [Bool.eq_false_iff]
  intro h
  simpa using forall_elim h t

theorem var_elim_eq_or_bool {α : Sort u} [DecidableEq α] {t : α} {b : α → Bool} :
    Bool.eq (Bool.forall (fun x => !decide (x = t) || b x)) (b t) := by
  apply Bool.eq.of_eq
  apply Bool.eq_iff_iff.mpr
  rw [Bool.forall_eq_true]
  constructor
  · intro h
    simpa using h t
  · intro h x
    by_cases hx : x = t
    · subst hx; simp [h]
    · simp [hx]

end Smt.Reconstruct.Quant
