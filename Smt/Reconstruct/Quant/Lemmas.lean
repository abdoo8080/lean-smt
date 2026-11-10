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

theorem forall_congr_bool {α : Sort u} {p q : α → Bool} (h : ∀ x, p x = q x) :
    Bool.forall p = Bool.forall q :=
  congrArg Bool.forall (funext h)

theorem bool_eq_of_imp {a b : Bool} (h₁ : a = true → b = true) (h₂ : b = true → a = true) : a = b :=
  Bool.eq_iff_iff.mpr ⟨h₁, h₂⟩

theorem exists_eq_not_forall {α : Sort u} {p q : α → Bool} (h : ∀ x, p x = !q x) :
    Bool.exists p = !Bool.forall q := by
  apply Bool.eq_iff_iff.mpr
  simp [Bool.exists_eq_true, Bool.forall_eq_false, h]

theorem forall_const_bool (α : Sort u) [Nonempty α] {b c : Bool} (h : b = c) :
    Bool.forall (fun _ : α => b) = c := by
  subst h
  apply Bool.eq_iff_iff.mpr
  rw [Bool.forall_eq_true]
  exact ⟨fun h => h (Classical.ofNonempty), fun h _ => h⟩

theorem forall_andN {α : Type u} {ps : List (α → Bool)} :
    Bool.forall (fun x => Bool.andN (ps.map (· x))) = Bool.andN (ps.map Bool.forall) := by
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.forall_eq_true, Bool.andN_eq_true, List.mem_map]
  constructor
  · rintro h _ ⟨p, hp, rfl⟩
    rw [Bool.forall_eq_true]
    exact fun x => h x _ ⟨p, hp, rfl⟩
  · rintro h x _ ⟨p, hp, rfl⟩
    have := h _ ⟨p, hp, rfl⟩
    rw [Bool.forall_eq_true] at this
    exact this x

theorem forall_orN {α : Sort u} {ps : List Bool} {q : α → Bool} {rs : List Bool} :
    Bool.forall (fun x => Bool.orN (ps ++ q x :: rs)) = Bool.orN (ps ++ Bool.forall q :: rs) := by
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

theorem var_elim_eq_bool {α : Type u} [DecidableEq α] {t : α} :
    Bool.forall (fun x => !@BEq.beq α instBEqOfDecidableEq x t) = false := by
  rw [Bool.eq_false_iff]
  intro h
  simpa using forall_elim h t

theorem var_elim_eq_or_bool {α : Type u} [DecidableEq α] {t : α} {b : α → Bool} :
    Bool.forall (fun x => !@BEq.beq α instBEqOfDecidableEq x t || b x) = b t := by
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
