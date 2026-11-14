/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomaz Gomes Mascarenhas
-/

module

public import Lean
public meta import Lean

public import Smt.Reconstruct.Prop.Core
public meta import Smt.Reconstruct.Prop.Core
public import Smt.Reconstruct.Util
public meta import Smt.Reconstruct.Util

@[expose] public section

namespace Smt.Reconstruct.Prop

open Lean Elab.Tactic Meta Expr Syntax
open Nat List Classical

theorem ite_eq (c : Prop) [h : Decidable c] (x y : α) : ite c ((ite c x y) = x) ((ite c x y) = y) := by
  cases h
  all_goals simp_all

theorem notImplies1 : ∀ {P Q : Prop}, ¬ (P → Q) → P := by
  intros P Q h
  cases Classical.em P with
  | inl p  => exact p
  | inr np => apply False.elim
              apply h
              intro p
              exact False.elim (np p)

theorem notImplies2 : ∀ {P Q : Prop}, ¬ (P → Q) → ¬ Q := by
  intros P Q h
  cases Classical.em Q with
  | inl q  => exact False.elim (h (λ _ => q))
  | inr nq => exact nq

theorem contradiction : ∀ {P : Prop}, P → ¬ P → False := λ p np => np p

theorem orComm : ∀ {P Q : Prop}, P ∨ Q → Q ∨ P := by
  intros P Q h
  cases h with
  | inl hp => exact Or.inr hp
  | inr hq => exact Or.inl hq

theorem orAssocDir : ∀ {P Q R: Prop}, P ∨ Q ∨ R → (P ∨ Q) ∨ R := by
  intros P Q R h
  cases h with
  | inl h₁ => exact Or.inl (Or.inl h₁)
  | inr h₂ => cases h₂ with
              | inl h₃ => exact Or.inl (Or.inr h₃)
              | inr h₄ => exact Or.inr h₄

theorem orAssocConv : ∀ {P Q R : Prop}, (P ∨ Q) ∨ R → P ∨ Q ∨ R := by
  intros P Q R h
  cases h with
  | inl h₁ => cases h₁ with
              | inl h₃ => exact Or.inl h₃
              | inr h₄ => exact (Or.inr (Or.inl h₄))
  | inr h₂ => exact Or.inr (Or.inr h₂)

theorem congOrRight : ∀ {P Q R : Prop}, (P → Q) → P ∨ R → Q ∨ R := by
  intros P Q R h₁ h₂
  cases h₂ with
  | inl h₃ => exact Or.inl (h₁ h₃)
  | inr h₄ => exact Or.inr h₄

theorem congOrLeft : ∀ {P Q R : Prop}, (P → Q) → R ∨ P → R ∨ Q := by
  intros P Q R h₁ h₂
  apply orComm
  exact congOrRight h₁ (orComm h₂)

theorem orImplies : ∀ {p q : Prop}, (¬ p → q) → p ∨ q :=
  by intros p q h
     exact match Classical.em p with
     | Or.inl pp => Or.inl pp
     | Or.inr npp => match Classical.em q with
                     | Or.inl pq => Or.inr pq
                     | Or.inr npq => False.elim (npq (h npp))

theorem orImplies₃ : ∀ {p q : Prop}, p ∨ q → ¬ p → q := by
  intros P Q h np
  cases h with
  | inl p => exact False.elim (np p)
  | inr q => exact q

theorem impliesElim : ∀ {p q : Prop}, (p → q) → ¬ p ∨ q :=
  by intros p q h
     exact match Classical.em p with
     | Or.inl pp =>  Or.inr (h pp)
     | Or.inr npp => Or.inl npp

theorem deMorganSmall : ∀ {p q : Prop}, ¬ (p ∨ q) → ¬ p ∧ ¬ q :=
  by intros p q h
     exact match Classical.em p, Classical.em q with
     | Or.inl pp,  _          => False.elim (h (Or.inl pp))
     | Or.inr _,   Or.inl pq  => False.elim (h (Or.inr pq))
     | Or.inr npp, Or.inr npq => And.intro npp npq

theorem deMorganSmall₂ : ∀ {p q : Prop}, ¬ p ∧ ¬ q → ¬ (p ∨ q) :=
  by intros p q h
     have ⟨np, nq⟩ := h
     exact match Classical.em p, Classical.em q with
     | Or.inl pp,  _   => False.elim (np pp)
     | _        ,  Or.inl pq  => False.elim (nq pq)
     | Or.inr npp, Or.inr npq => λ h₂ =>
                                    match h₂ with
                                    | Or.inl pp => False.elim (npp pp)
                                    | Or.inr pq => False.elim (npq pq)

theorem deMorganSmall₃ : ∀ {p q : Prop}, ¬ (p ∧ q) → ¬ p ∨ ¬ q :=
  by intros p q h
     match Classical.em p, Classical.em q with
     | Or.inl hp, Or.inl hq  => exact False.elim (h (And.intro hp hq))
     | _,         Or.inr hnq => exact Or.inr hnq
     | Or.inr hnp, _        => exact Or.inl hnp

theorem notNotElim : ∀ {p : Prop}, ¬ ¬ p → p :=
  by intros p h
     exact match Classical.em p with
     | Or.inl pp => pp
     | Or.inr np => False.elim (h (λ p => np p))

theorem notNotIntro : ∀ {p : Prop}, p → ¬ ¬ p := λ p np => np p

theorem deMorgan : ∀ {l : List Prop}, ¬ orN (notN l) → andN l := by
  intros l h
  exact match l with
  | []   => True.intro
  | [t]  => by
    simp only [andN]
    simp only [notN, orN, map] at h
    cases Classical.em t with
    | inl tt  => exact tt
    | inr ntt => exact False.elim (h ntt)
  | h₁::h₂::t => by
    simp only [orN, notN, map] at h
    have ⟨ t₁, t₂ ⟩ := deMorganSmall h
    have ih := @deMorgan (h₂::t) t₂
    simp [andN]
    have t₁' := notNotElim t₁
    exact ⟨ t₁', andN_cons_append ▸ ih ⟩

theorem deMorgan₂ : ∀ {l : List Prop}, andN l → ¬ orN (notN l) := by
  intros l h
  exact match l with
  | [] => by
    simp [orN, notN]
  | [t] => by
    simp only [notN]
    simp [andN] at h
    exact notNotIntro h
  | h₁::h₂::t => by
    simp only [orN, notN, map]
    simp [andN] at h
    apply deMorganSmall₂
    have nnh₁ := notNotIntro (And.left h)
    have ih := @deMorgan₂ (h₂::t) (And.right (andN_cons_append ▸ h))
    exact ⟨nnh₁, ih⟩

theorem iteIntro {α : Type u} {c : Prop} {t e : α} : ite c ((ite c t e) = t) ((ite c t e) = e) := by
  match Classical.em c with
  | Or.inl hc  => rw [ite_eq_left hc, ite_eq_left hc]
  | Or.inr hnc => rw [ite_eq_right hnc, ite_eq_right hnc]

theorem congrIte [Decidable c₁] [Decidable c₂] {t₁ t₂ e₁ e₂ : α} :
    c₁ = c₂ → t₁ = t₂ → e₁ = e₂ → ite c₁ t₁ e₁ = ite c₂ t₂ e₂ := by
  intros h₁ h₂ h₃
  simp only [h₁, h₂, h₃]

theorem congrHAdd {α β γ : Type} [HAdd α β γ] : ∀ {a₁ a₂ : α} {b₁ b₂ : β},
    a₁ = a₂ → b₁ = b₂ → a₁ + b₁ = a₂ + b₂ := by
  intros a₁ a₂ b₁ b₂ h₁ h₂
  rw [h₁, h₂]

theorem dupOr {P Q : Prop} : P ∨ P ∨ Q → P ∨ Q := λ h =>
  match h with
  | Or.inl p          => Or.inl p
  | Or.inr (Or.inl p) => Or.inl p
  | Or.inr (Or.inr q) => Or.inr q

theorem dupOr₂ {P : Prop} : P ∨ P → P := λ h =>
  match h with
  | Or.inl p => p
  | Or.inr p => p

theorem and_elim (hps : andN ps) (i : Nat) {hi : i < ps.length} : ps[i] := match ps with
  | []  => nomatch hi
  | [_] => match i with
    | 0     => hps
    | _ + 1 => nomatch hi
  | p₁ :: p₂ :: ps => match i with
    | 0     => hps.left
    | i + 1 => Eq.symm (List.getElem_cons_succ p₁ (p₂ :: ps) i hi) ▸ and_elim hps.right i

theorem not_or_elim (hnps : ¬orN ps) (i : Nat) {hi : i < ps.length} : ¬ps[i] := match ps with
  | []  => nomatch hi
  | [_] => match i with
    | 0     => hnps
    | _ + 1 => nomatch hi
  | p₁ :: p₂ :: ps => match i with
    | 0     => (deMorganSmall hnps).left
    | i + 1 => Eq.symm (List.getElem_cons_succ p₁ (p₂ :: ps) i hi) ▸ not_or_elim (deMorganSmall hnps).right i

public meta section

def andElimMeta (mvar : MVarId) (val : Expr) (i : Nat) (name : Name)
  : MetaM MVarId :=
    mvar.withContext do
      let mut pf ← getProof i val
      let type ←  inferType val
      let binderName ← getFirstBinderName type
      let env ← getEnv
      let andProp : Expr :=
        match (env.find? binderName).get!.value? with
        | none => type
        | some e => recGetLamBody e
      if i < getLengthAnd andProp - 1 then
        pf ← mkAppM ``And.left #[pf]
      let goal ← inferType pf
      let (_, mvar') ← MVarId.intro1P $ ← mvar.assert name goal pf
      return mvar'
where
  recGetLamBody (e : Expr) : Expr :=
    match e with
    | lam _ _ b _ => recGetLamBody b
    | e => e
  getProof (i : Nat) (hyp : Expr) : MetaM Expr :=
    match i with
    | 0 => pure hyp
    | (i + 1) => do
      let rc ← getProof i hyp
      mkAppM ``And.right #[rc]

def andElim (mv : MVarId) (val : Expr) (i : Nat) : MetaM Unit :=
    mv.withContext do
      let mut pf ← getProof i val
      let type ←  inferType val
      let binderName ← getFirstBinderName type
      let env ← getEnv
      let andProp : Expr :=
        match (env.find? binderName).get!.value? with
        | none => type
        | some e => recGetLamBody e
      if i < getLengthAnd andProp - 1 then
        pf ← mkAppM ``And.left #[pf]
      mv.assign pf
where
  recGetLamBody (e : Expr) : Expr :=
    match e with
    | lam _ _ b _ => recGetLamBody b
    | e => e
  getProof (i : Nat) (hyp : Expr) : MetaM Expr :=
    match i with
    | 0 => pure hyp
    | (i + 1) => do
      let rc ← getProof i hyp
      mkAppM ``And.right #[rc]

namespace Tactic

syntax (name := andElim) "andElim" term "," term : tactic
@[tactic andElim] def evalAndElim : Tactic := fun stx => do
  withMainContext do
    trace[smt.profile.reconstruct] m!"[andElim] start time: {← IO.monoNanosNow}ns"
    let mvar ← getMainGoal
    let val ← elabTerm stx[1] none
    let idx: Term := ⟨stx[3]⟩
    let i ← stxToNat idx
    let fname ← mkFreshId
    let mvar' ← andElimMeta mvar val i fname
    replaceMainGoal [mvar']
    evalTactic (← `(tactic| exact $(mkIdent fname)))
    trace[smt.profile.reconstruct] m!"[andElim] end time: {← IO.monoNanosNow}ns"

end Tactic

def notOrElimMeta (mvar : MVarId) (val : Expr) (i : Nat) (name : Name)
  : MetaM MVarId :=
    mvar.withContext do
      let type ← inferType val
      let orChain := notExpr type
      let props ← collectPropsInOrChain orChain
      let prop := props[i]!
      withLocalDeclD (← mkFreshId) prop $ fun bv => do
        let pf: Expr ←
          match (← getLength orChain) == i + 1 with
          | true  => pure bv
          | false =>
            let rest ← createOrChain (props.drop (i + 1))
            mkAppOptM ``Or.inl #[none, rest, bv]
        let pf ← getProof i 0 props pf
        let pf := mkApp val pf
        let pf ← mkLambdaFVars #[bv] pf
        let notProp := mkApp (mkConst ``Not) prop
        let (_, mvar') ← MVarId.intro1P $ ← mvar.assert name notProp pf
        return mvar'
where
  getProof (i j : Nat) (props : List Expr) (val : Expr) : MetaM Expr :=
    match i with
    | 0     => pure val
    | i + 1 => do
      let currProp := props[j]!
      mkAppOptM ``Or.inr #[currProp, none, ← getProof i (j + 1) props val]

def traceNotOrElim (r : Except Exception Unit) : MetaM MessageData :=
  return match r with
  | .ok _ => m!"{checkEmoji}"
  | _     => m!"{bombEmoji}"

def notOrElim (mv : MVarId) (val : Expr) (i : Nat) : MetaM Unit := withTraceNode `smt.reconstruct.notOrElim traceNotOrElim do
    mv.withContext do
      let type ← inferType val
      let orChain := notExpr type
      let props ← collectPropsInOrChain orChain
      let prop := props[i]!
      withLocalDeclD (← mkFreshId) prop $ fun bv => do
        let pf: Expr ←
          match (← getLength orChain) == i + 1 with
          | true  => pure bv
          | false =>
            let rest ← createOrChain (props.drop (i + 1))
            mkAppOptM ``Or.inl #[none, rest, bv]
        let pf ← getProof i 0 props pf
        let pf := mkApp val pf
        let pf ← mkLambdaFVars #[bv] pf
        mv.assign pf
where
  getProof (i j : Nat) (props : List Expr) (val : Expr) : MetaM Expr :=
    match i with
    | 0     => pure val
    | i + 1 => do
      let currProp := props[j]!
      mkAppOptM ``Or.inr #[currProp, none, ← getProof i (j + 1) props val]

namespace Tactic

syntax (name := notOrElim) "notOrElim" term "," term : tactic
@[tactic notOrElim] def evalNotOrElim : Tactic := fun stx => do
  withMainContext do
    trace[smt.profile.reconstruct] m!"[notOrElim] start time: {← IO.monoNanosNow}ns"
    let i ← stxToNat ⟨stx[3]⟩
    let val ← elabTerm stx[1] none
    let fname ← mkFreshId
    let mvar ← getMainGoal
    let mvar' ← notOrElimMeta mvar val i fname
    replaceMainGoal [mvar']
    evalTactic (← `(tactic| exact $(mkIdent fname)))
    trace[smt.profile.reconstruct] m!"[notOrElim] end time: {← IO.monoNanosNow}ns"

end Tactic

theorem trueImplies {p : Prop} : (True → p) → p := by
  intro htp
  exact htp trivial

theorem trueElim : ∀ {A : Prop}, A = True → A := by
  intros A h
  rewrite [h]
  trivial
theorem trueElim₂ : ∀ {A : Prop}, True = A → A :=
  trueElim ∘ Eq.symm

theorem falseIntro : ∀ {A : Prop}, ¬ A → A = False :=
  λ h => propext (Iff.intro (λ a => h a) (λ ff => False.elim ff))
theorem falseIntro₂ : ∀ {A : Prop}, ¬ A → False = A := Eq.symm ∘ falseIntro

theorem falseElim : ∀ {A : Prop}, A = False → ¬ A := λ h ha =>
  match h with
  | rfl => ha
theorem falseElim₂ : ∀ {A : Prop}, False = A → ¬ A := falseElim ∘ Eq.symm

theorem negSymm {α : Type u} {a b : α} : a ≠ b → b ≠ a := λ h f => h (Eq.symm f)

theorem orN_cons : orN (t :: l) = (t ∨ orN l) := by
  cases l with
  | nil => simp [orN]
  | cons t' l => simp [orN]

theorem orN_eraseIdx (hj : j < qs.length) : (orN (qs.eraseIdx j) ∨ qs[j]) = (orN qs) := by
  revert j
  induction qs with
  | nil =>
    intro j hj
    simp at hj
  | cons t l ih =>
    intro j hj
    cases j with
    | zero =>
      simp only [eraseIdx_cons_zero, getElem_cons_zero, orN_cons]
      rw [or_comm]
    | succ j =>
      simp only [getElem_cons_succ, orN_cons, eraseIdx, or_assoc]
      congr
      rw [@ih j (by rw [length_cons, succ_lt_succ_iff] at hj; exact hj)]

def subList' (xs : List α) (i j : Nat) : List α :=
  List.drop i (xs.take j)

theorem orN_subList (hps : orN ps) (hpq : ps = subList' qs i j): orN qs := by
  revert i j ps
  induction qs with
  | nil =>
    intro ps i j hp hps
    simp [subList', *] at *; assumption
  | cons t l ih =>
    simp only [subList'] at *
    intro ps i j hp hps
    rw [orN_cons]
    cases j with
    | zero =>
      simp [*, orN] at *
    | succ j =>
      simp only [List.take_succ_cons] at hps
      cases i with
      | zero =>
        simp only [hps, orN_cons, drop_zero] at hp
        exact congOrLeft (fun hp => @ih (drop 0 (take j l)) 0 j (by simp [hp]) rfl) hp
      | succ i =>
        apply Or.inr
        apply @ih ps i j hp
        simp [hps]

theorem length_take (h : n ≤ l.length) : (take n l).length = n := by
  revert n
  induction l with
  | nil => intro n h; simp at h; simp [h]
  | cons t l ih =>
    intro n h
    cases n with
    | zero => simp
    | succ n => simp [ih (by rw [length_cons, succ_le_succ_iff] at h; exact h)]

theorem length_eraseIdx (h : i < l.length) : (eraseIdx l i).length = l.length -1 := by
  revert i
  induction l with
  | nil => simp
  | cons t l ih =>
    intro i hi
    cases i with
    | zero => simp
    | succ i =>
      simp
      rw [length_cons, succ_lt_succ_iff] at hi
      rw [ih hi, Nat.sub_add_cancel (zero_lt_of_lt hi)]

theorem take_append (a b : List α) : take a.length (a ++ b) = a := by
  have H3:= take_append_drop a.length (a ++ b)
  apply (append_inj H3 _).1
  rw [length_take]
  rw [length_append]
  apply le_add_right

theorem drop_append (a b : List α): drop a.length (a ++ b) = b := by
  have H3:= take_append_drop a.length (a ++ b)
  apply (append_inj H3 _).2
  rw [length_take]
  rw [length_append]
  apply le_add_right

theorem orN_append_left (hps : orN ps) : orN (ps ++ qs) := by
  apply @orN_subList ps (ps ++ qs) 0 ps.length hps
  simp [subList']

theorem orN_append_right (hqs : orN qs) : orN (ps ++ qs) := by
  apply @orN_subList qs (ps ++ qs) ps.length (ps.length + qs.length) hqs
  simp only [←length_append, subList', take_length, drop_append]

theorem orN_resolution (hps : orN ps) (hqs : orN qs) (hi : i < ps.length) (hj : j < qs.length) (hij : ps[i] = ¬qs[j]) : orN (ps.eraseIdx i ++ qs.eraseIdx j) := by
  have H1 := orN_eraseIdx hj
  have H2 := orN_eraseIdx hi
  by_cases h : ps[i]
  · simp only [eq_iff_iff, true_iff, iff_true, h, hqs, hps] at *
    apply orN_append_right (by simp [*] at *; exact H1)
  · simp only [hps, hqs, h, eq_iff_iff, false_iff, not_not, iff_true, or_false,
    not_false_eq_true] at *
    apply orN_append_left H2

theorem implies_of_not_and : ¬(andN (ps ++ [¬q])) → impliesN ps q := by
  induction ps with
  | nil => exact notNotElim
  | cons p ps ih =>
    simp only [impliesN]
    intro hnpps hp
    cases ps
    <;> have hnpnps := deMorganSmall₃ hnpps
    <;> match hnpnps with
        | .inl hnp => contradiction
        | .inr hnps => exact ih hnps

theorem implies_false_of_not_and : ¬(andN ps) → impliesN ps False := by
  simp_all [implies_of_not_and]

syntax "flipCongrArg " term ("[" term "]")? : term
macro_rules
| `(flipCongrArg $premiss:term [$arg:term]) => `(congrArg $arg $premiss)

syntax "smtIte" (term)? (term)? (term)? (term)? : term
macro_rules
| `(smtIte $cond $t $e $type) => `(term| @ite $type $cond (propDecidable $cond) $t $e)

end

end Smt.Reconstruct.Prop
