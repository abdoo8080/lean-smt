/-
Copyright (c) 2021-2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

module

public import Lean.Meta.Tactic.Simp
public meta import Lean.Meta.Tactic.Simp
public import Qq
public meta import Qq
public import Smt.Preprocess.Basic
public meta import Smt.Preprocess.Basic
public import Smt.Preprocess.Boolify.Attribute
public meta import Smt.Preprocess.Boolify.Attribute
public import Smt.Reconstruct.Bool.Core
public meta import Smt.Reconstruct.Bool.Core

/-!
# From propositions to Booleans

SMT-LIB's `Bool` sort is Lean's `Bool`: translation and proof reconstruction work with Boolean
formulas, and a proof of a formula `b` is a proof of `b = true`. This preprocessing step turns every
hypothesis `h : p` into `h' : b = true`, where the Boolean formula `b` is obtained by pushing
`smtDecide p` into the connectives, quantifiers, and atoms of `p`:

| proposition    | Boolean formula                          |
|----------------|------------------------------------------|
| `¬p`, `p ∧ q`, `p ∨ q` | `!b`, `b₁ && b₂`, `b₁ \|\| b₂`   |
| `p → q`        | `b₁.smtImp b₂`                           |
| `p ↔ q`, `p = q` | `smtEq b₁ b₂`                          |
| `b = true`     | `b`                                      |
| `x = y`, `x < y`, … | `smtEq x y`, `smtLt x y`, …         |
| `∀ x, p x`     | `smtForall fun x => b x`                 |
| `∃ x, p x`     | `smtExists fun x => b x`                 |
| `if p then x else y` | `cond b x y`                       |
| `decide p`     | `b`                                      |
| other atom `p` | `smtDecide p`                            |

Quantified propositional variables `∀ x : Prop, p x` become Boolean ones `∀ x : Bool, p (x = true)`.
These are the Boolean formulas that proof reconstruction builds from SMT-LIB terms, so that the
formulas it reconstructs from cvc5's proofs are syntactically equal to the hypotheses.
-/

public section

namespace Smt.Preprocess.Boolify

universe u

variable {p q : Prop} {α : Sort u} {β : Type u}

@[smt_boolify ↓] theorem smtDecide_True : smtDecide True = true := by simp [smtDecide]
@[smt_boolify ↓] theorem smtDecide_False : smtDecide False = false := by simp [smtDecide]

@[smt_boolify ↓] theorem smtDecide_not : smtDecide (¬p) = !smtDecide p := by
  apply Bool.eq_iff_iff.mpr; simp
@[smt_boolify ↓] theorem smtDecide_and : smtDecide (p ∧ q) = (smtDecide p && smtDecide q) := by
  apply Bool.eq_iff_iff.mpr; simp
@[smt_boolify ↓] theorem smtDecide_or : smtDecide (p ∨ q) = (smtDecide p || smtDecide q) := by
  apply Bool.eq_iff_iff.mpr; simp
@[smt_boolify ↓] theorem smtDecide_imp : smtDecide (p → q) = (smtDecide p).smtImp (smtDecide q) := by
  apply Bool.eq_iff_iff.mpr; simp
theorem smtDecide_eq_smtDecide : (smtDecide p = smtDecide q) ↔ (p ↔ q) := by
  rw [Bool.eq_iff_iff, smtDecide_eq_true, smtDecide_eq_true]

@[smt_boolify ↓] theorem smtDecide_iff : smtDecide (p ↔ q) = smtEq (smtDecide p) (smtDecide q) := by
  apply Bool.eq_iff_iff.mpr; rw [smtDecide_eq_true, smtEq_eq_true, smtDecide_eq_smtDecide]
@[smt_boolify ↓ high] theorem smtDecide_prop_eq :
    smtDecide (p = q) = smtEq (smtDecide p) (smtDecide q) := by
  apply Bool.eq_iff_iff.mpr; rw [smtDecide_eq_true, smtEq_eq_true, smtDecide_eq_smtDecide]
  exact ⟨fun h => h ▸ Iff.rfl, propext⟩

@[smt_boolify ↓ high] theorem smtDecide_bool_eq_true {b : Bool} : smtDecide (b = true) = b := by
  cases b <;> simp
@[smt_boolify ↓ high] theorem smtDecide_bool_eq_false {b : Bool} : smtDecide (b = false) = !b := by
  cases b <;> simp
@[smt_boolify ↓ high] theorem smtDecide_true_eq_bool {b : Bool} : smtDecide (true = b) = b := by
  cases b <;> simp
@[smt_boolify ↓ high] theorem smtDecide_false_eq_bool {b : Bool} : smtDecide (false = b) = !b := by
  cases b <;> simp

@[smt_boolify ↓] theorem smtDecide_eq {a b : α} : smtDecide (a = b) = smtEq a b := rfl
@[smt_boolify ↓] theorem smtDecide_ne {a b : α} : smtDecide (a ≠ b) = !smtEq a b := by
  apply Bool.eq_iff_iff.mpr; simp
@[smt_boolify ↓] theorem smtDecide_lt [LT β] {x y : β} : smtDecide (x < y) = smtLt x y := rfl
@[smt_boolify ↓] theorem smtDecide_le [LE β] {x y : β} : smtDecide (x ≤ y) = smtLe x y := rfl
@[smt_boolify ↓] theorem smtDecide_gt [LT β] {x y : β} : smtDecide (x > y) = smtGt x y := rfl
@[smt_boolify ↓] theorem smtDecide_ge [LE β] {x y : β} : smtDecide (x ≥ y) = smtGe x y := rfl

@[smt_boolify ↓] theorem smtDecide_ite {c : Prop} {h : Decidable c} :
    smtDecide (@ite Prop c h p q) = cond (smtDecide c) (smtDecide p) (smtDecide q) := by
  by_cases hc : c
  · simp [hc]
  · simp [hc]

attribute [smt_boolify ↓] decide_eq_smtDecide

@[smt_boolify ↓] theorem beq_eq_smtEq [BEq β] [LawfulBEq β] {x y : β} : (x == y) = smtEq x y := by
  apply Bool.eq_iff_iff.mpr; simp
@[smt_boolify ↓] theorem bne_eq_not_smtEq [BEq β] [LawfulBEq β] {x y : β} :
    (x != y) = !smtEq x y := by
  apply Bool.eq_iff_iff.mpr; simp

theorem smtDecide_forall {P : α → Prop} : smtDecide (∀ x, P x) = smtForall fun x => smtDecide (P x) := by
  simp only [smtForall, smtDecide_eq_true]

theorem smtDecide_exists {P : α → Prop} : smtDecide (∃ x, P x) = smtExists fun x => smtDecide (P x) := by
  simp only [smtExists, smtDecide_eq_true]

theorem forall_prop_iff {P : Prop → Prop} : (∀ x, P x) ↔ ∀ x : Bool, P (x = true) :=
  ⟨fun h x => h _, fun h x => by
    have := h (smtDecide x)
    rwa [smtDecide_eq_true] at this⟩

theorem exists_prop_iff {P : Prop → Prop} : (∃ x, P x) ↔ ∃ x : Bool, P (x = true) :=
  ⟨fun ⟨x, hx⟩ => ⟨smtDecide x, by rwa [smtDecide_eq_true]⟩, fun ⟨x, hx⟩ => ⟨_, hx⟩⟩

theorem smtDecide_forall_prop {P : Prop → Prop} :
    smtDecide (∀ x, P x) = smtDecide (∀ x : Bool, P (x = true)) := by
  rw [propext forall_prop_iff]

theorem smtDecide_exists_prop {P : Prop → Prop} :
    smtDecide (∃ x, P x) = smtDecide (∃ x : Bool, P (x = true)) := by
  rw [propext exists_prop_iff]

theorem ite_eq_cond {c : Prop} {h : Decidable c} {x y : α} :
    @ite α c h x y = cond (smtDecide c) x y := by
  by_cases hc : c
  · simp [hc]
  · simp [hc]

end Smt.Preprocess.Boolify

public meta section

namespace Smt.Preprocess.Boolify

open Lean Meta Simp Qq

/-- Turn `smtDecide (∀ x, p x)` into `smtForall fun x => smtDecide (p x)`. Propositional variables
`x : Prop` become Boolean ones, and quantifiers over proofs are atoms. -/
simproc ↓ [smt_boolify] boolifyForall (smtDecide _) := fun e => do
  let_expr smtDecide p := e | return .continue
  let .forallE n t body bi := p | return .continue
  -- `p → q` is an implication, see `smtDecide_imp`.
  if !body.hasLooseBVars && (← isProp t) then return .continue
  let lp := Expr.lam n t body bi
  if t.isProp then
    let lp : Q(Prop → Prop) ← pure lp
    return .visit { expr := q(smtDecide (∀ x : Bool, $lp (x = true))),
                    proof? := q(smtDecide_forall_prop (P := $lp)) }
  if ← isProp t then return .continue
  let u ← getLevel t
  let lb := Expr.lam n t (mkApp (.const ``smtDecide []) body) bi
  return .visit { expr := mkApp2 (.const ``smtForall [u]) t lb,
                  proof? := mkApp2 (.const ``smtDecide_forall [u]) t lp }

/-- Turn `smtDecide (∃ x, p x)` into `smtExists fun x => smtDecide (p x)`. Propositional variables
`x : Prop` become Boolean ones, and quantifiers over proofs are atoms. -/
simproc ↓ [smt_boolify] boolifyExists (smtDecide (Exists _)) := fun e => do
  let_expr smtDecide p := e | return .continue
  let_expr Exists t lp := p | return .continue
  let .lam n _ body bi := lp | return .continue
  if t.isProp then
    let lp : Q(Prop → Prop) ← pure lp
    return .visit { expr := q(smtDecide (∃ x : Bool, $lp (x = true))),
                    proof? := q(smtDecide_exists_prop (P := $lp)) }
  if ← isProp t then return .continue
  let u ← getLevel t
  let lb := Expr.lam n t (mkApp (.const ``smtDecide []) body) bi
  return .visit { expr := mkApp2 (.const ``smtExists [u]) t lb,
                  proof? := mkApp2 (.const ``smtDecide_exists [u]) t lp }

/-- Replace `if c then x else y` by `cond (smtDecide c) x y` for non-propositional `x` and `y`. -/
simproc ↓ [smt_boolify] iteToCond (ite _ _ _) := fun e => do
  let_expr ite α c h x y := e | return .continue
  if α.isProp then return .continue
  let u ← getLevel α
  return .visit { expr := mkApp4 (.const ``cond [u]) α (mkApp (.const ``smtDecide []) c) x y,
                  proof? := mkAppN (.const ``ite_eq_cond [u]) #[α, c, h, x, y] }

end Smt.Preprocess.Boolify

namespace Smt.Preprocess

open Lean Meta Qq

/-- Turn every hypothesis `h : p` in `hs` into a hypothesis `h' : b = true`, where `b` is the Boolean
formula obtained from `p` (see `Smt.Preprocess.Boolify`). Hypotheses in `hs` that are not proofs
(e.g., definitions) are kept as they are. -/
def boolify (mv : MVarId) (hs : Array Expr) : MetaM Result := do
  let some thmsExt ← getSimpExtension? `smt_boolify | throwError "smt_boolify simp extension not found"
  let some procsExt ← Simp.getSimprocExtension? `smt_boolify
    | throwError "smt_boolify simproc extension not found"
  let simprocs := #[← procsExt.getSimprocs]
  let ctx ← mv.withContext do
    Simp.mkContext { zeta := false, beta := true, eta := true, proj := false, iota := false }
      (simpTheorems := #[← thmsExt.getTheorems]) (congrTheorems := ← getSimpCongrTheorems)
  let mut mv := mv
  let mut map : Std.HashMap Expr (Array Expr) := {}
  let mut hs' := #[]
  for h in hs do
    let (h', mv') ← mv.withContext do
      let p ← instantiateMVars (← inferType h)
      unless ← isProp p do return (h, mv)
      let p : Q(Prop) ← pure p
      let h : Q($p) ← pure h
      let hb : Q(smtDecide $p = true) := q(Eq.mpr smtDecide_eq_true $h)
      let (r, _) ← Meta.simp q(smtDecide $p = true) ctx simprocs
      let hb ← match r.proof? with
        | none => pure hb
        | some e => mkEqMP e hb
      let mv ← mv.assert (← mkFreshUserName `h) r.expr hb
      let (fv, mv) ← mv.intro1P
      return (.fvar fv, mv)
    mv := mv'
    hs' := hs'.push h'
    map := map.insert h' #[h]
  return { map, hs := hs', mv }

end Smt.Preprocess
