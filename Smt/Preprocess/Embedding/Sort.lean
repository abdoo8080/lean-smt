/-
Copyright (c) 2021-2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

module

public import Lean.Meta.KAbstract
public meta import Lean.Meta.KAbstract
public import Lean.Meta.Tactic.Simp
public meta import Lean.Meta.Tactic.Simp

/-!
# Lifting types in `Sort u` into `Type u`

SMT-LIB's sorts are reconstructed as types, and SMT-LIB's `=` as `==` on them (see
`Smt.Reconstruct.Bool.mkBEq`), which needs `Type u`. A type variable `U : Sort u` whose universe may
be zero, e.g., an auto-bound implicit `U : Sort u_1`, is lifted into `Type u` along the bijection
`PLift.up : U → PLift U` (see `liftSorts`):

1. The variables of `U`, and of function types built from `U`, become variables of `PLift U` and of
   the corresponding function types, e.g., `f : U → U → U` becomes `f' : PLift U → PLift U → PLift U`,
   standing for `fun x y => (f' ⟨x⟩ ⟨y⟩).down`.
2. The terms are simplified until `U` only occurs in `PLift U`: `⟨x.down⟩ = x`,
   `(x.down = y.down) = (x = y)`, and so on.
3. `PLift U` is replaced by a fresh type variable `U : Type u`, which proves the goal for `U` by
   instantiating it with `PLift U`.
-/

@[expose] public section

namespace Smt.Preprocess.Embedding

universe u v

theorem forall_eq_of_section {α : Sort u} {β : Sort v} (f : β → α) (g : α → β)
    (h : ∀ x, f (g x) = x) {p : α → Prop} : (∀ x, p x) = (∀ y, p (f y)) :=
  propext ⟨fun hp y => hp (f y), fun hp x => h x ▸ hp (g x)⟩

theorem exists_eq_of_section {α : Sort u} {β : Sort v} (f : β → α) (g : α → β)
    (h : ∀ x, f (g x) = x) {p : α → Prop} : (∃ x, p x) = (∃ y, p (f y)) :=
  propext ⟨fun ⟨x, hx⟩ => ⟨g x, (h x).symm ▸ hx⟩, fun ⟨y, hy⟩ => ⟨f y, hy⟩⟩

theorem nonempty_eq_nonempty_plift {α : Sort u} : Nonempty α = Nonempty (PLift α) :=
  propext ⟨fun ⟨x⟩ => ⟨⟨x⟩⟩, fun ⟨x⟩ => ⟨x.down⟩⟩

theorem plift_down_eq {α : Sort u} {a b : PLift α} : (a.down = b.down) = (a = b) :=
  propext ⟨fun h => by cases a; cases b; cases h; rfl, fun h => h ▸ rfl⟩

theorem plift_down_ite {α : Sort u} {c : Prop} [Decidable c] {a b : PLift α} :
    (if c then a.down else b.down) = (if c then a else b).down := by
  split <;> rfl

theorem plift_down_cond {α : Sort u} {c : Bool} {a b : PLift α} :
    cond c a.down b.down = (cond c a b).down := by
  cases c <;> rfl

end Smt.Preprocess.Embedding

public meta section

namespace Smt.Preprocess.Embedding

open Lean Meta

/-- Whether `T` is `Sort u` for a universe `u` that is not zero and may not be a successor, e.g.,
`Sort u_1`: the type of a type variable that is lifted into `Type u` (see `liftSorts`). -/
def isLiftableSort (T : Expr) : Bool :=
  match T with
  | .sort u => !u.isZero && u.dec.isNone
  | _ => false

/-- `T` with the type variable `U` replaced by `PLift U`, if `U` only occurs in `T` as the domain or
codomain of (non-dependent) function types. -/
partial def liftType? (U : Expr) (u : Level) (T : Expr) : MetaM (Option Expr) := do
  if !T.containsFVar U.fvarId! then return some T
  if T == U then return some (mkApp (.const ``PLift [u]) U)
  if let .forallE n A B bi := T then
    if B.hasLooseBVars then return none
    let some A' ← liftType? U u A | return none
    let some B' ← liftType? U u B | return none
    return some (.forallE n A' B' bi)
  return none

mutual

/-- The element of `T` that `y : liftType? U u T` stands for. -/
partial def downOf (U : Expr) (u : Level) (T y : Expr) : MetaM Expr := do
  if !T.containsFVar U.fvarId! then return y
  if T == U then return mkApp2 (.const ``PLift.down [u]) U y
  let .forallE n A B bi := T | throwError "[lift_sorts]: unexpected type{indentExpr T}"
  withLocalDecl n bi A fun a => do
    mkLambdaFVars #[a] (← downOf U u B (.app y (← upOf U u A a)))

/-- The element of `liftType? U u T` that stands for `x : T`. -/
partial def upOf (U : Expr) (u : Level) (T x : Expr) : MetaM Expr := do
  if !T.containsFVar U.fvarId! then return x
  if T == U then return mkApp2 (.const ``PLift.up [u]) U x
  let .forallE n A B bi := T | throwError "[lift_sorts]: unexpected type{indentExpr T}"
  let some A' ← liftType? U u A | throwError "[lift_sorts]: unexpected type{indentExpr A}"
  withLocalDecl n bi A' fun a => do
    mkLambdaFVars #[a] (← upOf U u B (.app x (← downOf U u A a)))

end

/-- Turn a quantifier over a type `T` built from `U` into a quantifier over `liftType? U u T`, and
`Nonempty U` into `Nonempty (PLift U)`. -/
def liftBinder (U : Expr) (u : Level) : Simp.Simproc := fun e => do
  if let .forallE n T b bi := e then
    if !T.containsFVar U.fvarId! || (← isProp T) || !(← isProp e) then return .continue
    let some T' ← liftType? U u T | return .continue
    let f ← withLocalDecl n bi T' fun y => do mkLambdaFVars #[y] (← downOf U u T y)
    let g ← withLocalDecl n bi T fun x => do mkLambdaFVars #[x] (← upOf U u T x)
    -- `f (g x)` reduces to `x`.
    let h ← withLocalDecl n bi T fun x => do mkLambdaFVars #[x] (← mkEqRefl x)
    let e' ← withLocalDecl n bi T' fun y => do
      mkForallFVars #[y] (b.instantiate1 (← downOf U u T y)).headBeta
    let p := Expr.lam n T b bi
    let pf ← mkAppOptM ``forall_eq_of_section #[T, T', f, g, h, p]
    return .visit { expr := e', proof? := pf }
  if e.isAppOfArity ``Exists 2 then
    let T := e.getArg! 0
    let p := e.getArg! 1
    if !T.containsFVar U.fvarId! then return .continue
    let some T' ← liftType? U u T | return .continue
    let n := if let .lam n .. := p then n else `x
    let f ← withLocalDeclD n T' fun y => do mkLambdaFVars #[y] (← downOf U u T y)
    let g ← withLocalDeclD n T fun x => do mkLambdaFVars #[x] (← upOf U u T x)
    let h ← withLocalDeclD n T fun x => do mkLambdaFVars #[x] (← mkEqRefl x)
    let p' ← withLocalDeclD n T' fun y => do mkLambdaFVars #[y] (p.beta #[← downOf U u T y])
    let pf ← mkAppOptM ``exists_eq_of_section #[T, T', f, g, h, p]
    return .visit { expr := ← mkAppM ``Exists #[p'], proof? := pf }
  if e.isAppOfArity ``Nonempty 1 && e.appArg! == U then
    return .done { expr := ← mkAppM ``Nonempty #[mkApp (.const ``PLift [u]) U],
                   proof? := mkApp (.const ``nonempty_eq_nonempty_plift [u]) U }
  return .continue

/-- Transport the proposition `p` along `PLift.up : U → PLift U`: the proposition `p'` with `U` only
in `PLift U`, abstracted, and a proof of `p = p'[PLift U]`. Returns `none` if `U` also occurs
elsewhere in `p'`. -/
def liftTypeVar? (U : Expr) (u : Level) (p : Expr) : MetaM (Option (Expr × Expr)) := do
  let thms ← [``PLift.up_down, ``plift_down_eq, ``plift_down_ite, ``plift_down_cond, ``ne_eq].foldlM
    (·.addConst ·) ({} : SimpTheorems)
  let ctx ← Simp.mkContext {} #[thms] (← getSimpCongrTheorems)
  let m := Simp.mkDefaultMethodsCore #[]
  let pre : Simp.Simproc := fun e => do
    match ← liftBinder U u e with
    | .continue _ => m.pre e
    | s => return s
  -- Leave `U` as it is if the transport fails.
  let some (r, _) ← try some <$> Simp.main p ctx (methods := { m with pre }) catch _ => pure none
    | return none
  let p' ← kabstract r.expr (mkApp (.const ``PLift [u]) U)
  if p'.containsFVar U.fvarId! then return none
  return some (p', ← r.getProof)

/-- Lift the type variables in `Sort u` among the binders of the proposition `G = ∀ xs, B` into
`Type u` (see `isLiftableSort`): the proposition `G'` with the same binders, and a proof of
`G' → G`. Returns `none` if there is nothing to lift. -/
partial def liftSortsIn? (G : Expr) : MetaM (Option (Expr × Expr)) := do
  let .forallE n T b bi := G | return none
  withLocalDecl n bi T fun x => do
    let body := b.instantiate1 x
    if let .sort u := T then
      if isLiftableSort T && body.containsFVar x.fvarId! then
        if let some (P, h) ← liftTypeVar? x u body then
          let tV := Expr.sort (.succ u)
          -- `fun V => P'`, where `P'` lifts the remaining type variables of `P[V]`, and
          -- `fun V => (_ : P' → P[V])`.
          let (lP', lh?) ← withLocalDecl n bi tV fun V => do
            let PV := P.instantiate1 V
            match ← liftSortsIn? PV with
            | some (PV', hPV) => return (← mkLambdaFVars #[V] PV', some (← mkLambdaFVars #[V] hPV))
            | none => return (← mkLambdaFVars #[V] PV, none)
          let G' := Expr.forallE n tV lP'.bindingBody! bi
          let pU := mkApp (.const ``PLift [u]) x
          let pf ← withLocalDeclD `g G' fun g => do
            let gx := mkApp g pU
            let q := match lh? with
              | some lh => mkApp (lh.beta #[pU]) gx
              | none => gx
            mkLambdaFVars #[g, x] (← mkEqMPR h q)
          return some (G', pf)
    let some (body', hb) ← liftSortsIn? body | return none
    let G' ← mkForallFVars #[x] body'
    let pf ← withLocalDeclD `g G' fun g => do mkLambdaFVars #[g, x] (mkApp hb (mkApp g x))
    return some (G', pf)

/-- Whether a binder of `G = ∀ xs, B` is a type variable in `Sort u` (see `isLiftableSort`). -/
def hasLiftableBinder : Expr → Bool
  | .forallE _ T b _ => isLiftableSort T || hasLiftableBinder b
  | _ => false

/-- Lift the type variables in `Sort u` of the goal `mv = ∀ xs, B`, which has its free variables
reverted, into `Type u`. The new goal has the same binders. -/
def liftSorts (mv : MVarId) : MetaM MVarId := mv.withContext do
  let G ← instantiateMVars (← mv.getType)
  -- Leave the goal, and the names of fresh free variables, untouched if there is nothing to lift.
  if !hasLiftableBinder G then return mv
  let some (G', pf) ← liftSortsIn? G | return mv
  let mv' ← mkFreshExprMVar G' (userName := ← mv.getTag)
  mv.assign (mkApp pf mv')
  return mv'.mvarId!

end Smt.Preprocess.Embedding
