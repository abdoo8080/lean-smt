/-
Copyright (c) 2021-2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

module

public import Lean.Meta.Tactic.Simp
public meta import Lean.Meta.Tactic.Simp
public import Smt.Preprocess.Basic
public meta import Smt.Preprocess.Basic
public import Smt.Preprocess.Boolify.Attribute
public meta import Smt.Preprocess.Boolify.Attribute
public import Smt.Reconstruct.Bool.Bridge
public meta import Smt.Reconstruct.Bool.Bridge

/-!
# From propositions to Booleans

SMT-LIB's `Bool` sort is Lean's `Bool`: translation and proof reconstruction work with Boolean
formulas, and a proof of a formula `b` is a proof of `b = true`. This preprocessing step turns every
hypothesis `h : p` into `h' : b = true`, where the Boolean formula `b` is obtained by pushing
`decide p` into the connectives and quantifiers of `p`:

| proposition    | Boolean formula                          |
|----------------|------------------------------------------|
| `¬p`, `p ∧ q`, `p ∨ q` | `!b`, `b₁ && b₂`, `b₁ \|\| b₂`   |
| `p → q`        | `b₁.smtImp b₂`                           |
| `p ↔ q`, `p = q` | `decide (b₁ = b₂)`                     |
| `b = true`     | `b`                                      |
| `∀ x, p x`     | `decide (∀ x, b x = true)`               |
| `∃ x, p x`     | `decide (∃ x, b x = true)`               |
| `if p then x else y` | `cond b x y`                       |
| atom `p`       | `decide p`                               |

Quantified propositional variables `∀ x : Prop, p x` become Boolean ones `∀ x : Bool, p (x = true)`.
Every `decide p` that remains is an atom, whose `Decidable p` instance is the one chosen by
`Smt.mkDecide`. Proof reconstruction builds atoms with the same instances, so that the formulas it
reconstructs from cvc5's proofs are syntactically equal to the hypotheses.
-/

public section

namespace Smt.Preprocess.Boolify

theorem decide_True_eq {h : Decidable True} : @decide True h = true := decide_true h

theorem decide_False_eq {h : Decidable False} : @decide False h = false := decide_false h

theorem decide_not_eq {p : Prop} {h : Decidable (¬p)} {hp : Decidable p} :
    @decide (¬p) h = !@decide p hp := by
  by_cases p <;> simp [*]

theorem decide_and_eq {p q : Prop} {h : Decidable (p ∧ q)} {hp : Decidable p} {hq : Decidable q} :
    @decide (p ∧ q) h = (@decide p hp && @decide q hq) := by
  by_cases p <;> by_cases q <;> simp [*]

theorem decide_or_eq {p q : Prop} {h : Decidable (p ∨ q)} {hp : Decidable p} {hq : Decidable q} :
    @decide (p ∨ q) h = (@decide p hp || @decide q hq) := by
  by_cases p <;> by_cases q <;> simp [*]

theorem decide_imp_eq {p q : Prop} {h : Decidable (p → q)} {hp : Decidable p} {hq : Decidable q} :
    @decide (p → q) h = (@decide p hp).smtImp (@decide q hq) := by
  by_cases p <;> by_cases q <;> simp [*, Bool.smtImp]

theorem decide_iff_eq {p q : Prop} {h : Decidable (p ↔ q)} {hp : Decidable p} {hq : Decidable q}
    {h' : Decidable (@decide p hp = @decide q hq)} :
    @decide (p ↔ q) h = @decide (@decide p hp = @decide q hq) h' := by
  by_cases p <;> by_cases q <;> simp [*]

theorem decide_prop_eq_eq {p q : Prop} {h : Decidable (p = q)} {hp : Decidable p}
    {hq : Decidable q} {h' : Decidable (@decide p hp = @decide q hq)} :
    @decide (p = q) h = @decide (@decide p hp = @decide q hq) h' := by
  by_cases p <;> by_cases q <;> simp [*]

theorem decide_ne_eq {α} {a b : α} {h : Decidable (a ≠ b)} {h' : Decidable (a = b)} :
    @decide (a ≠ b) h = !@decide (a = b) h' := by
  by_cases a = b <;> simp [*]

theorem decide_bool_eq_true {b : Bool} {h : Decidable (b = true)} : @decide (b = true) h = b := by
  cases b <;> simp

theorem decide_bool_eq_false {b : Bool} {h : Decidable (b = false)} : @decide (b = false) h = !b := by
  cases b <;> simp

theorem decide_true_eq_bool {b : Bool} {h : Decidable (true = b)} : @decide (true = b) h = b := by
  cases b <;> simp

theorem decide_false_eq_bool {b : Bool} {h : Decidable (false = b)} : @decide (false = b) h = !b := by
  cases b <;> simp

theorem decide_forall_congr {α} {p : α → Prop} {b : α → Bool} (hp : ∀ x, p x = (b x = true))
    {h : Decidable (∀ x, p x)} {h' : Decidable (∀ x, b x = true)} :
    @decide (∀ x, p x) h = @decide (∀ x, b x = true) h' := by
  congr 1; exact forall_congr hp

theorem decide_exists_congr {α} {p : α → Prop} {b : α → Bool} (hp : ∀ x, p x = (b x = true))
    {h : Decidable (∃ x, p x)} {h' : Decidable (∃ x, b x = true)} :
    @decide (∃ x, p x) h = @decide (∃ x, b x = true) h' := by
  congr 1; exact propext (exists_congr (hp · ▸ Iff.rfl))

theorem eq_true_of_decide_eq {p : Prop} {h : Decidable p} {b : Bool} (hb : @decide p h = b) :
    p = (b = true) := by
  subst hb; simp

theorem forall_prop_iff {p : Prop → Prop} : (∀ x, p x) ↔ ∀ x : Bool, p (x = true) :=
  ⟨fun h x => h _, fun h x => by
    have := h (@decide x (Classical.propDecidable x))
    rwa [@_root_.decide_eq_true_eq x (Classical.propDecidable x)] at this⟩

theorem exists_prop_iff {p : Prop → Prop} : (∃ x, p x) ↔ ∃ x : Bool, p (x = true) :=
  ⟨fun ⟨x, hx⟩ => ⟨@decide x (Classical.propDecidable x),
     by rwa [@_root_.decide_eq_true_eq x (Classical.propDecidable x)]⟩,
   fun ⟨x, hx⟩ => ⟨_, hx⟩⟩

theorem decide_forall_prop_eq {p : Prop → Prop} {h : Decidable (∀ x, p x)}
    {h' : Decidable (∀ x : Bool, p (x = true))} :
    @decide (∀ x, p x) h = @decide (∀ x : Bool, p (x = true)) h' := by
  congr 1; exact propext forall_prop_iff

theorem decide_exists_prop_eq {p : Prop → Prop} {h : Decidable (∃ x, p x)}
    {h' : Decidable (∃ x : Bool, p (x = true))} :
    @decide (∃ x, p x) h = @decide (∃ x : Bool, p (x = true)) h' := by
  congr 1; exact propext exists_prop_iff

theorem decide_ite_eq {c p q : Prop} {hc : Decidable c} {h : Decidable (@ite Prop c hc p q)}
    {hc' : Decidable c} {hp : Decidable p} {hq : Decidable q} :
    @decide (@ite Prop c hc p q) h = cond (@decide c hc') (@decide p hp) (@decide q hq) := by
  by_cases c <;> simp [*]

theorem decide_congr_inst {p : Prop} {h₁ h₂ : Decidable p} : @decide p h₁ = @decide p h₂ := by
  congr

theorem ite_eq_cond {α} {c : Prop} {h h' : Decidable c} {x y : α} :
    @ite α c h x y = cond (@decide c h') x y := by
  by_cases c <;> simp [*]

theorem beq_eq_decide {α} {inst : BEq α} [LawfulBEq α] {a b : α} {h : Decidable (a = b)} :
    (a == b) = @decide (a = b) h := by
  by_cases a = b <;> simp [*]

theorem bne_eq_not_decide {α} {inst : BEq α} [LawfulBEq α] {a b : α} {h : Decidable (a = b)} :
    (a != b) = !@decide (a = b) h := by
  by_cases a = b <;> simp [*]

end Smt.Preprocess.Boolify

public meta section

namespace Smt.Preprocess.Boolify

open Lean Meta Simp Qq

/-- For the predicate `lp = fun x => p x` of a quantifier, return the predicate `fun x => b x`, where
`b x` is the Boolean normal form of `decide (p x)`, and a proof of `∀ x, p x = (b x = true)`. Simp
does not visit the propositions inside `decide`, so quantifier bodies are normalized here. -/
private def boolifyQuantBody (n : Name) (α : Expr) (lp : Expr) : SimpM (Expr × Expr) :=
  withLocalDeclD n α fun x => do
    let px : Q(Prop) ← pure (lp.beta #[x])
    let hpx : Q(Decidable $px) ← mkDecidableInst px
    let r ← Simp.simp q(@decide $px $hpx)
    let b : Q(Bool) ← pure r.expr
    let hb : Q(@decide $px $hpx = $b) ← r.getProof
    return (← mkLambdaFVars #[x] b, ← mkLambdaFVars #[x] q(@eq_true_of_decide_eq $px $hpx $b $hb))

/-- The propositions `a` and `b` with the instances of their atoms `decide a` and `decide b`. -/
private def binary (a b : Expr) :
    MetaM ((a : Q(Prop)) × (b : Q(Prop)) × Q(Decidable $a) × Q(Decidable $b)) := do
  let a : Q(Prop) ← pure a
  let b : Q(Prop) ← pure b
  return ⟨a, b, ← mkDecidableInst a, ← mkDecidableInst b⟩

/-- Push `decide` into the connectives and quantifiers of a proposition. -/
simproc ↓ [smt_boolify] boolifyDecide (Decidable.decide _) := fun e => do
  let_expr Decidable.decide p h := e | return .continue
  if p.isConstOf ``True then
    return .visit { expr := q(true), proof? := mkApp (.const ``decide_True_eq []) h }
  if p.isConstOf ``False then
    return .visit { expr := q(false), proof? := mkApp (.const ``decide_False_eq []) h }
  if let some a := p.not? then
    let a : Q(Prop) ← pure a
    let h : Q(Decidable (¬$a)) ← pure h
    let ha : Q(Decidable $a) ← mkDecidableInst a
    return .visit { expr := q(!@decide $a $ha), proof? := q(@decide_not_eq $a $h $ha) }
  if let some (a, b) := p.and? then
    let ⟨a, b, ha, hb⟩ ← binary a b
    let h : Q(Decidable ($a ∧ $b)) ← pure h
    return .visit { expr := q(@decide $a $ha && @decide $b $hb), proof? := q(@decide_and_eq $a $b $h $ha $hb) }
  if let some (a, b) := p.app2? ``Or then
    let ⟨a, b, ha, hb⟩ ← binary a b
    let h : Q(Decidable ($a ∨ $b)) ← pure h
    return .visit { expr := q(@decide $a $ha || @decide $b $hb), proof? := q(@decide_or_eq $a $b $h $ha $hb) }
  if let some (a, b) := p.iff? then
    let ⟨a, b, ha, hb⟩ ← binary a b
    let h : Q(Decidable ($a ↔ $b)) ← pure h
    let h' : Q(Decidable (@decide $a $ha = @decide $b $hb)) ← mkDecidableInst q(@decide $a $ha = @decide $b $hb)
    return .visit { expr := q(@decide (@decide $a $ha = @decide $b $hb) $h'),
                    proof? := q(@decide_iff_eq $a $b $h $ha $hb $h') }
  if let some (α, a, b) := p.eq? then
    if α.isConstOf ``Bool then
      let a : Q(Bool) ← pure a
      let b : Q(Bool) ← pure b
      if b.isConstOf ``Bool.true then
        let h : Q(Decidable ($a = true)) ← pure h
        return .visit { expr := a, proof? := q(@decide_bool_eq_true $a $h) }
      if b.isConstOf ``Bool.false then
        let h : Q(Decidable ($a = false)) ← pure h
        return .visit { expr := q(!$a), proof? := q(@decide_bool_eq_false $a $h) }
      if a.isConstOf ``Bool.true then
        let h : Q(Decidable (true = $b)) ← pure h
        return .visit { expr := b, proof? := q(@decide_true_eq_bool $b $h) }
      if a.isConstOf ``Bool.false then
        let h : Q(Decidable (false = $b)) ← pure h
        return .visit { expr := q(!$b), proof? := q(@decide_false_eq_bool $b $h) }
    if α.isProp then
      let ⟨a, b, ha, hb⟩ ← binary a b
      let h : Q(Decidable ($a = $b)) ← pure h
      let h' : Q(Decidable (@decide $a $ha = @decide $b $hb)) ← mkDecidableInst q(@decide $a $ha = @decide $b $hb)
      return .visit { expr := q(@decide (@decide $a $ha = @decide $b $hb) $h'),
                      proof? := q(@decide_prop_eq_eq $a $b $h $ha $hb $h') }
    return .continue
  if let some (α, a, b) := p.ne? then
    let u ← getLevel α
    let α : Q(Sort u) ← pure α
    let a : Q($α) ← pure a
    let b : Q($α) ← pure b
    let h : Q(Decidable ($a ≠ $b)) ← pure h
    let h' : Q(Decidable ($a = $b)) ← mkDecidableInst q($a = $b)
    return .visit { expr := q(!@decide ($a = $b) $h'), proof? := q(@decide_ne_eq $α $a $b $h $h') }
  if p.isAppOfArity ``ite 5 && (p.getArg! 0).isProp then
    let c : Q(Prop) ← pure (p.getArg! 1)
    let hc : Q(Decidable $c) ← pure (p.getArg! 2)
    let ⟨a, b, ha, hb⟩ ← binary (p.getArg! 3) (p.getArg! 4)
    let h : Q(Decidable (@ite Prop $c $hc $a $b)) ← pure h
    let hc' : Q(Decidable $c) ← mkDecidableInst c
    return .visit { expr := q(cond (@decide $c $hc') (@decide $a $ha) (@decide $b $hb)),
                    proof? := q(@decide_ite_eq $c $a $b $hc $h $hc' $ha $hb) }
  if let some (α, lp) := p.app2? ``Exists then
    let .lam n t body bi := lp | return .continue
    if t.isProp then
      let lp : Q(Prop → Prop) ← pure lp
      let h : Q(Decidable (∃ x, $lp x)) ← pure h
      let h' : Q(Decidable (∃ x : Bool, $lp (x = true))) ← mkDecidableInst q(∃ x : Bool, $lp (x = true))
      return .visit { expr := q(@decide (∃ x : Bool, $lp (x = true)) $h'),
                      proof? := q(@decide_exists_prop_eq $lp $h $h') }
    let u ← getLevel α
    let lp := Expr.lam n t body bi
    let (lb, hp) ← boolifyQuantBody n t lp
    let .lam _ _ lbBody _ := lb | return .continue
    let lq := Expr.lam n t (mkApp3 (.const ``Eq [1]) (.const ``Bool []) lbBody (.const ``Bool.true [])) bi
    let pq := mkApp2 (.const ``Exists [u]) α lq
    let h' ← mkDecidableInst pq
    let e' := mkApp2 (.const ``Decidable.decide []) pq h'
    if e' == e then return .continue
    return .done { expr := e', proof? := mkAppN (.const ``decide_exists_congr [u]) #[α, lp, lb, hp, h, h'] }
  match p with
  | .forallE n t body bi =>
    if !body.hasLooseBVars && (← isProp t) then
      let ⟨a, b, ha, hb⟩ ← binary t body
      let h : Q(Decidable ($a → $b)) ← pure h
      return .visit { expr := q((@decide $a $ha).smtImp (@decide $b $hb)),
                      proof? := q(@decide_imp_eq $a $b $h $ha $hb) }
    if t.isProp then
      let lp : Q(Prop → Prop) ← pure (.lam n t body bi)
      let h : Q(Decidable (∀ x, $lp x)) ← pure h
      let h' : Q(Decidable (∀ x : Bool, $lp (x = true))) ← mkDecidableInst q(∀ x : Bool, $lp (x = true))
      return .visit { expr := q(@decide (∀ x : Bool, $lp (x = true)) $h'),
                      proof? := q(@decide_forall_prop_eq $lp $h $h') }
    if !(← isProp (.forallE n t body bi)) then return .continue
    let u ← getLevel t
    let lp := Expr.lam n t body bi
    let (lb, hp) ← boolifyQuantBody n t lp
    let .lam _ _ lbBody _ := lb | return .continue
    let pq := Expr.forallE n t (mkApp3 (.const ``Eq [1]) (.const ``Bool []) lbBody (.const ``Bool.true [])) bi
    let h' ← mkDecidableInst pq
    let e' := mkApp2 (.const ``Decidable.decide []) pq h'
    if e' == e then return .continue
    return .done { expr := e', proof? := mkAppN (.const ``decide_forall_congr [u]) #[t, lp, lb, hp, h, h'] }
  | _ => return .continue

/-- Replace the `Decidable p` instance of the atom `decide p` by the one of `Smt.mkDecide p`. -/
simproc [smt_boolify] canonicalDecide (Decidable.decide _) := fun e => do
  let_expr Decidable.decide p h := e | return .continue
  let p : Q(Prop) ← pure p
  let h : Q(Decidable $p) ← pure h
  let h' : Q(Decidable $p) ← mkDecidableInst p
  if h == h' then return .continue
  return .done { expr := q(@decide $p $h'), proof? := q(@decide_congr_inst $p $h $h') }

/-- Replace `if c then x else y` by `cond (decide c) x y`. -/
simproc ↓ [smt_boolify] iteToCond (ite _ _ _) := fun e => do
  let_expr ite α c h x y := e | return .continue
  if α.isProp then return .continue
  let u ← getLevel α
  let α : Q(Sort u) ← pure α
  let c : Q(Prop) ← pure c
  let h : Q(Decidable $c) ← pure h
  let x : Q($α) ← pure x
  let y : Q($α) ← pure y
  let h' : Q(Decidable $c) ← mkDecidableInst c
  return .visit { expr := q(cond (@decide $c $h') $x $y), proof? := q(@ite_eq_cond $α $c $h $h' $x $y) }

/-- Replace `a == b` by `decide (a = b)` for lawful `BEq` instances. -/
simproc ↓ [smt_boolify] beqToDecide (_ == _) := fun e => do
  let_expr BEq.beq α inst a b := e | return .continue
  let u ← getLevel α
  let .succ v := u | return .continue
  let α : Q(Type v) ← pure α
  let inst : Q(BEq $α) ← pure inst
  let some _ ← synthInstance? q(@LawfulBEq $α $inst) | return .continue
  let a : Q($α) ← pure a
  let b : Q($α) ← pure b
  let h : Q(Decidable ($a = $b)) ← mkDecidableInst q($a = $b)
  let some hl ← synthInstance? q(@LawfulBEq $α $inst) | return .continue
  let hl : Q(@LawfulBEq $α $inst) ← pure hl
  return .visit { expr := q(@decide ($a = $b) $h), proof? := q(@beq_eq_decide $α $inst $hl $a $b $h) }

/-- Replace `a != b` by `!decide (a = b)` for lawful `BEq` instances. -/
simproc ↓ [smt_boolify] bneToDecide (_ != _) := fun e => do
  let_expr bne α inst a b := e | return .continue
  let u ← getLevel α
  let .succ v := u | return .continue
  let α : Q(Type v) ← pure α
  let inst : Q(BEq $α) ← pure inst
  let some hl ← synthInstance? q(@LawfulBEq $α $inst) | return .continue
  let hl : Q(@LawfulBEq $α $inst) ← pure hl
  let a : Q($α) ← pure a
  let b : Q($α) ← pure b
  let h : Q(Decidable ($a = $b)) ← mkDecidableInst q($a = $b)
  return .visit { expr := q(!@decide ($a = $b) $h), proof? := q(@bne_eq_not_decide $α $inst $hl $a $b $h) }

end Smt.Preprocess.Boolify

namespace Smt.Preprocess

open Lean Meta Qq

/-- Turn every hypothesis `h : p` in `hs` into a hypothesis `h' : b = true`, where `b` is the Boolean
formula obtained from `p` (see `Smt.Preprocess.Boolify`). Hypotheses in `hs` that are not proofs
(e.g., definitions) are kept as they are. -/
def boolify (mv : MVarId) (hs : Array Expr) : MetaM Result := do
  let some procsExt ← Simp.getSimprocExtension? `smt_boolify
    | throwError "smt_boolify simproc extension not found"
  let simprocs := #[← procsExt.getSimprocs]
  let ctx ← mv.withContext do
    Simp.mkContext { zeta := false, beta := true, eta := true, proj := false, iota := false }
      (simpTheorems := #[]) (congrTheorems := ← getSimpCongrTheorems)
  let mut mv := mv
  let mut map : Std.HashMap Expr (Array Expr) := {}
  let mut hs' := #[]
  for h in hs do
    let (h', mv') ← mv.withContext do
      let p ← instantiateMVars (← inferType h)
      unless ← isProp p do return (h, mv)
      let p : Q(Prop) ← pure p
      let inst : Q(Decidable $p) ← mkDecidableInst p
      let h : Q($p) ← pure h
      let hb : Q(@decide $p $inst = true) := q(@decide_eq_true $p $inst $h)
      let (r, _) ← Meta.simp q(@decide $p $inst = true) ctx simprocs
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
