/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

module

public import Smt.Reconstruct
public meta import Smt.Reconstruct
public import Smt.Reconstruct.Bool.Lemmas
public meta import Smt.Reconstruct.Bool.Lemmas
public import Smt.Reconstruct.Quant.Lemmas
public meta import Smt.Reconstruct.Quant.Lemmas

public meta section

/-- Takes an array `xs` of free variables or metavariables and a term `e` that may contain those variables, and abstracts and binds them as existential quantifiers.

- if `usedOnly = true` then only variables that the expression body depends on will appear.
- if `usedLetOnly = true` same as `usedOnly` except for let-bound variables. (That is, local constants which have been assigned a value.)
 -/
def Lean.Meta.mkExistsFVars (xs : Array Expr) (e : Expr) (usedOnly : Bool := false) (usedLetOnly : Bool := true) (generalizeNondepLet := true) (binderInfoForMVars := BinderInfo.implicit) : MetaM Expr := do
  let e ← if xs.isEmpty then return e else liftMkBindingM <| MetavarContext.mkLambda xs e usedOnly usedLetOnly (etaReduce := false) generalizeNondepLet binderInfoForMVars
  addExists e xs.size
where
  addExists : Expr → Nat → MetaM Expr
    | .lam n t b i, m + 1 => do
      let b ← addExists b m
      mkAppM ``Exists #[.lam n t b i]
    | e, _ => pure e

namespace Smt.Reconstruct.Quant

open Lean Qq

def getVariableName (t : cvc5.Term) : Name :=
  if t.hasSymbol! then
    if t.getSymbol!.toName == .anonymous then
      Name.mkSimple t.getSymbol!
    else
      t.getSymbol!.toName
  else Name.num `x t.getId!

/-- `Bool.forall fun x₁ => ⋯ Bool.forall fun xₙ => b` (or with `Bool.exists`) over the free variables `xs`
of the Boolean formula `b`. -/
def mkQuantFVars (op : Name) (xs : Array Expr) (b : Expr) : MetaM Expr :=
  xs.foldrM (init := b) fun x b => do
    let α ← Meta.inferType x
    return mkApp2 (.const op [← Meta.getLevel α]) α (← Meta.mkLambdaFVars #[x] b)

/-- `(forall ((x₁ T₁) … (xₙ Tₙ)) F)` is reconstructed as `Bool.forall fun x₁ => ⋯ Bool.forall fun xₙ =>
⟦F⟧`, and `exists` likewise. -/
@[smt_term_reconstruct] def reconstructQuant : TermReconstructor := fun t => do match t.getKind! with
  | .FORALL =>
    let mut xs : Array (Name × (Array Expr → ReconstructM Expr)) := #[]
    for x in t[0]! do
      xs := xs.push (getVariableName x, fun _ => reconstructSort x.getSort!)
    Meta.withLocalDeclsD xs fun xs => withNewTermCache do
      mkQuantFVars ``Bool.forall xs (← reconstructTerm t[1]!)
  | .EXISTS =>
    let mut xs : Array (Name × (Array Expr → ReconstructM Expr)) := #[]
    for x in t[0]! do
      xs := xs.push (getVariableName x, fun _ => reconstructSort x.getSort!)
    Meta.withLocalDeclsD xs fun xs => withNewTermCache do
      mkQuantFVars ``Bool.exists xs (← reconstructTerm t[1]!)
  | .LAMBDA =>
    let mut xs : Array (Name × (Array Expr → ReconstructM Expr)) := #[]
    for x in t[0]! do
      xs := xs.push (getVariableName x, fun _ => reconstructSort x.getSort!)
    Meta.withLocalDeclsD xs fun xs => withNewTermCache do
      let b ← reconstructTerm t[1]!
      Meta.mkLambdaFVars xs b
  | .HO_APPLY =>
    return (← reconstructTerm t[0]!).app (← reconstructTerm t[1]!)
  | .SKOLEM => match t.getSkolemId! with
    | .QUANTIFIERS_SKOLEMIZE =>
      let q := t.getSkolemIndices![0]!
      let n := t.getSkolemIndices![1]!.getIntegerValue!.toNat
      let es ← reconstructForallSkolems q n
      return es[n]!
    | _ => return none
  | _ => return none
where
  reconstructForallSkolems (q : cvc5.Term) (n : Nat) : ReconstructM (Array Expr) := do
    let mut xs : Array (Name × (Array Expr → ReconstructM Expr)) := #[]
    let mut es := #[]
    for x in q[0]! do
      xs := xs.push (getVariableName x, fun _ => reconstructSort x.getSort!)
    let F := q[1]!
    for i in [0:n + 1] do
      let (u, (α : Q(Sort u))) ← reconstructSortLevelAndSort q[0]![i]!.getSort!
      let h : Q(Nonempty $α) ← Meta.synthInstance q(Nonempty $α)
      let e ← Meta.withLocalDeclsD xs fun xs => withNewTermCache do
        let F : Q(Bool) ← reconstructTerm F
        let ysF : Q(Bool) ← mkQuantFVars ``Bool.forall xs[i + 1:] F
        let xysF ← Meta.mkLambdaFVars #[xs[i]!] q(¬$ysF = true)
        let xysF : Q($α → Prop) := xysF.replaceFVars xs[0:i] es
        return q(@Classical.epsilon $α $h $xysF)
      es := es.push e
    return es

def reconstructRewrite (pf : cvc5.Proof) : ReconstructM (Option Expr) := do
  match pf.getRewriteRule! with
  | .BETA_REDUCE =>
    let (u, (α : Q(Sort u))) ← reconstructSortLevelAndSort pf.getResult[0]!.getSort!
    let t  : Q($α) ← reconstructTerm pf.getResult[0]!
    addEqThm pf.getResult q(Eq.refl $t)
  | .EXISTS_ELIM =>
    -- `(exists xs F) = (not (forall xs (not F)))`, one variable at a time from the innermost.
    let mut xs := #[]
    for x in pf.getResult[0]![0]! do
      xs := xs.push (getVariableName x, fun _ => reconstructSort x.getSort!)
    let h ← Meta.withLocalDeclsD xs fun xs => withNewTermCache do
      let b : Q(Bool) ← reconstructTerm pf.getResult[0]![1]!
      -- `h : e = !a`, where `e` and `a` quantify `F` and `not F` over the variables seen so far.
      let f := fun x (e, a, h) => do
        let α ← Meta.inferType x
        let u ← Meta.getLevel α
        let le ← Meta.mkLambdaFVars #[x] e
        let la ← Meta.mkLambdaFVars #[x] a
        let hx ← Meta.mkLambdaFVars #[x] h
        return (mkApp2 (.const ``Bool.exists [u]) α le, mkApp2 (.const ``Bool.forall [u]) α la,
          mkAppN (.const ``Quant.exists_eq_not_forall [u]) #[α, le, la, hx])
      let (_, _, h) ← xs.foldrM f (b, q(!$b), q((Bool.not_not $b).symm))
      return h
    addEqThm pf.getResult h
  | .QUANT_UNUSED_VARS =>
    -- `(forall xs F) = (forall ys F)`, where `ys` are the variables of `xs` that occur in `F`.
    let mut ys := #[]
    if pf.getResult[1]!.getKind! == .FORALL then
      for y in pf.getResult[1]![0]! do
        ys := ys.push (getVariableName y, fun _ => reconstructSort y.getSort!)
    let h ← Meta.withLocalDeclsD ys fun ys => withNewTermCache do
      let b : Q(Bool) ← reconstructTerm pf.getResult[0]![1]!
      -- `h : p = q`, where `p` quantifies `F` over the variables of `xs` seen so far, and `q` over
      -- those of `ys`.
      let f := fun i (j, p, q, h) => do
        let (u, α) ← reconstructSortLevelAndSort pf.getResult[0]![0]![i]!.getSort!
        if let some j := j then
          if pf.getResult[0]![0]![i]! == pf.getResult[1]![0]![j]! then
            let lp ← Meta.mkLambdaFVars #[ys[j]!] p
            let lq ← Meta.mkLambdaFVars #[ys[j]!] q
            let hx ← Meta.mkLambdaFVars #[ys[j]!] h
            return (if j == 0 then none else some (j - 1), mkApp2 (.const ``Bool.forall [u]) α lp,
              mkApp2 (.const ``Bool.forall [u]) α lq,
              mkAppN (.const ``Quant.forall_congr_bool [u]) #[α, lp, lq, hx])
        let hα ← Meta.synthInstance (mkApp (.const ``Nonempty [u]) α)
        let lp := .lam (getVariableName pf.getResult[0]![0]![i]!) α p .default
        return (j, mkApp2 (.const ``Bool.forall [u]) α lp, q,
          mkAppN (.const ``Quant.forall_const_bool [u]) #[α, hα, p, q, h])
      let i := pf.getResult[0]![0]!.getNumChildren
      let j := if ys.isEmpty then none else some (ys.size - 1)
      let (_, _, _, h) ← (List.range i).foldrM f (j, b, b, q(Eq.refl $b))
      return h
    addEqThm pf.getResult h
  | .QUANT_MERGE_PRENEX =>
    -- Both sides are reconstructed as `Bool.forall fun x₁ => ⋯ Bool.forall fun xₙ => F`.
    let b : Q(Bool) ← reconstructTerm pf.getResult[0]!
    addEqThm pf.getResult q(Eq.refl $b)
  | .QUANT_MINISCOPE_AND =>
    -- `(forall xs (and F₁ … Fₙ)) = (and (forall xs F₁) … (forall xs Fₙ))`, one variable at a time
    -- from the innermost.
    let mut xs := #[]
    for x in pf.getResult[0]![0]! do
      xs := xs.push (getVariableName x, fun _ => reconstructSort x.getSort!)
    let h ← Meta.withLocalDeclsD xs fun xs => withNewTermCache do
      let gs ← pf.getResult[0]![1]!.getChildren.mapM reconstructTerm
      let b ← reconstructTerm pf.getResult[0]![1]!
      let h ← Meta.mkExpectedTypeHint (← Meta.mkEqRefl b) (← Meta.mkEq b (← andN gs))
      -- `h : p = andN gs`, where `p` and the conjuncts `gs` are quantified over the variables seen
      -- so far.
      let f := fun x (p, gs, h) => do
        let α ← Meta.inferType x
        let u ← Meta.getLevel α
        let lgs ← gs.mapM (Meta.mkLambdaFVars #[x] ·)
        let ps ← mkPListLit (.forallE `x α (.const ``Bool []) .default) lgs.toList
        let h₁ ← Meta.mkAppM ``Quant.forall_congr_bool #[← Meta.mkLambdaFVars #[x] h]
        let h₂ := mkApp2 (.const ``Quant.miniscope_andN [u]) α ps
        let p := mkApp2 (.const ``Bool.forall [u]) α (← Meta.mkLambdaFVars #[x] p)
        return (p, lgs.map (mkApp2 (.const ``Bool.forall [u]) α), ← Meta.mkEqTrans h₁ h₂)
      let (_, _, h) ← xs.foldrM f (b, gs, h)
      return h
    addEqThm pf.getResult h
  | .QUANT_MINISCOPE_OR =>
    -- `(forall xs (or F₁ … Fₙ)) = (or (forall xs₁ F₁) … (forall xsₙ Fₙ))`, where `xsᵢ` are the
    -- variables of `Fᵢ`, one variable at a time from the innermost.
    let mut xs := #[]
    for x in pf.getResult[0]![0]! do
      xs := xs.push (getVariableName x, fun _ => reconstructSort x.getSort!)
    let h ← Meta.withLocalDeclsD xs fun xs => withNewTermCache do
      let mut xss := #[]
      let mut ci := 0
      for i in [0:pf.getResult[1]!.getNumChildren] do
        let F := pf.getResult[0]![1]![i]!
        let xsF := pf.getResult[1]![i]!
        if xsF.getKind! == .FORALL && xsF != F then
          xss := xss.push xs[ci:ci + xsF[0]!.getNumChildren]
          ci := ci + xsF[0]!.getNumChildren
        else
          xss := xss.push xs[ci:ci]
      let ps := (← pf.getResult[0]![1]!.getChildren.mapM reconstructTerm).toList
      let b ← reconstructTerm pf.getResult[0]![1]!
      let h ← Meta.mkExpectedTypeHint (← Meta.mkEqRefl b) (← Meta.mkEq b (← orN ps))
      -- `h : p = orN (ps ++ q :: rs)`, where `q` is the disjunct of the current variables.
      let fin := fun x (p, ps, q, rs, h) => do
        let α ← Meta.inferType x
        let u ← Meta.getLevel α
        let lq ← Meta.mkLambdaFVars #[x] q
        let h₁ ← Meta.mkAppM ``Quant.forall_congr_bool #[← Meta.mkLambdaFVars #[x] h]
        let h₂ := mkAppN (.const ``Quant.forall_orN [u])
          #[α, ← Meta.mkListLit (.const ``Bool []) ps, lq, ← Meta.mkListLit (.const ``Bool []) rs]
        let p := mkApp2 (.const ``Bool.forall [u]) α (← Meta.mkLambdaFVars #[x] p)
        return (p, ps, mkApp2 (.const ``Bool.forall [u]) α lq, rs, ← Meta.mkEqTrans h₁ h₂)
      let fout := fun xs (p, ps, q, rs, h) => do
        let (p, ps, q, rs, h) ← xs.foldrM fin (p, ps, q, rs, h)
        return (p, ps.dropLast, ps.getLastD (.const ``Bool.false []), q :: rs, h)
      let (_, _, _, _, h) ← xss.foldrM fout (b, ps.dropLast, ps.getLast!, [], h)
      return h
    addEqThm pf.getResult h
  | .QUANT_MINISCOPE_ITE =>
    -- `(forall xs (ite c F G)) = (ite c (forall xs F) (forall xs G))`, where `c` does not depend on
    -- `xs`, holds by cases on `c`.
    let c : Q(Bool) ← reconstructTerm pf.getResult[1]![0]!
    addEqTac pf.getResult fun mv => do
      let (fvs, mv) ← mv.generalize #[{ expr := c }]
      for g in ← mv.cases fvs[0]! do
        g.mvarId.refl
  | .QUANT_VAR_ELIM_EQ =>
    -- `(forall ((x T)) (or (not (= x t)) F₁ … Fₙ))` is `(or F₁ … Fₙ)[t/x]`, and
    -- `(forall ((x T)) (not (= x t)))` is `false`.
    let lb := pf.getResult[0]![1]!
    let eq := if lb.getKind! == .OR then lb[0]![0]! else lb[0]!
    let α ← reconstructSort eq[0]!.getSort!
    let v ← Meta.getLevel α
    let n : Name := getVariableName eq[0]!
    let t ← reconstructTerm eq[1]!
    -- the instances of `Decidable (x = t)` of the Boolean formulas `decide (x = t)`
    let insts ← Meta.withLocalDeclD n α fun x => do Meta.mkLambdaFVars #[x] (← Bool.eqInst α x t)
    if lb.getKind! == .OR then
      let b ← Meta.withLocalDeclD n α fun x => withNewTermCache do
        let mut b : Q(Bool) ← reconstructTerm lb[lb.getNumChildren - 1]!
        for i in [1:lb.getNumChildren - 1] do
          let c : Q(Bool) ← reconstructTerm lb[lb.getNumChildren - i - 1]!
          b := q($c || $b)
        Meta.mkLambdaFVars #[x] b
      addEqThm pf.getResult (mkAppN (.const ``Quant.var_elim_eq_or_bool [v]) #[α, t, insts, b])
    else
      addEqThm pf.getResult (mkAppN (.const ``Quant.var_elim_eq_bool [v]) #[α, t, insts])
  | _ => return none
where
  /-- The `PList` literal of the elements `es` of type `α`. -/
  mkPListLit (α : Expr) (es : List Expr) : MetaM Expr := do
    let u ← Meta.getLevel α
    let nil := mkApp (.const ``Quant.PList.nil [u]) α
    return es.foldr (mkApp3 (.const ``Quant.PList.cons [u]) α) nil
  /-- `Bool.andN [b₁, …, bₙ]`. -/
  andN (bs : Array Expr) : MetaM Expr := do
    return mkApp (.const ``Bool.andN []) (← Meta.mkListLit (.const ``Bool []) bs.toList)
  /-- `Bool.orN [b₁, …, bₙ]`. -/
  orN (bs : List Expr) : MetaM Expr := do
    return mkApp (.const ``Bool.orN []) (← Meta.mkListLit (.const ``Bool []) bs)

@[smt_proof_reconstruct] def reconstructQuantProof : ProofReconstructor := fun pf => do match pf.getRule with
  | .THEORY_REWRITE => reconstructRewrite pf
  | .CONG =>
    let k := pf.getResult[0]!.getKind!
    -- This rule needs more care for closures.
    if k == .FORALL then
      reconstructQuantCong ``Bool.forall pf
    else if k == .EXISTS then
      reconstructQuantCong ``Bool.exists pf
    else
      return none
  | .SKOLEMIZE => reconstructSkolemize pf
  | .INSTANTIATE =>
    -- Eliminate the quantifiers `Bool.forall fun x₁ => ⋯ Bool.forall fun xₙ => F` one by one.
    let mut h ← reconstructProof pf.getChildren[0]!
    let mut b ← reconstructTerm pf.getChildren[0]!.getResult
    for t in pf.getArguments[0]! do
      let e ← reconstructTerm t
      let α := b.getArg! 0
      let p := b.getArg! 1
      h := mkApp4 (.const ``Quant.forall_elim [← Meta.getLevel α]) α p h e
      b := p.beta #[e]
    addThm (← reconstructProofType pf.getResult) h
  | .ALPHA_EQUIV =>
    let t : Q(Bool) ← reconstructTerm pf.getResult[0]!
    addEqThm pf.getResult q(Eq.refl $t)
  | .QUANT_VAR_REORDERING =>
    -- `(forall xs F) = (forall ys F)`, where `ys` is a permutation of `xs`: eliminate the quantifiers
    -- of one side and introduce those of the other.
    let xs := pf.getResult[0]![0]!.getChildren
    let ys := pf.getResult[1]![0]!.getChildren
    let p ← reconstructTerm pf.getResult[0]!
    let q ← reconstructTerm pf.getResult[1]!
    let hpq ← reorder p xs ys
    let hqp ← reorder q ys xs
    addEqThm pf.getResult (← Meta.mkAppM ``Quant.bool_eq_of_imp #[hpq, hqp])
  | _ => return none
where
  /-- A proof of `p = true → (forall ys F) = true`, where `p` is `(forall xs F)` and `ys` is a
  permutation of `xs`. -/
  reorder (p : Expr) (xs ys : Array cvc5.Term) : ReconstructM Expr := do
    let decls := ys.map fun y => (getVariableName y, fun _ => reconstructSort y.getSort!)
    Meta.withLocalDeclD `hp (← Meta.mkEq p (.const ``Bool.true [])) fun hp => do
      let h ← Meta.withLocalDeclsD decls fun fvs => do
        let mut h := hp
        for x in xs do
          let some i := ys.findIdx? (· == x) | throwError "[var_reordering]: unknown variable {x}"
          h ← Meta.mkAppM ``Quant.forall_elim #[h, fvs[i]!]
        for fv in fvs.reverse do
          h ← Meta.mkAppM ``Quant.forall_intro #[← Meta.mkLambdaFVars #[fv] h]
        return h
      Meta.mkLambdaFVars #[hp] h
  /-- Congruence for `(forall xs F) = (forall xs G)` (and `exists`) from a proof of `F = G` under
  the bound variables `xs`. -/
  reconstructQuantCong (op : Name) (pf : cvc5.Proof) : ReconstructM Expr := do
    let mut xs := #[]
    for x in pf.getResult[0]![0]! do
      xs := xs.push (getVariableName x, fun _ => reconstructSort x.getSort!)
    let (_, _, h) ← Meta.withLocalDeclsD xs fun xs => withNewTermCache <| withNewProofCache <| withAssums xs do
      let b₁ ← reconstructTerm pf.getResult[0]![1]!
      let b₂ ← reconstructTerm pf.getResult[1]![1]!
      let h ← reconstructEqProof pf.getChildren[0]!
      let f := fun x (b₁, b₂, h) => do
        let α ← Meta.inferType x
        let q := mkApp (.const op [← Meta.getLevel α]) α
        let hq ← Meta.mkCongrArg q (← Meta.mkFunExt (← Meta.mkLambdaFVars #[x] h))
        return (mkApp q (← Meta.mkLambdaFVars #[x] b₁), mkApp q (← Meta.mkLambdaFVars #[x] b₂), hq)
      xs.foldrM f (b₁, b₂, h)
    addEqThm pf.getResult h
  /-- From `(not (forall xs F))`, conclude `(not F[sk/xs])` with the skolems `sk` of `xs`. -/
  reconstructSkolemize (pf : cvc5.Proof) : ReconstructM Expr := do
    let chRes := pf.getChildren[0]!.getResult
    let es ← reconstructQuant.reconstructForallSkolems chRes[0]! (chRes[0]![0]!.getNumChildren - 1)
    let mut h ← reconstructProof pf.getChildren[0]!
    let mut b ← reconstructTerm chRes[0]!
    for e in es do
      let α := b.getArg! 0
      let p := b.getArg! 1
      let u ← Meta.getLevel α
      let hα ← Meta.synthInstance (mkApp (.const ``Nonempty [u]) α)
      h := mkApp4 (.const ``Quant.forall_skolem [u]) α hα p h
      b := p.beta #[e]
    addThm (← reconstructProofType pf.getResult) h

end Smt.Reconstruct.Quant
