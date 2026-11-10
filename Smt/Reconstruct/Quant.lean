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

/-- `smtForall fun x₁ => ⋯ smtForall fun xₙ => b` (or with `smtExists`) over the free variables `xs`
of the Boolean formula `b`. -/
def mkSmtQuantFVars (op : Name) (xs : Array Expr) (b : Expr) : MetaM Expr :=
  xs.foldrM (init := b) fun x b => do
    let α ← Meta.inferType x
    return mkApp2 (.const op [← Meta.getLevel α]) α (← Meta.mkLambdaFVars #[x] b)

/-- `(forall ((x₁ T₁) … (xₙ Tₙ)) F)` is reconstructed as `smtForall fun x₁ => ⋯ smtForall fun xₙ =>
⟦F⟧`, and `exists` likewise. -/
@[smt_term_reconstruct] def reconstructQuant : TermReconstructor := fun t => do match t.getKind! with
  | .FORALL =>
    let mut xs : Array (Name × (Array Expr → ReconstructM Expr)) := #[]
    for x in t[0]! do
      xs := xs.push (getVariableName x, fun _ => reconstructSort x.getSort!)
    Meta.withLocalDeclsD xs fun xs => withNewTermCache do
      mkSmtQuantFVars ``smtForall xs (← reconstructTerm t[1]!)
  | .EXISTS =>
    let mut xs : Array (Name × (Array Expr → ReconstructM Expr)) := #[]
    for x in t[0]! do
      xs := xs.push (getVariableName x, fun _ => reconstructSort x.getSort!)
    Meta.withLocalDeclsD xs fun xs => withNewTermCache do
      mkSmtQuantFVars ``smtExists xs (← reconstructTerm t[1]!)
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
        let ysF : Q(Bool) ← mkSmtQuantFVars ``smtForall xs[i + 1:] F
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
    let mut xs := #[]
    for x in pf.getResult[0]![0]! do
      xs := xs.push (getVariableName x, fun _ => reconstructSort x.getSort!)
    let ((q : Q(Prop)), (p : Q(Prop)), (h : Q((¬$q) = $p))) ← Meta.withLocalDeclsD xs fun xs => withNewTermCache do
      let b : Q(Prop) ← reconstructProp pf.getResult[0]![1]!
      let h := q(Classical.not_not_eq $b)
      let f := fun x (p, q, h) => do
        let u ← Meta.getLevel (← Meta.inferType x)
        let α : Q(Sort u) ← Meta.inferType x
        let lp : Q($α → Prop) ← Meta.mkLambdaFVars #[x] p
        let lq : Q($α → Prop) ← Meta.mkLambdaFVars #[x] q
        let hx : Q(∀ x : $α, (¬$lp x) = $lq x) ← Meta.mkLambdaFVars #[x] h
        let ap ← Meta.mkForallFVars #[x] p
        let eq ← Meta.mkExistsFVars #[x] q
        return (ap, eq, q(Eq.trans (Classical.not_forall_eq $lp) (congrArg Exists (funext $hx))))
      xs.foldrM f (q(¬$b), b, h)
    addPropThm pf.getResult q(@Eq.symm Prop (¬$q) $p $h)
  | .QUANT_UNUSED_VARS =>
    let mut ys := #[]
    if pf.getResult[1]!.getKind! == .FORALL then
      for y in pf.getResult[1]![0]! do
        ys := ys.push (getVariableName y, fun _ => reconstructSort y.getSort!)
    let (_, p, q, h) ← Meta.withLocalDeclsD ys fun ys => withNewTermCache do
      let b : Q(Prop) ← reconstructProp pf.getResult[0]![1]!
      let h : Q($b = $b) := q(Eq.refl $b)
      let f := fun i (j, p, q, (h : Q($p = $q))) => do
        let (u, (α : Q(Sort u))) ← reconstructSortLevelAndSort pf.getResult[0]![0]![i]!.getSort!
        if let some j := j then
          if pf.getResult[0]![0]![i]! == pf.getResult[1]![0]![j]! then
            let lp : Q($α → Prop) ← Meta.mkLambdaFVars #[ys[j]!] p
            let lq : Q($α → Prop) ← Meta.mkLambdaFVars #[ys[j]!] q
            let hx : Q(∀ x : $α, $lp x = $lq x) ← Meta.mkLambdaFVars #[ys[j]!] h
            let ap ← Meta.mkForallFVars #[ys[j]!] p
            let aq ← Meta.mkForallFVars #[ys[j]!] q
            return (if j == 0 then none else some (j - 1), ap, aq, q(forall_congr $hx))
        let hα : Q(Nonempty $α) ← Meta.synthInstance q(Nonempty $α)
        let ap := .forallE (getVariableName pf.getResult[0]![0]![i]!) α p .default
        return (j, ap, q, q(@forall_const_eq $α $hα $p $q $h))
      let i := pf.getResult[0]![0]!.getNumChildren
      let j := if ys.isEmpty then none else some (ys.size - 1)
      (List.range i).foldrM f (j, b, b, h)
    let h : Q($p = $q) ← pure h
    addPropThm pf.getResult h
  | .QUANT_MERGE_PRENEX =>
    -- The propositions denoted by both sides are the same `∀ x₁ … xₙ, F`.
    let p : Q(Prop) ← reconstructProp pf.getResult[0]!
    addPropThm pf.getResult q(Eq.refl $p)
  | .QUANT_MINISCOPE_AND =>
    let mut xs := #[]
    for x in pf.getResult[0]![0]! do
      xs := xs.push (getVariableName x, fun _ => reconstructSort x.getSort!)
    let (_, _, h) ← Meta.withLocalDeclsD xs fun xs => withNewTermCache do
      let mut ps : Array Q(Prop) := #[]
      for ct in pf.getResult[0]![1]! do
        let p : Q(Prop) ← reconstructProp ct
        ps := ps.push q($p)
      let b : Q(Prop) ← reconstructProp pf.getResult[0]![1]!
      let h : Q($b = $b) := q(Eq.refl $b)
      let lf := fun x (u, (α : Q(Sort u))) p lps => do
        let lp : Q($α → Prop) ← (return ← Meta.mkLambdaFVars #[x] p)
        return .app q(PList.cons $lp) lps
      let f := fun x (p, ps, h) => do
        let u ← Meta.getLevel (← Meta.inferType x)
        let α : Q(Sort u) ← Meta.inferType x
        let lp : Q($α → Prop) ← Meta.mkLambdaFVars #[x] p
        let (lps : Q(PList ($α → Prop))) ← ps.foldrM (lf x (u, α)) q(@PList.nil ($α → Prop))
        let hx : Q(∀ x, $lp x = pAndN («$lps».map (· x))) ← Meta.mkLambdaFVars #[x] h
        let ap ← Meta.mkForallFVars #[x] p
        let aps ← liftM (ps.mapM (Meta.mkForallFVars #[x]))
        return (ap, aps, q(Eq.trans (forall_congr $hx) (@miniscope_andN $α $lps)))
      xs.foldrM f (b, ps, h)
    addPropThm pf.getResult h
  | .QUANT_MINISCOPE_OR =>
    let mut xs := #[]
    for x in pf.getResult[0]![0]! do
      xs := xs.push (getVariableName x, fun _ => reconstructSort x.getSort!)
    let (_, _, _, _, h) ← Meta.withLocalDeclsD xs fun xs => withNewTermCache do
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
      let ps : List Q(Prop) := (← pf.getResult[0]![1]!.getChildren.mapM reconstructProp).toList
      let b : Q(Prop) ← reconstructProp pf.getResult[0]![1]!
      let h : Q($b = $b) := q(Eq.refl $b)
      let fin := fun x (p, ps, q, rs, h) => do
        let u ← Meta.getLevel (← Meta.inferType x)
        let α : Q(Sort u) ← Meta.inferType x
        let lp : Q($α → Prop) ← Meta.mkLambdaFVars #[x] p
        let lq : Q($α → Prop) ← Meta.mkLambdaFVars #[x] q
        let qps : Q(List Prop) ← pure (ps.foldr (fun (p : Q(Prop)) qps => q($p :: $qps)) q([]))
        let qrs : Q(List Prop) ← pure (rs.foldr (fun (r : Q(Prop)) qrs => q($r :: $qrs)) q([]))
        let hx : Q(∀ x, $lp x = orN ($qps ++ $lq x :: $qrs)) ← Meta.mkLambdaFVars #[x] h
        let ap ← Meta.mkForallFVars #[x] p
        let aq ← Meta.mkForallFVars #[x] q
        return (ap, ps, aq, rs, q(Eq.trans (forall_congr $hx) (@miniscope_orN $α $qps $lq $qrs)))
      let fout := fun xs (p, ps, q, rs, h) => do
        let (p, ps, q, rs, h) ← xs.foldrM fin (p, ps, q, rs, h)
        return (p, ps.dropLast, ps.getLastD q(False), q :: rs, h)
      xss.foldrM fout (b, ps.dropLast, ps.getLast!, [], h)
    addPropThm pf.getResult h
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
    let (u, (α : Q(Sort u))) ← reconstructSortLevelAndSort eq[0]!.getSort!
    let n : Name := getVariableName eq[0]!
    let t : Q($α) ← reconstructTerm eq[1]!
    if lb.getKind! == .OR then
      let b : Q($α → Bool) ← Meta.withLocalDeclD n α fun x => withNewTermCache do
        let mut b : Q(Bool) ← reconstructTerm lb[lb.getNumChildren - 1]!
        for i in [1:lb.getNumChildren - 1] do
          let c : Q(Bool) ← reconstructTerm lb[lb.getNumChildren - i - 1]!
          b := q($c || $b)
        Meta.mkLambdaFVars #[x] b
      addEqThm pf.getResult q(@Quant.var_elim_eq_or_bool $α $t $b)
    else
      addEqThm pf.getResult q(@Quant.var_elim_eq_bool $α $t)
  | _ => return none

@[smt_proof_reconstruct] def reconstructQuantProof : ProofReconstructor := fun pf => do match pf.getRule with
  | .THEORY_REWRITE => reconstructRewrite pf
  | .CONG =>
    let k := pf.getResult[0]!.getKind!
    -- This rule needs more care for closures.
    if k == .FORALL then
      reconstructQuantCong ``smtForall pf
    else if k == .EXISTS then
      reconstructQuantCong ``smtExists pf
    else
      return none
  | .SKOLEMIZE => reconstructSkolemize pf
  | .INSTANTIATE =>
    -- Eliminate the quantifiers `smtForall fun x₁ => ⋯ smtForall fun xₙ => F` one by one.
    let mut h ← reconstructProof pf.getChildren[0]!
    let mut b ← reconstructTerm pf.getChildren[0]!.getResult
    for t in pf.getArguments[0]! do
      let e ← reconstructTerm t
      let α := b.getArg! 0
      let p := b.getArg! 1
      h := mkApp4 (.const ``Quant.smtForall_elim [← Meta.getLevel α]) α p h e
      b := p.beta #[e]
    addThm (← reconstructProofType pf.getResult) h
  | .ALPHA_EQUIV =>
    let t : Q(Bool) ← reconstructTerm pf.getResult[0]!
    addEqThm pf.getResult q(Eq.refl $t)
  | .QUANT_VAR_REORDERING =>
    let xs := pf.getResult[0]![0]!.getChildren
    let ys := pf.getResult[1]![0]!.getChildren
    let g xs := Id.run do
      let mut is : Std.HashMap cvc5.Term Expr := {}
      for h : i in [:xs.size] do
        is := is.insert xs[i] (.bvar (xs.size - i - 1))
      return is
    let (is, js) := (g xs, g ys)
    let (is, js) := (xs.map js.get!, ys.map is.get!)
    let f x h := do
      let n := getVariableName x
      let α ← reconstructSort x.getSort!
      return .lam n α h .default
    -- The propositions `∀ xs, F` and `∀ ys, F` denoted by both sides.
    let p : Q(Prop) ← reconstructProp pf.getResult[0]!
    let q : Q(Prop) ← reconstructProp pf.getResult[1]!
    let hpq ← ys.foldrM f (mkAppN (.bvar js.size) is)
    let hpq : Q($p → $q) ← pure (.lam `hp p hpq .default)
    let hqp ← xs.foldrM f (mkAppN (.bvar is.size) js)
    let hqp : Q($q → $p) ← pure (.lam `hq q hqp .default)
    addPropThm pf.getResult q(propext ⟨$hpq, $hqp⟩)
  | _ => return none
where
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
      h := mkApp4 (.const ``Quant.smtForall_skolem [u]) α hα p h
      b := p.beta #[e]
    addThm (← reconstructProofType pf.getResult) h

end Smt.Reconstruct.Quant
