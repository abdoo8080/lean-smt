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

/-- `(forall ((x₁ T₁) … (xₙ Tₙ)) F)` is reconstructed as `decide (∀ x₁ … xₙ, ⟦F⟧ = true)`, and
`exists` likewise. -/
@[smt_term_reconstruct] def reconstructQuant : TermReconstructor := fun t => do match t.getKind! with
  | .FORALL =>
    let mut xs : Array (Name × (Array Expr → ReconstructM Expr)) := #[]
    for x in t[0]! do
      xs := xs.push (getVariableName x, fun _ => reconstructSort x.getSort!)
    let p ← Meta.withLocalDeclsD xs fun xs => withNewTermCache do
      let b : Q(Bool) ← reconstructTerm t[1]!
      Meta.mkForallFVars xs q($b = true)
    mkDecide p
  | .EXISTS =>
    let mut xs : Array (Name × (Array Expr → ReconstructM Expr)) := #[]
    for x in t[0]! do
      xs := xs.push (getVariableName x, fun _ => reconstructSort x.getSort!)
    let p ← Meta.withLocalDeclsD xs fun xs => withNewTermCache do
      let b : Q(Bool) ← reconstructTerm t[1]!
      Meta.mkExistsFVars xs q($b = true)
    mkDecide p
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
        let ysF : Q(Prop) ← Meta.mkForallFVars xs[i + 1:] q($F = true)
        let xysF ← Meta.mkLambdaFVars #[xs[i]!] q(¬$ysF)
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
    let mut xs := #[]
    for x in pf.getResult[0]![0]! do
      xs := xs.push (getVariableName x, fun _ => reconstructSort x.getSort!)
    let (_, _, _, h) ← Meta.withLocalDeclsD xs fun xs => withNewTermCache do
      let c : Q(Prop) ← reconstructProp pf.getResult[0]![1]![0]!
      let p : Q(Prop) ← reconstructProp pf.getResult[0]![1]![1]!
      let q : Q(Prop) ← reconstructProp pf.getResult[0]![1]![2]!
      let hc : Q(Decidable $c) ← mkDecidableInst q($c)
      let h : Q((ite $c $p $q) = (ite $c $p $q)) := q(Eq.refl (ite $c $p $q))
      let f := fun x (p, q, r, h) => do
        let u ← Meta.getLevel (← Meta.inferType x)
        let α : Q(Sort u) ← Meta.inferType x
        let lp : Q($α → Prop) ← Meta.mkLambdaFVars #[x] p
        let lq : Q($α → Prop) ← Meta.mkLambdaFVars #[x] q
        let lr : Q($α → Prop) ← Meta.mkLambdaFVars #[x] r
        let hx : Q(∀ x, $lr x = ite $c ($lp x) ($lq x)) ← Meta.mkLambdaFVars #[x] h
        let ap ← Meta.mkForallFVars #[x] p
        let aq ← Meta.mkForallFVars #[x] q
        let ar ← Meta.mkForallFVars #[x] r
        return (ap, aq, ar, q(Eq.trans (forall_congr $hx) (@miniscope_ite $α $c $hc $lp $lq)))
      xs.foldrM f (p, q, q(ite $c $p $q), h)
    addPropThm pf.getResult h
  | .QUANT_VAR_ELIM_EQ =>
    -- `(forall ((x T)) (or (not (= x t)) F₁ … Fₙ))` is `(or F₁ … Fₙ)[t/x]`, and
    -- `(forall ((x T)) (not (= x t)))` is `false`.
    let lb := pf.getResult[0]![1]!
    let eq := if lb.getKind! == .OR then lb[0]![0]! else lb[0]!
    let (u, (α : Q(Sort u))) ← reconstructSortLevelAndSort eq[0]!.getSort!
    let n : Name := getVariableName eq[0]!
    let t : Q($α) ← reconstructTerm eq[1]!
    let hx : Q(∀ x : $α, Decidable (x = $t)) ← Meta.withLocalDeclD n α fun x => do
      let x : Q($α) ← pure x
      Meta.mkLambdaFVars #[x] (← mkDecidableInst q($x = $t))
    let (_, h) ← getDecide! (← reconstructTerm pf.getResult[0]!)
    if lb.getKind! == .OR then
      let b : Q($α → Bool) ← Meta.withLocalDeclD n α fun x => withNewTermCache do
        let mut b : Q(Bool) ← reconstructTerm lb[lb.getNumChildren - 1]!
        for i in [1:lb.getNumChildren - 1] do
          let c : Q(Bool) ← reconstructTerm lb[lb.getNumChildren - i - 1]!
          b := q($c || $b)
        Meta.mkLambdaFVars #[x] b
      let h : Q(Decidable (∀ x, (!@decide (x = $t) ($hx x) || $b x) = true)) ← pure h
      addEqThm pf.getResult q(@Quant.var_elim_eq_or_bool $α $t $b $hx $h)
    else
      let h : Q(Decidable (∀ x, (!@decide (x = $t) ($hx x)) = true)) ← pure h
      addEqThm pf.getResult q(@Quant.var_elim_eq_bool $α $t $hx $h)
  | _ => return none

@[smt_proof_reconstruct] def reconstructQuantProof : ProofReconstructor := fun pf => do match pf.getRule with
  | .THEORY_REWRITE => reconstructRewrite pf
  | .CONG =>
    let k := pf.getResult[0]!.getKind!
    -- This rule needs more care for closures.
    if k == .FORALL then
      reconstructQuantCong pf
    else if k == .EXISTS then
      reconstructQuantCong pf
    else
      return none
  | .SKOLEMIZE => reconstructSkolemize pf
  | .INSTANTIATE =>
    -- `⟦(forall xs F)⟧ = decide (∀ xs, ⟦F⟧ = true)`, so its proof yields `∀ xs, ⟦F⟧ = true`.
    let h ← reconstructProof pf.getChildren[0]!
    let (p, inst) ← getDecide! (← reconstructTerm pf.getChildren[0]!.getResult)
    let p : Q(Prop) ← pure p
    let inst : Q(Decidable $p) ← pure inst
    let h : Q(decide $p = true) ← pure h
    let xsF : Q($p) := q(@of_decide_eq_true $p $inst $h)
    let mut es := #[]
    for t in pf.getArguments[0]! do
      es := es.push (← reconstructTerm t)
    addThm (← reconstructProofType pf.getResult) (mkAppN xsF es)
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
    -- The propositions `∀ xs, ⟦F⟧ = true` and `∀ ys, ⟦F⟧ = true` of both sides.
    let (p, hp) ← getDecide! (← reconstructTerm pf.getResult[0]!)
    let (q, hq) ← getDecide! (← reconstructTerm pf.getResult[1]!)
    let p : Q(Prop) ← pure p
    let q : Q(Prop) ← pure q
    let hp : Q(Decidable $p) ← pure hp
    let hq : Q(Decidable $q) ← pure hq
    let hpq ← ys.foldrM f (mkAppN (.bvar js.size) is)
    let hpq : Q($p → $q) ← pure (.lam `hp p hpq .default)
    let hqp ← xs.foldrM f (mkAppN (.bvar is.size) js)
    let hqp : Q($q → $p) ← pure (.lam `hq q hqp .default)
    addEqThm pf.getResult q(@Bool.decide_congr $p $q $hp $hq (propext ⟨$hpq, $hqp⟩))
  | _ => return none
where
  /-- Congruence for `(forall xs F) = (forall xs G)` (and `exists`) from a proof of `F = G` under
  the bound variables `xs`. -/
  reconstructQuantCong (pf : cvc5.Proof) : ReconstructM Expr := do
    let isForall := pf.getResult[0]!.getKind! == .FORALL
    let mut xs := #[]
    for x in pf.getResult[0]![0]! do
      xs := xs.push (getVariableName x, fun _ => reconstructSort x.getSort!)
    let (p, q, h) ← Meta.withLocalDeclsD xs fun xs => withNewTermCache <| withNewProofCache <| withAssums xs do
      let b₁ : Q(Bool) ← reconstructTerm pf.getResult[0]![1]!
      let b₂ : Q(Bool) ← reconstructTerm pf.getResult[1]![1]!
      let h : Q($b₁ = $b₂) ← reconstructEqProof pf.getChildren[0]!
      let h : Q(($b₁ = true) = ($b₂ = true)) := q(congrArg (· = true) $h)
      let f := fun x (p, q, h) => do
        let u ← Meta.getLevel (← Meta.inferType x)
        let α : Q(Sort u) ← Meta.inferType x
        let lp : Q($α → Prop) ← Meta.mkLambdaFVars #[x] p
        let lq : Q($α → Prop) ← Meta.mkLambdaFVars #[x] q
        let hx : Q(∀ x : $α, $lp x = $lq x) ← Meta.mkLambdaFVars #[x] h
        if isForall then
          let ap ← Meta.mkForallFVars #[x] p
          let aq ← Meta.mkForallFVars #[x] q
          return (ap, aq, q(forall_congr $hx))
        else
          let ep ← Meta.mkExistsFVars #[x] p
          let eq ← Meta.mkExistsFVars #[x] q
          return (ep, eq, q(Bool.exists_congr_eq $hx))
      xs.foldrM f (q($b₁ = true), q($b₂ = true), h)
    let p : Q(Prop) ← pure p
    let q : Q(Prop) ← pure q
    let h : Q($p = $q) ← pure h
    let hp : Q(Decidable $p) ← mkDecidableInst p
    let hq : Q(Decidable $q) ← mkDecidableInst q
    addEqThm pf.getResult q(@Bool.decide_congr $p $q $hp $hq $h)
  /-- From `(not (forall xs F))`, conclude `(not F[sk/xs])` with the skolems `sk` of `xs`. -/
  reconstructSkolemize (pf : cvc5.Proof) : ReconstructM Expr := do
    let chRes := pf.getChildren[0]!.getResult
    let es ← reconstructQuant.reconstructForallSkolems chRes[0]! (chRes[0]![0]!.getNumChildren - 1)
    let (p, hp) ← getDecide! (← reconstructTerm chRes[0]!)
    let p : Q(Prop) ← pure p
    let hp : Q(Decidable $p) ← pure hp
    let hnp : Q((!decide $p) = true) ← reconstructProof pf.getChildren[0]!
    let hnp : Q(¬$p) := q(Eq.mp Bool.not_decide_eq_true_iff $hnp)
    let f := fun h e => do
      let u ← Meta.getLevel (e.getArg! 0)
      let α : Q(Sort u) ← pure (e.getArg! 0)
      let hα : Q(Nonempty $α) ← Meta.synthInstance q(Nonempty $α)
      let .lam n _ (.app _ b) bi := e.getArg! 2 | throwError "[skolemize]: expected a predicate with a negated body: {e}"
      let p : Q($α → Prop)  ← pure (.lam n α b bi)
      let h : Q(¬∀ x, $p x) ← pure h
      return q(@Classical.epsilon_spec_aux' $α $hα $p $h)
    -- The last skolem gives a proof of `¬⟦F[sk/xs]⟧ = true`.
    let h : Expr ← es.foldlM f hnp
    let b : Q(Bool) ← reconstructTerm pf.getResult[0]!
    let h : Q(¬$b = true) ← pure h
    addThm (← reconstructProofType pf.getResult) q(Bool.not_eq_true_of_not $h)

end Smt.Reconstruct.Quant
