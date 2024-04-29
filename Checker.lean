import Smt

import Lean

open Lean
open Qq

open cvc5 in
def cvc5.prove (query : String) : IO (Except Error Proof) := do
  Solver.run (← TermManager.new) do
    Solver.setOption "dag-thresh" "0"
    Solver.setOption "simplification" "none"
    Solver.setOption "enum-inst" "true"
    Solver.setOption "produce-models" "true"
    Solver.setOption "produce-proofs" "true"
    Solver.setOption "proof-elim-subtypes" "true"
    Solver.setOption "proof-granularity" "dsl-rewrite"
    Solver.parse query
    let r ← Solver.checkSat
    if r.isUnsat then
      let ps ← Solver.getProof
      if h : 0 < ps.size then
        return ps[0]
    throw (Error.user_error "expected unsat result")

partial def getBoundVars (t : cvc5.Term) : HashSet cvc5.Term :=
  go t {}
where
  go (t : cvc5.Term) (bvs : HashSet cvc5.Term) : HashSet cvc5.Term := Id.run do
    if t.getKind == .VARIABLE then
      return bvs.insert t
    let mut bvs := bvs
    for ct in t do
      bvs := go ct bvs
    return bvs


partial def getFreeVars (t : cvc5.Term) : HashSet cvc5.Term :=
  go t {}
where
  go (t : cvc5.Term) (fvs : HashSet cvc5.Term) : HashSet cvc5.Term := Id.run do
    if t.getKind == .CONSTANT then
      return fvs.insert t
    let mut bvs := fvs
    for ct in t do
      bvs := go ct bvs
    return bvs

partial def getUninterpretedSorts (t : cvc5.Term) : HashSet cvc5.Sort :=
  let vs := HashSet.merge (getBoundVars t) (getFreeVars t)
  vs.fold (fun ss v => go v.getSort ss) {}
where
  go (s : cvc5.Sort) (ss : HashSet cvc5.Sort) : HashSet cvc5.Sort := Id.run do
    if s.getKind == .UNINTERPRETED_SORT || s.getKind == .INTERNAL_SORT_KIND then
      return ss.insert s
    if s.getKind != .FUNCTION_SORT then
      return ss
    let mut ss := ss
    for ds in s.getFunctionDomainSorts do
      ss := go ds ss
    ss := go s.getFunctionCodomainSort ss
    return ss

def withDeclaredSorts [Inhabited α] (ss : Array cvc5.Sort) (k : Array Expr → MetaM α) : MetaM α := do
  let sorts : Array (Name × (Array Expr → MetaM Expr)) := ss.map (fun s => (s.getSymbol, fun _ => return q(Type)))
  let mut insts : Array (Name × (Array Expr → MetaM Expr)) := #[]
  for i in [:ss.size] do
    insts := insts.push (Name.anonymous, fun xs => return .app q(Nonempty.{1}) xs[i]!)
  Meta.withLocalDeclsD (sorts ++ insts) k

def withDeclaredFuns [Inhabited α] (vs : Array cvc5.Term) (k : Array Expr → MetaM α) : MetaM α := do
  let state := ⟨{}, {}, {}, 0, #[], #[]⟩
  let fvs : Array (Name × (Array Expr → MetaM Expr)) := vs.map (fun v => (v.getSymbol, fun _ => do
    let (t, _) ← (Smt.Reconstruct.reconstructSort v.getSort).run state
    return t))
  Meta.withLocalDeclsD fvs k

def withDecls [Inhabited α] (ss : Array cvc5.Sort) (vs : Array cvc5.Term) (k : Array Expr → MetaM α) : MetaM α :=
  withDeclaredSorts ss fun ts => withDeclaredFuns vs fun fvs => k (ts ++ fvs)

def checkProof (pf : cvc5.Proof) : MetaM Unit := do
  withDecls (getUninterpretedSorts pf.getResult).toArray (getFreeVars pf.getResult).toArray fun xs => do
  let (value, mvs) ← Smt.reconstructProof pf
  if !mvs.isEmpty then
    logInfo "proof contains trusted steps"
    for mv in mvs do
      let p : Q(Prop) ← mv.getType
      mv.assign q(sorry : $p)
  let value ← instantiateMVars value
  let value ← Meta.mkLambdaFVars xs value
  let type ← Meta.inferType value
  let r := (← getEnv).addDecl (.thmDecl { name := `thm, levelParams := [], type := type, value })
  match r with
  | .error e =>
    logInfo (e.toMessageData Options.empty)
  | .ok env =>
    modifyEnv fun _ => env

unsafe def main (args : List String) : IO Unit := do
  Lean.initSearchPath (← Lean.findSysroot)
  let query ← IO.FS.readFile args[0]!
  match ← cvc5.prove query with
  | .error e =>
    IO.println (repr e)
  | .ok pf =>
    let check := do
      checkProof pf
      (← Core.getMessageLog).forM fun msg => do IO.print (← msg.toString)
    Lean.withImportModules #[`Smt] Lean.Options.empty 0 fun env => do
      _ ← MetaEval.eval env Options.empty check true

#eval show Elab.Command.CommandElabM Unit from do
  let query ← IO.FS.readFile "test4.smt2"
  match ← cvc5.prove query with
  | .error e =>
    IO.println (repr e)
  | .ok pf =>
    Lean.Elab.Command.runTermElabM (fun _ => checkProof pf)

#eval main ["test4.smt2"]
