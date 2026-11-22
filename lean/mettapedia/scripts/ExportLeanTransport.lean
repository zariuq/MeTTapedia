import Mettapedia.Languages.Lean.Declarations.Terms
import Mettapedia.Languages.Lean.Declarations.TargetEnvironment

/-!
Export Lean's proofs of chosen theorems, and of every theorem those proofs
cite, as first-order data, so that the Egal kernel can follow them.

Run from the project root:
`lake env lean scripts/ExportLeanTransport.lean`
imports the target's module inventory (`modules.txt`, as the terms export does),
reads the roots, one theorem per line (rows starting with `#` are comments),
from `artifacts/lean-declarations/transport/lemma-roots.txt` and writes
`artifacts/lean-declarations/transport/proofs.metta`, with `needs.txt` (the families and
functions the theorems name; those the target's roots lack are printed); `LEAN_TRANSPORT_OUT`
selects another directory.

  (TransportTheorem c (binder ..) statement)   a theorem of the closure, its statement
  (TransportLevels c (l ..))                   its level parameters, in order
                                               read as a cited lemma's is
  (TransportProof c proof)                     Lean's proof of it
  (TransportRefused c reason)                  a theorem whose statement or proof is not read
  (TransportOrder c ..)                        the theorems, each after those its proof cites
  (EgalName c ident)                           a theorem's Egal name, and each recursor's
                                               a proof applies (F.rec: the family's recursor)

A proof is written as
  (plam x T p)       an abstraction over x : T (T a term)
  (phyp h (a ..))    a hypothesis or a variable applied to arguments
  (pcite c (a ..))   a theorem (propext and Quot.sound among them) applied to arguments,
                     its level arguments first, each written (level L)
  (pctor c (a ..))   a constructor applied to arguments (`Eq.refl`, `List.Perm.cons`)
  (prec r (a ..))    a recursor applied to arguments: parameters, motive, minor
                     premises, indices, major premise
  (phave P h p)      the proof p, which uses P, proved by h (a motive at a proof,
                     whose value the reading erases)
  (pquot q (a ..))   a primitive of quotients (`Quot.ind`) applied to arguments
and an argument (a ..) that is not a proof is a term, written as the terms
export writes terms.  A definition a proof applies (`rfl`, `id`, `Eq.mpr`)
is read through its body.  The closure follows theorems only: what a proof
applies otherwise is named in the proof and read by the families export.
-/

open Lean Meta Elab Term
open Mettapedia.Languages.Lean.Declarations

/-- A proof term as Lean records it.  An argument that is not a proof is a
term (`term`). -/
inductive TProof where
  | lam (name : String) (type : FTerm) (body : TProof)
  | hyp (name : String) (args : List TProof)
  | cite (c : Name) (args : List TProof)
  | ctor (c : Name) (args : List TProof)
  | recursor (r : Name) (args : List TProof)
  | quot (q : Name) (args : List TProof)
  | proj (s : Name) (i : Nat) (of : TProof) (args : List TProof)
  | term (t : FTerm)
  /-- A proof of a proposition the proof around it needs: a cut. -/
  | cut (fact : FTerm) (proof body : TProof)
  /-- A universe level given to a cited theorem's level parameter. -/
  | level (l : FLevel)
  deriving Inhabited

partial def TProof.atom : TProof → String
  | .lam x T p => s!"(plam {egalVar x} {T.atom} {p.atom})"
  | .hyp h args => s!"(phyp {egalVar h} ({" ".intercalate (args.map TProof.atom)}))"
  | .cite c args => s!"(pcite {c} ({" ".intercalate (args.map TProof.atom)}))"
  | .ctor c args => s!"(pctor {c} ({" ".intercalate (args.map TProof.atom)}))"
  | .recursor r args => s!"(prec {r} ({" ".intercalate (args.map TProof.atom)}))"
  | .quot q args => s!"(pquot {q} ({" ".intercalate (args.map TProof.atom)}))"
  | .proj S i p args => s!"(pproj {S} {i} {p.atom} ({" ".intercalate (args.map TProof.atom)}))"
  | .term t => t.atom
  | .cut P h b => s!"(phave {P.atom} {h.atom} {b.atom})"
  | .level l => s!"(level {l.atom})"

/-- A projection out of a proof (`h.2` of `a ∧ b`): the structure's recursor at a constant
motive, so that the structure's parameters, which the proof's value does not carry, are given. -/
def eliminationOfProof (S : Name) (i : Nat) (struct : Expr) : MetaM (Option Expr) := do
  let structType ← whnf (← inferType struct)
  unless (← isProp structType) do return none
  let .const family us := structType.getAppFn | return none
  unless family == S do return none
  let .inductInfo info ← getConstInfo S | return none
  let [ctor] := info.ctors | return none
  if info.numIndices != 0 then return none
  let params := structType.getAppArgs
  let fieldType ← inferType (mkProj S i struct)
  let motive := mkLambda `h .default structType fieldType
  let ctorType ← inferType (mkAppN (mkConst ctor us) params)
  let minor ← forallTelescope ctorType fun fields _ => do
    if h : i < fields.size then mkLambdaFVars fields fields[i] else throwError "no field {i} in {S}"
  let recInfo ← getConstInfo (mkRecName S)
  let levels := if recInfo.levelParams.length > us.length then Level.zero :: us else us
  return some (mkAppN (mkConst (mkRecName S) levels) (params ++ #[motive, minor, struct]))

/-- Read a proof as Lean records it.  A definition met at the head is read
through its body; `depth` bounds how many in a row. -/
partial def readTransportProof (names : Names) (e : Expr) (depth : Nat := 0)
    (expected : Option Expr := none) : FReadM TProof := do
  -- against a motive at its arguments: each proof among them is what its beta step needs
  if let some t := expected then
    if t.getAppFn.isLambda && t.getAppNumArgs > 0 then
      let mut body ← readTransportProof names e depth (some t.headBeta)
      for a in t.getAppArgs.reverse do
        if ← Meta.isProof a then
          body := .cut (← readTerm names (← inferType a)) (← readTransportProof names a) body
      return body
  let e := (← instantiateMVars e).consumeMData
  if let .letE _ _ value body _ := e then
    return ← readTransportProof names (body.instantiate1 value) depth expected
  if e.isAppOfArity ``letFun 4 then
    return ← readTransportProof names (mkApp (e.getArg! 3) (e.getArg! 2)).headBeta
  if let .lam binderName type body _ := e then
    let typeTerm ← readTerm names type
    return ← Meta.withLocalDeclD binderName type fun x => do
      let name ← readTerm.binderName' names x
      let bodyType := match expected with
        | some (.forallE _ _ b _) => some (b.instantiate1 x)
        | _ => none
      return .lam name typeTerm
        (← readTransportProof (names.insert x.fvarId! name) (body.instantiate1 x) 0 bodyType)
  let argument (a : Expr) (type : Option Expr := none) : FReadM TProof := do
    if ← Meta.isProof a then return ← readTransportProof names a 0 type
    return .term (← readTerm names a)
  -- arguments, each against the type the head gives it
  let arguments (headType : Expr) (given : Array Expr) : FReadM (List TProof) := do
    let mut type := headType
    let mut out := #[]
    for a in given do
      let type' ← if type.isForall then pure type else whnf type
      match type' with
      | .forallE _ d b _ =>
        out := out.push (← argument a (some d))
        type := b.instantiate1 a
      | _ => out := out.push (← argument a)
    return out.toList
  let args := e.getAppArgs
  match e.getAppFn.consumeMData with
  | .fvar id =>
    let some name := names[id]? | throwThe String s!"an unnamed hypothesis: {← ppExpr e}"
    return .hyp name (← args.toList.mapM argument)
  | .lam .. => readTransportProof names e.headBeta depth expected
  | .letE _ _ value body _ => readTransportProof names (mkAppN (body.instantiate1 value) args) depth
  | .proj S i struct =>
    if let some eliminated ← eliminationOfProof S i struct then
      return ← readTransportProof names (mkAppN eliminated args) depth
    return .proj S i (← argument struct) (← args.toList.mapM argument)
  | .const c levels =>
    -- A cited theorem is universe-polymorphic: its level arguments come first, in the order of
    -- its level parameters, as its statement quantifies them.
    let levelArgs : FReadM (List TProof) := levels.mapM fun l => match FLevel.of? l with
      | some v => pure (.level v)
      | none => throwThe String s!"a level with a metavariable in {c}"
    match ← getConstInfo c with
    | .thmInfo t =>
      let own ← arguments (t.type.instantiateLevelParams t.levelParams levels) args
      return .cite c ((← levelArgs) ++ own)
    | .axiomInfo _ =>
      unless c == ``propext || c == ``Quot.sound do
        throwThe String s!"a proof by the axiom {c}"
      return .cite c ((← levelArgs) ++ (← args.toList.mapM argument))
    | .ctorInfo _ => return .ctor c (← args.toList.mapM argument)
    | .recInfo r => return .recursor c (← arguments (r.type.instantiateLevelParams r.levelParams levels) args)
    | .quotInfo _ => return .quot c (← args.toList.mapM argument)
    -- Structural recursion in a proof (`List.brecOn t F`): read as Lean states brecOn's type,
    -- like a recursor, so that F, a proof, is followed rather than erased inside the data
    -- (the `PProd` tower brecOn unfolds to).
    | info@(.defnInfo _) =>
      if isBRecOnRecursor (← getEnv) c then
        return .recursor c (← arguments (info.type.instantiateLevelParams info.levelParams levels) args)
      if depth ≥ 64 then throwThe String s!"64 definitions in a row, at {c}"
      let value ← instantiateValueLevelParams info levels
      readTransportProof names (value.beta args) (depth + 1) expected
    | _ => throwThe String s!"a proof by {c}"
  | _ => throwThe String s!"a proof outside the readable profile: {← ppExpr e}"

/-- The recursors a proof applies. -/
partial def TProof.recursors : TProof → List Name
  | .lam _ _ p => p.recursors
  | .hyp _ args | .cite _ args | .ctor _ args | .quot _ args => args.flatMap TProof.recursors
  | .recursor r args => r :: args.flatMap TProof.recursors
  | .proj _ _ p args => p.recursors ++ args.flatMap TProof.recursors
  | .cut _ h b => h.recursors ++ b.recursors
  | .term _ | .level _ => []

/-- The constants a term names. -/
partial def FTerm.constants : FTerm → List Name
  | .app c args => c :: args.flatMap FTerm.constants
  | .apv f args => f.constants ++ args.flatMap FTerm.constants
  | .lam _ t b => t.constants ++ b.constants
  | .arrow d c => d.constants ++ c.constants
  | .pi _ d c => d.constants ++ c.constants
  | .proofBy t => t.constants
  | .cite _ args => args.flatMap FTerm.constants
  | _ => []

/-- The constants a proof names: its terms, and the constructors, recursors,
structures and primitives of quotients it applies. -/
partial def TProof.constants : TProof → List Name
  | .lam _ T p => T.constants ++ p.constants
  | .hyp _ args | .cite _ args => args.flatMap TProof.constants
  | .ctor c args | .recursor c args | .quot c args => c :: args.flatMap TProof.constants
  | .proj S _ p args => S :: p.constants ++ args.flatMap TProof.constants
  | .term t => t.constants
  | .cut P h b => P.constants ++ h.constants ++ b.constants
  | .level _ => []

def FBinder.constants : FBinder → List Name
  | .term _ T => T.constants
  | .hyp _ P => P.constants
  | _ => []

/-- What the reading must have for the transported theorems: the family of
every inductive type, constructor and recursor they name, and every
definition their statements and terms apply. -/
def transportNeeds (env : Environment) (names : List Name) : NameSet × NameSet :=
  names.foldl (init := ({}, {})) fun (families, functions) n =>
    match env.find? n with
    | some (.inductInfo _) => (families.insert n, functions)
    | some (.ctorInfo c) => (families.insert c.induct, functions)
    | some (.recInfo _) => (families.insert n.getPrefix, functions)
    | some (.defnInfo _) =>
      if isBRecOnRecursor env n || isBelowRecursor env n || isCasesOnRecursor env n then
        (families.insert n.getPrefix, functions)
      else (families, functions.insert n)
    | _ => (families, functions)

def rootLines (file : System.FilePath) : IO NameSet := do
  if !(← file.pathExists) then return {}
  let rows ← IO.FS.lines file
  return rows.foldl (init := {}) fun s row =>
    let r := row.trimAscii.toString
    if r.isEmpty || r.startsWith "#" then s else s.insert (r.splitOn " " |>.getLast!).toName

/-- The theorems a proof cites as it is read: those of the definitions read through
their bodies among them.  A proof inside a term is no citation: its value is 0, and it is
not followed. -/
partial def TProof.cited : TProof → List Name
  | .cite c args => c :: args.flatMap TProof.cited
  | .lam _ _ p => p.cited
  | .hyp _ args | .ctor _ args | .recursor _ args | .quot _ args => args.flatMap TProof.cited
  | .proj _ _ p args => p.cited ++ args.flatMap TProof.cited
  | .cut _ h b => h.cited ++ b.cited
  | .term _ | .level _ => []

/-- The theorems of the closure, each after the theorems its proof cites. -/
partial def transportClosure (roots : List Name) : MetaM (Array Name) := do
  let env ← getEnv
  let mut seen : NameSet := {}
  let mut order : Array Name := #[]
  -- an explicit stack: (theorem, whether its citations are already pushed)
  let mut stack : Array (Name × Bool) := (roots.reverse.map (·, false)).toArray
  while h : stack.size > 0 do
    let (c, expanded) := stack.back
    stack := stack.pop
    if expanded then
      order := order.push c
      continue
    if seen.contains c then continue
    seen := seen.insert c
    match env.find? c with
    | some (.thmInfo t) =>
      stack := stack.push (c, true)
      -- what its proof cites as read; of a proof that is not read, what it names
      let read : MetaM (Except String TProof) :=
        try (readTransportProof {} t.value).run catch _ => pure (.error "not readable")
      let cited := match ← read with
        | .ok proof => proof.cited
        | .error _ => t.value.getUsedConstants.toList
      for d in cited do
        if !seen.contains d then
          if let some (.thmInfo _) := env.find? d then stack := stack.push (d, false)
    | _ => pure ()
  return order

def transportRoots : IO (List Name) := do
  let rows ← IO.FS.lines "artifacts/lean-declarations/transport/lemma-roots.txt"
  return rows.toList.filterMap fun row =>
    if row.isEmpty || row.startsWith "#" then none else some row.toName

def exportTransport : TermElabM (String × String) := do
  let roots ← transportRoots
  let order ← transportClosure roots
  let mut out : Array String := #[]
  -- a root that is not a theorem of the target's environment is refused, with what it is
  let env ← getEnv
  for r in roots do
    match env.find? r with
    | none => out := out.push s!"(TransportRefused {r} {(Json.str "root: not in the target's environment").compress})"
    | some (.thmInfo _) => pure ()
    | some info =>
      let kind := match info with
        | .defnInfo _ => if (env.getProjectionFnInfo? r).isSome then "a structure projection" else "a definition"
        | .axiomInfo _ => "an axiom"
        | .ctorInfo _ => "a constructor"
        | .recInfo _ => "a recursor"
        | .inductInfo _ => "an inductive type"
        | .quotInfo _ => "a primitive of quotients"
        | .opaqueInfo _ => "an opaque constant"
        | .thmInfo _ => "a theorem"
      out := out.push s!"(TransportRefused {r} {(Json.str s!"root: {kind}, not a theorem").compress})"
  let mut recursors : NameSet := {}
  let mut named : List Name := []
  for c in order do
    out := out.push s!"(EgalName {c} {egalIdent c.toString})"
    let info ← getConstInfo c
    match ← (readLemma info.type).run with
    | .ok (binders, statement) =>
      out := out.push s!"(TransportTheorem {c} ({" ".intercalate (binders.map FBinder.atom)}) {statement.atom})"
      out := out.push s!"(TransportLevels {c} ({" ".intercalate (info.levelParams.map (fun u => egalLevel u.toString))}))"
      named := named ++ binders.flatMap FBinder.constants ++ statement.constants
    | .error reason =>
      out := out.push s!"(TransportRefused {c} {(Json.str ("statement: " ++ reason)).compress})"
    if let .thmInfo t := info then
      let attempt : MetaM (Except String TProof) :=
        try (readTransportProof {} t.value).run catch ex => do pure (.error s!"not readable: {← ex.toMessageData.toString}")
      match ← attempt with
      | .ok proof =>
        out := out.push s!"(TransportProof {c} {proof.atom})"
        for r in proof.recursors do recursors := recursors.insert r
        named := named ++ proof.constants
      | .error reason => out := out.push s!"(TransportRefused {c} {(Json.str ("proof: " ++ reason)).compress})"
  -- each recursor a proof applies, under the Egal name of its family's recursor
  for r in recursors.toList do
    out := out.push s!"(EgalName {r} {egalIdent r.toString})"
  -- and each family's below a proof names (F's hypothesis in F.brecOn), under the name the
  -- reading defines it by
  let env ← getEnv
  for n in named.eraseDups do
    if isBelowRecursor env n then out := out.push s!"(EgalName {n} {egalIdent n.toString})"
    -- a case analysis, with its family (as the terms export writes it)
    if isCasesOnRecursor env n then out := out.push s!"(LeanCasesOn {n} {n.getPrefix})"
    -- a recursor, with its family (as the terms export writes it): where it stands in a
    -- term, the reading gives it the parameters, the minor premises and the major
    if let some (.recInfo info) := env.find? n then
      out := out.push s!"(LeanRecursor {n} {info.getMajorInduct})"
      unless recursors.contains n do out := out.push s!"(EgalName {n} {egalIdent n.toString})"
  out := out.push s!"(TransportOrder {" ".intercalate (order.toList.map toString)})"
  -- what the target must read: families and functions the theorems name
  let (families, functions) := transportNeeds (← getEnv) named
  let needs := "# Families and functions the transported theorems name, in their statements and in\n" ++
    "# the terms and constructors of their proofs (written by scripts/ExportLeanTransport.lean).\n" ++
    String.join (families.toList.map (s!"family {·}\n")) ++ String.join (functions.toList.map (s!"function {·}\n"))
  return ("\n".intercalate out.toList ++ "\n", needs)

#eval show TermElabM Unit from do
  -- the target's environment: its module inventory (modules.txt), as the terms export reads it
  discard <| TargetEnvironment.load "artifacts/lean-declarations/transport"
  let (text, needs) ← exportTransport
  let dir := (← IO.getEnv "LEAN_TRANSPORT_OUT").getD "artifacts/lean-declarations/transport"
  IO.FS.createDirAll dir
  IO.FS.writeFile s!"{dir}/proofs.metta" text
  IO.FS.writeFile s!"{dir}/needs.txt" needs
  IO.println s!"wrote {dir}/proofs.metta and {dir}/needs.txt"
  -- the needs the target's roots do not list yet
  let families ← rootLines s!"{dir}/family-roots.txt"
  let functions ← rootLines s!"{dir}/roots.txt"
  for row in needs.splitOn "\n" do
    match row.splitOn " " with
    | ["family", n] => unless families.contains n.toName do IO.println s!"missing family {n}"
    | ["function", n] => unless functions.contains n.toName do IO.println s!"missing function {n}"
    | _ => pure ()
