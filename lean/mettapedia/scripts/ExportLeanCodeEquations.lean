import Mathlib
import Mettapedia.Languages.Lean.CodeEquations.Erase
import Mettapedia.Languages.Lean.CodeEquations.Value
import Mettapedia.Languages.Lean.CodeEquations.FunctionalCorrespondenceValues
import Mettapedia.Languages.Lean.Declarations.Manifest

/-!
Export a slice of Lean and Mathlib as PeTTa code equations, with the tests
that compare a PeTTa run against Lean's own evaluation.

Run from the project root:
`lake env lean scripts/ExportLeanCodeEquations.lean`
writes `artifacts/lean-code-equations/core/`:
- `rules.metta`: one first-match rule per function;
- `tests.metta`: one collapsed query per test;
- `expected.txt`: Lean's compiled evaluation of each test, as a one-answer collapse;
- `tests.tsv`: each test's Lean source, its value in Lean syntax and in PeTTa syntax;
- `Controls.lean`: each test's `t = V` as a theorem for Lean's kernel, with its axioms printed;
- `receipts.tsv`: each rule's source theorem, its kind, its statement digest and its axioms;
- `refusals.tsv`: constants that cannot run, with the reason, and the refusal controls.

`LEAN_CODE_EQUATIONS_TESTS` selects a file with one closed source term per
line; `LEAN_CODE_EQUATIONS_ROOTS` adds explicit executable declaration roots.
`LEAN_CODE_EQUATIONS_OUT` selects the output directory. The control module
imports, namespace and proof mode may be selected with the corresponding
`_IMPORTS`, `_NAMESPACE` and `_PROOF` variables. Defaults retain the original
slice. `LEAN_CODE_EQUATIONS_CHECK=1` compares in memory without changing files.
The `equations` proof mode simplifies with the comma-separated declarations
in `LEAN_CODE_EQUATIONS_EQUATIONS`; their names must exist in the environment.
-/

open Lean Meta Elab Term
open Mettapedia.Languages.Lean.CodeEquations

/-- Closed test terms; each type has a `PeTTaValue` instance. -/
def testSources : List String := [
  "List.map (fun x => x + 1) [1, 2, 3]",
  "List.foldl (fun a b => a + b) 0 [1, 2, 3, 4]",
  "List.foldr (fun a b => a :: a :: b) [] [1, 2]",
  "List.reverse [1, 2, 3, 4]",
  "[1, 2] ++ [3, 4]",
  "List.length [5, 6, 7]",
  "List.filter (fun x => x % 2 == 0) (List.range 10)",
  "List.zip [1, 2, 3] [true, false, true]",
  "List.sum [1, 2, 3, 4, 5]",
  "List.mergeSort [5, 3, 8, 1, 9, 2, 7] (fun a b => decide (a ≤ b))",
  "List.max? [3, 7, 2]",
  "Option.map (fun x => x * 2) (some 21)",
  "Option.bind (some 3) (fun x => if x > 2 then some (x + 1) else none)",
  "(none : Option Nat).getD 7",
  "Nat.gcd 1071 462",
  "Nat.lcm 4 6",
  "compare 3 5",
  "2 ^ 100",
  "123456789012345678901234567890 / 7",
  "123456789012345678901234567890 % 7",
  "10 - 25",
  "7 / 0",
  "Nat.factorial 20",
  "Nat.choose 20 10",
  "Nat.fib 50",
  "Nat.primeFactorsList 360",
  "decide (Nat.Prime 97)",
  "decide (Nat.Prime 91)",
  "(Finset.range 11).sum id",
  "(Finset.filter (fun x => x % 3 = 0) (Finset.range 20)).card"
]

/-- The kernel proof of a test's control `t = V`, where `decide` does not
reach: a well-founded sort and a factorization go through their lemmas. -/
def controlProof (src : String) : String :=
  if src == "List.mergeSort [5, 3, 8, 1, 9, 2, 7] (fun a b => decide (a ≤ b))" then
    "  have hperm : List.Perm (List.mergeSort [5, 3, 8, 1, 9, 2, 7] (fun a b : ℕ => decide (a ≤ b)))\n" ++
    "      [1, 2, 3, 5, 7, 8, 9] :=\n" ++
    "    (List.mergeSort_perm _ _).trans (by decide)\n" ++
    "  have hsorted : (List.mergeSort [5, 3, 8, 1, 9, 2, 7]\n" ++
    "      (fun a b : ℕ => decide (a ≤ b))).Pairwise (· ≤ ·) :=\n" ++
    "    (List.pairwise_mergeSort (le := fun a b : ℕ => decide (a ≤ b))\n" ++
    "      (fun a b c hab hbc => by simp only [decide_eq_true_eq] at *; omega)\n" ++
    "      (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega)\n" ++
    "      [5, 3, 8, 1, 9, 2, 7]).imp (fun h => by simpa using h)\n" ++
    "  exact List.Perm.eq_of_pairwise' hsorted (by decide) hperm\n"
  else if src == "Nat.primeFactorsList 360" then
    "  simp only [Nat.primeFactorsList_ofNat]\n"
  else
    "  decide\n"

/-- Roots that must be refused, with the reason checked by the export. -/
def refusalSources : List (String × Name) := [
  ("fun (x : ℝ) => x⁻¹", ``Classical.choice),
  ("fun (n : ℕ) => Classical.choose (⟨n, rfl⟩ : ∃ m, m = n)", ``Classical.choice)
]

def elabClosed (src : String) : TermElabM Expr := do
  let stx ← match Parser.runParserCategory (← getEnv) `term src with
    | .ok s => pure s
    | .error e => throwError "parse error in {src}: {e}"
  let e ← elabTerm stx none
  synthesizeSyntheticMVarsNoPostponing
  instantiateMVars e

unsafe def expectedOf (e : Expr) : TermElabM String := do
  let r ← mkAppM ``PeTTaValue.render #[e]
  evalExpr String (mkConst ``String) r

/-- The value in Lean syntax, for the kernel-checked control `t = V`. -/
unsafe def leanValueOf (e : Expr) : TermElabM String := do
  let r ← mkAppM ``reprStr #[e]
  evalExpr String (mkConst ``String) r

/-- Export the closure of what the tests need, starting from their erased terms. -/
def runExport (tests : List Expr) (roots : List Name := []) :
    MetaM (List ETerm × Array EFunction × Array (Name × String)) := do
  let go : EraseM (List ETerm × Array EFunction) := do
    let erased ← tests.mapM erase
    for root in roots do noteConst root
    let mut done : NameSet := {}
    let mut out : Array EFunction := #[]
    let mut i := 0
    while i < (← get).needed.size do
      let c := (← get).needed[i]!
      i := i + 1
      if done.contains c then continue
      done := done.insert c
      try
        if let some f ← codeOf c then out := out.push f
      catch err =>
        let msg ← err.toMessageData.toString
        modify fun s => { s with refusals := s.refusals.push (c, msg) }
    return (erased, out)
  let ((erased, fns), st) ← go.run {}
  return (erased, fns, st.refusals)

def kindOf (f : EFunction) (thm : Name) : MetaM String := do
  if (← getProjectionFnInfo? f.name).isSome then return "projection"
  if thm == f.name then return "delta"
  if ← isMatcher f.name then return "matcher-equation"
  return "equation"

def axiomsOf (thm : Name) : MetaM String := do
  if (← getEnv).find? thm |>.any (fun | .thmInfo _ => true | _ => false) then
    let axs ← collectAxioms thm
    return ",".intercalate (axs.toList.map toString)
  return "-"

def artifactFiles : List String :=
  ["rules.metta", "tests.metta", "expected.txt", "tests.tsv", "Controls.lean",
   "receipts.tsv", "refusals.tsv"]

unsafe def exportSlice : TermElabM Unit := do
  let testSources ← match ← IO.getEnv "LEAN_CODE_EQUATIONS_TESTS" with
    | none => pure testSources
    | some file =>
        pure ((← IO.FS.lines file).toList.map (·.trimAscii.toString) |>.filter
          (fun line => !line.isEmpty && !line.startsWith "#"))
  let roots ← match ← IO.getEnv "LEAN_CODE_EQUATIONS_ROOTS" with
    | none => pure []
    | some file =>
        match Mettapedia.Languages.Lean.Declarations.Manifest.resolveRoots (← getEnv) (← IO.FS.readFile file) with
        | .ok roots => pure roots.toList
        | .error reason => throwError reason
  let out : System.FilePath := (← IO.getEnv "LEAN_CODE_EQUATIONS_OUT").getD "artifacts/lean-code-equations/core"
  let checking := (← IO.getEnv "LEAN_CODE_EQUATIONS_CHECK") == some "1"
  let proofMode := (← IO.getEnv "LEAN_CODE_EQUATIONS_PROOF").getD "slice"
  unless ["slice", "rfl", "equations"].contains proofMode do
    throwError "unknown code-equation control proof mode: {proofMode}"
  let equationNames := ((← IO.getEnv "LEAN_CODE_EQUATIONS_EQUATIONS").getD "").splitOn "," |>.map
    (fun name => name.trimAscii.toString) |>.filter (!·.isEmpty)
  if proofMode == "equations" then
    if equationNames.isEmpty then throwError "equations proof mode needs named declarations"
    for name in equationNames do
      unless (← getEnv).contains name.toName do throwError "unknown equation declaration: {name}"
  let controlNamespace := (← IO.getEnv "LEAN_CODE_EQUATIONS_NAMESPACE").getD "LeanCodeEquationsControls"
  let imports := (← IO.getEnv "LEAN_CODE_EQUATIONS_IMPORTS").getD "Mathlib"
  if !checking then IO.FS.createDirAll out
  let writeArtifact := fun (file text : String) => (do
    if checking then
      let previous ← try IO.FS.readFile (out / file) catch _ => pure ""
      unless previous == text do throwError "fresh code-equation export differs: {file}"
    else IO.FS.writeFile (out / file) text : TermElabM Unit)
  let mut exprs : Array Expr := #[]
  let mut expected : Array String := #[]
  let mut controls : Array String := #[]
  let mut testRows : Array String := #["index\tlean_source\tlean_value\tpetta_value"]
  for src in testSources do
    let e ← elabClosed src
    exprs := exprs.push e
    expected := expected.push ("(" ++ (← expectedOf e) ++ ")")
    let i := controls.size + 1
    let name := if i < 10 then s!"test_0{i}" else s!"test_{i}"
    let leanValue := (← leanValueOf e).replace "\n" " " |>.replace "\t" " "
    let proof := if proofMode == "rfl" then "  rfl\n"
      else if proofMode == "equations" then
        s!"  simp +decide only [{", ".intercalate equationNames}]\n"
      else controlProof src
    controls := controls.push
      s!"theorem {name} : ({src}) = {leanValue} := by\n{proof}"
    testRows := testRows.push s!"{i}\t{src}\t{leanValue}\t{expected.back!}"
  let (erased, fns, refusals) ← runExport exprs.toList roots
  -- Names must not collide as symbols.
  let symbols := fns.toList.map (encodeName ·.name)
  if symbols.eraseDups.length != symbols.length then
    throwError "two exported functions share a PeTTa symbol"
  let header := ";; Generated by scripts/ExportLeanCodeEquations.lean from Lean's equation theorems.\n"
  let rules := fns.toList.map EFunction.render
  -- A refused constant has no answer: a run that reaches it answers nothing,
  -- never a value of an unrelated branch.
  let mut refusedRules : Array String := #[]
  for (c, _) in refusals do
    if (← getEnv).contains c then
      let arity := (← keptParams c).toList.count true
      let params := (List.range arity).map (fun i => s!"$lean_a{i}")
      let head := if arity == 0 then "(" ++ encodeName c ++ ")"
        else "(" ++ " ".intercalate (encodeName c :: params) ++ ")"
      refusedRules := refusedRules.push s!"(= {head} (empty))"
  writeArtifact "rules.metta" (header ++ "\n".intercalate (rules ++ refusedRules.toList) ++ "\n")
  let tests := erased.map fun t => "!(collapse " ++ t.render ++ ")"
  writeArtifact "tests.metta" (header ++ "\n".intercalate tests ++ "\n")
  writeArtifact "expected.txt" ("\n".intercalate expected.toList ++ "\n")
  -- Each test's value as a theorem the kernel checks.
  let controlsHeader := "import " ++ imports ++ "\n\n/-! Generated by scripts/ExportLeanCodeEquations.lean: each test term equals\nthe value its PeTTa run must answer, checked by Lean's kernel. -/\n\nnamespace " ++ controlNamespace ++ "\n\n"
  let axiomLines := (List.range controls.size).map fun k =>
    let i := k + 1
    if i < 10 then s!"#print axioms {controlNamespace}.test_0{i}"
    else s!"#print axioms {controlNamespace}.test_{i}"
  writeArtifact "Controls.lean"
    (controlsHeader ++ "\n".intercalate controls.toList ++ "\nend " ++ controlNamespace ++ "\n\n" ++
      "\n".intercalate axiomLines ++ "\n")
  writeArtifact "tests.tsv" ("\n".intercalate testRows.toList ++ "\n")
  let mut receipts : Array String := #["function\ttheorem\tkind\tstatement_digest\taxioms"]
  for f in fns do
    for b in f.branches do
      let digest := match (← getEnv).find? b.theorem_ with
        | some info => toString info.type.hash
        | none => "-"
      receipts := receipts.push
        s!"{f.name}\t{b.theorem_}\t{← kindOf f b.theorem_}\t{digest}\t{← axiomsOf b.theorem_}"
  writeArtifact "receipts.tsv" ("\n".intercalate receipts.toList ++ "\n")
  -- The negative controls: roots that must not run.
  let mut refusalRows : Array String := #["constant\treason"]
  for (c, r) in refusals do refusalRows := refusalRows.push s!"{c}\t{r}"
  for (src, root) in refusalSources do
    let e ← elabClosed src
    let (_, _, rs) ← runExport [e]
    unless rs.any (fun (c, _) => c == root) do
      throwError "expected {src} to reach the refused {root}, got {rs.toList}"
    refusalRows := refusalRows.push s!"control:{src}\treaches {root}"
  writeArtifact "refusals.tsv" ("\n".intercalate refusalRows.toList ++ "\n")
  IO.println s!"exported {fns.size} functions, {testSources.length} tests, {refusals.size} refusals"
  if checking then
    IO.println "check: the committed export equals a fresh export"

#eval exportSlice
