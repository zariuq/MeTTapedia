import Mettapedia.GSLT.LanguageDef.ModuleFormat.GoldOSLFControls
import Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangMailboxControls
import Mettapedia.OSLF.NativeTypes.Product.Query
import Mettapedia.OSLF.NativeTypes.Product.Export

/-! File-based OSLF questions about the same operational IRs used by the
shared MeTTa gate. Expected targets come from the independent language
examples. The executable chooses its declared reading; agreement here is
a finite differential check, not a general core-lowering theorem. -/

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.OSLF.NativeTypes GeneratedLogic
open Mettapedia.GSLT.LanguageDef.ModuleFormat

def rows (file : String) (source target wrong : Pattern) : List String :=
  let row := fun (formula : Formula 0) (term : Pattern) (budget : Nat) (expected : String) =>
    s!"{file} | {Product.formulaText formula} | {Product.patternText term} | {budget} | {expected} | fuel=2 hints=0\n"
  [row (GoldOSLF.reaches target) source 32 "established",
   row (GoldOSLF.reaches wrong) source 32 "refuted",
   row (.necessarily .any .bot) target 4 "established",
   row (.possibly .any .top) target 4 "refuted"]

def readingRecord (file : String) (language : LanguageDef) : Lean.Json :=
  Lean.Json.mkObj [
    ("file", .str file), ("compilerLanguage", .str language.name),
    ("readingChangesLanguage", .bool ((Product.readingOf (.ok language)).toOption != some language)),
    ("generalCoreAdequacy", .bool false)]

abbrev Graph := List (Pattern × List Pattern)

def discover (language : LanguageDef) : Nat → List Pattern → Graph → Except String Graph
  | 0, _ :: _, _ => .error "finite graph discovery exhausted its budget"
  | _, [], graph => .ok graph
  | fuel + 1, source :: rest, graph =>
      if graph.any (·.1 == source) then discover language fuel rest graph
      else
        let successors := (ContextualStep.reducts language 2 source).eraseDups
        discover language fuel (rest ++ successors) (graph ++ [(source, successors)])

def successorFormula (states : List Pattern) : Formula 0 :=
  states.foldr (fun state rest => .or (.is state) rest) .bot

def graphRows (file : String) (language : LanguageDef) (source target wrong : Pattern) :
    Except String (List String × Lean.Json) := do
  let graph ← discover language 256 [source] []
  unless graph.any (·.1 == target) && !(graph.any (·.1 == wrong)) do
    throw "reference graph disagrees with the independent result fixture"
  let leaves := graph.filterMap fun (state, next) => if next.isEmpty then some state else none
  unless leaves == [target] do throw "reference graph has another terminal outcome"
  let row := fun (formula : Formula 0) (term : Pattern) (expected : String) =>
    s!"{file} | {Product.formulaText formula} | {Product.patternText term} | 1 | {expected} | fuel=2 hints=0\n"
  let questions := graph.flatMap fun (state, successors) =>
    [row (.necessarily .any (successorFormula successors)) state "established",
     row (.possibly .any (.is wrong)) state "refuted"] ++
      successors.map (fun next => row (.possibly .any (.is next)) state "established") ++
      (if successors.isEmpty then [row (.possibly .any .top) state "refuted"] else [])
  pure (questions, Lean.Json.mkObj [
    ("file", .str file), ("source", .str (Product.patternText source)),
    ("target", .str (Product.patternText target)), ("wrong", .str (Product.patternText wrong)),
    ("nodes", .arr (graph.map fun (state, successors) => Lean.Json.mkObj [
      ("state", .str (Product.patternText state)),
      ("successors", .arr (successors.map (fun next => .str (Product.patternText next))).toArray)]).toArray),
    ("closed", .bool true), ("questions", Lean.toJson questions.length)])

def main (arguments : List String) : IO Unit := do
  let [directory, moduleDirectory] := arguments
    | throw (IO.userError "expected output and authored-module directories")
  let output := System.FilePath.mk directory
  IO.FS.createDirAll output
  let mailboxFile := "ErlangMailbox.module"
  for file in ["Radix16.module", "ErlangData.module", mailboxFile] do
    IO.FS.writeFile (output / file) (← IO.FS.readFile ((System.FilePath.mk moduleDirectory) / file))
  let mut questions : List String := []
  let mut globalQuestions : List String := []
  let mut graphs : List Lean.Json := []
  let mut manifest := [readingRecord mailboxFile ErlangMailbox.language]
  for sample in ErlangMailbox.Controls.examples do
    let .ok (localRows, graph) := graphRows mailboxFile ErlangMailbox.language sample.source sample.expected sample.wrong
      | throw (IO.userError s!"mailbox graph qualification failed: {sample.name}")
    questions := questions ++ localRows
    graphs := graphs ++ [graph]
    globalQuestions := globalQuestions ++ rows mailboxFile sample.source sample.expected sample.wrong
  for sample in Mettapedia.Languages.OCaml.Examples.structuralExamples do
    let .ok prepared := OCamlCompilation.prepare sample.program
      | throw (IO.userError s!"OCaml preparation failed: {sample.name}")
    let .ok expected := sample.expected | throw (IO.userError "expected an OCaml value fixture")
    let file := s!"OCaml-{sample.name}.module"
    IO.FS.writeFile (output / file) (Product.moduleText prepared.compiled)
    let source := OCamlCompilation.initial sample.program
    let target := OCamlCompilation.node "MlDone" [OCamlCompilation.value expected]
    let wrong := OCamlCompilation.node "MlDone" [OCamlCompilation.literal (.integer 123456)]
    let .ok (localRows, graph) := graphRows file prepared.compiled source target wrong
      | throw (IO.userError s!"OCaml graph qualification failed: {sample.name}")
    questions := questions ++ localRows
    graphs := graphs ++ [graph]
    globalQuestions := globalQuestions ++ rows file source
      (OCamlCompilation.node "MlDone" [OCamlCompilation.value expected])
      (OCamlCompilation.node "MlDone" [OCamlCompilation.literal (.integer 123456)])
    manifest := manifest ++ [readingRecord file prepared.compiled]
  let some sample := ErlangMailbox.Controls.examples.head?
    | throw (IO.userError "mailbox fixture set is empty")
  questions := questions ++ [s!"{mailboxFile} | {Product.formulaText (GoldOSLF.reaches sample.expected)} | " ++
    s!"{Product.patternText sample.source} | 0 | suspended | fuel=2 hints=0\n"]
  IO.FS.writeFile (output / "matrix.txt")
    ("# Operational compiler inputs; expected targets from source-model fixtures.\n" ++ String.join questions)
  IO.FS.writeFile (output / "global-matrix.txt")
    ("# Retained global queries; not part of the bounded local-check gate.\n" ++ String.join globalQuestions)
  IO.FS.writeFile (output / "graphs.json") (Lean.Json.arr graphs.toArray).pretty
  IO.FS.writeFile (output / "manifest.json") (Lean.Json.mkObj [
    ("rows", Lean.toJson questions.length), ("languages", .arr manifest.toArray),
    ("mailboxPrograms", Lean.toJson ErlangMailbox.Controls.examples.length),
    ("ocamlPrograms", Lean.toJson Mettapedia.Languages.OCaml.Examples.structuralExamples.length),
    ("scope", .str "file-based edges, complete successor sets, terminality and budget suspension for closed fixture graphs"),
    ("globalSearchRowsQualified", .bool false),
    ("universalCompilerAdequacy", .bool false)]).pretty
  IO.println s!"emitted {questions.length} executable OSLF questions"
