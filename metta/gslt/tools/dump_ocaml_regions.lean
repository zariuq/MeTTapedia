import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlPreparedControlFlowControls
import Mettapedia.GSLT.LanguageDef.ModuleFormat.Portable
import Mettapedia.GSLT.LanguageDef.ModuleSource.Printer
import Mettapedia.OSLF.MeTTaIL.FreeNameMaps
import Mettapedia.Languages.OCaml.Examples

/-! Readable and lossless inputs for a compiler of prepared O0 term regions.
The rule order, repeated pattern slots and provider requests are retained.
The `.module` view uses escaped identifiers; the portable wire retains the
complete five-field LanguageDef, including optional binding metadata.
-/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

private def identifier (name : String) : String := "«" ++ name ++ "»"

private def displayPattern (pattern : Pattern) : Pattern :=
  Substitution.mapFVars identifier pattern

private def displayPremise : Premise → Premise
  | .freshness condition => .freshness
      { condition with varName := identifier condition.varName, term := displayPattern condition.term }
  | .congruence left right => .congruence (displayPattern left) (displayPattern right)
  | .scopedStep step => .scopedStep
      { step with source := displayPattern step.source, target := displayPattern step.target }
  | .relationQuery relation arguments => .relationQuery relation (arguments.map displayPattern)
  | .forAll collection parameter body =>
      .forAll (identifier collection) (identifier parameter) (displayPremise body)

private def readableRule (row : RewriteRule) : String :=
  ModuleSource.Printer.rewrite { row with
    name := if row.typeContext.isEmpty then identifier row.name else row.name
    typeContext := row.typeContext.map fun (name, sort) => (identifier name, sort)
    premises := row.premises.map displayPremise
    left := displayPattern row.left
    right := displayPattern row.right }

private def moduleText (label : String) (language : LanguageDef) : String :=
  "Module " ++ label ++ " {\n  Theory Core() {\n    Types {\n" ++
  String.intercalate "\n" (language.types.map fun row => "      " ++ ModuleSource.Printer.typeRow row) ++
  "\n    }\n    Terms {\n" ++
  String.intercalate "\n" (language.terms.map fun row => "      " ++ ModuleSource.Printer.rule row) ++
  "\n    }\n    Rewrites {\n" ++
  String.intercalate "\n" (language.rewrites.map fun row => "      " ++ readableRule row) ++
  "\n    }\n  }\n  theory Core()\n}\n"

private def writeProgram (directory : System.FilePath) (label : String) (program : OCaml.Program) : IO Unit := do
  let .ok prepared := prepare program | throw (IO.userError "O0 preparation refused")
  let language := prepared.compiled
  unless language.equations.isEmpty && language.rewrites.all (·.bindings.isNone) do
    throw (IO.userError "readable module view requires equation-free rows without explicit binding metadata")
  let .ok functions := functionBatches? program prepared.patternPool
    | throw (IO.userError "function compilation refused")
  IO.FS.createDirAll (directory / label)
  let output := directory / label
  IO.FS.writeFile (output / (label ++ ".module")) (moduleText label language)
  let wire := ModuleAlgebra.NativeAuthoring.Wire.language language
  unless (ModuleAlgebra.NativeAuthoring.Wire.language? wire).isSome do
    throw (IO.userError "language wire did not decode")
  IO.FS.writeFile (output / "language.sexp") (ModuleFormat.Text.render wire ++ "\n")
  IO.FS.writeFile (output / "source.txt") (reprStr program ++ "\n")
  IO.FS.writeFile (output / "initial.sexp") ((CettaWire.Term.render (InferenceCettaWire.encodePattern (initial program))) ++ "\n")
  IO.FS.writeFile (output / "patterns.txt") (String.intercalate "\n"
    (prepared.patternPool.zipIdx.map fun (pattern, index) => s!"{index}: {reprStr pattern}") ++ "\n")
  IO.FS.writeFile (output / "rules.txt") (String.intercalate "\n\n"
    (language.rewrites.zipIdx.map fun (row, index) => s!"[{index}] {readableRule row}\nbindings: {reprStr row.bindings}") ++ "\n")
  let summary := s!"{label}: instructions={program.code.size}, base-rules={baseLanguage.rewrites.length}, " ++
    s!"function-rules={functions.flatten.length}, pattern-slots={prepared.patternPool.length}, " ++
    s!"pattern-rules={2 * prepared.patternPool.length}, total-rules={language.rewrites.length}, " ++
    s!"sorts={language.types.length}, constructors={language.terms.length}, entry={program.entry}"
  IO.FS.writeFile (output / "summary.txt") (summary ++ "\n")
  IO.println summary

def main (arguments : List String) : IO Unit := do
  let [directory] := arguments | throw (IO.userError "expected output directory")
  writeProgram directory "O0Recursion" OCaml.Examples.recursion
  writeProgram directory "O0Capture" ControlFlowControls.captureProgram
