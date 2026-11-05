import Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRExecutionData
import Mettapedia.Languages.CHR.Examples
import Mettapedia.Languages.MeTTa.PeTTa.SpaceSemantics

/-! Build-time preparation of a dataflow constant folder. The input is
MeTTa data, not CHR concrete syntax. Execution uses the shared MeTTa CHR
controller; the general source/controller correspondence remains open. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

open Mettapedia.Languages.CHR
open Mettapedia.Languages.CHR.Examples
open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.GSLT.LanguageDef.ModuleFormat CHRCompilation

private def program : Program :=
  ⟨[⟨"constant",2⟩,⟨"add",3⟩,⟨"input",1⟩,⟨"seen",1⟩],
   [⟨"same_input", [h "constant" [v 1,v 2]], [h "add" [v 0,v 1,v 1]], [],
      [.assign 3 (op .add (i 2) (i 2)), .tell (h "constant" [v 0,v 3])]⟩,
    ⟨"two_inputs", [h "constant" [v 1,v 3],h "constant" [v 2,v 4]],
      [h "add" [v 0,v 1,v 2]], [.distinct (v 1) (v 2)],
      [.assign 5 (op .add (i 3) (i 4)), .tell (h "constant" [v 0,v 5])]⟩,
    ⟨"note_constant", [h "constant" [v 0,v 1]], [], [], [.tell (h "seen" [v 0])]⟩]⟩

private abbrev HostAtom := Mettapedia.Languages.MeTTa.OSLFCore.Atom

private def seed? : HostAtom → Except String (Option (String × Constraint))
  | .expression [.symbol "Add", .grounded (.string node), .grounded (.string left), .grounded (.string right)] =>
      .ok (some (node, fact "add" [.atom node,.atom left,.atom right]))
  | .expression [.symbol "Constant", .grounded (.string node), .grounded (.int value)] =>
      .ok (some (node, fact "constant" [.atom node,.integer value]))
  | .expression [.symbol "Input", .grounded (.string node)] =>
      .ok (some (node, fact "input" [.atom node]))
  | .expression [.symbol "Output", .grounded (.string _)] => .ok none
  | _ => .error "expected ground Add, Constant, Input or Output data"

private def valueJson : Value → Lean.Json
  | .atom name => .str name
  | .integer value => Lean.toJson value
  | .tuple _ => .null

private def dataJson : HostAtom → Lean.Json
  | .grounded (.string value) => .str value
  | .grounded (.int value) => Lean.toJson value
  | .symbol value => .str value
  | .expression fields => Lean.toJson (fields.map dataJson)
  | _ => .null

private def consText (fields : List String) : String :=
  fields.foldr (fun head tail => "(LCons " ++ head ++ " " ++ tail ++ ")") "LNil"

private def patternText (pattern : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern) : String :=
  CettaWire.Term.render (InferenceCettaWire.encodePattern pattern)

def main (args : List String) : IO Unit := do
  let [source, directory] := args | throw (IO.userError "expected MeTTa data file and output directory")
  let text ← IO.FS.readFile source
  let .ok forms := Mettapedia.Languages.MeTTa.PeTTa.SpaceSemantics.readSource text
    | throw (IO.userError "cannot read MeTTa data")
  let .ok selections := forms.mapM seed? | throw (IO.userError "unsupported dataflow input")
  let seeds := selections.filterMap id
  let constraints := seeds.map Prod.snd
  let .ok prepared := prepare program constraints | throw (IO.userError "CHR preparation refused")
  let .ok emitted := ExecutionData.emitText? prepared constraints "compiler:fold"
    | throw (IO.userError "CHR emission refused")
  let some arguments := ExecutionData.arguments? prepared constraints
    | throw (IO.userError "CHR argument encoding refused")
  let mut entries : List CettaWire.Term := []
  for (node, constraint) in seeds do
    let some goal := ExecutionData.goal? prepared.vocabulary (.tell constraint.asHead)
      | throw (IO.userError "cannot encode a seed")
    entries := entries ++ [.application "CompilerSeed" [.string node, goal]]
  let selected := "(compiler:select-seeds $needed " ++ (encodeList id entries).render ++ ")"
  let begin := "(let $goals " ++ selected ++ " (gslt:chr:begin " ++
    String.intercalate " " ((arguments.take 5).map CettaWire.Term.render) ++ " $goals))"
  let mut decoder := ""
  for (value,index) in prepared.vocabulary.scalars.zipIdx do
    if let .atom name := value then
      decoder := decoder ++ "(= (compiler:scalar " ++ patternText (scalarRef index) ++ ") " ++
        (CettaWire.Term.string name).render ++ ")\n"
  for (name,index) in prepared.vocabulary.predicates.zipIdx do
    let some declaration := program.declarations.find? (·.name == name)
      | throw (IO.userError "missing declaration")
    let fieldVars := (List.range declaration.arity).map (fun index => "$field" ++ toString index)
    let fields := consText fieldVars
    let lhs := "(PApp \"ChrConstraint\" (LCons " ++ patternText (predicateRef index) ++
      " (LCons (PCollection \"Mettapedia.OSLF.MeTTaIL.Syntax.CollType.vec\" " ++ fields ++ " RNone) LNil)))"
    let bindings := String.join (fieldVars.zipIdx.map (fun (field,index) =>
      "($decoded" ++ toString index ++ " (compiler:value " ++ field ++ "))"))
    let rhs := "(let* (" ++ bindings ++ ") (" ++ name ++
      String.join ((List.range declaration.arity).map (fun index => " $decoded" ++ toString index)) ++ "))"
    decoder := decoder ++ "(= (compiler:constraint " ++ lhs ++ ") " ++ rhs ++ ")\n"
  let output := System.FilePath.mk directory
  IO.FS.createDirAll output
  IO.FS.writeFile (output / "prepared.metta") (emitted ++ decoder ++
    "(= (compiler:begin $needed) " ++ begin ++ ")\n")
  IO.FS.writeFile (output / "input.json") (Lean.Json.mkObj [
    ("source", Lean.toJson (forms.map dataJson)),
    ("seeds", Lean.toJson (seeds.map (fun (node,c) => Lean.toJson
      ([Lean.Json.str node, .str c.name] ++ c.arguments.map valueJson)))),
    ("compiledOccurrences", Lean.toJson prepared.entries.length),
    ("scope", .str "Prepared CHR IR and a MeTTa runtime adapter; no general CHR concrete-syntax or controller theorem is claimed")]).pretty
