import Mettapedia.Languages.VibeITP.Presentation.SimultaneousPresentationControls
import Mettapedia.GSLT.LanguageDef.InferenceCettaWireFormat
import Mettapedia.GSLT.LanguageDef.FirstOrderCertificateData
import Lean.Data.Json.Parser
import Lean.Data.Json.Printer

/-! Untrusted interchange adapter and calibration exporter. Candidate articles
are checked against the selected validated presentation and independently
specified source results. This adapter does not certify the native runtime. -/

open Lean (Json toJson)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.FirstOrderRules
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.Languages.VibeITP
open Presentation Presentation.SimultaneousPresentation
open Mettapedia.GSLT.LanguageDef.FirstOrderCertificateData

def ruleJson (rule : FORule) : Except String Json := do
  return Json.mkObj [("id", .str rule.id), ("vars", toJson rule.vars),
    ("premises", .arr (← rule.premises.toArray.mapM patternJson)),
    ("conclusion", ← patternJson rule.conclusion)]

structure Case where
  name : String
  replacements : List (Spec.SymId × Spec.Term)
  expected : Spec.Term

def resultWith (left right : Spec.Term) : Spec.Term :=
  .eq (.app Controls.D [left, right]) (.eq left right)

def cases : List Case := [
  ⟨"crossing", Controls.replacements, Controls.crossing⟩,
  ⟨"swap", [(Controls.F, Controls.g), (Controls.G, Controls.f)], resultWith Controls.g Controls.f⟩,
  ⟨"reverse-target-order", [(Controls.G, Controls.f), (Controls.F, Controls.g)], resultWith Controls.g Controls.f⟩,
  ⟨"duplicate-first", [(Controls.F, Controls.g), (Controls.F, .natLit 7)], resultWith Controls.g Controls.g⟩,
  ⟨"only-first", [(Controls.F, Controls.g)], resultWith Controls.g Controls.g⟩,
  ⟨"only-second", [(Controls.G, Controls.f)], resultWith Controls.f Controls.f⟩,
  ⟨"zero-copy", [], Controls.source⟩]

def nodeSeed (rule : FORule) (arguments : List Pattern) (children : List Json) : Except String Json := do
  return Json.mkObj [("rule", .str rule.id), ("arguments", .arr (← arguments.toArray.mapM patternJson)),
    ("children", .arr children.toArray)]

def caseJson (entry : Case) : Except String Json := do
  unless Spec.SimultaneousInstantiation.statement Controls.theory.sig entry.replacements Controls.source =
      some entry.expected do throw s!"independent result disagreement: {entry.name}"
  let some prepared := Spec.SimultaneousInstantiation.prepare Controls.theory.sig entry.replacements |
    throw "preparation failed"
  let leaf := Json.mkObj [("rule", .str (definitionRuleId 1)),
    ("arguments", .arr #[]), ("children", .arr #[])]
  let seed ← match entry.replacements, prepared with
    | [], [] => nodeSeed rInstantiateManyNil [encTerm Controls.theory.sig Controls.source] [leaf, .null]
    | first :: rest, head :: tail =>
      nodeSeed rInstantiateManyCons
        [encReplacement Controls.theory.sig first, encReplacements Controls.theory.sig rest,
         encEntry Controls.theory.sig head, encEntries Controls.theory.sig tail,
         encTerm Controls.theory.sig Controls.source, encTerm Controls.theory.sig entry.expected]
        [leaf, .null, .null, .null]
    | _, _ => .error "preparation length mismatch"
  return Json.mkObj [("name", .str entry.name),
    ("goal", ← patternJson (jThm (encTerm Controls.theory.sig entry.expected))), ("seed", seed)]

def bindingSource : Spec.Term := KernelControls.underBinder (.app KernelControls.parameter [.bvar 0])
def bindingValue : Spec.Term := .eq (.bvar 0) (.natLit 4)
def bindingEntries : List Spec.SimultaneousInstantiation.Entry := [⟨KernelControls.parameter, 1, bindingValue⟩]
def bindingResult : Spec.Term := KernelControls.underBinder (.eq (.bvar 0) (.natLit 4))

def bindingGoals : List (String × Pattern) :=
  let sig := KernelControls.controlTheory.sig
  [("under-binder", jMany (encEntries sig bindingEntries) (encNat 0)
      (encTerm sig bindingSource) (encTerm sig bindingResult)),
   ("closed-copy", jMany (encEntries sig bindingEntries) (encNat 0)
      (encTerm sig (.lit [])) (encTerm sig (.lit [])))]

def bindingInput : Except String Json := do
  unless Spec.SimultaneousInstantiation.go KernelControls.controlTheory.sig bindingEntries 0 bindingSource =
      some bindingResult do throw "independent binding result disagreement"
  let rules := rulesV2 ++ theoryRules KernelControls.controlTheory 4
  return Json.mkObj [("rules", .arr (← rules.toArray.mapM ruleJson)),
    ("requests", .arr (← bindingGoals.toArray.mapM fun (name, goal) => do
      return Json.mkObj [("name", .str name), ("goal", ← patternJson goal)]))]

partial def nodeCount : RawProof → Nat
  | .node _ children => 1 + (children.map nodeCount).sum

partial def renameFirstRule (before after : String) : RawProof → Option RawProof
  | .node application children =>
      if application.ruleId.value = before then some (.node { application with ruleId := ⟨after⟩ } children)
      else visit application children []
  where
    visit (application : RuleInstance) : List RawProof → List RawProof → Option RawProof
      | [], _ => none
      | child :: rest, earlier =>
          match renameFirstRule before after child with
          | some changed => some (.node application (earlier.reverse ++ changed :: rest))
          | none => visit application rest (child :: earlier)

def mutations (article : RawProof) : List (String × Pattern × RawProof) :=
  let goal := jThm (encTerm Controls.theory.sig Controls.crossing)
  let wrong := jThm (encTerm Controls.theory.sig Controls.sequential)
  match article with
  | .node application children =>
      [("wrong-goal", wrong, article),
       ("missing-argument", goal, .node { application with arguments := application.arguments.drop 1 } children),
       ("swapped-premises", goal, .node application children.reverse),
       ("missing-validation", goal, .node application (children.take 1 ++ children.drop 2)),
       ("free-meta-argument", goal, .node { application with arguments := .fvar "untrusted" :: application.arguments.drop 1 } children),
       ("sequential-collapse", wrong, .node { application with
          arguments := application.arguments.take 5 ++ [encTerm Controls.theory.sig Controls.sequential] } children)] ++
      [("changed-source-definition", definitionRuleId 1, definitionRuleId 99),
       ("wrong-hit-order", rManyHitLt.id, rManyHitGt.id),
       ("unknown-traversal-rule", rManySelected.id, "unknown-traversal")].filterMap
        (fun (name, before, after) => (renameFirstRule before after article).map (name, goal, ·))

def exportInputs (directory : System.FilePath) : IO Unit := do
  IO.FS.createDirAll directory
  let rules := rulesV2 ++ theoryRules Controls.theory Controls.allocated
  let input ← unwrap do
    return Json.mkObj [("rules", .arr (← rules.toArray.mapM ruleJson)),
      ("requests", .arr (← cases.toArray.mapM caseJson))]
  IO.FS.writeFile (directory / "inputs.json") (input.compress ++ "\n")
  IO.FS.writeFile (directory / "VibeITPV2.module")
    (ModuleFormat.Portable.renderCalculus fixedDefinitionV2 ++ "\n")
  IO.FS.writeFile (directory / "definition-theory.module")
    (CheckingMachineV2.kernelModule Controls.theory Controls.allocated ++ "\n")
  IO.FS.writeFile (directory / "language.sexp")
    (CettaWire.Term.render (InferenceCettaWire.encodeDefinition (definitionV2 Controls.theory Controls.allocated)) ++ "\n")

def checkArticles (file directory : System.FilePath) (binding : Bool := false) : IO Unit := do
  let input ← unwrap (Json.parse (← IO.FS.readFile file))
  let rows ← unwrap do (← input.getObjVal? "results").getArr?
  let requests := if binding then bindingGoals else
    cases.map fun entry => (entry.name, jThm (encTerm Controls.theory.sig entry.expected))
  unless rows.size = requests.length do throw (IO.userError "candidate count mismatch")
  let definition := if binding then validatedV2 KernelControls.controlTheory 4 else
    validatedV2 Controls.theory Controls.allocated
  let mut reports := #[]
  for ((expectedName, goal), row) in requests.zip rows.toList do
    let name ← unwrap do (← row.getObjVal? "name").getStr?
    let status ← unwrap do (← row.getObjVal? "status").getStr?
    unless name = expectedName ∧ status = "candidate" do throw (IO.userError "candidate identity/status mismatch")
    let suppliedGoal ← unwrap do pattern (← row.getObjVal? "goal")
    unless suppliedGoal = goal do throw (IO.userError "changed source goal")
    let article ← unwrap do FirstOrderCertificateData.article (← row.getObjVal? "article")
    unless checkRaw definition goal article do throw (IO.userError s!"certificate refused: {name}")
    IO.FS.writeFile (directory / s!"{name}.goal.sexp") (CettaWire.Term.render (InferenceCettaWire.encodePattern goal) ++ "\n")
    IO.FS.writeFile (directory / s!"{name}.proof.sexp") (CettaWire.Term.render (InferenceCettaWire.encodeRawProof article) ++ "\n")
    reports := reports.push (Json.mkObj [("name", .str name), ("accepted", .bool true),
      ("nodes", toJson (nodeCount article))])
    if name = "crossing" then
      let controls := mutations article
      unless controls.length = 9 do throw (IO.userError "missing mutation target")
      for (label, negativeGoal, changed) in controls do
        if checkRaw definition negativeGoal changed then
          throw (IO.userError s!"mutation accepted: {label}")
        IO.FS.writeFile (directory / s!"{label}.goal.sexp")
          (CettaWire.Term.render (InferenceCettaWire.encodePattern negativeGoal) ++ "\n")
        IO.FS.writeFile (directory / s!"{label}.proof.sexp")
          (CettaWire.Term.render (InferenceCettaWire.encodeRawProof changed) ++ "\n")
        reports := reports.push (Json.mkObj [("name", .str label), ("accepted", .bool false),
          ("nodes", toJson (nodeCount changed))])
  IO.FS.writeFile (directory / "checked.json") ((Json.mkObj [("cases", .arr reports)]).pretty ++ "\n")

def main (arguments : List String) : IO UInt32 := do
  match arguments with
  | ["export", directory] => exportInputs directory
  | ["check", file, directory] => checkArticles file directory
  | ["export-binding", output] =>
      let directory : System.FilePath := output
      IO.FS.createDirAll directory
      IO.FS.writeFile (directory / "inputs.json") ((← unwrap bindingInput).compress ++ "\n")
      IO.FS.writeFile (directory / "language.sexp")
        (CettaWire.Term.render (InferenceCettaWire.encodeDefinition (definitionV2 KernelControls.controlTheory 4)) ++ "\n")
      IO.FS.writeFile (directory / "definition-theory.module")
        (CheckingMachineV2.kernelModule KernelControls.controlTheory 4 ++ "\n")
  | ["check-binding", file, directory] => checkArticles file directory true
  | _ => throw (IO.userError "expected export DIRECTORY or check CANDIDATES DIRECTORY")
  return 0
