import Mettapedia.Languages.Metamath.MM2SourceActionExecution

/-!
# Export one raw Metamath unit fixture through the two MM2 transformations

This executable keeps the source and verifier transformations separate.  It
first converts raw Metamath bytes into structurally admitted, proof-neutral
source-event data.  It then composes that data with the generic verifier
generated from the authored Metamath and MM2 presentations and renders the
result as ordinary MM2.
-/

namespace Mettapedia.OSLF.Tools.ExportMetamathMM2RawUnit

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2DataEncoding
open Mettapedia.Languages.Metamath.MM2SourceActionExecution
open Mettapedia.Languages.Metamath.MM2SourceActionPlan
open Mettapedia.Languages.Metamath.MM2SourceEventTransformation
open Mettapedia.Languages.Metamath.MM2Transformation
open Mettapedia.Languages.Metamath.SourceGSLTIncludeDAG
open Mettapedia.Languages.ProcessCalculi.MORK.MM2Surface

/-- The executable projection of `transformNormalVerifierSlice`.  The target's
proof fields are erased here; the following equality keeps this projection
definitionally tied to the semantic transformation. -/
def baseVerifierProgram (source : MetamathVerifierGSLT) : List Atom :=
  normalVerifierInternalRows ++
    (orderedSourceEventPreludeRules ++
      source.operations.flatMap verifierRulesForNormalSlice)

theorem baseVerifierProgram_eq_transform (source : MetamathVerifierGSLT)
    (target : MM2Target) :
    baseVerifierProgram source =
      (transformNormalVerifierSlice source target).program := by
  rfl

def verifierProgram (source : MetamathVerifierGSLT) : List Atom :=
  baseVerifierProgram source ++ sourceActionVerifierExtensionProgram

theorem verifierProgram_eq_transform_extension
    (source : MetamathVerifierGSLT) (target : MM2Target) :
    verifierProgram source =
      (transformNormalVerifierSlice source target).program ++
        sourceActionVerifierExtensionProgram := by
  rw [verifierProgram, baseVerifierProgram_eq_transform source target]

def composeProgram (source : MetamathVerifierGSLT) {owner : Atom}
    (input : AdmittedSourceEventInput owner)
    (actions : AdmittedSourceActionPlans owner input.statements) : List Atom :=
  verifierProgram source ++ deferProofControls input.initialRows ++ actions.rows

theorem composeProgram_eq_admitted_extension (source : MetamathVerifierGSLT)
    (target : MM2Target) {owner : Atom}
    (input : AdmittedSourceEventInput owner)
    (actions : AdmittedSourceActionPlans owner input.statements) :
    composeProgram source input actions =
      ((transformNormalVerifierSlice source target).program ++
          sourceActionVerifierExtensionProgram) ++
        deferProofControls input.initialRows ++ actions.rows := by
  simp [composeProgram, verifierProgram,
    baseVerifierProgram_eq_transform source target,
    List.append_assoc]

def run (arguments : List String) : IO UInt32 := do
  let (sourcePath, outputPath) <- match arguments with
    | [sourcePath, outputPath] => pure (sourcePath, outputPath)
    | _ =>
        IO.eprintln
          "usage: ExportMetamathMM2RawUnit <source.mm> <output.mm2>"
        return 2

  let sourceBytes <- IO.FS.readBinFile sourcePath
  let logicalRoot := "unit.mm"
  let files : FileMap := fun path =>
    if path = logicalRoot then some sourceBytes else none
  let owner := stringAtom "metamath-test-unit"

  match transformRawSource owner files bookSpecPolicy logicalRoot with
  | .error _ =>
      IO.eprintln "raw Metamath source transformation rejected the fixture"
      return 1
  | .ok artifact =>
      match admitSourceEventInput owner artifact.rows with
      | .error _ =>
          IO.eprintln "MM2 source-event admission rejected transformed rows"
          return 1
      | .ok input =>
          match admitSourceActionPlans owner input.statements with
          | .rejected _ =>
              IO.eprintln "MM2 source-action planning rejected transformed rows"
              return 1
          | .ok actions =>
              let program :=
                composeProgram authoredMetamathVerifierGSLT input actions
              match renderProgram? program with
              | none =>
                  IO.eprintln
                    "the transformed program is outside ordinary MM2"
                  return 1
              | some rendered =>
                  IO.FS.writeFile outputPath rendered
                  IO.println
                    s!"MM2RawUnitExport statements={artifact.statements.length} obligations={artifact.obligations.length} initialRows={input.initialRows.length} actionPlans={actions.plans.length} actionRows={actions.rows.length} programAtoms={program.length} outputBytes={rendered.toUTF8.size}"
                  return 0

end Mettapedia.OSLF.Tools.ExportMetamathMM2RawUnit

def exportMetamathMM2RawUnitMain (arguments : List String) : IO UInt32 :=
  Mettapedia.OSLF.Tools.ExportMetamathMM2RawUnit.run arguments

/-- Environment-facing entry used by the bounded conformance gate.  Keeping
the entry named avoids inheriting an unrelated root `main` from the raw-source
parser library. -/
def exportMetamathMM2RawUnitFromEnvironment : IO UInt32 := do
  match (← IO.getEnv "METTAPEDIA_MM2_RAW_SOURCE"),
      (← IO.getEnv "METTAPEDIA_MM2_RAW_OUTPUT") with
  | some sourcePath, some outputPath =>
      exportMetamathMM2RawUnitMain [sourcePath, outputPath]
  | _, _ =>
      IO.eprintln
        "METTAPEDIA_MM2_RAW_SOURCE and METTAPEDIA_MM2_RAW_OUTPUT are required"
      return 2
