import Mettapedia.Languages.Metamath.MM2SourceActionExecution
import Mettapedia.Languages.Metamath.MM2SourceActionRuleInventory
import Mettapedia.Languages.Metamath.MM2SourceActionKindDispatch
import Mettapedia.Languages.Metamath.MM2NormalLabelLookup
import Mettapedia.Languages.Metamath.MM2NormalLabelLookupAgreement
import Mettapedia.Languages.Metamath.MM2CompressedProofExecution
import Mettapedia.Languages.Metamath.MM2CompressedProofOrderedActivation
import Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeOrderedPresentation
import Mettapedia.Languages.Metamath.MM2Transformation

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
open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.Metamath.MM2CompressedProofOrderedActivation
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeOrderedPresentation
open Mettapedia.Languages.Metamath.MM2SourceActionExecution
open Mettapedia.Languages.Metamath.MM2SourceActionRuleInventory
open Mettapedia.Languages.Metamath.MM2SourceActionKindDispatch
open Mettapedia.Languages.Metamath.MM2SourceActionPlan
open Mettapedia.Languages.Metamath.MM2NormalLabelLookup
open Mettapedia.Languages.Metamath.MM2SourceEventTransformation
open Mettapedia.Languages.Metamath.MM2OrderedEventVerifier
open Mettapedia.Languages.Metamath.MM2Transformation
open Mettapedia.Languages.Metamath.SourceGSLTIncludeDAG
open Mettapedia.Languages.Metamath.SourceGSLTOperations
open Mettapedia.Languages.Metamath.SourceGSLTRawSourceComposition
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

/-- Fixed-profile compressed source-rule extension selected by the supplied
operation spine.  These source-level activation, loading, and finishing rules
are verifier-owned and must be reinstalled by the ordinary source reload
protocol; compact header/body rows remain dynamic source data. -/
def compressedVerifierSourceRulesForOperation : SourceOperation → List Atom
  | .checkTheoremCompressed => compressedOrderedActivationRules
  | _ => []

/-- Fixed verifier-owned compressed runtime inventory selected by the supplied
operation spine.  These linked rows are data for the ordered rule loader; they
are not executable source actions. -/
def compressedVerifierRuntimeRowsForOperation : SourceOperation → List Atom
  | .checkTheoremCompressed =>
    compressedSpeculativeVerifierRuleRows ++
      [compressedSpeculativeVerifierRuleEnd] ++
      compressedSpeculativeVerifierStaticRows ++
      compressedNormalHandoffRuleRows ++ [compressedNormalHandoffRuleEnd] ++
          compressedNormalDispatchBridgeRows ++ [compressedDispatchReloadCaptureRow]
  | _ => []

/-- The compressed source-rule branch is selected from the actual supplied
operation list.  This is an operation-spine profile selection, not a claim
that the present fixed rule inventory has been synthesized from arbitrary
source operational equations. -/
def compressedVerifierSourceExtension
    (source : MetamathVerifierGSLT) : List Atom :=
  source.operations.flatMap compressedVerifierSourceRulesForOperation

/-- The corresponding fixed verifier-owned runtime rows. -/
def compressedVerifierRuntimeExtension
    (source : MetamathVerifierGSLT) : List Atom :=
  source.operations.flatMap compressedVerifierRuntimeRowsForOperation

def verifierProgram (source : MetamathVerifierGSLT) : List Atom :=
  baseVerifierProgram source ++
    sourceActionVerifierExtensionProgramWith normalProofMachineRuleInventory
      (normalLabelLookupSourceRules ++
        compressedVerifierSourceExtension source) ++
      normalLabelLookupStaticRows ++
      compressedVerifierRuntimeExtension source

theorem verifierProgram_eq_transform_extension
    (source : MetamathVerifierGSLT) (target : MM2Target) :
    verifierProgram source =
      (transformNormalVerifierSlice source target).program ++
        sourceActionVerifierExtensionProgramWith
          normalProofMachineRuleInventory
          (normalLabelLookupSourceRules ++
            compressedVerifierSourceExtension source) ++
          normalLabelLookupStaticRows ++
          compressedVerifierRuntimeExtension source := by
  rw [verifierProgram, baseVerifierProgram_eq_transform source target]

/-- A compact-only source can defer the normal proof machine until the compact
verifier reaches its explicit normal assertion handoff.  This is selected from
the admitted statement shape, not from a pathname, digest, or fixture label. -/
def allTheoremProofsCompressed : List RawStatement → Bool
  | [] => true
  | .provable _ _ _ _ (.normal _) _ _ :: _ => false
  | .provable _ _ _ _ (.compressed _ _ _ _) _ _ :: statements =>
      allTheoremProofsCompressed statements
  | _ :: statements => allTheoremProofsCompressed statements

def containsCompressedTheorem : List RawStatement → Bool
  | [] => false
  | .provable _ _ _ _ (.compressed _ _ _ _) _ _ :: _ => true
  | _ :: statements => containsCompressedTheorem statements

def usesDeferredNormalCompressedProfile
    (statements : List RawStatement) : Bool :=
  containsCompressedTheorem statements && allTheoremProofsCompressed statements

/-- A mixed normal/compact source needs the normal machine available for an
earlier ordinary proof, while retaining the reactive source-action inventory
that lets a later compact proof rejoin the ordered source loop. -/
def usesMixedNormalCompressedProfile
    (statements : List RawStatement) : Bool :=
  containsCompressedTheorem statements && !allTheoremProofsCompressed statements

/-- The source-event prelude needed before a compact proof reaches its
normal-machine handoff.  The normal proof machine is deliberately absent from
this profile until verifier-owned compact activation loads it. -/
def deferredNormalCompressedBaseProgram : List Atom :=
  normalVerifierInternalRows ++
    [sourceEventBootstrapRule, sourceEventDispatchRule, sourceTheoremStartRule]

/-- Initial executable surface for a source that contains both normal and
compact theorem proofs.  The normal proof machine is available from the first
ordinary theorem; compact activation and its reactive source-loop support are
added separately below. -/
def mixedNormalCompressedBaseProgram : List Atom :=
  deferredNormalCompressedBaseProgram ++ normalProofMachineRules

def mixedNormalCompressedProgram (source : MetamathVerifierGSLT) : List Atom :=
  mixedNormalCompressedBaseProgram ++
    compressedNormalSourceActionExtension
      (normalLabelLookupSourceRules ++
        compressedVerifierSourceExtension source) ++
      normalLabelLookupStaticRows ++
      compressedVerifierRuntimeExtension source

def verifierProgramForStatements (source : MetamathVerifierGSLT)
    (statements : List RawStatement) : List Atom :=
  (if usesDeferredNormalCompressedProfile statements then
      deferredNormalCompressedBaseProgram ++
        compressedNormalSourceActionExtension
          (compressedVerifierSourceExtension source) ++
          compressedVerifierRuntimeExtension source
    else if usesMixedNormalCompressedProfile statements then
      mixedNormalCompressedProgram source
    else verifierProgram source)

def composeProgram (source : MetamathVerifierGSLT) {owner : Atom}
    (input : AdmittedSourceEventInput owner)
    (actions : AdmittedSourceActionPlans owner input.statements) : List Atom :=
  verifierProgramForStatements source input.statements ++
    deferCompressedHeaderControls (deferProofControls input.initialRows) ++
      actions.rows ++ admittedSourceActionPlanActionKindRows actions

theorem composeProgram_eq_profiled (source : MetamathVerifierGSLT)
    {owner : Atom}
    (input : AdmittedSourceEventInput owner)
    (actions : AdmittedSourceActionPlans owner input.statements) :
    composeProgram source input actions =
      (verifierProgramForStatements source input.statements ++
        deferCompressedHeaderControls (deferProofControls input.initialRows) ++
          actions.rows ++ admittedSourceActionPlanActionKindRows actions) := by
  rfl

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
          | .ok plannedActions =>
              match admitSourceActionPlanRows plannedActions
                  plannedActions.bundleRows with
              | .error _ =>
                  IO.eprintln
                    "MM2 source-action bundle admission rejected derived rows"
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
