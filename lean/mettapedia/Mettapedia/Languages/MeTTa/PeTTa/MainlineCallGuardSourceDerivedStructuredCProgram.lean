import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardSourceDerivedStructuredCQualification
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCProgram

/-!
# Source-derived StructuredC program for the cold call guard

The partial source compiler is composed directly with StructuredC dispatcher,
function, and program construction.  Successful output is connected to the
existing operational target semantics; unsupported source structure remains a
compilation failure.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardSourceDerivedStructuredCProgram

open Mettapedia.GSLT
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.TotalGSLT
open Mettapedia.GSLT.LanguageDef.StructuredC
open Mettapedia.GSLT.LanguageDef.StructuredC.Builder
open Mettapedia.GSLT.LanguageDef.NormalizationPath
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardOperational
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardSourceDerivedStructuredC
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCDispatcher
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCProgram
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCFinishSemantics
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCOneStepSimulation
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCTotalRealization

/-- Compose source-row compilation with dispatcher assembly. -/
def sourceDerivedColdBody? : Option Pattern := do
  let bodies ← sourceDerivedBodies?
  assembleDispatcherBody? bodies

theorem sourceDerivedColdBody?_eq_generated :
    sourceDerivedColdBody? = some generatedColdBody := by
  simp only [sourceDerivedColdBody?,
    sourceDerivedBodies?_eq_allMatchedFamilyBodies]
  exact assemble_all_bodies_body

/-- Compose source-row compilation with complete function assembly. -/
def sourceDerivedColdFunction? : Option Pattern := do
  let bodies ← sourceDerivedBodies?
  assembleFunction? bodies

theorem sourceDerivedColdFunction?_eq_generated :
    sourceDerivedColdFunction? = some generatedColdFunction := by
  simp only [sourceDerivedColdFunction?,
    sourceDerivedBodies?_eq_allMatchedFamilyBodies]
  exact assemble_all_bodies

/-- Package the generated function with its typed primitive ABI. -/
def sourceDerivedColdProgram? : Option Pattern := do
  let generatedFunction ← sourceDerivedColdFunction?
  pure (program primitiveExternals [generatedFunction])

theorem sourceDerivedColdProgram?_eq_generated :
    sourceDerivedColdProgram? = some generatedColdProgram := by
  simp [sourceDerivedColdProgram?, sourceDerivedColdFunction?_eq_generated,
    generatedColdProgram]

/-- Successful source-derived program generation produces a well-sorted
StructuredC program. -/
theorem sourceDerivedColdProgram?_target_typed
    {target : Pattern} (compiled : sourceDerivedColdProgram? = some target) :
    CarrierWellSorted.HasType StructuredC.language
      WellSorted.FreeTypeContext.empty [] target (.base "Program") := by
  rw [sourceDerivedColdProgram?_eq_generated] at compiled
  have targetExact : target = generatedColdProgram :=
    (Option.some.inj compiled).symm
  simpa [targetExact] using generatedColdProgram_target_typed

/-- Every source compiler step is observed after normalizing the exact body
returned by the source-derived compiler. -/
theorem sourceDerivedColdBody?_realizes_step
    {body : Pattern} (compiled : sourceDerivedColdBody? = some body)
    {source target : CompileLanguageControl}
    (step : compileLanguageGSLT.Step source target) :
    terminalControl?
        (normalizeFirstUsing coldRelations StructuredC.language 1 64
          (run body (initialEnvironment source) readyReceipt)) = some target := by
  rw [sourceDerivedColdBody?_eq_generated] at compiled
  have bodyExact : body = generatedColdBody :=
    (Option.some.inj compiled).symm
  subst body
  simpa [runControl] using
    (normalized_observation_iff_of_step step target).mpr rfl

/-- The source-derived target cannot observe a different successor for a
licensed source step. -/
theorem sourceDerivedColdBody?_rejects_wrong_target
    {body : Pattern} (compiled : sourceDerivedColdBody? = some body)
    {source target : CompileLanguageControl}
    (step : compileLanguageGSLT.Step source target)
    (observed : CompileLanguageControl) (wrong : observed ≠ target) :
    terminalControl?
        (normalizeFirstUsing coldRelations StructuredC.language 1 64
          (run body (initialEnvironment source) readyReceipt)) ≠ some observed := by
  intro invented
  have exactTarget := sourceDerivedColdBody?_realizes_step compiled step
  rw [exactTarget] at invented
  exact wrong (Option.some.inj invented).symm

#print axioms sourceDerivedColdBody?_eq_generated
#print axioms sourceDerivedColdFunction?_eq_generated
#print axioms sourceDerivedColdProgram?_target_typed
#print axioms sourceDerivedColdBody?_realizes_step
#print axioms sourceDerivedColdBody?_rejects_wrong_target

end Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardSourceDerivedStructuredCProgram
