import Mettapedia.Languages.Metamath.MM2TwoTransformLineageClosure
import Mettapedia.Languages.ProcessCalculi.MORK.MM2MaximalTokenLineageExecution

/-!
# Generated syntax and rule-scoped execution for the two-transform program

The proof-independent Metamath verifier and the admitted source-data transform
are composed before rendering.  A successful generated MM2 parse reconstructs
that exact program, its elaboration inhabits the generated parser target type,
and the duplicate-coalesced support enters rule-scoped MORK execution under the
fixed verifier's recursive executable-lineage invariant.  Every bounded
primitive transition also carries its exact OSLF-generated native type.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2TwoTransformGeneratedSyntaxLineage

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2SourceActionPlan
open Mettapedia.Languages.Metamath.MM2SourceEventTransformation
open Mettapedia.Languages.Metamath.MM2Transformation
open Mettapedia.Languages.Metamath.MM2TwoTransformLineageClosure
open Mettapedia.Languages.Metamath.MM2TwoTransformProgram
open Mettapedia.Languages.Metamath.MM2VerifierExecutableOrigin
open Mettapedia.Languages.Metamath.MM2VerifierLineageOrigin
open Mettapedia.Languages.Metamath.MM2VerifierProgram
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.Conformance.Computable
open Mettapedia.Languages.ProcessCalculi.MORK.MM2MaximalTokenElaborationGSLT
open Mettapedia.Languages.ProcessCalculi.MORK.MM2MaximalTokenElaborationPlan
open Mettapedia.Languages.ProcessCalculi.MORK.MM2MaximalTokenExecution
open Mettapedia.Languages.ProcessCalculi.MORK.MM2MaximalTokenLineageExecution
open Mettapedia.Languages.ProcessCalculi.MORK.MM2MaximalTokenRuleScopedExecution
open Mettapedia.Languages.ProcessCalculi.MORK.MM2MaximalTokenSemantics
open Mettapedia.Languages.ProcessCalculi.MORK.MM2Surface

/-- The complete two-transform program passes generated MM2 parsing and
elaboration into an arbitrary-fuel rule-scoped MORK run while retaining exact
compiler-derived executable lineage and a proof-relevant native-type trace. -/
theorem composeProgram_generatedSyntax_lineage_pipeline_of_rendered
    {owner : Atom} (ownerAuthorized : SourceOwnerLineageAuthorized owner)
    (input : AdmittedSourceEventInput owner)
    (actions : AdmittedSourceActionPlans owner input.statements)
    {rendered : String}
    (renderedExact : renderProgram?
      (composeProgram authoredMetamathVerifierGSLT input actions) =
        some rendered)
    (policy : UnsupportedExecPolicy) (fuel : Nat) :
    ∃ parsed : PlannedProgram (stringScalars rendered),
      parsed.atoms =
        composeProgram authoredMetamathVerifierGSLT input actions ∧
      (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
        MM2MaximalTokenElaborationGSLT.theory).satisfies
          (.request parsed.tree)
          (MM2MaximalTokenElaborationGSLT.exactOutcomeNativeType
            (.program parsed.atoms)).pred ∧
      initialSupport parsed.toParsedProgram =
        (composeProgram authoredMetamathVerifierGSLT input actions).eraseDups ∧
      AtomsWithin VerifierExecutableLineageAuthorized
        (cRuleScopedSourceWorkQueueRunN policy fuel
          (initialSupport parsed.toParsedProgram)).1 ∧
      Nonempty (RuleScopedNativeTypeTrace policy fuel
        (initialSupport parsed.toParsedProgram)
        (cRuleScopedSourceWorkQueueRunN policy fuel
          (initialSupport parsed.toParsedProgram)).1) := by
  obtain ⟨parsed, atomsExact, elaborates, supportExact, lineage, trace⟩ :=
    successful_render_ruleScoped_native_type_lineage_pipeline renderedExact
      verifierExecutableRawFacts
      (composeProgram_executable_lineageAuthorized ownerAuthorized input
        actions) policy fuel
  refine ⟨parsed, atomsExact, elaborates, supportExact, ?_, trace⟩
  change AtomsWithin
    (ExecutableSchemaAtomAuthorized verifierExecutableRawFacts)
    (cRuleScopedSourceWorkQueueRunN policy fuel
      (initialSupport parsed.toParsedProgram)).1
  exact lineage

section AxiomAudit

#print axioms composeProgram_generatedSyntax_lineage_pipeline_of_rendered

end AxiomAudit

end Mettapedia.Languages.Metamath.MM2TwoTransformGeneratedSyntaxLineage
