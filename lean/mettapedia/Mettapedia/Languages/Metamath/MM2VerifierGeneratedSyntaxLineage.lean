import Mettapedia.Languages.Metamath.MM2VerifierLineageOrigin
import Mettapedia.Languages.ProcessCalculi.MORK.MM2MaximalTokenLineageExecution

/-!
# Generated MM2 syntax pipeline for the fixed Metamath verifier

This module instantiates the generated MM2 parser-to-rule-scoped-execution
lineage theorem with the exact fixed Metamath verifier compiler output once an
independent renderer-domain witness has been supplied.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2VerifierGeneratedSyntaxLineage

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2Transformation
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

/-- Given a renderer-domain witness for the exact fixed verifier compiler
output, its generated maximal-token parse, independent elaboration GSLT, and
exact rule-scoped native-type trace retain finite executable-schema lineage. -/
theorem genericVerifierProgram_generatedSyntax_lineage_pipeline_of_rendered
    {rendered : String}
    (renderedExact : renderProgram? (genericVerifierProgram
      authoredMetamathVerifierGSLT) = some rendered)
    (policy : UnsupportedExecPolicy) (fuel : Nat) :
    ∃ parsed : PlannedProgram (stringScalars rendered),
      parsed.atoms = genericVerifierProgram authoredMetamathVerifierGSLT ∧
      (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
        MM2MaximalTokenElaborationGSLT.theory).satisfies
          (.request parsed.tree)
          (MM2MaximalTokenElaborationGSLT.exactOutcomeNativeType
            (.program parsed.atoms)).pred ∧
      initialSupport parsed.toParsedProgram =
        (genericVerifierProgram authoredMetamathVerifierGSLT).eraseDups ∧
      AtomsWithin VerifierExecutableLineageAuthorized
        (cRuleScopedSourceWorkQueueRunN policy fuel
          (initialSupport parsed.toParsedProgram)).1 ∧
      Nonempty (RuleScopedNativeTypeTrace policy fuel
        (initialSupport parsed.toParsedProgram)
        (cRuleScopedSourceWorkQueueRunN policy fuel
          (initialSupport parsed.toParsedProgram)).1) := by
  obtain ⟨parsed, atomsExact, elaborates, supportExact, lineage, trace⟩ :=
    successful_render_ruleScoped_native_type_lineage_pipeline
      renderedExact verifierExecutableRawFacts
      genericVerifierProgram_executable_lineageAuthorized policy fuel
  refine ⟨parsed, atomsExact, elaborates, supportExact, ?_, trace⟩
  change AtomsWithin
    (ExecutableSchemaAtomAuthorized verifierExecutableRawFacts)
    (cRuleScopedSourceWorkQueueRunN policy fuel
      (initialSupport parsed.toParsedProgram)).1
  exact lineage

section AxiomAudit

#print axioms genericVerifierProgram_generatedSyntax_lineage_pipeline_of_rendered

end AxiomAudit

end Mettapedia.Languages.Metamath.MM2VerifierGeneratedSyntaxLineage
