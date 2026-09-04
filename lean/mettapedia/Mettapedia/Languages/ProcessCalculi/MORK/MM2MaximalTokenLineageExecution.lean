import Mettapedia.Languages.ProcessCalculi.MORK.ExecutableSchemaParserBridge
import Mettapedia.Languages.ProcessCalculi.MORK.MM2MaximalTokenRuleScopedExecution

/-!
# Generated MM2 parsing with executable-schema lineage

The maximal-token syntax language admits an ordered atom program through its
generated parser and independent elaboration.  This module adds the separate
semantic admission boundary required before that program is executed: every
initial atom must be authorized by a finite executable-schema inventory.

Parsing does not itself grant executable authority.  Once a caller supplies
that source-relative authorization, the generated parser, elaboration GSLT,
and actual rule-scoped scheduler preserve it through every bounded run.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MORK.MM2MaximalTokenLineageExecution

open Mettapedia.Languages.MeTTa.OSLFCore
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.Conformance.Computable
open Mettapedia.Languages.ProcessCalculi.MORK.MM2MaximalTokenElaborationPlan
open Mettapedia.Languages.ProcessCalculi.MORK.MM2MaximalTokenExecution
open Mettapedia.Languages.ProcessCalculi.MORK.MM2MaximalTokenRuleScopedExecution
open Mettapedia.Languages.ProcessCalculi.MORK.MM2MaximalTokenSemantics
open Mettapedia.Languages.ProcessCalculi.MORK.MM2Surface

/-- The parser-to-support boundary only removes duplicate occurrences, so an
atom-local executable-schema authorization is retained exactly. -/
theorem initialSupport_lineageAuthorized
    (schemas : List RawExecFact) {input : List Nat}
    (parsed : ParsedProgram input)
    (atomsAuthorized :
      AtomsWithin (ExecutableSchemaAtomAuthorized schemas) parsed.atoms) :
    AtomsWithin (ExecutableSchemaAtomAuthorized schemas)
      (initialSupport parsed) := by
  intro atom member
  apply atomsAuthorized atom
  simpa only [initialSupport, List.mem_eraseDups] using member

/-- A successfully rendered MM2 program has a generated parse, an independent
elaboration witness, and a bounded actual scheduler run that retains the
caller-supplied finite executable-schema lineage. -/
theorem successful_render_ruleScoped_lineage_pipeline
    {program : List Atom} {rendered : String}
    (renderedExact : renderProgram? program = some rendered)
    (schemas : List RawExecFact)
    (programAuthorized :
      AtomsWithin (ExecutableSchemaAtomAuthorized schemas) program)
    (policy : UnsupportedExecPolicy) (fuel : Nat) :
    ∃ parsed : PlannedProgram (stringScalars rendered),
      parsed.atoms = program ∧
      (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
        MM2MaximalTokenElaborationGSLT.theory).satisfies
          (.request parsed.tree)
          (MM2MaximalTokenElaborationGSLT.exactOutcomeNativeType
            (.program parsed.atoms)).pred ∧
      initialSupport parsed.toParsedProgram = program.eraseDups ∧
      AtomsWithin (ExecutableSchemaAtomAuthorized schemas)
        (cRuleScopedSourceWorkQueueRunN policy fuel
          (initialSupport parsed.toParsedProgram)).1 := by
  obtain ⟨parsed, atomsExact, elaborates, supportExact, _⟩ :=
    successful_render_ruleScoped_bounded_pipeline renderedExact policy fuel
  have parsedAuthorized :
      AtomsWithin (ExecutableSchemaAtomAuthorized schemas) parsed.atoms := by
    rw [atomsExact]
    exact programAuthorized
  have initialAuthorized := initialSupport_lineageAuthorized schemas
    parsed.toParsedProgram parsedAuthorized
  refine ⟨parsed, atomsExact, elaborates, supportExact, ?_⟩
  exact cRuleScopedSourceWorkQueueRunN_lineageAuthorized schemas policy fuel
    (initialSupport parsed.toParsedProgram) initialAuthorized

/-- The same parser-to-scheduler pipeline retains executable-schema lineage
while exposing the exact OSLF-generated native type of every primitive run
transition. -/
theorem successful_render_ruleScoped_native_type_lineage_pipeline
    {program : List Atom} {rendered : String}
    (renderedExact : renderProgram? program = some rendered)
    (schemas : List RawExecFact)
    (programAuthorized :
      AtomsWithin (ExecutableSchemaAtomAuthorized schemas) program)
    (policy : UnsupportedExecPolicy) (fuel : Nat) :
    ∃ parsed : PlannedProgram (stringScalars rendered),
      parsed.atoms = program ∧
      (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
        MM2MaximalTokenElaborationGSLT.theory).satisfies
          (.request parsed.tree)
          (MM2MaximalTokenElaborationGSLT.exactOutcomeNativeType
            (.program parsed.atoms)).pred ∧
      initialSupport parsed.toParsedProgram = program.eraseDups ∧
      AtomsWithin (ExecutableSchemaAtomAuthorized schemas)
        (cRuleScopedSourceWorkQueueRunN policy fuel
          (initialSupport parsed.toParsedProgram)).1 ∧
      Nonempty (RuleScopedNativeTypeTrace policy fuel
        (initialSupport parsed.toParsedProgram)
        (cRuleScopedSourceWorkQueueRunN policy fuel
          (initialSupport parsed.toParsedProgram)).1) := by
  obtain ⟨parsed, atomsExact, elaborates, supportExact, nativeTrace⟩ :=
    successful_render_ruleScoped_native_type_trace_pipeline renderedExact
      policy fuel
  have parsedAuthorized :
      AtomsWithin (ExecutableSchemaAtomAuthorized schemas) parsed.atoms := by
    rw [atomsExact]
    exact programAuthorized
  have initialAuthorized := initialSupport_lineageAuthorized schemas
    parsed.toParsedProgram parsedAuthorized
  refine ⟨parsed, atomsExact, elaborates, supportExact, ?_, nativeTrace⟩
  exact cRuleScopedSourceWorkQueueRunN_lineageAuthorized schemas policy fuel
    (initialSupport parsed.toParsedProgram) initialAuthorized

section AxiomAudit

#print axioms initialSupport_lineageAuthorized
#print axioms successful_render_ruleScoped_lineage_pipeline
#print axioms successful_render_ruleScoped_native_type_lineage_pipeline

end AxiomAudit

end Mettapedia.Languages.ProcessCalculi.MORK.MM2MaximalTokenLineageExecution
