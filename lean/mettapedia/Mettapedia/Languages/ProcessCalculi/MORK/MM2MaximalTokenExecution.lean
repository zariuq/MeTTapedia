import Mettapedia.Languages.ProcessCalculi.MORK.MM2MaximalTokenSemantics
import Mettapedia.Languages.ProcessCalculi.MORK.MM2MaximalTokenElaborationGSLT
import Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveGSLTNativeTypes

/-!
# Generated MM2 parsing to existing execution semantics

Parsing produces an ordered list of atom occurrences.  The existing MM2
loader has support semantics, so duplicate removal occurs at this single
explicit boundary.  No parser rule introduces an execution transition.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MORK.MM2MaximalTokenExecution

open Mettapedia.Languages.MeTTa.OSLFCore
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.MM2MaximalTokenElaborationPlan
open Mettapedia.Languages.ProcessCalculi.MORK.MM2Surface
open Mettapedia.Languages.ProcessCalculi.MORK.MM2MaximalTokenSemantics

def initialSupport {input : List Nat}
    (parsed : ParsedProgram input) : List Atom :=
  parsed.atoms.eraseDups

private theorem eraseDups_nodup :
    (atoms : List Atom) → atoms.eraseDups.Nodup
  | [] => by simp
  | atom :: atoms => by
      rw [List.eraseDups_cons]
      refine List.nodup_cons.mpr ⟨?_, eraseDups_nodup _⟩
      intro member
      rw [List.mem_eraseDups, List.mem_filter] at member
      simp at member
termination_by atoms => atoms.length
decreasing_by
  have shorter :=
    List.length_filter_le (fun other => !other == atom) atoms
  simp only [List.length_cons]
  omega

theorem initialSupport_nodup
    {input : List Nat} (parsed : ParsedProgram input) :
    (initialSupport parsed).Nodup :=
  eraseDups_nodup parsed.atoms

/-- The generated parse enters the existing executable MM2 GSLT through its
generated OSLF native type.  Parsing introduces no second execution relation. -/
theorem execution_native_type_iff
    {input : List Nat} (parsed : ParsedProgram input)
    (policy : UnsupportedExecPolicy) (target : List Atom) :
    (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
      (reflectiveNativeListExecGSLT policy)).satisfies
        (initialSupport parsed)
        (reflectiveNativeListExactTargetNativeType policy target).pred ↔
      ReflectiveComputable.cReflectiveSourceWorkQueueStep
        policy (initialSupport parsed) = some target :=
  satisfies_reflectiveNativeListExactTargetNativeType_iff_step
    policy (initialSupport parsed) target

/-- Canonical rendering, generated parsing, both CST lowerings, and the
existing reflective MM2 execution GSLT form one commuting boundary. -/
theorem successful_render_execution_commutes
    {program : List Atom} {rendered : String}
    (renderedExact : renderProgram? program = some rendered) :
    ∃ parsed : PlannedProgram (stringScalars rendered),
      parsed.atoms = program ∧
      initialSupport parsed.toParsedProgram = program.eraseDups ∧
      ∀ (policy : UnsupportedExecPolicy) (target : List Atom),
        (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
          (reflectiveNativeListExecGSLT policy)).satisfies
            (initialSupport parsed.toParsedProgram)
            (reflectiveNativeListExactTargetNativeType policy target).pred ↔
          ReflectiveComputable.cReflectiveSourceWorkQueueStep
            policy (initialSupport parsed.toParsedProgram) = some target := by
  obtain ⟨parsed, atomsExact⟩ :=
    successful_render_has_planned_parser_square renderedExact
  refine ⟨parsed, atomsExact, ?_, ?_⟩
  · simp only [initialSupport, atomsExact]
  · intro policy target
    exact execution_native_type_iff parsed.toParsedProgram policy target

/-- The full generated parsing boundary includes the independently executable
CST elaboration GSLT before entering the existing MM2 execution GSLT. -/
theorem successful_render_full_pipeline
    {program : List Atom} {rendered : String}
    (renderedExact : renderProgram? program = some rendered) :
    ∃ parsed : PlannedProgram (stringScalars rendered),
      parsed.atoms = program ∧
      (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
        MM2MaximalTokenElaborationGSLT.theory).satisfies
          (.request parsed.tree)
          (MM2MaximalTokenElaborationGSLT.exactOutcomeNativeType
            (.program parsed.atoms)).pred ∧
      initialSupport parsed.toParsedProgram = program.eraseDups ∧
      ∀ (policy : UnsupportedExecPolicy) (target : List Atom),
        (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
          (reflectiveNativeListExecGSLT policy)).satisfies
            (initialSupport parsed.toParsedProgram)
            (reflectiveNativeListExactTargetNativeType policy target).pred ↔
          ReflectiveComputable.cReflectiveSourceWorkQueueStep
            policy (initialSupport parsed.toParsedProgram) = some target := by
  obtain ⟨parsed, atomsExact, supportExact, executionExact⟩ :=
    successful_render_execution_commutes renderedExact
  exact ⟨parsed, atomsExact,
    MM2MaximalTokenElaborationGSLT.parsed_program_inhabits_exact_outcome
      parsed,
    supportExact, executionExact⟩

#print axioms initialSupport_nodup
#print axioms execution_native_type_iff
#print axioms successful_render_execution_commutes
#print axioms successful_render_full_pipeline

end Mettapedia.Languages.ProcessCalculi.MORK.MM2MaximalTokenExecution
