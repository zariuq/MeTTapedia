import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalTemplateAllocation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalTemplateOriginControls

/-!
# Allocated inputs and replacement outputs use the proved source witnesses

The native net reads only the compatible entry. A recycled logical output
number denotes a new allocation name, and only its last generation remains
in the net output set. Its conditional meaning comes from the saved source
birth, rather than a final-store value supplied to the compiler.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalTemplateAllocationControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualConditionalRows ContextualConditionalRealizations
open ContextualConditionalTemplateControls (base Operation)
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

local instance : DecidableEq base.Srt := inferInstanceAs (DecidableEq Unit)
local instance (sort : base.Srt) : DecidableEq (base.Op sort) := inferInstanceAs (DecidableEq Operation)

abbrev entryBody := ContextualConditionalTemplateOriginControls.sourceBody

theorem the_allocated_net_reads_only_the_used_entry :
    entryBody.net.effect.taken = ∅ ∧ entryBody.net.effect.kept = {Sum.inl 0} := by decide +kernel

theorem the_unused_entry_is_not_a_net_input :
    Sum.inl 1 ∉ entryBody.net.effect.taken ∪ entryBody.net.effect.kept := by
  rw [the_allocated_net_reads_only_the_used_entry.1, the_allocated_net_reads_only_the_used_entry.2]
  decide +kernel

theorem every_source_model_supplies_actual_net_input_witnesses {V : Type} (next : V → MetaArity base)
    (candidate : Assignment ContextualConditionalTemplateOriginControls.result next)
    (modeled : ContextualResidual.Models candidate ContextualConditionalTemplateOriginControls.after.equations) :
    ∃ extension : ContextualGuardMatching.Extension next,
    ∃ _filler : Assignment ContextualConditionalTemplateOriginControls.locals extension.declarations,
      ∀ physical ∈ ([Sum.inl 0] : List (OccurrenceAllocationRenaming.Name Nat)),
        ∃ value : Term (signature base extension.declarations) [] (),
          Realizes ContextualConditionalTemplateOriginControls.locals ContextualConditionalTemplateOriginControls.captures
            (Assignment.compose extension.assignment (Assignment.compose candidate entryBody.frame.assignment))
            value (ContextualConditionalTemplateOriginControls.before.rows (OccurrenceAllocationRenaming.erase physical)) := by
  have admitted := entryBody.admitted_characterization.mp ContextualConditionalTemplateOriginControls.source_body_admitted
  apply entryBody.net_inputs_realize_together admitted.1 admitted.2.1 candidate modeled [Sum.inl 0]
  intro physical member
  have same := List.mem_singleton.mp member
  subst physical
  rw [the_allocated_net_reads_only_the_used_entry.1, the_allocated_net_reads_only_the_used_entry.2]
  decide +kernel

namespace Reuse

abbrev sourceBody := ContextualConditionalTemplateOriginControls.Reuse.sourceBody
abbrev finalWorld := ContextualConditionalTemplateOriginControls.Reuse.finalWorld

theorem the_new_generation_is_the_net_output :
    OccurrenceAllocationRenaming.fresh 2 10 ∈ sourceBody.net.effect.made ∧
      OccurrenceAllocationRenaming.fresh 0 10 ∉ sourceBody.net.effect.made ∧
      Sum.inl 10 ∉ sourceBody.net.effect.made := by decide +kernel

theorem the_net_output_selects_its_saved_conditional_meaning {V : Type} (next : V → MetaArity base)
    (candidate : Assignment finalWorld.declarations next) (value : Term (signature base next) [] ()) :
    ∃ birth : ContextualConditionalTemplateSchedules.Birth finalWorld.declarations Nat [] (),
      sourceBody.outputBirth 10 = some birth ∧
        (birth.origin.Instances candidate value ↔ Matches
          (ContextualClauseSourceState.resultLocals ContextualConditionalTemplateSourceControls.queries
            ContextualConditionalTemplateOriginControls.Reuse.middleLocals ContextualConditionalTemplateOriginControls.Reuse.middle)
          finalWorld.declarations candidate value (finalWorld.rows 10)) := by
  have resources := (CompiledSchedule.compile_condition_iff ContextualSourceSchedules.Schedule.unitLabel
    sourceBody.commits ContextualConditionalTemplateSourceControls.before.present).mp
      ContextualConditionalTemplateOriginControls.Reuse.logical_identifier_reuse_has_valid_resources
  exact sourceBody.net_output_instances ContextualConditionalTemplateOriginControls.Reuse.source_shapes resources
    (OccurrenceAllocationRenaming.fresh 2 10) the_new_generation_is_the_net_output.1 candidate value

end Reuse

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalTemplateAllocationControls
