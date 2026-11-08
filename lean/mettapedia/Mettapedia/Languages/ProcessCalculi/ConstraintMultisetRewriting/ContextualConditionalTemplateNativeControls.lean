import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalTemplateNativeResult
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalTemplateOriginControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualExecutionCommutationNames

/-!
# Actual mixed producer controls

Two reads of a compatible reusable schema share the caller and keep their
own private witnesses. An unused incompatible entry remains stored without
preventing the actual firing. Selecting the incompatible output instead
makes the native binding problem inconsistent.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalTemplateNativeControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualConjunctiveQueries ContextualConditionalRows ContextualClauseWitnesses
open ContextualConditionalTemplateControls (base Operation literal pattern)
open ContextualConditionalTemplateSchedules
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

local instance : DecidableEq base.Srt := inferInstanceAs (DecidableEq Unit)
local instance (sort : base.Srt) : DecidableEq (base.Op sort) := inferInstanceAs (DecidableEq Operation)

namespace Mixed

open ContextualConditionalTemplateSourceControls

local instance (side : Bool) : DecidableEq
    (ContextualConditionalTemplateState.PrivateNames (Query := Empty) (Inner := Unit) rowLocals before side) := by
  let _ : DecidableEq (Empty ⊕ (Nat × Unit)) := inferInstance
  let _ : DecidableEq (Mettapedia.Logic.LP.ScopedVar (Empty ⊕ (Nat × Unit))) := inferInstance
  let _ : DecidableEq (Mettapedia.Logic.LP.ScopedVar (Empty ⊕ (Nat × Unit)) ⊕ Unit) := inferInstance
  cases side
  · change DecidableEq (Empty ⊕ (Nat × Unit))
    infer_instance
  · change DecidableEq ((Empty ⊕ (Nat × Unit)) ⊕
      ((Empty ⊕ (Nat × Unit)) ⊕ (Mettapedia.Logic.LP.ScopedVar (Empty ⊕ (Nat × Unit)) ⊕ Unit)))
    infer_instance

theorem two_private_reads_have_one_actual_native_publication (occupied : Finset Nat) (fuel : Nat) :
    ∃ publication : goodBody.NativePublication occupied,
      publication.firing.fuel = fuel ∧
        ContextualWorldComparison.Equivalent
          (ContextualClauseSourceState.target queries privateRows after nextPlan nextSelection)
          (generator _) publication.projection publication.producerCaller := by
  have parts := goodBody.admitted_characterization.mp the_mixed_body_is_admitted
  obtain ⟨publication, budget⟩ := goodBody.realize_native_publication parts.1 parts.2.1 parts.2.2.1 occupied fuel
  exact ⟨publication, budget, publication.world_equivalent parts.1 parts.2.1⟩

/-- Every output of the actual mixed-body firing is materialized from
its emitted term and a recipe supplied by the source compiler. -/
theorem actual_native_outputs_carry_recipes (occupied : Finset Nat) (fuel : Nat) :
    ∃ publication : goodBody.NativePublication occupied,
      publication.firing.fuel = fuel ∧
        ∀ physical ∈ publication.firing.selection.made,
          ∃ recipe, publication.recipes physical = some recipe ∧
            publication.target.rows physical = recipe.publish
              (ContextualComputedFreshFrame.includeSource publication.firing.update)
              (publication.firing.outputs physical) := by
  have parts := goodBody.admitted_characterization.mp the_mixed_body_is_admitted
  obtain ⟨publication, budget, _meaning⟩ := two_private_reads_have_one_actual_native_publication occupied fuel
  refine ⟨publication, budget, ?_⟩
  intro physical made
  obtain ⟨recipe, selected⟩ := publication.recipes_cover_outputs parts.1 parts.2.1 physical made
  refine ⟨recipe, selected, ?_⟩
  change publication.rows physical = _
  unfold Schedule.NativePublication.rows ContextualConditionalRowPacking.publishWithFallback
  unfold Schedule.NativePublication.recipes Schedule.NativePublication.embedRecipe at selected
  rw [selected]

/-- An actual mixed native publication can place all of its private output
names in a fresh tagged bank without changing the rendered conditional row.
The captured solver frame and physical output identities are fixed. -/
theorem actual_native_recipes_commute_with_private_reindexing (occupied : Finset Nat) (fuel : Nat) :
    ∃ publication : goodBody.NativePublication occupied,
      publication.firing.fuel = fuel ∧
        ∀ physical ∈ publication.firing.selection.made,
          ∃ recipe, publication.recipes physical = some recipe ∧
            let enlarged := fun name : Bool × (Σ index, publication.PrivateNames index) =>
              publication.resultLocals name.2
            (recipe.reindexPrivate enlarged (fun name => (true, name)) (fun _ => rfl)).publish
                (ContextualComputedFreshFrame.includeSource publication.firing.update)
                (publication.firing.outputs physical) =
              ContextualConditionalPublication.reindexPrivate publication.resultLocals enlarged _
                (fun name => (true, name)) (fun _ => rfl) (publication.target.rows physical) := by
  obtain ⟨publication, budget, rendered⟩ := actual_native_outputs_carry_recipes occupied fuel
  refine ⟨publication, budget, ?_⟩
  intro physical made
  obtain ⟨recipe, selected, same⟩ := rendered physical made
  refine ⟨recipe, selected, ?_⟩
  dsimp only
  rw [same]
  exact recipe.publish_reindexPrivate _ _ _ _ _

/-- The execution component of an actual compiled mixed body can be
realized with another fresh-scope allocation and another solver budget.
Transport of native predicate queries and publication recipes is separate. -/
theorem actual_native_execution_relocates (occupied reserved : Finset Nat) (firstFuel nextFuel : Nat) :
    ∃ publication : goodBody.NativePublication occupied,
      publication.firing.fuel = firstFuel ∧
      ∃ permutation : Equiv.Perm Nat,
        (∀ port : ContextualActivationScopes.Port publication.firing.selection,
          permutation (ContextualActivationScopes.scopeAt occupied port) =
            ContextualActivationScopes.scopeAt reserved port) ∧
        ∃ moved : ContextualConditionalExecution.Firing _
            {goodBody.native.nativeBindingState occupied with occupied := reserved},
          moved.rule = publication.firing.rule ∧ moved.selection = publication.firing.selection ∧
            moved.fuel = nextFuel ∧ moved.target.present = publication.firing.target.present := by
  obtain ⟨publication, budget, _meaning⟩ := two_private_reads_have_one_actual_native_publication occupied firstFuel
  obtain ⟨permutation, aligned⟩ := ContextualPairFrames.exists_scope_relocation
    publication.firing.selection occupied reserved
  obtain ⟨moved, rule, selection, _outputs, _reuse, nextBudget, physical⟩ :=
    publication.firing.relocate_exists _ reserved permutation aligned nextFuel
  exact ⟨publication, budget, permutation, aligned, moved, rule, selection, nextBudget, physical⟩

theorem incompatible_source_information_has_no_model :
    ¬ ContextualConditionalExecution.Solvable
      (ContextualClauseSourceState.target queries privateRows after nextPlan badSelection).equations := by
  rintro ⟨Future, future, images, modeled⟩
  let witness := witness_of_model queries privateRows result badSelection nextCode after.rows after.equations rfl rfl images modeled
  exact bad_row_never_matches future witness.capture witness.previous _
    ((witness.read ⟨1, by decide +kernel⟩).matches privateRows result)

theorem incompatible_read_has_no_actual_native_firing (occupied : Finset Nat) :
    ¬ ∃ firing : ContextualConditionalExecution.Firing
        (ContextualClauseFrames.bank badBody.native.bindingLocals badBody.native.bindingLocals) (badBody.native.nativeBindingState occupied),
      firing.rule = badBody.producer.rule ∧ firing.selection = badBody.native.bindingSelection := by
  rintro ⟨firing, rule, selection⟩
  have shapes : badBody.ShapesHold := by
    apply (Schedule.shapes_segment _ _).mpr
    constructor
    · exact (firstPart.admitted_characterization.mp the_mixed_body_is_admitted.1).1
    · apply (ContextualSourceSchedules.Schedule.shapes_snoc
        (ContextualSourceSchedules.Schedule.nil after) queries nextPlan badSelection).mpr
      constructor
      · intro shape member
        cases member
      · exact ⟨by decide +kernel, by decide +kernel, rfl, rfl, rfl⟩
  have resources := (CompiledSchedule.compile_condition_iff ContextualSourceSchedules.Schedule.unitLabel
    badBody.commits before.present).mp both_bodies_have_available_resources.2
  have consistent := firing.admitted.solvable
  rw [rule, selection] at consistent
  apply incompatible_source_information_has_no_model
  exact (badBody.native.native_binding_solvable_iff shapes resources occupied badBody.producer.values []).mp consistent

end Mixed

namespace DormantEntry

open ContextualConditionalTemplateOriginControls

theorem an_unused_incompatible_entry_does_not_block_the_actual_firing (occupied : Finset Nat) (fuel : Nat) :
    ∃ publication : sourceBody.NativePublication occupied,
      publication.firing.fuel = fuel ∧
        ContextualWorldComparison.Equivalent after (generator _) publication.projection publication.producerCaller := by
  have parts := sourceBody.admitted_characterization.mp source_body_admitted
  obtain ⟨publication, budget⟩ := sourceBody.realize_native_publication parts.1 parts.2.1 parts.2.2.1 occupied fuel
  exact ⟨publication, budget, publication.world_equivalent parts.1 parts.2.1⟩

theorem the_actual_result_keeps_the_incompatible_entry_local {occupied : Finset Nat}
    (publication : sourceBody.NativePublication occupied) {V : Type} (next : V → MetaArity base)
    (candidate : Assignment publication.firing.target.declarations next)
    (modeled : ContextualResidual.Models candidate publication.target.equations)
    (value : Term (signature base next) [] ()) :
    1 ∈ publication.projection.present ∧
      ¬ Matches publication.resultLocals publication.firing.target.declarations candidate value (publication.projection.rows 1) := by
  have parts := sourceBody.admitted_characterization.mp source_body_admitted
  have noBirth : sourceBody.outputBirth 1 = none := by
    apply (sourceBody.outputBirth_none_iff_shapes parts.1 1).mpr
    intro picked member
    change picked ∈ [selection] at member
    have same := List.mem_singleton.mp member
    subst picked
    decide +kernel
  have visible : 1 ∈ after.present := by decide +kernel
  refine ⟨?_, ?_⟩
  · have physical := sourceBody.native.projection_physical occupied publication.firing parts.2.1 publication.selected
      publication.resultLocals publication.target.rows
    change 1 ∈ (sourceBody.native.projectionOf occupied publication.firing publication.resultLocals
      publication.target.rows).present
    rw [physical]
    exact visible
  · intro matched
    have sourceModel := sourceBody.native.producer_projected_model occupied publication.firing sourceBody.producer.values
      publication.authored publication.selected candidate modeled
    apply the_unused_row_remains_incompatible next (Assignment.compose candidate publication.producerCaller) sourceModel value
    apply (sourceBody.retained_entry_instances parts.1 1 noBirth next
      (Assignment.compose candidate publication.producerCaller) value).mpr
    exact (publication.row_matches_source parts.1 parts.2.1 candidate value 1 visible).mp matched

end DormantEntry

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalTemplateNativeControls
