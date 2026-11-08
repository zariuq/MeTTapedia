import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualCensusPublication
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualQueryAnswersControls

/-! # Actual complete tables publish duplicate values and invalidate on arrivals -/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualCensusPublication.Controls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualConjunctiveQueries ContextualConjunctiveControls
open ContextualQueryAnswersControls
open ContextualSelectionViews.Controls (base)
open ContextualWorldScopeLedger

local instance : DecidableEq base.Srt := inferInstanceAs (DecidableEq Unit)
local instance (sort : base.Srt) : DecidableEq (base.Op sort) :=
  inferInstanceAs (DecidableEq ContextualFrame.Controls.Operator)

def scopes (_ : Nat) : Finset Nat := ∅
def inventory : Inventory locals captures (O := Nat) [] () := ⟨⟨[], domain⟩, alternatives, [], []⟩
def before : ContextualExecution.Endpoint locals Nat [] () where
  Names := Nat
  equality := inferInstance
  declarations := captures
  scopes := scopes
  occupied := ∅
  inventory := inventory
  covered := (coveredWorld_iff locals captures scopes ∅ inventory).mpr (by decide +kernel)

def request : Request queries locals before where
  patterns := single
  template := patternA
  budget := budget
  complete := the_actual_table_is_complete

local instance : DecidableEq (ContextualAnswerFamilies.Names request.Variables) := request.variableEquality

noncomputable def order : List request.Index := request.entries.attach.toList

theorem exactly_three_source_tuples : request.entries.card = 3 := by
  have injective : Set.InjOn (fun chosen : Fin request.patterns.length → Nat => chosen ⟨0, by decide⟩)
      {chosen | chosen ∈ request.entries} := by
    intro first _ second _ same
    exact (tuple_eq first).trans ((congrArg tuple same).trans (tuple_eq second).symm)
  have image := every_physical_alternative_is_retained
  change request.entries.image (fun chosen => chosen ⟨0, by decide⟩) = domain at image
  rw [← Finset.card_image_of_injOn injective, image]
  decide +kernel

theorem order_length : order.length = 3 := by
  simpa only [order, Finset.length_toList, Finset.card_attach] using exactly_three_source_tuples

/-- All three source tuples emit the same value. Their physical multiplicity
is not the support cardinality of their projected values. -/
theorem the_projected_values_are_equal (first second : request.Index) :
    request.packedValue first = request.packedValue second := rfl

theorem publication_exists :
    ∃ publication : request.Publication order,
      publication.firing.selection = ContextualSchemaBatch.selection [90, 91, 92] := by
  apply request.realize_publication order (List.Perm.refl _) [90, 91, 92] (by decide +kernel) (by decide +kernel)
    (by simpa only [List.length_cons, List.length_nil] using order_length.symm)
  · exact ⟨Nat, captures, generator captures, by intro equation member; cases member⟩
  · intro equation member
    cases member

theorem one_atomic_firing_installs_all_three :
    ∃ publication : request.Publication order,
      publication.firing.target.inventory.configuration.present = domain ∪ {90, 91, 92} ∧
      publication.firing.selection.made.Nodup := by
  obtain ⟨publication, selected⟩ := publication_exists
  refine ⟨publication, ?_, publication.firing.execution.admitted.output_distinct⟩
  rw [publication.firing.physical_result, selected]
  simp [ContextualSchemaBatch.selection, Selection.commit,
    MeTTaCalculus.OccurrenceCommits.fire, ContextualSchemaBatch.prepared,
    ContextualTemplatePublication.prepareEndpoint, before, inventory,
    ContextualPublication.extendInventory]

theorem a_late_matching_schema_invalidates_the_table :
    ¬ request.CompleteAt [] alternatives (insert 4 domain) := by
  apply request.arrival_invalidates [] alternatives (insert 4 domain) (tuple 4) ⟨0, by decide⟩
  · decide +kernel
  · intro _
    exact Finset.mem_insert_self _ _
  · obtain ⟨Next, next, candidate, model⟩ := job_has_a_model 4
    have source := (ContextualResidual.models_observeProblem candidate _).mp model
    have split := ContextualConjunctiveModels.joint_model_gives_caller_and_match queries locals captures
      candidate [] single alternatives (tuple 4) source
    exact ⟨Next, next, ContextualConjunctiveModels.caller queries locals captures candidate, split⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualCensusPublication.Controls
