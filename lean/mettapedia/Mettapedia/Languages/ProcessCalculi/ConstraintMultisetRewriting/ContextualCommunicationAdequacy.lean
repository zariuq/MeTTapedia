import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualCommunicationProfiles
import Mettapedia.OSLF.Syntax.RhoScopedParallelSourceAdequacy

/-!
# Scoped rho/CMR adequacy with one shared interpretation of every occurrence

An interpreted firing retains its original source root, an ordinary CMR step,
and one model of the complete result equation store. Its observed endpoints
are related by the independently defined source event relation.

Conversely every source event lifts from any normalized physical occurrence
representation, provided its existing equations hold at the identity model.
The lift constructs distinct takes and fresh outputs through the existing
occurrence supply. It retains normalized output, so the representation
invariant is available for subsequent steps.

Contextual closure is the source's declared parallel reaction permission.
The source equations include name quote/drop; admitting operational process
Drop remains a separate choice of rule profile. Event identities and physical
selection order are not quotiented into the endpoint comparison.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualCommunicationAdequacy

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open RhoSchema RhoQuotationClassFibres
open RhoScopedParallelInventory RhoScopedEventPresheaf
open ContextualCommunicationProfiles
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

variable {admitted : RhoScopedParallelEvents.SourceRule → Prop} {context : Ctx sig}

local instance : DecidableEq (Process context) := Classical.decEq _

/-- Existing CMR execution, with the exact admitted source origin and the
shared interpretation needed by its source-class observation. -/
def InterpretedStep (admitted : RhoScopedParallelEvents.SourceRule → Prop)
    (assignment : Sub sig context context)
    (before after : Configuration (Process context) (Occurrence context)) : Prop :=
  ∃ root : Root admitted context,
    ConstraintMultisetRewriting.Step (action context) label (instanceRule root) before after ∧
      (action context).Models assignment after.equations

theorem selected_firing_no_invention (root : Root admitted context)
    (assignment : Sub sig context context)
    {before : Configuration (Process context) (Occurrence context)} {selection : Selection (Occurrence context)}
    (valid : selection.Valid (action context) label (instanceRule root) before)
    (solved : (action context).Models assignment (selection.result label (instanceRule root) before).equations) :
    RhoScopedParallelEvents.Step (rules := RhoScopedParallelEvents.sourceRules) (admitted := admitted)
      (observe assignment before.present)
      (observe assignment (selection.result label (instanceRule root) before).present) := by
  obtain ⟨frame, sourceRead, targetRead, _reads⟩ :=
    PositiveResourceProjection.observed_frame (action context) rfl valid solved
  have sourceClass := congrArg assemble sourceRead
  have targetClass := congrArg assemble targetRead
  rw [assemble_add, assemble_mapped_take] at sourceClass
  rw [assemble_add, assemble_mapped_produce] at targetClass
  apply (RhoScopedParallelEvents.step_iff_root_surrounding _ _).mpr
  refine ⟨root.map assignment, assemble frame, ?_, ?_⟩
  · rw [RhoScopedParallelEvents.Root.source_map]
    exact sourceClass.trans (join_commutes _ _)
  · rw [RhoScopedParallelEvents.Root.target_map]
    exact targetClass.trans (join_commutes _ _)

theorem InterpretedStep.no_invention {assignment : Sub sig context context}
    {before after : Configuration (Process context) (Occurrence context)}
    (executed : InterpretedStep admitted assignment before after) :
    RhoScopedParallelEvents.Step (rules := RhoScopedParallelEvents.sourceRules) (admitted := admitted)
      (observe assignment before.present) (observe assignment after.present) := by
  obtain ⟨root, ⟨selection, valid, rfl⟩, solved⟩ := executed
  exact selected_firing_no_invention root assignment valid solved

theorem source_step_has_firing (source target : Process context)
    (before : Configuration (Process context) (Occurrence context))
    (background : (action context).Models (action context).identity before.equations)
    (represents : labels label before.present = normalized source)
    (event : RhoScopedParallelEvents.Step (rules := RhoScopedParallelEvents.sourceRules)
      (admitted := admitted) source target) :
    ∃ after : Configuration (Process context) (Occurrence context),
      InterpretedStep admitted (action context).identity before after ∧
        labels label after.present = normalized target := by
  obtain ⟨root, surrounding, sourceShape, targetShape⟩ :=
    (RhoScopedParallelEvents.step_iff_root_surrounding source target).mp event
  have identity : (action context).apply (action context).identity = id := by
    funext process
    exact (action context).apply_identity process
  have labelsFixed : PositiveResourceProjection.realized (action context)
      (action context).identity (label (context := context)) = label := by
    funext occurrence
    exact (action context).apply_identity _
  have sourceFrame : labels (PositiveResourceProjection.realized (action context)
      (action context).identity label) before.present = normalized surrounding +
        ((instanceRule root).take.map ((action context).apply (action context).identity) : Multiset (Process context)) := by
    rw [labelsFixed, identity, List.map_id, instance_take, represents, sourceShape, normalized_join]
    exact add_comm _ _
  obtain ⟨selection, valid, solved, targetRead⟩ :=
    PositiveResourceProjection.lift_no_read_frame (action context) (action context).identity label rfl
      IndexedOccurrences.supply (instanceRule root) rfl rfl before background
      ((action context).models_nil _) (normalized surrounding) sourceFrame
  refine ⟨selection.result label (instanceRule root) before,
    ⟨root, ⟨selection, valid, rfl⟩, solved⟩, ?_⟩
  rw [labelsFixed, identity, List.map_id, instance_produce] at targetRead
  rw [targetRead, targetShape, normalized_join]
  exact add_comm _ _

/-- Exact source-event support from a declared normalized occurrence store. -/
theorem source_step_iff_firing (source target : Process context)
    (before : Configuration (Process context) (Occurrence context))
    (background : (action context).Models (action context).identity before.equations)
    (represents : labels label before.present = normalized source) :
    RhoScopedParallelEvents.Step (rules := RhoScopedParallelEvents.sourceRules) (admitted := admitted)
      source target ↔
      ∃ after : Configuration (Process context) (Occurrence context),
        InterpretedStep admitted (action context).identity before after ∧
          labels label after.present = normalized target := by
  constructor
  · exact source_step_has_firing source target before background represents
  · rintro ⟨after, executed, targetRead⟩
    have event := executed.no_invention
    rw [observe_identity_of_normalized before.present source represents,
      observe_identity_of_normalized after.present target targetRead] at event
    exact event

theorem every_source_step_has_occurrence_execution (source target : Process context)
    (event : RhoScopedParallelEvents.Step (rules := RhoScopedParallelEvents.sourceRules)
      (admitted := admitted) source target) :
    ∃ before after : Configuration (Process context) (Occurrence context),
      before.equations = [] ∧ labels label before.present = normalized source ∧
      InterpretedStep admitted (action context).identity before after ∧
      labels label after.present = normalized target := by
  obtain ⟨world, represented⟩ := every_source_class_has_occurrences source
  let before : Configuration (Process context) (Occurrence context) := ⟨[], world⟩
  obtain ⟨after, executed, targetRead⟩ := source_step_has_firing source target before
    ((action context).models_nil _) represented event
  exact ⟨before, after, rfl, represented, executed, targetRead⟩

/-- The same admitted source event remains executable under every declared
parallel surrounding process, including an open ambient continuation. -/
theorem parallel_plugging (source target surrounding : Process context)
    (event : RhoScopedParallelEvents.Step (rules := RhoScopedParallelEvents.sourceRules)
      (admitted := admitted) source target)
    (before : Configuration (Process context) (Occurrence context))
    (background : (action context).Models (action context).identity before.equations)
    (represents : labels label before.present = normalized (join source surrounding)) :
    ∃ after : Configuration (Process context) (Occurrence context),
      InterpretedStep admitted (action context).identity before after ∧
        labels label after.present = normalized (join target surrounding) :=
  source_step_has_firing _ _ before background represents
    (RhoScopedParallelEvents.step_join event surrounding)

theorem substitution_plugging {destination : Ctx sig}
    (change : Sub sig context destination) (source target : Process context)
    (event : RhoScopedParallelEvents.Step (rules := RhoScopedParallelEvents.sourceRules)
      (admitted := admitted) source target) :
    ∃ before after : Configuration (Process destination) (Occurrence destination),
      before.equations = [] ∧ labels label before.present = normalized (bindQ change source) ∧
      InterpretedStep admitted (action destination).identity before after ∧
      labels label after.present = normalized (bindQ change target) :=
  every_source_step_has_occurrence_execution _ _ (RhoScopedParallelEvents.step_substitution change event)

/-- At closed context the comparison reaches the existing declared
parallel source reduction relation, including source equation closure. -/
theorem closed_parallel_source_iff (source target : Term sig [] Srt.pr)
    (before : Configuration (Process []) (Occurrence []))
    (background : (action []).Models (action []).identity before.equations)
    (represents : labels label before.present = normalized (RhoEquationConstructorControls.project source)) :
    RhoSchema.ParallelStepModE source target ↔
      ∃ after : Configuration (Process []) (Occurrence []),
        InterpretedStep RhoScopedParallelEvents.withReflection (action []).identity before after ∧
          labels label after.present = normalized (RhoEquationConstructorControls.project target) := by
  rw [RhoScopedParallelSourceAdequacy.parallelStepModE_iff_event]
  exact source_step_iff_firing _ _ before background represents

/-- The source representation retains the whole incoming equation store;
identity is one shared model of it, not a reset before the next event. -/
def Represents (state : Configuration (Process context) (Occurrence context)) (process : Process context) : Prop :=
  (action context).Models (action context).identity state.equations ∧
    labels label state.present = normalized process

theorem InterpretedStep.retains_model
    {before after : Configuration (Process context) (Occurrence context)}
    (executed : InterpretedStep admitted (action context).identity before after) :
    (action context).Models (action context).identity after.equations := by
  obtain ⟨root, step, modeled⟩ := executed
  exact modeled

/-- Source paths compose through the actual occurrence states returned by
the previous firings. Every old equation remains present and satisfied. -/
theorem source_path_has_firings (source target : Process context)
    (before : Configuration (Process context) (Occurrence context))
    (represented : Represents before source)
    (path : Relation.ReflTransGen
      (RhoScopedParallelEvents.Step (rules := RhoScopedParallelEvents.sourceRules) (admitted := admitted)) source target) :
    ∃ after, Relation.ReflTransGen (InterpretedStep admitted (action context).identity) before after ∧
      Represents after target := by
  induction path with
  | refl => exact ⟨before, .refl, represented⟩
  | tail prior event ih =>
      obtain ⟨middle, executed, models, represented⟩ := ih
      obtain ⟨after, firing, targetRead⟩ := source_step_has_firing _ _ middle models represented event
      exact ⟨after, executed.tail firing, firing.retains_model, targetRead⟩

theorem interpreted_path_no_invention
    {before after : Configuration (Process context) (Occurrence context)}
    (path : Relation.ReflTransGen (InterpretedStep admitted (action context).identity) before after) :
    Relation.ReflTransGen
      (RhoScopedParallelEvents.Step (rules := RhoScopedParallelEvents.sourceRules) (admitted := admitted))
      (observe (action context).identity before.present) (observe (action context).identity after.present) := by
  induction path with
  | refl => exact .refl
  | tail prior event ih => exact ih.tail event.no_invention

/-- Finite reachability for the declared intrinsic source profile. This
does not identify semantic COMM substitution with ordinary substitution or
turn the optional free-Drop profile into the paper-faithful rho core. -/
theorem source_path_iff_firings (source target : Process context)
    (before : Configuration (Process context) (Occurrence context))
    (represented : Represents before source) :
    Relation.ReflTransGen
      (RhoScopedParallelEvents.Step (rules := RhoScopedParallelEvents.sourceRules) (admitted := admitted)) source target ↔
    ∃ after, Relation.ReflTransGen (InterpretedStep admitted (action context).identity) before after ∧
      Represents after target := by
  constructor
  · exact source_path_has_firings source target before represented
  · rintro ⟨after, executed, _, targetRead⟩
    have sourcePath := interpreted_path_no_invention executed
    rw [observe_identity_of_normalized before.present source represented.2,
      observe_identity_of_normalized after.present target targetRead] at sourcePath
    exact sourcePath

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualCommunicationAdequacy
