import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualNativeProgramResult
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualScheduleControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSymbolicCountControls

/-!
# Complete constructed firings: computation, original guards and counts

The witnesses use the uniform producer's rule, outputs, flags and query
list. They do not supply a hand-written native result. Negative cases
reject incompatible answer reuse and an earlier guard that a later tell
would otherwise repair. A count instance retains its own clause's tell.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualNativeProgramControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualConjunctiveQueries ContextualConditionalRows ContextualPredicateQueryAdmission ContextualSourceSchedules
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

namespace Earlier

open ContextualPrefixPublicationControls
open ContextualScheduleControls.EarlierSchema (body admitted guardedBody)

local instance : DecidableEq base.Srt := inferInstanceAs (DecidableEq Unit)
local instance (sort : base.Srt) : DecidableEq (base.Op sort) := inferInstanceAs (DecidableEq DataOperator)

theorem an_actual_compiled_body_preserves_the_earlier_schema (fuel : Nat) :
    ∃ observed : WithQueries body.native.guardNativeBank (body.native.nativeBindingState ∅),
      observed.firing.rule = body.producer.rule ∧ observed.firing.selection = body.native.bindingSelection ∧
        observed.firing.outputs = body.producer.outputs ∅ ∧ observed.firing.reusable = body.producerReusable ∧
        observed.firing.fuel = fuel ∧ observed.queries = body.producer.queries ∅ ∧
        ContextualWorldComparison.Equivalent afterSecond (generator afterSecond.declarations)
          (body.native.producerProjection ∅ observed.firing) (body.native.producerCaller ∅ observed.firing) ∧
        ∀ (Future : Type) (future : Future → MetaArity base) (candidate : Assignment observed.firing.target.declarations future),
          Matches (ContextualPublication.privateFamily body.native.guardNativeBank observed.firing.update.declaration)
            observed.firing.target.declarations candidate (box (symbol 2))
            (observed.firing.target.rows (body.native.producerPhysical 0)) := by
  obtain ⟨observed, rule, selection, outputs, flags, budget, queries⟩ :=
    (body.producer.source_iff_native_body_admission ∅ fuel).mp admitted
  refine ⟨observed, rule, selection, outputs, flags, budget, queries,
    body.producer_world_equivalent ∅ observed.firing admitted rule selection outputs flags, ?_⟩
  intro Future future candidate
  apply (body.producer_row_matches_source ∅ observed.firing admitted rule selection outputs flags
    candidate (box (symbol 2)) 0 (by decide +kernel)).mpr
  exact the_earlier_schema_still_matches_two future _

theorem a_later_tell_cannot_make_the_whole_native_body_fire (fuel : Nat) :
    ¬ ∃ observed : WithQueries guardedBody.native.guardNativeBank (guardedBody.native.nativeBindingState ∅),
      observed.firing.rule = guardedBody.producer.rule ∧ observed.firing.selection = guardedBody.native.bindingSelection ∧
        observed.firing.outputs = guardedBody.producer.outputs ∅ ∧ observed.firing.reusable = guardedBody.producerReusable ∧
        observed.firing.fuel = fuel ∧ observed.queries = guardedBody.producer.queries ∅ := by
  intro native
  exact ContextualScheduleControls.EarlierSchema.a_later_binding_does_not_repair_the_compiled_earlier_check
    (guardedBody.compile_exact.mpr ((guardedBody.producer.source_iff_native_body_admission ∅ fuel).mpr native))

end Earlier

namespace Computed

open ContextualClausePublication.BinderControls (DataOperator dataSignature base locals captures)
open ContextualComputedJoinControls (world)
open ContextualScheduleControls.ComputedBody (body result admitted conflictingBody)

local instance : DecidableEq base.Srt := inferInstanceAs (DecidableEq Unit)
local instance (sort : base.Srt) : DecidableEq (base.Op sort) := by
  change DecidableEq (DataOperator ⊕ Operator (SchematicReach.spaceDeclaration dataSignature () (Name := Nat)) sort)
  infer_instance

theorem the_computed_join_and_repeated_read_are_one_native_firing (fuel : Nat) :
    ∃ observed : WithQueries body.native.guardNativeBank (body.native.nativeBindingState ∅),
      observed.firing.rule = body.producer.rule ∧ observed.firing.selection = body.native.bindingSelection ∧
        observed.firing.outputs = body.producer.outputs ∅ ∧ observed.firing.reusable = body.producerReusable ∧
        observed.firing.fuel = fuel ∧ observed.queries = body.producer.queries ∅ ∧
        ContextualWorldComparison.Equivalent result (generator result.declarations)
          (body.native.producerProjection ∅ observed.firing) (body.native.producerCaller ∅ observed.firing) ∧
        (body.native.producerProjection ∅ observed.firing).present = {0, 1, 2, 4, 5} := by
  obtain ⟨observed, rule, selection, outputs, flags, budget, queries⟩ :=
    (body.producer.source_iff_native_body_admission ∅ fuel).mp admitted
  refine ⟨observed, rule, selection, outputs, flags, budget, queries,
    body.producer_world_equivalent ∅ observed.firing admitted rule selection outputs flags, ?_⟩
  rw [body.native.projection_physical ∅ observed.firing (body.admitted_characterization.mp admitted).2.1 selection _ _]
  decide +kernel

theorem incompatible_reuse_has_no_compiled_firing (fuel : Nat) :
    ¬ ∃ observed : WithQueries conflictingBody.native.guardNativeBank (conflictingBody.native.nativeBindingState ∅),
      observed.firing.rule = conflictingBody.producer.rule ∧ observed.firing.selection = conflictingBody.native.bindingSelection ∧
        observed.firing.outputs = conflictingBody.producer.outputs ∅ ∧ observed.firing.reusable = conflictingBody.producerReusable ∧
        observed.firing.fuel = fuel ∧ observed.queries = conflictingBody.producer.queries ∅ := by
  intro native
  exact ContextualScheduleControls.ComputedBody.the_conflicting_body_is_refused
    (conflictingBody.compile_exact.mpr ((conflictingBody.producer.source_iff_native_body_admission ∅ fuel).mpr native))

end Computed

namespace Count

open ContextualPrefixPublicationControls
open ContextualNativeGuardControls (entry)

local instance : DecidableEq base.Srt := inferInstanceAs (DecidableEq Unit)
local instance (sort : base.Srt) : DecidableEq (base.Op sort) := inferInstanceAs (DecidableEq DataOperator)

def plan : ContextualPublication.Plan (Term (signature base actor) [] ()) :=
  ⟨{ContextualNativeGuardControls.OwnEquations.plan.rule with checks := [.count (box (symbol 1)) 1]}, [true], rfl⟩

abbrev middle := ContextualClauseSourceState.target none none entry plan firstSelection
abbrev result := ContextualClauseSourceState.target none firstLocals middle secondPlan secondSelection

def body : Schedule base Nat [] () entry result :=
  .snoc (.snoc (.nil entry) none plan firstSelection) none secondPlan secondSelection

theorem admitted : body.Admitted := by
  have shapes : body.ShapesHold := ContextualNativeGuardControls.OwnEquations.shapes
  have resources : Executable Schedule.unitLabel entry.present body.commits := ContextualNativeGuardControls.OwnEquations.resources
  have consistent : ContextualConditionalExecution.Solvable result.equations := ContextualNativeGuardControls.OwnEquations.consistent
  apply body.admitted_characterization.mpr
  refine ⟨shapes, resources, consistent, ?_⟩
  apply (body.native.entry_guards_iff shapes resources).mp
  intro cut member
  obtain ⟨index, rfl⟩ := List.mem_iff_get.mp member
  have bound : index.val < 2 := index.isLt
  have choices : index.val = 0 ∨ index.val = 1 := by omega
  rcases choices with value | value
  · have equal : index = ⟨0, by decide +kernel⟩ := Fin.ext value
    subst index
    intro check selected
    have only : check = .count (box (symbol 1)) 1 := List.mem_singleton.mp selected
    subst check
    exact ContextualSymbolicCountControls.source_count_is_one
  · have equal : index = ⟨1, by decide +kernel⟩ := Fin.ext value
    subst index
    intro check selected
    cases selected

theorem the_own_equation_count_has_one_constructed_firing (fuel : Nat) :
    ∃ observed : WithQueries body.native.guardNativeBank (body.native.nativeBindingState ∅),
      observed.firing.rule = body.producer.rule ∧ observed.firing.selection = body.native.bindingSelection ∧
        observed.firing.outputs = body.producer.outputs ∅ ∧ observed.firing.reusable = body.producerReusable ∧
        observed.firing.fuel = fuel ∧ observed.queries = body.producer.queries ∅ ∧
        ContextualWorldComparison.Equivalent result (generator result.declarations)
          (body.native.producerProjection ∅ observed.firing) (body.native.producerCaller ∅ observed.firing) := by
  obtain ⟨observed, rule, selection, outputs, flags, budget, queries⟩ :=
    (body.producer.source_iff_native_body_admission ∅ fuel).mp admitted
  exact ⟨observed, rule, selection, outputs, flags, budget, queries,
    body.producer_world_equivalent ∅ observed.firing admitted rule selection outputs flags⟩

end Count

namespace InternalFreshness

open ContextualPrefixPublicationControls

local instance : DecidableEq base.Srt := inferInstanceAs (DecidableEq Unit)
local instance (sort : base.Srt) : DecidableEq (base.Op sort) := inferInstanceAs (DecidableEq DataOperator)

abbrev world (initial : Finset Nat) : ContextualClauseSourceState.World none Nat [] () :=
  ⟨Empty, inferInstance, none, [], initial, fun _ => ofStored none none (.shared (symbol 9))⟩

def makePlan : ContextualPublication.Plan (Term (signature base (queryFamily none none)) [] ()) :=
  ⟨⟨[], [], [], [], [symbol 7]⟩, [true], rfl⟩
def makeSelection : Selection Nat := ⟨[], [], [0]⟩
def takeSelection : Selection Nat := ⟨[0], [], []⟩

abbrev middle (initial : Finset Nat) := ContextualClauseSourceState.target none none (world initial) makePlan makeSelection
abbrev middleLocals (initial : Finset Nat) := ContextualClauseSourceState.resultLocals none none (world initial)

def takePlan (initial : Finset Nat) :
    ContextualPublication.Plan (Term (signature base (queryFamily none (middle initial).declarations)) [] ()) :=
  ⟨⟨[symbol 7], [], [], [], []⟩, [], rfl⟩

abbrev result (initial : Finset Nat) :=
  ContextualClauseSourceState.target none (middleLocals initial) (middle initial) (takePlan initial) takeSelection

def body (initial : Finset Nat) : Schedule base Nat [] () (world initial) (result initial) :=
  .snoc (.snoc (.nil (world initial)) none makePlan makeSelection) none (takePlan initial) takeSelection

theorem the_net_effect_alone_accepts_the_invalid_prefix :
    Enabled OccurrenceAllocationRenaming.label ((world {0}).present.image Sum.inl) (body {0}).net.effect := by
  decide +kernel

theorem the_full_resource_condition_refuses_the_invalid_prefix :
    ¬ Executable Schedule.unitLabel (world {0}).present (body {0}).commits := by
  intro executable
  have condition : (body {0}).native.sourceResourceCondition.Holds Schedule.unitLabel (world {0}).present :=
    (CompiledSchedule.compile_condition_iff _ _ _).mpr executable
  have absent : (0 : Nat) ∈ (body {0}).native.sourceResourceCondition.absent := by decide +kernel
  have present : (0 : Nat) ∈ (world {0}).present := by decide +kernel
  exact Finset.disjoint_left.mp condition.2.2.1 absent present

theorem the_native_absence_query_sees_the_conflict (candidate : Candidate (body {0}).native.guardNativeFamily) :
    ¬ (((body {0}).native.producerAbsentQuery).atSolution candidate).Holds
      (nativeLabels (body {0}).native.guardNativeBank ((body {0}).native.nativeBindingState ∅))
      ((body {0}).native.nativeBindingState ∅).present := by
  intro observed
  have member : ContextualNativeBodies.Body.entryIdentity 0 ∈ regionOf
      (nativeLabels (body {0}).native.guardNativeBank ((body {0}).native.nativeBindingState ∅))
      ((body {0}).native.nativeBindingState ∅).present ((body {0}).native.producerAbsentQuery.region candidate) := by
    apply mem_regionOf.mpr
    refine ⟨by decide +kernel, ?_⟩
    change decide (ContextualNativeBodies.Body.entryIdentity 0 ∈ (body {0}).native.sourceResourceCondition.absent.image ContextualNativeBodies.Body.entryIdentity) = true
    exact decide_eq_true (Finset.mem_image_of_mem ContextualNativeBodies.Body.entryIdentity (by decide +kernel))
  change regionOf (nativeLabels (body {0}).native.guardNativeBank ((body {0}).native.nativeBindingState ∅))
    ((body {0}).native.nativeBindingState ∅).present ((body {0}).native.producerAbsentQuery.region candidate) = ∅ at observed
  rw [observed] at member
  exact Finset.notMem_empty _ member

theorem the_invalid_prefix_has_no_complete_native_firing (fuel : Nat) :
    ¬ ∃ observed : WithQueries (body {0}).native.guardNativeBank ((body {0}).native.nativeBindingState ∅),
      observed.firing.rule = (body {0}).producer.rule ∧ observed.firing.selection = (body {0}).native.bindingSelection ∧
        observed.firing.outputs = (body {0}).producer.outputs ∅ ∧ observed.firing.reusable = (body {0}).producerReusable ∧
        observed.firing.fuel = fuel ∧ observed.queries = (body {0}).producer.queries ∅ := by
  intro native
  have source := ((body {0}).producer.source_iff_native_body_admission ∅ fuel).mpr native
  exact the_full_resource_condition_refuses_the_invalid_prefix ((body {0}).admitted_characterization.mp source).2.1

theorem the_empty_entry_body_is_admitted : (body ∅).Admitted := by
  apply (body ∅).admitted_characterization.mpr
  refine ⟨?_, ?_, ?_, ?_⟩
  · erw [Schedule.shapes_snoc, Schedule.shapes_snoc]
    exact ⟨⟨by simp [Schedule.ShapesHold, Schedule.shapes],
      ⟨by decide +kernel, by decide +kernel, rfl, rfl, rfl⟩⟩,
      ⟨by decide +kernel, by decide +kernel, rfl, rfl, rfl⟩⟩
  · exact .cons (by decide +kernel) (.cons (by decide +kernel) (.nil _))
  · refine ⟨(result ∅).Names, (result ∅).declarations, generator (result ∅).declarations, ?_⟩
    change ContextualResidual.Models (generator (result ∅).declarations)
      [(observe (symbol (decl := (result ∅).declarations) 7), observe (symbol 7))]
    intro equation member
    have same := List.mem_singleton.mp member
    subst equation
    rfl
  · erw [Schedule.cuts_snoc, Schedule.cuts_snoc]
    exact ⟨⟨by simp [Schedule.CutsHold, Schedule.cuts], by intro check member; cases member⟩,
      by intro check member; cases member⟩

theorem the_valid_internal_make_take_has_a_complete_firing (fuel : Nat) :
    ∃ observed : WithQueries (body ∅).native.guardNativeBank ((body ∅).native.nativeBindingState ∅),
      observed.firing.rule = (body ∅).producer.rule ∧ observed.firing.selection = (body ∅).native.bindingSelection ∧
        observed.firing.outputs = (body ∅).producer.outputs ∅ ∧ observed.firing.reusable = (body ∅).producerReusable ∧
        observed.firing.fuel = fuel ∧ observed.queries = (body ∅).producer.queries ∅ :=
  ((body ∅).producer.source_iff_native_body_admission ∅ fuel).mp the_empty_entry_body_is_admitted

end InternalFreshness

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualNativeProgramControls
