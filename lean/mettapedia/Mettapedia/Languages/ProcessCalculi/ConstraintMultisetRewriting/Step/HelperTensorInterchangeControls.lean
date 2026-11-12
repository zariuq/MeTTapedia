import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HelperTensorInterchange
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HelperTensorCompositionDomain
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HelperTensorPlanData
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HelperRunObservations
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HelperRunCompositionControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HelperBlockTransportControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.EventTrace

/-!
# Four native contextual blocks and a forbidden output collision

Both components extend declaration scopes. The right component creates a
function-valued helper and its continuation refers to the original context's
forty-two. The native schedules differ, while the actual tensor theorem
relates their complete histories. Reusing a left output identity on the right
is locally admissible and fails the joint tensor's exact domain.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Helpers.TensorInterchangeControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Helpers.Consumer (tiny constant)
open ContextResultControls (placed)

abbrev first := RunCompositionControls.initial
abbrev second := TensorRunsControls.second
abbrev afterSecond := BlockTransportControls.rightRun

def laterLeft : Firing first.last := ⟨2, ([], ()), constant 8, []⟩

theorem later_left_allowed : helperStep.Admits laterLeft :=
  (admits_iff laterLeft).mpr
    ⟨(run_solvable_iff first).mpr Helpers.Consumer.start_solvable, by decide, asks_nil⟩

def afterFirst : helperStep.Run first.last := .cons laterLeft later_left_allowed (.nil _)

theorem before_domain : TensorDomain placed first second :=
  ⟨Or.inr ContextResultControls.placed_solvable,
    (outputsAvoid_iff_disjoint _ _).mpr (by decide),
    (outputsAvoid_iff_disjoint _ _).mpr (by decide)⟩

def before : TensorPlan placed first second := TensorPlan.ofDomain placed first second before_domain

theorem after_domain : TensorDomain (TensorPlan.realize before).target afterFirst afterSecond :=
  ⟨Or.inr (before.target_solvable_iff.mpr ContextResultControls.placed_solvable),
    (outputsAvoid_iff_disjoint _ _).mpr (by decide),
    (outputsAvoid_iff_disjoint _ _).mpr (by decide)⟩

def after : TensorPlan (TensorPlan.realize before).target afterFirst afterSecond :=
  TensorPlan.ofDomain _ afterFirst afterSecond after_domain

theorem whole_domain : TensorDomain placed (first.append afterFirst) (second.append afterSecond) :=
  ⟨Or.inr ContextResultControls.placed_solvable,
    (outputsAvoid_iff_disjoint _ _).mpr (by decide),
    (outputsAvoid_iff_disjoint _ _).mpr (by decide)⟩

def whole : TensorPlan placed (first.append afterFirst) (second.append afterSecond) :=
  before.compose after

def sequential : helperStep.Run placed.state := before.sequentialExecution after
def combined : helperStep.Run placed.state := (TensorPlan.realize whole).execution

def aritySchedule {source : State tiny Nat} (run : helperStep.Run source) : List Nat :=
  (helperWord run).map (fun helper => helper.1.length)

theorem sequential_schedule : aritySchedule sequential = [0, 1, 0, 0] := by
  unfold aritySchedule sequential
  rw [TensorPlan.sequential_helperWord]
  rfl

theorem combined_schedule : aritySchedule combined = [0, 0, 1, 0] := by
  unfold aritySchedule combined
  rw [TensorPlan.helperWord_eq, helperWord_append, helperWord_append]
  rfl

theorem higher_order_declaration : TensorRunsControls.rightFiring.helper = ([()], ()) := rfl

theorem native_interchange : helperTransport.TraceEquiv placed.state sequential combined := before.four_block_compose after

theorem raw_histories_distinct : sequential ≠ combined := by
  intro same
  have equal := congrArg (fun run : helperStep.Run placed.state => aritySchedule run) same
  rw [sequential_schedule, combined_schedule] at equal
  cases equal

abbrev origin := Transport.StateClass.mk helperTransport placed.state
abbrev target := Transport.StateClass.mk helperTransport sequential.last

def sequentialArrow : helperTransport.Arrow origin target := ⟨_, sequential, rfl, rfl⟩
def combinedArrow : helperTransport.Arrow origin target :=
  ⟨_, combined, rfl, (Transport.StateClass.mk_eq_mk_iff helperTransport).mpr native_interchange.same_last.symm⟩

theorem related_arrows : Transport.Arrow.Rel sequentialArrow combinedArrow :=
  ⟨sequential, Transport.Similar.refl _, native_interchange⟩

def schedule (arrow : helperTransport.Arrow origin target) : List Nat := aritySchedule arrow.run

theorem schedule_does_not_descend :
    ¬∃ observe : helperTransport.Trace origin target → List Nat,
      ∀ arrow, observe (Quot.mk _ arrow) = schedule arrow := by
  apply Transport.Trace.no_observation_of_distinguished_related helperTransport schedule sequentialArrow combinedArrow related_arrows
  change aritySchedule sequential ≠ aritySchedule combined
  rw [sequential_schedule, combined_schedule]
  decide

theorem event_count_descends :
    Transport.Trace.eventCount helperTransport (Quot.mk _ sequentialArrow) = 4 ∧
      Transport.Trace.eventCount helperTransport (Quot.mk _ combinedArrow) = 4 := by
  constructor
  · change sequential.word.length = 4
    have length := congrArg List.length sequential_schedule
    simpa only [aritySchedule, helperWord, List.length_map, List.length_cons, List.length_nil] using length
  · change combined.word.length = 4
    have length := congrArg List.length combined_schedule
    simpa only [aritySchedule, helperWord, List.length_map, List.length_cons, List.length_nil] using length

def collidingRight : Firing second.last := ⟨2, ([], ()), constant 99, []⟩

theorem colliding_right_locally_allowed : helperStep.Admits collidingRight :=
  (admits_iff collidingRight).mpr
    ⟨(run_solvable_iff second).mpr ContextResultControls.context_solvable, by decide, asks_nil⟩

def collidingContinuation : helperStep.Run second.last := .cons collidingRight colliding_right_locally_allowed (.nil _)

theorem colliding_whole_refused :
    ¬Nonempty (TensorPlan placed (first.append afterFirst) (second.append collidingContinuation)) := by
  intro plan
  have domain := (tensor_plan_iff_domain _ _ _).mp plan
  have disjoint := (outputsAvoid_iff_disjoint _ _).mp domain.2.2
  exact Finset.disjoint_left.mp disjoint (show 2 ∈ outputs (second.append collidingContinuation) by decide)
    (show 2 ∈ (first.append afterFirst).last.present by decide)

theorem colliding_second_stage_refused :
    ¬Nonempty (TensorPlan (TensorPlan.realize before).target afterFirst collidingContinuation) := by
  rintro ⟨later⟩
  exact colliding_whole_refused ⟨before.compose later⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Helpers.TensorInterchangeControls
