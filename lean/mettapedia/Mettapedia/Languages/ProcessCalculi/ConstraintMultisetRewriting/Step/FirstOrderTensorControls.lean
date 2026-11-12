import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.FirstOrderContextRuns
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.CoexistenceRunBoundaries

/-!
# Native consumers and refusal controls for the shared tensor contract

The original taker/reader example runs through the generic implementation.
Inconsistent joint tells are rejected. A separate example executes a permitted
consumption of a shared resource, but cannot claim an unchanged context.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.FirstOrderNativeRuns.Controls

open AnnotatedRuns (Firing firstOrder firstOrderTransport)
open ConstraintMultisetRewriting.Controls (signature A)
open AnnotatedRuns.Controls (label taker reader)
open AnnotatedRuns.TensorControls (takerSide readerSide taker_runs reader_runs taker_reader_separated)

abbrev I := contextualRunInterpretation A label
abbrev flip := contextualFlip A label

def first : (firstOrder A label).toStep.Run takerSide := ofExecutable A label _ _ taker_runs
def second : (firstOrder A label).toStep.Run readerSide := ofExecutable A label _ _ reader_runs

def leftPlan : I.Plan (right := readerSide) PUnit.unit first :=
  .cons (I := I) (left := takerSide) (right := readerSide) (place := PUnit.unit)
    (by decide) taker_reader_separated.head_left_valid (.nil _)

def rightPlan : I.Plan (right := first.last) (flip.swap (leftPlan.realize I PUnit.unit first).target) second :=
  .cons (I := I) (left := readerSide) (right := first.last) (place := PUnit.unit)
    (by decide) taker_reader_separated.tail_left.symm.head_left_valid (.nil _)

def plan : I.TensorPlan flip PUnit.unit first second := ⟨leftPlan, rightPlan⟩

def result : I.TensorResult PUnit.unit first second := plan.realize I flip

theorem shared_implementation_has_two_events : result.execution.word.length = 2 := result.length_preserved

def recovered : TensorExecution A label takerSide readerSide [taker] [reader] :=
  tensor_of_separated A label _ _ _ _ taker_reader_separated

theorem recovered_full_word : sites A label recovered.execution = [taker, reader] := recovered.word

theorem shared_implementation_retains_full_word : sites A label result.execution = [taker, reader] :=
  tensor_sites A label plan

theorem shared_implementation_equals_recovered_run : result.execution = recovered.execution := by
  apply sites_injective A label
  exact shared_implementation_retains_full_word.trans recovered_full_word.symm

theorem inconsistent_tells_have_no_native_composite :
    ¬∃ run : (firstOrder A label).toStep.Run
      (AnnotatedRuns.tensor AnnotatedRuns.TensorControls.empty AnnotatedRuns.TensorControls.empty),
        sites A label run = [AnnotatedRuns.TensorControls.tellOne, AnnotatedRuns.TensorControls.tellTwo] := by
  rw [exists_run_iff]
  rintro (empty | executable)
  · cases empty
  · exact AnnotatedRuns.TensorControls.tensor_undefined_by_equations.2.2 executable

theorem overlapping_take_is_permitted :
    (firstOrder A label).Admits (s := AnnotatedRuns.tensor takerSide takerSide) taker := by
  change taker.Valid A label (AnnotatedRuns.tensor takerSide takerSide)
  simpa [AnnotatedRuns.tensor, takerSide] using taker_runs.1

theorem overlapping_take_fails_frame_domain :
    ¬I.domain (left := takerSide) (right := takerSide) PUnit.unit taker := by decide

def interfering_execution : (firstOrder A label).toStep.Run (AnnotatedRuns.tensor takerSide takerSide) :=
  .cons taker overlapping_take_is_permitted (.nil _)

theorem permitted_take_has_no_unchanged_context_iso :
    ¬(firstOrderTransport A label).Same
      (taker.result label (AnnotatedRuns.tensor takerSide takerSide))
      (AnnotatedRuns.tensor (taker.result label takerSide) takerSide) :=
  fun iso => overlapping_take_fails_frame_domain
    ((framing_domain_iff_native_iso A label taker taker_runs.1).mpr iso)

theorem no_unchanged_context_plan :
    ¬Nonempty (I.Plan (right := takerSide) PUnit.unit first) := by
  intro plan
  have checked := (I.plan_iff_checks (right := takerSide) PUnit.unit first).mp plan
  exact overlapping_take_fails_frame_domain checked.1.1

theorem permitted_take_changes_shared_context :
    (taker.result label (AnnotatedRuns.tensor takerSide takerSide)).present ≠
      (AnnotatedRuns.tensor (taker.result label takerSide) takerSide).present := by decide

theorem empty_consistency_distinction :
    (∃ run : Coexistence.RunBoundaries.profile.Run Coexistence.RunBoundaries.joined,
      sites Coexistence.RunBoundaries.action Coexistence.RunBoundaries.label run = []) ∧
    ¬∃ run : Coexistence.RunBoundaries.profile.Run Coexistence.RunBoundaries.joined,
      sites Coexistence.RunBoundaries.action Coexistence.RunBoundaries.label run = [] ∧
        Coexistence.RunBoundaries.action.Consistent Coexistence.RunBoundaries.joined.equations := by
  refine ⟨⟨.nil _, rfl⟩, ?_⟩
  rw [consistent_run_iff]
  exact Coexistence.RunBoundaries.consistent_identity_does_not_exist

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.FirstOrderNativeRuns.Controls
