import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.FirstOrderFourBlock
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.CanonicalFirstOrder
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.EventTrace

/-!
# Four actual blocks, distinct schedules and lawful trace observations

Two components each produce two resources. Sequential tensors execute the
order 1,3,2,4; the tensor of the sequential components executes 1,2,3,4.
The actual native runs differ, their interchange is proved, and the existing
trace category rejects a schedule observer while retaining event count.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.FirstOrderNativeRuns.FourBlockControls

open Mettapedia.Logic.LP
open ConstraintMultisetRewriting.Controls (signature A)
open AnnotatedRuns (Firing firstOrder firstOrderTransport Separated)
open AnnotatedRuns.EscapeControls (blank)
open AnnotatedRuns.CanonicalControls (producer producerKey producer_valid_iff producer_equations)

def source : Configuration (Term signature) Nat := ⟨[], ∅⟩
abbrev P := (firstOrder A blank).toStep
abbrev T := firstOrderTransport A blank

def first : P.Run source := .cons (producer 1) ((producer_valid_iff rfl 1).mpr (by decide)) (.nil _)
def second : P.Run source := .cons (producer 3) ((producer_valid_iff rfl 3).mpr (by decide)) (.nil _)

theorem next_first : (producer 2).Valid A blank first.last := by
  apply (producer_valid_iff (C := first.last) ?_ 2).mpr (by decide)
  change ((producer 1).result blank source).equations = []
  rw [producer_equations]
  rfl

theorem next_second : (producer 4).Valid A blank second.last := by
  apply (producer_valid_iff (C := second.last) ?_ 4).mpr (by decide)
  change ((producer 3).result blank source).equations = []
  rw [producer_equations]
  rfl

def afterFirst : P.Run first.last := .cons (producer 2) next_first (.nil _)
def afterSecond : P.Run second.last := .cons (producer 4) next_second (.nil _)

theorem separated : Separated A blank source (sites A blank (first.append afterFirst))
    source (sites A blank (second.append afterSecond)) := by
  refine ⟨executable_of_run A blank _ ⟨Subst.id signature, by simp [source]⟩,
    executable_of_run A blank _ ⟨Subst.id signature, by simp [source]⟩, by decide, ?_, ?_, ?_⟩
  · intro f member
    have cases : f = producer 1 ∨ f = producer 2 := by simpa [sites, first, afterFirst, Step.Run.append, Step.Run.word] using member
    rcases cases with rfl | rfl <;> exact AnnotatedRuns.blindTo_of_plain A blank rfl rfl
  · intro f member
    have cases : f = producer 3 ∨ f = producer 4 := by simpa [sites, second, afterSecond, Step.Run.append, Step.Run.word] using member
    rcases cases with rfl | rfl <;> exact AnnotatedRuns.blindTo_of_plain A blank rfl rfl
  · refine ⟨Subst.id signature, ?_⟩
    intro equation member
    simp [AnnotatedRuns.jointStore, AnnotatedRuns.Firing.added, GuardFreeProcessOrders.added,
      Selection.equations, source, sites, first, second, afterFirst, afterSecond, producer,
      Step.Run.append, Step.Run.word] at member

def blocks := fourBlockOfSeparated A blank first second afterFirst afterSecond separated
def sequential : P.Run (AnnotatedRuns.tensor source source) := sequentialTensor A blank blocks.before blocks.after
def combined : P.Run (AnnotatedRuns.tensor source source) :=
  (blocks.whole.realize (contextualRunInterpretation A blank) (contextualFlip A blank)).execution

theorem sequential_schedule : (sites A blank sequential).map producerKey = [1, 3, 2, 4] := by
  rw [sequential, sites_sequentialTensor]
  rfl

theorem combined_schedule : (sites A blank combined).map producerKey = [1, 2, 3, 4] := by
  rw [combined, tensor_sites, sites_append, sites_append]
  rfl

theorem native_interchange : T.TraceEquiv (AnnotatedRuns.tensor source source) sequential combined := blocks.interchange

theorem raw_schedules_distinct : sequential ≠ combined := by
  intro same
  have equal := congrArg (fun run : P.Run (AnnotatedRuns.tensor source source) =>
    (sites A blank run).map producerKey) same
  rw [sequential_schedule, combined_schedule] at equal
  cases equal

abbrev origin := Transport.StateClass.mk T (AnnotatedRuns.tensor source source)
abbrev target := Transport.StateClass.mk T sequential.last

def sequentialArrow : T.Arrow origin target := ⟨_, sequential, rfl, rfl⟩
def combinedArrow : T.Arrow origin target :=
  ⟨_, combined, rfl, (Transport.StateClass.mk_eq_mk_iff T).mpr native_interchange.same_last.symm⟩

theorem related_arrows : Transport.Arrow.Rel sequentialArrow combinedArrow :=
  ⟨sequential, Transport.Similar.refl _, native_interchange⟩

def schedule (arrow : T.Arrow origin target) : List Nat := (sites A blank arrow.run).map producerKey

theorem schedule_does_not_descend :
    ¬∃ observe : T.Trace origin target → List Nat,
      ∀ arrow, observe (Quot.mk _ arrow) = schedule arrow := by
  apply Transport.Trace.no_observation_of_distinguished_related T schedule sequentialArrow combinedArrow related_arrows
  change (sites A blank sequential).map producerKey ≠ (sites A blank combined).map producerKey
  rw [sequential_schedule, combined_schedule]
  decide

theorem event_count_descends :
    Transport.Trace.eventCount T (Quot.mk _ sequentialArrow) = 4 ∧
      Transport.Trace.eventCount T (Quot.mk _ combinedArrow) = 4 := by
  constructor
  · change sequential.word.length = 4
    have length := congrArg List.length sequential_schedule
    simpa only [List.length_map, List.length_cons, List.length_nil] using length
  · change combined.word.length = 4
    have length := congrArg List.length combined_schedule
    simpa only [List.length_map, List.length_cons, List.length_nil] using length

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.FirstOrderNativeRuns.FourBlockControls
