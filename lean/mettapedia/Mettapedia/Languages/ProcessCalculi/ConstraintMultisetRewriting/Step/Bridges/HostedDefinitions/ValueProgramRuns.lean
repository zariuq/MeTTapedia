import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.ValueProgram
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.Completeness

/-!
# Exact successful value-worker runs of the compiled program

The actual program cannot continue after its done reply. Combined with phase
isolation, this interprets every successful worker execution, including runs
that were not selected by the forward compiler.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.ValueWorker

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation
open SourceLanguage.Elaboration
open NativeTypesOnTheStep.Computing

theorem no_step_at_done {dev : Definitions.Development} (built : Compiled dev)
    (datum next : MClosed) : ¬ ProgramBinders.Rewrites built.rules.get (doneC datum) next := by
  rintro ⟨index, environment, matched, _⟩
  have headed := literalHead_instantiate
    ((built.rules.get index).assign environment (ProgramBinders.ground MSig))
    (built.separated.lhs index)
  rw [matched, literalHead_include] at headed
  exact active_done_distinct (Option.some.inj headed).symm

def CompletedInvariant (original current : MClosed) : Prop :=
  Invariant original current ∨ ∃ value : Tower.Tm 0,
    DirectedAnswers.Value value ∧ original = encodeTm value ∧ current = doneC (encodeTm value)

theorem program_runs_preserve {dev : Definitions.Development} (built : Compiled dev)
    {original first last : MClosed} (before : CompletedInvariant original first)
    (run : RuleInstances.Steps built.rules first last) : CompletedInvariant original last := by
  induction run with
  | refl => exact before
  | tail _ edge ih =>
      rcases ih with invariant | finished
      · exact program_step_preserves built invariant edge
      · obtain ⟨value, _, _, rfl⟩ := finished
        exact False.elim (no_step_at_done built _ _ edge)

theorem invariant_not_done (original datum : MClosed) : ¬ Invariant original (doneC datum) := by
  rintro (checking | returning)
  · obtain ⟨term, stack, same, _, _⟩ := checking
    simp [doneC, valueC, activeC, DataEmbedding.nodeC_eq_iff] at same
    exact active_done_distinct same.1.symm
  · obtain ⟨term, stack, _, same, _, _⟩ := returning
    simp [doneC, resumeC, activeC, DataEmbedding.nodeC_eq_iff] at same
    exact active_done_distinct same.1.symm

theorem compiled_success_reflects {dev : Definitions.Development} (built : Compiled dev)
    (datum result : MClosed)
    (run : RuleInstances.Steps built.rules (valueC datum finishContinuation) (doneC result)) :
    result = datum ∧ ∃ value : Tower.Tm 0, DirectedAnswers.Value value ∧ result = encodeTm value := by
  have after := program_runs_preserve built (.inl (initialized datum)) run
  rcases after with invariant | finished
  · exact False.elim (invariant_not_done _ _ invariant)
  · obtain ⟨value, isValue, original, reply⟩ := finished
    have payload : result = encodeTm value := by
      simpa [doneC, DataEmbedding.nodeC_eq_iff] using reply
    exact ⟨payload.trans original.symm, value, isValue, payload⟩

theorem compiled_success_iff {dev : Definitions.Development} (built : Compiled dev)
    (datum result : MClosed) :
    RuleInstances.Steps built.rules (valueC datum finishContinuation) (doneC result) ↔
      result = datum ∧ ∃ value : Tower.Tm 0, DirectedAnswers.Value value ∧ result = encodeTm value := by
  constructor
  · exact compiled_success_reflects built datum result
  · rintro ⟨rfl, value, isValue, rfl⟩
    exact (DriverRewrites.value_runs (fun _ member => Completeness.driver_member built member)
      isValue finishContinuation).trans
        (.single (DriverRewrites.finish (fun _ member => Completeness.driver_member built member) _))

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.ValueWorker

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.ValueWorker.compiled_success_iff
