import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.ExecutionInvariant
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.Completeness

/-!
# Exact value-reaching results of the finite hosted definition compiler

The equivalence is about may-results of directed reduction. It neither
identifies reduction derivations nor asserts that a chosen evaluation
strategy terminates. Normal results outside the value grammar require a
separate finish profile.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.ExecutionReflection

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization
open SourceLanguage.Elaboration
open NativeTypesOnTheStep.Computing

theorem head_or_value {dev : Definitions.Development} (built : Compiled dev) {initial : Tower.Tm 0}
    {current : MClosed} (represented : ExecutionInvariant.Represents built initial current) :
    closedHead current = some activeTag ∨ ∃ value : Tower.Tm 0,
      StrongNormalization.ReducesStar (Definitions.devPackage dev built.nativeRows) initial value ∧
      DirectedAnswers.Value value ∧ current = doneC (encodeTm value) := by
  cases represented with
  | evaluating term reached => exact .inl rfl
  | searching term reached search =>
      obtain ⟨_, _, _, rfl, _⟩ := search
      exact .inl rfl
  | rooted term reached root =>
      obtain ⟨_, _, _, rfl, _⟩ := root
      exact .inl rfl
  | pending result stack reached helper => exact .inl (HelperPending.head helper)
  | resumingPlug result stack reached => exact .inl rfl
  | plugging term reached reconstruct =>
      obtain ⟨_, _, _, rfl, _⟩ := reconstruct
      exact .inl rfl
  | resuming term reached => exact .inl rfl
  | checking term reached worker =>
      rcases worker with checking | returning
      · obtain ⟨_, _, rfl, _, _⟩ := checking
        exact .inl rfl
      · obtain ⟨_, _, _, rfl, _, _⟩ := returning
        exact .inl rfl
  | finished term reached value => exact .inr ⟨term, reached, value, rfl⟩

theorem success_reflects {dev : Definitions.Development} (built : Compiled dev)
    (initial : Tower.Tm 0) (result : MClosed)
    (run : RuleInstances.Steps built.rules (queryCode initial) (doneC result)) :
    ∃ value : Tower.Tm 0,
      StrongNormalization.ReducesStar (Definitions.devPackage dev built.nativeRows) initial value ∧
      DirectedAnswers.Value value ∧ result = encodeTm value := by
  have represented := ExecutionInvariant.runs built (ExecutionInvariant.initial built initial) run
  rcases head_or_value built represented with impossible | finished
  · exact False.elim (active_done_distinct (Option.some.inj impossible).symm)
  · obtain ⟨value, reached, isValue, same⟩ := finished
    have resultEq : result = encodeTm value := by
      simpa only [doneC, DataEmbedding.nodeC_eq_iff, true_and, List.cons.injEq, and_true] using same
    exact ⟨value, reached, isValue, resultEq⟩

theorem success_iff {dev : Definitions.Development} (built : Compiled dev)
    (initial : Tower.Tm 0) (result : MClosed) :
    RuleInstances.Steps built.rules (queryCode initial) (doneC result) ↔
      ∃ value : Tower.Tm 0,
        StrongNormalization.ReducesStar (Definitions.devPackage dev built.nativeRows) initial value ∧
        DirectedAnswers.Value value ∧ result = encodeTm value := by
  constructor
  · exact success_reflects built initial result
  · rintro ⟨value, reached, isValue, rfl⟩
    exact Completeness.value_reached built reached isValue

theorem encoded_success_iff {dev : Definitions.Development} (built : Compiled dev)
    (initial value : Tower.Tm 0) :
    RuleInstances.Steps built.rules (queryCode initial) (doneC (encodeTm value)) ↔
      StrongNormalization.ReducesStar (Definitions.devPackage dev built.nativeRows) initial value ∧
        DirectedAnswers.Value value := by
  rw [success_iff]
  constructor
  · rintro ⟨actual, reached, isValue, same⟩
    have equal := encodeTm_injective same
    subst actual
    exact ⟨reached, isValue⟩
  · rintro ⟨reached, isValue⟩
    exact ⟨value, reached, isValue, rfl⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.ExecutionReflection
