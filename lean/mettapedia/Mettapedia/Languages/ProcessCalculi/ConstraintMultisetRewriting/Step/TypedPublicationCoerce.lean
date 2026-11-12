import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.TypedPublicationExecution
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.TypedPublicationOutputControls

/-!
# The actual coerce schema publishes its learned type

The source declares the original value x : X and requests Ground. Its tell
equates x : X with g : Ground. The certified concrete answer is supplied
directly, without a classical ideal settler. Both source admission and the
published frame, knowledge, occurrence and typed value are checked.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.Coerce

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta DependentFull DependentFull.Controls
open ProgrammingOnTheStep.Refinement
open OutputControls

def schema : Schema setting.levels Nat baseState.frame where
  helpers := coerceFiring.helpers
  takes := []
  reads := []
  outputs := [.value coerceOutput]
  tells := coerceFiring.tells
  guards := []
  queries := []

def pick : Pick schema := ⟨⟨[], [], [8]⟩, rfl⟩

theorem compiled_is_actual_coerce : schema.compile pick = coerceFiring := rfl

def application : Application setting.levels Nat baseState :=
  ⟨schema, pick, point, toGround, .principal NativeTypesOnTheStep.Coerce.toGround_principal⟩

theorem source_admitted : schema.Admits pick := by
  apply application.basis.native_checks_iff.mp
  have existing := NativeTypesOnTheStep.Coerce.coerce_admitsAfterMatch
  refine ⟨⟨List.nodup_nil, List.nodup_singleton _, rfl, rfl⟩,
    existing.2.1, existing.2.2.1, existing.2.2.2, ?_⟩
  intro output member
  obtain rfl := List.mem_singleton.mp member
  exact coerce_answer_license

theorem native_admitted : (realizationStep setting.levels Nat).Admits application :=
  (realization_admits_iff application).mpr source_admitted

def published : State Tower.rules Nat := application.sourceResult source_admitted

theorem actual_result_is_published :
    (realizationStep setting.levels Nat).result application native_admitted = published :=
  realization_result application source_admitted

theorem published_frame : published.frame = point := rfl

theorem published_occurrences : published.present = {8} := by decide

theorem published_type : (published.label 8).1.code = ground := rfl

theorem published_value : (published.label 8).2.code = .var ⟨0, by decide⟩ := rfl

theorem published_knowledge : published.knowledge =
    (frames setting.levels).applyStore toGround coerceFiring.information := rfl

theorem learned_typing_is_a_real_extension :
    (realizationStep setting.levels Nat).Admits application ∧
      ¬ (DependentFull.step setting.levels Nat).Admits coerceFiring :=
  ⟨native_admitted, coerce_refused⟩

/-- Removing the source information cannot be masked by a vacuous output
check: identity is a model of the empty information and does not type x at Ground. -/
theorem missing_information_refuses :
    ¬ coerceOutput.Uniform setting.levels ([] : EquationStore (TotalTerm triple)) := by
  intro uniform
  have typed := coerceOutput.raw_typed (𝟙 triple) (uniform triple (𝟙 triple) (Frames.models_nil _))
  rw [NativeTypesOnTheStep.Make.reindex_id'] at typed
  exact coerce_not_frame_typed typed

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.Coerce

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.Coerce.source_admitted
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.Coerce.actual_result_is_published
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.Coerce.learned_typing_is_a_real_extension
