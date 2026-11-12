import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.TypedPublicationRealization
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentFullControls

/-!
# Exact residual information is not merely transported source information

An exact refinement introduces X : U0 with the equation X = Ground, while
retaining an old value p : Ground. Every old model extends and its p is
unchanged. The residual equation nevertheless restricts the new variable:
dropping it would admit target interpretations that the update excluded.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.ResidualControls

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta DependentFull DependentFull.Controls

abbrev target := extend point (smallUniverse point)

def typeVariable : TotalTerm target :=
  ⟨smallUniverse target, ⟨.var 0, Derivable.var 0⟩⟩

def groundCode : TotalTerm target :=
  ⟨smallUniverse target, ⟨ground, ground_typed _⟩⟩

def residual : EquationStore (TotalTerm target) := [(typeVariable, groundCode)]

def update : ContextualDependentUpdate.Update setting.levels ([] : EquationStore (TotalTerm point)) where
  target := target
  answer := projectionHom point (smallUniverse point)
  remaining := residual
  sound := fun _ _ _ => Frames.models_nil _
  complete := by
    intro observer substitution _
    let expanded := pair substitution (⟨ground, ground_typed _⟩ : Term observer ((smallUniverse point).reindex substitution))
    refine ⟨expanded, ?_, ?_⟩
    · intro equation member
      obtain rfl := List.mem_singleton.mp member
      exact ((frames setting.levels).equivalence observer).refl _
    · intro term
      apply act_equal_of_substEq setting.levels
      refine ⟨substitution.typed, fun index => ?_⟩
      fin_cases index
      exact Derivable.refl (substitution.typed 0)

def oldValue : TotalTerm point := ⟨groundType point, ⟨.var 0, Derivable.var 0⟩⟩
def before : State Tower.rules Nat := ⟨point, [], ∅, fun _ => oldValue⟩

def schema : Schema setting.levels Nat point where
  helpers := .nil _
  takes := []
  reads := []
  outputs := [.value (Output.unchanged oldValue)]
  tells := []
  guards := []
  queries := []

def pick : Pick schema := ⟨⟨[], [], [9]⟩, rfl⟩

theorem licenses : ∀ output ∈ schema.outputs, output.At update.answer := by
  intro output member
  obtain rfl := List.mem_singleton.mp member
  exact NativeTypesOnTheStep.below_refl_of_isType (oldValue.1.reindex update.answer).isType

def application : Application setting.levels Nat before :=
  ⟨schema, pick, target, update.answer,
    Basis.residual (state := before) (schema := schema) (pick := pick) update licenses⟩

theorem admitted : (realizationStep setting.levels Nat).Admits application := by
  refine ⟨⟨⟨List.nodup_nil, List.nodup_singleton _, rfl, rfl⟩, ?_⟩, ?_,
    ⟨point, 𝟙 point, Frames.models_nil _⟩, ?_⟩
  · intro output member
    obtain rfl := List.mem_singleton.mp member
    exact NativeTypesOnTheStep.below_refl_of_isType (oldValue.1.reindex update.answer).isType
  · apply (DependentFull.enabled_iff application.compile).mpr
    decide
  · intro observer substitution _
    exact ⟨(fun _ member => nomatch member), (fun _ member => nomatch member)⟩

abbrev published := (realizationStep setting.levels Nat).result application admitted

theorem residual_is_actually_retained : published.knowledge = residual := rfl

theorem old_value_is_retained : (published.label 9).2.code = .var ⟨1, by decide⟩ := rfl

theorem identity_does_not_solve_residual : ¬ (frames setting.levels).Models (𝟙 target) residual := by
  intro models
  have equality := (models (typeVariable, groundCode) (List.mem_singleton_self _)).2
  change Equal Tower.rules target.raw (.var 0) ground (.head (.sort Tower.zero)) at equality
  have typeEquality : TypeEq Tower.rules target.raw (.var 0) ground := ⟨_, .sort _, equality⟩
  have neutral : Neutral (TowerModel.roles (L := Nat)) (.var 0 : Tower.Tm 2) := .var 0
  exact (TypeEq.neutral_form (TowerModel.facts (L := Nat)) typeEquality target.formed neutral
    (.inl ⟨_, rfl⟩)).not_former.1 _ rfl

theorem dropping_residual_adds_target_models :
    (frames setting.levels).Models (𝟙 target)
      ((frames setting.levels).applyStore update.answer ([] : EquationStore (TotalTerm point))) ∧
      ¬ (frames setting.levels).Models (𝟙 target) published.knowledge :=
  ⟨Frames.models_nil _, identity_does_not_solve_residual⟩

theorem all_original_models_still_covered {observer : Context Tower.rules}
    (substitution : observer ⟶ point) :
    ∃ further : observer ⟶ target, (frames setting.levels).Models further published.knowledge ∧
      UnificationWithLevels.Agree (frames setting.levels) substitution (further ≫ update.answer) :=
  application.basis.covers substitution (Frames.models_nil _)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.ResidualControls

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.ResidualControls.dropping_residual_adds_target_models
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.ResidualControls.all_original_models_still_covered
