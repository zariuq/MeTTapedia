import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.TypedPublicationRealization

/-!
# Conservativity for outputs already typed in their frame

An old schema's judged output annotations become retained source annotations.
The identity residual update keeps all information, including nonprincipal
constraints. No principal answer is required for this embedding.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta DependentFull

variable {Head : Type} {rules : Rules Head}
variable {L : Type} [UniverseLevel.LevelOrder L] {levels : LevelModel rules L} {O : Type}

namespace FrameTyped

section Schema

variable {context : Context rules} (original : DependentProgram.Schema levels O context)
  (typed : ∀ made ∈ original.makes, made.WellTyped)

abbrev schema : Schema levels O context where
  helpers := original.helpers
  takes := original.takes
  reads := original.reads
  outputs := original.makes.attach.map fun made => .value (Output.unchanged (made.1.row (typed made.1 made.2)))
  tells := original.tells
  guards := original.guards
  queries := original.queries

theorem erased_outputs : ((schema original typed).outputs.map Code.raw) = original.makes := by
  simp only [schema, List.map_map]
  change original.makes.attach.map (fun made => (Output.unchanged (made.1.row (typed made.1 made.2))).raw) = _
  simpa only [Output.unchanged, Output.raw, Make.row] using List.attach_map_subtype_val original.makes

theorem erase_eq : (schema original typed).erase = original := by
  cases original
  simp only [Schema.erase, schema]
  congr 1
  exact erased_outputs _ typed

abbrev pick (choice : DependentProgram.Pick original) : Pick (schema original typed) :=
  ⟨choice.1, by simpa only [schema, Schema.erase, List.length_map, List.length_attach] using choice.2⟩

end Schema

variable {state : State rules O} (original : DependentProgram.Schema levels O state.frame)
  (typed : ∀ made ∈ original.makes, made.WellTyped)

theorem compile_eq (choice : DependentProgram.Pick original) :
    (schema original typed).compile (pick original typed choice) = original.compile choice := by
  dsimp only [Schema.compile, DependentProgram.Schema.compile, Schema.erase, schema, pick]
  congr 1
  exact congrArg (List.zip choice.1.fresh) (erased_outputs original typed)

theorem output_license (output : Code original.helpers.frame)
    (member : output ∈ (schema original typed).outputs) : output.At (𝟙 original.helpers.frame) := by
  obtain ⟨made, _, rfl⟩ := List.mem_map.mp member
  exact Output.unchanged_uniform levels (made.1.row (typed made.1 made.2)) [] _ _ (Frames.models_nil _)

abbrev application (choice : DependentProgram.Pick original) : Application levels O state :=
  ⟨schema original typed, pick original typed choice, original.helpers.frame, 𝟙 _,
    .residual (ContextualDependentUpdate.Update.pending levels _)
      (output_license original typed)⟩

theorem admits_iff [DecidableEq O] (choice : DependentProgram.Pick original) :
    (realizationStep levels O).Admits (application original typed choice) ↔ original.Admits choice := by
  rw [realization_admits_iff]
  have uniform : ∀ output ∈ (schema original typed).outputs,
      output.Uniform levels ((schema original typed).compile (pick original typed choice)).information := by
    intro output member target substitution _
    have license := output.at_precompose (output_license original typed output member) substitution
    simpa only [Category.comp_id] using license
  have outputModels := ((schema original typed).output_models_iff (pick original typed choice)).mpr uniform
  change ((schema original typed).SelectionShape _ ∧ _ ∧ _ ∧ _ ∧ _) ↔ _
  unfold DependentProgram.Schema.Admits DependentProgram.Schema.Shapes
  change ((_ ∧ _ ∧ _ ∧ _) ∧ _ ∧ _ ∧ _ ∧ _) ↔ ((_ ∧ _ ∧ _ ∧ _ ∧ _) ∧ _ ∧ _ ∧ _)
  tauto

theorem result_eq [DecidableEq O] (choice : DependentProgram.Pick original)
    (admitted : original.Admits choice) :
    (realizationStep levels O).result (application original typed choice)
        ((admits_iff original typed choice).mpr admitted) = original.publish choice admitted.1 := by
  have sourceAdmitted := (realization_admits_iff (application original typed choice)).mp
    ((admits_iff original typed choice).mpr admitted)
  rw [realization_result (application original typed choice) sourceAdmitted]
  dsimp only [Application.sourceResult, application, Schema.publish,
    DependentProgram.Schema.publish, Basis.knowledge, ContextualDependentUpdate.Update.pending]
  congr 1
  apply NativeTypesOnTheStep.relabel_congr
  · funext occurrence
    exact reindex_id _
  · rw [← (schema original typed).settled_makes (pick original typed choice) (𝟙 _)]
    rw [NativeTypesOnTheStep.settledMakes, NativeTypesOnTheStep.map_reindex_id]
    exact congrArg (List.zip choice.1.fresh) (erased_outputs original typed)

end FrameTyped

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.FrameTyped.admits_iff
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.FrameTyped.result_eq
