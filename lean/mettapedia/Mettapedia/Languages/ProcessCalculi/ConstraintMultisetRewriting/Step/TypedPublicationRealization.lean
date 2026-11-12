import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.TypedPublicationSchemas
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentUpdate

/-!
# Realization of typed schema publications

A candidate retains either a certified principal answer or an exact solver
update whose outputs already type at the residual frame. The step uses the dependent firing's resource effects and the
existing settled-state construction. Its output checks use retained declared
types or the template filling conditions. Source publication is specified directly from schema
rows, chosen occurrences and the supplied substitution.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta DependentFull
open MeTTaCalculus.OccurrenceCommits (Enabled fire)

variable {Head : Type} {rules : Rules Head}
variable {L : Type} [UniverseLevel.LevelOrder L] (levels : LevelModel rules L) (O : Type)

/-- Two justified realization routes. A principal answer makes output checks
complete. An exact residual update can publish already-licensed outputs while
retaining its unresolved constraints; it need not have a principal answer. -/
inductive Basis {state : State rules O} (schema : Schema levels O state.frame) (pick : Pick schema) :
    {target : Context rules} → (target ⟶ schema.helpers.frame) → Type where
  | principal {target : Context rules} {answer : target ⟶ schema.helpers.frame}
      (certificate : (frames levels).Principal (schema.compile pick).information answer) : Basis schema pick answer
  | residual (update : ContextualDependentUpdate.Update levels (schema.compile pick).information)
      (licensed : ∀ output ∈ schema.outputs, output.At update.answer) : Basis schema pick update.answer

/-- An actual selected schema with a certified realization route. -/
structure Application (state : State rules O) where
  schema : Schema levels O state.frame
  pick : Pick schema
  target : Context rules
  answer : target ⟶ schema.helpers.frame
  basis : Basis levels O schema pick answer

variable {levels O}

namespace Basis

variable {state : State rules O} {schema : Schema levels O state.frame} {pick : Pick schema}
  {target : Context rules} {answer : target ⟶ schema.helpers.frame}

/-- A residual realization keeps the actual residual store, including
constraints on target variables that are not determined by the answer map. -/
def knowledge : Basis levels O schema pick answer → EquationStore (TotalTerm target)
  | .principal _ => (frames levels).applyStore answer (schema.compile pick).information
  | .residual update _ => update.remaining

theorem sound (basis : Basis levels O schema pick answer) {context : Context rules}
    (further : context ⟶ target) (solved : (frames levels).Models further basis.knowledge) :
    (frames levels).Models (further ≫ answer) (schema.compile pick).information := by
  cases basis with
  | principal certificate => exact (Frames.models_applyStore _ _ _).mp solved
  | residual update _ => exact update.sound context further solved

/-- Every original solution is covered, in the same observing context, by
a solution of the actual published knowledge and an agreeing interpretation. -/
theorem covers (basis : Basis levels O schema pick answer) {context : Context rules}
    (solution : context ⟶ schema.helpers.frame)
    (solved : (frames levels).Models solution (schema.compile pick).information) :
    ∃ further : context ⟶ target, (frames levels).Models further basis.knowledge ∧
      UnificationWithLevels.Agree (frames levels) solution (further ≫ answer) := by
  cases basis with
  | principal certificate =>
      obtain ⟨further, agree⟩ := certificate.factors context solution solved
      exact ⟨further, (Frames.models_applyStore _ _ _).mpr
        ((UnificationWithLevels.models_of_agree agree _).mp solved), agree⟩
  | residual update _ => exact update.complete context solution solved

theorem outputs_iff (basis : Basis levels O schema pick answer) :
    (∀ output ∈ schema.outputs, output.Uniform levels (schema.compile pick).information) ↔
      ∀ output ∈ schema.outputs, output.At answer := by
  cases basis with
  | principal certificate =>
      constructor
      · intro uniform output member
        exact (output.uniform_iff_at_principal levels certificate).mp (uniform output member)
      · intro licensed output member
        exact (output.uniform_iff_at_principal levels certificate).mpr (licensed output member)
  | residual update licensed =>
      refine ⟨fun _ => licensed, fun _ output member context substitution solved => ?_⟩
      obtain ⟨further, _, agree⟩ := update.complete context substitution solved
      exact (output.at_agree levels agree).mpr
        (output.at_precompose (licensed output member) further)

theorem native_checks_iff [DecidableEq O] (basis : Basis levels O schema pick answer) :
    schema.NativeChecks pick answer ↔ schema.Admits pick := by
  unfold Schema.NativeChecks Schema.Admits
  rw [DependentFull.enabled_iff, schema.erase.compile_made pick,
    schema.helpers.solvable_iff_arguments levels,
    schema.helpers.entails_iff_arguments levels, ← basis.outputs_iff,
    ← schema.output_models_iff pick]
  simp_rw [schema.erase.compile_information_iff]
  rfl

end Basis

namespace Schema

variable {state : State rules O} (schema : Schema levels O state.frame) (pick : Pick schema)
  {target : Context rules} (answer : target ⟶ schema.helpers.frame)

theorem made_typed (licensed : ∀ output ∈ schema.outputs, output.At answer) :
    ∀ made ∈ (schema.compile pick).makes, (made.2.reindex answer).WellTyped := by
  intro made member
  obtain ⟨output, inside, same⟩ := List.mem_map.mp (List.of_mem_zip member).2
  rw [← same]
  exact output.raw_typed answer (licensed output inside)

/-- Direct source publication, with the answer frame, transported source
constraints, resource update and explicitly substituted output rows. -/
def publish [DecidableEq O] (licensed : ∀ output ∈ schema.outputs, output.At answer) : State rules O where
  frame := target
  knowledge := (frames levels).applyStore answer (schema.erase.information pick)
  present := (state.present \ pick.1.taken.toFinset) ∪ pick.1.fresh.toFinset
  label := relabel
    (fun occurrence => ((state.label occurrence).reindex schema.helpers.weaken).reindex answer)
    ((pick.1.fresh.zip schema.outputs).map fun pair => (pair.1, pair.2.raw.reindex answer))
    (by
      intro made member
      obtain ⟨pair, inside, rfl⟩ := List.mem_map.mp member
      exact pair.2.raw_typed answer (licensed pair.2 (List.of_mem_zip inside).2))

theorem settled_makes :
    NativeTypesOnTheStep.settledMakes levels (schema.compile pick) answer =
      (pick.1.fresh.zip schema.outputs).map (fun pair => (pair.1, pair.2.raw.reindex answer)) := by
  simp only [NativeTypesOnTheStep.settledMakes, compile, DependentProgram.Schema.compile,
    Schema.erase, List.zip_map_right, List.map_map, Function.comp_def, Prod.map, id_eq]

theorem publication_eq_settled [DecidableEq O]
    (licensed : ∀ output ∈ schema.outputs, output.At answer) :
    schema.publish pick answer licensed =
      NativeTypesOnTheStep.settledState levels (schema.compile pick) ⟨target, answer⟩
        (schema.made_typed pick answer licensed) := by
  unfold publish NativeTypesOnTheStep.settledState
  congr 1
  · change _ = (state.present \ pick.1.taken.toFinset) ∪ (schema.compile pick).made.toFinset
    rw [schema.erase.compile_made]
  · apply NativeTypesOnTheStep.relabel_congr
    · rfl
    · exact (schema.settled_makes pick answer).symm

end Schema

namespace Application

variable {state : State rules O} (application : Application levels O state)

abbrev compile : Firing levels state := application.schema.compile application.pick

def Shapes : Prop := application.schema.SelectionShape application.pick ∧
  ∀ output ∈ application.schema.outputs, output.At application.answer

theorem made_typed (shape : application.Shapes) :
    ∀ made ∈ application.compile.makes, (made.2.reindex application.answer).WellTyped :=
  application.schema.made_typed application.pick application.answer shape.2

theorem source_licenses (admitted : application.schema.Admits application.pick) :
    ∀ output ∈ application.schema.outputs, output.At application.answer := by
  exact application.basis.outputs_iff.mp
    ((application.schema.output_models_iff application.pick).mp admitted.2.2.2.2)

def sourceResult [DecidableEq O] (admitted : application.schema.Admits application.pick) : State rules O :=
  { application.schema.publish application.pick application.answer (application.source_licenses admitted) with
    knowledge := application.basis.knowledge }

end Application

variable (levels O) [DecidableEq O]

/-- The concrete publication step: standard resource effects with an explicit
certified settlement. No solver or typing-decision oracle is installed here. -/
def realizationStep : Interface.Step (frames levels) O (State rules O) (Application levels O) where
  frame state := state.frame
  knowledge state := state.knowledge
  present state := state.present
  selection application := application.compile.selection
  target application := application.schema.helpers.frame
  extension application := application.schema.helpers.weaken
  information application := application.compile.information
  information_refines application := (DependentFull.step levels O).information_refines application.compile
  Shapes application := application.Shapes
  Admits {state} application := application.Shapes ∧
    Enabled (fun _ : O => ()) state.present (application.compile.selection.commit (T := Unit)) ∧
    (frames levels).Solvable application.compile.information ∧
    (frames levels).Entails application.compile.information (fun _ substitution => application.compile.Holds substitution)
  admitted_prepares _ admitted := ⟨admitted.1, admitted.2.1, admitted.2.2.1⟩
  preparedResult application prepared :=
    { NativeTypesOnTheStep.settledState levels application.compile
      ⟨application.target, application.answer⟩ (application.made_typed prepared.1) with
      knowledge := application.basis.knowledge }
  present_preparedResult _ _ := rfl
  preparedSettle application _ := application.answer
  result_refines application _ _ further solved := application.basis.sound further solved

variable {levels O}

theorem realization_admits_iff {state : State rules O} (application : Application levels O state) :
    (realizationStep levels O).Admits application ↔ application.schema.Admits application.pick := by
  have checks := application.basis.native_checks_iff
  change _ ↔ _ at checks
  rw [← checks]
  change ((application.schema.SelectionShape application.pick ∧ _) ∧ _) ↔ _
  unfold Schema.NativeChecks
  tauto

theorem realization_result {state : State rules O} (application : Application levels O state)
    (admitted : application.schema.Admits application.pick) :
    (realizationStep levels O).result application ((realization_admits_iff application).mpr admitted) =
      application.sourceResult admitted := by
  dsimp only [realizationStep, Step.result, Application.sourceResult,
    NativeTypesOnTheStep.settledState, Schema.publish]
  congr 1
  · change (state.present \ application.pick.1.taken.toFinset) ∪ application.compile.made.toFinset = _
    rw [application.schema.erase.compile_made]
  · apply NativeTypesOnTheStep.relabel_congr
    · rfl
    · exact application.schema.settled_makes application.pick application.answer

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.realization_admits_iff
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.realization_result
