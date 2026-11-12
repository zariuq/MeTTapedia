import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentProgramControls

/-!
# One dependent schema retains distinct type instantiations

The schema introduces `A : U0` and `x : A`, then publishes `x : A` without
equating A to a predetermined type. Both a Ground value and a function
value are models of the same application and its published result. Their
types are unequal in the actual cumulative theory. The application retains
that solution family in its residual context.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentProgram.PolymorphismControls

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentTwins DependentFull
open Controls
open DependentFull.Controls (point ground arrow ground_typed arrow_typed smallUniverse)

def pairHelpers (Γ : Context Tower.rules) : Helpers Γ :=
  .cons (smallUniverse Γ) (.cons (valueType Γ) (.nil _))

def publishedRow (Γ : Context Tower.rules) : TotalTerm (valueContext Γ) :=
  ⟨(valueType Γ).reindex (projectionHom (typeContext Γ) (valueType Γ)),
    newest (typeContext Γ) (valueType Γ)⟩

def polymorphicSchema (Γ : Context Tower.rules) : Schema levels Nat Γ where
  helpers := pairHelpers Γ
  takes := []
  reads := []
  makes := [Make.ofRow (publishedRow Γ)]
  tells := []
  guards := [(publishedRow Γ, publishedRow Γ)]
  queries := []

def groundArguments {Γ : Context Tower.rules} (baseMap : point ⟶ Γ) :
    (pairHelpers Γ).Arguments baseMap :=
  ⟨typeArgument baseMap, valueArgument baseMap, PUnit.unit⟩

def groundModel {Γ : Context Tower.rules} (baseMap : point ⟶ Γ) : point ⟶ valueContext Γ :=
  (pairHelpers Γ).instantiate baseMap (groundArguments baseMap)

def arrowArguments {Γ Δ : Context Tower.rules} (baseMap : Δ ⟶ Γ) :
    (pairHelpers Γ).Arguments baseMap :=
  ⟨⟨arrow, arrow_typed _⟩,
    ⟨.lam (.var 0), .lamIntro (arrow_typed _) (.sort _) (Derivable.var 0)⟩,
    PUnit.unit⟩

def arrowModel {Γ Δ : Context Tower.rules} (baseMap : Δ ⟶ Γ) : Δ ⟶ valueContext Γ :=
  (pairHelpers Γ).instantiate baseMap (arrowArguments baseMap)

def table : Program levels Nat := fun Γ => [polymorphicSchema Γ]

def candidate : Candidate table start where
  ruleIndex := ⟨0, by decide⟩
  pick := ⟨⟨[], [], [7]⟩, rfl⟩

theorem every_argument_models (args : (pairHelpers start.frame).Arguments (𝟙 point)) :
    candidate.schema.ModelsAt candidate.pick (𝟙 point) args := by
  refine ⟨Frames.models_nil _, ?_, ?_, Frames.models_nil _⟩
  · intro pattern occurrence member
    cases member
  · intro pattern occurrence member
    cases member

theorem admits_polymorphic_application : candidate.schema.Admits candidate.pick := by
  refine ⟨⟨List.nodup_nil, List.nodup_singleton _, rfl, rfl, ?_⟩, ?_,
    ⟨point, 𝟙 point, groundArguments (𝟙 point), every_argument_models _⟩, ?_⟩
  · intro made member
    obtain rfl := List.mem_singleton.mp member
    exact Make.ofRow_wellTyped _
  · refine ⟨(fun _ member => nomatch member), (fun _ member => nomatch member),
      (fun _ member => nomatch member), ?_⟩
    intro occurrence member
    obtain rfl := List.mem_singleton.mp member
    decide
  · intro Δ baseMap args _
    refine ⟨?_, fun _ member => nomatch member⟩
    intro equation member
    obtain rfl := List.mem_singleton.mp member
    exact ((frames levels).equivalence Δ).refl _

def permission : {state : State Tower.rules Nat} → Candidate table state → Prop := fun _ => True

def execution : table.Execution permission start :=
  .cons candidate admits_polymorphic_application True.intro
    (.nil (candidate.schema.publish candidate.pick admits_polymorphic_application.1))

theorem one_actual_event : execution.toRun.word.length = 1 := by
  rw [Program.Execution.toRun_word]
  rfl

theorem published_occurrences : execution.last.present = {0, 7} := by decide

theorem published_label : execution.last.label 7 = publishedRow start.frame := rfl

theorem both_arguments_survive :
    (frames levels).Models (groundModel (𝟙 point)) execution.last.knowledge ∧
    (frames levels).Models (arrowModel (𝟙 point)) execution.last.knowledge := by
  constructor
  · change (frames levels).Models
      (candidate.schema.helpers.instantiate (𝟙 point) (groundArguments (𝟙 point)))
      (candidate.schema.information (s := start) candidate.pick)
    rw [← candidate.schema.compile_information (s := start) candidate.pick]
    exact (candidate.schema.compile_information_iff (s := start) candidate.pick _ _).mpr
      (every_argument_models _)
  · change (frames levels).Models
      (candidate.schema.helpers.instantiate (𝟙 point) (arrowArguments (𝟙 point)))
      (candidate.schema.information (s := start) candidate.pick)
    rw [← candidate.schema.compile_information (s := start) candidate.pick]
    exact (candidate.schema.compile_information_iff (s := start) candidate.pick _ _).mpr
      (every_argument_models _)

theorem published_ground_value :
    ((execution.last.label 7).reindex (groundModel (𝟙 point))).2.code = .var 0 := rfl

theorem published_function_value :
    ((execution.last.label 7).reindex (arrowModel (𝟙 point))).2.code = .lam (.var 0) := rfl

/-- The retained alternatives differ in the actual theory's type equality,
not merely in their printed syntax. -/
theorem retained_types_are_distinct :
    ¬ (frames levels).E
      ((execution.last.label 7).reindex (groundModel (𝟙 point)))
      ((execution.last.label 7).reindex (arrowModel (𝟙 point))) := by
  intro same
  have types := same.1
  change TypeEq Tower.rules point.raw ground arrow at types
  exact DependentFull.Controls.ground_arrow_clash point.formed types

/-- A closed initial state needs no present row and no Ground inhabitant.
Its total unused label map denotes the closed type Ground as a term of U0. -/
def closedStart : State Tower.rules Nat where
  frame := empty Tower.rules
  knowledge := []
  present := ∅
  label := fun _ => ⟨smallUniverse _, ⟨ground, ground_typed _⟩⟩

def closedCandidate : Candidate table closedStart where
  ruleIndex := ⟨0, by decide⟩
  pick := ⟨⟨[], [], [7]⟩, rfl⟩

theorem closed_application_admitted : closedCandidate.schema.Admits closedCandidate.pick := by
  refine ⟨⟨List.nodup_nil, List.nodup_singleton _, rfl, rfl, ?_⟩, ?_,
    ⟨empty Tower.rules, 𝟙 _, arrowArguments (𝟙 _), ?_⟩, ?_⟩
  · intro made member
    obtain rfl := List.mem_singleton.mp member
    exact Make.ofRow_wellTyped _
  · refine ⟨(fun _ member => nomatch member), (fun _ member => nomatch member),
      (fun _ member => nomatch member), ?_⟩
    intro occurrence _
    simp [closedStart]
  · refine ⟨Frames.models_nil _, ?_, ?_, Frames.models_nil _⟩
    · intro pattern occurrence member
      cases member
    · intro pattern occurrence member
      cases member
  · intro Δ baseMap args _
    refine ⟨?_, fun _ member => nomatch member⟩
    intro equation member
    obtain rfl := List.mem_singleton.mp member
    exact ((frames levels).equivalence Δ).refl _

def closedExecution : table.Execution permission closedStart :=
  .cons closedCandidate closed_application_admitted True.intro
    (.nil (closedCandidate.schema.publish closedCandidate.pick closed_application_admitted.1))

theorem closed_run_is_one_actual_event : closedExecution.toRun.word.length = 1 := by
  rw [Program.Execution.toRun_word]
  rfl

/-- The published function has a model in the empty context, with its
actual residual equations satisfied and its closed lambda code retained. -/
theorem closed_output_is_realized :
    (frames levels).Models (arrowModel (𝟙 (empty Tower.rules))) closedExecution.last.knowledge ∧
      ((closedExecution.last.label 7).reindex (arrowModel (𝟙 (empty Tower.rules)))).2.code =
        .lam (.var 0) :=
  ⟨Frames.models_nil _, rfl⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentProgram.PolymorphismControls
