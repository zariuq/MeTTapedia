import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ComputationExecution

/-!
# Complete finite source computations are realized by actual runs

The proof follows the independent source reduction from its first step.
Fresh occurrences are constructed at each stage; source and target scopes
are aligned explicitly. No source reachability is assumed in the target's
admission or state representation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationProfile

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta DependentFull
open AlgebraicParallel NativeTypesOnTheStep.Computing ConversionCoherence

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
  (qualified : Qualified S) (presentation : SchemaPresentation S.R)

theorem realize_scoped {n : Nat} {before after : Tm Head n} (steps : StepStar S.R before after) :
    ∀ (configuration : Configuration (S := S)), configuration.state.frame.arity = n →
      HEq configuration.code before →
      ∃ execution : Execution qualified presentation configuration, HEq execution.term after := by
  induction steps using Relation.ReflTransGen.head_induction_on with
  | refl =>
      intro configuration same aligned
      exact ⟨.nil configuration, aligned⟩
  | @head before middle first rest ih =>
      intro configuration same aligned
      cases same
      have code : configuration.code = before := eq_of_heq aligned
      subst before
      obtain ⟨instruction, target⟩ := source_complete (presentation := presentation) first
      let next := instruction.next qualified configuration.fresh configuration.fresh_not_present
      have atNext : HEq next.code middle :=
        heq_of_eq ((instruction.next_code qualified configuration.fresh configuration.fresh_not_present).trans target)
      obtain ⟨continuation, endpoint⟩ := ih next rfl atNext
      exact ⟨.cons instruction configuration.fresh configuration.fresh_not_present continuation, endpoint⟩

theorem realize {configuration : Configuration (S := S)} {value : Tm Head configuration.state.frame.arity}
    (steps : StepStar S.R configuration.code value) :
    ∃ execution : Execution qualified presentation configuration, execution.term = value := by
  obtain ⟨execution, endpoint⟩ := realize_scoped qualified presentation steps configuration rfl HEq.rfl
  exact ⟨execution, eq_of_heq endpoint⟩

theorem reaches_iff {configuration : Configuration (S := S)} {value : Tm Head configuration.state.frame.arity} :
    StepStar S.R configuration.code value ↔
      ∃ execution : Execution qualified presentation configuration, execution.term = value := by
  constructor
  · exact realize qualified presentation
  · rintro ⟨execution, rfl⟩
    exact execution.reduces

theorem answers_iff {configuration : Configuration (S := S)} {value : Tm Head configuration.state.frame.arity} :
    Answer S.R configuration.code value ↔
      ∃ execution : Execution qualified presentation configuration,
        execution.term = value ∧ ConstructorSystem.Normal S.R execution.term := by
  constructor
  · rintro ⟨steps, normal⟩
    obtain ⟨execution, rfl⟩ := realize qualified presentation steps
    exact ⟨execution, rfl, normal⟩
  · rintro ⟨execution, rfl, normal⟩
    exact ⟨execution.reduces, normal⟩

theorem conversion_answer_iff {configuration : Configuration (S := S)} {value : Tm Head configuration.state.frame.arity} :
    (Conv S.R.headEq configuration.code value S.R.computation ∧ ConstructorSystem.Normal S.R value) ↔
      ∃ execution : Execution qualified presentation configuration,
        execution.term = value ∧ ConstructorSystem.Normal S.R execution.term :=
  (answer_iff qualified.churchRosser).symm.trans (answers_iff qualified presentation)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationProfile

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationProfile.reaches_iff
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationProfile.conversion_answer_iff
