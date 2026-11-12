import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.TypedPublicationAgreementControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.VectorAppend

/-!
# An initial solution does not decide arbitrary raw output typing

Defining a Ground-function variable to identity has an initial solution.
At that answer the variable's raw code becomes an identity which can be
rechecked at U0 -> U0. Another solution inserts a typed beta-redex at the
original function type, and cannot be rechecked at U0 -> U0. Thus even this
initial answer does not license universal raw output typing.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublicationPrincipalControls

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta TypedPublicationAgreementControls

def closedIdentity : Term (empty Tower.rules) (arrowType (empty Tower.rules)) :=
  ⟨.lam (.var 0), .lamIntro (DependentFull.Controls.arrow_typed _) (.sort _) (Derivable.var 0)⟩

def information : EquationStore (TotalTerm scope) :=
  [Elimination.definition (empty Tower.rules) closedIdentity]

def answer : empty Tower.rules ⟶ scope := Elimination.instantiate (empty Tower.rules) closedIdentity

theorem answer_initial : UnificationWithLevels.InitialSolution (frames levels) information answer :=
  NativeTypesOnTheStep.definition_initial levels _ closedIdentity

theorem answer_types_raw_row : (requestedRow.reindex answer).WellTyped :=
  .lamIntro (wide_typed _) (.sort _) (Derivable.var 0)

theorem identity_reading_solves : (frames levels).Models identityReading information := by
  have solved := Frames.models_comp (X := frames levels) answer_initial.solves (toEmpty scope)
  have same : (frames levels).comp (toEmpty scope) answer = identityReading := by
    apply Hom.ext
    funext index
    fin_cases index
    rfl
  rwa [same] at solved

theorem expanded_reading_solves : (frames levels).Models expandedReading information :=
  (UnificationWithLevels.models_of_agree readings_agree information).mp identity_reading_solves

theorem output_not_typed_at_every_solution :
    ¬ NativeTypesOnTheStep.TypedAfterMatch levels information requestedRow := by
  intro typed
  have actual := (NativeTypesOnTheStep.typedAfterMatch_iff levels information requestedRow).mp typed
    scope expandedReading expanded_reading_solves
  exact expanded_reading_does_not_type_requested_row actual

theorem initial_answer_check_is_strictly_weaker :
    UnificationWithLevels.InitialSolution (frames levels) information answer ∧
      (requestedRow.reindex answer).WellTyped ∧
      ¬ NativeTypesOnTheStep.TypedAfterMatch levels information requestedRow :=
  ⟨answer_initial, answer_types_raw_row, output_not_typed_at_every_solution⟩

theorem output_is_typed_up_to_agreement :
    NativeTypesOnTheStep.TypedUpToAgreement levels information requestedRow :=
  NativeTypesOnTheStep.settled_sound levels
    (NativeTypesOnTheStep.principal_of_initial levels answer_initial) answer_types_raw_row

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublicationPrincipalControls

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublicationPrincipalControls.initial_answer_check_is_strictly_weaker
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublicationPrincipalControls.output_is_typed_up_to_agreement
