import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.ExecutionReflection
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.NativeExecution
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.DirectedAnswers.Rows

/-!
# Exact data-value observations of the compiled public execution

The native frontier's actual public query reports precisely the source terms
reachable by directed reduction that belong to the data-value grammar. For a
checked development these values are also normal forms of the actual package.
General normal results and divergence remain separate observations.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.ValueAnswers

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality
open SourceLanguage SourceLanguage.Elaboration
open NativeTypesOnTheStep.Computing

variable {dev : Definitions.Development} (built : Compiled dev)
  (D : Discipline MSig [] ()) (N : Hosting.Nodes MSig [] ()) (supply : Nat → MClosed)

include supply

theorem answer_iff (term value : Tower.Tm 0) :
    NativeExecution.Answer built D N term value ↔
      StrongNormalization.ReducesStar (Definitions.devPackage dev built.nativeRows) term value ∧
        DirectedAnswers.Value value :=
  (NativeExecution.done_iff_answer built D N supply term value).symm.trans
    (ExecutionReflection.encoded_success_iff built term value)

theorem checked_answer_is_normal (ok : Definitions.devCheck dev = true)
    {term value : Tower.Tm 0} (answered : NativeExecution.Answer built D N term value) :
    DirectedAnswers.DirectedAnswer (Definitions.devPackage dev built.nativeRows) term value := by
  obtain ⟨reached, isValue⟩ := (answer_iff built D N supply term value).mp answered
  exact ⟨reached, DirectedAnswers.directedNormal_of_normal (isValue.normal_dev ok built.native)⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.ValueAnswers

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.ValueAnswers.answer_iff
