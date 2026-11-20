import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.CompiledProgress
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.ExecutionControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.ValueAnswers

/-!
# Real compiled executions separate termination from value completeness

The actual empty development's compiler and concrete tagged-tuple frontier
execute a beta reduction to zero. Its normal identity function terminates
through the complete source/controller chain but has no value-profile
answer. A general normal-form endpoint remains necessary.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.CompiledProgressControls

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization
open SourceLanguage SourceLanguage.Elaboration

def supply (index : Nat) : MClosed := nodeC "space" [encodeNat index]

theorem beta_native_answer :
    NativeExecution.Answer ExecutionControls.built untyped.discipline Hosting.mettaNodes
      ExecutionControls.betaInput (TowerVectorsModel.zeroC : Tower.Tm 0) :=
  NativeExecution.directed_value_executes ExecutionControls.built untyped.discipline Hosting.mettaNodes supply
    (.single (.betaPi _ _)) .zero

theorem identity_directed_normalizes :
    Acc (fun after before => StrongNormalization.Reduces
      (NativeTypesOnTheStep.Computing.Definitions.devPackage [] ExecutionControls.built.nativeRows) before after)
      ExecutionControls.identity :=
  .intro _ (fun output edge => False.elim (ExecutionControls.identity_normal output edge))

theorem identity_native_normalizes :
    Acc (fun after before => (FrontierArrow.target (D := untyped.discipline) Hosting.mettaNodes
      (BinderCore.program ExecutionControls.built.rules)).Step before after)
      (FrontierArrow.initialState (D := untyped.discipline) Hosting.mettaNodes
        (BinderCore.program ExecutionControls.built.rules)
        (PublicQuery.query RuntimeSubstitution.rules ExecutionControls.built.authored
          (queryCode ExecutionControls.identity))) :=
  CompiledProgress.native_normalizes ExecutionControls.built untyped.discipline supply Hosting.mettaNodes
    ExecutionControls.identity identity_directed_normalizes

theorem identity_still_has_no_value_answer (value : Tower.Tm 0) :
    ¬ NativeExecution.Answer ExecutionControls.built untyped.discipline Hosting.mettaNodes
      ExecutionControls.identity value := by
  intro answered
  exact ExecutionControls.normal_identity_has_no_value_profile_answer _
    ((NativeExecution.done_iff_answer ExecutionControls.built untyped.discipline Hosting.mettaNodes supply _ _).mpr answered)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.CompiledProgressControls

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.CompiledProgressControls.identity_native_normalizes
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.CompiledProgressControls.beta_native_answer
