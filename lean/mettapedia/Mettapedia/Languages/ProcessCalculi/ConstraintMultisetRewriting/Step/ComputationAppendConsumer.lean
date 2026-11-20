import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ComputationDefinitions

/-!
# Recursive append from checked source rows, with addition in its result type

The actual compiler output for append is applied to two singleton vectors.
Its declared result type uses the earlier addition-by-rows definition. Both
the call and the computation of that type are justified by the existing
compiler interpretation. The general bridge realizes the complete recursive
computation as full-step firings, not one assumed recursive-function answer.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationProfile.CheckedDefinitions

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta DependentFull
open NativeTypesOnTheStep.Computing
open NativeTypesOnTheStep.Computing.Definitions
open TowerVectorsModel (numC vecC)
open ProgrammingOnTheStep.IndexedFamilies.Eliminator (pkg D level1)
open ProgrammingOnTheStep.IndexedFamilies.ClosedCalls

def appendArguments : Sub Tower.Head 5 0
  | 0 => single three
  | 1 => single two
  | 2 => one
  | 3 => one
  | 4 => numC

theorem appendArguments_typed : SubstMor pkg appendRDef.telescope .nil appendArguments := by
  intro index
  fin_cases index
  · exact single_typed (three_typed _)
  · exact single_typed (two_typed _)
  · exact one_typed _
  · exact one_typed _
  · exact D.num_typed

def appendInput : Configuration (S := setting) := input appendR_checked .nil appendArguments_typed

theorem append_source :
    appendInput.code = spine appendRTerm [numC, one, one, single two, single three] := by
  decide +kernel

theorem append_answer : Answer pkg appendInput.code twoThree := by
  rw [append_source]
  exact ⟨Vectors.vecNormalize_sound level1 ground_answers.2.1, Vectors.twoThree_normal⟩

theorem append_actual_full_run :
    ∃ run : (step setting.levels Nat).toStep.Run appendInput.state,
      ∃ profile : RunProfile qualified presentation appendInput run,
        profile.execution.term = twoThree ∧
          ConstructorSystem.Normal pkg profile.execution.term :=
  (full_answers_iff qualified presentation (configuration := appendInput)).mp append_answer

theorem append_result_keeps_computed_type
    {run : (step setting.levels Nat).toStep.Run appendInput.state}
    (profile : RunProfile qualified presentation appendInput run) :
    Typed pkg .nil profile.execution.term (subst appendArguments appendRDef.result) :=
  checked_run_at_source_type appendR_checked .nil appendArguments_typed profile

theorem result_type_mentions_checked_addition :
    subst appendArguments appendRDef.result = vecC numC (spine addExport [one, one]) := by
  decide +kernel

theorem result_type_computes :
    Conv pkg.headEq (subst appendArguments appendRDef.result) (vecC numC two) pkg.computation :=
  joins_conv (fuel := 60) (by decide +kernel)

theorem cannot_answer_short_vector : ¬ Answer pkg appendInput.code (single two) := by
  intro short
  have same := Vectors.vectors_answer_unique level1 short append_answer
  exact (by decide : (single two : Tower.Tm 0) ≠ twoThree) same

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationProfile.CheckedDefinitions

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationProfile.CheckedDefinitions.append_actual_full_run
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationProfile.CheckedDefinitions.result_type_computes
