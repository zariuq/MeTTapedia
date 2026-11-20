import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ComputationDefinitions

/-!
# A partial head definition keeps its uncovered call

This uses the checked compiler interpretation over the function's own name
in an open frame. The uncovered zero-length call reduces to that residual
name applied to its arguments. It does not manufacture a numeral result.
Normal form here includes stuck neutral terms; it does not mean successful
constructor output, nor does this open frame prove a closed total head
function exists.
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
open TowerVectorsModel (numC zeroC ttC)
open ProgrammingOnTheStep.IndexedFamilies.Eliminator (pkg D level1)

def headTerm : Tower.Tm 1 := Classical.choose head_checked

theorem headTerm_checked : Checked Vectors.Checker.headDef 1 headTerm := Classical.choose_spec head_checked

theorem headFrame_formed : CtxFormed pkg (baseCtx Vectors.Checker.headDef 1) := by
  obtain ⟨fuel, found⟩ := headTerm_checked.typed
  cases checked : Vectors.Checker.formed? fuel (baseCtx Vectors.Checker.headDef 1) with
  | none => simp [typed?, checked] at found
  | some formed => exact formed.down

def headArguments : Sub Tower.Head 3 1
  | 0 => ttC
  | 1 => zeroC
  | 2 => numC

theorem headArguments_typed :
    SubstMor pkg Vectors.Checker.headDef.telescope (baseCtx Vectors.Checker.headDef 1) headArguments := by
  intro index
  fin_cases index
  · exact D.nil_typed D.num_typed
  · exact D.zero_typed
  · exact D.num_typed

def headInput : Configuration (S := setting) := input headTerm_checked headFrame_formed headArguments_typed

def stuckHead : Tower.Tm 1 := spine (.var 0) [numC, zeroC, ttC]

theorem head_input_code : headInput.code = spine headTerm [numC, zeroC, ttC] := rfl

theorem stuckHead_normal : ConstructorSystem.Normal pkg stuckHead :=
  (VarSpine.app
    (VarSpine.app (VarSpine.app (.var 0) (Vectors.const_normal level1 (by decide)))
      (Vectors.const_normal level1 (by decide))) (Vectors.const_normal level1 (by decide))).normal

theorem head_uncovered_answer : Answer pkg headInput.code stuckHead := by
  have ran := ground_answers.2.2.2.2.2.1
  rw [headTerm_checked.compiled] at ran
  change Vectors.vecNormalize level1 40 (spine headTerm [numC, zeroC, ttC]) = some stuckHead at ran
  rw [head_input_code]
  exact ⟨Vectors.vecNormalize_sound level1 ran, stuckHead_normal⟩

theorem partial_head_has_residual_full_run :
    ∃ run : (step setting.levels Nat).toStep.Run headInput.state,
      ∃ profile : RunProfile qualified presentation headInput run,
        profile.execution.term = stuckHead ∧ ConstructorSystem.Normal pkg profile.execution.term :=
  (full_answers_iff qualified presentation (configuration := headInput)).mp head_uncovered_answer

theorem uncovered_is_not_zero : ¬ Answer pkg headInput.code zeroC := by
  intro fabricated
  have same := Vectors.vectors_answer_unique level1 fabricated head_uncovered_answer
  cases same

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationProfile.CheckedDefinitions

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationProfile.CheckedDefinitions.partial_head_has_residual_full_run
