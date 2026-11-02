import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveAlignmentCheckpoints
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveElaborationAssembly
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveIntroductionReplay
import Mettapedia.GSLT.LanguageDef.PositiveInductiveVectorTreeBaseComponents
import Mettapedia.GSLT.LanguageDef.PositiveInductiveVectorTreeAlignmentComponents
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveElaborationCheckpoints
/-!
# Retained Vector-tree cons method

The original cons-method request is checked at its original budget. Its four
abstractions and dependent pair retain formation, component replay and each
alignment gate. The retained method code is the original producer result,
with an independent replay proof. The complete branch bundle remains separate.
-/

set_option autoImplicit false
set_option Elab.async false
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Mettapedia.GSLT.LanguageDef.PositiveInductiveVectorTreeGuest
open Presentation ProducerEvidence
open Mettapedia.GSLT.LanguageDef.PositiveInductiveVectorTreeGuest.BranchReplayComponents
open Mettapedia.GSLT.LanguageDef.PositiveInductiveVectorTreeGuest.BranchAlignmentComponents
open Mettapedia.GSLT.LanguageDef.PositiveInductiveVectorTreeGuest.BranchBaseComponents
namespace Mettapedia.GSLT.LanguageDef.PositiveInductiveVectorTreeGuest.BranchMethodComponents
local instance : DecidableRel inventoryRules.headTyping :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.headTyping h u))
local instance : DecidablePred inventoryRules.isUniverse :=
  fun h => inferInstanceAs (Decidable (Tower.rules.isUniverse h))
local instance : ∀ u v w, Decidable (inventoryRules.join u v w) :=
  fun h u v => inferInstanceAs (Decidable (Tower.rules.join h u v))
local instance : DecidableRel inventoryRules.cumulative :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.cumulative h u))
local instance : DecidableRel inventoryRules.headEq :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.headEq h u))


def fourthDomain : Tower.Tm 5 :=
  match candidateType3 with | .pi domain _ => domain | _ => .head .legacyGround
def fourthBody : Tower.Tm 6 :=
  match candidateType3 with | .pi _ body => body | _ => .head .legacyGround
theorem candidate3_shape : candidateType3 = .pi fourthDomain fourthBody := rfl
def methodTerm : Tower.Tm 5 :=
  NativeVectorAll.allEvidenceConsCase (recursiveWitness (.var 4) (.var 3) (.var 2))


set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
theorem fourth_normalization :
    inventoryChoices.normalize 252 candidateType3 = .pi fourthDomain fourthBody := by
  rw [evaluationChoices_exact]
  decide +kernel

theorem fourth_alignment :
    FormationSensitiveElaboration.align inventoryRules inventoryChoices 252 branchContext
      (applicationPrefix 3) candidateType3 (.pi fourthDomain fourthBody)
      actualCode3 = some actualCode3 := by
  rw [← candidate3_shape]
  simp [FormationSensitiveElaboration.align]


private def expected0 : Tower.Tm 5 := fourthDomain
private def body0 : Tower.Tm 5 := methodTerm
private def context0 : Tower.Ctx 5 := branchContext

private def domain0 : Tower.Tm 5 :=
  match expected0 with | .pi domain _ => domain | _ => .head .legacyGround
private def expected1 : Tower.Tm 6 :=
  match expected0 with | .pi _ body => body | _ => .head .legacyGround
private def body1 : Tower.Tm 6 :=
  match body0 with | .lam body => body | _ => .var 0
private def context1 : Tower.Ctx 6 := .snoc context0 domain0
private theorem expected0_shape : expected0 = .pi domain0 expected1 := rfl
private theorem body0_shape : body0 = .lam body1 := rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
private theorem view0 : inventoryChoices.normalize 251 expected0 = .pi domain0 expected1 := by
  rw [evaluationChoices_exact]
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
private theorem formation0 : FormationSensitiveElaboration.formationReplayAccepted inventoryRules inventoryDecoder
    inventoryChoices 251 context0 (.pi domain0 expected1) = true := by
  rw [evaluationChoices_exact]
  decide +kernel

#print axioms formation0

private def domain1 : Tower.Tm 6 :=
  match expected1 with | .pi domain _ => domain | _ => .head .legacyGround
private def expected2 : Tower.Tm 7 :=
  match expected1 with | .pi _ body => body | _ => .head .legacyGround
private def body2 : Tower.Tm 7 :=
  match body1 with | .lam body => body | _ => .var 0
private def context2 : Tower.Ctx 7 := .snoc context1 domain1
private theorem expected1_shape : expected1 = .pi domain1 expected2 := rfl
private theorem body1_shape : body1 = .lam body2 := rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
private theorem view1 : inventoryChoices.normalize 250 expected1 = .pi domain1 expected2 := by
  rw [evaluationChoices_exact]
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
private theorem formation1 : FormationSensitiveElaboration.formationReplayAccepted inventoryRules inventoryDecoder
    inventoryChoices 250 context1 (.pi domain1 expected2) = true := by
  rw [evaluationChoices_exact]
  decide +kernel

#print axioms formation1

private def domain2 : Tower.Tm 7 :=
  match expected2 with | .pi domain _ => domain | _ => .head .legacyGround
private def expected3 : Tower.Tm 8 :=
  match expected2 with | .pi _ body => body | _ => .head .legacyGround
private def body3 : Tower.Tm 8 :=
  match body2 with | .lam body => body | _ => .var 0
private def context3 : Tower.Ctx 8 := .snoc context2 domain2
private theorem expected2_shape : expected2 = .pi domain2 expected3 := rfl
private theorem body2_shape : body2 = .lam body3 := rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
private theorem view2 : inventoryChoices.normalize 249 expected2 = .pi domain2 expected3 := by
  rw [evaluationChoices_exact]
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
private theorem formation2 : FormationSensitiveElaboration.formationReplayAccepted inventoryRules inventoryDecoder
    inventoryChoices 249 context2 (.pi domain2 expected3) = true := by
  rw [evaluationChoices_exact]
  decide +kernel

#print axioms formation2

private def domain3 : Tower.Tm 8 :=
  match expected3 with | .pi domain _ => domain | _ => .head .legacyGround
private def expected4 : Tower.Tm 9 :=
  match expected3 with | .pi _ body => body | _ => .head .legacyGround
private def body4 : Tower.Tm 9 :=
  match body3 with | .lam body => body | _ => .var 0
private def context4 : Tower.Ctx 9 := .snoc context3 domain3
private theorem expected3_shape : expected3 = .pi domain3 expected4 := rfl
private theorem body3_shape : body3 = .lam body4 := rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
private theorem view3 : inventoryChoices.normalize 248 expected3 = .pi domain3 expected4 := by
  rw [evaluationChoices_exact]
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
private theorem formation3 : FormationSensitiveElaboration.formationReplayAccepted inventoryRules inventoryDecoder
    inventoryChoices 248 context3 (.pi domain3 expected4) = true := by
  rw [evaluationChoices_exact]
  decide +kernel

#print axioms formation3


private def pairDomain : Tower.Tm 9 :=
  match expected4 with | .sigma domain _ => domain | _ => .head .legacyGround
private def pairBody : Tower.Tm 10 :=
  match expected4 with | .sigma _ body => body | _ => .head .legacyGround
private def pairFirst : Tower.Tm 9 :=
  match body4 with | .pair first _ => first | _ => .var 0
private def pairSecond : Tower.Tm 9 :=
  match body4 with | .pair _ second => second | _ => .var 0
private theorem pair_type_shape : expected4 = .sigma pairDomain pairBody := rfl
private theorem pair_term_shape : body4 = .pair pairFirst pairSecond := rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
private theorem pair_view : inventoryChoices.normalize 247 expected4 = .sigma pairDomain pairBody := by
  rw [evaluationChoices_exact]
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
private theorem pair_formation : FormationSensitiveElaboration.formationReplayAccepted inventoryRules inventoryDecoder
    inventoryChoices 247 context4 (.sigma pairDomain pairBody) = true := by
  rw [evaluationChoices_exact]
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
private theorem pair_first_replay : FormationSensitiveElaboration.termReplayAccepted inventoryRules inventoryDecoder
    inventoryChoices 247 context4 pairFirst pairDomain = true := by
  rw [evaluationChoices_exact]
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
private theorem pair_second_replay : FormationSensitiveElaboration.termReplayAccepted inventoryRules inventoryDecoder
    inventoryChoices 247 context4 pairSecond (inst0 pairFirst pairBody) = true := by
  rw [evaluationChoices_exact]
  decide +kernel

#print axioms pair_formation
#print axioms pair_first_replay
#print axioms pair_second_replay


private theorem pair_guard : FormationSensitiveElaboration.alignReplayGuard inventoryRules inventoryDecoder
    inventoryChoices 247 context4 (.sigma pairDomain pairBody) expected4 = true := by
  rw [← pair_type_shape]
  simp [FormationSensitiveElaboration.alignReplayGuard]

private theorem body4_accepted : FormationSensitiveElaboration.termReplayAccepted inventoryRules inventoryDecoder
    inventoryChoices 248 context4 body4 expected4 = true := by
  exact (FormationSensitiveElaboration.pair_replay_factor inventoryRules inventoryDecoder inventoryChoices
    247 context4 pairFirst pairSecond expected4 pairDomain pairBody pair_view).trans
    (congrArg₂ Bool.and (congrArg₂ Bool.and (congrArg₂ Bool.and pair_formation pair_first_replay)
      pair_second_replay) pair_guard)

private theorem guard3 : FormationSensitiveElaboration.alignReplayGuard inventoryRules inventoryDecoder
    inventoryChoices 248 context3 (.pi domain3 expected4) expected3 = true := by
  rw [← expected3_shape]
  simp [FormationSensitiveElaboration.alignReplayGuard]

private theorem body3_accepted : FormationSensitiveElaboration.termReplayAccepted inventoryRules inventoryDecoder
    inventoryChoices 249 context3 body3 expected3 = true := by
  exact (FormationSensitiveElaboration.lambda_replay_factor inventoryRules inventoryDecoder inventoryChoices
    248 context3 body4 expected3 domain3 expected4 view3).trans
    (congrArg₂ Bool.and (congrArg₂ Bool.and formation3 body4_accepted) guard3)

private theorem guard2 : FormationSensitiveElaboration.alignReplayGuard inventoryRules inventoryDecoder
    inventoryChoices 249 context2 (.pi domain2 expected3) expected2 = true := by
  rw [← expected2_shape]
  simp [FormationSensitiveElaboration.alignReplayGuard]

private theorem body2_accepted : FormationSensitiveElaboration.termReplayAccepted inventoryRules inventoryDecoder
    inventoryChoices 250 context2 body2 expected2 = true := by
  exact (FormationSensitiveElaboration.lambda_replay_factor inventoryRules inventoryDecoder inventoryChoices
    249 context2 body3 expected2 domain2 expected3 view2).trans
    (congrArg₂ Bool.and (congrArg₂ Bool.and formation2 body3_accepted) guard2)

private theorem guard1 : FormationSensitiveElaboration.alignReplayGuard inventoryRules inventoryDecoder
    inventoryChoices 250 context1 (.pi domain1 expected2) expected1 = true := by
  rw [← expected1_shape]
  simp [FormationSensitiveElaboration.alignReplayGuard]

private theorem body1_accepted : FormationSensitiveElaboration.termReplayAccepted inventoryRules inventoryDecoder
    inventoryChoices 251 context1 body1 expected1 = true := by
  exact (FormationSensitiveElaboration.lambda_replay_factor inventoryRules inventoryDecoder inventoryChoices
    250 context1 body2 expected1 domain1 expected2 view1).trans
    (congrArg₂ Bool.and (congrArg₂ Bool.and formation1 body2_accepted) guard1)

private theorem guard0 : FormationSensitiveElaboration.alignReplayGuard inventoryRules inventoryDecoder
    inventoryChoices 251 context0 (.pi domain0 expected1) expected0 = true := by
  rw [← expected0_shape]
  simp [FormationSensitiveElaboration.alignReplayGuard]

private theorem body0_accepted : FormationSensitiveElaboration.termReplayAccepted inventoryRules inventoryDecoder
    inventoryChoices 252 context0 body0 expected0 = true := by
  exact (FormationSensitiveElaboration.lambda_replay_factor inventoryRules inventoryDecoder inventoryChoices
    251 context0 body1 expected0 domain0 expected1 view0).trans
    (congrArg₂ Bool.and (congrArg₂ Bool.and formation0 body1_accepted) guard0)

theorem method_accepted : FormationSensitiveElaboration.termReplayAccepted inventoryRules inventoryDecoder
    inventoryChoices 252 branchContext methodTerm fourthDomain = true :=
  body0_accepted

private theorem term_produced_of_replay {Head : Type} (R : Rules Head) [DecidableEq Head]
    [DecidableRel R.headTyping] [DecidablePred R.isUniverse]
    [∀ u v w, Decidable (R.join u v w)] [DecidableRel R.cumulative] [DecidableRel R.headEq]
    (decoder : StructuralConversionCode.RootDecoder R.computation)
    (choices : FormationSensitiveElaboration.Choices Head decoder.Code) (fuel : Nat) {n : Nat}
    (context : Ctx Head n) (term type : Tm Head n)
    (accepted : FormationSensitiveElaboration.termReplayAccepted R decoder choices fuel context term type = true) :
    (FormationSensitiveElaboration.check R choices fuel context term type).isSome = true := by
  unfold FormationSensitiveElaboration.termReplayAccepted at accepted
  cases produced : FormationSensitiveElaboration.check R choices fuel context term type with
  | none => simp [produced] at accepted
  | some code => rfl

theorem method_present :
    (FormationSensitiveElaboration.check inventoryRules inventoryChoices 252 branchContext
      methodTerm fourthDomain).isSome = true :=
  term_produced_of_replay inventoryRules inventoryDecoder inventoryChoices 252 branchContext
    methodTerm fourthDomain method_accepted

noncomputable def methodCode := FormationSensitiveElaboration.producedTermCode inventoryRules inventoryChoices
  252 branchContext methodTerm fourthDomain method_present

theorem method_origin : FormationSensitiveElaboration.check inventoryRules inventoryChoices 252 branchContext
    methodTerm fourthDomain = some methodCode :=
  FormationSensitiveElaboration.producedTermCode_origin inventoryRules inventoryChoices
    252 branchContext methodTerm fourthDomain method_present

theorem method_replay : StructuralTypingReplay.check inventoryRules
    (fun code left right => code.check inventoryRules.headEq inventoryDecoder.decode left right)
    branchContext methodTerm fourthDomain methodCode = true := by
  have checkpoint := FormationSensitiveElaboration.termReplayAccepted_eq_produced_code inventoryRules inventoryDecoder
    inventoryChoices 252 branchContext methodTerm fourthDomain method_present
  unfold methodCode
  exact checkpoint.symm.trans method_accepted

#print axioms method_accepted
#print axioms method_origin
#print axioms method_replay

end Mettapedia.GSLT.LanguageDef.PositiveInductiveVectorTreeGuest.BranchMethodComponents
