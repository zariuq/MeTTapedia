import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveAlignmentCheckpoints
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveElaborationAssembly
import Mettapedia.GSLT.LanguageDef.PositiveInductiveVectorTreeRightReplayComponents
import Mettapedia.GSLT.LanguageDef.PositiveInductiveVectorTreeRightAlignmentComponents
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveElaborationCheckpoints
/-!
# Retained base continuation in the original branch target

The non-reflexive alignment and the next application retain the exact results
of the original bounded producer. The same retained codes are independently
replayed before composing the base case application. Acceptance of the whole
branch bundle remains a separate check.
-/

set_option autoImplicit false
set_option Elab.async false
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Mettapedia.GSLT.LanguageDef.PositiveInductiveVectorTreeGuest
open Presentation ProducerEvidence
open Mettapedia.GSLT.LanguageDef.PositiveInductiveVectorTreeGuest.BranchRightReplayComponents
open Mettapedia.GSLT.LanguageDef.PositiveInductiveVectorTreeGuest.BranchRightAlignmentComponents
namespace Mettapedia.GSLT.LanguageDef.PositiveInductiveVectorTreeGuest.BranchRightBaseComponents
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

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
theorem third_alignment_present :
    (FormationSensitiveElaboration.align inventoryRules inventoryChoices 249 branchContext
      (applicationPrefix 2) candidateType2 viewType2 actualCode2).isSome = true := by
  rw [FormationSensitiveElaboration.align_success inventoryRules inventoryChoices]
  rw [evaluationChoices_exact]
  decide +kernel

noncomputable def aligned2 : FormationSensitiveElaboration.Code Tower.Head inventoryDecoder.Code 5 :=
  (FormationSensitiveElaboration.align inventoryRules inventoryChoices 249 branchContext
    (applicationPrefix 2) candidateType2 viewType2 actualCode2).get third_alignment_present

theorem aligned2_origin :
    FormationSensitiveElaboration.align inventoryRules inventoryChoices 249 branchContext
      (applicationPrefix 2) candidateType2 viewType2 actualCode2 = some aligned2 :=
  Option.eq_some_of_isSome third_alignment_present

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
theorem aligned2_replay :
    StructuralTypingReplay.check inventoryRules
      (fun code left right => code.check inventoryRules.headEq inventoryDecoder.decode left right)
      branchContext (applicationPrefix 2) viewType2 aligned2 = true := by
  have joined : (StructuralTypingReplay.check inventoryRules
      (fun code left right => code.check inventoryRules.headEq inventoryDecoder.decode left right)
      branchContext (applicationPrefix 2) candidateType2 actualCode2 &&
      FormationSensitiveElaboration.alignReplayGuard inventoryRules inventoryDecoder inventoryChoices
        249 branchContext candidateType2 viewType2) = true := by
    exact Bool.and_eq_true_iff.mpr ⟨actualCode2_replay, third_guard⟩
  have accepted := (FormationSensitiveElaboration.align_replay_factor inventoryRules inventoryDecoder inventoryChoices
    249 branchContext (applicationPrefix 2) candidateType2 viewType2 actualCode2).trans joined
  have checkpoint := FormationSensitiveElaboration.alignReplayAccepted_eq_produced_code inventoryRules inventoryDecoder
    inventoryChoices 249 branchContext (applicationPrefix 2) candidateType2 viewType2 actualCode2 third_alignment_present
  simpa only [aligned2, FormationSensitiveElaboration.producedAlignmentCode] using
    checkpoint.symm.trans accepted


set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
theorem third_argument_present :
    (FormationSensitiveElaboration.check inventoryRules inventoryChoices 249
      branchContext NativeVectorAll.unitEvidence thirdDomain).isSome = true := by
  rw [FormationSensitiveElaboration.check_success inventoryRules inventoryChoices]
  rw [evaluationChoices_exact]
  decide +kernel

noncomputable def thirdArgumentCode := FormationSensitiveElaboration.producedTermCode inventoryRules
  inventoryChoices 249 branchContext NativeVectorAll.unitEvidence thirdDomain third_argument_present

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
theorem third_argument_replay :
    StructuralTypingReplay.check inventoryRules
      (fun code left right => code.check inventoryRules.headEq inventoryDecoder.decode left right)
      branchContext NativeVectorAll.unitEvidence thirdDomain thirdArgumentCode = true := by
  unfold thirdArgumentCode FormationSensitiveElaboration.producedTermCode
  rw [Option.get_congr (ho := third_argument_present)
    (congrArg (fun selected => FormationSensitiveElaboration.check inventoryRules
      selected 249 branchContext NativeVectorAll.unitEvidence thirdDomain) evaluationChoices_exact)]
  decide +kernel

noncomputable def actualCode3 : FormationSensitiveElaboration.Code Tower.Head inventoryDecoder.Code 5 :=
  .appElim thirdDomain thirdBody aligned2 thirdArgumentCode

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
theorem originalPrefix3 :
    FormationSensitiveElaboration.synth inventoryRules inventoryChoices 250
      branchContext (applicationPrefix 3) = some ⟨candidateType3,actualCode3⟩ := by
  have termEq : applicationPrefix 3 = .app (applicationPrefix 2) NativeVectorAll.unitEvidence := rfl
  rw [termEq]
  have notLambda : ∀ body, applicationPrefix 2 ≠ .lam body := by
    intro body h
    change Tm.app _ _ = .lam body at h
    cases h
  have view : inventoryChoices.normalize 249 candidateType2 = .pi thirdDomain thirdBody :=
    third_normalization
  have aligned : FormationSensitiveElaboration.align inventoryRules inventoryChoices 249 branchContext
      (applicationPrefix 2) candidateType2 (.pi thirdDomain thirdBody) actualCode2 = some aligned2 :=
    aligned2_origin
  have checked : FormationSensitiveElaboration.check inventoryRules inventoryChoices 249 branchContext
      NativeVectorAll.unitEvidence thirdDomain = some thirdArgumentCode :=
    FormationSensitiveElaboration.producedTermCode_origin inventoryRules inventoryChoices
      249 branchContext NativeVectorAll.unitEvidence thirdDomain third_argument_present
  have application : FormationSensitiveElaboration.synth inventoryRules inventoryChoices 250 branchContext
      (.app (applicationPrefix 2) NativeVectorAll.unitEvidence) =
        some ⟨inst0 NativeVectorAll.unitEvidence thirdBody,
          StructuralTypingReplay.Code.appElim thirdDomain thirdBody aligned2 thirdArgumentCode⟩ := by
    with_reducible
      exact FormationSensitiveElaboration.synth_application_of inventoryRules inventoryChoices
        249 branchContext (applicationPrefix 2) NativeVectorAll.unitEvidence notLambda
        ⟨candidateType2,actualCode2⟩ thirdDomain thirdBody aligned2 thirdArgumentCode
        originalPrefix2 view aligned checked
  have result : inst0 (NativeVectorAll.unitEvidence : Tower.Tm 5) thirdBody = candidateType3 := by decide +kernel
  simpa only [actualCode3,result] using application

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
theorem actualCode3_replay :
    StructuralTypingReplay.check inventoryRules
      (fun code left right => code.check inventoryRules.headEq inventoryDecoder.decode left right)
      branchContext (applicationPrefix 3) candidateType3 actualCode3 = true := by
  have termEq : applicationPrefix 3 = .app (applicationPrefix 2) NativeVectorAll.unitEvidence := rfl
  rw [termEq]
  unfold actualCode3
  rw [StructuralTypingReplay.check]
  have previous := aligned2_replay
  rw [view2_shape] at previous
  rw [previous,third_argument_replay]
  decide +kernel

#print axioms aligned2_origin
#print axioms aligned2_replay
#print axioms third_argument_replay
#print axioms originalPrefix3
#print axioms actualCode3_replay

end Mettapedia.GSLT.LanguageDef.PositiveInductiveVectorTreeGuest.BranchRightBaseComponents
