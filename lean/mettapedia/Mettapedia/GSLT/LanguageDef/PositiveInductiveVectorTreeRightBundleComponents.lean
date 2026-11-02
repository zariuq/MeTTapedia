import Mettapedia.GSLT.LanguageDef.PositiveInductiveVectorTreeRightBaseComponents
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveAlignmentCheckpoints
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveElaborationAssembly
import Mettapedia.GSLT.LanguageDef.PositiveInductiveVectorTreeRightMethodComponents
import Mettapedia.GSLT.LanguageDef.PositiveInductiveVectorTreeRightAlignmentComponents
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveElaborationCheckpoints
/-!
# Original nested bundle in the branch target

The original branch target checks its bundle argument at budget 254. This
component retains that exact synthesis/check result and independently replays
it. It does not replace the outer endpoint's unchanged budget 256 with a
separate request. Closed retained codes are proof data; the original producer
and checker remain executable.
-/

set_option autoImplicit false
set_option Elab.async false
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Mettapedia.GSLT.LanguageDef.PositiveInductiveVectorTreeGuest
open Presentation ProducerEvidence
open Mettapedia.GSLT.LanguageDef.PositiveInductiveVectorTreeGuest.BranchRightReplayComponents
open Mettapedia.GSLT.LanguageDef.PositiveInductiveVectorTreeGuest.BranchRightAlignmentComponents
open Mettapedia.GSLT.LanguageDef.PositiveInductiveVectorTreeGuest.BranchRightBaseComponents
open Mettapedia.GSLT.LanguageDef.PositiveInductiveVectorTreeGuest.BranchRightMethodComponents
namespace Mettapedia.GSLT.LanguageDef.PositiveInductiveVectorTreeGuest.BranchRightBundleComponents
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
private theorem fourth_normalization :
    inventoryChoices.normalize 250 candidateType3 = .pi fourthDomain fourthBody := by
  rw [evaluationChoices_exact]
  decide +kernel

private theorem fourth_alignment :
    FormationSensitiveElaboration.align inventoryRules inventoryChoices 250 branchContext
      (applicationPrefix 3) candidateType3 (.pi fourthDomain fourthBody)
      actualCode3 = some actualCode3 := by
  rw [← candidate3_shape]
  simp [FormationSensitiveElaboration.align]

private noncomputable def actualCode4 : FormationSensitiveElaboration.Code Tower.Head inventoryDecoder.Code 5 :=
  .appElim fourthDomain fourthBody actualCode3 methodCode

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
private theorem originalPrefix4 :
    FormationSensitiveElaboration.synth inventoryRules inventoryChoices 251
      branchContext (applicationPrefix 4) = some ⟨candidateType4,actualCode4⟩ := by
  have termEq : applicationPrefix 4 = .app (applicationPrefix 3) methodTerm := rfl
  rw [termEq]
  have notLambda : ∀ body, applicationPrefix 3 ≠ .lam body := by
    intro body h
    change Tm.app _ _ = .lam body at h
    cases h
  have view := fourth_normalization
  have aligned := fourth_alignment
  have checked := method_origin
  have application : FormationSensitiveElaboration.synth inventoryRules inventoryChoices 251 branchContext
      (.app (applicationPrefix 3) methodTerm) =
        some ⟨inst0 methodTerm fourthBody,
          StructuralTypingReplay.Code.appElim fourthDomain fourthBody actualCode3 methodCode⟩ := by
    with_reducible
      exact FormationSensitiveElaboration.synth_application_of inventoryRules inventoryChoices
        250 branchContext (applicationPrefix 3) methodTerm notLambda
        ⟨candidateType3,actualCode3⟩ fourthDomain fourthBody actualCode3 methodCode
        originalPrefix3 view aligned checked
  have result : inst0 methodTerm fourthBody = candidateType4 := by decide +kernel
  simpa only [actualCode4,result] using application

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
private theorem actualCode4_replay :
    StructuralTypingReplay.check inventoryRules
      (fun code left right => code.check inventoryRules.headEq inventoryDecoder.decode left right)
      branchContext (applicationPrefix 4) candidateType4 actualCode4 = true := by
  have termEq : applicationPrefix 4 = .app (applicationPrefix 3) methodTerm := rfl
  rw [termEq]
  unfold actualCode4
  rw [StructuralTypingReplay.check]
  have previous : StructuralTypingReplay.check inventoryRules
      (fun code left right => code.check inventoryRules.headEq inventoryDecoder.decode left right)
      branchContext (applicationPrefix 3) (.pi fourthDomain fourthBody) actualCode3 = true := by
    change StructuralTypingReplay.check inventoryRules
      (fun code left right => code.check inventoryRules.headEq inventoryDecoder.decode left right)
      branchContext (applicationPrefix 3) candidateType3 actualCode3 = true
    exact actualCode3_replay
  exact Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨previous, method_replay⟩, by decide +kernel⟩

#print axioms originalPrefix4
#print axioms actualCode4_replay


private def lengthDomain : Tower.Tm 5 :=
  match candidateType4 with | .pi domain _ => domain | _ => .head .legacyGround
private def lengthBody : Tower.Tm 6 :=
  match candidateType4 with | .pi _ body => body | _ => .head .legacyGround
private theorem candidate4_shape : candidateType4 = .pi lengthDomain lengthBody := rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
private theorem length_normalization :
    inventoryChoices.normalize 251 candidateType4 = .pi lengthDomain lengthBody := by
  rw [evaluationChoices_exact]
  decide +kernel

private theorem length_alignment :
    FormationSensitiveElaboration.align inventoryRules inventoryChoices 251 branchContext
      (applicationPrefix 4) candidateType4 (.pi lengthDomain lengthBody)
      actualCode4 = some actualCode4 := by
  rw [← candidate4_shape]
  simp [FormationSensitiveElaboration.align]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
private theorem length_origin : FormationSensitiveElaboration.check inventoryRules inventoryChoices 251
    branchContext (.var 1) lengthDomain =
      some (.var : FormationSensitiveElaboration.Code Tower.Head inventoryDecoder.Code 5) := by
  rw [evaluationChoices_exact]
  rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
private theorem length_replay : StructuralTypingReplay.check inventoryRules
    (fun code left right => code.check inventoryRules.headEq inventoryDecoder.decode left right)
    branchContext (.var 1) lengthDomain
      (.var : FormationSensitiveElaboration.Code Tower.Head inventoryDecoder.Code 5) = true := by
  decide +kernel

private noncomputable def actualCode5 : FormationSensitiveElaboration.Code Tower.Head inventoryDecoder.Code 5 :=
  .appElim lengthDomain lengthBody actualCode4 .var

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
private theorem originalPrefix5 :
    FormationSensitiveElaboration.synth inventoryRules inventoryChoices 252
      branchContext (applicationPrefix 5) = some ⟨candidateType5,actualCode5⟩ := by
  have termEq : applicationPrefix 5 = .app (applicationPrefix 4) (.var 1) := rfl
  rw [termEq]
  have notLambda : ∀ body, applicationPrefix 4 ≠ .lam body := by
    intro body h
    change Tm.app _ _ = .lam body at h
    cases h
  have view := length_normalization
  have aligned := length_alignment
  have checked := length_origin
  have application : FormationSensitiveElaboration.synth inventoryRules inventoryChoices 252 branchContext
      (.app (applicationPrefix 4) (.var 1)) =
        some ⟨inst0 (.var 1) lengthBody,
          StructuralTypingReplay.Code.appElim lengthDomain lengthBody actualCode4 .var⟩ := by
    with_reducible
      exact FormationSensitiveElaboration.synth_application_of inventoryRules inventoryChoices
        251 branchContext (applicationPrefix 4) (.var 1) notLambda
        ⟨candidateType4,actualCode4⟩ lengthDomain lengthBody actualCode4 .var
        originalPrefix4 view aligned checked
  have result : inst0 (.var 1 : Tower.Tm 5) lengthBody = candidateType5 := by decide +kernel
  simpa only [actualCode5,result] using application

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
private theorem actualCode5_replay :
    StructuralTypingReplay.check inventoryRules
      (fun code left right => code.check inventoryRules.headEq inventoryDecoder.decode left right)
      branchContext (applicationPrefix 5) candidateType5 actualCode5 = true := by
  have termEq : applicationPrefix 5 = .app (applicationPrefix 4) (.var 1) := rfl
  rw [termEq]
  unfold actualCode5
  rw [StructuralTypingReplay.check]
  have previous : StructuralTypingReplay.check inventoryRules
      (fun code left right => code.check inventoryRules.headEq inventoryDecoder.decode left right)
      branchContext (applicationPrefix 4) (.pi lengthDomain lengthBody) actualCode4 = true := by
    change StructuralTypingReplay.check inventoryRules
      (fun code left right => code.check inventoryRules.headEq inventoryDecoder.decode left right)
      branchContext (applicationPrefix 4) candidateType4 actualCode4 = true
    exact actualCode4_replay
  exact Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨previous, length_replay⟩, by decide +kernel⟩

#print axioms originalPrefix5
#print axioms actualCode5_replay

private def childrenDomain : Tower.Tm 5 :=
  match candidateType5 with | .pi domain _ => domain | _ => .head .legacyGround
private def childrenBody : Tower.Tm 6 :=
  match candidateType5 with | .pi _ body => body | _ => .head .legacyGround
private theorem candidate5_shape : candidateType5 = .pi childrenDomain childrenBody := rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
private theorem children_normalization :
    inventoryChoices.normalize 252 candidateType5 = .pi childrenDomain childrenBody := by
  rw [evaluationChoices_exact]
  decide +kernel

private theorem children_alignment :
    FormationSensitiveElaboration.align inventoryRules inventoryChoices 252 branchContext
      (applicationPrefix 5) candidateType5 (.pi childrenDomain childrenBody)
      actualCode5 = some actualCode5 := by
  rw [← candidate5_shape]
  simp [FormationSensitiveElaboration.align]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
private theorem children_origin : FormationSensitiveElaboration.check inventoryRules inventoryChoices 252
    branchContext (.var 0) childrenDomain =
      some (.var : FormationSensitiveElaboration.Code Tower.Head inventoryDecoder.Code 5) := by
  rw [evaluationChoices_exact]
  rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
private theorem children_replay : StructuralTypingReplay.check inventoryRules
    (fun code left right => code.check inventoryRules.headEq inventoryDecoder.decode left right)
    branchContext (.var 0) childrenDomain
      (.var : FormationSensitiveElaboration.Code Tower.Head inventoryDecoder.Code 5) = true := by
  decide +kernel

noncomputable def bundleCode : FormationSensitiveElaboration.Code Tower.Head inventoryDecoder.Code 5 :=
  .appElim childrenDomain childrenBody actualCode5 .var

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
theorem synthesizedBundle_origin :
    FormationSensitiveElaboration.synth inventoryRules inventoryChoices 253
      branchContext (applicationPrefix 6) = some ⟨candidateType6,bundleCode⟩ := by
  have termEq : applicationPrefix 6 = .app (applicationPrefix 5) (.var 0) := rfl
  rw [termEq]
  have notLambda : ∀ body, applicationPrefix 5 ≠ .lam body := by
    intro body h
    change Tm.app _ _ = .lam body at h
    cases h
  have view := children_normalization
  have aligned := children_alignment
  have checked := children_origin
  have application : FormationSensitiveElaboration.synth inventoryRules inventoryChoices 253 branchContext
      (.app (applicationPrefix 5) (.var 0)) =
        some ⟨inst0 (.var 0) childrenBody,
          StructuralTypingReplay.Code.appElim childrenDomain childrenBody actualCode5 .var⟩ := by
    with_reducible
      exact FormationSensitiveElaboration.synth_application_of inventoryRules inventoryChoices
        252 branchContext (applicationPrefix 5) (.var 0) notLambda
        ⟨candidateType5,actualCode5⟩ childrenDomain childrenBody actualCode5 .var
        originalPrefix5 view aligned checked
  have result : inst0 (.var 0 : Tower.Tm 5) childrenBody = candidateType6 := by decide +kernel
  simpa only [bundleCode,result] using application

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
private theorem bundleCode_replay :
    StructuralTypingReplay.check inventoryRules
      (fun code left right => code.check inventoryRules.headEq inventoryDecoder.decode left right)
      branchContext (applicationPrefix 6) candidateType6 bundleCode = true := by
  have termEq : applicationPrefix 6 = .app (applicationPrefix 5) (.var 0) := rfl
  rw [termEq]
  unfold bundleCode
  rw [StructuralTypingReplay.check]
  have previous : StructuralTypingReplay.check inventoryRules
      (fun code left right => code.check inventoryRules.headEq inventoryDecoder.decode left right)
      branchContext (applicationPrefix 5) (.pi childrenDomain childrenBody) actualCode5 = true := by
    change StructuralTypingReplay.check inventoryRules
      (fun code left right => code.check inventoryRules.headEq inventoryDecoder.decode left right)
      branchContext (applicationPrefix 5) candidateType5 actualCode5 = true
    exact actualCode5_replay
  exact Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨previous, children_replay⟩, by decide +kernel⟩

#print axioms synthesizedBundle_origin
#print axioms bundleCode_replay

private theorem check_application_of {Head : Type} {RootCode : Nat → Type}
    (R : Rules Head) (choices : FormationSensitiveElaboration.Choices Head RootCode) [DecidableEq Head]
    (fuel : Nat) {n : Nat} (context : Ctx Head n) (function argument expected : Tm Head n)
    (inferred : FormationSensitiveElaboration.Inferred Head RootCode n)
    (result : FormationSensitiveElaboration.Code Head RootCode n)
    (produced : FormationSensitiveElaboration.synth R choices fuel context (.app function argument) = some inferred)
    (aligned : FormationSensitiveElaboration.align R choices fuel context (.app function argument)
      inferred.type expected inferred.evidence = some result) :
    FormationSensitiveElaboration.check R choices (fuel+1) context (.app function argument) expected = some result := by
  cases choices.normalize fuel expected <;>
    simp only [FormationSensitiveElaboration.check, produced, aligned, Option.bind_eq_bind, Option.bind_some]

private theorem candidate6_expected : candidateType6 = branchBundleType := rfl

private theorem final_alignment : FormationSensitiveElaboration.align inventoryRules inventoryChoices 253
    branchContext (applicationPrefix 6) candidateType6 branchBundleType bundleCode = some bundleCode := by
  rw [candidate6_expected]
  simp [FormationSensitiveElaboration.align]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
theorem bundle_origin : FormationSensitiveElaboration.check inventoryRules inventoryChoices 254
    branchContext branchBundle branchBundleType = some bundleCode := by
  have termEq : applicationPrefix 6 = .app (applicationPrefix 5) (.var 0) := rfl
  have produced := synthesizedBundle_origin
  rw [termEq] at produced
  have aligned := final_alignment
  rw [termEq] at aligned
  rw [← original_term, termEq]
  with_reducible
    exact check_application_of inventoryRules inventoryChoices 253 branchContext
      (applicationPrefix 5) (.var 0) branchBundleType ⟨candidateType6,bundleCode⟩ bundleCode produced aligned

theorem bundle_replay : StructuralTypingReplay.check inventoryRules
    (fun code left right => code.check inventoryRules.headEq inventoryDecoder.decode left right)
    branchContext branchBundle branchBundleType bundleCode = true := by
  change StructuralTypingReplay.check inventoryRules
    (fun code left right => code.check inventoryRules.headEq inventoryDecoder.decode left right)
    branchContext (applicationPrefix 6) candidateType6 bundleCode = true
  exact bundleCode_replay

private theorem termReplayAccepted_of_origin {Head : Type} (R : Rules Head) [DecidableEq Head]
    [DecidableRel R.headTyping] [DecidablePred R.isUniverse]
    [∀ u v w, Decidable (R.join u v w)] [DecidableRel R.cumulative] [DecidableRel R.headEq]
    (decoder : StructuralConversionCode.RootDecoder R.computation)
    (choices : FormationSensitiveElaboration.Choices Head decoder.Code) (fuel : Nat) {n : Nat}
    (context : Ctx Head n) (term type : Tm Head n)
    (code : FormationSensitiveElaboration.Code Head decoder.Code n)
    (produced : FormationSensitiveElaboration.check R choices fuel context term type = some code)
    (replayed : StructuralTypingReplay.check R
      (fun recipe left right => recipe.check R.headEq decoder.decode left right)
      context term type code = true) :
    FormationSensitiveElaboration.termReplayAccepted R decoder choices fuel context term type = true := by
  unfold FormationSensitiveElaboration.termReplayAccepted
  rw [produced]
  exact replayed

theorem nested_bundle_accepted : FormationSensitiveElaboration.termReplayAccepted inventoryRules inventoryDecoder
    inventoryChoices 254 branchContext branchBundle branchBundleType = true :=
  termReplayAccepted_of_origin inventoryRules inventoryDecoder inventoryChoices 254 branchContext
    branchBundle branchBundleType bundleCode bundle_origin bundle_replay

#print axioms bundle_origin
#print axioms bundle_replay
#print axioms nested_bundle_accepted

end Mettapedia.GSLT.LanguageDef.PositiveInductiveVectorTreeGuest.BranchRightBundleComponents
