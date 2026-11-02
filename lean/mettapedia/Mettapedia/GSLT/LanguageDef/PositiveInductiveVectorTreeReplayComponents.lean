import Mettapedia.GSLT.LanguageDef.PositiveInductiveVectorTreeProducerChecks
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveElaborationCheckpoints
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveElaborationAssembly
/-!
# Retained original Vector-tree application prefixes

The first two application prefixes retain the exact results of the original
bounded producer. Each retained code is independently replayed. These facts
are intermediate checks; acceptance of the complete branch bundle is separate.
The closed retained codes are proof data, while the producer and checker remain
executable.
-/

set_option autoImplicit false
set_option Elab.async false
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Mettapedia.GSLT.LanguageDef.PositiveInductiveVectorTreeGuest
open Presentation ProducerEvidence
namespace Mettapedia.GSLT.LanguageDef.PositiveInductiveVectorTreeGuest.BranchReplayComponents
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

theorem present0 :
    (FormationSensitiveElaboration.synth inventoryRules inventoryChoices 249
      branchContext (applicationPrefix 0)).isSome = true :=
  FormationSensitiveElaboration.synth_present_of_typeProjection inventoryRules inventoryChoices
    249 branchContext (applicationPrefix 0) candidateType0 checkedPrefix0

noncomputable def inferred0 := FormationSensitiveElaboration.producedInference inventoryRules inventoryChoices
  249 branchContext (applicationPrefix 0) present0

theorem inferred0_origin :
    FormationSensitiveElaboration.synth inventoryRules inventoryChoices 249
      branchContext (applicationPrefix 0) = some inferred0 :=
  FormationSensitiveElaboration.producedInference_origin inventoryRules inventoryChoices
    249 branchContext (applicationPrefix 0) present0

theorem inferred0_type : inferred0.type = candidateType0 :=
  FormationSensitiveElaboration.producedInference_type inventoryRules inventoryChoices
    249 branchContext (applicationPrefix 0) candidateType0 present0 checkedPrefix0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
theorem inferred0_replay :
    StructuralTypingReplay.check inventoryRules
      (fun code left right => code.check inventoryRules.headEq inventoryDecoder.decode left right)
      branchContext (applicationPrefix 0) candidateType0 inferred0.evidence = true := by
  unfold inferred0 FormationSensitiveElaboration.producedInference
  rw [Option.get_congr (ho := present0)
    (congrArg (fun selected => FormationSensitiveElaboration.synth inventoryRules
      selected 249 branchContext (applicationPrefix 0)) evaluationChoices_exact)]
  decide +kernel
#print axioms inferred0_origin
#print axioms inferred0_type
#print axioms inferred0_replay

def firstDomain : Tower.Tm 5 :=
  match candidateType0 with | .pi domain _ => domain | _ => .head .legacyGround
def firstBody : Tower.Tm 6 :=
  match candidateType0 with | .pi _ body => body | _ => .head .legacyGround
theorem candidate0_shape : candidateType0 = .pi firstDomain firstBody := rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
theorem first_normalization :
    inventoryChoices.normalize 249 candidateType0 = .pi firstDomain firstBody := by
  rw [evaluationChoices_exact]
  decide +kernel

theorem first_alignment :
    FormationSensitiveElaboration.align inventoryRules inventoryChoices 249 branchContext
      (applicationPrefix 0) candidateType0 (.pi firstDomain firstBody)
      inferred0.evidence = some inferred0.evidence := by
  rw [← candidate0_shape]
  simp [FormationSensitiveElaboration.align]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
theorem first_argument_present :
    (FormationSensitiveElaboration.check inventoryRules inventoryChoices 249
      branchContext treeTm firstDomain).isSome = true := by
  rw [FormationSensitiveElaboration.check_success inventoryRules inventoryChoices]
  rw [evaluationChoices_exact]
  decide +kernel

noncomputable def firstArgumentCode := FormationSensitiveElaboration.producedTermCode inventoryRules
  inventoryChoices 249 branchContext treeTm firstDomain first_argument_present

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
theorem first_argument_replay :
    StructuralTypingReplay.check inventoryRules
      (fun code left right => code.check inventoryRules.headEq inventoryDecoder.decode left right)
      branchContext treeTm firstDomain firstArgumentCode = true := by
  unfold firstArgumentCode FormationSensitiveElaboration.producedTermCode
  rw [Option.get_congr (ho := first_argument_present)
    (congrArg (fun selected => FormationSensitiveElaboration.check inventoryRules
      selected 249 branchContext treeTm firstDomain) evaluationChoices_exact)]
  decide +kernel

noncomputable def actualCode1 : FormationSensitiveElaboration.Code Tower.Head inventoryDecoder.Code 5 :=
  .appElim firstDomain firstBody inferred0.evidence firstArgumentCode

theorem originalPrefix1 :
    FormationSensitiveElaboration.synth inventoryRules inventoryChoices 250
      branchContext (applicationPrefix 1) = some ⟨candidateType1,actualCode1⟩ := by
  have termEq : applicationPrefix 1 = .app (applicationPrefix 0) treeTm := rfl
  rw [termEq]
  have view := first_normalization
  rw [← inferred0_type] at view
  have aligned := first_alignment
  rw [← inferred0_type] at aligned
  have application := FormationSensitiveElaboration.synth_application_of inventoryRules inventoryChoices
    249 branchContext (applicationPrefix 0) treeTm
    (by intro body; change ¬Tm.const NativeNaturalVectorFamilies.vecEliminateName = .lam body; intro h; cases h)
    inferred0 firstDomain firstBody inferred0.evidence firstArgumentCode
    inferred0_origin view aligned
    (FormationSensitiveElaboration.producedTermCode_origin inventoryRules inventoryChoices
      249 branchContext treeTm firstDomain first_argument_present)
  have result : inst0 (treeTm : Tower.Tm 5) firstBody = candidateType1 := by decide +kernel
  simpa only [actualCode1,result] using application

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
theorem actualCode1_replay :
    StructuralTypingReplay.check inventoryRules
      (fun code left right => code.check inventoryRules.headEq inventoryDecoder.decode left right)
      branchContext (applicationPrefix 1) candidateType1 actualCode1 = true := by
  have termEq : applicationPrefix 1 = .app (applicationPrefix 0) treeTm := rfl
  rw [termEq]
  unfold actualCode1
  rw [StructuralTypingReplay.check]
  have previous := inferred0_replay
  rw [candidate0_shape] at previous
  rw [previous,first_argument_replay]
  decide +kernel

#print axioms first_argument_replay
#print axioms originalPrefix1
#print axioms actualCode1_replay

def secondDomain : Tower.Tm 5 :=
  match candidateType1 with | .pi domain _ => domain | _ => .head .legacyGround
def secondBody : Tower.Tm 6 :=
  match candidateType1 with | .pi _ body => body | _ => .head .legacyGround
theorem candidate1_shape : candidateType1 = .pi secondDomain secondBody := rfl
def motiveTerm : Tower.Tm 5 := NativeVectorAll.allEvidenceMotive treeTm (.var 4)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
theorem second_normalization :
    inventoryChoices.normalize 250 candidateType1 = .pi secondDomain secondBody := by
  rw [evaluationChoices_exact]
  decide +kernel

theorem second_alignment :
    FormationSensitiveElaboration.align inventoryRules inventoryChoices 250 branchContext
      (applicationPrefix 1) candidateType1 (.pi secondDomain secondBody)
      actualCode1 = some actualCode1 := by
  rw [← candidate1_shape]
  simp [FormationSensitiveElaboration.align]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
theorem motive_present :
    (FormationSensitiveElaboration.check inventoryRules inventoryChoices 250
      branchContext motiveTerm secondDomain).isSome = true := by
  rw [FormationSensitiveElaboration.check_success inventoryRules inventoryChoices]
  rw [evaluationChoices_exact]
  decide +kernel

noncomputable def motiveCode := FormationSensitiveElaboration.producedTermCode inventoryRules
  inventoryChoices 250 branchContext motiveTerm secondDomain motive_present

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
theorem motive_replay :
    StructuralTypingReplay.check inventoryRules
      (fun code left right => code.check inventoryRules.headEq inventoryDecoder.decode left right)
      branchContext motiveTerm secondDomain motiveCode = true := by
  unfold motiveCode FormationSensitiveElaboration.producedTermCode
  rw [Option.get_congr (ho := motive_present)
    (congrArg (fun selected => FormationSensitiveElaboration.check inventoryRules
      selected 250 branchContext motiveTerm secondDomain) evaluationChoices_exact)]
  decide +kernel

noncomputable def actualCode2 : FormationSensitiveElaboration.Code Tower.Head inventoryDecoder.Code 5 :=
  .appElim secondDomain secondBody actualCode1 motiveCode

theorem originalPrefix2 :
    FormationSensitiveElaboration.synth inventoryRules inventoryChoices 251
      branchContext (applicationPrefix 2) = some ⟨candidateType2,actualCode2⟩ := by
  have termEq : applicationPrefix 2 = .app (applicationPrefix 1) motiveTerm := rfl
  rw [termEq]
  have application := FormationSensitiveElaboration.synth_application_of inventoryRules inventoryChoices
    250 branchContext (applicationPrefix 1) motiveTerm
    (by intro body; change ¬Tm.app (.const NativeNaturalVectorFamilies.vecEliminateName) treeTm = .lam body; intro h; cases h)
    ⟨candidateType1,actualCode1⟩ secondDomain secondBody actualCode1 motiveCode
    originalPrefix1 second_normalization second_alignment
    (FormationSensitiveElaboration.producedTermCode_origin inventoryRules inventoryChoices
      250 branchContext motiveTerm secondDomain motive_present)
  have result : inst0 motiveTerm secondBody = candidateType2 := by decide +kernel
  simpa only [actualCode2,result] using application

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
theorem actualCode2_replay :
    StructuralTypingReplay.check inventoryRules
      (fun code left right => code.check inventoryRules.headEq inventoryDecoder.decode left right)
      branchContext (applicationPrefix 2) candidateType2 actualCode2 = true := by
  have termEq : applicationPrefix 2 = .app (applicationPrefix 1) motiveTerm := rfl
  rw [termEq]
  unfold actualCode2
  rw [StructuralTypingReplay.check]
  have previous := actualCode1_replay
  rw [candidate1_shape] at previous
  rw [previous,motive_replay]
  decide +kernel

#print axioms motive_replay
#print axioms originalPrefix2
#print axioms actualCode2_replay
end Mettapedia.GSLT.LanguageDef.PositiveInductiveVectorTreeGuest.BranchReplayComponents
