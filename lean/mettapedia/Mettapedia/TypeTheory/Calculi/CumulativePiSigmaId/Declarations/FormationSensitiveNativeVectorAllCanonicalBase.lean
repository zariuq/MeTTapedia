import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.FormationSensitiveNativeVectorAllCanonicalAlignment
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.FormationSensitiveNativeVectorAllCanonicalFront
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveAlignmentCheckpoints
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveElaborationAssembly

/-!
# Original native Vector All production through its base argument

The original source application retains its produced alignment and base
evidence. Its assembled code is identified with the original bounded
producer result and independently replayed. Closed code receipts are proof
data. The original executable producer and checker are unchanged.
-/
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
set_option autoImplicit false
namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAll.CanonicalChecking.Base
open Presentation RussellTarski
open NativeNaturalVectorFamilies
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAll

local instance : DecidableRel NativeVectorAll.rules.headTyping :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.headTyping h u))
local instance : DecidablePred NativeVectorAll.rules.isUniverse :=
  fun h => inferInstanceAs (Decidable (Tower.rules.isUniverse h))
local instance : ∀ u v w, Decidable (NativeVectorAll.rules.join u v w) :=
  fun u v w => inferInstanceAs (Decidable (Tower.rules.join u v w))
local instance : DecidableRel NativeVectorAll.rules.cumulative :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.cumulative h u))
local instance : DecidableRel NativeVectorAll.rules.headEq :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.headEq h u))


def baseApplication : Tower.Tm 0 := applicationPrefix 3
private theorem third_alignment_accepted :
    FormationSensitiveElaboration.alignReplayAccepted NativeVectorAll.rules NativeVectorAll.decoder
      NativeVectorAll.choices 123 .nil (applicationPrefix 2) (prefixType 2) Alignment.functionView Front.code2 = true := by
  exact (FormationSensitiveElaboration.align_replay_factor NativeVectorAll.rules NativeVectorAll.decoder
    NativeVectorAll.choices 123 .nil (applicationPrefix 2) (prefixType 2)
    Alignment.functionView Front.code2).trans
      (congrArg₂ Bool.and Front.replay2 Alignment.canonical_alignmentGuard)


private theorem third_alignment_present :
    (FormationSensitiveElaboration.align NativeVectorAll.rules NativeVectorAll.choices
      123 .nil (applicationPrefix 2) (prefixType 2) Alignment.functionView Front.code2).isSome = true := by
  exact FormationSensitiveElaboration.alignment_produced_of_replay NativeVectorAll.rules NativeVectorAll.decoder NativeVectorAll.choices
    123 .nil (applicationPrefix 2) (prefixType 2) Alignment.functionView Front.code2 third_alignment_accepted

private noncomputable def actualAlignment2 :=
  FormationSensitiveElaboration.producedAlignmentCode NativeVectorAll.rules NativeVectorAll.choices
    123 .nil (applicationPrefix 2) (prefixType 2) Alignment.functionView Front.code2 third_alignment_present

private theorem actualAlignment2_origin :
    FormationSensitiveElaboration.align NativeVectorAll.rules NativeVectorAll.choices
      123 .nil (applicationPrefix 2) (prefixType 2) Alignment.functionView Front.code2 = some actualAlignment2 := by
  unfold actualAlignment2
  exact FormationSensitiveElaboration.producedAlignmentCode_origin NativeVectorAll.rules NativeVectorAll.choices
    123 .nil (applicationPrefix 2) (prefixType 2)
    Alignment.functionView Front.code2 third_alignment_present

private theorem actualAlignment2_replay :
    StructuralTypingReplay.check (ConversionCode := FormationSensitiveElaboration.ConversionCode Tower.Head NativeVectorAll.decoder.Code) NativeVectorAll.rules
      (fun code left right => code.check NativeVectorAll.rules.headEq NativeVectorAll.decoder.decode left right)
      .nil (applicationPrefix 2) Alignment.functionView actualAlignment2 = true := by
  unfold actualAlignment2
  exact (FormationSensitiveElaboration.alignReplayAccepted_eq_produced_code NativeVectorAll.rules NativeVectorAll.decoder NativeVectorAll.choices
    123 .nil (applicationPrefix 2) (prefixType 2) Alignment.functionView Front.code2
    third_alignment_present).symm.trans third_alignment_accepted


private def thirdDomain : Tower.Tm 0 :=
  match Alignment.functionView with | .pi domain _ => domain | _ => .head .legacyGround
private def thirdBody : Tower.Tm 1 :=
  match Alignment.functionView with | .pi _ body => body | _ => .head .legacyGround

private theorem motiveView_shape : Alignment.functionView = .pi thirdDomain thirdBody := rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
private theorem base_present :
    (FormationSensitiveElaboration.check NativeVectorAll.rules NativeVectorAll.choices
      123 .nil unitEvidence thirdDomain).isSome = true := by
  rw [FormationSensitiveElaboration.check_success,ReplayComponents.choices_for_proof_evaluation]
  decide +kernel

private noncomputable def actualBaseCode := FormationSensitiveElaboration.producedTermCode NativeVectorAll.rules
  NativeVectorAll.choices 123 .nil unitEvidence thirdDomain base_present

private theorem actualBaseCode_origin :
    FormationSensitiveElaboration.check NativeVectorAll.rules NativeVectorAll.choices
      123 .nil unitEvidence thirdDomain = some actualBaseCode := by
  unfold actualBaseCode
  exact FormationSensitiveElaboration.producedTermCode_origin NativeVectorAll.rules NativeVectorAll.choices
    123 .nil unitEvidence thirdDomain base_present

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
private theorem actualBaseCode_replay :
    StructuralTypingReplay.check (ConversionCode := FormationSensitiveElaboration.ConversionCode Tower.Head NativeVectorAll.decoder.Code) NativeVectorAll.rules
      (fun code left right => code.check NativeVectorAll.rules.headEq NativeVectorAll.decoder.decode left right)
      .nil unitEvidence thirdDomain actualBaseCode = true := by
  unfold actualBaseCode FormationSensitiveElaboration.producedTermCode
  rw [Option.get_congr (ho := base_present)
    (congrArg (fun selected => FormationSensitiveElaboration.check NativeVectorAll.rules
      selected 123 .nil unitEvidence thirdDomain) ReplayComponents.choices_for_proof_evaluation)]
  decide +kernel


private noncomputable def actualCode3 : FormationSensitiveElaboration.Code Tower.Head NativeVectorAll.decoder.Code 0 :=
  .appElim thirdDomain thirdBody actualAlignment2 actualBaseCode

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
private theorem originalPrefix3 :
    FormationSensitiveElaboration.synth NativeVectorAll.rules NativeVectorAll.choices
      124 .nil baseApplication = some ⟨(prefixType 3),actualCode3⟩ := by
  have termEq : baseApplication = .app (applicationPrefix 2) unitEvidence := rfl
  rw [termEq]
  have aligned := actualAlignment2_origin
  rw [motiveView_shape] at aligned
  have notLambda : ∀ body : Tower.Tm 1, (applicationPrefix 2) ≠ .lam body := by
    intro body h
    rw [prefix2_source] at h
    cases h
  have application :
      FormationSensitiveElaboration.synth NativeVectorAll.rules NativeVectorAll.choices 124 .nil
        (.app (applicationPrefix 2) unitEvidence) =
        some ⟨inst0 unitEvidence thirdBody,
          StructuralTypingReplay.Code.appElim thirdDomain thirdBody actualAlignment2 actualBaseCode⟩ := by
    with_reducible
      exact FormationSensitiveElaboration.synth_application_of (Head := Tower.Head) (RootCode := NativeVectorAll.decoder.Code)
        NativeVectorAll.rules NativeVectorAll.choices
        123 .nil (applicationPrefix 2) unitEvidence
        notLambda
        ⟨(prefixType 2),Front.code2⟩ thirdDomain thirdBody actualAlignment2 actualBaseCode
        Front.origin2 (Alignment.canonical_viewed.trans motiveView_shape) aligned
        actualBaseCode_origin
  have result : inst0 (unitEvidence : Tower.Tm 0) thirdBody = (prefixType 3) := by decide +kernel
  simpa only [actualCode3,result] using application

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
private theorem actualCode3_replay :
    StructuralTypingReplay.check (ConversionCode := FormationSensitiveElaboration.ConversionCode Tower.Head NativeVectorAll.decoder.Code) NativeVectorAll.rules
      (fun code left right => code.check NativeVectorAll.rules.headEq NativeVectorAll.decoder.decode left right)
      .nil baseApplication (prefixType 3) actualCode3 = true := by
  have termEq : baseApplication = .app (applicationPrefix 2) unitEvidence := rfl
  rw [termEq]
  unfold actualCode3
  rw [StructuralTypingReplay.check]
  have previous := actualAlignment2_replay
  rw [motiveView_shape] at previous
  rw [previous,actualBaseCode_replay]
  decide +kernel

#print axioms originalPrefix3
#print axioms actualCode3_replay

def baseApplicationType : Tower.Tm 0 := (prefixType 3)
noncomputable def baseApplicationCode :
    FormationSensitiveElaboration.Code Tower.Head NativeVectorAll.decoder.Code 0 := actualCode3

def methodType : Tower.Tm 0 :=
  match baseApplicationType with | .pi domain _ => domain | _ => .head .legacyGround
def afterMethodType : Tower.Tm 1 :=
  match baseApplicationType with | .pi _ body => body | _ => .head .legacyGround

theorem baseApplicationType_shape : baseApplicationType = .pi methodType afterMethodType := rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
theorem baseApplication_viewed :
    NativeVectorAll.choices.normalize 124 baseApplicationType = baseApplicationType := by
  rw [ReplayComponents.choices_for_proof_evaluation]
  decide +kernel

theorem baseApplication_produced :
    FormationSensitiveElaboration.synth NativeVectorAll.rules NativeVectorAll.choices
      124 .nil baseApplication = some ⟨baseApplicationType,baseApplicationCode⟩ := by
  unfold baseApplicationType baseApplicationCode
  exact originalPrefix3

theorem baseApplication_replay :
    StructuralTypingReplay.check
      (ConversionCode := FormationSensitiveElaboration.ConversionCode Tower.Head NativeVectorAll.decoder.Code)
      NativeVectorAll.rules
      (fun code left right => code.check NativeVectorAll.rules.headEq NativeVectorAll.decoder.decode left right)
      .nil baseApplication baseApplicationType baseApplicationCode = true := by
  unfold baseApplicationType baseApplicationCode
  exact actualCode3_replay

#print axioms baseApplication_produced
#print axioms baseApplication_replay
#print axioms baseApplication_viewed
end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAll.CanonicalChecking.Base
