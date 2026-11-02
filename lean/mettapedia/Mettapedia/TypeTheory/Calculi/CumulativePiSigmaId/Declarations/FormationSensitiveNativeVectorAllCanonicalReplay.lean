import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.FormationSensitiveNativeVectorAllCanonicalBase
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.FormationSensitiveNativeVectorAllCanonicalMethod
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.FormationSensitiveNativeVectorAllCanonicalFinalAlignment

/-!
# Original two-position closed Vector All publication

Every application and final alignment retains the original bounded producer's
full code. Its original independent replay and empty-telescope publication
are checked for the unchanged two-position control at fuel 128.
-/

set_option autoImplicit false
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAll.CanonicalChecking.Suffix
open Presentation RussellTarski
open NativeNaturalVectorFamilies CanonicalAdequacy
open CanonicalChecking.Base
open CanonicalChecking.Method

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

def source4 : Tower.Tm 0 := .app baseApplication methodSource
def type4 : Tower.Tm 0 := inst0 methodSource afterMethodType
noncomputable def code4 : FormationSensitiveElaboration.Code Tower.Head NativeVectorAll.decoder.Code 0 :=
  .appElim Base.methodType afterMethodType baseApplicationCode methodCode

private theorem aligned4 :
    FormationSensitiveElaboration.align NativeVectorAll.rules NativeVectorAll.choices
      124 .nil baseApplication baseApplicationType (.pi Base.methodType afterMethodType)
      baseApplicationCode = some baseApplicationCode := by
  rw [← baseApplicationType_shape]
  simp [FormationSensitiveElaboration.align]

theorem origin4 : FormationSensitiveElaboration.synth NativeVectorAll.rules NativeVectorAll.choices
    125 .nil source4 = some ⟨type4,code4⟩ := by
  have notLambda : ∀ body : Tower.Tm 1, baseApplication ≠ .lam body := by
    intro body h
    unfold baseApplication at h
    cases h
  have checked : FormationSensitiveElaboration.check NativeVectorAll.rules NativeVectorAll.choices
      124 .nil methodSource Base.methodType = some methodCode := by
    change FormationSensitiveElaboration.check NativeVectorAll.rules NativeVectorAll.choices
      124 .nil methodSource Method.domain = some methodCode
    exact methodCode_origin
  unfold source4 type4 code4
  with_reducible
    exact FormationSensitiveElaboration.synth_application_of NativeVectorAll.rules NativeVectorAll.choices
      124 .nil baseApplication methodSource notLambda
      ⟨baseApplicationType,baseApplicationCode⟩ Base.methodType afterMethodType baseApplicationCode methodCode
      baseApplication_produced (baseApplication_viewed.trans baseApplicationType_shape) aligned4 checked

theorem replay4 : StructuralTypingReplay.check
    (ConversionCode := FormationSensitiveElaboration.ConversionCode Tower.Head NativeVectorAll.decoder.Code)
    NativeVectorAll.rules
    (fun code left right => code.check NativeVectorAll.rules.headEq NativeVectorAll.decoder.decode left right)
    .nil source4 type4 code4 = true := by
  unfold source4 code4
  rw [StructuralTypingReplay.check]
  have base : StructuralTypingReplay.check
      (ConversionCode := FormationSensitiveElaboration.ConversionCode Tower.Head NativeVectorAll.decoder.Code)
      NativeVectorAll.rules
      (fun code left right => code.check NativeVectorAll.rules.headEq NativeVectorAll.decoder.decode left right)
      .nil baseApplication (.pi Base.methodType afterMethodType) baseApplicationCode = true := by
    change StructuralTypingReplay.check NativeVectorAll.rules
      (fun code left right => code.check NativeVectorAll.rules.headEq NativeVectorAll.decoder.decode left right)
      .nil baseApplication baseApplicationType baseApplicationCode = true
    exact baseApplication_replay
  have method : StructuralTypingReplay.check
      (ConversionCode := FormationSensitiveElaboration.ConversionCode Tower.Head NativeVectorAll.decoder.Code)
      NativeVectorAll.rules
      (fun code left right => code.check NativeVectorAll.rules.headEq NativeVectorAll.decoder.decode left right)
      .nil methodSource Base.methodType methodCode = true := by
    change StructuralTypingReplay.check NativeVectorAll.rules
      (fun code left right => code.check NativeVectorAll.rules.headEq NativeVectorAll.decoder.decode left right)
      .nil methodSource Method.domain methodCode = true
    exact methodCode_replay
  exact congrArg₂ Bool.and (congrArg₂ Bool.and base method) (by simp [type4])

def lengthDomain : Tower.Tm 0 := match type4 with | .pi a _ => a | _ => .head .legacyGround
def lengthBody : Tower.Tm 1 := match type4 with | .pi _ b => b | _ => .head .legacyGround
theorem shape4 : type4 = .pi lengthDomain lengthBody := rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
theorem view4 : NativeVectorAll.choices.normalize 125 type4 = .pi lengthDomain lengthBody := by
  rw [ReplayComponents.choices_for_proof_evaluation]
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
private theorem length_present : (FormationSensitiveElaboration.check NativeVectorAll.rules NativeVectorAll.choices
    125 .nil (numeral values.length) lengthDomain).isSome = true := by
  rw [FormationSensitiveElaboration.check_success,ReplayComponents.choices_for_proof_evaluation]
  decide +kernel

noncomputable def lengthCode := FormationSensitiveElaboration.producedTermCode NativeVectorAll.rules NativeVectorAll.choices
  125 .nil (numeral values.length) lengthDomain length_present

private theorem length_checked : FormationSensitiveElaboration.check NativeVectorAll.rules NativeVectorAll.choices
    125 .nil (numeral values.length) lengthDomain = some lengthCode := by
  unfold lengthCode
  exact FormationSensitiveElaboration.producedTermCode_origin NativeVectorAll.rules NativeVectorAll.choices
    125 .nil (numeral values.length) lengthDomain length_present

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
private theorem length_replay : StructuralTypingReplay.check
    (ConversionCode := FormationSensitiveElaboration.ConversionCode Tower.Head NativeVectorAll.decoder.Code)
    NativeVectorAll.rules
    (fun code left right => code.check NativeVectorAll.rules.headEq NativeVectorAll.decoder.decode left right)
    .nil (numeral values.length) lengthDomain lengthCode = true := by
  unfold lengthCode FormationSensitiveElaboration.producedTermCode
  rw [Option.get_congr (ho := length_present) (congrArg
    (fun selected => FormationSensitiveElaboration.check NativeVectorAll.rules selected
      125 .nil (numeral values.length) lengthDomain) ReplayComponents.choices_for_proof_evaluation)]
  decide +kernel

private theorem aligned5 :
    FormationSensitiveElaboration.align NativeVectorAll.rules NativeVectorAll.choices
      125 .nil source4 type4 (.pi lengthDomain lengthBody) code4 = some code4 := by
  rw [← shape4]
  simp [FormationSensitiveElaboration.align]

def source5 : Tower.Tm 0 := .app source4 (numeral values.length)
def type5 : Tower.Tm 0 := inst0 (numeral values.length) lengthBody
noncomputable def code5 : FormationSensitiveElaboration.Code Tower.Head NativeVectorAll.decoder.Code 0 :=
  .appElim lengthDomain lengthBody code4 lengthCode

theorem origin5 : FormationSensitiveElaboration.synth NativeVectorAll.rules NativeVectorAll.choices
    126 .nil source5 = some ⟨type5,code5⟩ := by
  have notLambda : ∀ body : Tower.Tm 1, source4 ≠ .lam body := by
    intro body h
    unfold source4 at h
    cases h
  unfold source5 type5 code5
  with_reducible
    exact FormationSensitiveElaboration.synth_application_of NativeVectorAll.rules NativeVectorAll.choices
      125 .nil source4 (numeral values.length) notLambda ⟨type4,code4⟩ lengthDomain lengthBody code4 lengthCode
      origin4 view4 aligned5 length_checked

theorem replay5 : StructuralTypingReplay.check
    (ConversionCode := FormationSensitiveElaboration.ConversionCode Tower.Head NativeVectorAll.decoder.Code)
    NativeVectorAll.rules
    (fun code left right => code.check NativeVectorAll.rules.headEq NativeVectorAll.decoder.decode left right)
    .nil source5 type5 code5 = true := by
  unfold source5 code5
  rw [StructuralTypingReplay.check]
  have previous := replay4
  rw [shape4] at previous
  exact congrArg₂ Bool.and (congrArg₂ Bool.and previous length_replay) (by simp [type5])

def vectorDomain : Tower.Tm 0 := match type5 with | .pi a _ => a | _ => .head .legacyGround
def vectorBody : Tower.Tm 1 := match type5 with | .pi _ b => b | _ => .head .legacyGround
theorem shape5 : type5 = .pi vectorDomain vectorBody := rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
theorem view5 : NativeVectorAll.choices.normalize 126 type5 = .pi vectorDomain vectorBody := by
  rw [ReplayComponents.choices_for_proof_evaluation]
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
private theorem vector_present : (FormationSensitiveElaboration.check NativeVectorAll.rules NativeVectorAll.choices
    126 .nil (encodeVector natTm values) vectorDomain).isSome = true := by
  rw [FormationSensitiveElaboration.check_success,ReplayComponents.choices_for_proof_evaluation]
  decide +kernel

noncomputable def vectorCode := FormationSensitiveElaboration.producedTermCode NativeVectorAll.rules NativeVectorAll.choices
  126 .nil (encodeVector natTm values) vectorDomain vector_present

private theorem vector_checked : FormationSensitiveElaboration.check NativeVectorAll.rules NativeVectorAll.choices
    126 .nil (encodeVector natTm values) vectorDomain = some vectorCode := by
  unfold vectorCode
  exact FormationSensitiveElaboration.producedTermCode_origin NativeVectorAll.rules NativeVectorAll.choices
    126 .nil (encodeVector natTm values) vectorDomain vector_present

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
private theorem vector_replay : StructuralTypingReplay.check
    (ConversionCode := FormationSensitiveElaboration.ConversionCode Tower.Head NativeVectorAll.decoder.Code)
    NativeVectorAll.rules
    (fun code left right => code.check NativeVectorAll.rules.headEq NativeVectorAll.decoder.decode left right)
    .nil (encodeVector natTm values) vectorDomain vectorCode = true := by
  unfold vectorCode FormationSensitiveElaboration.producedTermCode
  rw [Option.get_congr (ho := vector_present) (congrArg
    (fun selected => FormationSensitiveElaboration.check NativeVectorAll.rules selected
      126 .nil (encodeVector natTm values) vectorDomain) ReplayComponents.choices_for_proof_evaluation)]
  decide +kernel

private theorem aligned6 :
    FormationSensitiveElaboration.align NativeVectorAll.rules NativeVectorAll.choices
      126 .nil source5 type5 (.pi vectorDomain vectorBody) code5 = some code5 := by
  rw [← shape5]
  simp [FormationSensitiveElaboration.align]

def source6 : Tower.Tm 0 := .app source5 (encodeVector natTm values)
def type6 : Tower.Tm 0 := inst0 (encodeVector natTm values) vectorBody
noncomputable def code6 : FormationSensitiveElaboration.Code Tower.Head NativeVectorAll.decoder.Code 0 :=
  .appElim vectorDomain vectorBody code5 vectorCode

theorem origin6 : FormationSensitiveElaboration.synth NativeVectorAll.rules NativeVectorAll.choices
    127 .nil source6 = some ⟨type6,code6⟩ := by
  have notLambda : ∀ body : Tower.Tm 1, source5 ≠ .lam body := by
    intro body h
    unfold source5 at h
    cases h
  unfold source6 type6 code6
  with_reducible
    exact FormationSensitiveElaboration.synth_application_of NativeVectorAll.rules NativeVectorAll.choices
      126 .nil source5 (encodeVector natTm values) notLambda ⟨type5,code5⟩ vectorDomain vectorBody code5 vectorCode
      origin5 view5 aligned6 vector_checked

theorem replay6 : StructuralTypingReplay.check
    (ConversionCode := FormationSensitiveElaboration.ConversionCode Tower.Head NativeVectorAll.decoder.Code)
    NativeVectorAll.rules
    (fun code left right => code.check NativeVectorAll.rules.headEq NativeVectorAll.decoder.decode left right)
    .nil source6 type6 code6 = true := by
  unfold source6 code6
  rw [StructuralTypingReplay.check]
  have previous := replay5
  rw [shape5] at previous
  exact congrArg₂ Bool.and (congrArg₂ Bool.and previous vector_replay) (by simp [type6])

#print axioms origin6
#print axioms replay6

theorem source6_eq : source6 = CanonicalChecking.evidence := by
  unfold source6 source5 source4 Base.baseApplication
  rw [prefix3_source,prefix2_source,prefix1_source,prefix0_source,Method.methodSource_eq]
  rfl

theorem type6_eq : type6 = prefixType 6 := by rfl

private theorem final_accepted : FormationSensitiveElaboration.alignReplayAccepted NativeVectorAll.rules NativeVectorAll.decoder
    NativeVectorAll.choices 127 .nil source6 type6 CanonicalChecking.type code6 = true := by
  have guard := FinalAlignment.final_alignmentGuard
  rw [← type6_eq] at guard
  exact (FormationSensitiveElaboration.align_replay_factor NativeVectorAll.rules NativeVectorAll.decoder
    NativeVectorAll.choices 127 .nil source6 type6 CanonicalChecking.type code6).trans
      (congrArg₂ Bool.and replay6 guard)

private theorem final_present : (FormationSensitiveElaboration.align NativeVectorAll.rules NativeVectorAll.choices
    127 .nil source6 type6 CanonicalChecking.type code6).isSome = true :=
  FormationSensitiveElaboration.alignment_produced_of_replay NativeVectorAll.rules NativeVectorAll.decoder NativeVectorAll.choices
    127 .nil source6 type6 CanonicalChecking.type code6 final_accepted

noncomputable def finalCode := FormationSensitiveElaboration.producedAlignmentCode NativeVectorAll.rules NativeVectorAll.choices
  127 .nil source6 type6 CanonicalChecking.type code6 final_present

theorem finalCode_origin : FormationSensitiveElaboration.align NativeVectorAll.rules NativeVectorAll.choices
    127 .nil source6 type6 CanonicalChecking.type code6 = some finalCode := by
  unfold finalCode
  exact FormationSensitiveElaboration.producedAlignmentCode_origin NativeVectorAll.rules NativeVectorAll.choices
    127 .nil source6 type6 CanonicalChecking.type code6 final_present

theorem finalCode_replay : StructuralTypingReplay.check
    (ConversionCode := FormationSensitiveElaboration.ConversionCode Tower.Head NativeVectorAll.decoder.Code)
    NativeVectorAll.rules
    (fun code left right => code.check NativeVectorAll.rules.headEq NativeVectorAll.decoder.decode left right)
    .nil source6 CanonicalChecking.type finalCode = true := by
  unfold finalCode
  exact (FormationSensitiveElaboration.alignReplayAccepted_eq_produced_code NativeVectorAll.rules NativeVectorAll.decoder
    NativeVectorAll.choices 127 .nil source6 type6 CanonicalChecking.type code6 final_present).symm.trans final_accepted

private theorem check_application_of {Head : Type} {RootCode : Nat → Type}
    (R : Rules Head) (choices : FormationSensitiveElaboration.Choices Head RootCode) [DecidableEq Head]
    (fuel : Nat) {n : Nat} (context : Ctx Head n) (function argument expected : Tm Head n)
    (inferred : FormationSensitiveElaboration.Inferred Head RootCode n)
    (result : FormationSensitiveElaboration.Code Head RootCode n)
    (prior : FormationSensitiveElaboration.synth R choices fuel context (.app function argument) = some inferred)
    (aligned : FormationSensitiveElaboration.align R choices fuel context (.app function argument)
      inferred.type expected inferred.evidence = some result) :
    FormationSensitiveElaboration.check R choices (fuel+1) context (.app function argument) expected = some result := by
  simp only [FormationSensitiveElaboration.check,prior,aligned,Option.bind_eq_bind,Option.bind_some]

theorem check_origin : FormationSensitiveElaboration.check NativeVectorAll.rules NativeVectorAll.choices
    128 .nil CanonicalChecking.evidence CanonicalChecking.type = some finalCode := by
  rw [← source6_eq]
  have prior := origin6
  have aligned := finalCode_origin
  change FormationSensitiveElaboration.synth NativeVectorAll.rules NativeVectorAll.choices
    127 .nil (.app source5 (encodeVector natTm values)) = some ⟨type6,code6⟩ at prior
  change FormationSensitiveElaboration.align NativeVectorAll.rules NativeVectorAll.choices
    127 .nil (.app source5 (encodeVector natTm values)) type6 CanonicalChecking.type code6 = some finalCode at aligned
  unfold source6
  with_reducible
    exact check_application_of NativeVectorAll.rules NativeVectorAll.choices 127 .nil source5
      (encodeVector natTm values) CanonicalChecking.type ⟨type6,code6⟩ finalCode prior aligned

private theorem termReplayAccepted_of_origin {Head : Type} (R : Rules Head) [DecidableEq Head]
    [DecidableRel R.headTyping] [DecidablePred R.isUniverse]
    [∀ u v w, Decidable (R.join u v w)] [DecidableRel R.cumulative] [DecidableRel R.headEq]
    (decoder : StructuralConversionCode.RootDecoder R.computation)
    (choices : FormationSensitiveElaboration.Choices Head decoder.Code) (fuel : Nat) {n : Nat}
    (context : Ctx Head n) (term type : Tm Head n)
    (code : FormationSensitiveElaboration.Code Head decoder.Code n)
    (produced : FormationSensitiveElaboration.check R choices fuel context term type = some code)
    (checked : StructuralTypingReplay.check R
      (fun code left right => code.check R.headEq decoder.decode left right) context term type code = true) :
    FormationSensitiveElaboration.termReplayAccepted R decoder choices fuel context term type = true := by
  unfold FormationSensitiveElaboration.termReplayAccepted
  rw [produced]
  exact checked

theorem canonical_term_replay : FormationSensitiveElaboration.termReplayAccepted NativeVectorAll.rules NativeVectorAll.decoder
    NativeVectorAll.choices 128 .nil CanonicalChecking.evidence CanonicalChecking.type = true := by
  have checked : StructuralTypingReplay.check
      (ConversionCode := FormationSensitiveElaboration.ConversionCode Tower.Head NativeVectorAll.decoder.Code)
      NativeVectorAll.rules
      (fun code left right => code.check NativeVectorAll.rules.headEq NativeVectorAll.decoder.decode left right)
      .nil CanonicalChecking.evidence CanonicalChecking.type finalCode = true := by
    change StructuralTypingReplay.check NativeVectorAll.rules
      (fun code left right => code.check NativeVectorAll.rules.headEq NativeVectorAll.decoder.decode left right)
      .nil source6 CanonicalChecking.type finalCode = true
    exact finalCode_replay
  exact termReplayAccepted_of_origin NativeVectorAll.rules NativeVectorAll.decoder NativeVectorAll.choices
    128 .nil CanonicalChecking.evidence CanonicalChecking.type finalCode check_origin checked

theorem canonical_accepted : NativeVectorAll.accepted .nil CanonicalChecking.evidence CanonicalChecking.type = true := by
  rw [NativeVectorAll.accepted,FormationSensitiveElaboration.elaborate_isSome_eq_components]
  exact Bool.and_eq_true_iff.mpr ⟨FormationSensitiveElaboration.contextReplayAccepted_nil _ _ _ _,canonical_term_replay⟩

#print axioms check_origin
#print axioms canonical_term_replay
#print axioms canonical_accepted
end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAll.CanonicalChecking.Suffix
