import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.FormationSensitiveNativeVectorAllMethodComponents

/-!
# Original native Vector All evidence production and replay

The remaining method, length and vector applications assemble the exact code
returned by the original producer. The original final check at fuel 128 and
its independent term replay are proved with the unchanged source and type.
Ambient-telescope replay remains a separate publication obligation.
-/

set_option autoImplicit false
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAll.ReplayComponents
open Presentation RussellTarski
open NativeNaturalVectorFamilies
open ReplayComponents

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

private def source4 : Tower.Tm 5 := .app baseApplication methodSource
private def type4 : Tower.Tm 5 := inst0 methodSource afterMethodType
private noncomputable def code4 : FormationSensitiveElaboration.Code Tower.Head NativeVectorAll.decoder.Code 5 :=
  .appElim methodType afterMethodType baseApplicationCode methodCode

private theorem aligned4 :
    FormationSensitiveElaboration.align NativeVectorAll.rules NativeVectorAll.choices
      124 contextAPWNV baseApplication baseApplicationType (.pi methodType afterMethodType)
      baseApplicationCode = some baseApplicationCode := by
  rw [← baseApplicationType_shape]
  simp [FormationSensitiveElaboration.align]

private theorem origin4 : FormationSensitiveElaboration.synth NativeVectorAll.rules NativeVectorAll.choices
    125 contextAPWNV source4 = some ⟨type4,code4⟩ := by
  have notLambda : ∀ body : Tower.Tm 6, baseApplication ≠ .lam body := by
    intro body h
    unfold baseApplication at h
    cases h
  unfold source4 type4 code4
  with_reducible
    exact FormationSensitiveElaboration.synth_application_of NativeVectorAll.rules NativeVectorAll.choices
      124 contextAPWNV baseApplication methodSource notLambda
      ⟨baseApplicationType,baseApplicationCode⟩ methodType afterMethodType baseApplicationCode methodCode
      baseApplication_produced (baseApplication_viewed.trans baseApplicationType_shape) aligned4 methodCode_origin

private theorem replay4 : StructuralTypingReplay.check
    (ConversionCode := FormationSensitiveElaboration.ConversionCode Tower.Head NativeVectorAll.decoder.Code)
    NativeVectorAll.rules
    (fun code left right => code.check NativeVectorAll.rules.headEq NativeVectorAll.decoder.decode left right)
    contextAPWNV source4 type4 code4 = true := by
  unfold source4 code4
  rw [StructuralTypingReplay.check]
  have base : StructuralTypingReplay.check
      (ConversionCode := FormationSensitiveElaboration.ConversionCode Tower.Head NativeVectorAll.decoder.Code)
      NativeVectorAll.rules
      (fun code left right => code.check NativeVectorAll.rules.headEq NativeVectorAll.decoder.decode left right)
      contextAPWNV baseApplication (.pi methodType afterMethodType) baseApplicationCode = true := by
    change StructuralTypingReplay.check NativeVectorAll.rules
      (fun code left right => code.check NativeVectorAll.rules.headEq NativeVectorAll.decoder.decode left right)
      contextAPWNV baseApplication baseApplicationType baseApplicationCode = true
    exact baseApplication_replay
  exact congrArg₂ Bool.and (congrArg₂ Bool.and base methodCode_replay) (by simp [type4])

private def lengthDomain : Tower.Tm 5 := match type4 with | .pi a _ => a | _ => .head .legacyGround
private def lengthBody : Tower.Tm 6 := match type4 with | .pi _ b => b | _ => .head .legacyGround
private theorem shape4 : type4 = .pi lengthDomain lengthBody := rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
private theorem view4 : NativeVectorAll.choices.normalize 125 type4 = .pi lengthDomain lengthBody := by
  rw [choices_for_proof_evaluation]
  decide +kernel

private theorem length_checked : FormationSensitiveElaboration.check NativeVectorAll.rules NativeVectorAll.choices
    125 contextAPWNV (.var 1) lengthDomain = some (.var) := by rfl

private theorem length_replay : StructuralTypingReplay.check
    (ConversionCode := FormationSensitiveElaboration.ConversionCode Tower.Head NativeVectorAll.decoder.Code)
    NativeVectorAll.rules
    (fun code left right => code.check NativeVectorAll.rules.headEq NativeVectorAll.decoder.decode left right)
    contextAPWNV (.var 1) lengthDomain (.var) = true := by rfl

private theorem aligned5 :
    FormationSensitiveElaboration.align NativeVectorAll.rules NativeVectorAll.choices
      125 contextAPWNV source4 type4 (.pi lengthDomain lengthBody) code4 = some code4 := by
  rw [← shape4]
  simp [FormationSensitiveElaboration.align]

private def source5 : Tower.Tm 5 := .app source4 (.var 1)
private def type5 : Tower.Tm 5 := inst0 (.var 1) lengthBody
private noncomputable def code5 : FormationSensitiveElaboration.Code Tower.Head NativeVectorAll.decoder.Code 5 :=
  .appElim lengthDomain lengthBody code4 .var

private theorem origin5 : FormationSensitiveElaboration.synth NativeVectorAll.rules NativeVectorAll.choices
    126 contextAPWNV source5 = some ⟨type5,code5⟩ := by
  have notLambda : ∀ body : Tower.Tm 6, source4 ≠ .lam body := by
    intro body h
    unfold source4 at h
    cases h
  unfold source5 type5 code5
  with_reducible
    exact FormationSensitiveElaboration.synth_application_of NativeVectorAll.rules NativeVectorAll.choices
      125 contextAPWNV source4 (.var 1) notLambda ⟨type4,code4⟩ lengthDomain lengthBody code4 .var
      origin4 view4 aligned5 length_checked

private theorem replay5 : StructuralTypingReplay.check
    (ConversionCode := FormationSensitiveElaboration.ConversionCode Tower.Head NativeVectorAll.decoder.Code)
    NativeVectorAll.rules
    (fun code left right => code.check NativeVectorAll.rules.headEq NativeVectorAll.decoder.decode left right)
    contextAPWNV source5 type5 code5 = true := by
  unfold source5 code5
  rw [StructuralTypingReplay.check]
  have previous := replay4
  rw [shape4] at previous
  exact congrArg₂ Bool.and (congrArg₂ Bool.and previous length_replay) (by simp [type5])

private def vectorDomain : Tower.Tm 5 := match type5 with | .pi a _ => a | _ => .head .legacyGround
private def vectorBody : Tower.Tm 6 := match type5 with | .pi _ b => b | _ => .head .legacyGround
private theorem shape5 : type5 = .pi vectorDomain vectorBody := rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
private theorem view5 : NativeVectorAll.choices.normalize 126 type5 = .pi vectorDomain vectorBody := by
  rw [choices_for_proof_evaluation]
  decide +kernel

private theorem vector_checked : FormationSensitiveElaboration.check NativeVectorAll.rules NativeVectorAll.choices
    126 contextAPWNV (.var 0) vectorDomain = some (.var) := by rfl

private theorem vector_replay : StructuralTypingReplay.check
    (ConversionCode := FormationSensitiveElaboration.ConversionCode Tower.Head NativeVectorAll.decoder.Code)
    NativeVectorAll.rules
    (fun code left right => code.check NativeVectorAll.rules.headEq NativeVectorAll.decoder.decode left right)
    contextAPWNV (.var 0) vectorDomain (.var) = true := by rfl

private theorem aligned6 :
    FormationSensitiveElaboration.align NativeVectorAll.rules NativeVectorAll.choices
      126 contextAPWNV source5 type5 (.pi vectorDomain vectorBody) code5 = some code5 := by
  rw [← shape5]
  simp [FormationSensitiveElaboration.align]

private def source6 : Tower.Tm 5 := .app source5 (.var 0)
private def type6 : Tower.Tm 5 := inst0 (.var 0) vectorBody
private noncomputable def code6 : FormationSensitiveElaboration.Code Tower.Head NativeVectorAll.decoder.Code 5 :=
  .appElim vectorDomain vectorBody code5 .var

private theorem origin6 : FormationSensitiveElaboration.synth NativeVectorAll.rules NativeVectorAll.choices
    127 contextAPWNV source6 = some ⟨type6,code6⟩ := by
  have notLambda : ∀ body : Tower.Tm 6, source5 ≠ .lam body := by
    intro body h
    unfold source5 at h
    cases h
  unfold source6 type6 code6
  with_reducible
    exact FormationSensitiveElaboration.synth_application_of NativeVectorAll.rules NativeVectorAll.choices
      126 contextAPWNV source5 (.var 0) notLambda ⟨type5,code5⟩ vectorDomain vectorBody code5 .var
      origin5 view5 aligned6 vector_checked

private theorem replay6 : StructuralTypingReplay.check
    (ConversionCode := FormationSensitiveElaboration.ConversionCode Tower.Head NativeVectorAll.decoder.Code)
    NativeVectorAll.rules
    (fun code left right => code.check NativeVectorAll.rules.headEq NativeVectorAll.decoder.decode left right)
    contextAPWNV source6 type6 code6 = true := by
  unfold source6 code6
  rw [StructuralTypingReplay.check]
  have previous := replay5
  rw [shape5] at previous
  exact congrArg₂ Bool.and (congrArg₂ Bool.and previous vector_replay) (by simp [type6])

#print axioms origin6
#print axioms replay6

private theorem source6_eq : source6 = allEvidenceControl := by
  unfold source6 source5 source4 baseApplication
  rw [motiveApplication_source,methodSource_eq]
  rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
private theorem type6_eq : type6 = allTypeControl := by
  rfl

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

private theorem final_aligned : FormationSensitiveElaboration.align NativeVectorAll.rules NativeVectorAll.choices
    127 contextAPWNV source6 type6 allTypeControl code6 = some code6 := by
  rw [type6_eq]
  simp [FormationSensitiveElaboration.align]

private theorem final_check_origin :
    FormationSensitiveElaboration.check NativeVectorAll.rules NativeVectorAll.choices
      128 contextAPWNV allEvidenceControl allTypeControl = some code6 := by
  rw [← source6_eq]
  have prior := origin6
  have aligned := final_aligned
  change FormationSensitiveElaboration.synth NativeVectorAll.rules NativeVectorAll.choices
    127 contextAPWNV (.app source5 (.var 0)) = some ⟨type6,code6⟩ at prior
  change FormationSensitiveElaboration.align NativeVectorAll.rules NativeVectorAll.choices
    127 contextAPWNV (.app source5 (.var 0)) type6 allTypeControl code6 = some code6 at aligned
  unfold source6
  with_reducible
    exact check_application_of NativeVectorAll.rules NativeVectorAll.choices
      127 contextAPWNV source5 (.var 0) allTypeControl ⟨type6,code6⟩ code6 prior aligned

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

private theorem full_term_replay : FormationSensitiveElaboration.termReplayAccepted NativeVectorAll.rules NativeVectorAll.decoder
    NativeVectorAll.choices 128 contextAPWNV allEvidenceControl allTypeControl = true := by
  have checked : StructuralTypingReplay.check
      (ConversionCode := FormationSensitiveElaboration.ConversionCode Tower.Head NativeVectorAll.decoder.Code)
      NativeVectorAll.rules
      (fun code left right => code.check NativeVectorAll.rules.headEq NativeVectorAll.decoder.decode left right)
      contextAPWNV allEvidenceControl allTypeControl code6 = true := by
    change StructuralTypingReplay.check NativeVectorAll.rules
      (fun code left right => code.check NativeVectorAll.rules.headEq NativeVectorAll.decoder.decode left right)
      contextAPWNV source6 type6 code6 = true
    exact replay6
  exact termReplayAccepted_of_origin NativeVectorAll.rules NativeVectorAll.decoder NativeVectorAll.choices
    128 contextAPWNV allEvidenceControl allTypeControl code6 final_check_origin checked

#print axioms final_check_origin
#print axioms full_term_replay

noncomputable def evidenceCode : FormationSensitiveElaboration.Code Tower.Head NativeVectorAll.decoder.Code 5 := code6
def evidenceFunction : Tower.Tm 5 := source5

theorem evidence_application : allEvidenceControl = .app evidenceFunction (.var 0) := by
  rw [← source6_eq]
  rfl

theorem evidence_synth_origin :
    FormationSensitiveElaboration.synth NativeVectorAll.rules NativeVectorAll.choices
      127 contextAPWNV allEvidenceControl = some ⟨allTypeControl,evidenceCode⟩ := by
  unfold evidenceCode
  have produced := origin6
  rw [source6_eq,type6_eq] at produced
  exact produced

theorem evidenceCode_origin :
    FormationSensitiveElaboration.check NativeVectorAll.rules NativeVectorAll.choices
      128 contextAPWNV allEvidenceControl allTypeControl = some evidenceCode := by
  unfold evidenceCode
  exact final_check_origin

theorem evidenceCode_replay : StructuralTypingReplay.check
    (ConversionCode := FormationSensitiveElaboration.ConversionCode Tower.Head NativeVectorAll.decoder.Code)
    NativeVectorAll.rules
    (fun code left right => code.check NativeVectorAll.rules.headEq NativeVectorAll.decoder.decode left right)
    contextAPWNV allEvidenceControl allTypeControl evidenceCode = true := by
  unfold evidenceCode
  change StructuralTypingReplay.check NativeVectorAll.rules
    (fun code left right => code.check NativeVectorAll.rules.headEq NativeVectorAll.decoder.decode left right)
    contextAPWNV source6 type6 code6 = true
  exact replay6

theorem evidence_term_replay : FormationSensitiveElaboration.termReplayAccepted NativeVectorAll.rules NativeVectorAll.decoder
    NativeVectorAll.choices 128 contextAPWNV allEvidenceControl allTypeControl = true :=
  full_term_replay

#print axioms evidenceCode_origin
#print axioms evidence_synth_origin
#print axioms evidenceCode_replay
#print axioms evidence_term_replay
end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAll.ReplayComponents
