import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.FormationSensitiveNativeVectorAllCanonicalMotive

/-!
# Actual closed Vector All production through element and motive

The retained codes originate in the original bounded calls. Composition uses
the exact original application equation, and the independent checker replays
the same full codes. Closed receipts are proof data.
-/

set_option autoImplicit false
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAll.CanonicalChecking.Front
open Presentation RussellTarski
open NativeNaturalVectorFamilies

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

private theorem inf0_present : (FormationSensitiveElaboration.synth NativeVectorAll.rules NativeVectorAll.choices
    121 .nil (applicationPrefix 0)).isSome = true :=
  FormationSensitiveElaboration.synth_present_of_typeProjection NativeVectorAll.rules NativeVectorAll.choices
    121 .nil (applicationPrefix 0) (prefixType 0) (prefix_projected 0)

noncomputable def inf0 := FormationSensitiveElaboration.producedInference NativeVectorAll.rules NativeVectorAll.choices
  121 .nil (applicationPrefix 0) inf0_present
theorem origin0 : FormationSensitiveElaboration.synth NativeVectorAll.rules NativeVectorAll.choices
    121 .nil (applicationPrefix 0) = some inf0 :=
  FormationSensitiveElaboration.producedInference_origin NativeVectorAll.rules NativeVectorAll.choices
    121 .nil (applicationPrefix 0) inf0_present
theorem type0 : inf0.type = prefixType 0 :=
  FormationSensitiveElaboration.producedInference_type NativeVectorAll.rules NativeVectorAll.choices
    121 .nil (applicationPrefix 0) (prefixType 0) inf0_present (prefix_projected 0)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
theorem replay0 : StructuralTypingReplay.check
    (ConversionCode := FormationSensitiveElaboration.ConversionCode Tower.Head NativeVectorAll.decoder.Code)
    NativeVectorAll.rules
    (fun code left right => code.check NativeVectorAll.rules.headEq NativeVectorAll.decoder.decode left right)
    .nil (applicationPrefix 0) (prefixType 0) inf0.evidence = true := by
  unfold inf0 FormationSensitiveElaboration.producedInference
  rw [Option.get_congr (ho := inf0_present) (congrArg
    (fun selected => FormationSensitiveElaboration.synth NativeVectorAll.rules selected 121 .nil (applicationPrefix 0))
    ReplayComponents.choices_for_proof_evaluation)]
  decide +kernel

def domain0 : Tower.Tm 0 := match prefixType 0 with | .pi a _ => a | _ => .head .legacyGround
def body0 : Tower.Tm 1 := match prefixType 0 with | .pi _ b => b | _ => .head .legacyGround
theorem shape0 : prefixType 0 = .pi domain0 body0 := rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
theorem view0 : NativeVectorAll.choices.normalize 121 (prefixType 0) = .pi domain0 body0 := by
  rw [ReplayComponents.choices_for_proof_evaluation]
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
theorem element_present : (FormationSensitiveElaboration.check NativeVectorAll.rules NativeVectorAll.choices
    121 .nil natTm domain0).isSome = true := by
  rw [FormationSensitiveElaboration.check_success,ReplayComponents.choices_for_proof_evaluation]
  decide +kernel

noncomputable def elementCode := FormationSensitiveElaboration.producedTermCode NativeVectorAll.rules NativeVectorAll.choices
  121 .nil natTm domain0 element_present
theorem element_origin : FormationSensitiveElaboration.check NativeVectorAll.rules NativeVectorAll.choices
    121 .nil natTm domain0 = some elementCode := by
  unfold elementCode
  exact FormationSensitiveElaboration.producedTermCode_origin NativeVectorAll.rules NativeVectorAll.choices
    121 .nil natTm domain0 element_present

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
theorem element_replay : StructuralTypingReplay.check
    (ConversionCode := FormationSensitiveElaboration.ConversionCode Tower.Head NativeVectorAll.decoder.Code)
    NativeVectorAll.rules
    (fun code left right => code.check NativeVectorAll.rules.headEq NativeVectorAll.decoder.decode left right)
    .nil natTm domain0 elementCode = true := by
  unfold elementCode FormationSensitiveElaboration.producedTermCode
  rw [Option.get_congr (ho := element_present) (congrArg
    (fun selected => FormationSensitiveElaboration.check NativeVectorAll.rules selected 121 .nil natTm domain0)
    ReplayComponents.choices_for_proof_evaluation)]
  decide +kernel

private theorem aligned0 : FormationSensitiveElaboration.align NativeVectorAll.rules NativeVectorAll.choices
    121 .nil (applicationPrefix 0) (prefixType 0) (.pi domain0 body0) inf0.evidence = some inf0.evidence := by
  rw [← shape0]
  simp [FormationSensitiveElaboration.align]

noncomputable def code1 : FormationSensitiveElaboration.Code Tower.Head NativeVectorAll.decoder.Code 0 :=
  .appElim domain0 body0 inf0.evidence elementCode

theorem origin1 : FormationSensitiveElaboration.synth NativeVectorAll.rules NativeVectorAll.choices
    122 .nil (applicationPrefix 1) = some ⟨prefixType 1,code1⟩ := by
  have notLambda : ∀ body : Tower.Tm 1, applicationPrefix 0 ≠ .lam body := by
    intro body h
    rw [prefix0_source] at h
    cases h
  have view := view0
  rw [← type0] at view
  have aligned := aligned0
  rw [← type0] at aligned
  have application : FormationSensitiveElaboration.synth NativeVectorAll.rules NativeVectorAll.choices
      122 .nil (.app (applicationPrefix 0) natTm) =
      some ⟨inst0 natTm body0,StructuralTypingReplay.Code.appElim domain0 body0 inf0.evidence elementCode⟩ := by
    with_reducible
      exact FormationSensitiveElaboration.synth_application_of NativeVectorAll.rules NativeVectorAll.choices
        121 .nil (applicationPrefix 0) natTm notLambda inf0 domain0 body0 inf0.evidence elementCode
        origin0 view aligned element_origin
  rw [prefix1_source]
  have returned : inst0 (natTm : Tower.Tm 0) body0 = prefixType 1 := rfl
  simpa only [code1,returned] using application

theorem replay1 : StructuralTypingReplay.check
    (ConversionCode := FormationSensitiveElaboration.ConversionCode Tower.Head NativeVectorAll.decoder.Code)
    NativeVectorAll.rules
    (fun code left right => code.check NativeVectorAll.rules.headEq NativeVectorAll.decoder.decode left right)
    .nil (applicationPrefix 1) (prefixType 1) code1 = true := by
  rw [prefix1_source]
  unfold code1
  rw [StructuralTypingReplay.check]
  have previous := replay0
  rw [shape0] at previous
  exact congrArg₂ Bool.and (congrArg₂ Bool.and previous element_replay) (by rfl)

#print axioms origin1
#print axioms replay1

def body1 : Tower.Tm 1 := match prefixType 1 with | .pi _ b => b | _ => .head .legacyGround
theorem shape1 : prefixType 1 = .pi Motive.motiveType body1 := rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
theorem view1 : NativeVectorAll.choices.normalize 122 (prefixType 1) = .pi Motive.motiveType body1 := by
  rw [ReplayComponents.choices_for_proof_evaluation]
  decide +kernel

private theorem aligned1 : FormationSensitiveElaboration.align NativeVectorAll.rules NativeVectorAll.choices
    122 .nil (applicationPrefix 1) (prefixType 1) (.pi Motive.motiveType body1) code1 = some code1 := by
  rw [← shape1]
  simp [FormationSensitiveElaboration.align]

noncomputable def code2 : FormationSensitiveElaboration.Code Tower.Head NativeVectorAll.decoder.Code 0 :=
  .appElim Motive.motiveType body1 code1 Motive.motiveCode

theorem origin2 : FormationSensitiveElaboration.synth NativeVectorAll.rules NativeVectorAll.choices
    123 .nil (applicationPrefix 2) = some ⟨prefixType 2,code2⟩ := by
  have notLambda : ∀ body : Tower.Tm 1, applicationPrefix 1 ≠ .lam body := by
    intro body h
    rw [prefix1_source] at h
    cases h
  rw [prefix2_source]
  have application : FormationSensitiveElaboration.synth NativeVectorAll.rules NativeVectorAll.choices
      123 .nil (.app (applicationPrefix 1) (allEvidenceMotive natTm predicate)) =
      some ⟨inst0 (allEvidenceMotive natTm predicate) body1,
        StructuralTypingReplay.Code.appElim Motive.motiveType body1 code1 Motive.motiveCode⟩ := by
    with_reducible
      exact FormationSensitiveElaboration.synth_application_of NativeVectorAll.rules NativeVectorAll.choices
        122 .nil (applicationPrefix 1) (allEvidenceMotive natTm predicate) notLambda
        ⟨prefixType 1,code1⟩ Motive.motiveType body1 code1 Motive.motiveCode origin1 view1 aligned1 Motive.motiveCode_origin
  have returned : inst0 (allEvidenceMotive natTm predicate) body1 = prefixType 2 := rfl
  simpa only [code2,returned] using application

theorem replay2 : StructuralTypingReplay.check
    (ConversionCode := FormationSensitiveElaboration.ConversionCode Tower.Head NativeVectorAll.decoder.Code)
    NativeVectorAll.rules
    (fun code left right => code.check NativeVectorAll.rules.headEq NativeVectorAll.decoder.decode left right)
    .nil (applicationPrefix 2) (prefixType 2) code2 = true := by
  rw [prefix2_source]
  unfold code2
  rw [StructuralTypingReplay.check]
  have previous := replay1
  rw [shape1] at previous
  exact congrArg₂ Bool.and (congrArg₂ Bool.and previous Motive.motiveCode_replay) (by rfl)

#print axioms origin2
#print axioms replay2
end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAll.CanonicalChecking.Front
