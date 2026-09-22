import Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentQuotientInterpretation
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.FormationSensitiveQuotientIdentity

/-!
# Native identity formation and reflexivity on the shared quotient data

The actual native identity and reflexivity constructors agree with their
constructed operations on the same formed conversion-class CwF and the same
shared interpretation. Independently supplied graph witnesses can use
different universe witnesses or convertible representatives; no equality of
those raw witnesses is required.

This attachment covers only formation and reflexivity. It supplies no total
based-J operation, declaration-level extension, K/UIP principle, independent
semantic host, or jointly qualified complete constructor record.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentQuotientIdentity

open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
open Presentation FormationSensitive SharedJudgmentFragment
open FormationSensitiveContextual
open SharedJudgmentQuotientInterpretation (data context)

variable {assembly : Assembly}

/-- The two actual term representatives have the same retained annotation
and code. Their class equality is proved through the native relation. -/
private theorem actual_term_class {n : Nat}
    {source : SharedJudgmentInterpretation.Context assembly n}
    {code annotation : Tower.Tm n}
    {semanticType : (QuotientCwf.cwf assembly.rules).Ty ((data assembly).ctx source)}
    {value : (QuotientCwf.cwf assembly.rules).Tm ((data assembly).ctx source) semanticType}
    (meaning : (data assembly).term source code annotation semanticType value)
    {actualType : TypeOver (context source)} (actual : Term (context source) actualType)
    (typeCode : actualType.code = annotation) (termCode : actual.code = code) :
    QTerm.mk actual = value.val := by
  obtain ⟨otherType, otherAnnotation, other, otherCode, _, otherClass⟩ := meaning
  refine ((QTerm.mk_eq_iff actual other).mpr ?_).trans otherClass
  constructor
  · rw [typeCode, otherAnnotation]
    exact .refl _
  · rw [termCode, otherCode]
    exact .refl _

/-- This holds on every admitted native context of the supplied assembly;
the independent level witness is retained by the native type representative. -/
theorem identity_formation_meaning :
    SharedJudgmentTypeInterpretation.IdentityFormationMeaning (data assembly)
      (QuotientIdentity.formation assembly.rules) := by
  intro n source type left right level semanticType semanticLeft semanticRight
    _ _ leftAdmitted rightAdmitted typeMeaning leftMeaning rightMeaning
  obtain ⟨actual, typeCode, typeClass⟩ := typeMeaning
  let actualLeft : Term (context source) actual :=
    ⟨left, by rw [typeCode]; exact leftAdmitted.typing⟩
  let actualRight : Term (context source) actual :=
    ⟨right, by rw [typeCode]; exact rightAdmitted.typing⟩
  have leftClass := actual_term_class leftMeaning actualLeft typeCode rfl
  have rightClass := actual_term_class rightMeaning actualRight typeCode rfl
  refine ⟨QuotientIdentity.nativeId actual actualLeft actualRight, ?_, ?_⟩
  · change Presentation.Tm.id actual.code left right = .id type left right
    rw [typeCode]
  · exact (QuotientIdentity.idTy_eq_native semanticLeft semanticRight actual
      actualLeft actualRight typeClass leftClass rightClass).symm

theorem reflexivity_meaning :
    SharedJudgmentTypeInterpretation.ReflexivityMeaning (data assembly)
      (QuotientIdentity.reflexivity assembly.rules) := by
  intro n source type left semanticType semanticLeft leftAdmitted typeMeaning leftMeaning
  obtain ⟨actual, typeCode, typeClass⟩ := typeMeaning
  let actualLeft : Term (context source) actual :=
    ⟨left, by rw [typeCode]; exact leftAdmitted.typing⟩
  have leftClass := actual_term_class leftMeaning actualLeft typeCode rfl
  refine ⟨QuotientIdentity.nativeId actual actualLeft actualLeft, ?_,
    QuotientIdentity.nativeRefl actualLeft, rfl, ?_, ?_⟩
  · change Presentation.Tm.id actual.code left left = .id type left left
    rw [typeCode]
  · exact (QuotientIdentity.idTy_eq_native semanticLeft semanticLeft actual
      actualLeft actualLeft typeClass leftClass leftClass).symm
  · exact (QuotientIdentity.refl_eq_native semanticLeft actual actualLeft typeClass leftClass).symm

theorem formation_and_reflexivity :
    SharedJudgmentTypeInterpretation.IdentityFormationMeaning (data assembly)
        (QuotientIdentity.formation assembly.rules) ∧
      SharedJudgmentTypeInterpretation.ReflexivityMeaning (data assembly)
        (QuotientIdentity.reflexivity assembly.rules) :=
  ⟨identity_formation_meaning, reflexivity_meaning⟩

namespace Controls

noncomputable def resultIdentity (wire : NativeWireData.Wire) :
    (QuotientCwf.cwf common.rules).Ty ((data common).ctx .nil) :=
  QuotientIdentity.idTy QuotientCwf.Controls.wireType
    (QuotientCwf.Controls.result wire) (QuotientCwf.Controls.result wire)

noncomputable def resultReflexivity (wire : NativeWireData.Wire) :
    (QuotientCwf.cwf common.rules).Tm ((data common).ctx .nil) (resultIdentity wire) :=
  QuotientIdentity.refl (QuotientCwf.Controls.result wire)

/-- The actual mixed HOL-list/wire projection supplies both endpoints of
the native identity type; its semantic endpoints are the computed result. -/
theorem mixed_identity_meaning (wire : NativeWireData.Wire) :
    (data common).ty .nil
      (.id NativeWireData.dataType (Common.projected wire).code (Common.projected wire).code)
      (resultIdentity wire) :=
  identity_formation_meaning (assembly := common) 0 .nil NativeWireData.dataType
    (Common.projected wire).code (Common.projected wire).code (.sort Tower.zero)
    QuotientCwf.Controls.wireType (QuotientCwf.Controls.result wire) (QuotientCwf.Controls.result wire)
    Common.wireType.judgment (.sort _) (Common.projected wire).judgment (Common.projected wire).judgment
    (QuotientInterpretation.type_meaning _ Common.wireType)
    (SharedJudgmentQuotientInterpretation.Controls.mixed_projection_meaning wire)
    (SharedJudgmentQuotientInterpretation.Controls.mixed_projection_meaning wire)

theorem mixed_reflexivity_meaning (wire : NativeWireData.Wire) :
    (data common).term .nil (.refl (Common.projected wire).code)
      (.id NativeWireData.dataType (Common.projected wire).code (Common.projected wire).code)
      (resultIdentity wire) (resultReflexivity wire) :=
  reflexivity_meaning (assembly := common) 0 .nil NativeWireData.dataType (Common.projected wire).code
    QuotientCwf.Controls.wireType (QuotientCwf.Controls.result wire)
    (Common.projected wire).judgment (QuotientInterpretation.type_meaning _ Common.wireType)
    (SharedJudgmentQuotientInterpretation.Controls.mixed_projection_meaning wire)

theorem mixed_admission_and_meaning (wire : NativeWireData.Wire) :
    Judgment common.rules .nil
        (.id NativeWireData.dataType (Common.projected wire).code (Common.projected wire).code)
        (sortTm Tower.zero) ∧
      Judgment common.rules .nil (.refl (Common.projected wire).code)
        (.id NativeWireData.dataType (Common.projected wire).code (Common.projected wire).code) ∧
      (data common).ty .nil
        (.id NativeWireData.dataType (Common.projected wire).code (Common.projected wire).code)
        (resultIdentity wire) ∧
      (data common).term .nil (.refl (Common.projected wire).code)
        (.id NativeWireData.dataType (Common.projected wire).code (Common.projected wire).code)
        (resultIdentity wire) (resultReflexivity wire) :=
  ⟨(QuotientIdentity.nativeId Common.wireType (Common.projected wire) (Common.projected wire)).judgment,
    (QuotientIdentity.nativeRefl (Common.projected wire)).judgment,
    mixed_identity_meaning wire, mixed_reflexivity_meaning wire⟩

private theorem parStar_identity_constants {n : Nat} {carrier left right : DeclName}
    {target : Tower.Tm n}
    (steps : NativeRelatorConversionParallel.ParStar
      (.id (.const carrier) (.const left) (.const right)) target) :
    target = .id (.const carrier) (.const left) (.const right) := by
  induction steps with
  | refl => rfl
  | tail _ finalStep ih =>
      rw [ih] at finalStep
      cases finalStep with
      | id typeStep leftStep rightStep =>
          cases typeStep
          cases leftStep
          cases rightStep
          rfl

/-- The same common-package identity operation does not identify distinct
encoded endpoints. The separation uses actual opacity and completed joins,
not failure of one chosen conversion certificate. -/
theorem result_identity_naturals_equal_iff (first second : Nat) :
    resultIdentity (.natural first) = resultIdentity (.natural second) ↔ first = second := by
  constructor
  · intro same
    have firstClass := QuotientIdentity.idTy_mk Common.wireType
      (Common.result (.natural first)) (Common.result (.natural first))
    have secondClass := QuotientIdentity.idTy_mk Common.wireType
      (Common.result (.natural second)) (Common.result (.natural second))
    have converted := (QType.mk_eq_iff _ _).mp (firstClass.symm.trans (same.trans secondClass))
    obtain ⟨joined, firstSteps, secondSteps⟩ := NativeRelatorConversionParallel.conversion_join
      ((OpaqueRelatorExtension.conversion_iff HOLNativeRelatorCompatibility.opacity).mp converted)
    simp only [QuotientIdentity.nativeId, Common.wireType, NativeWireData.dataType,
      Common.result, NativeWireData.encode] at firstSteps secondSteps
    have endpoints := (parStar_identity_constants firstSteps).symm.trans
      (parStar_identity_constants secondSteps)
    exact (Lean.Name.num.inj (Presentation.Tm.const.inj
      (Presentation.Tm.id.inj endpoints).2.1)).2
  · rintro rfl
    rfl

theorem mixed_changed_identity_meaning :
    ¬ (data common).ty .nil
      (.id NativeWireData.dataType (Common.projected (.natural 7)).code
        (Common.projected (.natural 7)).code)
      (resultIdentity (.natural 8)) := by
  intro changed
  have same := SharedJudgmentQuotientInterpretation.type_meaning_unique
    (mixed_identity_meaning (.natural 7)) changed
  have impossible := (result_identity_naturals_equal_iff 7 8).mp same
  cases impossible

/-- Both semantic endpoints and the reflexivity value were changed to
eight, while the retained native program still computes seven. -/
theorem mixed_changed_reflexivity_meaning :
    ¬ (data common).term .nil (.refl (Common.projected (.natural 7)).code)
      (.id NativeWireData.dataType (Common.projected (.natural 7)).code
        (Common.projected (.natural 7)).code)
      (resultIdentity (.natural 8)) (resultReflexivity (.natural 8)) := by
  rintro ⟨actualType, typeCode, _, _, typeClass, _⟩
  exact mixed_changed_identity_meaning ⟨actualType, typeCode, typeClass⟩

/-- The negative control is not caused by an unformed proposed target:
the changed identity and its reflexivity proof are both genuinely admitted. -/
theorem changed_result_still_admitted :
    Judgment common.rules .nil
        (.id NativeWireData.dataType (Common.result (.natural 8)).code (Common.result (.natural 8)).code)
        (sortTm Tower.zero) ∧
      Judgment common.rules .nil (.refl (Common.result (.natural 8)).code)
        (.id NativeWireData.dataType (Common.result (.natural 8)).code (Common.result (.natural 8)).code) :=
  ⟨(QuotientIdentity.nativeId Common.wireType (Common.result (.natural 8))
      (Common.result (.natural 8))).judgment,
    (QuotientIdentity.nativeRefl (Common.result (.natural 8))).judgment⟩

end Controls

#print axioms identity_formation_meaning
#print axioms reflexivity_meaning
#print axioms Controls.mixed_admission_and_meaning
#print axioms Controls.result_identity_naturals_equal_iff
#print axioms Controls.mixed_changed_reflexivity_meaning

end Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentQuotientIdentity
