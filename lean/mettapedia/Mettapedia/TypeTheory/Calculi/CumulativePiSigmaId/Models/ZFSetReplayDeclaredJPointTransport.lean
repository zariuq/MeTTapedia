import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Checking.NativeDeclaredJPointFormation
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Models.ZFSetReplayDeclaredJSubstitution

/-!
# Interpreting a checked replacement of J's base point

The dependent telescope is checked by the native point-formation construction.
Its set-code images then assemble under the existing replay interpretation.
If the computed point has the original point's value on specified environments,
the entire interpreted substitution has the original environment's values there.
The value hypothesis is explicit: checker acceptance alone is not a semantic
typing or certificate-coherence theorem.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.ZFSetReplayDeclaredJPointTransport

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open StructuralTypingReplay NativeIndexedFamilies NativeJudgmentReplay
open ZFSetReplayInterpretation
open ZFSetReplayDeclaredJAgreement
open ZFSetTraceIdentityTypeInterpretation
open ZFSetTypeExpressionInterpretation (Environment)
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.Logic.HOL.Embedding
open ZFSetUniverseClosure (CofinalInaccessibles)

universe u

def imageCodes (point : Tower.Tm 4) (pointCode : Code 4)
    (pointConversion : NativeRelatorConversionChecking.Code 4) : Fin 4 → Code 4 :=
  NativeDeclaredJPointFormation.completeImageCodes point pointCode pointConversion

theorem images_check (point : Tower.Tm 4) (pointCode : Code 4)
    (pointConversion : NativeRelatorConversionChecking.Code 4)
    (pointChecked : StructuralTypingReplay.check IntrinsicRelator.rules
      NativeRelatorConversionChecking.check Intrinsic.contextAXPD
      point (.var 3) pointCode = true)
    (pointConverted : NativeRelatorConversionChecking.check pointConversion
      (.var 2) point = true) :
    TelescopeArgumentChecking.checkArguments
      (StructuralTypingReplay.check IntrinsicRelator.rules
        NativeRelatorConversionChecking.check Intrinsic.contextAXPD)
      Intrinsic.contextAXPD (NativeDeclaredJPointConversion.substitutePoint point)
      (imageCodes point pointCode pointConversion) = true :=
  NativeDeclaredJPointFormation.complete_images_check
    point pointCode pointConversion pointChecked pointConverted

private theorem image_checked (point : Tower.Tm 4) (pointCode : Code 4)
    (pointConversion : NativeRelatorConversionChecking.Code 4)
    (pointChecked : StructuralTypingReplay.check IntrinsicRelator.rules
      NativeRelatorConversionChecking.check Intrinsic.contextAXPD
      point (.var 3) pointCode = true)
    (pointConverted : NativeRelatorConversionChecking.check pointConversion
      (.var 2) point = true) (index : Fin 4) :
    StructuralTypingReplay.check IntrinsicRelator.rules
      NativeRelatorConversionChecking.check Intrinsic.contextAXPD
      (NativeDeclaredJPointConversion.substitutePoint point index)
      (subst (NativeDeclaredJPointConversion.substitutePoint point)
        (Intrinsic.contextAXPD.lookup index))
      (imageCodes point pointCode pointConversion index) = true :=
  (TelescopeArgumentChecking.checkArguments_eq_true_iff
    (StructuralTypingReplay.check IntrinsicRelator.rules
      NativeRelatorConversionChecking.check Intrinsic.contextAXPD)
    Intrinsic.contextAXPD (NativeDeclaredJPointConversion.substitutePoint point)
    (imageCodes point pointCode pointConversion)).mp
      (images_check point pointCode pointConversion pointChecked pointConverted) index

noncomputable def imageMeaning (h : CofinalInaccessibles.{u})
    (heads : Tower.Head → ZFSet.{u}) (constants : DeclName → ZFSet.{u})
    (point : Tower.Tm 4) (pointCode : Code 4)
    (pointConversion : NativeRelatorConversionChecking.Code 4)
    (pointChecked : StructuralTypingReplay.check IntrinsicRelator.rules
      NativeRelatorConversionChecking.check Intrinsic.contextAXPD
      point (.var 3) pointCode = true)
    (pointConverted : NativeRelatorConversionChecking.check pointConversion
      (.var 2) point = true) (index : Fin 4) : Meaning.{u} 4 :=
  Classical.choose (accepted_assembles heads (identityConstants h ∅ 0 1 constants)
    IntrinsicRelator.rules NativeRelatorConversionChecking.check
    (imageCodes point pointCode pointConversion index)
    (image_checked point pointCode pointConversion pointChecked pointConverted index))

theorem image_assembles (h : CofinalInaccessibles.{u})
    (heads : Tower.Head → ZFSet.{u}) (constants : DeclName → ZFSet.{u})
    (point : Tower.Tm 4) (pointCode : Code 4)
    (pointConversion : NativeRelatorConversionChecking.Code 4)
    (pointChecked : StructuralTypingReplay.check IntrinsicRelator.rules
      NativeRelatorConversionChecking.check Intrinsic.contextAXPD
      point (.var 3) pointCode = true)
    (pointConverted : NativeRelatorConversionChecking.check pointConversion
      (.var 2) point = true) (index : Fin 4) :
    assemble heads (identityConstants h ∅ 0 1 constants)
      (imageCodes point pointCode pointConversion index)
      (NativeDeclaredJPointConversion.substitutePoint point index)
      (subst (NativeDeclaredJPointConversion.substitutePoint point)
        (Intrinsic.contextAXPD.lookup index)) =
      some (imageMeaning h heads constants point pointCode pointConversion
        pointChecked pointConverted index) :=
  (Classical.choose_spec (accepted_assembles heads
    (identityConstants h ∅ 0 1 constants) IntrinsicRelator.rules
    NativeRelatorConversionChecking.check
    (imageCodes point pointCode pointConversion index)
    (image_checked point pointCode pointConversion pointChecked pointConverted index))).1

theorem unchanged_image_value (h : CofinalInaccessibles.{u})
    (heads : Tower.Head → ZFSet.{u}) (constants : DeclName → ZFSet.{u})
    (point : Tower.Tm 4) (pointCode : Code 4)
    (pointConversion : NativeRelatorConversionChecking.Code 4)
    (pointChecked : StructuralTypingReplay.check IntrinsicRelator.rules
      NativeRelatorConversionChecking.check Intrinsic.contextAXPD
      point (.var 3) pointCode = true)
    (pointConverted : NativeRelatorConversionChecking.check pointConversion
      (.var 2) point = true)
    (index : Fin 4) (different : index ≠ 2) (env : Environment.{u} 4) :
    (imageMeaning h heads constants point pointCode pointConversion
      pointChecked pointConverted index).value env = env index := by
  have assembled := image_assembles h heads constants point pointCode
    pointConversion pointChecked pointConverted index
  simp only [NativeDeclaredJPointConversion.substitutePoint, if_neg different] at assembled
  exact agrees_with_type_expressions heads (identityConstants h ∅ 0 1 constants)
    (imageCodes point pointCode pointConversion index) (.var index)
    (subst (NativeDeclaredJPointConversion.substitutePoint point)
      (Intrinsic.contextAXPD.lookup index))
    (imageMeaning h heads constants point pointCode pointConversion
      pointChecked pointConverted index) rfl assembled env

theorem image_environment_eq_of_point_value (h : CofinalInaccessibles.{u})
    (heads : Tower.Head → ZFSet.{u}) (constants : DeclName → ZFSet.{u})
    (point : Tower.Tm 4) (pointCode : Code 4)
    (pointConversion : NativeRelatorConversionChecking.Code 4)
    (pointChecked : StructuralTypingReplay.check IntrinsicRelator.rules
      NativeRelatorConversionChecking.check Intrinsic.contextAXPD
      point (.var 3) pointCode = true)
    (pointConverted : NativeRelatorConversionChecking.check pointConversion
      (.var 2) point = true)
    (env : Environment.{u} 4)
    (pointValue : (imageMeaning h heads constants point pointCode pointConversion
      pointChecked pointConverted 2).value env = env 2) :
    imageEnvironment (imageMeaning h heads constants point pointCode
      pointConversion pointChecked pointConverted) env = env := by
  funext index
  change (imageMeaning h heads constants point pointCode pointConversion
    pointChecked pointConverted index).value env = env index
  by_cases changed : index = 2
  · subst index
    exact pointValue
  · exact unchanged_image_value h heads constants point pointCode
      pointConversion pointChecked pointConverted index changed env

/-- For the checked replacement telescope, preserving the entire interpreted
environment is equivalent to preserving its one changed coordinate. -/
theorem image_environment_eq_iff_point_value (h : CofinalInaccessibles.{u})
    (heads : Tower.Head → ZFSet.{u}) (constants : DeclName → ZFSet.{u})
    (point : Tower.Tm 4) (pointCode : Code 4)
    (pointConversion : NativeRelatorConversionChecking.Code 4)
    (pointChecked : StructuralTypingReplay.check IntrinsicRelator.rules
      NativeRelatorConversionChecking.check Intrinsic.contextAXPD
      point (.var 3) pointCode = true)
    (pointConverted : NativeRelatorConversionChecking.check pointConversion
      (.var 2) point = true)
    (env : Environment.{u} 4) :
    imageEnvironment (imageMeaning h heads constants point pointCode
      pointConversion pointChecked pointConverted) env = env ↔
    (imageMeaning h heads constants point pointCode pointConversion
      pointChecked pointConverted 2).value env = env 2 := by
  constructor
  · intro same
    have atPoint := congrFun same (2 : Fin 4)
    change (imageMeaning h heads constants point pointCode pointConversion
      pointChecked pointConverted 2).value env = env 2 at atPoint
    exact atPoint
  · exact image_environment_eq_of_point_value h heads constants point pointCode
      pointConversion pointChecked pointConverted env

theorem point_value_in_carrier_of_admission (h : CofinalInaccessibles.{u})
    (heads : Tower.Head → ZFSet.{u}) (constants : DeclName → ZFSet.{u})
    (point : Tower.Tm 4) (pointCode : Code 4)
    (pointConversion : NativeRelatorConversionChecking.Code 4)
    (pointChecked : StructuralTypingReplay.check IntrinsicRelator.rules
      NativeRelatorConversionChecking.check Intrinsic.contextAXPD
      point (.var 3) pointCode = true)
    (pointConverted : NativeRelatorConversionChecking.check pointConversion
      (.var 2) point = true)
    (env : Environment.{u} 4)
    (admitted : AdmittedJArguments h ∅ 0 1 heads constants
      (.var 3) (.var 2) (.var 1) (.var 0)
      (by decide) (by decide) (by decide) (by decide) env)
    (pointValue : (imageMeaning h heads constants point pointCode pointConversion
      pointChecked pointConverted 2).value env = env 2) :
    (imageMeaning h heads constants point pointCode pointConversion
      pointChecked pointConverted 2).value env ∈ env 3 := by
  obtain ⟨carrier, endpoint, _, _, atCarrier, atEndpoint, _, _⟩ := admitted
  change env 3 = carrier.1 at atCarrier
  change env 2 = endpoint.1 at atEndpoint
  rw [pointValue, atEndpoint, atCarrier]
  exact endpoint.2

/-- A checked computed point may replace J's original point without changing
the admitted result on environments where the point's interpreted value is
unchanged. This connects the dependent checker, actual certificate assembly,
and the set-code J computation; it does not posit a global value law. -/
theorem checked_j_iota_of_point_value (h : CofinalInaccessibles.{u})
    (heads : Tower.Head → ZFSet.{u}) (constants : DeclName → ZFSet.{u})
    (point : Tower.Tm 4) (pointCode : Code 4)
    (pointConversion : NativeRelatorConversionChecking.Code 4)
    (pointChecked : StructuralTypingReplay.check IntrinsicRelator.rules
      NativeRelatorConversionChecking.check Intrinsic.contextAXPD
      point (.var 3) pointCode = true)
    (pointConverted : NativeRelatorConversionChecking.check pointConversion
      (.var 2) point = true)
    (valid : Environment.{u} 4 → Prop)
    (admitted : ∀ env, valid env → AdmittedJArguments h ∅ 0 1 heads constants
      (.var 3) (.var 2) (.var 1) (.var 0)
      (by decide) (by decide) (by decide) (by decide) env)
    (pointValuesAgree : ∀ env, valid env →
      (imageMeaning h heads constants point pointCode pointConversion
        pointChecked pointConverted 2).value env = env 2) :
    NativeJudgmentReplay.check Intrinsic.contextAXPD
      (subst (NativeDeclaredJPointConversion.substitutePoint point)
        Intrinsic.identityIotaLeft)
      (subst (NativeDeclaredJPointConversion.substitutePoint point)
        Intrinsic.identityIotaResultType)
      ZFSetReplayDeclaredJAgreement.contextCode
      (NativeJudgmentReplay.substitute
        (NativeDeclaredJPointConversion.substitutePoint point)
        (imageCodes point pointCode pointConversion)
        Intrinsic.identityIotaLeft Intrinsic.identityIotaResultType
        ZFSetReplayDeclaredJAgreement.sourceCode) = true ∧
    NativeJudgmentReplay.check Intrinsic.contextAXPD
      (subst (NativeDeclaredJPointConversion.substitutePoint point)
        Intrinsic.identityIotaRight)
      (subst (NativeDeclaredJPointConversion.substitutePoint point)
        Intrinsic.identityIotaResultType)
      ZFSetReplayDeclaredJAgreement.contextCode
      (NativeJudgmentReplay.substitute
        (NativeDeclaredJPointConversion.substitutePoint point)
        (imageCodes point pointCode pointConversion)
        Intrinsic.identityIotaRight Intrinsic.identityIotaResultType
        ZFSetReplayDeclaredJAgreement.returnedReceipt.2) = true ∧
    ∃ sourceAfter resultAfter,
      assemble heads (identityConstants h ∅ 0 1 constants)
        (NativeJudgmentReplay.substitute
          (NativeDeclaredJPointConversion.substitutePoint point)
          (imageCodes point pointCode pointConversion)
          Intrinsic.identityIotaLeft Intrinsic.identityIotaResultType
          ZFSetReplayDeclaredJAgreement.sourceCode)
        (subst (NativeDeclaredJPointConversion.substitutePoint point)
          Intrinsic.identityIotaLeft)
        (subst (NativeDeclaredJPointConversion.substitutePoint point)
          Intrinsic.identityIotaResultType) = some sourceAfter ∧
      assemble heads (identityConstants h ∅ 0 1 constants)
        (NativeJudgmentReplay.substitute
          (NativeDeclaredJPointConversion.substitutePoint point)
          (imageCodes point pointCode pointConversion)
          Intrinsic.identityIotaRight Intrinsic.identityIotaResultType
          ZFSetReplayDeclaredJAgreement.returnedReceipt.2)
        (subst (NativeDeclaredJPointConversion.substitutePoint point)
          Intrinsic.identityIotaRight)
        (subst (NativeDeclaredJPointConversion.substitutePoint point)
          Intrinsic.identityIotaResultType) = some resultAfter ∧
      ∀ env, valid env → sourceAfter.value env = resultAfter.value env := by
  have admissionOfImages : ∀ env, valid env →
      AdmittedJArguments h ∅ 0 1 heads constants
        (.var 3) (.var 2) (.var 1) (.var 0)
        (by decide) (by decide) (by decide) (by decide)
        (imageEnvironment (imageMeaning h heads constants point pointCode
          pointConversion pointChecked pointConverted) env) := by
    intro env hValid
    rw [image_environment_eq_of_point_value h heads constants point pointCode
      pointConversion pointChecked pointConverted env (pointValuesAgree env hValid)]
    exact admitted env hValid
  exact ZFSetReplayDeclaredJSubstitution.checked_j_iota_substitute
    h ∅ 0 1 heads constants
    Intrinsic.contextAXPD ZFSetReplayDeclaredJAgreement.contextCode
    Intrinsic.contextAXPD ZFSetReplayDeclaredJAgreement.contextCode
    (.var 3) (.var 2) (.var 1) (.var 0) Intrinsic.identityIotaResultType
    (by decide) (by decide) (by decide) (by decide)
    ZFSetReplayDeclaredJAgreement.sourceCode
    ZFSetReplayDeclaredJAgreement.returnedReceipt.2
    ZFSetReplayDeclaredJAgreement.proposal_accepted
    ZFSetReplayDeclaredJAgreement.returned_accepted
    ZFSetReplayDeclaredJAgreement.context_formed
    (NativeDeclaredJPointConversion.substitutePoint point)
    (imageCodes point pointCode pointConversion)
    (images_check point pointCode pointConversion pointChecked pointConverted)
    (imageMeaning h heads constants point pointCode pointConversion
      pointChecked pointConverted)
    (image_assembles h heads constants point pointCode pointConversion
      pointChecked pointConverted)
    valid admissionOfImages

#print axioms image_environment_eq_of_point_value
#print axioms image_environment_eq_iff_point_value
#print axioms point_value_in_carrier_of_admission
#print axioms checked_j_iota_of_point_value

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.ZFSetReplayDeclaredJPointTransport
