import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Models.ZFSetReplayDeclaredJSubstitution
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Checking.NativeDeclaredJPointConversion
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Checking.NativeDeclaredJPointFormation
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Models.ZFSetReplayDeclaredJPointTransport

/-!
# Checked computed-point substitution for declared identity elimination

A beta-computed base point changes the expected types of both the dependent
motive and its method. Their original variable certificates are insufficient.
The reusable point-formation construction transports the motive and method
formations through the earlier context prefixes, then gives their variables
explicit checked conversion certificates. One point-conversion receipt
generates both dependent casts. Its completed telescope is used directly by
the declared J proof and its set-code interpretation.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.ZFSetReplayDeclaredJPointSubstitution

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open StructuralTypingReplay
open NativeIndexedFamilies
open NativeJudgmentReplay
open ZFSetReplayDeclaredJAgreement
open ZFSetTraceIdentityTypeInterpretation
open ZFSetReplayInterpretation
open ZFSetTypeExpressionInterpretation (Environment)
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.Logic.HOL.Embedding
open ZFSetUniverseClosure (CofinalInaccessibles)

universe u

private def pointType : Tower.Tm 4 := .var 3
private def identityFunctionType : Tower.Tm 4 := .pi pointType (rename wk pointType)
def computedPoint : Tower.Tm 4 := .app (.lam (.var 0)) (.var 2)

private def functionProposal : Tower.Tm 4 × Code 4 :=
  (CertificateProposal.term 64 Intrinsic.contextAXPD identityFunctionType).get
    (by decide +kernel)

private def functionLevel? : Option Tower.Head :=
  match functionProposal.1 with
  | .head level => some level
  | _ => none

private def functionLevel : Tower.Head := functionLevel?.get (by decide +kernel)

private def computedPointCode : Code 4 :=
  .appElim pointType (rename wk pointType)
    (.lamIntro functionLevel functionProposal.2 .var) .var

theorem computed_point_checks :
    StructuralTypingReplay.check IntrinsicRelator.rules NativeRelatorConversionChecking.check
      Intrinsic.contextAXPD computedPoint pointType computedPointCode = true := by
  decide +kernel

def pointSubstitution : Sub Tower.Head 4 4 :=
  fun index => if index = 2 then computedPoint else .var index

def naiveImageCodes : Fin 4 → Code 4 :=
  fun index => if index = 2 then computedPointCode else .var

/-- Keeping the later motive and method certificates as bare variables is
rejected: their expected types changed with the computed point. -/
theorem naive_images_rejected :
    TelescopeArgumentChecking.checkArguments
      (StructuralTypingReplay.check IntrinsicRelator.rules
        NativeRelatorConversionChecking.check Intrinsic.contextAXPD)
      Intrinsic.contextAXPD pointSubstitution naiveImageCodes = false := by
  decide +kernel

private def pointConversion : NativeRelatorConversionChecking.Code 4 :=
  .symm (.single (.betaPi (.var 0) (.var 2)))

private theorem point_conversion_checked :
    NativeRelatorConversionChecking.check pointConversion (.var 2) computedPoint = true := by
  decide +kernel

def repairedImageCodes : Fin 4 → Code 4 :=
  NativeDeclaredJPointFormation.completeImageCodes
    computedPoint computedPointCode pointConversion

theorem repaired_images_check :
    TelescopeArgumentChecking.checkArguments
      (StructuralTypingReplay.check IntrinsicRelator.rules
        NativeRelatorConversionChecking.check Intrinsic.contextAXPD)
      Intrinsic.contextAXPD pointSubstitution repairedImageCodes = true := by
  exact NativeDeclaredJPointFormation.complete_images_check
    computedPoint computedPointCode pointConversion
    computed_point_checks point_conversion_checked

/-- The existing declared J redex and its returned method both remain accepted
after the base point is replaced by a checked beta-computed application. The
two later variable images retain the exact motive/method conversion trees. -/
theorem computed_point_j_accepted :
    NativeJudgmentReplay.check Intrinsic.contextAXPD
      (subst pointSubstitution Intrinsic.identityIotaLeft)
      (subst pointSubstitution Intrinsic.identityIotaResultType)
      ZFSetReplayDeclaredJAgreement.contextCode
      (NativeJudgmentReplay.substitute pointSubstitution repairedImageCodes
        Intrinsic.identityIotaLeft Intrinsic.identityIotaResultType
        ZFSetReplayDeclaredJAgreement.sourceCode) = true ∧
    NativeJudgmentReplay.check Intrinsic.contextAXPD
      (subst pointSubstitution Intrinsic.identityIotaRight)
      (subst pointSubstitution Intrinsic.identityIotaResultType)
      ZFSetReplayDeclaredJAgreement.contextCode
      (NativeJudgmentReplay.substitute pointSubstitution repairedImageCodes
        Intrinsic.identityIotaRight Intrinsic.identityIotaResultType
        ZFSetReplayDeclaredJAgreement.returnedReceipt.2) = true := by
  exact ⟨NativeJudgmentReplay.check_substitute
      ZFSetReplayDeclaredJAgreement.proposal_accepted
      ZFSetReplayDeclaredJAgreement.contextCode
      ZFSetReplayDeclaredJAgreement.context_formed
      pointSubstitution repairedImageCodes repaired_images_check,
    NativeJudgmentReplay.check_substitute
      ZFSetReplayDeclaredJAgreement.returned_accepted
      ZFSetReplayDeclaredJAgreement.contextCode
      ZFSetReplayDeclaredJAgreement.context_formed
      pointSubstitution repairedImageCodes repaired_images_check⟩

/-- The point image is not a renamed variable, even though its beta value
agrees with the old point on an admitted domain. -/
theorem computed_point_not_variable : computedPoint ≠ (.var 2 : Tower.Tm 4) := by
  decide

noncomputable abbrev imageMeaning (h : CofinalInaccessibles.{u})
    (heads : Tower.Head → ZFSet.{u}) (constants : DeclName → ZFSet.{u})
    (index : Fin 4) : Meaning.{u} 4 :=
  ZFSetReplayDeclaredJPointTransport.imageMeaning h heads constants
    computedPoint computedPointCode pointConversion
    computed_point_checks point_conversion_checked index

theorem image_assembles (h : CofinalInaccessibles.{u})
    (heads : Tower.Head → ZFSet.{u}) (constants : DeclName → ZFSet.{u})
    (index : Fin 4) :
    assemble heads (identityConstants h ∅ 0 1 constants)
      (repairedImageCodes index) (pointSubstitution index)
      (subst pointSubstitution (Intrinsic.contextAXPD.lookup index)) =
      some (imageMeaning h heads constants index) :=
  ZFSetReplayDeclaredJPointTransport.image_assembles h heads constants
    computedPoint computedPointCode pointConversion
    computed_point_checks point_conversion_checked index

private theorem function_formation_checked :
    StructuralTypingReplay.check IntrinsicRelator.rules
      NativeRelatorConversionChecking.check Intrinsic.contextAXPD
      identityFunctionType (.head functionLevel) functionProposal.2 = true := by
  decide +kernel

private theorem point_supported :
    ZFSetTypeExpressionInterpretation.supported pointType = true := by
  decide

/-- The computed point beta-contracts only when its argument inhabits the
retained product domain; this does not assert a value law on invalid inputs. -/
theorem computed_image_value_of_domain (h : CofinalInaccessibles.{u})
    (heads : Tower.Head → ZFSet.{u}) (constants : DeclName → ZFSet.{u})
    (formed : Meaning.{u} 4) (domain : Value.{u} 4)
    (atFormation : assemble heads (identityConstants h ∅ 0 1 constants)
      functionProposal.2 identityFunctionType (.head functionLevel) = some formed)
    (atDomain : formed.productDomain? = some domain)
    (env : Environment.{u} 4) (inside : env 2 ∈ domain env) :
    (imageMeaning h heads constants 2).value env = env 2 := by
  have atResult := image_assembles h heads constants 2
  have atBody : assemble heads (identityConstants h ∅ 0 1 constants)
      (.var : Code 5) (.var 0) (rename wk pointType) =
      some (.plain (fun environment => environment 0) : Meaning.{u} 5) := rfl
  have atArgument : assemble heads (identityConstants h ∅ 0 1 constants)
      (.var : Code 4) (.var 2) pointType =
      some (.plain (fun environment => environment 2) : Meaning.{u} 4) := rfl
  have atComputed : assemble heads (identityConstants h ∅ 0 1 constants)
      computedPointCode computedPoint pointType =
      some (imageMeaning h heads constants 2) := by
    have same : subst pointSubstitution
        (Intrinsic.contextAXPD.lookup (2 : Fin 4)) = pointType := by
      decide +kernel
    rw [same] at atResult
    simpa [repairedImageCodes, NativeDeclaredJPointFormation.completeImageCodes,
      NativeDeclaredJPointConversion.imageCodes,
      pointSubstitution] using atResult
  have value := application_lambda_value heads (identityConstants h ∅ 0 1 constants)
    functionLevel pointType (rename wk pointType) (.var 0) (.var 2)
    functionProposal.2 (.var : Code 4) (.var : Code 5)
    formed (.plain (fun environment => environment 2))
    (imageMeaning h heads constants 2) (.plain (fun environment => environment 0))
    domain atFormation atDomain atBody atArgument atComputed env inside
  simpa [Meaning.plain, ZFSetTypeExpressionInterpretation.extend] using value

theorem point_domain_value (h : CofinalInaccessibles.{u})
    (heads : Tower.Head → ZFSet.{u}) (constants : DeclName → ZFSet.{u})
    (formed : Meaning.{u} 4) (domain : Value.{u} 4)
    (atFormation : assemble heads (identityConstants h ∅ 0 1 constants)
      functionProposal.2 identityFunctionType (.head functionLevel) = some formed)
    (atDomain : formed.productDomain? = some domain)
    (env : Environment.{u} 4) :
    domain env = ZFSetTypeExpressionInterpretation.interpret heads
      (identityConstants h ∅ 0 1 constants) pointType point_supported env := by
  obtain ⟨uLevel, vLevel, domainCode, bodyCode, extracted, _, _, _, _⟩ :=
    functionProposal.2.piFormation_checked IntrinsicRelator.rules
      NativeRelatorConversionChecking.check function_formation_checked
  obtain ⟨domainMeaning, bodyMeaning, atDomainMeaning, _, _, domainEquals⟩ :=
    assemble_piFormation heads (identityConstants h ∅ 0 1 constants)
      functionProposal.2 extracted atFormation
  rw [atDomain] at domainEquals
  cases Option.some.inj domainEquals
  exact agrees_with_type_expressions heads (identityConstants h ∅ 0 1 constants)
    domainCode pointType (.head uLevel) domainMeaning point_supported atDomainMeaning env

theorem universe_point_in_domain (h : CofinalInaccessibles.{u})
    (heads : Tower.Head → ZFSet.{u}) (constants : DeclName → ZFSet.{u}) :
    (ZFSetTraceIdentityTypeInterpretation.Controls.universeEnvironment h) 2 ∈
      ZFSetTypeExpressionInterpretation.interpret heads
        (identityConstants h ∅ 0 1 constants) pointType point_supported
        (ZFSetTraceIdentityTypeInterpretation.Controls.universeEnvironment h) := by
  change (ZFSetTraceIdentityDeclaration.Controls.zeroPoint h).1 ∈
    (Mettapedia.TypeTheory.UniverseLevel.ZFSetInterpretation.Controls.twoCode h).1
  exact (ZFSetTraceIdentityDeclaration.Controls.zeroPoint h).2

/-- All four interpreted substitution images are the original components at
the concrete typed universe environment; the computed point uses the retained
function-domain membership, while the motive and method use their casts. -/
theorem universe_image_environment_eq (h : CofinalInaccessibles.{u})
    (heads : Tower.Head → ZFSet.{u}) (constants : DeclName → ZFSet.{u}) :
    imageEnvironment (imageMeaning h heads constants)
      (ZFSetTraceIdentityTypeInterpretation.Controls.universeEnvironment h) =
      ZFSetTraceIdentityTypeInterpretation.Controls.universeEnvironment h := by
  obtain ⟨formed, atFormation, domainExists⟩ := accepted_assembles heads
    (identityConstants h ∅ 0 1 constants) IntrinsicRelator.rules
    NativeRelatorConversionChecking.check functionProposal.2 function_formation_checked
  obtain ⟨domain, atDomain⟩ := domainExists pointType (rename wk pointType) rfl
  let env := ZFSetTraceIdentityTypeInterpretation.Controls.universeEnvironment h
  have inside : env 2 ∈ domain env := by
    rw [point_domain_value h heads constants formed domain atFormation atDomain env]
    exact universe_point_in_domain h heads constants
  have computed : (imageMeaning h heads constants 2).value env = env 2 :=
    computed_image_value_of_domain h heads constants formed domain
      atFormation atDomain env inside
  exact ZFSetReplayDeclaredJPointTransport.image_environment_eq_of_point_value
    h heads constants computedPoint computedPointCode pointConversion
    computed_point_checks point_conversion_checked env computed

def admittedImageEnvironment (h : CofinalInaccessibles.{u})
    (heads : Tower.Head → ZFSet.{u}) (constants : DeclName → ZFSet.{u})
    (env : Environment.{u} 4) : Prop :=
  AdmittedJArguments h ∅ 0 1 heads constants
    (.var 3) (.var 2) (.var 1) (.var 0)
    (by decide) (by decide) (by decide) (by decide)
    (imageEnvironment (imageMeaning h heads constants) env)

/-- The semantic-square admission predicate has a concrete inhabitant; it is
not an empty-domain comparison. -/
theorem universe_environment_admitted (h : CofinalInaccessibles.{u})
    (heads : Tower.Head → ZFSet.{u}) (constants : DeclName → ZFSet.{u}) :
    admittedImageEnvironment h heads constants
      (ZFSetTraceIdentityTypeInterpretation.Controls.universeEnvironment h) := by
  have original : AdmittedJArguments h ∅ 0 1 heads constants
      (.var 3) (.var 2) (.var 1) (.var 0)
      (by decide) (by decide) (by decide) (by decide)
      (ZFSetTraceIdentityTypeInterpretation.Controls.universeEnvironment h) := by
    exact ⟨Mettapedia.TypeTheory.UniverseLevel.ZFSetInterpretation.Controls.twoCode h,
      ZFSetTraceIdentityDeclaration.Controls.zeroPoint h,
      ZFSetTraceIdentityDeclaration.Controls.universeMotive h,
      ZFSetTraceIdentityDeclaration.Controls.universeMethod h,
      rfl, rfl, rfl, rfl⟩
  change AdmittedJArguments h ∅ 0 1 heads constants
    (.var 3) (.var 2) (.var 1) (.var 0)
    (by decide) (by decide) (by decide) (by decide)
    (imageEnvironment (imageMeaning h heads constants)
      (ZFSetTraceIdentityTypeInterpretation.Controls.universeEnvironment h))
  rw [universe_image_environment_eq h heads constants]
  exact original

/-- Checked base-point computation and both dependent casts feed the existing
J-iota semantic square. Agreement is on the explicitly admitted set-code
environments, not on arbitrary raw environments. -/
theorem checked_computed_point_j_square (h : CofinalInaccessibles.{u})
    (heads : Tower.Head → ZFSet.{u}) (constants : DeclName → ZFSet.{u}) :
    ∃ sourceAfter resultAfter,
      assemble heads (identityConstants h ∅ 0 1 constants)
        (NativeJudgmentReplay.substitute pointSubstitution repairedImageCodes
          Intrinsic.identityIotaLeft Intrinsic.identityIotaResultType
          ZFSetReplayDeclaredJAgreement.sourceCode)
        (subst pointSubstitution Intrinsic.identityIotaLeft)
        (subst pointSubstitution Intrinsic.identityIotaResultType) = some sourceAfter ∧
      assemble heads (identityConstants h ∅ 0 1 constants)
        (NativeJudgmentReplay.substitute pointSubstitution repairedImageCodes
          Intrinsic.identityIotaRight Intrinsic.identityIotaResultType
          ZFSetReplayDeclaredJAgreement.returnedReceipt.2)
        (subst pointSubstitution Intrinsic.identityIotaRight)
        (subst pointSubstitution Intrinsic.identityIotaResultType) = some resultAfter ∧
      ∀ env, admittedImageEnvironment h heads constants env →
        sourceAfter.value env = resultAfter.value env := by
  obtain ⟨_, _, sourceAfter, resultAfter, sourceAssembled, resultAssembled, agreement⟩ :=
    ZFSetReplayDeclaredJSubstitution.checked_j_iota_substitute
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
      pointSubstitution repairedImageCodes repaired_images_check
      (imageMeaning h heads constants) (image_assembles h heads constants)
      (admittedImageEnvironment h heads constants)
      (by intro _ admitted; exact admitted)
  exact ⟨sourceAfter, resultAfter, sourceAssembled, resultAssembled, agreement⟩

theorem computed_point_j_agrees_at_universe (h : CofinalInaccessibles.{u})
    (heads : Tower.Head → ZFSet.{u}) (constants : DeclName → ZFSet.{u}) :
    ∃ sourceAfter resultAfter,
      assemble heads (identityConstants h ∅ 0 1 constants)
        (NativeJudgmentReplay.substitute pointSubstitution repairedImageCodes
          Intrinsic.identityIotaLeft Intrinsic.identityIotaResultType
          ZFSetReplayDeclaredJAgreement.sourceCode)
        (subst pointSubstitution Intrinsic.identityIotaLeft)
        (subst pointSubstitution Intrinsic.identityIotaResultType) = some sourceAfter ∧
      assemble heads (identityConstants h ∅ 0 1 constants)
        (NativeJudgmentReplay.substitute pointSubstitution repairedImageCodes
          Intrinsic.identityIotaRight Intrinsic.identityIotaResultType
          ZFSetReplayDeclaredJAgreement.returnedReceipt.2)
        (subst pointSubstitution Intrinsic.identityIotaRight)
        (subst pointSubstitution Intrinsic.identityIotaResultType) = some resultAfter ∧
      sourceAfter.value (ZFSetTraceIdentityTypeInterpretation.Controls.universeEnvironment h) =
        resultAfter.value (ZFSetTraceIdentityTypeInterpretation.Controls.universeEnvironment h) := by
  let env := ZFSetTraceIdentityTypeInterpretation.Controls.universeEnvironment h
  have original : AdmittedJArguments h ∅ 0 1 heads constants
      (.var 3) (.var 2) (.var 1) (.var 0)
      (by decide) (by decide) (by decide) (by decide) env := by
    have admitted := universe_environment_admitted h heads constants
    change AdmittedJArguments h ∅ 0 1 heads constants
      (.var 3) (.var 2) (.var 1) (.var 0)
      (by decide) (by decide) (by decide) (by decide)
      (imageEnvironment (imageMeaning h heads constants) env) at admitted
    rw [universe_image_environment_eq h heads constants] at admitted
    exact admitted
  have pointValue :
      (ZFSetReplayDeclaredJPointTransport.imageMeaning h heads constants
        computedPoint computedPointCode pointConversion
        computed_point_checks point_conversion_checked 2).value env = env 2 := by
    have atPoint := congrFun (universe_image_environment_eq h heads constants)
      (2 : Fin 4)
    change (imageMeaning h heads constants 2).value env = env 2 at atPoint
    exact atPoint
  obtain ⟨_, _, sourceAfter, resultAfter, atSource, atResult, agreement⟩ :=
    ZFSetReplayDeclaredJPointTransport.checked_j_iota_of_point_value
      h heads constants computedPoint computedPointCode pointConversion
      computed_point_checks point_conversion_checked
      (fun current => current = env)
      (by intro current equal; subst current; exact original)
      (by intro current equal; subst current; exact pointValue)
  exact ⟨sourceAfter, resultAfter, atSource, atResult, agreement env rfl⟩

#print axioms computed_point_checks
#print axioms naive_images_rejected
#print axioms repaired_images_check
#print axioms computed_point_j_accepted
#print axioms checked_computed_point_j_square
#print axioms universe_environment_admitted
#print axioms computed_point_j_agrees_at_universe

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.ZFSetReplayDeclaredJPointSubstitution
