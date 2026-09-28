import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Checking.NativeDeclaredJPointConversion
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Checking.NativeStructuralCertificateProposal
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Checking.NativeJudgmentReplayTransport

/-!
# Forming dependent J arguments from one checked replacement point

The fixed identity-elimination telescope already has checked motive and
method formations. Given a replacement for its point, transport the motive
formation through the `A, X` prefix. Its checked cast then participates in
the `A, X, P` prefix that transports the method formation. The completed
telescope uses the existing pointwise conversion construction.

The source formation proposals are fixed finite trees independently accepted
by the native checker. The replacement point's certificate and conversion
receipt remain explicit inputs; no certificate is recovered from erased syntax.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeDeclaredJPointFormation

open Presentation StructuralTypingReplay NativeIndexedFamilies NativeJudgmentReplay
open NativeDeclaredJPointConversion

private def axCode : ContextCode 2 :=
  (CertificateProposal.context Intrinsic.contextAX).get (by decide +kernel)

private def axpCode : ContextCode 3 :=
  (CertificateProposal.context Intrinsic.contextAXP).get (by decide +kernel)

private def targetCode : ContextCode 4 :=
  (CertificateProposal.context Intrinsic.contextAXPD).get (by decide +kernel)

private theorem target_formed :
    StructuralTypingReplay.checkContext IntrinsicRelator.rules
      NativeRelatorConversionChecking.check Intrinsic.contextAXPD targetCode = true := by
  decide +kernel

def axSubstitution (point : Tower.Tm 4) : Sub Tower.Head 2 4 :=
  fun index => if index = 0 then point else .var 3

def axImageCodes (pointCode : Code 4) : Fin 2 → Code 4 :=
  fun index => if index = 0 then pointCode else .var

theorem ax_images_check (point : Tower.Tm 4) (pointCode : Code 4)
    (pointChecked : StructuralTypingReplay.check IntrinsicRelator.rules
      NativeRelatorConversionChecking.check Intrinsic.contextAXPD
      point (.var 3) pointCode = true) :
    TelescopeArgumentChecking.checkArguments
      (StructuralTypingReplay.check IntrinsicRelator.rules
        NativeRelatorConversionChecking.check Intrinsic.contextAXPD)
      Intrinsic.contextAX (axSubstitution point) (axImageCodes pointCode) = true := by
  apply (TelescopeArgumentChecking.checkArguments_eq_true_iff _ _ _ _).mpr
  intro index
  fin_cases index
  · change StructuralTypingReplay.check IntrinsicRelator.rules
        NativeRelatorConversionChecking.check Intrinsic.contextAXPD
        point (.var 3) pointCode = true
    exact pointChecked
  · change StructuralTypingReplay.check IntrinsicRelator.rules
        NativeRelatorConversionChecking.check Intrinsic.contextAXPD
        (.var 3) (sortTm Intrinsic.elementLevel) (.var : Code 4) = true
    decide +kernel

private def motiveProposal : Tower.Tm 2 × Code 2 :=
  (CertificateProposal.term 64 Intrinsic.contextAX Intrinsic.identityMotiveType).get
    (by decide +kernel)

private def motiveLevel? : Option Tower.Head :=
  match motiveProposal.1 with
  | .head level => some level
  | _ => none

def motiveLevel : Tower.Head := motiveLevel?.get (by decide +kernel)

private theorem motive_source_checked :
    NativeJudgmentReplay.check Intrinsic.contextAX Intrinsic.identityMotiveType
      (.head motiveLevel) axCode motiveProposal.2 = true := by
  decide +kernel

def motiveFormation (point : Tower.Tm 4) (pointCode : Code 4) : Code 4 :=
  NativeJudgmentReplay.substitute (axSubstitution point) (axImageCodes pointCode)
    Intrinsic.identityMotiveType (.head motiveLevel) motiveProposal.2

theorem motive_formed (point : Tower.Tm 4) (pointCode : Code 4)
    (pointChecked : StructuralTypingReplay.check IntrinsicRelator.rules
      NativeRelatorConversionChecking.check Intrinsic.contextAXPD
      point (.var 3) pointCode = true) :
    StructuralTypingReplay.check IntrinsicRelator.rules
      NativeRelatorConversionChecking.check Intrinsic.contextAXPD
      (expectedMotive point) (.head motiveLevel) (motiveFormation point pointCode) = true := by
  have accepted := NativeJudgmentReplay.check_substitute motive_source_checked
    targetCode target_formed (axSubstitution point) (axImageCodes pointCode)
    (ax_images_check point pointCode pointChecked)
  have same : subst (axSubstitution point) Intrinsic.identityMotiveType =
      expectedMotive point := by
    rfl
  rw [same] at accepted
  change StructuralTypingReplay.checkJudgment IntrinsicRelator.rules
    NativeRelatorConversionChecking.check Intrinsic.contextAXPD
    (expectedMotive point) (.head motiveLevel) targetCode
    (motiveFormation point pointCode) = true at accepted
  simp only [StructuralTypingReplay.checkJudgment, Bool.and_eq_true] at accepted
  exact accepted.2

def motiveCast (point : Tower.Tm 4) (pointCode : Code 4)
    (pointConversion : NativeRelatorConversionChecking.Code 4) : Code 4 :=
  .convert (Intrinsic.contextAXPD.lookup 1) motiveLevel .var
    (motiveFormation point pointCode)
    (lookupConversion point pointConversion 1)

theorem motive_cast_checked (point : Tower.Tm 4) (pointCode : Code 4)
    (pointConversion : NativeRelatorConversionChecking.Code 4)
    (pointChecked : StructuralTypingReplay.check IntrinsicRelator.rules
      NativeRelatorConversionChecking.check Intrinsic.contextAXPD
      point (.var 3) pointCode = true)
    (pointConverted : NativeRelatorConversionChecking.check pointConversion
      (.var 2) point = true) :
    StructuralTypingReplay.check IntrinsicRelator.rules
      NativeRelatorConversionChecking.check Intrinsic.contextAXPD
      (.var 1) (expectedMotive point)
      (motiveCast point pointCode pointConversion) = true := by
  have source : StructuralTypingReplay.check IntrinsicRelator.rules
      NativeRelatorConversionChecking.check Intrinsic.contextAXPD
      (.var 1) (Intrinsic.contextAXPD.lookup 1) (.var : Code 4) = true := by
    decide +kernel
  have formed := motive_formed point pointCode pointChecked
  have converted := lookup_conversion_checked point pointConversion pointConverted 1
  have isUniverse : IntrinsicRelator.rules.isUniverse motiveLevel := by decide +kernel
  simpa only [motiveCast, StructuralTypingReplay.check, decide_eq_true isUniverse,
    source, formed, converted, Bool.true_and, Bool.and_true]

def axpSubstitution (point : Tower.Tm 4) : Sub Tower.Head 3 4 :=
  fun index => if index = 0 then .var 1 else if index = 1 then point else .var 3

def axpImageCodes (point : Tower.Tm 4) (pointCode : Code 4)
    (pointConversion : NativeRelatorConversionChecking.Code 4) : Fin 3 → Code 4 :=
  fun index => if index = 0 then motiveCast point pointCode pointConversion
    else if index = 1 then pointCode else .var

theorem axp_images_check (point : Tower.Tm 4) (pointCode : Code 4)
    (pointConversion : NativeRelatorConversionChecking.Code 4)
    (pointChecked : StructuralTypingReplay.check IntrinsicRelator.rules
      NativeRelatorConversionChecking.check Intrinsic.contextAXPD
      point (.var 3) pointCode = true)
    (pointConverted : NativeRelatorConversionChecking.check pointConversion
      (.var 2) point = true) :
    TelescopeArgumentChecking.checkArguments
      (StructuralTypingReplay.check IntrinsicRelator.rules
        NativeRelatorConversionChecking.check Intrinsic.contextAXPD)
      Intrinsic.contextAXP (axpSubstitution point)
        (axpImageCodes point pointCode pointConversion) = true := by
  apply (TelescopeArgumentChecking.checkArguments_eq_true_iff _ _ _ _).mpr
  intro index
  fin_cases index
  · change StructuralTypingReplay.check IntrinsicRelator.rules
        NativeRelatorConversionChecking.check Intrinsic.contextAXPD
        (.var 1) (expectedMotive point)
        (motiveCast point pointCode pointConversion) = true
    exact motive_cast_checked point pointCode pointConversion pointChecked pointConverted
  · change StructuralTypingReplay.check IntrinsicRelator.rules
        NativeRelatorConversionChecking.check Intrinsic.contextAXPD
        point (.var 3) pointCode = true
    exact pointChecked
  · change StructuralTypingReplay.check IntrinsicRelator.rules
        NativeRelatorConversionChecking.check Intrinsic.contextAXPD
        (.var 3) (sortTm Intrinsic.elementLevel) (.var : Code 4) = true
    decide +kernel

private def methodProposal : Tower.Tm 3 × Code 3 :=
  (CertificateProposal.term 64 Intrinsic.contextAXP Intrinsic.identityReflCaseType).get
    (by decide +kernel)

private def methodLevel? : Option Tower.Head :=
  match methodProposal.1 with
  | .head level => some level
  | _ => none

def methodLevel : Tower.Head := methodLevel?.get (by decide +kernel)

private theorem method_source_checked :
    NativeJudgmentReplay.check Intrinsic.contextAXP Intrinsic.identityReflCaseType
      (.head methodLevel) axpCode methodProposal.2 = true := by
  decide +kernel

def methodFormation (point : Tower.Tm 4) (pointCode : Code 4)
    (pointConversion : NativeRelatorConversionChecking.Code 4) : Code 4 :=
  NativeJudgmentReplay.substitute (axpSubstitution point)
    (axpImageCodes point pointCode pointConversion)
    Intrinsic.identityReflCaseType (.head methodLevel) methodProposal.2

theorem method_formed (point : Tower.Tm 4) (pointCode : Code 4)
    (pointConversion : NativeRelatorConversionChecking.Code 4)
    (pointChecked : StructuralTypingReplay.check IntrinsicRelator.rules
      NativeRelatorConversionChecking.check Intrinsic.contextAXPD
      point (.var 3) pointCode = true)
    (pointConverted : NativeRelatorConversionChecking.check pointConversion
      (.var 2) point = true) :
    StructuralTypingReplay.check IntrinsicRelator.rules
      NativeRelatorConversionChecking.check Intrinsic.contextAXPD
      (expectedMethod point) (.head methodLevel)
      (methodFormation point pointCode pointConversion) = true := by
  have accepted := NativeJudgmentReplay.check_substitute method_source_checked
    targetCode target_formed (axpSubstitution point)
    (axpImageCodes point pointCode pointConversion)
    (axp_images_check point pointCode pointConversion pointChecked pointConverted)
  have same : subst (axpSubstitution point) Intrinsic.identityReflCaseType =
      expectedMethod point := by
    rfl
  rw [same] at accepted
  change StructuralTypingReplay.checkJudgment IntrinsicRelator.rules
    NativeRelatorConversionChecking.check Intrinsic.contextAXPD
    (expectedMethod point) (.head methodLevel) targetCode
    (methodFormation point pointCode pointConversion) = true at accepted
  simp only [StructuralTypingReplay.checkJudgment, Bool.and_eq_true] at accepted
  exact accepted.2

def completeImageCodes (point : Tower.Tm 4) (pointCode : Code 4)
    (pointConversion : NativeRelatorConversionChecking.Code 4) : Fin 4 → Code 4 :=
  imageCodes pointCode point pointConversion motiveLevel methodLevel
    (motiveFormation point pointCode)
    (methodFormation point pointCode pointConversion)

theorem complete_images_check (point : Tower.Tm 4) (pointCode : Code 4)
    (pointConversion : NativeRelatorConversionChecking.Code 4)
    (pointChecked : StructuralTypingReplay.check IntrinsicRelator.rules
      NativeRelatorConversionChecking.check Intrinsic.contextAXPD
      point (.var 3) pointCode = true)
    (pointConverted : NativeRelatorConversionChecking.check pointConversion
      (.var 2) point = true) :
    TelescopeArgumentChecking.checkArguments
      (StructuralTypingReplay.check IntrinsicRelator.rules
        NativeRelatorConversionChecking.check Intrinsic.contextAXPD)
      Intrinsic.contextAXPD (substitutePoint point)
      (completeImageCodes point pointCode pointConversion) = true := by
  exact NativeDeclaredJPointConversion.images_check point pointCode pointConversion
    motiveLevel methodLevel (motiveFormation point pointCode)
    (methodFormation point pointCode pointConversion)
    pointChecked pointConverted (by decide +kernel) (by decide +kernel)
    (motive_formed point pointCode pointChecked)
    (method_formed point pointCode pointConversion pointChecked pointConverted)

#print axioms complete_images_check

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeDeclaredJPointFormation
