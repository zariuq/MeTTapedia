import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeIntroductionView
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Checking.NativeIntroductionComputationReplay
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Conversion.NativeConversionComponents

/-!
# Native computation through converted introduction premises

Actual introduction evidence is extracted from the supplied function or pair
proof. Computed component conversions align its original types with the
eliminator's types. The contractum retains the displayed dependent type through
checked substitution and an explicit result cast. No proof search is used.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false


namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeJudgmentReplay.ConvertedIntroductionComputation

open Presentation StructuralTypingReplay NativeIndexedFamilies NativeParallelReceipt

def betaPi {n : Nat} (contextCode : ContextCode n) (A : Tower.Tm n)
    (B body : Tower.Tm (n + 1)) (argument : Tower.Tm n)
    (functionCode argumentCode : Code n) : Option (Code n) := do
  let view ← lambdaView (.pi A B) functionCode
  let components ← checkedPiComponents view.conversion view.domain A view.codomain B
  let (u, _, domainFormation, _) ← view.formation.piFormation
  let convertedArgument := Code.convert A u argumentCode domainFormation components.1.symm.code
  let contractum := IntroductionComputation.betaPi body view.codomain argument view.body convertedArgument
  let (v, formation) ← resultFormation contextCode (.app (.lam body) argument) (inst0 argument B)
    (.appElim A B functionCode argumentCode)
  return .convert (inst0 argument view.codomain) v contractum formation
    (NativeRelatorConversionChecking.substitute (subst0 argument) components.2.code)

theorem betaPi_checked {n : Nat} {context : Tower.Ctx n} {contextCode : ContextCode n}
    {A argument : Tower.Tm n} {B body : Tower.Tm (n + 1)} {functionCode argumentCode : Code n}
    (accepted : check context (.app (.lam body) argument) (inst0 argument B) contextCode
      (.appElim A B functionCode argumentCode) = true) :
    ∃ resultCode, betaPi contextCode A B body argument functionCode argumentCode = some resultCode ∧
      check context (inst0 argument body) (inst0 argument B) contextCode resultCode = true := by
  have inputs := accepted
  simp only [check, checkJudgment, StructuralTypingReplay.check, Bool.and_eq_true,
    decide_eq_true_eq] at inputs
  obtain ⟨view, viewComputed, isU, formed, bodyChecked, converted⟩ := lambdaView_checked inputs.2.1.1
  let components := piComponents (⟨view.conversion, converted⟩ :
    NativeCompletedRootCertificate.Certificate (.pi view.domain view.codomain) (.pi A B))
  have componentComputed : checkedPiComponents view.conversion view.domain A view.codomain B =
      some components := by simp only [checkedPiComponents, converted, ↓reduceDIte, components]
  obtain ⟨u, v, domainFormation, bodyFormation, formationComputed,
      isDomainUniverse, _, domainFormed, _⟩ :=
    Code.piFormation_checked IntrinsicRelator.rules NativeRelatorConversionChecking.check view.formation formed
  let convertedArgument := Code.convert A u argumentCode domainFormation components.1.symm.code
  have argumentChecked : StructuralTypingReplay.check IntrinsicRelator.rules
      NativeRelatorConversionChecking.check context argument view.domain convertedArgument = true := by
    simp only [convertedArgument, StructuralTypingReplay.check, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨⟨isDomainUniverse, inputs.2.1.2⟩, domainFormed⟩, components.1.symm.checked⟩
  have sourceChecked : check context (.app (.lam body) argument) (inst0 argument view.codomain)
      contextCode (.appElim view.domain view.codomain
        (.lamIntro view.level view.formation view.body) convertedArgument) = true := by
    simp only [check, checkJudgment, StructuralTypingReplay.check, Bool.and_eq_true,
      decide_eq_true_eq]
    exact ⟨inputs.1, ⟨⟨⟨⟨isU, formed⟩, bodyChecked⟩, argumentChecked⟩, True.intro⟩⟩
  have contractumChecked := (IntroductionComputation.betaPi_checked sourceChecked).1
  obtain ⟨level, formation, resultComputed, levelUniverse, resultFormed⟩ := resultFormation_checked accepted
  let resultCode := Code.convert (inst0 argument view.codomain) level
    (IntroductionComputation.betaPi body view.codomain argument view.body convertedArgument) formation
    (NativeRelatorConversionChecking.substitute (subst0 argument) components.2.code)
  refine ⟨resultCode, ?_, ?_⟩
  · simp [betaPi, viewComputed, componentComputed, formationComputed, resultComputed,
      resultCode, convertedArgument]
  · simp only [check, checkJudgment, Bool.and_eq_true] at contractumChecked resultFormed
    simp only [resultCode, check, checkJudgment, StructuralTypingReplay.check,
      Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨inputs.1, ⟨⟨⟨levelUniverse, contractumChecked.2⟩, resultFormed.2⟩,
      NativeRelatorConversionChecking.check_substitute (subst0 argument) components.2.code
        components.2.checked⟩⟩

def betaSigmaFst {n : Nat} (contextCode : ContextCode n) (A : Tower.Tm n)
    (B : Tower.Tm (n + 1)) (first second : Tower.Tm n) (pairCode : Code n) : Option (Code n) := do
  let view ← pairView (.sigma A B) pairCode
  let components ← checkedSigmaComponents view.conversion view.domain A view.codomain B
  let (u, formation) ← resultFormation contextCode (.fst (.pair first second)) A (.fstElim B pairCode)
  return .convert view.domain u view.first formation components.1.code

theorem betaSigmaFst_checked {n : Nat} {context : Tower.Ctx n} {contextCode : ContextCode n}
    {A first second : Tower.Tm n} {B : Tower.Tm (n + 1)} {pairCode : Code n}
    (accepted : check context (.fst (.pair first second)) A contextCode (.fstElim B pairCode) = true) :
    ∃ resultCode, betaSigmaFst contextCode A B first second pairCode = some resultCode ∧
      check context first A contextCode resultCode = true := by
  have inputs := accepted
  simp only [check, checkJudgment, StructuralTypingReplay.check, Bool.and_eq_true] at inputs
  obtain ⟨view, viewComputed, _, _, firstChecked, _, converted⟩ := pairView_checked inputs.2
  let components := sigmaComponents (⟨view.conversion, converted⟩ :
    NativeCompletedRootCertificate.Certificate (.sigma view.domain view.codomain) (.sigma A B))
  have componentComputed : checkedSigmaComponents view.conversion view.domain A view.codomain B =
      some components := by simp only [checkedSigmaComponents, converted, ↓reduceDIte, components]
  obtain ⟨u, formation, resultComputed, isU, formed⟩ := resultFormation_checked accepted
  refine ⟨.convert view.domain u view.first formation components.1.code, ?_, ?_⟩
  · simp [betaSigmaFst, viewComputed, componentComputed, resultComputed]
  · simp only [check, checkJudgment, Bool.and_eq_true] at formed
    simp only [check, checkJudgment, StructuralTypingReplay.check, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨inputs.1, ⟨⟨⟨isU, firstChecked⟩, formed.2⟩, components.1.checked⟩⟩

def betaSigmaSnd {n : Nat} (contextCode : ContextCode n) (A : Tower.Tm n)
    (B : Tower.Tm (n + 1)) (first second : Tower.Tm n) (pairCode : Code n) : Option (Code n) := do
  let view ← pairView (.sigma A B) pairCode
  let components ← checkedSigmaComponents view.conversion view.domain A view.codomain B
  let (u, formation) ← resultFormation contextCode (.snd (.pair first second))
    (inst0 (.fst (.pair first second)) B) (.sndElim A B pairCode)
  return .convert (inst0 first view.codomain) u view.second formation
    (.trans (NativeRelatorConversionChecking.substitute (subst0 first) components.2.code)
      (.symm (NativeRelatorConversionChecking.inst0Argument (.fst (.pair first second)) first
        (.single (.betaSigmaFst first second)) B)))

theorem betaSigmaSnd_checked {n : Nat} {context : Tower.Ctx n} {contextCode : ContextCode n}
    {A first second : Tower.Tm n} {B : Tower.Tm (n + 1)} {pairCode : Code n}
    (accepted : check context (.snd (.pair first second)) (inst0 (.fst (.pair first second)) B)
      contextCode (.sndElim A B pairCode) = true) :
    ∃ resultCode, betaSigmaSnd contextCode A B first second pairCode = some resultCode ∧
      check context second (inst0 (.fst (.pair first second)) B) contextCode resultCode = true := by
  have inputs := accepted
  simp only [check, checkJudgment, StructuralTypingReplay.check, Bool.and_eq_true,
    decide_eq_true_eq] at inputs
  obtain ⟨view, viewComputed, _, _, _, secondChecked, converted⟩ := pairView_checked inputs.2.1
  let components := sigmaComponents (⟨view.conversion, converted⟩ :
    NativeCompletedRootCertificate.Certificate (.sigma view.domain view.codomain) (.sigma A B))
  have componentComputed : checkedSigmaComponents view.conversion view.domain A view.codomain B =
      some components := by simp only [checkedSigmaComponents, converted, ↓reduceDIte, components]
  obtain ⟨u, formation, resultComputed, isU, formed⟩ := resultFormation_checked accepted
  let conversion := StructuralConversionCode.Code.trans
    (NativeRelatorConversionChecking.substitute (subst0 first) components.2.code)
    (.symm (NativeRelatorConversionChecking.inst0Argument (.fst (.pair first second)) first
      (.single (.betaSigmaFst first second)) B))
  refine ⟨.convert (inst0 first view.codomain) u view.second formation conversion, ?_, ?_⟩
  · simp [betaSigmaSnd, viewComputed, componentComputed, resultComputed, conversion]
  · simp only [check, checkJudgment, Bool.and_eq_true] at formed
    simp only [check, checkJudgment, StructuralTypingReplay.check, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨inputs.1, ⟨⟨⟨isU, secondChecked⟩, formed.2⟩, ?_⟩⟩
    apply StructuralConversionCode.Code.check_trans Tower.HeadEq NativeRelatorRootConversionCode.decode
    · exact NativeRelatorConversionChecking.check_substitute (subst0 first) components.2.code components.2.checked
    · apply StructuralConversionCode.Code.check_symm Tower.HeadEq NativeRelatorRootConversionCode.decode
      apply NativeRelatorConversionChecking.check_inst0Argument
      simp [NativeRelatorConversionChecking.check, StructuralConversionCode.Code.check,
        StructuralConversionCode.Code.decode, StructuralConversionCode.StepCode.decode]

#print axioms betaPi_checked
#print axioms betaSigmaFst_checked
#print axioms betaSigmaSnd_checked

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeJudgmentReplay.ConvertedIntroductionComputation
