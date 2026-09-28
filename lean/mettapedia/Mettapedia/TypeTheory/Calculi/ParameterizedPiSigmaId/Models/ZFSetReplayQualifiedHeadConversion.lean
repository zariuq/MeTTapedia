import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayQualifiedTyping
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.StructuralConversionCode

/-!
# Qualified membership through one checked head conversion

A source program may have a structural typing certificate while its displayed
type is changed by a retained head-conversion step. The conversion checker
establishes the new judgment. Semantic membership additionally requires that
the model interpret equivalent heads by equal sets; universe-model typing
closure alone does not include this condition.

This file covers one head step, not arbitrary beta, declaration roots, or a
conversion path containing those steps.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace ZFSetReplayInterpretation

open StructuralTypingReplay StructuralConversionCode
open ZFSetTypeExpressionInterpretation (Environment)

universe u

variable {Head : Type} {RootCode : Nat → Type} {n : Nat}
variable (R : Rules Head) [DecidableEq Head] [DecidableRel R.headEq]

def headStepCheck
    (decodeRoot : {n : Nat} → RootCode n → Option (Tm Head n × Tm Head n))
    {n : Nat} (code : StructuralConversionCode.Code Head RootCode n)
    (left right : Tm Head n) : Bool :=
  code.check R.headEq decodeRoot left right

def headConvertedCode (sourceCode : StructuralTypingReplay.Code Head NoConversion n)
    (sourceHead targetHead targetLevel : Head) :
    StructuralTypingReplay.Code Head (StructuralConversionCode.Code Head RootCode) n :=
  .convert (.head sourceHead) targetLevel
    (sourceCode.mapConversion (fun impossible => nomatch impossible))
    .headType (.single (.head sourceHead targetHead))

theorem head_step_checked
    (decodeRoot : {n : Nat} → RootCode n → Option (Tm Head n × Tm Head n))
    (sourceHead targetHead : Head) (related : R.headEq sourceHead targetHead) :
    headStepCheck R decodeRoot
      (.single (.head sourceHead targetHead) :
        StructuralConversionCode.Code Head RootCode n)
      (.head sourceHead) (.head targetHead) = true := by
  simp [headStepCheck, StructuralConversionCode.Code.check,
    StructuralConversionCode.Code.decode, StructuralConversionCode.StepCode.decode,
    related]

variable [∀ h v, Decidable (R.headTyping h v)] [∀ h, Decidable (R.isUniverse h)]
variable [∀ v w z, Decidable (R.join v w z)] [∀ v w, Decidable (R.cumulative v w)]

theorem embedded_source_checked
    (decodeRoot : {n : Nat} → RootCode n → Option (Tm Head n × Tm Head n))
    (context : Ctx Head n) (subject type : Tm Head n)
    (sourceCode : StructuralTypingReplay.Code Head NoConversion n)
    (sourceChecked : StructuralTypingReplay.check R noConversionCheck context
      subject type sourceCode = true) :
    StructuralTypingReplay.check R (headStepCheck R decodeRoot) context
      subject type
      (sourceCode.mapConversion (fun impossible => nomatch impossible)) = true := by
  have comparison := StructuralTypingReplay.check_mapConversion R noConversionCheck
    (headStepCheck R decodeRoot) (fun impossible => nomatch impossible)
    (by intro n impossible; exact nomatch impossible)
    sourceCode context subject type
  exact comparison.trans sourceChecked

/-- A qualified program checked at one universe head remains semantically
typed after one accepted head-conversion wrapper. The source membership is
derived from the retained structural certificate; the model's head-equivalence
law is the separate premise needed to transport it to the displayed target. -/
theorem qualified_head_conversion_membership
    (decodeRoot : {n : Nat} → RootCode n → Option (Tm Head n × Tm Head n))
    (heads : Head → ZFSet.{u}) (constants : DeclName → ZFSet.{u})
    (headEqSound : ∀ left right, R.headEq left right → heads left = heads right)
    (successor : Head → Head)
    (universes : FormationSensitive.UniverseRegularity R)
    (successorQualified : ∀ level, R.isUniverse level →
      R.isUniverse (successor level) ∧ R.headTyping level (successor level))
    (model : UniverseModel R heads) (constantModel : ConstantsModel heads constants R)
    (context : Ctx Head n) (contextCode : ContextCode Head NoConversion n)
    (valid : Environment.{u} n → Prop)
    (contextChecked : StructuralTypingReplay.checkContext R noConversionCheck
      context contextCode = true)
    (atContext : assembleContext heads constants contextCode context = some valid)
    (subject : Tm Head n) (sourceCode : StructuralTypingReplay.Code Head NoConversion n)
    (sourceHead targetHead sourceLevel targetLevel : Head)
    (sourceChecked : StructuralTypingReplay.check R noConversionCheck context
      subject (.head sourceHead) sourceCode = true)
    (qualified : sourceCode.resultFormationsNeutral R successor contextCode
      subject (.head sourceHead) = true)
    (sourceFormed : R.headTyping sourceHead sourceLevel)
    (targetFormed : R.headTyping targetHead targetLevel)
    (targetUniverse : R.isUniverse targetLevel)
    (related : R.headEq sourceHead targetHead) :
    ∃ meaning,
      assemble heads constants sourceCode subject (.head sourceHead) = some meaning ∧
      StructuralTypingReplay.check R (headStepCheck R decodeRoot) context
        subject (.head targetHead)
        (headConvertedCode (RootCode := RootCode) sourceCode
          sourceHead targetHead targetLevel) = true ∧
      assemble heads constants
        (headConvertedCode (RootCode := RootCode) sourceCode
          sourceHead targetHead targetLevel)
        subject (.head targetHead) = some meaning ∧
      ∀ env, valid env → meaning.value env ∈ heads targetHead := by
  obtain ⟨meaning, atSource, _⟩ := accepted_assembles heads constants R
    noConversionCheck sourceCode sourceChecked
  have mapped := embedded_source_checked R decodeRoot context subject
    (.head sourceHead) sourceCode sourceChecked
  have conversionChecked := head_step_checked (n := n)
    R decodeRoot sourceHead targetHead related
  have targetChecked : StructuralTypingReplay.check R (headStepCheck R decodeRoot)
      context subject (.head targetHead)
      (headConvertedCode (RootCode := RootCode) sourceCode
        sourceHead targetHead targetLevel) = true := by
    simp only [headConvertedCode, StructuralTypingReplay.check,
      decide_eq_true targetUniverse, mapped, decide_eq_true targetFormed,
      conversionChecked, Bool.true_and]
  have atMapped := assemble_mapConversion
    (OtherCode := StructuralConversionCode.Code Head RootCode)
    (fun {n} (impossible : NoConversion n) => nomatch impossible)
    heads constants sourceCode subject (.head sourceHead)
  have atConverted : assemble heads constants
      (headConvertedCode (RootCode := RootCode) sourceCode
        sourceHead targetHead targetLevel)
      subject (.head targetHead) = some meaning := by
    simpa only [headConvertedCode, assemble] using atMapped.trans atSource
  have sourceFormationChecked : StructuralTypingReplay.check R noConversionCheck
      context (.head sourceHead) (.head sourceLevel)
      (.headType : StructuralTypingReplay.Code Head NoConversion n) = true := by
    simpa only [StructuralTypingReplay.check, decide_eq_true_eq] using sourceFormed
  have atSourceFormation : assemble heads constants
      (.headType : StructuralTypingReplay.Code Head NoConversion n)
      (.head sourceHead) (.head sourceLevel) =
      some (.plain (fun _ => heads sourceHead) : Meaning.{u} n) := rfl
  have sourceMember := qualified_membership heads constants R successor universes
    successorQualified model constantModel sourceCode contextCode contextChecked
    sourceChecked qualified valid meaning atContext atSource sourceLevel
    (.headType : StructuralTypingReplay.Code Head NoConversion n)
    (.plain (fun _ => heads sourceHead) : Meaning.{u} n)
    sourceFormationChecked atSourceFormation
  refine ⟨meaning, atSource, targetChecked, atConverted, ?_⟩
  intro env admitted
  rw [← headEqSound sourceHead targetHead related]
  exact sourceMember env admitted

#print axioms head_step_checked
#print axioms embedded_source_checked
#print axioms qualified_head_conversion_membership

end ZFSetReplayInterpretation
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
