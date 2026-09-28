import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayQualifiedHeadConversion
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayComputation

/-!
# A converted computed argument in a retained dependent product domain

The formation certificate for a dependent product retains the interpretation
of its domain. A computed argument checked at a convertible universe head can
be used at that exact retained domain when head equivalence is sound in the
model. Neither a variable-shaped argument nor a freestanding domain-membership
assumption is required.

The conversion fragment here consists of one checked head step. Other
conversion classes require their own semantic preservation laws.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace ZFSetReplayInterpretation

open StructuralTypingReplay
open ZFSetTypeExpressionInterpretation (Environment)

universe u

variable {Head : Type} {RootCode : Nat → Type} {n : Nat}
variable (R : Rules Head) [DecidableEq Head] [DecidableRel R.headEq]
variable [∀ h v, Decidable (R.headTyping h v)] [∀ h, Decidable (R.isUniverse h)]
variable [∀ v w z, Decidable (R.join v w z)] [∀ v w, Decidable (R.cumulative v w)]

/-- Recover the exact domain of a checked dependent product, then admit a
computed argument whose retained certificate performs one head conversion. -/
theorem qualified_head_converted_argument_in_product_domain
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
    (contextChecked : checkContext R noConversionCheck context contextCode = true)
    (atContext : assembleContext heads constants contextCode context = some valid)
    (productLevel sourceHead targetHead sourceLevel targetLevel : Head)
    (B : Tm Head (n + 1))
    (formation : Code Head NoConversion n) (formed : Meaning.{u} n)
    (domain : Value.{u} n)
    (formationChecked : check R noConversionCheck context
      (.pi (.head targetHead) B) (.head productLevel) formation = true)
    (atFormation : assemble heads constants formation
      (.pi (.head targetHead) B) (.head productLevel) = some formed)
    (atDomain : formed.productDomain? = some domain)
    (argument : Tm Head n) (argumentCode : Code Head NoConversion n)
    (argumentChecked : check R noConversionCheck context argument
      (.head sourceHead) argumentCode = true)
    (argumentQualified : argumentCode.resultFormationsNeutral R successor
      contextCode argument (.head sourceHead) = true)
    (sourceFormed : R.headTyping sourceHead sourceLevel)
    (targetFormed : R.headTyping targetHead targetLevel)
    (targetUniverse : R.isUniverse targetLevel)
    (related : R.headEq sourceHead targetHead) :
    ∃ arg,
      check R (headStepCheck R decodeRoot) context argument (.head targetHead)
        (headConvertedCode (RootCode := RootCode) argumentCode
          sourceHead targetHead targetLevel) = true ∧
      assemble heads constants
        (headConvertedCode (RootCode := RootCode) argumentCode
          sourceHead targetHead targetLevel)
        argument (.head targetHead) = some arg ∧
      ∀ env, valid env → arg.value env ∈ domain env := by
  obtain ⟨arg, _, convertedChecked, atArgument, member⟩ :=
    qualified_head_conversion_membership R decodeRoot heads constants headEqSound
      successor universes successorQualified model constantModel context contextCode
      valid contextChecked atContext argument argumentCode sourceHead targetHead
      sourceLevel targetLevel argumentChecked argumentQualified sourceFormed
      targetFormed targetUniverse related
  obtain ⟨domainLevel, bodyLevel, domainCode, bodyCode, parts, _, _, _, _⟩ :=
    formation.piFormation_checked R noConversionCheck formationChecked
  obtain ⟨domainMeaning, _, atDomainCode, _, _, retained⟩ :=
    assemble_piFormation heads constants formation parts atFormation
  rw [atDomain] at retained
  cases Option.some.inj retained
  refine ⟨arg, convertedChecked, atArgument, ?_⟩
  intro env admitted
  have domainValue := agrees_with_type_expressions heads constants domainCode
    (.head targetHead) (.head domainLevel) domainMeaning rfl atDomainCode env
  change domainMeaning.value env = heads targetHead at domainValue
  rw [domainValue]
  exact member env admitted

/-- A checked dependent lambda actually consumes the converted computed
argument in its retained domain. The result has the expected beta value on
every valid environment; the application tree retains the conversion receipt. -/
theorem qualified_head_converted_lambda_application
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
    (contextChecked : checkContext R noConversionCheck context contextCode = true)
    (atContext : assembleContext heads constants contextCode context = some valid)
    (productLevel sourceHead targetHead sourceLevel targetLevel : Head)
    (B body : Tm Head (n + 1)) (argument : Tm Head n)
    (formation : Code Head NoConversion n)
    (bodyCode : Code Head NoConversion (n + 1))
    (argumentCode : Code Head NoConversion n)
    (productUniverse : R.isUniverse productLevel)
    (formationChecked : check R noConversionCheck context
      (.pi (.head targetHead) B) (.head productLevel) formation = true)
    (bodyChecked : check R noConversionCheck (.snoc context (.head targetHead))
      body B bodyCode = true)
    (argumentChecked : check R noConversionCheck context argument
      (.head sourceHead) argumentCode = true)
    (argumentQualified : argumentCode.resultFormationsNeutral R successor
      contextCode argument (.head sourceHead) = true)
    (sourceFormed : R.headTyping sourceHead sourceLevel)
    (targetFormed : R.headTyping targetHead targetLevel)
    (targetUniverse : R.isUniverse targetLevel)
    (related : R.headEq sourceHead targetHead) :
    let mappedFormation : Code Head (StructuralConversionCode.Code Head RootCode) n :=
      formation.mapConversion (fun impossible => nomatch impossible)
    let mappedBody : Code Head (StructuralConversionCode.Code Head RootCode) (n + 1) :=
      bodyCode.mapConversion (fun impossible => nomatch impossible)
    let convertedArgument := headConvertedCode (RootCode := RootCode)
      argumentCode sourceHead targetHead targetLevel
    let applicationCode : Code Head (StructuralConversionCode.Code Head RootCode) n :=
      .appElim (.head targetHead) B
        (.lamIntro productLevel mappedFormation mappedBody) convertedArgument
    ∃ arg result bodyMeaning,
      check R (headStepCheck R decodeRoot) context
        (.app (.lam body) argument) (inst0 argument B) applicationCode = true ∧
      assemble heads constants convertedArgument argument (.head targetHead) = some arg ∧
      assemble heads constants applicationCode
        (.app (.lam body) argument) (inst0 argument B) = some result ∧
      assemble heads constants mappedBody body B = some bodyMeaning ∧
      ∀ env, valid env →
        result.value env = bodyMeaning.value
          (ZFSetTypeExpressionInterpretation.extend env (arg.value env)) := by
  let mappedFormation : Code Head (StructuralConversionCode.Code Head RootCode) n :=
    formation.mapConversion (fun impossible => nomatch impossible)
  let mappedBody : Code Head (StructuralConversionCode.Code Head RootCode) (n + 1) :=
    bodyCode.mapConversion (fun impossible => nomatch impossible)
  let convertedArgument := headConvertedCode (RootCode := RootCode)
    argumentCode sourceHead targetHead targetLevel
  let applicationCode : Code Head (StructuralConversionCode.Code Head RootCode) n :=
    .appElim (.head targetHead) B
      (.lamIntro productLevel mappedFormation mappedBody) convertedArgument
  obtain ⟨formed, atFormation, product⟩ := accepted_assembles heads constants R
    noConversionCheck formation formationChecked
  obtain ⟨domain, atDomain⟩ := product (.head targetHead) B rfl
  obtain ⟨arg, convertedChecked, atArgument, inside⟩ :=
    qualified_head_converted_argument_in_product_domain R decodeRoot heads constants
      headEqSound successor universes successorQualified model constantModel
      context contextCode valid contextChecked atContext productLevel sourceHead
      targetHead sourceLevel targetLevel B formation formed domain formationChecked
      atFormation atDomain argument argumentCode argumentChecked argumentQualified
      sourceFormed targetFormed targetUniverse related
  have mappedFormationChecked : check R (headStepCheck R decodeRoot) context
      (.pi (.head targetHead) B) (.head productLevel) mappedFormation = true :=
    embedded_source_checked R decodeRoot context (.pi (.head targetHead) B)
      (.head productLevel) formation formationChecked
  have mappedBodyChecked : check R (headStepCheck R decodeRoot)
      (.snoc context (.head targetHead)) body B mappedBody = true :=
    embedded_source_checked R decodeRoot (.snoc context (.head targetHead))
      body B bodyCode bodyChecked
  have applicationChecked : check R (headStepCheck R decodeRoot) context
      (.app (.lam body) argument) (inst0 argument B) applicationCode = true := by
    simp [applicationCode, check, productUniverse,
      mappedFormationChecked, mappedBodyChecked]
    exact convertedChecked
  obtain ⟨bodyMeaning, atBody, _⟩ := accepted_assembles heads constants R
    noConversionCheck bodyCode bodyChecked
  have atMappedBody : assemble heads constants mappedBody body B = some bodyMeaning := by
    exact (assemble_mapConversion
      (OtherCode := StructuralConversionCode.Code Head RootCode)
      (fun {n} (impossible : NoConversion n) => nomatch impossible)
      heads constants bodyCode body B).trans atBody
  obtain ⟨result, atResult, _⟩ := accepted_assembles heads constants R
    (headStepCheck R decodeRoot) applicationCode applicationChecked
  have atMappedFormation : assemble heads constants mappedFormation
      (.pi (.head targetHead) B) (.head productLevel) = some formed := by
    exact (assemble_mapConversion
      (OtherCode := StructuralConversionCode.Code Head RootCode)
      (fun {n} (impossible : NoConversion n) => nomatch impossible)
      heads constants formation (.pi (.head targetHead) B) (.head productLevel)).trans
      atFormation
  refine ⟨arg, result, bodyMeaning, applicationChecked, atArgument, atResult,
    atMappedBody, ?_⟩
  intro env admitted
  exact application_lambda_value heads constants productLevel (.head targetHead) B
    body argument mappedFormation convertedArgument mappedBody formed arg result
    bodyMeaning domain atMappedFormation atDomain atMappedBody atArgument atResult
    env (inside env admitted)

#print axioms qualified_head_converted_argument_in_product_domain
#print axioms qualified_head_converted_lambda_application

end ZFSetReplayInterpretation
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
