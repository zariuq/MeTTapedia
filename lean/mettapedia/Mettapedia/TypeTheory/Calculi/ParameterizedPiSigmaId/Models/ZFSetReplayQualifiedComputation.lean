import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayQualifiedTyping
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayBetaReduction
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayCoherence

/-!
# Beta computation with semantically admitted computed arguments

Result-formation qualification supplies argument membership by structural
typing induction. Arguments need not reduce to variables, be neutral, or
have a supplied normal form. This closes the admission premise of the
existing beta-value theorem, including cumulative result wrappers.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace ZFSetReplayInterpretation

open StructuralTypingReplay
open ZFSetTypeExpressionInterpretation (Environment)

universe u
variable {Head : Type} {n : Nat}
variable (heads : Head → ZFSet.{u}) (constants : DeclName → ZFSet.{u})
variable (R : Rules Head) [DecidableEq Head]
variable [∀ h v, Decidable (R.headTyping h v)] [∀ h, Decidable (R.isUniverse h)]
variable [∀ v w z, Decidable (R.join v w z)] [∀ v w, Decidable (R.cumulative v w)]
variable (successor : Head → Head) (universes : FormationSensitive.UniverseRegularity R)
variable (successorQualified : ∀ level, R.isUniverse level →
  R.isUniverse (successor level) ∧ R.headTyping level (successor level))
variable (model : UniverseModel R heads) (constantModel : ConstantsModel heads constants R)

include universes successorQualified model constantModel

theorem qualified_rootBeta_admitted (code : Code Head NoConversion n) :
    ∀ {context : Ctx Head n} {body : Tm Head (n + 1)} {argument type : Tm Head n}
      (contextCode : ContextCode Head NoConversion n) {valid : Environment.{u} n → Prop},
      checkContext R noConversionCheck context contextCode = true →
      check R noConversionCheck context (.app (.lam body) argument) type code = true →
      code.resultFormationsNeutral R successor contextCode (.app (.lam body) argument) type = true →
      assembleContext heads constants contextCode context = some valid →
      ∀ env, valid env → RootBetaAdmitted heads constants argument type env code := by
  induction code with
  | cumul lower prior ih =>
      intro context body argument type contextCode valid contextChecked checked qualified atContext env admitted
      cases type <;> simp only [check, Bool.and_eq_true, Bool.false_eq_true] at checked
      exact ih contextCode contextChecked checked.1
        (Bool.and_eq_true_iff.mp qualified).2 atContext env admitted
  | appElim A B function argumentCode _ _ =>
      intro context body argument type contextCode valid contextChecked checked qualified atContext env admitted
      have premises := checked
      simp only [check, Bool.and_eq_true, decide_eq_true_eq] at premises
      obtain ⟨⟨functionChecked, argumentChecked⟩, rfl⟩ := premises
      have argumentQualified := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp qualified).2).2
      cases function with
      | convert _ _ _ _ impossible => exact nomatch impossible
      | lamIntro level formation bodyCode =>
        have formationChecked := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp functionChecked).1).2
        obtain ⟨domainLevel, bodyLevel, domainCode, codomainCode, parts, _, _, domainChecked, _⟩ :=
          formation.piFormation_checked R noConversionCheck formationChecked
        obtain ⟨arg, atArgument, _⟩ :=
          accepted_assembles heads constants R noConversionCheck argumentCode argumentChecked
        obtain ⟨domain, atDomain, _⟩ :=
          accepted_assembles heads constants R noConversionCheck domainCode domainChecked
        have member := qualified_membership heads constants R successor universes successorQualified
          model constantModel argumentCode contextCode contextChecked argumentChecked argumentQualified
          valid arg atContext atArgument domainLevel domainCode domain domainChecked atDomain env admitted
        exact rootBeta_argument_admitted heads constants R checked parts arg domain atArgument atDomain env member
      | _ => simp only [check, Bool.false_eq_true] at functionChecked
  | convert _ _ _ _ impossible _ _ => exact nomatch impossible
  | _ => intros; simp_all only [check, Bool.false_eq_true]

/-- The existing executable contraction returns an accepted certificate and
preserves the interpreted value on all valid environments. Membership is
earned from the source qualification, not an additional semantic premise. -/
theorem qualified_contractBeta {context : Ctx Head n} {body : Tm Head (n + 1)}
    {argument type : Tm Head n} (contextCode : ContextCode Head NoConversion n)
    (code : Code Head NoConversion n) (source : Meaning.{u} n)
    {valid : Environment.{u} n → Prop}
    (contextChecked : checkContext R noConversionCheck context contextCode = true)
    (checked : check R noConversionCheck context (.app (.lam body) argument) type code = true)
    (qualified : code.resultFormationsNeutral R successor contextCode (.app (.lam body) argument) type = true)
    (atContext : assembleContext heads constants contextCode context = some valid)
    (atSource : assemble heads constants code (.app (.lam body) argument) type = some source) :
    ∃ resultCode result,
      code.contractBeta body argument type = some resultCode ∧
      check R noConversionCheck context (inst0 argument body) type resultCode = true ∧
      assemble heads constants resultCode (inst0 argument body) type = some result ∧
      ∀ env, valid env → source.value env = result.value env := by
  obtain ⟨resultCode, computed, resultChecked⟩ := code.contractBeta_checked R checked
  obtain ⟨result, atResult, _⟩ :=
    accepted_assembles heads constants R noConversionCheck resultCode resultChecked
  refine ⟨resultCode, result, computed, resultChecked, atResult, ?_⟩
  intro env admitted
  have rootAdmitted := qualified_rootBeta_admitted heads constants R successor universes
    successorQualified model constantModel code contextCode contextChecked checked qualified atContext env admitted
  obtain ⟨actual, atActual, equal⟩ :=
    contractBeta_value heads constants R code source checked atSource computed env rootAdmitted
  rw [atResult] at atActual
  cases Option.some.inj atActual
  exact equal

/-- Independent qualified certificates agree through a common independently
checked neutral-elimination reduct. Internal lambda domains may differ.
There is no argument-membership assumption left for the caller to discharge. -/
theorem qualified_rootBeta_coherent
    {context : Ctx Head n} {body : Tm Head (n + 1)} {argument type : Tm Head n}
    (contextCode : ContextCode Head NoConversion n)
    (leftCode rightCode normalCode : Code Head NoConversion n)
    (left right normal : Meaning.{u} n) {valid : Environment.{u} n → Prop}
    (contextChecked : checkContext R noConversionCheck context contextCode = true)
    (leftChecked : check R noConversionCheck context (.app (.lam body) argument) type leftCode = true)
    (rightChecked : check R noConversionCheck context (.app (.lam body) argument) type rightCode = true)
    (leftQualified : leftCode.resultFormationsNeutral R successor contextCode
      (.app (.lam body) argument) type = true)
    (rightQualified : rightCode.resultFormationsNeutral R successor contextCode
      (.app (.lam body) argument) type = true)
    (atContext : assembleContext heads constants contextCode context = some valid)
    (atLeft : assemble heads constants leftCode (.app (.lam body) argument) type = some left)
    (atRight : assemble heads constants rightCode (.app (.lam body) argument) type = some right)
    (normalChecked : check R noConversionCheck context (inst0 argument body) type normalCode = true)
    (normalQualified : normalCode.neutralEliminations (inst0 argument body) type = true)
    (atNormal : assemble heads constants normalCode (inst0 argument body) type = some normal)
    (env : Environment.{u} n) (admitted : valid env) : left.value env = right.value env := by
  exact rootBeta_coherent_of_normal_reduct heads constants R leftCode rightCode normalCode
    left right normal leftChecked rightChecked atLeft atRight normalChecked normalQualified atNormal env
    (qualified_rootBeta_admitted heads constants R successor universes successorQualified model
      constantModel leftCode contextCode contextChecked leftChecked leftQualified atContext env admitted)
    (qualified_rootBeta_admitted heads constants R successor universes successorQualified model
      constantModel rightCode contextCode contextChecked rightChecked rightQualified atContext env admitted)

/-- Two independently checked beta applications agree whenever their actual
contracted expression belongs to the structural interpretation fragment.
The argument itself may be an arbitrary computed expression admitted by the
qualified source certificates; no common reduct certificate or neutral
elimination hypothesis is supplied by the caller. -/
theorem qualified_rootBeta_coherent_of_supported_reduct
    {context : Ctx Head n} {body : Tm Head (n + 1)} {argument type : Tm Head n}
    (contextCode : ContextCode Head NoConversion n)
    (leftCode rightCode : Code Head NoConversion n)
    (left right : Meaning.{u} n) {valid : Environment.{u} n → Prop}
    (contextChecked : checkContext R noConversionCheck context contextCode = true)
    (leftChecked : check R noConversionCheck context (.app (.lam body) argument) type
      leftCode = true)
    (rightChecked : check R noConversionCheck context (.app (.lam body) argument) type
      rightCode = true)
    (leftQualified : leftCode.resultFormationsNeutral R successor contextCode
      (.app (.lam body) argument) type = true)
    (rightQualified : rightCode.resultFormationsNeutral R successor contextCode
      (.app (.lam body) argument) type = true)
    (atContext : assembleContext heads constants contextCode context = some valid)
    (atLeft : assemble heads constants leftCode (.app (.lam body) argument) type = some left)
    (atRight : assemble heads constants rightCode (.app (.lam body) argument) type = some right)
    (reductSupported : ZFSetTypeExpressionInterpretation.supported
      (inst0 argument body) = true) :
    ∀ env, valid env → left.value env = right.value env := by
  obtain ⟨leftResultCode, leftResult, _, _, atLeftResult, leftPreserves⟩ :=
    qualified_contractBeta heads constants R successor universes successorQualified
      model constantModel contextCode leftCode left contextChecked leftChecked
      leftQualified atContext atLeft
  obtain ⟨rightResultCode, rightResult, _, _, atRightResult, rightPreserves⟩ :=
    qualified_contractBeta heads constants R successor universes successorQualified
      model constantModel contextCode rightCode right contextChecked rightChecked
      rightQualified atContext atRight
  have resultsEqual := assemble_supported_values heads constants reductSupported
    atLeftResult atRightResult
  intro env admitted
  calc
    left.value env = leftResult.value env := leftPreserves env admitted
    _ = rightResult.value env := congrFun resultsEqual env
    _ = right.value env := (rightPreserves env admitted).symm

/-- Reflexivity inhabits an independently formed identity fibre whose two
endpoint certificates may retain different internal domains. This is a
derived identity-compatible comparison, even when the identity result
formation itself fails the neutral qualification. -/
theorem qualified_rootBeta_identity_membership
    {context : Ctx Head n} {body : Tm Head (n + 1)} {argument A : Tm Head n}
    (contextCode : ContextCode Head NoConversion n)
    (level : Head) (formation leftCode rightCode normalCode : Code Head NoConversion n)
    (proofMeaning identityMeaning : Meaning.{u} n) {valid : Environment.{u} n → Prop}
    (contextChecked : checkContext R noConversionCheck context contextCode = true)
    (identityChecked : check R noConversionCheck context
      (.id A (.app (.lam body) argument) (.app (.lam body) argument)) (.head level)
      (.idForm level formation leftCode rightCode) = true)
    (leftQualified : leftCode.resultFormationsNeutral R successor contextCode
      (.app (.lam body) argument) A = true)
    (rightQualified : rightCode.resultFormationsNeutral R successor contextCode
      (.app (.lam body) argument) A = true)
    (atContext : assembleContext heads constants contextCode context = some valid)
    (atProof : assemble heads constants (.reflIntro A leftCode) (.refl (.app (.lam body) argument))
      (.id A (.app (.lam body) argument) (.app (.lam body) argument)) = some proofMeaning)
    (atIdentity : assemble heads constants (.idForm level formation leftCode rightCode)
      (.id A (.app (.lam body) argument) (.app (.lam body) argument)) (.head level) = some identityMeaning)
    (normalChecked : check R noConversionCheck context (inst0 argument body) A normalCode = true)
    (normalQualified : normalCode.neutralEliminations (inst0 argument body) A = true)
    (env : Environment.{u} n) (admitted : valid env) :
    check R noConversionCheck context (.refl (.app (.lam body) argument))
      (.id A (.app (.lam body) argument) (.app (.lam body) argument)) (.reflIntro A leftCode) = true ∧
      proofMeaning.value env ∈ identityMeaning.value env := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq] at identityChecked
  have leftChecked := identityChecked.1.1.2
  have rightChecked := identityChecked.1.2
  obtain ⟨left, atLeft, _⟩ := accepted_assembles heads constants R noConversionCheck leftCode leftChecked
  obtain ⟨right, atRight, _⟩ := accepted_assembles heads constants R noConversionCheck rightCode rightChecked
  obtain ⟨normal, atNormal, _⟩ := accepted_assembles heads constants R noConversionCheck normalCode normalChecked
  have equal := qualified_rootBeta_coherent heads constants R successor universes successorQualified
    model constantModel contextCode leftCode rightCode normalCode left right normal contextChecked
    leftChecked rightChecked leftQualified rightQualified atContext atLeft atRight
    normalChecked normalQualified atNormal env admitted
  refine ⟨?_, ?_⟩
  · simpa only [check, Bool.and_eq_true, decide_eq_true_eq, and_true] using leftChecked
  · simp only [assemble, Option.some.injEq] at atProof
    subst proofMeaning
    simp only [assemble, atLeft, atRight, Option.bind_eq_bind, Option.bind_some,
      Option.pure_def, Option.some.injEq] at atIdentity
    subst identityMeaning
    exact (Mettapedia.Logic.HOL.Embedding.ZFSetTraceProofDecoding.mem_truthCode _ _).mpr ⟨rfl, equal⟩

#print axioms qualified_rootBeta_identity_membership
#print axioms qualified_rootBeta_coherent
#print axioms qualified_rootBeta_coherent_of_supported_reduct
#print axioms qualified_rootBeta_admitted
#print axioms qualified_contractBeta

end ZFSetReplayInterpretation
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
