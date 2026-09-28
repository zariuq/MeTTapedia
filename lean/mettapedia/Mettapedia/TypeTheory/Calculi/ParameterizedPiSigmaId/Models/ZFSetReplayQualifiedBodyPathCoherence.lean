import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayCrossContextQualifiedPaths
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayQualifiedApplicationComparison
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayFunctionRelations

/-!
# Comparing computed lambda bodies across retained product domains

The domain certificate embedded in each checked product formation determines
the context in which its body was checked. A qualified computation in each of
these distinct contexts can be compared at any argument admitted to both
domains, provided both computations reach one structurally interpreted term.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace ZFSetReplayInterpretation

open StructuralTypingReplay
open ZFSetTypeExpressionInterpretation (Environment extend)
open Mettapedia.Logic.HOL.Embedding.ZFSetTraceProducts (TraceFunctionRelated)

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

/-- Separate checked product formations supply the actual extended-context
certificates. At a value admitted to both retained domains, qualified body
computations with one supported terminal agree even if the raw domain types,
displayed body types, and intermediate certificates differ. -/
theorem qualified_body_paths_agree_on_shared_admitted_input
    (context : Ctx Head n) (contextCode : ContextCode Head NoConversion n)
    {valid : Environment.{u} n → Prop}
    (contextChecked : checkContext R noConversionCheck context contextCode = true)
    (atContext : assembleContext heads constants contextCode context = some valid)
    (leftA rightA : Tm Head n) (leftB rightB body terminal : Tm Head (n + 1))
    (leftLevel rightLevel leftDomainLevel leftBodyLevel rightDomainLevel rightBodyLevel : Head)
    (leftFormation rightFormation leftDomainCode rightDomainCode : Code Head NoConversion n)
    (leftFormationBodyCode rightFormationBodyCode leftBodyCode rightBodyCode
      leftTerminal rightTerminal : Code Head NoConversion (n + 1))
    (leftFormed rightFormed : Meaning.{u} n)
    (leftBody rightBody : Meaning.{u} (n + 1))
    (leftDomain rightDomain : Value.{u} n)
    (leftFormationChecked : check R noConversionCheck context (.pi leftA leftB)
      (.head leftLevel) leftFormation = true)
    (rightFormationChecked : check R noConversionCheck context (.pi rightA rightB)
      (.head rightLevel) rightFormation = true)
    (leftBodyChecked : check R noConversionCheck (.snoc context leftA) body leftB
      leftBodyCode = true)
    (rightBodyChecked : check R noConversionCheck (.snoc context rightA) body rightB
      rightBodyCode = true)
    (leftExtract : leftFormation.piFormation = some
      (leftDomainLevel, leftBodyLevel, leftDomainCode, leftFormationBodyCode))
    (rightExtract : rightFormation.piFormation = some
      (rightDomainLevel, rightBodyLevel, rightDomainCode, rightFormationBodyCode))
    (leftPath : QualifiedBetaPath R successor
      (.snoc contextCode leftDomainLevel leftDomainCode) leftB body leftBodyCode
      terminal leftTerminal)
    (rightPath : QualifiedBetaPath R successor
      (.snoc contextCode rightDomainLevel rightDomainCode) rightB body rightBodyCode
      terminal rightTerminal)
    (atLeftFormation : assemble heads constants leftFormation (.pi leftA leftB)
      (.head leftLevel) = some leftFormed)
    (atRightFormation : assemble heads constants rightFormation (.pi rightA rightB)
      (.head rightLevel) = some rightFormed)
    (atLeftDomain : leftFormed.productDomain? = some leftDomain)
    (atRightDomain : rightFormed.productDomain? = some rightDomain)
    (atLeftBody : assemble heads constants leftBodyCode body leftB = some leftBody)
    (atRightBody : assemble heads constants rightBodyCode body rightB = some rightBody)
    (terminalSupported : ZFSetTypeExpressionInterpretation.supported terminal = true)
    (env : Environment.{u} n) (admitted : valid env)
    (x : ZFSet.{u}) (insideLeft : x ∈ leftDomain env)
    (insideRight : x ∈ rightDomain env) :
    leftBody.value (extend env x) = rightBody.value (extend env x) := by
  obtain ⟨lu, lv, ld, lb, leftFound, leftIsUniverse, _, leftDomainChecked, _⟩ :=
    leftFormation.piFormation_checked R noConversionCheck leftFormationChecked
  rw [leftExtract] at leftFound
  cases Option.some.inj leftFound
  obtain ⟨ru, rv, rd, rb, rightFound, rightIsUniverse, _, rightDomainChecked, _⟩ :=
    rightFormation.piFormation_checked R noConversionCheck rightFormationChecked
  rw [rightExtract] at rightFound
  cases Option.some.inj rightFound
  obtain ⟨leftDomainMeaning, _, atLeftDomainCode, _, _, leftDomainValue⟩ :=
    assemble_piFormation heads constants leftFormation leftExtract atLeftFormation
  obtain ⟨rightDomainMeaning, _, atRightDomainCode, _, _, rightDomainValue⟩ :=
    assemble_piFormation heads constants rightFormation rightExtract atRightFormation
  rw [atLeftDomain] at leftDomainValue
  rw [atRightDomain] at rightDomainValue
  have leftDomainEq : leftDomainMeaning.value = leftDomain := Option.some.inj leftDomainValue.symm
  have rightDomainEq : rightDomainMeaning.value = rightDomain := Option.some.inj rightDomainValue.symm
  let leftValid : Environment.{u} (n + 1) → Prop :=
    fun e => valid (e ∘ wk) ∧ e 0 ∈ leftDomain (e ∘ wk)
  let rightValid : Environment.{u} (n + 1) → Prop :=
    fun e => valid (e ∘ wk) ∧ e 0 ∈ rightDomain (e ∘ wk)
  have leftContextChecked : checkContext R noConversionCheck (.snoc context leftA)
      (.snoc contextCode leftDomainLevel leftDomainCode) = true := by
    simp only [checkContext, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨contextChecked, leftIsUniverse⟩, leftDomainChecked⟩
  have rightContextChecked : checkContext R noConversionCheck (.snoc context rightA)
      (.snoc contextCode rightDomainLevel rightDomainCode) = true := by
    simp only [checkContext, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨contextChecked, rightIsUniverse⟩, rightDomainChecked⟩
  have atLeftContext : assembleContext heads constants
      (.snoc contextCode leftDomainLevel leftDomainCode) (.snoc context leftA) =
      some leftValid := by
    simp [assembleContext, atContext, atLeftDomainCode, leftValid, leftDomainEq]
  have atRightContext : assembleContext heads constants
      (.snoc contextCode rightDomainLevel rightDomainCode) (.snoc context rightA) =
      some rightValid := by
    simp [assembleContext, atContext, atRightDomainCode, rightValid, rightDomainEq]
  exact qualified_paths_supported_terminal_values_across_contexts heads constants R
    successor universes successorQualified model constantModel
    (.snoc contextCode leftDomainLevel leftDomainCode)
    (.snoc contextCode rightDomainLevel rightDomainCode) leftPath rightPath
    leftContextChecked rightContextChecked leftBodyChecked rightBodyChecked
    atLeftContext atRightContext leftBody rightBody atLeftBody atRightBody
    terminalSupported (extend env x) ⟨admitted, insideLeft⟩ ⟨admitted, insideRight⟩

/-- Before either function is applied, its two accepted lambda certificates
already satisfy the domain-indexed observational relation. Their function
sets need not be equal: only applications at inputs in both retained domains
are compared. The body relation is derived from qualified checked paths. -/
theorem qualified_lambdas_observationally_related_of_body_paths
    (context : Ctx Head n) (contextCode : ContextCode Head NoConversion n)
    {valid : Environment.{u} n → Prop}
    (contextChecked : checkContext R noConversionCheck context contextCode = true)
    (atContext : assembleContext heads constants contextCode context = some valid)
    (leftA rightA : Tm Head n) (leftB rightB body terminal : Tm Head (n + 1))
    (leftLevel rightLevel leftDomainLevel leftBodyLevel rightDomainLevel rightBodyLevel : Head)
    (leftFormation rightFormation leftDomainCode rightDomainCode : Code Head NoConversion n)
    (leftFormationBodyCode rightFormationBodyCode leftBodyCode rightBodyCode
      leftTerminal rightTerminal : Code Head NoConversion (n + 1))
    (leftFormed rightFormed leftLambda rightLambda : Meaning.{u} n)
    (leftBody rightBody : Meaning.{u} (n + 1))
    (leftDomain rightDomain : Value.{u} n)
    (leftChecked : check R noConversionCheck context (.lam body) (.pi leftA leftB)
      (.lamIntro leftLevel leftFormation leftBodyCode) = true)
    (rightChecked : check R noConversionCheck context (.lam body) (.pi rightA rightB)
      (.lamIntro rightLevel rightFormation rightBodyCode) = true)
    (leftExtract : leftFormation.piFormation = some
      (leftDomainLevel, leftBodyLevel, leftDomainCode, leftFormationBodyCode))
    (rightExtract : rightFormation.piFormation = some
      (rightDomainLevel, rightBodyLevel, rightDomainCode, rightFormationBodyCode))
    (leftPath : QualifiedBetaPath R successor
      (.snoc contextCode leftDomainLevel leftDomainCode) leftB body leftBodyCode
      terminal leftTerminal)
    (rightPath : QualifiedBetaPath R successor
      (.snoc contextCode rightDomainLevel rightDomainCode) rightB body rightBodyCode
      terminal rightTerminal)
    (atLeftFormation : assemble heads constants leftFormation (.pi leftA leftB)
      (.head leftLevel) = some leftFormed)
    (atRightFormation : assemble heads constants rightFormation (.pi rightA rightB)
      (.head rightLevel) = some rightFormed)
    (atLeftDomain : leftFormed.productDomain? = some leftDomain)
    (atRightDomain : rightFormed.productDomain? = some rightDomain)
    (atLeftBody : assemble heads constants leftBodyCode body leftB = some leftBody)
    (atRightBody : assemble heads constants rightBodyCode body rightB = some rightBody)
    (atLeftLambda : assemble heads constants (.lamIntro leftLevel leftFormation leftBodyCode)
      (.lam body) (.pi leftA leftB) = some leftLambda)
    (atRightLambda : assemble heads constants (.lamIntro rightLevel rightFormation rightBodyCode)
      (.lam body) (.pi rightA rightB) = some rightLambda)
    (terminalSupported : ZFSetTypeExpressionInterpretation.supported terminal = true)
    (env : Environment.{u} n) (admitted : valid env) :
    TraceFunctionRelated (leftDomain env) (rightDomain env) Eq Eq
      (leftLambda.value env) (rightLambda.value env) := by
  have leftParts := leftChecked
  have rightParts := rightChecked
  simp only [check, Bool.and_eq_true, decide_eq_true_eq] at leftParts rightParts
  apply assembled_lambdas_related heads constants leftLevel rightLevel
    leftA rightA leftB rightB body body leftFormation rightFormation
    leftBodyCode rightBodyCode leftFormed rightFormed leftLambda rightLambda
    leftBody rightBody leftDomain rightDomain atLeftFormation atRightFormation
    atLeftDomain atRightDomain atLeftBody atRightBody atLeftLambda atRightLambda
    env env Eq Eq
  intro x insideLeft y insideRight equal
  subst y
  exact qualified_body_paths_agree_on_shared_admitted_input heads constants R
    successor universes successorQualified model constantModel context contextCode
    contextChecked atContext leftA rightA leftB rightB body terminal leftLevel
    rightLevel leftDomainLevel leftBodyLevel rightDomainLevel rightBodyLevel
    leftFormation rightFormation leftDomainCode rightDomainCode leftFormationBodyCode
    rightFormationBodyCode leftBodyCode rightBodyCode leftTerminal rightTerminal
    leftFormed rightFormed leftBody rightBody leftDomain rightDomain
    leftParts.1.2 rightParts.1.2 leftParts.2 rightParts.2
    leftExtract rightExtract leftPath rightPath atLeftFormation atRightFormation
    atLeftDomain atRightDomain atLeftBody atRightBody terminalSupported
    env admitted x insideLeft insideRight

/-- Two actual checked applications agree when both their computed arguments
and their certificate-dependent bodies have qualified paths to common
supported terminals. The body paths live in the distinct context extensions
selected by each accepted product formation. -/
theorem qualified_cross_domain_lambda_applications_coherent_of_body_paths
    (context : Ctx Head n) (contextCode : ContextCode Head NoConversion n)
    {valid : Environment.{u} n → Prop}
    (contextChecked : checkContext R noConversionCheck context contextCode = true)
    (atContext : assembleContext heads constants contextCode context = some valid)
    (leftA rightA : Tm Head n) (leftB rightB body : Tm Head (n + 1))
    (leftLevel rightLevel leftDomainLevel leftBodyLevel rightDomainLevel rightBodyLevel : Head)
    (leftFormation rightFormation leftArgumentCode rightArgumentCode
      leftDomainCode rightDomainCode : Code Head NoConversion n)
    (leftFormationBodyCode rightFormationBodyCode leftBodyCode rightBodyCode
      leftBodyTerminal rightBodyTerminal : Code Head NoConversion (n + 1))
    (leftArgument rightArgument argumentTerminal : Tm Head n)
    (leftArgumentTerminal rightArgumentTerminal : Code Head NoConversion n)
    (bodyTerminal : Tm Head (n + 1))
    (leftChecked : check R noConversionCheck context (.app (.lam body) leftArgument)
      (inst0 leftArgument leftB)
      (.appElim leftA leftB (.lamIntro leftLevel leftFormation leftBodyCode)
        leftArgumentCode) = true)
    (rightChecked : check R noConversionCheck context (.app (.lam body) rightArgument)
      (inst0 rightArgument rightB)
      (.appElim rightA rightB (.lamIntro rightLevel rightFormation rightBodyCode)
        rightArgumentCode) = true)
    (leftArgumentQualified : leftArgumentCode.resultFormationsNeutral R successor
      contextCode leftArgument leftA = true)
    (rightArgumentQualified : rightArgumentCode.resultFormationsNeutral R successor
      contextCode rightArgument rightA = true)
    (leftArgumentPath : QualifiedBetaPath R successor contextCode leftA
      leftArgument leftArgumentCode argumentTerminal leftArgumentTerminal)
    (rightArgumentPath : QualifiedBetaPath R successor contextCode rightA
      rightArgument rightArgumentCode argumentTerminal rightArgumentTerminal)
    (argumentTerminalSupported : ZFSetTypeExpressionInterpretation.supported
      argumentTerminal = true)
    (leftExtract : leftFormation.piFormation = some
      (leftDomainLevel, leftBodyLevel, leftDomainCode, leftFormationBodyCode))
    (rightExtract : rightFormation.piFormation = some
      (rightDomainLevel, rightBodyLevel, rightDomainCode, rightFormationBodyCode))
    (leftBodyPath : QualifiedBetaPath R successor
      (.snoc contextCode leftDomainLevel leftDomainCode) leftB body leftBodyCode
      bodyTerminal leftBodyTerminal)
    (rightBodyPath : QualifiedBetaPath R successor
      (.snoc contextCode rightDomainLevel rightDomainCode) rightB body rightBodyCode
      bodyTerminal rightBodyTerminal)
    (bodyTerminalSupported : ZFSetTypeExpressionInterpretation.supported
      bodyTerminal = true) :
    ∃ leftResult rightResult,
      assemble heads constants
        (.appElim leftA leftB (.lamIntro leftLevel leftFormation leftBodyCode)
          leftArgumentCode)
        (.app (.lam body) leftArgument) (inst0 leftArgument leftB) = some leftResult ∧
      assemble heads constants
        (.appElim rightA rightB (.lamIntro rightLevel rightFormation rightBodyCode)
          rightArgumentCode)
        (.app (.lam body) rightArgument) (inst0 rightArgument rightB) = some rightResult ∧
      ∀ env, valid env → leftResult.value env = rightResult.value env := by
  have leftParts := leftChecked
  have rightParts := rightChecked
  simp only [check, Bool.and_eq_true, decide_eq_true_eq] at leftParts rightParts
  have leftFormationChecked := leftParts.1.1.1.2
  have leftBodyChecked := leftParts.1.1.2
  have leftArgumentChecked := leftParts.1.2
  have rightFormationChecked := rightParts.1.1.1.2
  have rightBodyChecked := rightParts.1.1.2
  have rightArgumentChecked := rightParts.1.2
  obtain ⟨leftFormed, atLeftFormation, leftProduct⟩ :=
    accepted_assembles heads constants R noConversionCheck leftFormation leftFormationChecked
  obtain ⟨rightFormed, atRightFormation, rightProduct⟩ :=
    accepted_assembles heads constants R noConversionCheck rightFormation rightFormationChecked
  obtain ⟨leftDomain, atLeftDomain⟩ := leftProduct leftA leftB rfl
  obtain ⟨rightDomain, atRightDomain⟩ := rightProduct rightA rightB rfl
  obtain ⟨leftBody, atLeftBody, _⟩ :=
    accepted_assembles heads constants R noConversionCheck leftBodyCode leftBodyChecked
  obtain ⟨rightBody, atRightBody, _⟩ :=
    accepted_assembles heads constants R noConversionCheck rightBodyCode rightBodyChecked
  obtain ⟨leftArg, atLeftArgument, _⟩ :=
    accepted_assembles heads constants R noConversionCheck leftArgumentCode leftArgumentChecked
  obtain ⟨rightArg, atRightArgument, _⟩ :=
    accepted_assembles heads constants R noConversionCheck rightArgumentCode rightArgumentChecked
  obtain ⟨leftResult, atLeftResult, _⟩ := accepted_assembles heads constants R
    noConversionCheck (.appElim leftA leftB (.lamIntro leftLevel leftFormation leftBodyCode)
      leftArgumentCode) leftChecked
  obtain ⟨rightResult, atRightResult, _⟩ := accepted_assembles heads constants R
    noConversionCheck (.appElim rightA rightB (.lamIntro rightLevel rightFormation rightBodyCode)
      rightArgumentCode) rightChecked
  refine ⟨leftResult, rightResult, atLeftResult, atRightResult, ?_⟩
  intro env admitted
  apply qualified_lambda_applications_related_of_paths heads constants R successor
    universes successorQualified model constantModel context contextCode valid
    contextChecked atContext leftLevel rightLevel leftA rightA leftB rightB body body
    leftArgument rightArgument argumentTerminal leftFormation rightFormation
    leftArgumentCode rightArgumentCode leftArgumentTerminal rightArgumentTerminal
    leftBodyCode rightBodyCode leftFormed rightFormed leftArg rightArg leftResult
    rightResult leftBody rightBody leftDomain rightDomain leftFormationChecked
    rightFormationChecked leftArgumentChecked rightArgumentChecked
    leftArgumentQualified rightArgumentQualified leftArgumentPath rightArgumentPath
    argumentTerminalSupported atLeftFormation atRightFormation atLeftDomain
    atRightDomain atLeftBody atRightBody atLeftArgument atRightArgument
    atLeftResult atRightResult env admitted Eq
  intro x insideLeft y insideRight equal
  subst y
  exact qualified_body_paths_agree_on_shared_admitted_input heads constants R
    successor universes successorQualified model constantModel context contextCode
    contextChecked atContext leftA rightA leftB rightB body bodyTerminal leftLevel
    rightLevel leftDomainLevel leftBodyLevel rightDomainLevel rightBodyLevel
    leftFormation rightFormation leftDomainCode rightDomainCode leftFormationBodyCode
    rightFormationBodyCode leftBodyCode rightBodyCode leftBodyTerminal
    rightBodyTerminal leftFormed rightFormed leftBody rightBody leftDomain rightDomain
    leftFormationChecked rightFormationChecked leftBodyChecked rightBodyChecked
    leftExtract rightExtract leftBodyPath rightBodyPath atLeftFormation
    atRightFormation atLeftDomain atRightDomain atLeftBody atRightBody
    bodyTerminalSupported env admitted x insideLeft insideRight

#print axioms qualified_body_paths_agree_on_shared_admitted_input
#print axioms qualified_lambdas_observationally_related_of_body_paths
#print axioms qualified_cross_domain_lambda_applications_coherent_of_body_paths

end ZFSetReplayInterpretation
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
