import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.StructuralTypingReplayVariableReduction
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayVariableMembership
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayContextComparison

/-!
# Membership and comparison of computed variable arguments

A finite `BetaToVariable` computation establishes the meaning of its actual
source certificate on valid context environments. Each argument's membership
is derived recursively from its own computation and the checked terminal
variable; no semantic soundness premise is attached to the trace.

Membership in an independently checked, qualified result formation follows.
Comparison also allows different displayed types and intermediate domains.
The scope is the recorded beta computations with qualified retained domains,
not arbitrary checked programs or a general normalization result.
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


variable (headsMonotone : ∀ a b, R.cumulative a b → heads a ⊆ heads b)

include headsMonotone

/-- Interpretation of every recorded contraction, including recursively
computed arguments, agrees with the returned context value on valid inputs.
Neither global certificate coherence nor argument membership is assumed. -/
theorem BetaToVariable.value
    {subject type : Tm Head n} {source terminal : Code Head NoConversion n} {index : Fin n}
    (trace : StructuralTypingReplay.BetaToVariable subject type source index terminal)
    (contextCode : ContextCode Head NoConversion n)
    {context : Ctx Head n} {valid : Environment.{u} n → Prop}
    (contextChecked : checkContext R noConversionCheck context contextCode = true)
    (sourceChecked : check R noConversionCheck context subject type source = true)
    (atContext : assembleContext heads constants contextCode context = some valid)
    (meaning : Meaning.{u} n)
    (atSource : assemble heads constants source subject type = some meaning)
    (env : Environment.{u} n) (admitted : valid env) : meaning.value env = env index := by
  induction trace generalizing meaning with
  | var =>
      exact agrees_with_type_expressions heads constants _ _ _ meaning rfl atSource env
  | cumulative prior ih =>
      simp only [check, Bool.and_eq_true] at sourceChecked
      exact ih sourceChecked.1 meaning atSource
  | @beta A argument B body level domainLevel bodyLevel formation domainCode argumentCode
      argumentTerminal terminal codomainCode bodyCode argumentIndex index parts qualified
      argumentTrace reductTrace ihArgument ihReduct =>
      have premises := sourceChecked
      simp only [check, Bool.and_eq_true] at premises
      have argumentChecked := premises.1.2
      have formationChecked := premises.1.1.1.2
      obtain ⟨actualDomainLevel, actualBodyLevel, actualDomainCode, actualBodyCode, computed,
        _, _, domainChecked, _⟩ := formation.piFormation_checked R noConversionCheck formationChecked
      rw [parts] at computed
      cases Option.some.inj computed
      obtain ⟨arg, atArgument, _⟩ :=
        accepted_assembles heads constants R noConversionCheck argumentCode argumentChecked
      obtain ⟨domain, atDomain, _⟩ :=
        accepted_assembles heads constants R noConversionCheck domainCode domainChecked
      have terminalChecked := argumentTrace.terminal_checked R argumentChecked
      obtain ⟨terminalMeaning, atTerminal, _⟩ :=
        accepted_assembles heads constants R noConversionCheck argumentTerminal terminalChecked
      have terminalMember := variable_membership heads constants R headsMonotone
        contextCode argumentTerminal domainCode terminalMeaning domain contextChecked
        terminalChecked domainChecked qualified atContext atTerminal atDomain env admitted
      have terminalValue := agrees_with_type_expressions heads constants argumentTerminal
        (.var argumentIndex) A terminalMeaning rfl atTerminal env
      change terminalMeaning.value env = env argumentIndex at terminalValue
      have argumentMember : arg.value env ∈ domain.value env := by
        rw [ihArgument argumentChecked arg atArgument, ← terminalValue]
        exact terminalMember
      have rootAdmitted := rootBeta_argument_admitted heads constants R sourceChecked
        parts arg domain atArgument atDomain env argumentMember
      obtain ⟨result, atResult, equal⟩ := contractBeta_value heads constants R _ meaning
        sourceChecked atSource rfl env rootAdmitted
      have resultChecked := Code.contractBeta_result_checked R _ _ sourceChecked rfl
      exact equal.trans (ihReduct resultChecked result atResult)

/-- Membership is transported back from the actual checked terminal
variable, into an independently checked formation of the displayed type. -/
theorem BetaToVariable.membership
    {subject type : Tm Head n} {source terminal : Code Head NoConversion n} {index : Fin n}
    (trace : StructuralTypingReplay.BetaToVariable subject type source index terminal)
    (contextCode : ContextCode Head NoConversion n)
    {context : Ctx Head n} {valid : Environment.{u} n → Prop}
    (formation : Code Head NoConversion n) (level : Head)
    (contextChecked : checkContext R noConversionCheck context contextCode = true)
    (sourceChecked : check R noConversionCheck context subject type source = true)
    (formationChecked : check R noConversionCheck context type (.head level) formation = true)
    (qualified : formation.neutralEliminations type (.head level) = true)
    (atContext : assembleContext heads constants contextCode context = some valid)
    (meaning typeMeaning : Meaning.{u} n)
    (atSource : assemble heads constants source subject type = some meaning)
    (atFormation : assemble heads constants formation type (.head level) = some typeMeaning)
    (env : Environment.{u} n) (admitted : valid env) :
    meaning.value env ∈ typeMeaning.value env := by
  have terminalChecked := trace.terminal_checked R sourceChecked
  obtain ⟨terminalMeaning, atTerminal, _⟩ :=
    accepted_assembles heads constants R noConversionCheck terminal terminalChecked
  have member := variable_membership heads constants R headsMonotone contextCode terminal
    formation terminalMeaning typeMeaning contextChecked terminalChecked formationChecked
    qualified atContext atTerminal atFormation env admitted
  have terminalValue := agrees_with_type_expressions heads constants terminal (.var index) type
    terminalMeaning rfl atTerminal env
  change terminalMeaning.value env = env index at terminalValue
  rw [BetaToVariable.value heads constants R headsMonotone trace contextCode contextChecked
    sourceChecked atContext meaning atSource env admitted, ← terminalValue]
  exact member

/-- Independent computations returning the same variable agree on valid
environments, even if their displayed types and intermediate domains differ. -/
theorem BetaToVariable.values_agree
    {leftSubject leftType rightSubject rightType : Tm Head n}
    {leftCode leftTerminal rightCode rightTerminal : Code Head NoConversion n} {index : Fin n}
    (leftTrace : StructuralTypingReplay.BetaToVariable leftSubject leftType leftCode index leftTerminal)
    (rightTrace : StructuralTypingReplay.BetaToVariable rightSubject rightType rightCode index rightTerminal)
    (contextCode : ContextCode Head NoConversion n)
    {context : Ctx Head n} {valid : Environment.{u} n → Prop}
    (contextChecked : checkContext R noConversionCheck context contextCode = true)
    (leftChecked : check R noConversionCheck context leftSubject leftType leftCode = true)
    (rightChecked : check R noConversionCheck context rightSubject rightType rightCode = true)
    (atContext : assembleContext heads constants contextCode context = some valid)
    (left right : Meaning.{u} n)
    (atLeft : assemble heads constants leftCode leftSubject leftType = some left)
    (atRight : assemble heads constants rightCode rightSubject rightType = some right)
    (env : Environment.{u} n) (admitted : valid env) : left.value env = right.value env :=
  (BetaToVariable.value heads constants R headsMonotone leftTrace contextCode contextChecked
    leftChecked atContext left atLeft env admitted).trans
      (BetaToVariable.value heads constants R headsMonotone rightTrace contextCode contextChecked
        rightChecked atContext right atRight env admitted).symm

/-- Any checked dependent family can be instantiated at the computed source
or at its checked terminal variable. Both exact generated certificates check,
and their set values agree on valid environments. No qualification of the
family or its instantiated syntax is required: the same retained family
certificate is used on both sides. This is semantic equality, not acceptance
of a new conversion rule between the two raw types. -/
theorem BetaToVariable.family_values
    {argument A : Tm Head n} {source terminal : Code Head NoConversion n} {index : Fin n}
    (trace : StructuralTypingReplay.BetaToVariable argument A source index terminal)
    (contextCode : ContextCode Head NoConversion n)
    {context : Ctx Head n} {valid : Environment.{u} n → Prop}
    (contextChecked : checkContext R noConversionCheck context contextCode = true)
    (sourceChecked : check R noConversionCheck context argument A source = true)
    (atContext : assembleContext heads constants contextCode context = some valid)
    (family : Tm Head (n + 1)) (level : Head)
    (familyCode : Code Head NoConversion (n + 1))
    (familyChecked : check R noConversionCheck (.snoc context A) family (.head level) familyCode = true) :
    let sourceFormation := Code.instantiate noConversionRename noConversionSubstitute
      family (.head level) argument familyCode source
    let terminalFormation := Code.instantiate noConversionRename noConversionSubstitute
      family (.head level) (.var index) familyCode terminal
    check R noConversionCheck context (inst0 argument family) (.head level) sourceFormation = true ∧
      check R noConversionCheck context (inst0 (.var index) family) (.head level) terminalFormation = true ∧
      ∃ left right,
        assemble heads constants sourceFormation (inst0 argument family) (.head level) = some left ∧
        assemble heads constants terminalFormation (inst0 (.var index) family) (.head level) = some right ∧
        ∀ env, valid env → left.value env = right.value env := by
  dsimp only
  have terminalChecked := trace.terminal_checked R sourceChecked
  have sourceFormationChecked := Code.instantiate_checked noConversionRename noConversionSubstitute
    R noConversionCheck (fun _ impossible => nomatch impossible)
    (fun _ impossible => nomatch impossible) familyChecked sourceChecked
  have terminalFormationChecked := Code.instantiate_checked noConversionRename noConversionSubstitute
    R noConversionCheck (fun _ impossible => nomatch impossible)
    (fun _ impossible => nomatch impossible) familyChecked terminalChecked
  obtain ⟨arg, atArg, _⟩ :=
    accepted_assembles heads constants R noConversionCheck source sourceChecked
  obtain ⟨terminalMeaning, atTerminal, _⟩ :=
    accepted_assembles heads constants R noConversionCheck terminal terminalChecked
  obtain ⟨familyMeaning, atFamily, _⟩ :=
    accepted_assembles heads constants R noConversionCheck familyCode familyChecked
  obtain ⟨left, atLeft, leftValues⟩ := assemble_instantiate noConversionRename noConversionSubstitute
    heads constants R noConversionCheck familyCode source familyMeaning arg familyChecked atFamily atArg
  obtain ⟨right, atRight, rightValues⟩ := assemble_instantiate noConversionRename noConversionSubstitute
    heads constants R noConversionCheck familyCode terminal familyMeaning terminalMeaning
      familyChecked atFamily atTerminal
  refine ⟨sourceFormationChecked, terminalFormationChecked, left, right, atLeft, atRight, ?_⟩
  intro env admitted
  have terminalValue := agrees_with_type_expressions heads constants terminal (.var index) A
    terminalMeaning rfl atTerminal env
  change terminalMeaning.value env = env index at terminalValue
  rw [leftValues, rightValues,
    BetaToVariable.value heads constants R headsMonotone trace contextCode contextChecked
      sourceChecked atContext arg atArg env admitted, terminalValue]

/-- Independently supplied family certificates and argument computations
remain comparable after actual dependent instantiation. Qualification is
required of the first original family, not of either instantiated family.
The argument certificates and terminal certificates need not be equal. -/
theorem BetaToVariable.independent_family_values
    {leftArgument rightArgument A : Tm Head n}
    {leftCode rightCode leftTerminal rightTerminal : Code Head NoConversion n} {index : Fin n}
    (leftTrace : StructuralTypingReplay.BetaToVariable leftArgument A leftCode index leftTerminal)
    (rightTrace : StructuralTypingReplay.BetaToVariable rightArgument A rightCode index rightTerminal)
    (contextCode : ContextCode Head NoConversion n)
    {context : Ctx Head n} {valid : Environment.{u} n → Prop}
    (contextChecked : checkContext R noConversionCheck context contextCode = true)
    (leftChecked : check R noConversionCheck context leftArgument A leftCode = true)
    (rightChecked : check R noConversionCheck context rightArgument A rightCode = true)
    (atContext : assembleContext heads constants contextCode context = some valid)
    (family : Tm Head (n + 1)) (leftLevel rightLevel : Head)
    (leftFamily rightFamily : Code Head NoConversion (n + 1))
    (leftFamilyChecked : check R noConversionCheck (.snoc context A)
      family (.head leftLevel) leftFamily = true)
    (rightFamilyChecked : check R noConversionCheck (.snoc context A)
      family (.head rightLevel) rightFamily = true)
    (qualified : leftFamily.neutralEliminations family (.head leftLevel) = true) :
    let leftFormation := Code.instantiate noConversionRename noConversionSubstitute
      family (.head leftLevel) leftArgument leftFamily leftCode
    let rightFormation := Code.instantiate noConversionRename noConversionSubstitute
      family (.head rightLevel) rightArgument rightFamily rightCode
    check R noConversionCheck context (inst0 leftArgument family) (.head leftLevel) leftFormation = true ∧
      check R noConversionCheck context (inst0 rightArgument family) (.head rightLevel) rightFormation = true ∧
      ∃ left right,
        assemble heads constants leftFormation (inst0 leftArgument family) (.head leftLevel) = some left ∧
        assemble heads constants rightFormation (inst0 rightArgument family) (.head rightLevel) = some right ∧
        ∀ env, valid env → left.value env = right.value env := by
  dsimp only
  have leftResultChecked := Code.instantiate_checked noConversionRename noConversionSubstitute
    R noConversionCheck (fun _ impossible => nomatch impossible)
    (fun _ impossible => nomatch impossible) leftFamilyChecked leftChecked
  have rightResultChecked := Code.instantiate_checked noConversionRename noConversionSubstitute
    R noConversionCheck (fun _ impossible => nomatch impossible)
    (fun _ impossible => nomatch impossible) rightFamilyChecked rightChecked
  obtain ⟨leftArg, atLeftArg, _⟩ :=
    accepted_assembles heads constants R noConversionCheck leftCode leftChecked
  obtain ⟨rightArg, atRightArg, _⟩ :=
    accepted_assembles heads constants R noConversionCheck rightCode rightChecked
  obtain ⟨leftFamilyMeaning, atLeftFamily, _⟩ :=
    accepted_assembles heads constants R noConversionCheck leftFamily leftFamilyChecked
  obtain ⟨rightFamilyMeaning, atRightFamily, _⟩ :=
    accepted_assembles heads constants R noConversionCheck rightFamily rightFamilyChecked
  have familyAgreement := assemble_neutralEliminations_coherent heads constants R leftFamily
    leftFamilyChecked qualified atLeftFamily rightFamilyChecked atRightFamily (EqualOrHeads.heads _ _)
  obtain ⟨left, atLeft, leftValues⟩ := assemble_instantiate noConversionRename noConversionSubstitute
    heads constants R noConversionCheck leftFamily leftCode leftFamilyMeaning leftArg
      leftFamilyChecked atLeftFamily atLeftArg
  obtain ⟨right, atRight, rightValues⟩ := assemble_instantiate noConversionRename noConversionSubstitute
    heads constants R noConversionCheck rightFamily rightCode rightFamilyMeaning rightArg
      rightFamilyChecked atRightFamily atRightArg
  refine ⟨leftResultChecked, rightResultChecked, left, right, atLeft, atRight, ?_⟩
  intro env admitted
  rw [leftValues, rightValues, familyAgreement,
    BetaToVariable.values_agree heads constants R headsMonotone leftTrace rightTrace
      contextCode contextChecked leftChecked rightChecked atContext leftArg rightArg
      atLeftArg atRightArg env admitted]

/-- The two dependent family instances extend the context to exactly the
same set of environments. Both raw telescopes are checked with their actual
generated formation certificates, although their last types may differ
syntactically. No context-conversion rule is added to the checker. -/
theorem BetaToVariable.family_contexts
    {argument A : Tm Head n} {source terminal : Code Head NoConversion n} {index : Fin n}
    (trace : StructuralTypingReplay.BetaToVariable argument A source index terminal)
    (contextCode : ContextCode Head NoConversion n)
    {context : Ctx Head n} {valid : Environment.{u} n → Prop}
    (contextChecked : checkContext R noConversionCheck context contextCode = true)
    (sourceChecked : check R noConversionCheck context argument A source = true)
    (atContext : assembleContext heads constants contextCode context = some valid)
    (family : Tm Head (n + 1)) (level : Head) (levelUniverse : R.isUniverse level)
    (familyCode : Code Head NoConversion (n + 1))
    (familyChecked : check R noConversionCheck (.snoc context A) family (.head level) familyCode = true) :
    let leftFormation := Code.instantiate noConversionRename noConversionSubstitute
      family (.head level) argument familyCode source
    let rightFormation := Code.instantiate noConversionRename noConversionSubstitute
      family (.head level) (.var index) familyCode terminal
    checkContext R noConversionCheck (.snoc context (inst0 argument family))
      (.snoc contextCode level leftFormation) = true ∧
      checkContext R noConversionCheck (.snoc context (inst0 (.var index) family))
        (.snoc contextCode level rightFormation) = true ∧
      ∃ leftValid rightValid,
        assembleContext heads constants (.snoc contextCode level leftFormation)
          (.snoc context (inst0 argument family)) = some leftValid ∧
        assembleContext heads constants (.snoc contextCode level rightFormation)
          (.snoc context (inst0 (.var index) family)) = some rightValid ∧
        leftValid = rightValid := by
  dsimp only
  obtain ⟨leftChecked, rightChecked, left, right, atLeft, atRight, equal⟩ :=
    BetaToVariable.family_values heads constants R headsMonotone trace contextCode contextChecked
      sourceChecked atContext family level familyCode familyChecked
  refine ⟨?_, ?_,
    (fun env => valid (env ∘ wk) ∧ env 0 ∈ left.value (env ∘ wk)),
    (fun env => valid (env ∘ wk) ∧ env 0 ∈ right.value (env ∘ wk)), ?_, ?_, ?_⟩
  · simpa only [checkContext, Bool.and_eq_true, decide_eq_true_eq] using
      And.intro (And.intro contextChecked levelUniverse) leftChecked
  · simpa only [checkContext, Bool.and_eq_true, decide_eq_true_eq] using
      And.intro (And.intro contextChecked levelUniverse) rightChecked
  · simp only [assembleContext, atContext, atLeft, Option.bind_eq_bind, Option.bind_some,
      Option.pure_def]
  · simp only [assembleContext, atContext, atRight, Option.bind_eq_bind, Option.bind_some,
      Option.pure_def]
  · apply assembleContext_extensions_eq heads constants context context
      (inst0 argument family) (inst0 (.var index) family) contextCode contextCode level level
      _ _ valid valid left right _ _ atContext atContext atLeft atRight
    · simp only [assembleContext, atContext, atLeft, Option.bind_eq_bind, Option.bind_some,
        Option.pure_def]
    · simp only [assembleContext, atContext, atRight, Option.bind_eq_bind, Option.bind_some,
        Option.pure_def]
    · exact fun _ => Iff.rfl
    · exact equal

#print axioms rootBeta_argument_admitted
#print axioms BetaToVariable.value
#print axioms BetaToVariable.membership
#print axioms BetaToVariable.values_agree
#print axioms BetaToVariable.family_values
#print axioms BetaToVariable.independent_family_values
#print axioms BetaToVariable.family_contexts

end ZFSetReplayInterpretation
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
