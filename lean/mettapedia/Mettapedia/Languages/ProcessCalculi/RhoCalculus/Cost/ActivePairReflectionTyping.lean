import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivePairContextualReflection
import Mettapedia.GSLT.LanguageDef.ReflectiveInstantiationTyping
import Mettapedia.GSLT.LanguageDef.ContextSupport
import Mettapedia.OSLF.MeTTaIL.ScopedReflectiveExecution

/-!
# Typed name admission for finite synchronous Cost reflection

The actual generated signature has two name constructors, the base and wrapped
quotations. The existing full reflection profile seals both. Their declared
grammar discharges the operational atomic-name check; validation alone is not
used to assert completeness of a name grammar.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Synchronous.ActivePairReflectionTyping

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.ReflectiveWellSorted
open Mettapedia.GSLT.LanguageDef.ReflectiveInstantiationTyping
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.OSLF.MeTTaIL.ReflectiveInstantiation
open Mettapedia.OSLF.MeTTaIL.RuleBinding
open Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching
open ActivePairContextualReflection (declaration operation)

abbrev language := ActivePair.language
abbrev profile := ActivePair.presentation.reflection.1

def baseQuote : GrammarRule := communicationDecoration.baseConstructor rhoCalc.terms[2]
def wrappedQuote : GrammarRule := costWrappedConstructor (theory := rhoSyncIGSLT) rhoCalc.terms[2]

/-- This is the complete computed name-constructor row of the actual finite
signature, including both quotation colors. -/
theorem name_constructor_rows :
    language.terms.filter (fun rule => rule.category == costBaseSortName "Name") =
      [baseQuote, wrappedQuote] := by decide +kernel

theorem name_constructor_cases {rule : GrammarRule}
    (member : rule ∈ language.terms) (category : rule.category = costBaseSortName "Name") :
    rule = baseQuote ∨ rule = wrappedQuote := by
  have filtered : rule ∈ language.terms.filter
      (fun candidate => candidate.category == costBaseSortName "Name") :=
    List.mem_filter.mpr ⟨member, by simp [category]⟩
  rw [name_constructor_rows] at filtered
  simpa only [List.mem_cons, List.not_mem_nil, or_false] using filtered

theorem name_constructor_quoted {rule : GrammarRule}
    (member : rule ∈ language.terms) (category : rule.category = costBaseSortName "Name") :
    ReflectiveContextSupport.isQuoteConstructor profile rule.label = true := by
  rcases name_constructor_cases member category with rfl | rfl <;> decide +kernel

/-- Every admitted object name in the generated language is an atomic
variable or a sealed quoted term, for the selected wrapped operation. -/
theorem typed_name_atomicOrClosed
    {free : FreeTypeContext} {bound : List TypeExpr} {name : Pattern}
    (typed : HasSort language free bound name (costBaseSortName "Name"))
    (object : isObjectPattern name = true)
    (sealed : ReflectiveScopeSafeAt profile bound.length name) :
    atomicOrClosed declaration name = true := by
  change HasType language free bound name (.base (costBaseSortName "Name")) at typed
  generalize resultEq : TypeExpr.base (costBaseSortName "Name") = result at typed
  cases typed with
  | bvar lookup => rfl
  | fvar lookup => rfl
  | @constructor bound rule arguments member notBare argumentsTyped =>
      have category : rule.category = costBaseSortName "Name" := (TypeExpr.base.inj resultEq).symm
      have closedArguments := isWellScopedListAt_zero_of_typed_quote
        ActivePair.language_valid ActivePair.presentation.reflection.2
        member argumentsTyped (name_constructor_quoted member category) sealed
      exact atomicOrClosed_of_closed closedArguments
  | lambda _ => cases resultEq
  | multiLambda _ => cases resultEq
  | subst _ _ => simp [isObjectPattern] at object
  | collection _ => cases resultEq
  | @collectionConstructor bound rule parameter kind elements rest elementType member parameters elementsTyped =>
      have category : rule.category = costBaseSortName "Name" := (TypeExpr.base.inj resultEq).symm
      rcases name_constructor_cases member category with rfl | rfl
      · have actual : baseQuote.params = [.simple "p" (.base (costBaseSortName "Proc"))] := by decide +kernel
        rw [actual] at parameters
        simp at parameters
      · have actual : wrappedQuote.params = [.simple "p" (.base costWrappedSortName)] := by decide +kernel
        rw [actual] at parameters
        simp at parameters

/-- Reflection admission supplies the same unique quote/drop witness used by
the generic sorting theorem. It does not assert a preservation theorem. -/
theorem selected_witness :
    Nonempty (LanguageDef.ReflectivePresentationWitness language declaration) :=
  LanguageDef.reflectivePresentationWitness_of_validate_eq_nil _ _ (by decide +kernel)

/-- The full profile's safety descends to typed constructor arguments. A
quotation gives the stronger depth-zero judgment, which can be weakened. -/
theorem constructor_argument_scopes
    {free : FreeTypeContext} {bound : List TypeExpr}
    {rule : GrammarRule} {arguments : List Pattern}
    (member : rule ∈ language.terms)
    (typed : ArgumentsHaveTypes language free bound arguments rule.params)
    (sealed : ReflectiveScopeSafeAt profile bound.length (.apply rule.label arguments)) :
    ∀ presentation ∈ profile.presentations,
      binderSafeListAt presentation.quoteConstructor bound.length arguments = true := by
  by_cases quoted : ReflectiveContextSupport.isQuoteConstructor profile rule.label = true
  · have zero := reflectiveScopeSafeListAt_zero_of_typed_quote
      ActivePair.language_valid ActivePair.presentation.reflection.2 member typed quoted sealed
    intro presentation membership
    rw [binderSafeListAt_eq_true_iff] at ⊢
    intro argument argumentMember
    exact binderSafeAt_mono _
      ((binderSafeListAt_eq_true_iff _ _ _).mp (zero presentation membership) argument argumentMember)
      (Nat.zero_le _)
  · exact reflectiveScopeSafeListAt_of_nonquote (Bool.eq_false_iff.mpr quoted) sealed

mutual
  /-- The operational name-form premise follows from actual finite Cost
  typing, object syntax, and sealing for both authored quotation colors. -/
  theorem typed_namesAdmitted
      {free : FreeTypeContext} {bound : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
      (typed : HasType language free bound pattern type)
      (object : isObjectPattern pattern = true)
      (sealed : ReflectiveScopeSafeAt profile bound.length pattern) :
      namesAdmitted declaration pattern = true := by
    cases typed with
    | bvar _ => rfl
    | fvar _ => rfl
    | @constructor bound rule arguments member notBare argumentsTyped =>
        have argumentScopes := constructor_argument_scopes member argumentsTyped sealed
        have argumentNames := typed_arguments_namesAdmitted argumentsTyped object argumentScopes
        cases arguments with
        | nil => rfl
        | cons first rest =>
            cases rest with
            | nil =>
                by_cases quoted : rule.label = declaration.quoteConstructor
                · simp [namesAdmitted, quoted]
                · by_cases dropped : rule.label = declaration.dropConstructor
                  · obtain ⟨witness⟩ := selected_witness
                    have dropTyped : HasType language free bound
                        (.apply declaration.dropConstructor [first]) (.base rule.category) := by
                      simpa only [dropped] using HasType.constructor member notBare argumentsTyped
                    have nameTyped := (ReflectiveNormalizationTyping.drop_inv witness dropTyped).2
                    have firstObject : isObjectPattern first = true := by
                      simpa only [isObjectPattern, isObjectPatternList, Bool.and_true] using object
                    have firstScope : ReflectiveScopeSafeAt profile bound.length first := by
                      intro presentation membership
                      simpa only [binderSafeListAt, Bool.and_true] using argumentScopes presentation membership
                    have admitted := typed_name_atomicOrClosed nameTyped firstObject firstScope
                    simpa only [namesAdmitted, beq_iff_eq, if_neg quoted, if_pos dropped] using admitted
                  · simpa only [namesAdmitted, beq_iff_eq, if_neg quoted, if_neg dropped,
                      namesAdmittedList, Bool.and_true] using argumentNames
            | cons second more => exact argumentNames
    | lambda bodyTyped =>
        apply typed_namesAdmitted bodyTyped object
        intro presentation membership
        simpa [binderSafeAt, List.length_cons, Nat.add_comm] using sealed presentation membership
    | multiLambda bodyTyped =>
        apply typed_namesAdmitted bodyTyped object
        intro presentation membership
        simpa [binderSafeAt, List.length_append, List.length_replicate, Nat.add_comm] using
          sealed presentation membership
    | subst _ _ => simp [isObjectPattern] at object
    | collection elementsTyped =>
        have objects := (show _ ∧ _ from Bool.and_eq_true_iff.mp object).2
        exact typed_elements_namesAdmitted elementsTyped objects sealed
    | collectionConstructor _ _ elementsTyped =>
        have objects := (show _ ∧ _ from Bool.and_eq_true_iff.mp object).2
        exact typed_elements_namesAdmitted elementsTyped objects sealed

  theorem typed_arguments_namesAdmitted
      {free : FreeTypeContext} {bound : List TypeExpr}
      {patterns : List Pattern} {parameters : List TermParam}
      (typed : ArgumentsHaveTypes language free bound patterns parameters)
      (object : isObjectPatternList patterns = true)
      (sealed : ∀ presentation ∈ profile.presentations,
        binderSafeListAt presentation.quoteConstructor bound.length patterns = true) :
      namesAdmittedList declaration patterns = true := by
    cases typed with
    | nil => rfl
    | cons _ _ headTyped tailTyped =>
        simp only [isObjectPatternList, Bool.and_eq_true] at object
        simp only [namesAdmittedList, Bool.and_eq_true]
        constructor
        · apply typed_namesAdmitted headTyped object.1
          intro presentation membership
          have pair := sealed presentation membership
          simp only [binderSafeListAt, Bool.and_eq_true] at pair
          exact pair.1
        · apply typed_arguments_namesAdmitted tailTyped object.2
          intro presentation membership
          have pair := sealed presentation membership
          simp only [binderSafeListAt, Bool.and_eq_true] at pair
          exact pair.2

  theorem typed_elements_namesAdmitted
      {free : FreeTypeContext} {bound : List TypeExpr}
      {patterns : List Pattern} {type : TypeExpr}
      (typed : ElementsHaveType language free bound patterns type)
      (object : isObjectPatternList patterns = true)
      (sealed : ∀ presentation ∈ profile.presentations,
        binderSafeListAt presentation.quoteConstructor bound.length patterns = true) :
      namesAdmittedList declaration patterns = true := by
    cases typed with
    | nil => rfl
    | cons headTyped tailTyped =>
        simp only [isObjectPatternList, Bool.and_eq_true] at object
        simp only [namesAdmittedList, Bool.and_eq_true]
        constructor
        · apply typed_namesAdmitted headTyped object.1
          intro presentation membership
          have pair := sealed presentation membership
          simp only [binderSafeListAt, Bool.and_eq_true] at pair
          exact pair.1
        · apply typed_elements_namesAdmitted tailTyped object.2
          intro presentation membership
          have pair := sealed presentation membership
          simp only [binderSafeListAt, Bool.and_eq_true] at pair
          exact pair.2
end

/-- Arbitrary ambient-context activation is sorted in the actual finite Cost
language. Name-form admission is derived above from its declared constructors.
The conclusion is ordinary typing, without asserting literal-quote sealing. -/
theorem operation_hasType
    {free : FreeTypeContext} {bound : List TypeExpr} {body payload : Pattern}
    (bodyTyped : HasSort language free (.base (costBaseSortName "Name") :: bound)
      body costWrappedSortName)
    (bodyObject : isObjectPattern body = true)
    (bodySealed : ReflectiveScopeSafeAt profile
      (.base (costBaseSortName "Name") :: bound).length body)
    (payloadTyped : HasSort language free bound payload costWrappedSortName) :
    HasSort language free bound
      (operation (.apply (costWrappedConstructorName "NQuote") [payload]) body)
      costWrappedSortName := by
  obtain ⟨witness⟩ := selected_witness
  have normalizedPayload := ReflectiveNormalizationTyping.normalizeReflective_hasType witness payloadTyped
  have replacementTyped : HasSort language free bound
      (normalizeReflectiveReplacement declaration
        (.apply (costWrappedConstructorName "NQuote") [payload])) declaration.nameSort := by
    have quoted := quote_hasType witness normalizedPayload
    simpa only [normalizeReflectiveReplacement,
      show costWrappedConstructorName "NQuote" = declaration.quoteConstructor from rfl,
      beq_self_eq_true, if_true] using quoted
  exact instantiate_hasType witness (binders := []) bodyTyped
    (bodySealed declaration (by decide +kernel))
    (typed_namesAdmitted bodyTyped bodyObject bodySealed) replacementTyped

def residual (body payload after tail : Pattern) : Pattern :=
  .apply costContactConstructorName
    [.collection .hashBag
      [operation (.apply (costWrappedConstructorName "NQuote") [payload]) body, after] none,
     .apply costFundingConstructorName [tail]]

theorem residual_hasType
    {free : FreeTypeContext} {bound : List TypeExpr} {body payload after tail : Pattern}
    (bodyTyped : HasSort language free (.base (costBaseSortName "Name") :: bound)
      body costWrappedSortName)
    (bodyObject : isObjectPattern body = true)
    (bodySealed : ReflectiveScopeSafeAt profile
      (.base (costBaseSortName "Name") :: bound).length body)
    (payloadTyped : HasSort language free bound payload costWrappedSortName)
    (afterTyped : HasSort language free bound after costWrappedSortName)
    (tailTyped : HasSort language free bound tail costTokenStackSortName) :
    HasSort language free bound (residual body payload after tail) costWrappedSortName := by
  apply CostApparatus.contact_hasType (by decide +kernel)
  · apply HasType.collectionConstructor
      (rule := costWrappedConstructor (theory := rhoSyncIGSLT) rhoCalc.terms[3])
      (parameterName := "ps") (elementType := .base costWrappedSortName)
    · decide +kernel
    · rfl
    · exact .cons (operation_hasType bodyTyped bodyObject bodySealed payloadTyped)
        (.cons afterTyped (.nil _ _))
  · exact CostApparatus.funding_hasType (by decide +kernel) tailTyped

/-- The exact authored RHS instantiates the retained contextual assignment,
then applies the selected reflective binder operation to its substitution. -/
theorem reduct_pair (ambient : List TypeExpr)
    (channel body sent after signature tail : Pattern)
    (bodyScoped : body.isWellScopedAt (1 + ambient.length) = true)
    (sentScoped : sent.isWellScopedAt ambient.length = true)
    (afterScoped : after.isWellScopedAt ambient.length = true)
    (tailScoped : tail.isWellScopedAt ambient.length = true) :
    reductWith? operation ActivePair.rule ActivePair.bindingSpec ambient.length
      (ActivePair.pairAssignment ambient channel body sent after signature tail) =
      some (residual body sent after tail) := by
  have bodyRecovery : recoverValue? [.base (costBaseSortName "Name")]
      ambient.length 1 [.bvar 0] body =
      some ⟨[.base (costBaseSortName "Name")], ambient.length, body⟩ :=
    RestAwareTyping.recoverValue?_fullSpine _ ambient body bodyScoped
  have bodyInst := recoverValue?_forward _ _ _ _ _ _ bodyRecovery
  have sentInst := recoverValue?_forward _ _ _ _ _ _
    (RestAwareTyping.recoverValue?_root_empty ambient.length sent sentScoped)
  have afterInst := recoverValue?_forward _ _ _ _ _ _
    (RestAwareTyping.recoverValue?_root_empty ambient.length after afterScoped)
  have tailInst := recoverValue?_forward _ _ _ _ _ _
    (RestAwareTyping.recoverValue?_root_empty ambient.length tail tailScoped)
  have args_p : arguments? ActivePair.rule ActivePair.bindingSpec (costSourceSchemaName "p") .right
      [0, 0, 0] = some [.bvar 0] := by decide +kernel
  have args_q : arguments? ActivePair.rule ActivePair.bindingSpec (costSourceSchemaName "q") .right
      [0, 0, 1, 0] = some [] := by decide +kernel
  have args_k : arguments? ActivePair.rule ActivePair.bindingSpec (costSourceSchemaName "k") .right
      [0, 1] = some [] := by decide +kernel
  have args_tail : arguments? ActivePair.rule ActivePair.bindingSpec
      (costAdministrativeSchemaName "stack-tail") .right [1, 0] = some [] := by decide +kernel
  have rightShape : ActivePair.rule.right =
      .apply costContactConstructorName
        [.collection .hashBag
          [.subst (.fvar (costSourceSchemaName "p"))
            (.apply (costWrappedConstructorName "NQuote") [.fvar (costSourceSchemaName "q")]),
           .fvar (costSourceSchemaName "k")] none,
         .apply costFundingConstructorName [.fvar (costAdministrativeSchemaName "stack-tail")]] := rfl
  simp only [reductWith?, rightShape]
  simp [instantiateWith?, instantiateArgsWith?, lookup, ActivePair.pairAssignment,
    args_p, args_q, args_k, args_tail, tailInst, residual]
  simp [costSourceSchemaName, costSourceSchemaTag, costAdministrativeSchemaName,
    costAdministrativeSchemaTag] at *
  simp_all

/-- Actual corrected scoped execution on arbitrary well-scoped payloads.
The matcher and binding authority are the existing ones. -/
theorem firing_pair (ambient : List TypeExpr)
    (channel body sent after signature tail : Pattern)
    (channelScoped : channel.isWellScopedAt ambient.length = true)
    (bodyScoped : body.isWellScopedAt (1 + ambient.length) = true)
    (sentScoped : sent.isWellScopedAt ambient.length = true)
    (afterScoped : after.isWellScopedAt ambient.length = true)
    (signatureScoped : signature.isWellScopedAt ambient.length = true)
    (tailScoped : tail.isWellScopedAt ambient.length = true) :
    Mettapedia.OSLF.MeTTaIL.ScopedRuleExecution.applyRuleWithAt operation
      Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv.empty language ambient.length ActivePair.rule
      (ActivePair.fundedPair channel body sent after signature tail) =
      [residual body sent after tail] := by
  simp only [Mettapedia.OSLF.MeTTaIL.ScopedRuleExecution.applyRuleWithAt,
    Mettapedia.OSLF.MeTTaIL.ScopedRuleExecution.applyRuleComparedWithAt,
    show ActivePair.rule.bindings = some ActivePair.bindingSpec from rfl,
    ActivePair.binding_admitted, if_true]
  rw [matchRuleWithAt_literal, ActivePair.scoped_match_pair ambient channel body sent after signature tail
    channelScoped bodyScoped sentScoped afterScoped signatureScoped tailScoped]
  have noPremises : ActivePair.rule.premises = [] := rfl
  simp [Mettapedia.OSLF.MeTTaIL.ScopedRuleExecution.completeAssignments, noPremises,
    reduct_pair ambient channel body sent after signature tail
      bodyScoped sentScoped afterScoped tailScoped]

/-- General funded activation and its typed result, with binder-local body
admission proved from the actual finite generated signature. -/
theorem typed_firing_pair {free : FreeTypeContext} (ambient : List TypeExpr)
    (channel body sent after signature tail : Pattern)
    (channelTyped : HasSort language free ambient channel (costBaseSortName "Name"))
    (bodyTyped : HasSort language free (.base (costBaseSortName "Name") :: ambient)
      body costWrappedSortName)
    (bodyObject : isObjectPattern body = true)
    (bodySealed : ReflectiveScopeSafeAt profile
      (.base (costBaseSortName "Name") :: ambient).length body)
    (sentTyped : HasSort language free ambient sent costWrappedSortName)
    (afterTyped : HasSort language free ambient after costWrappedSortName)
    (signatureTyped : HasSort language free ambient signature costSignatureSortName)
    (tailTyped : HasSort language free ambient tail costTokenStackSortName) :
    Mettapedia.OSLF.MeTTaIL.ScopedRuleExecution.applyRuleWithAt operation
      Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv.empty language ambient.length ActivePair.rule
      (ActivePair.fundedPair channel body sent after signature tail) =
      [residual body sent after tail] ∧
    HasSort language free ambient (residual body sent after tail) costWrappedSortName := by
  refine ⟨firing_pair ambient channel body sent after signature tail channelTyped.isWellScopedAt
    ?_ sentTyped.isWellScopedAt afterTyped.isWellScopedAt signatureTyped.isWellScopedAt
    tailTyped.isWellScopedAt,
    residual_hasType bodyTyped bodyObject bodySealed sentTyped afterTyped tailTyped⟩
  simpa [Nat.add_comm] using bodyTyped.isWellScopedAt

/-- The actual admitted reflection profile selects the operation for this
general sorted firing; callers supply only the authored payload judgments. -/
theorem source_selected_typed_firing {free : FreeTypeContext} (ambient : List TypeExpr)
    (channel body sent after signature tail : Pattern)
    (channelTyped : HasSort language free ambient channel (costBaseSortName "Name"))
    (bodyTyped : HasSort language free (.base (costBaseSortName "Name") :: ambient)
      body costWrappedSortName)
    (bodyObject : isObjectPattern body = true)
    (bodySealed : ReflectiveScopeSafeAt profile
      (.base (costBaseSortName "Name") :: ambient).length body)
    (sentTyped : HasSort language free ambient sent costWrappedSortName)
    (afterTyped : HasSort language free ambient after costWrappedSortName)
    (signatureTyped : HasSort language free ambient signature costSignatureSortName)
    (tailTyped : HasSort language free ambient tail costTokenStackSortName) :
    Mettapedia.OSLF.MeTTaIL.ScopedReflectiveExecution.applyRuleAt profile
      Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv.empty language ambient.length ActivePair.rule
      (ActivePair.fundedPair channel body sent after signature tail) =
      [residual body sent after tail] ∧
    HasSort language free ambient (residual body sent after tail) costWrappedSortName := by
  rw [Mettapedia.OSLF.MeTTaIL.ScopedReflectiveExecution.selected _ _ _ _ _ _ declaration
    ActivePairContextualReflection.declaration_selected]
  exact typed_firing_pair ambient channel body sent after signature tail channelTyped bodyTyped
    bodyObject bodySealed sentTyped afterTyped signatureTyped tailTyped

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Synchronous.ActivePairReflectionTyping
