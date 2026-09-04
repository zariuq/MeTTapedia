import Mettapedia.GSLT.LanguageDef.StructuralCoproduct
import Mettapedia.OSLF.MeTTaIL.ContextualStep

/-!
# Premise-aware operational conservativity for structural coproducts

The premise-free matcher is insufficient for languages whose operational
rules query primitive relations or recurse through congruence premises.  This
module proves exact, fuel-indexed transport for the actual contextual engine.
The only semantic input is an explicit commuting law for the non-contextual
premise evaluator; constructor matching, ordered rule choice, contextual
recursion, result order, and multiplicity are all handled by the theorem.
-/

namespace Mettapedia.GSLT.LanguageDef.StructuralCoproductOperational

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.StructuralRenamingSemantics
open Mettapedia.GSLT.LanguageDef.StructuralCoproduct

/-- Exact change-of-base law for non-contextual premise evidence.  This is
the semantic datum that a structural presentation map alone cannot invent. -/
def PremiseEvaluatorCommutes
    (symbols : LanguageDefSymbolMap)
    (source target : LanguageDef)
    (sourceBase targetBase : BasePremiseEvaluator) : Prop :=
  ∀ bindings premise,
    targetBase target (mapBindings symbols bindings)
        (mapPremise symbols premise) =
      (sourceBase source bindings premise).map (mapBindings symbols)

/-- The same change-of-base law restricted to one authored premise. -/
def PremiseEvaluatorCommutesAt
    (symbols : LanguageDefSymbolMap)
    (source target : LanguageDef)
    (sourceBase targetBase : BasePremiseEvaluator)
    (premise : Premise) : Prop :=
  ∀ bindings,
    targetBase target (mapBindings symbols bindings)
        (mapPremise symbols premise) =
      (sourceBase source bindings premise).map (mapBindings symbols)

/-- The primitive semantic square is needed precisely on premises that occur
in source rewrite rules.  This avoids imposing behavior on premise forms that
the operational theory never authors. -/
def RulePremiseEvaluatorsCommute
    (symbols : LanguageDefSymbolMap)
    (source target : LanguageDef)
    (sourceBase targetBase : BasePremiseEvaluator) : Prop :=
  ∀ rule ∈ source.rewrites, ∀ premise ∈ rule.premises,
    PremiseEvaluatorCommutesAt symbols source target sourceBase targetBase
      premise

private theorem premiseStepUsing_equivariance
    (symbols : LanguageDefSymbolMap)
    (constructorInjective : Function.Injective symbols.constructor)
    (source target : LanguageDef)
    (sourceBase targetBase : BasePremiseEvaluator)
    (premise : Premise)
    (baseCommutes : PremiseEvaluatorCommutesAt symbols source target
      sourceBase targetBase premise)
    (sourceRecursive targetRecursive : Pattern → List Pattern)
    (recursiveCommutes : ∀ term,
      targetRecursive (mapPattern symbols term) =
        (sourceRecursive term).map (mapPattern symbols))
    (bindings : Bindings) :
    premiseStepUsing targetBase target targetRecursive
        (mapBindings symbols bindings) (mapPremise symbols premise) =
      (premiseStepUsing sourceBase source sourceRecursive bindings premise).map
        (mapBindings symbols) := by
  cases premise with
  | freshness condition =>
      simpa [mapPremise, premiseStepUsing] using baseCommutes bindings
  | relationQuery relation arguments =>
      simpa [mapPremise, premiseStepUsing] using baseCommutes bindings
  | forAll collection parameter body =>
      simpa [mapPremise, premiseStepUsing] using baseCommutes bindings
  | congruence sourcePattern targetPattern =>
      simp only [mapPremise, premiseStepUsing,
        applyBindings_mapPattern, recursiveCommutes,
        List.flatMap_map]
      rw [List.map_flatMap]
      apply List.flatMap_congr
      intro candidate candidateMembership
      rw [matchPattern_equivariance symbols constructorInjective]
      simpa only [Function.comp_apply] using
        filterMap_merge_mapBindings symbols constructorInjective
          bindings (matchPattern targetPattern candidate)

private theorem premisesUsing_equivariance
    (symbols : LanguageDefSymbolMap)
    (constructorInjective : Function.Injective symbols.constructor)
    (source target : LanguageDef)
    (sourceBase targetBase : BasePremiseEvaluator)
    (sourceRecursive targetRecursive : Pattern → List Pattern)
    (recursiveCommutes : ∀ term,
      targetRecursive (mapPattern symbols term) =
        (sourceRecursive term).map (mapPattern symbols)) :
    ∀ (premises : List Premise),
      (∀ premise ∈ premises,
        PremiseEvaluatorCommutesAt symbols source target sourceBase targetBase
          premise) →
      ∀ bindings,
      premisesUsing targetBase target targetRecursive
          (premises.map (mapPremise symbols)) (mapBindings symbols bindings) =
        (premisesUsing sourceBase source sourceRecursive premises bindings).map
          (mapBindings symbols)
  | [], _baseCommutes, bindings => rfl
  | premise :: premises, baseCommutes, bindings => by
      simp only [List.map_cons, premisesUsing]
      rw [premiseStepUsing_equivariance symbols constructorInjective
        source target sourceBase targetBase premise
        (baseCommutes premise (by simp))
        sourceRecursive targetRecursive recursiveCommutes bindings]
      simp only [List.flatMap_map]
      rw [List.map_flatMap]
      apply List.flatMap_congr
      intro nextBindings nextMembership
      simpa only [Function.comp_apply] using
        premisesUsing_equivariance symbols constructorInjective
          source target sourceBase targetBase sourceRecursive targetRecursive
          recursiveCommutes premises
          (fun later laterMembership =>
            baseCommutes later (by simp [laterMembership])) nextBindings

private theorem applyRuleUsing_equivariance
    (symbols : LanguageDefSymbolMap)
    (constructorInjective : Function.Injective symbols.constructor)
    (source target : LanguageDef)
    (sourceBase targetBase : BasePremiseEvaluator)
    (rule : RewriteRule)
    (baseCommutes : ∀ premise ∈ rule.premises,
      PremiseEvaluatorCommutesAt symbols source target sourceBase targetBase
        premise)
    (sourceRecursive targetRecursive : Pattern → List Pattern)
    (recursiveCommutes : ∀ term,
      targetRecursive (mapPattern symbols term) =
        (sourceRecursive term).map (mapPattern symbols))
    (term : Pattern) :
    applyRuleUsing targetBase target targetRecursive
        (mapRewriteRule symbols rule) (mapPattern symbols term) =
      (applyRuleUsing sourceBase source sourceRecursive rule term).map
        (mapPattern symbols) := by
  unfold applyRuleUsing matchPatternForRule applyBindingsForRule
  simp only [matchPatternForRuleUsing, matchingPresentationForRule?,
    reflectiveRuleForRule?,
    Mettapedia.OSLF.MeTTaIL.Reflection.ReflectionProfile.empty_rules,
    List.filter_nil, applyBindingsForRuleUsing,
    substitutionPresentationForRule?, mapRewriteRule]
  rw [matchPattern_equivariance symbols constructorInjective]
  simp only [List.flatMap_map]
  rw [List.map_flatMap]
  apply List.flatMap_congr
  intro initialBindings initialMembership
  rw [premisesUsing_equivariance symbols constructorInjective
    source target sourceBase targetBase sourceRecursive targetRecursive
    recursiveCommutes rule.premises baseCommutes initialBindings]
  simp only [List.map_map]
  apply List.map_congr_left
  intro finalBindings finalMembership
  simpa only [Function.comp_apply] using
    applyBindings_mapPattern symbols finalBindings rule.right

private theorem mappedRules_apply_exact
    (symbols : LanguageDefSymbolMap)
    (constructorInjective : Function.Injective symbols.constructor)
    (source target : LanguageDef)
    (sourceBase targetBase : BasePremiseEvaluator)
    (sourceRecursive targetRecursive : Pattern → List Pattern)
    (recursiveCommutes : ∀ term,
      targetRecursive (mapPattern symbols term) =
        (sourceRecursive term).map (mapPattern symbols))
    : ∀ (rules : List RewriteRule),
      (∀ rule ∈ rules, ∀ premise ∈ rule.premises,
        PremiseEvaluatorCommutesAt symbols source target sourceBase targetBase
          premise) →
      ∀ (term : Pattern),
    (rules.map (mapRewriteRule symbols)).flatMap
        (fun rule => applyRuleUsing targetBase target targetRecursive rule
          (mapPattern symbols term)) =
      (rules.flatMap fun rule =>
        applyRuleUsing sourceBase source sourceRecursive rule term).map
          (mapPattern symbols) := by
  intro rules baseCommutes term
  induction rules generalizing term with
  | nil => rfl
  | cons rule rules inductionHypothesis =>
      simp only [List.map_cons, List.flatMap_cons, List.map_append]
      rw [applyRuleUsing_equivariance symbols constructorInjective
        source target sourceBase targetBase rule
        (baseCommutes rule (by simp))
        sourceRecursive targetRecursive recursiveCommutes term,
        inductionHypothesis
          (fun later laterMembership premise premiseMembership =>
            baseCommutes later (by simp [laterMembership]) premise premiseMembership)
          term]

private theorem crossRule_apply_eq_nil
    (leftSymbols rightSymbols : LanguageDefSymbolMap)
    (imagesDisjoint : ∀ leftConstructor rightConstructor,
      leftSymbols.constructor leftConstructor ≠
        rightSymbols.constructor rightConstructor)
    (targetBase : BasePremiseEvaluator) (target : LanguageDef)
    (targetRecursive : Pattern → List Pattern)
    (rewrite : RewriteRule) (rooted : ConstructorRooted rewrite)
    (term : Pattern) :
    applyRuleUsing targetBase target targetRecursive
        (mapRewriteRule rightSymbols rewrite)
        (mapPattern leftSymbols term) = [] := by
  rcases rooted with ⟨root, arguments, rootEquality⟩
  have matching :
      matchPatternForRule target (mapRewriteRule rightSymbols rewrite)
          (mapPattern leftSymbols term) = [] := by
    unfold matchPatternForRule matchPatternForRuleUsing
    simp only [matchingPresentationForRule?, reflectiveRuleForRule?,
      Mettapedia.OSLF.MeTTaIL.Reflection.ReflectionProfile.empty_rules,
      List.filter_nil, mapRewriteRule, rootEquality, mapPattern]
    cases term with
    | bvar index => simp [mapPattern, matchPattern]
    | fvar name => simp [mapPattern, matchPattern]
    | apply constructor termArguments =>
        have unequal :
            rightSymbols.constructor root ≠
              leftSymbols.constructor constructor :=
          fun equality => imagesDisjoint constructor root equality.symm
        simp [mapPattern, matchPattern, unequal]
    | lambda binder body => simp [mapPattern, matchPattern]
    | multiLambda arity binders body => simp [mapPattern, matchPattern]
    | subst body replacement => simp [mapPattern, matchPattern]
    | collection collectionType elements rest => simp [mapPattern, matchPattern]
  unfold applyRuleUsing
  rw [matching]
  rfl

private theorem reverseCrossRule_apply_eq_nil
    (leftSymbols rightSymbols : LanguageDefSymbolMap)
    (imagesDisjoint : ∀ leftConstructor rightConstructor,
      leftSymbols.constructor leftConstructor ≠
        rightSymbols.constructor rightConstructor)
    (targetBase : BasePremiseEvaluator) (target : LanguageDef)
    (targetRecursive : Pattern → List Pattern)
    (rewrite : RewriteRule) (rooted : ConstructorRooted rewrite)
    (term : Pattern) :
    applyRuleUsing targetBase target targetRecursive
        (mapRewriteRule leftSymbols rewrite)
        (mapPattern rightSymbols term) = [] := by
  rcases rooted with ⟨root, arguments, rootEquality⟩
  have matching :
      matchPatternForRule target (mapRewriteRule leftSymbols rewrite)
          (mapPattern rightSymbols term) = [] := by
    unfold matchPatternForRule matchPatternForRuleUsing
    simp only [matchingPresentationForRule?, reflectiveRuleForRule?,
      Mettapedia.OSLF.MeTTaIL.Reflection.ReflectionProfile.empty_rules,
      List.filter_nil, mapRewriteRule, rootEquality, mapPattern]
    cases term with
    | bvar index => simp [mapPattern, matchPattern]
    | fvar name => simp [mapPattern, matchPattern]
    | apply constructor termArguments =>
        have unequal :
            leftSymbols.constructor root ≠
              rightSymbols.constructor constructor :=
          imagesDisjoint root constructor
        simp [mapPattern, matchPattern, unequal]
    | lambda binder body => simp [mapPattern, matchPattern]
    | multiLambda arity binders body => simp [mapPattern, matchPattern]
    | subst body replacement => simp [mapPattern, matchPattern]
    | collection collectionType elements rest => simp [mapPattern, matchPattern]
  unfold applyRuleUsing
  rw [matching]
  rfl

namespace Compatibility

variable {name : String} {leftSymbols rightSymbols : LanguageDefSymbolMap}
  {left right : ValidatedLanguageDef}

/-- Exact premise-aware and contextual operational conservativity for the
left component.  The equality preserves rule order, result order, and proof
occurrence multiplicity at every contextual fuel. -/
theorem left_rewriteAt_exact_onRules
    (compatible : Compatibility name leftSymbols rightSymbols left right)
    (sourceBase targetBase : BasePremiseEvaluator)
    (baseCommutes : RulePremiseEvaluatorsCommute leftSymbols left.language
      compatible.combinedLanguage.language sourceBase targetBase)
    (fuel : Nat) (term : Pattern) :
    rewriteAt targetBase compatible.combinedLanguage.language fuel
        (mapPattern leftSymbols term) =
      (rewriteAt sourceBase left.language fuel term).map
        (mapPattern leftSymbols) := by
  induction fuel generalizing term with
  | zero => rfl
  | succ fuel inductionHypothesis =>
      simp only [rewriteAt]
      change
        (((left.language.rewrites.map (mapRewriteRule leftSymbols)) ++
          (right.language.rewrites.map (mapRewriteRule rightSymbols))).flatMap
          (fun rule => applyRuleUsing targetBase
            compatible.combinedLanguage.language
            (rewriteAt targetBase compatible.combinedLanguage.language fuel)
            rule (mapPattern leftSymbols term))) = _
      rw [List.flatMap_append]
      rw [mappedRules_apply_exact leftSymbols
        compatible.leftSymbolsInjective.constructor
        left.language compatible.combinedLanguage.language sourceBase targetBase
        (rewriteAt sourceBase left.language fuel)
        (rewriteAt targetBase compatible.combinedLanguage.language fuel)
        inductionHypothesis left.language.rewrites baseCommutes term]
      have rightSilent :
          (right.language.rewrites.map (mapRewriteRule rightSymbols)).flatMap
              (fun rule => applyRuleUsing targetBase
                compatible.combinedLanguage.language
                (rewriteAt targetBase compatible.combinedLanguage.language fuel)
                rule (mapPattern leftSymbols term)) = [] := by
        rw [List.flatMap_eq_nil_iff]
        intro mappedRule mappedMember
        obtain ⟨sourceRule, sourceMember, rfl⟩ :=
          List.mem_map.mp mappedMember
        exact crossRule_apply_eq_nil leftSymbols rightSymbols
          compatible.symbolImagesDisjoint.constructor targetBase
          compatible.combinedLanguage.language
          (rewriteAt targetBase compatible.combinedLanguage.language fuel)
          sourceRule
          (compatible.rightRewritesRooted sourceRule sourceMember) term
      rw [rightSilent, List.append_nil]

/-- Symmetric premise-aware and contextual operational conservativity for the
right component. -/
theorem right_rewriteAt_exact_onRules
    (compatible : Compatibility name leftSymbols rightSymbols left right)
    (sourceBase targetBase : BasePremiseEvaluator)
    (baseCommutes : RulePremiseEvaluatorsCommute rightSymbols right.language
      compatible.combinedLanguage.language sourceBase targetBase)
    (fuel : Nat) (term : Pattern) :
    rewriteAt targetBase compatible.combinedLanguage.language fuel
        (mapPattern rightSymbols term) =
      (rewriteAt sourceBase right.language fuel term).map
        (mapPattern rightSymbols) := by
  induction fuel generalizing term with
  | zero => rfl
  | succ fuel inductionHypothesis =>
      simp only [rewriteAt]
      change
        (((left.language.rewrites.map (mapRewriteRule leftSymbols)) ++
          (right.language.rewrites.map (mapRewriteRule rightSymbols))).flatMap
          (fun rule => applyRuleUsing targetBase
            compatible.combinedLanguage.language
            (rewriteAt targetBase compatible.combinedLanguage.language fuel)
            rule (mapPattern rightSymbols term))) = _
      rw [List.flatMap_append]
      have leftSilent :
          (left.language.rewrites.map (mapRewriteRule leftSymbols)).flatMap
              (fun rule => applyRuleUsing targetBase
                compatible.combinedLanguage.language
                (rewriteAt targetBase compatible.combinedLanguage.language fuel)
                rule (mapPattern rightSymbols term)) = [] := by
        rw [List.flatMap_eq_nil_iff]
        intro mappedRule mappedMember
        obtain ⟨sourceRule, sourceMember, rfl⟩ :=
          List.mem_map.mp mappedMember
        exact reverseCrossRule_apply_eq_nil leftSymbols rightSymbols
          compatible.symbolImagesDisjoint.constructor targetBase
          compatible.combinedLanguage.language
          (rewriteAt targetBase compatible.combinedLanguage.language fuel)
          sourceRule
          (compatible.leftRewritesRooted sourceRule sourceMember) term
      rw [leftSilent, List.nil_append]
      exact mappedRules_apply_exact rightSymbols
        compatible.rightSymbolsInjective.constructor
        right.language compatible.combinedLanguage.language sourceBase targetBase
        (rewriteAt sourceBase right.language fuel)
        (rewriteAt targetBase compatible.combinedLanguage.language fuel)
        inductionHypothesis right.language.rewrites baseCommutes term

/-- A global primitive-evaluator square is a sufficient special case of the
rule-local premise-aware operational theorem. -/
theorem left_rewriteAt_exact
    (compatible : Compatibility name leftSymbols rightSymbols left right)
    (sourceBase targetBase : BasePremiseEvaluator)
    (baseCommutes : PremiseEvaluatorCommutes leftSymbols left.language
      compatible.combinedLanguage.language sourceBase targetBase)
    (fuel : Nat) (term : Pattern) :
    rewriteAt targetBase compatible.combinedLanguage.language fuel
        (mapPattern leftSymbols term) =
      (rewriteAt sourceBase left.language fuel term).map
        (mapPattern leftSymbols) :=
  left_rewriteAt_exact_onRules compatible sourceBase targetBase
    (by
      intro rule ruleMembership premise premiseMembership bindings
      exact baseCommutes bindings premise)
    fuel term

/-- Symmetric global-square specialization. -/
theorem right_rewriteAt_exact
    (compatible : Compatibility name leftSymbols rightSymbols left right)
    (sourceBase targetBase : BasePremiseEvaluator)
    (baseCommutes : PremiseEvaluatorCommutes rightSymbols right.language
      compatible.combinedLanguage.language sourceBase targetBase)
    (fuel : Nat) (term : Pattern) :
    rewriteAt targetBase compatible.combinedLanguage.language fuel
        (mapPattern rightSymbols term) =
      (rewriteAt sourceBase right.language fuel term).map
        (mapPattern rightSymbols) :=
  right_rewriteAt_exact_onRules compatible sourceBase targetBase
    (by
      intro rule ruleMembership premise premiseMembership bindings
      exact baseCommutes bindings premise)
    fuel term

end Compatibility

#print axioms Compatibility.left_rewriteAt_exact_onRules
#print axioms Compatibility.right_rewriteAt_exact_onRules
#print axioms Compatibility.left_rewriteAt_exact
#print axioms Compatibility.right_rewriteAt_exact

end Mettapedia.GSLT.LanguageDef.StructuralCoproductOperational
