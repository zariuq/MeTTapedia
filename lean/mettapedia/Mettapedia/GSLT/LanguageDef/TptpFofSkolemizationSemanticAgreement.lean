import Mettapedia.GSLT.LanguageDef.TptpFofSkolemizationAgreement

/-!
# Semantic agreement of authored FOF Skolemization

This module derives the authored matrix and prenex traversals directly from
typed FOF syntax, then identifies their encoded results with the independent
semantic `skolemizeFrom` function.  The semantic construction does not call
the rewrite engine; exact execution is inherited from the operational
agreement theorem.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.TptpFofSkolemizationSemanticAgreement

open LO FirstOrder
open scoped LO.FirstOrder
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.GSLT.LanguageDef.TptpFofPrenexSemantics
open Mettapedia.GSLT.LanguageDef.TptpFofSkolemizationSemantics
open Mettapedia.GSLT.LanguageDef.TptpFofSkolemizationLanguageDef

theorem sourceTermsPattern_exact {depth : Nat}
    (terms : List (TptpFofSkolemizationSemantics.Source.Term depth)) :
    TptpFofSkolemTermAgreement.Semantic.sourceTermsPattern terms =
      TptpResolvedFofLanguageDef.encodeTerms terms := by
  unfold TptpFofSkolemTermAgreement.Semantic.sourceTermsPattern
    TptpResolvedFofLanguageDef.encodeTerms
  rw [TptpFofSkolemTermAgreement.Semantic.encodeSourcePatternList_exact]
  congr 1
  apply List.map_congr_left
  intro term membership
  exact TptpFofSkolemTermAgreement.Semantic.sourceTermPattern_exact term

theorem translatedTermsPattern_exact {sourceDepth targetDepth : Nat}
    (environment : Fin sourceDepth -> Term targetDepth)
    (terms : List (TptpFofSkolemizationSemantics.Source.Term sourceDepth)) :
    TptpFofSkolemTermAgreement.Semantic.translatedTermsPattern environment terms =
      TptpFofSkolemLanguageDef.encodeTerms
        (terms.map (TptpFofSkolemizationSemantics.translateTerm environment)) := by
  unfold TptpFofSkolemTermAgreement.Semantic.translatedTermsPattern
    TptpFofSkolemLanguageDef.encodeTerms
  rw [TptpFofSkolemTermAgreement.Semantic.encodePatternList_exact]
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  intro term membership
  exact TptpFofSkolemTermAgreement.Semantic.translatedTermPattern_exact
    environment term

/-! ## Quantifier-free matrix traversal -/

noncomputable def matrixTargetPattern {sourceDepth targetDepth : Nat}
    (environment : Fin sourceDepth -> Term targetDepth) :
    (formula : Source.Formula sourceDepth) -> QuantifierFree formula -> Pattern
  | .verum, _ => TptpFofSkolemLanguageDef.verum
  | .falsum, _ => TptpFofSkolemLanguageDef.falsum
  | .rel (.predicate predicate) arguments, _ =>
      TptpFofSkolemLanguageDef.positive
        (TptpFofSymbolLanguageDef.encodePredicateHead ⟨predicate.kind, predicate.name⟩)
        (TptpFofSkolemTermAgreement.Semantic.translatedTermsPattern environment (List.ofFn arguments))
  | .rel .equality arguments, _ =>
      TptpFofSkolemLanguageDef.equal
        (TptpFofSkolemTermAgreement.Semantic.translatedTermPattern environment (arguments 0))
        (TptpFofSkolemTermAgreement.Semantic.translatedTermPattern environment (arguments 1))
  | .nrel (.predicate predicate) arguments, _ =>
      TptpFofSkolemLanguageDef.negative
        (TptpFofSymbolLanguageDef.encodePredicateHead ⟨predicate.kind, predicate.name⟩)
        (TptpFofSkolemTermAgreement.Semantic.translatedTermsPattern environment (List.ofFn arguments))
  | .nrel .equality arguments, _ =>
      TptpFofSkolemLanguageDef.notEqual
        (TptpFofSkolemTermAgreement.Semantic.translatedTermPattern environment (arguments 0))
        (TptpFofSkolemTermAgreement.Semantic.translatedTermPattern environment (arguments 1))
  | .and left right, free =>
      TptpFofSkolemLanguageDef.and
        (matrixTargetPattern environment left free.1)
        (matrixTargetPattern environment right free.2)
  | .or left right, free =>
      TptpFofSkolemLanguageDef.or
        (matrixTargetPattern environment left free.1)
        (matrixTargetPattern environment right free.2)
  | .all _, impossible => False.elim impossible
  | .ex _, impossible => False.elim impossible

noncomputable def matrixDerivation {sourceDepth targetDepth : Nat}
    (environment : Fin sourceDepth -> Term targetDepth) :
    (formula : Source.Formula sourceDepth) ->
    (free : QuantifierFree formula) ->
    TptpFofSkolemizationAgreement.Derivation
      (matrixRequest (TptpFofSkolemTermAgreement.Semantic.environmentPattern environment)
        (TptpFofPrenexLanguageDef.encodeMatrix formula free))
      (matrixResult (TptpFofSkolemTermAgreement.Semantic.environmentPattern environment)
        (TptpFofPrenexLanguageDef.encodeMatrix formula free)
        (matrixTargetPattern environment formula free))
  | .verum, _ => by
      simpa [TptpFofPrenexLanguageDef.encodeMatrix, matrixTargetPattern] using
        TptpFofSkolemizationAgreement.Derivation.matrixVerum
          (TptpFofSkolemTermAgreement.Semantic.environmentPattern environment)
  | .falsum, _ => by
      simpa [TptpFofPrenexLanguageDef.encodeMatrix, matrixTargetPattern] using
        TptpFofSkolemizationAgreement.Derivation.matrixFalsum
          (TptpFofSkolemTermAgreement.Semantic.environmentPattern environment)
  | .rel (.predicate predicate) arguments, _ => by
      simpa [TptpFofPrenexLanguageDef.encodeMatrix, matrixTargetPattern,
        sourceTermsPattern_exact, translatedTermsPattern_exact] using
        TptpFofSkolemizationAgreement.Derivation.matrixPositive
          (TptpFofSkolemTermAgreement.Semantic.termsTranslationDerivation environment
            (List.ofFn arguments))
  | .rel .equality arguments, _ => by
      simpa [TptpFofPrenexLanguageDef.encodeMatrix, matrixTargetPattern,
        TptpFofSkolemTermAgreement.Semantic.sourceTermPattern_exact,
        TptpFofSkolemTermAgreement.Semantic.translatedTermPattern_exact] using
        TptpFofSkolemizationAgreement.Derivation.matrixEqual
          (TptpFofSkolemTermAgreement.Semantic.translationDerivation environment (arguments 0))
          (TptpFofSkolemTermAgreement.Semantic.translationDerivation environment (arguments 1))
  | .nrel (.predicate predicate) arguments, _ => by
      simpa [TptpFofPrenexLanguageDef.encodeMatrix, matrixTargetPattern,
        sourceTermsPattern_exact, translatedTermsPattern_exact] using
        TptpFofSkolemizationAgreement.Derivation.matrixNegative
          (TptpFofSkolemTermAgreement.Semantic.termsTranslationDerivation environment
            (List.ofFn arguments))
  | .nrel .equality arguments, _ => by
      simpa [TptpFofPrenexLanguageDef.encodeMatrix, matrixTargetPattern,
        TptpFofSkolemTermAgreement.Semantic.sourceTermPattern_exact,
        TptpFofSkolemTermAgreement.Semantic.translatedTermPattern_exact] using
        TptpFofSkolemizationAgreement.Derivation.matrixNotEqual
          (TptpFofSkolemTermAgreement.Semantic.translationDerivation environment (arguments 0))
          (TptpFofSkolemTermAgreement.Semantic.translationDerivation environment (arguments 1))
  | .and left right, free => by
      simpa [TptpFofPrenexLanguageDef.encodeMatrix, matrixTargetPattern] using
        TptpFofSkolemizationAgreement.Derivation.matrixAnd
          (matrixDerivation environment left free.1)
          (matrixDerivation environment right free.2)
  | .or left right, free => by
      simpa [TptpFofPrenexLanguageDef.encodeMatrix, matrixTargetPattern] using
        TptpFofSkolemizationAgreement.Derivation.matrixOr
          (matrixDerivation environment left free.1)
          (matrixDerivation environment right free.2)
  | .all _, impossible => False.elim impossible
  | .ex _, impossible => False.elim impossible

theorem matrixTargetPattern_semantic_exact
    {sourceDepth targetDepth : Nat}
    (environment : Fin sourceDepth -> Term targetDepth)
    (formula : Source.Formula sourceDepth)
    (free : QuantifierFree formula) (frontier : Nat) :
    matrixTargetPattern environment formula free =
      TptpFofSkolemLanguageDef.encodeFormula
        (skolemizeFrom environment formula frontier).formula
        (skolemizeFrom_existentialFree environment formula frontier) := by
  induction formula generalizing targetDepth frontier with
  | verum =>
      simp [matrixTargetPattern, skolemizeFrom,
        TptpFofSkolemLanguageDef.encodeFormula]
  | falsum =>
      simp [matrixTargetPattern, skolemizeFrom,
        TptpFofSkolemLanguageDef.encodeFormula]
  | rel relation arguments =>
      cases relation with
      | predicate predicate =>
          simp [matrixTargetPattern, skolemizeFrom,
            TptpFofSkolemLanguageDef.encodeFormula,
            translatedTermsPattern_exact, Function.comp_def]
      | equality =>
          simp [matrixTargetPattern, skolemizeFrom,
            TptpFofSkolemLanguageDef.encodeFormula,
            TptpFofSkolemTermAgreement.Semantic.translatedTermPattern_exact]
  | nrel relation arguments =>
      cases relation with
      | predicate predicate =>
          simp [matrixTargetPattern, skolemizeFrom,
            TptpFofSkolemLanguageDef.encodeFormula,
            translatedTermsPattern_exact, Function.comp_def]
      | equality =>
          simp [matrixTargetPattern, skolemizeFrom,
            TptpFofSkolemLanguageDef.encodeFormula,
            TptpFofSkolemTermAgreement.Semantic.translatedTermPattern_exact]
  | and left right leftHypothesis rightHypothesis =>
      simp only [matrixTargetPattern, skolemizeFrom,
        TptpFofSkolemLanguageDef.encodeFormula]
      rw [leftHypothesis environment free.1 frontier]
      rw [rightHypothesis environment free.2
        (skolemizeFrom environment left frontier).next]
  | or left right leftHypothesis rightHypothesis =>
      simp only [matrixTargetPattern, skolemizeFrom,
        TptpFofSkolemLanguageDef.encodeFormula]
      rw [leftHypothesis environment free.1 frontier]
      rw [rightHypothesis environment free.2
        (skolemizeFrom environment left frontier).next]
  | all body inductionHypothesis => contradiction
  | ex body inductionHypothesis => contradiction

#print axioms matrixTargetPattern_semantic_exact

/-! ## Binder environments -/

theorem environmentPattern_underUniversal_exact
    {sourceDepth targetDepth : Nat}
    (environment : Fin sourceDepth -> Term targetDepth) :
    TptpFofSkolemTermAgreement.Semantic.environmentPattern
        (underUniversal environment) =
      TptpFofSkolemTermLanguageDef.envCons
        (TptpFofSkolemTermLanguageDef.targetTermVariable
          TptpFofSkolemTermLanguageDef.indexZero)
        (TptpFofSkolemTermAgreement.Semantic.shiftedEnvironmentPattern
          environment) := by
  rw [TptpFofSkolemTermAgreement.Semantic.shiftedEnvironmentPattern_semantic_exact]
  simp [underUniversal,
    TptpFofSkolemTermAgreement.Semantic.environmentPattern,
    TptpFofSkolemTermAgreement.Semantic.environmentListPattern,
    TptpFofSkolemTermAgreement.Semantic.encodeEnvironmentPatterns,
    TptpFofSkolemTermAgreement.Semantic.targetTermPattern_exact,
    TptpFofSkolemTermLanguageDef.targetTermVariable,
    TptpFofSkolemTermLanguageDef.indexZero,
    TptpFofSkolemTermLanguageDef.a,
    TptpFofSkolemLanguageDef.termVariable,
    TptpFofSkolemLanguageDef.a,
    TptpFofSkolemLanguageDef.encodeTerm,
    TptpResolvedFofLanguageDef.encodeIndex,
    Function.comp_def, List.ofFn_succ]

theorem environmentPattern_underExistential_exact
    {sourceDepth targetDepth : Nat}
    (environment : Fin sourceDepth -> Term targetDepth) (frontier : Nat) :
    TptpFofSkolemTermAgreement.Semantic.environmentPattern
        (underExistential environment frontier) =
      TptpFofSkolemTermLanguageDef.envCons
        (TptpFofSkolemTermLanguageDef.targetTermGenerated
          (TptpResolvedFofLanguageDef.encodeNatIndex frontier)
          (TptpFofSkolemTermAgreement.Semantic.variablesPattern targetDepth))
        (TptpFofSkolemTermAgreement.Semantic.environmentPattern environment) := by
  simp [underExistential,
    TptpFofSkolemTermAgreement.Semantic.environmentPattern,
    TptpFofSkolemTermAgreement.Semantic.environmentListPattern,
    TptpFofSkolemTermAgreement.Semantic.encodeEnvironmentPatterns,
    TptpFofSkolemTermAgreement.Semantic.targetTermPattern_exact,
    TptpFofSkolemTermLanguageDef.targetTermGenerated,
    TptpFofSkolemTermLanguageDef.a,
    TptpFofSkolemLanguageDef.termGenerated,
    TptpFofSkolemLanguageDef.a,
    TptpFofSkolemLanguageDef.encodeTerm,
    TptpFofSkolemLanguageDef.encodeTerms,
    TptpFofSkolemTermAgreement.Semantic.variablesPattern,
    TptpFofSkolemTermAgreement.Semantic.universalVariables,
    TptpFofSkolemTermAgreement.Semantic.targetTermsPattern_exact,
    TptpFofSkolemizationSemantics.generatedApplication,
    TptpResolvedFofLanguageDef.encodeIndex,
    Function.comp_def, List.map_ofFn, List.ofFn_succ]

#print axioms environmentPattern_underUniversal_exact
#print axioms environmentPattern_underExistential_exact

/-! ## Full prenex traversal -/

theorem existentialCount_eq_zero_of_quantifierFree {depth : Nat}
    (formula : Source.Formula depth) (free : QuantifierFree formula) :
    existentialCount formula = 0 := by
  induction formula with
  | verum => rfl
  | falsum => rfl
  | rel => rfl
  | nrel => rfl
  | and left right leftHypothesis rightHypothesis =>
      simp [existentialCount, leftHypothesis free.1, rightHypothesis free.2]
  | or left right leftHypothesis rightHypothesis =>
      simp [existentialCount, leftHypothesis free.1, rightHypothesis free.2]
  | all body inductionHypothesis => contradiction
  | ex body inductionHypothesis => contradiction

theorem skolemizeFrom_next_of_quantifierFree {sourceDepth targetDepth : Nat}
    (environment : Fin sourceDepth -> Term targetDepth)
    (formula : Source.Formula sourceDepth) (free : QuantifierFree formula)
    (frontier : Nat) :
    (skolemizeFrom environment formula frontier).next = frontier := by
  rw [skolemizeFrom_next_exact]
  simp [existentialCount_eq_zero_of_quantifierFree formula free]

theorem skolemizeFrom_introduced_of_quantifierFree
    {sourceDepth targetDepth : Nat}
    (environment : Fin sourceDepth -> Term targetDepth)
    (formula : Source.Formula sourceDepth) (free : QuantifierFree formula)
    (frontier : Nat) :
    (skolemizeFrom environment formula frontier).introduced = [] := by
  induction formula generalizing targetDepth frontier with
  | verum => simp [skolemizeFrom]
  | falsum => simp [skolemizeFrom]
  | rel => simp [skolemizeFrom]
  | nrel => simp [skolemizeFrom]
  | and left right leftHypothesis rightHypothesis =>
      simp only [skolemizeFrom]
      rw [leftHypothesis environment free.1 frontier]
      rw [rightHypothesis environment free.2
        (skolemizeFrom environment left frontier).next]
      rfl
  | or left right leftHypothesis rightHypothesis =>
      simp only [skolemizeFrom]
      rw [leftHypothesis environment free.1 frontier]
      rw [rightHypothesis environment free.2
        (skolemizeFrom environment left frontier).next]
      rfl
  | all body inductionHypothesis => contradiction
  | ex body inductionHypothesis => contradiction

noncomputable def semanticResultPattern {sourceDepth targetDepth : Nat}
    (environment : Fin sourceDepth -> Term targetDepth)
    (form : PrenexForm sourceDepth) (frontier : Nat) : Pattern :=
  let result := skolemizeFrom environment form.toFormula frontier
  formResult
    (TptpFofSkolemTermAgreement.Semantic.environmentPattern environment)
    (TptpResolvedFofLanguageDef.encodeNatIndex targetDepth)
    (TptpResolvedFofLanguageDef.encodeNatIndex frontier)
    (TptpFofPrenexLanguageDef.encodePrenex form)
    (TptpFofSkolemLanguageDef.encodeFormula result.formula
      (skolemizeFrom_existentialFree environment form.toFormula frontier))
    (TptpResolvedFofLanguageDef.encodeNatIndex result.next)
    (TptpFofSkolemLanguageDef.encodeIntroduced result.introduced)

noncomputable def formDerivation {sourceDepth targetDepth : Nat}
    (environment : Fin sourceDepth -> Term targetDepth) :
    (form : PrenexForm sourceDepth) -> (frontier : Nat) ->
    TptpFofSkolemizationAgreement.Derivation
      (formRequest
        (TptpFofSkolemTermAgreement.Semantic.environmentPattern environment)
        (TptpResolvedFofLanguageDef.encodeNatIndex targetDepth)
        (TptpResolvedFofLanguageDef.encodeNatIndex frontier)
        (TptpFofPrenexLanguageDef.encodePrenex form))
      (semanticResultPattern environment form frontier)
  | .matrix formula free, frontier => by
      have matrixExecution := matrixDerivation environment formula free
      have targetExact := matrixTargetPattern_semantic_exact
        environment formula free frontier
      simpa [semanticResultPattern, TptpFofPrenexLanguageDef.encodePrenex,
        PrenexForm.toFormula, targetExact,
        skolemizeFrom_next_of_quantifierFree environment formula free frontier,
        skolemizeFrom_introduced_of_quantifierFree environment formula free frontier,
        TptpFofSkolemLanguageDef.encodeIntroduced] using
        TptpFofSkolemizationAgreement.Derivation.formMatrix matrixExecution
  | .all body, frontier => by
      have bodyExecution := formDerivation (underUniversal environment) body frontier
      simp only [semanticResultPattern] at bodyExecution
      rw [environmentPattern_underUniversal_exact environment] at bodyExecution
      rw [TptpFofSkolemTermAgreement.Semantic.encodeNatIndex_succ] at bodyExecution
      simpa [semanticResultPattern, TptpFofPrenexLanguageDef.encodePrenex,
        PrenexForm.toFormula, skolemizeFrom,
        TptpFofSkolemLanguageDef.encodeFormula] using
        TptpFofSkolemizationAgreement.Derivation.formAll
          (TptpFofSkolemTermAgreement.Semantic.environmentDerivation environment)
          bodyExecution
  | .ex body, frontier => by
      have bodyExecution := formDerivation
        (underExistential environment frontier) body (frontier + 1)
      simp only [semanticResultPattern] at bodyExecution
      rw [environmentPattern_underExistential_exact environment frontier] at bodyExecution
      rw [TptpFofSkolemTermAgreement.Semantic.encodeNatIndex_succ] at bodyExecution
      simpa [semanticResultPattern, TptpFofPrenexLanguageDef.encodePrenex,
        PrenexForm.toFormula, skolemizeFrom,
        TptpFofSkolemLanguageDef.encodeFormula,
        TptpFofSkolemLanguageDef.encodeIntroduced,
        TptpFofSkolemLanguageDef.encodeIntroducedSymbol,
        TptpFofSkolemTermLanguageDef.indexSucc,
        TptpResolvedFofLanguageDef.encodeNatIndex] using
        TptpFofSkolemizationAgreement.Derivation.formEx
          (TptpFofSkolemTermAgreement.Semantic.variablesDerivation targetDepth)
          bodyExecution

#print axioms existentialCount_eq_zero_of_quantifierFree
#print axioms skolemizeFrom_next_of_quantifierFree
#print axioms skolemizeFrom_introduced_of_quantifierFree

theorem rewriteAt_skolemizeFrom_exact {sourceDepth targetDepth : Nat}
    (environment : Fin sourceDepth -> Term targetDepth)
    (form : PrenexForm sourceDepth) (frontier : Nat) :
    rewriteAt (engineBasePremises RelationEnv.empty)
        TptpFofSkolemizationLanguageDef.language
        (formDerivation environment form frontier).height
        (formRequest
          (TptpFofSkolemTermAgreement.Semantic.environmentPattern environment)
          (TptpResolvedFofLanguageDef.encodeNatIndex targetDepth)
          (TptpResolvedFofLanguageDef.encodeNatIndex frontier)
          (TptpFofPrenexLanguageDef.encodePrenex form)) =
      [semanticResultPattern environment form frontier] :=
  (formDerivation environment form frontier).rewriteAt_exact
    (formDerivation environment form frontier).height (le_refl _)

theorem rewriteAt_skolemizeFrom_no_invention
    {sourceDepth targetDepth : Nat}
    (environment : Fin sourceDepth -> Term targetDepth)
    (form : PrenexForm sourceDepth) (frontier : Nat) (invented : Pattern)
    (membership : invented ∈ rewriteAt
      (engineBasePremises RelationEnv.empty)
      TptpFofSkolemizationLanguageDef.language
      (formDerivation environment form frontier).height
      (formRequest
        (TptpFofSkolemTermAgreement.Semantic.environmentPattern environment)
        (TptpResolvedFofLanguageDef.encodeNatIndex targetDepth)
        (TptpResolvedFofLanguageDef.encodeNatIndex frontier)
        (TptpFofPrenexLanguageDef.encodePrenex form))) :
    invented = semanticResultPattern environment form frontier :=
  (formDerivation environment form frontier).no_invention
    (formDerivation environment form frontier).height (le_refl _) membership

theorem closed_prenex_equisatisfiable (form : PrenexForm 0) :
    SourceSatisfiable form.toFormula <->
      Satisfiable (skolemize form.toFormula).formula :=
  sourceSatisfiable_iff_skolemSatisfiable_of_prenex form.toFormula
    form.toFormula_prenex

#print axioms rewriteAt_skolemizeFrom_exact
#print axioms rewriteAt_skolemizeFrom_no_invention
#print axioms closed_prenex_equisatisfiable

end Mettapedia.GSLT.LanguageDef.TptpFofSkolemizationSemanticAgreement
