import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementAbstractModelMapCommutation
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementAbstractEvidenceExtraction

/-!
# Mixed context, substitution and generated-certificate images

The image scope is constructed through every data binder and assumption
inclusion. Actual source evaluation determines the target context, dependent
annotation, complete value and ordered guarded substitution. All eleven
judgment species then preserve their interpretations. The certificate
comparison retains the supplied trees and uses independently proved
soundness and deterministic evaluation.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Abstract

open Mettapedia.GSLT.Core.ContextualLadder
open ContextualPredicateModel ContextualPredicateModelScopes ContextualPredicateScopeMorphism
open ContextualModelTelescopes ContextualComprehensionMorphism ContextualTelescopeMorphism
open ContextualTypeOperations
open External (bindResult bindResult_eq_some_iff)

universe a c s t m p q
variable {S : Symbols.{a}} {C D : CwfWithTerminal.{c,s,t,m}}
  {sourceModel : LocalModel.{c,s,t,m,p} C} {targetModel : LocalModel.{c,s,t,m,q} D}
  {source : ModelData S C sourceModel} {target : ModelData S D targetModel}

namespace ModelMap

set_option backward.isDefEq.respectTransparency false in
theorem evaluateContext_image (mapping : ModelMap source target) :
    {n : Nat} → (raw : ContextExpr S n) → (Γ : ModelScope C sourceModel n) →
    source.evaluateContext raw = some Γ → target.evaluateContext raw =
      some (imageScope mapping.morphism mapping.predicates.assumptions Γ)
  | _, .nil, Γ, evaluated => by
      have actual : Scope.nil C sourceModel.doctrine sourceModel.assumptions = Γ :=
        Option.some.inj evaluated
      rw [← actual, imageScope_nil]
      rfl
  | _, .snoc raw domain, Γ, evaluated => by
      rw [ModelData.evaluateContext] at evaluated
      rcases (bindResult_eq_some_iff _ _ _).mp evaluated with ⟨previous, previousRead, rest⟩
      rcases (bindResult_eq_some_iff _ _ _).mp rest with ⟨A, typeRead, last⟩
      have actual : previous.snoc A = Γ := Option.some.inj last
      rw [← actual, imageScope_snoc]
      have previousImage := evaluateContext_image mapping raw previous previousRead
      have contexts := imageScope_comparison mapping.morphism mapping.predicates.assumptions previous
      rcases mapping.evaluateType_image domain previous _ contexts A typeRead with
        ⟨A', typeImage, types⟩
      have annotation : A' = imageType mapping.morphism contexts.contexts A :=
        eq_of_heq (types.symm.trans (imageType_heq mapping.morphism contexts.contexts A))
      rw [annotation] at typeImage
      exact target.evaluateContext_snoc raw domain _ _ previousImage typeImage
  | _, .assume raw predicate, Γ, evaluated => by
      rw [ModelData.evaluateContext] at evaluated
      rcases (bindResult_eq_some_iff _ _ _).mp evaluated with ⟨previous, previousRead, rest⟩
      rcases (bindResult_eq_some_iff _ _ _).mp rest with ⟨φ, predicateRead, last⟩
      have actual : previous.assume φ = Γ := Option.some.inj last
      rw [← actual, imageScope_assume]
      have previousImage := evaluateContext_image mapping raw previous previousRead
      have contexts := imageScope_comparison mapping.morphism mapping.predicates.assumptions previous
      rcases mapping.evaluatePredicate_image predicate previous _ contexts φ predicateRead with
        ⟨φ', predicateImage, predicates⟩
      have annotation : φ' = imagePredicate mapping.predicates.doctrine contexts.contexts φ :=
        eq_of_heq (predicates.symm.trans
          (imagePredicate_heq mapping.predicates.doctrine contexts.contexts φ))
      rw [annotation] at predicateImage
      exact target.evaluateContext_assume raw predicate _ _ previousImage predicateImage

theorem evaluateType_image_unique (mapping : ModelMap source target) {n : Nat}
    (type : TypeExpr S n) (Γ : ModelScope C sourceModel n) (Γ' : ModelScope D targetModel n)
    (contexts : ScopeImage mapping.morphism Γ Γ') (A : C.toCwf.Ty Γ.1) (A' : D.toCwf.Ty Γ'.1)
    (sourceRead : source.evaluateType Γ type = some A)
    (targetRead : target.evaluateType Γ' type = some A') :
    HEq (mapping.morphism.toFamilyMorphism.mapType A) A' := by
  rcases mapping.evaluateType_image type Γ Γ' contexts A sourceRead with ⟨actual, read, related⟩
  cases Option.some.inj (read.symm.trans targetRead)
  exact related

theorem evaluateTerm_image_unique (mapping : ModelMap source target) {n : Nat}
    (term : TermExpr S n) (Γ : ModelScope C sourceModel n) (Γ' : ModelScope D targetModel n)
    (contexts : ScopeImage mapping.morphism Γ Γ')
    (value : Value C.toCwf Γ.1) (value' : Value D.toCwf Γ'.1)
    (sourceRead : source.evaluateTerm Γ term = some value)
    (targetRead : target.evaluateTerm Γ' term = some value') :
    ValueImage mapping.morphism value value' := by
  rcases mapping.evaluateTerm_image term Γ Γ' contexts value sourceRead with ⟨actual, read, related⟩
  cases Option.some.inj (read.symm.trans targetRead)
  exact related

theorem evaluatePredicate_image_unique (mapping : ModelMap source target) {n : Nat}
    (predicate : PropExpr S n) (Γ : ModelScope C sourceModel n) (Γ' : ModelScope D targetModel n)
    (contexts : ScopeImage mapping.morphism Γ Γ')
    (φ : sourceModel.doctrine.Predicate Γ.1) (φ' : targetModel.doctrine.Predicate Γ'.1)
    (sourceRead : source.evaluatePredicate Γ predicate = some φ)
    (targetRead : target.evaluatePredicate Γ' predicate = some φ') :
    HEq (mapping.predicates.doctrine.hom Γ.1 φ) φ' := by
  rcases mapping.evaluatePredicate_image predicate Γ Γ' contexts φ sourceRead with
    ⟨actual, read, related⟩
  cases Option.some.inj (read.symm.trans targetRead)
  exact related

theorem typed_evaluation_image (mapping : ModelMap source target) {n : Nat}
    (type : TypeExpr S n) (term : TermExpr S n)
    (Γ : ModelScope C sourceModel n) (Γ' : ModelScope D targetModel n)
    (contexts : ScopeImage mapping.morphism Γ Γ') (A : C.toCwf.Ty Γ.1)
    (value : C.toCwf.Tm Γ.1 A) (typeRead : source.evaluateType Γ type = some A)
    (termRead : source.evaluateTerm Γ term = some ⟨A, value⟩) :
    ∃ A' : D.toCwf.Ty Γ'.1, ∃ value' : D.toCwf.Tm Γ'.1 A',
      target.evaluateType Γ' type = some A' ∧
      target.evaluateTerm Γ' term = some ⟨A', value'⟩ ∧
      ValueImage mapping.morphism (⟨A, value⟩ : Value C.toCwf Γ.1) ⟨A', value'⟩ := by
  rcases mapping.evaluateType_image type Γ Γ' contexts A typeRead with ⟨A', typeImage, types⟩
  rcases mapping.evaluateTerm_image term Γ Γ' contexts _ termRead with ⟨actual, termImage, related⟩
  rcases ValueImage.at_type mapping.morphism contexts.contexts types value actual related with
    ⟨value', valueRead, terms⟩
  rw [valueRead] at termImage
  exact ⟨A', value', typeImage, termImage, ⟨types, terms⟩⟩

theorem evaluateSubstitution_image (mapping : ModelMap source target) {n k : Nat}
    (Γ : ModelScope C sourceModel n) (Δ : ModelScope C sourceModel k)
    (Γ' : ModelScope D targetModel n) (Δ' : ModelScope D targetModel k)
    (sources : ScopeImage mapping.morphism Γ Γ') (targets : ScopeImage mapping.morphism Δ Δ')
    (substitution : Substitution S k n) (arrow : C.toCwf.Sub Γ.1 Δ.1)
    (evaluated : source.evaluateSubstitution Γ Δ substitution = some arrow) :
    target.evaluateSubstitution Γ' Δ' substitution =
      some (imageArrow mapping.morphism sources.contexts targets.contexts arrow) :=
  targets.assemble mapping.morphism sources.contexts _ _ arrow evaluated
    (fun index value read => mapping.evaluateTerm_image (substitution index) Γ Γ' sources value read)

/-- Full judgment preservation is a consequence of the actual expression,
mixed-context and guarded-substitution comparisons. -/
theorem interprets (mapping : ModelMap source target) {judgment : Judgment S}
    (interpreted : Interprets source judgment) : Interprets target judgment := by
  cases judgment with
  | context raw =>
      rcases interpreted with ⟨Γ, contextRead⟩
      exact ⟨_, mapping.evaluateContext_image raw Γ contextRead⟩
  | type raw type =>
      rcases interpreted with ⟨Γ, A, contextRead, typeRead⟩
      rcases mapping.evaluateType_image type Γ _
        (imageScope_comparison _ mapping.predicates.assumptions Γ) A typeRead with
          ⟨A', typeImage, _⟩
      exact ⟨_, A', mapping.evaluateContext_image raw Γ contextRead, typeImage⟩
  | term raw term type =>
      rcases interpreted with ⟨Γ, A, value, contextRead, typeRead, termRead⟩
      rcases mapping.typed_evaluation_image type term Γ _
        (imageScope_comparison _ mapping.predicates.assumptions Γ) A value typeRead termRead with
          ⟨A', value', typeImage, termImage, _⟩
      exact ⟨_, A', value', mapping.evaluateContext_image raw Γ contextRead, typeImage, termImage⟩
  | substitution rawSource rawTarget substitution =>
      rcases interpreted with ⟨Γ, Δ, arrow, sourceRead, targetRead, arrowRead⟩
      exact ⟨_, _, _, mapping.evaluateContext_image rawSource Γ sourceRead,
        mapping.evaluateContext_image rawTarget Δ targetRead,
        mapping.evaluateSubstitution_image Γ Δ _ _
          (imageScope_comparison _ mapping.predicates.assumptions Γ)
          (imageScope_comparison _ mapping.predicates.assumptions Δ) substitution arrow arrowRead⟩
  | contextEq first second =>
      rcases interpreted with ⟨Γ, firstRead, secondRead⟩
      exact ⟨_, mapping.evaluateContext_image first Γ firstRead,
        mapping.evaluateContext_image second Γ secondRead⟩
  | typeEq raw first second =>
      rcases interpreted with ⟨Γ, A, contextRead, firstRead, secondRead⟩
      have contexts := imageScope_comparison mapping.morphism mapping.predicates.assumptions Γ
      rcases mapping.evaluateType_image first Γ _ contexts A firstRead with
        ⟨A', firstImage, firstTypes⟩
      rcases mapping.evaluateType_image second Γ _ contexts A secondRead with
        ⟨A'', secondImage, secondTypes⟩
      have same : A'' = A' := eq_of_heq (secondTypes.symm.trans firstTypes)
      rw [same] at secondImage
      exact ⟨_, A', mapping.evaluateContext_image raw Γ contextRead, firstImage, secondImage⟩
  | termEq raw first second type =>
      rcases interpreted with ⟨Γ, A, value, contextRead, typeRead, firstRead, secondRead⟩
      have contexts := imageScope_comparison mapping.morphism mapping.predicates.assumptions Γ
      rcases mapping.typed_evaluation_image type first Γ _ contexts A value typeRead firstRead with
        ⟨A', value', typeImage, firstImage, firstValues⟩
      rcases mapping.evaluateTerm_image second Γ _ contexts _ secondRead with
        ⟨actual, secondImage, secondValues⟩
      have equalValues : actual = ⟨A', value'⟩ :=
        Sigma.ext (eq_of_heq (secondValues.types.symm.trans firstValues.types))
          (secondValues.terms.symm.trans firstValues.terms)
      rw [equalValues] at secondImage
      exact ⟨_, A', value', mapping.evaluateContext_image raw Γ contextRead,
        typeImage, firstImage, secondImage⟩
  | substitutionEq rawSource rawTarget first second =>
      rcases interpreted with ⟨Γ, Δ, arrow, sourceRead, targetRead, firstRead, secondRead⟩
      have sources := imageScope_comparison mapping.morphism mapping.predicates.assumptions Γ
      have targets := imageScope_comparison mapping.morphism mapping.predicates.assumptions Δ
      exact ⟨_, _, _, mapping.evaluateContext_image rawSource Γ sourceRead,
        mapping.evaluateContext_image rawTarget Δ targetRead,
        mapping.evaluateSubstitution_image Γ Δ _ _ sources targets first arrow firstRead,
        mapping.evaluateSubstitution_image Γ Δ _ _ sources targets second arrow secondRead⟩
  | predicate raw predicate =>
      rcases interpreted with ⟨Γ, φ, contextRead, predicateRead⟩
      rcases mapping.evaluatePredicate_image predicate Γ _
        (imageScope_comparison _ mapping.predicates.assumptions Γ) φ predicateRead with
          ⟨φ', predicateImage, _⟩
      exact ⟨_, φ', mapping.evaluateContext_image raw Γ contextRead, predicateImage⟩
  | entails raw predicate =>
      rcases interpreted with ⟨Γ, contextRead, predicateRead⟩
      have contexts := imageScope_comparison mapping.morphism mapping.predicates.assumptions Γ
      rcases mapping.evaluatePredicate_image predicate Γ _ contexts ⊤ predicateRead with
        ⟨φ', predicateImage, predicates⟩
      have truth : φ' = ⊤ := eq_of_heq
        (predicates.symm.trans (mapping.truth_image contexts.contexts))
      rw [truth] at predicateImage
      exact ⟨_, mapping.evaluateContext_image raw Γ contextRead, predicateImage⟩
  | predicateEq raw first second =>
      rcases interpreted with ⟨Γ, φ, contextRead, firstRead, secondRead⟩
      have contexts := imageScope_comparison mapping.morphism mapping.predicates.assumptions Γ
      rcases mapping.evaluatePredicate_image first Γ _ contexts φ firstRead with
        ⟨φ', firstImage, firstPredicates⟩
      rcases mapping.evaluatePredicate_image second Γ _ contexts φ secondRead with
        ⟨φ'', secondImage, secondPredicates⟩
      have same : φ'' = φ' := eq_of_heq (secondPredicates.symm.trans firstPredicates)
      rw [same] at secondImage
      exact ⟨_, φ', mapping.evaluateContext_image raw Γ contextRead, firstImage, secondImage⟩

end ModelMap

namespace Derivation

variable {signature : Signature S}

/-- The actual local map carries the generated certificate interpretation;
judgment preservation is proved, rather than a map capability. -/
theorem sound_modelMap (mapping : ModelMap source target)
    (realization : SignatureRealization source signature) (qualified : Qualification sourceModel)
    {judgment : Judgment S} (derivation : Derivation signature judgment) :
    Interprets target judgment :=
  mapping.interprets (Derivation.qualified_sound source realization qualified derivation)

/-- Distinct supplied derivation trees compare at their exact complete
section readings under the actual local logical map. -/
theorem termSection_modelMap (mapping : ModelMap source target)
    (sourceRealization : SignatureRealization source signature) (sourceQualified : Qualification sourceModel)
    (targetRealization : SignatureRealization target signature) (targetQualified : Qualification targetModel)
    {n : Nat} {raw : ContextExpr S n} {term : TermExpr S n} {type : TypeExpr S n}
    (first second : Derivation signature (.term raw term type))
    (Γ : ModelScope C sourceModel n) (Γ' : ModelScope D targetModel n)
    (contexts : ScopeImage mapping.morphism Γ Γ') (A : C.toCwf.Ty Γ.1) (A' : D.toCwf.Ty Γ'.1)
    (sourceContext : source.evaluateContext raw = some Γ)
    (sourceType : source.evaluateType Γ type = some A)
    (targetContext : target.evaluateContext raw = some Γ')
    (targetType : target.evaluateType Γ' type = some A') :
    HEq (mapping.morphism.toFamilyMorphism.mapTerm
      (Derivation.termSection source sourceRealization sourceQualified.stableProducts
        sourceQualified.productBeta sourceQualified.productEta first Γ A sourceContext sourceType))
      (Derivation.termSection target targetRealization targetQualified.stableProducts
        targetQualified.productBeta targetQualified.productEta second Γ' A' targetContext targetType) :=
  (mapping.evaluateTerm_image_unique term Γ Γ' contexts _ _
    (Derivation.termSection_readout source sourceRealization sourceQualified.stableProducts
      sourceQualified.productBeta sourceQualified.productEta first Γ A sourceContext sourceType)
    (Derivation.termSection_readout target targetRealization targetQualified.stableProducts
      targetQualified.productBeta targetQualified.productEta second Γ' A' targetContext targetType)).terms

end Derivation

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Abstract
