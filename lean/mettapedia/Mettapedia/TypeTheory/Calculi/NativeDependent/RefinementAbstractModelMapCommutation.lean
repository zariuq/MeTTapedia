import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementAbstractModelMapComputation
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementAbstractPredicateInterpretation

/-!
# Mixed predicate interpretation commutes with local model maps

Mutual induction visits the independent raw type, term and predicate syntax, including
every primitive argument, binder annotation and complete sum motive.
Successful source readouts commute using only the local contextual,
logical-constructor and primitive-meaning capabilities. Failed source
checks are not reflected by an arbitrary noninjective model map.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Abstract

open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.ContextualModelTelescopes
open Mettapedia.TypeTheory.ContextualComprehensionMorphism
open Mettapedia.TypeTheory.ContextualTelescopeMorphism
open Mettapedia.TypeTheory.ContextualLogicalMorphism
open Mettapedia.TypeTheory.ContextualSumComprehension
open Mettapedia.TypeTheory.ContextualProductComparison (selfExtend)
open Mettapedia.TypeTheory.ContextualTypeOperations
open ContextualPredicateModel ContextualPredicateScopeMorphism
open External (bindResult bindResult_eq_some_iff bindResult_some)

universe a c s t m p q

variable {S : Symbols.{a}} {C D : CwfWithTerminal.{c, s, t, m}}
  {sourceModel : LocalModel.{c,s,t,m,p} C} {targetModel : LocalModel.{c,s,t,m,q} D}
  {source : ModelData S C sourceModel} {target : ModelData S D targetModel}

namespace ModelMap

set_option backward.isDefEq.respectTransparency false in
mutual

theorem evaluateType_image (mapping : ModelMap source target) :
    {n : Nat} → (type : TypeExpr S n) → (Γ : ModelScope C sourceModel n) → (Γ' : ModelScope D targetModel n) →
    (contexts : ScopeImage mapping.morphism Γ Γ') → (A : C.toCwf.Ty Γ.1) →
    source.evaluateType Γ type = some A →
    ∃ A' : D.toCwf.Ty Γ'.1, target.evaluateType Γ' type = some A' ∧
      HEq (mapping.morphism.toFamilyMorphism.mapType A) A'
  | _, .family symbol arguments, Γ, Γ', contexts, A, evaluated => by
      change bindResult ((source.typeParameters symbol).2.assemble?
        (fun index => source.evaluateTerm Γ (arguments index)))
        (fun actual => some (source.familyAt symbol actual)) = some A at evaluated
      rcases (bindResult_eq_some_iff _ _ _).mp evaluated with ⟨actual, assembled, last⟩
      have actualType : source.familyAt symbol actual = A := Option.some.inj last
      have argumentImages : ∀ index value,
          source.evaluateTerm Γ (arguments index) = some value →
          ∃ value', target.evaluateTerm Γ' (arguments index) = some value' ∧
            ValueImage mapping.morphism value value' := by
        intro index value read
        exact evaluateTerm_image mapping (arguments index) Γ Γ' contexts value read
      have targetAssembled := (mapping.typeParameters symbol).assemble mapping.morphism
        contexts.contexts _ _ actual assembled argumentImages
      refine ⟨target.familyAt symbol (imageArrow mapping.morphism contexts.contexts
        (mapping.typeParameters symbol).contexts actual), ?_, ?_⟩
      · change bindResult ((target.typeParameters symbol).2.assemble?
          (fun index => target.evaluateTerm Γ' (arguments index))) _ = _
        rw [targetAssembled]
        rfl
      · rw [← actualType]
        exact mapping.familyAt_image contexts.contexts symbol actual
  | _, .propositions, Γ, Γ', contexts, result, evaluated => by
      change some (sourceModel.propositions.omega Γ.1) = some result at evaluated
      refine ⟨targetModel.propositions.omega Γ'.1, rfl, ?_⟩
      rw [← Option.some.inj evaluated]
      exact mapping.proposition_image contexts.contexts
  | _, .pi domain body, Γ, Γ', contexts, result, evaluated => by
      rcases (source.dependentAnnotations_eq_some_iff Γ domain body
        (fun A B => some (sourceModel.products.pi A B)) result).mp evaluated with
        ⟨A, B, domainRead, bodyRead, last⟩
      have actualType : sourceModel.products.pi A B = result :=
        Option.some.inj last
      rcases evaluateType_image mapping domain Γ Γ' contexts A domainRead with
        ⟨A', domainImage, domains⟩
      rcases evaluateType_image mapping body (Γ.snoc A) (Γ'.snoc A')
        (contexts.snoc mapping.morphism domains) B bodyRead with ⟨B', bodyImage, codomains⟩
      refine ⟨targetModel.products.pi A' B', target.evaluate_pi Γ' domain body A' B' domainImage bodyImage, ?_⟩
      rw [← actualType]
      exact mapping.logical.products.formation contexts.contexts domains codomains
  | _, .sigma domain body, Γ, Γ', contexts, result, evaluated => by
      rcases (source.dependentAnnotations_eq_some_iff Γ domain body
        (fun A B => some (sourceModel.sums.operations.sigma A B)) result).mp evaluated with
        ⟨A, B, domainRead, bodyRead, last⟩
      have actualType : sourceModel.sums.operations.sigma A B = result :=
        Option.some.inj last
      rcases evaluateType_image mapping domain Γ Γ' contexts A domainRead with
        ⟨A', domainImage, domains⟩
      rcases evaluateType_image mapping body (Γ.snoc A) (Γ'.snoc A')
        (contexts.snoc mapping.morphism domains) B bodyRead with ⟨B', bodyImage, codomains⟩
      refine ⟨targetModel.sums.operations.sigma A' B',
        target.evaluate_sigma Γ' domain body A' B' domainImage bodyImage, ?_⟩
      rw [← actualType]
      exact mapping.logical.sums.formation contexts.contexts domains codomains
  | _, .comprehension domain predicate, Γ, Γ', contexts, result, evaluated => by
      change bindResult (source.evaluateType Γ domain) (fun A =>
        bindResult (source.evaluatePredicate (Γ.snoc A) predicate)
          (fun φ => some (sourceModel.refinements.refined A φ))) = some result at evaluated
      rcases (bindResult_eq_some_iff _ _ _).mp evaluated with ⟨A, domainRead, remaining⟩
      rcases (bindResult_eq_some_iff _ _ _).mp remaining with ⟨φ, predicateRead, last⟩
      rcases evaluateType_image mapping domain Γ Γ' contexts A domainRead with
        ⟨A', domainImage, domains⟩
      rcases evaluatePredicate_image mapping predicate (Γ.snoc A) (Γ'.snoc A')
        (contexts.snoc mapping.morphism domains) φ predicateRead with
        ⟨φ', predicateImage, predicates⟩
      refine ⟨targetModel.refinements.refined A' φ',
        target.evaluate_comprehension Γ' domain predicate A' φ' domainImage predicateImage, ?_⟩
      rw [← Option.some.inj last]
      exact mapping.refinement_image contexts.contexts domains predicates

theorem evaluateTerm_image (mapping : ModelMap source target) :
    {n : Nat} → (term : TermExpr S n) → (Γ : ModelScope C sourceModel n) → (Γ' : ModelScope D targetModel n) →
    (contexts : ScopeImage mapping.morphism Γ Γ') → (value : Value C.toCwf Γ.1) →
    source.evaluateTerm Γ term = some value →
    ∃ value' : Value D.toCwf Γ'.1, target.evaluateTerm Γ' term = some value' ∧
      ValueImage mapping.morphism value value'
  | _, .var index, Γ, Γ', contexts, value, evaluated => by
      have actual : Γ.2.lookup index = value := Option.some.inj evaluated
      refine ⟨Γ'.2.lookup index, rfl, ?_⟩
      rw [← actual]
      exact contexts.variableReadouts index
  | _, .primitive symbol arguments, Γ, Γ', contexts, value, evaluated => by
      change bindResult ((source.termParameters symbol).2.assemble?
        (fun index => source.evaluateTerm Γ (arguments index)))
        (fun actual => some (source.primitiveAt symbol actual)) = some value at evaluated
      rcases (bindResult_eq_some_iff _ _ _).mp evaluated with ⟨actual, assembled, last⟩
      have actualValue : source.primitiveAt symbol actual = value := Option.some.inj last
      have argumentImages : ∀ index value,
          source.evaluateTerm Γ (arguments index) = some value →
          ∃ value', target.evaluateTerm Γ' (arguments index) = some value' ∧
            ValueImage mapping.morphism value value' := by
        intro index value read
        exact evaluateTerm_image mapping (arguments index) Γ Γ' contexts value read
      have targetAssembled := (mapping.termParameters symbol).assemble mapping.morphism
        contexts.contexts _ _ actual assembled argumentImages
      refine ⟨target.primitiveAt symbol (imageArrow mapping.morphism contexts.contexts
        (mapping.termParameters symbol).contexts actual), ?_, ?_⟩
      · change bindResult ((target.termParameters symbol).2.assemble?
          (fun index => target.evaluateTerm Γ' (arguments index))) _ = _
        rw [targetAssembled]
        rfl
      · rw [← actualValue]
        exact mapping.primitiveAt_image contexts.contexts symbol actual
  | _, .lam domain body term, Γ, Γ', contexts, value, evaluated => by
      rcases (source.dependentAnnotations_eq_some_iff Γ domain body
        (fun A B => ModelData.lambda? sourceModel A B (source.evaluateTerm (Γ.snoc A) term)) value).mp evaluated with
        ⟨A, B, domainRead, bodyRead, last⟩
      have checked := last
      rw [ModelData.lambda?] at checked
      rcases (bindResult_eq_some_iff _ _ _).mp checked with ⟨b, bodyChecked, _⟩
      have termRead := (ModelData.check?_eq_some_iff _ _ _).mp bodyChecked
      rw [termRead, ModelData.lambda?_supplied] at last
      have actualValue : (⟨sourceModel.products.pi A B, sourceModel.products.lam b⟩ : Value C.toCwf Γ.1) = value :=
        Option.some.inj last
      rcases evaluateType_image mapping domain Γ Γ' contexts A domainRead with
        ⟨A', domainImage, domains⟩
      have extended := contexts.snoc mapping.morphism domains
      rcases evaluateType_image mapping body (Γ.snoc A) (Γ'.snoc A') extended B bodyRead with
        ⟨B', bodyImage, codomains⟩
      rcases evaluateTerm_image mapping term (Γ.snoc A) (Γ'.snoc A') extended _ termRead with
        ⟨bValue', termImage, related⟩
      rcases ValueImage.at_type mapping.morphism extended.contexts codomains b bValue' related with
        ⟨b', bValueRead, bodies⟩
      rw [bValueRead] at termImage
      refine ⟨⟨targetModel.products.pi A' B', targetModel.products.lam b'⟩,
        target.evaluate_lambda Γ' domain body A' B' domainImage bodyImage term b' termImage, ?_⟩
      rw [← actualValue]
      exact mapping.lambda_image contexts.contexts domains codomains b b' bodies
  | _, .app domain body function argument, Γ, Γ', contexts, value, evaluated => by
      rcases (source.dependentAnnotations_eq_some_iff Γ domain body
        (fun A B => ModelData.application? sourceModel A B (source.evaluateTerm Γ function)
          (source.evaluateTerm Γ argument)) value).mp evaluated with
        ⟨A, B, domainRead, bodyRead, last⟩
      have checked := last
      rw [ModelData.application?] at checked
      rcases (bindResult_eq_some_iff _ _ _).mp checked with ⟨f, functionChecked, rest⟩
      rcases (bindResult_eq_some_iff _ _ _).mp rest with ⟨a, argumentChecked, _⟩
      have functionRead := (ModelData.check?_eq_some_iff _ _ _).mp functionChecked
      have argumentRead := (ModelData.check?_eq_some_iff _ _ _).mp argumentChecked
      rw [functionRead, argumentRead, ModelData.application?_supplied] at last
      rcases evaluateType_image mapping domain Γ Γ' contexts A domainRead with
        ⟨A', domainImage, domains⟩
      rcases evaluateType_image mapping body (Γ.snoc A) (Γ'.snoc A')
        (contexts.snoc mapping.morphism domains) B bodyRead with ⟨B', bodyImage, codomains⟩
      rcases evaluateTerm_image mapping function Γ Γ' contexts _ functionRead with
        ⟨fValue', functionImage, functionRelated⟩
      rcases ValueImage.at_type mapping.morphism contexts.contexts
        (mapping.logical.products.formation contexts.contexts domains codomains) f fValue' functionRelated with
        ⟨f', fValueRead, functions⟩
      rcases evaluateTerm_image mapping argument Γ Γ' contexts _ argumentRead with
        ⟨aValue', argumentImage, argumentRelated⟩
      rcases ValueImage.at_type mapping.morphism contexts.contexts domains a aValue' argumentRelated with
        ⟨a', aValueRead, arguments⟩
      rw [fValueRead] at functionImage
      rw [aValueRead] at argumentImage
      refine ⟨_, target.evaluate_application Γ' domain body A' B' domainImage bodyImage
        function argument f' a' functionImage argumentImage, ?_⟩
      rw [← Option.some.inj last]
      exact mapping.application_image contexts.contexts domains codomains f f' functions a a' arguments
  | _, .pair domain body first second, Γ, Γ', contexts, value, evaluated => by
      rcases (source.dependentAnnotations_eq_some_iff Γ domain body
        (fun A B => ModelData.pair? sourceModel A B (source.evaluateTerm Γ first) (source.evaluateTerm Γ second))
        value).mp evaluated with ⟨A, B, domainRead, bodyRead, last⟩
      have checked := last
      rw [ModelData.pair?] at checked
      rcases (bindResult_eq_some_iff _ _ _).mp checked with ⟨a, firstChecked, rest⟩
      rcases (bindResult_eq_some_iff _ _ _).mp rest with ⟨b, secondChecked, _⟩
      have firstRead := (ModelData.check?_eq_some_iff _ _ _).mp firstChecked
      have secondRead := (ModelData.check?_eq_some_iff _ _ _).mp secondChecked
      rw [firstRead, secondRead, ModelData.pair?_supplied] at last
      rcases evaluateType_image mapping domain Γ Γ' contexts A domainRead with
        ⟨A', domainImage, domains⟩
      rcases evaluateType_image mapping body (Γ.snoc A) (Γ'.snoc A')
        (contexts.snoc mapping.morphism domains) B bodyRead with ⟨B', bodyImage, codomains⟩
      rcases evaluateTerm_image mapping first Γ Γ' contexts _ firstRead with
        ⟨aValue', firstImage, firstRelated⟩
      rcases ValueImage.at_type mapping.morphism contexts.contexts domains a aValue' firstRelated with
        ⟨a', aValueRead, firsts⟩
      have secondTypes := substituted_type_heq mapping.morphism contexts.contexts
        (extension_images mapping.morphism contexts.contexts domains) codomains
        (self_extension_heq mapping.morphism contexts.contexts domains a a' firsts)
      rcases evaluateTerm_image mapping second Γ Γ' contexts _ secondRead with
        ⟨bValue', secondImage, secondRelated⟩
      rcases ValueImage.at_type mapping.morphism contexts.contexts secondTypes b bValue' secondRelated with
        ⟨b', bValueRead, seconds⟩
      rw [aValueRead] at firstImage
      rw [bValueRead] at secondImage
      refine ⟨_, target.evaluate_pair Γ' domain body A' B' domainImage bodyImage
        first second a' b' firstImage secondImage, ?_⟩
      rw [← Option.some.inj last]
      exact mapping.pair_image contexts.contexts domains codomains a a' firsts b b' seconds
  | _, .fst domain body pair, Γ, Γ', contexts, value, evaluated => by
      rcases (source.dependentAnnotations_eq_some_iff Γ domain body
        (fun A B => ModelData.first? sourceModel A B (source.evaluateTerm Γ pair)) value).mp evaluated with
        ⟨A, B, domainRead, bodyRead, last⟩
      have checked := last
      rw [ModelData.first?] at checked
      rcases (bindResult_eq_some_iff _ _ _).mp checked with ⟨p, pairChecked, _⟩
      have pairRead := (ModelData.check?_eq_some_iff _ _ _).mp pairChecked
      rw [pairRead, ModelData.first?_supplied] at last
      rcases evaluateType_image mapping domain Γ Γ' contexts A domainRead with
        ⟨A', domainImage, domains⟩
      rcases evaluateType_image mapping body (Γ.snoc A) (Γ'.snoc A')
        (contexts.snoc mapping.morphism domains) B bodyRead with ⟨B', bodyImage, codomains⟩
      rcases evaluateTerm_image mapping pair Γ Γ' contexts _ pairRead with
        ⟨pValue', pairImage, pairRelated⟩
      rcases ValueImage.at_type mapping.morphism contexts.contexts
        (mapping.logical.sums.formation contexts.contexts domains codomains) p pValue' pairRelated with
        ⟨p', pValueRead, pairs⟩
      rw [pValueRead] at pairImage
      refine ⟨_, target.evaluate_first Γ' domain body A' B' domainImage bodyImage pair p' pairImage, ?_⟩
      rw [← Option.some.inj last]
      exact mapping.first_image contexts.contexts domains codomains p p' pairs
  | _, .snd domain body pair, Γ, Γ', contexts, value, evaluated => by
      rcases (source.dependentAnnotations_eq_some_iff Γ domain body
        (fun A B => ModelData.second? sourceModel A B (source.evaluateTerm Γ pair)) value).mp evaluated with
        ⟨A, B, domainRead, bodyRead, last⟩
      have checked := last
      rw [ModelData.second?] at checked
      rcases (bindResult_eq_some_iff _ _ _).mp checked with ⟨p, pairChecked, _⟩
      have pairRead := (ModelData.check?_eq_some_iff _ _ _).mp pairChecked
      rw [pairRead, ModelData.second?_supplied] at last
      rcases evaluateType_image mapping domain Γ Γ' contexts A domainRead with
        ⟨A', domainImage, domains⟩
      rcases evaluateType_image mapping body (Γ.snoc A) (Γ'.snoc A')
        (contexts.snoc mapping.morphism domains) B bodyRead with ⟨B', bodyImage, codomains⟩
      rcases evaluateTerm_image mapping pair Γ Γ' contexts _ pairRead with
        ⟨pValue', pairImage, pairRelated⟩
      rcases ValueImage.at_type mapping.morphism contexts.contexts
        (mapping.logical.sums.formation contexts.contexts domains codomains) p pValue' pairRelated with
        ⟨p', pValueRead, pairs⟩
      rw [pValueRead] at pairImage
      refine ⟨_, target.evaluate_second Γ' domain body A' B' domainImage bodyImage pair p' pairImage, ?_⟩
      rw [← Option.some.inj last]
      exact mapping.second_image contexts.contexts domains codomains p p' pairs
  | _, .sigmaElim domain body motive branch pair, Γ, Γ', contexts, value, evaluated => by
      rcases (source.dependentAnnotations_eq_some_iff Γ domain body
        (fun A B => bindResult (source.evaluateType
          (Γ.snoc (sourceModel.sums.operations.sigma A B)) motive) (fun M =>
          ModelData.sumEliminate? sourceModel A B M (source.evaluateTerm ((Γ.snoc A).snoc B) branch)
            (source.evaluateTerm Γ pair))) value).mp evaluated with
        ⟨A, B, domainRead, bodyRead, motiveStep⟩
      rcases (bindResult_eq_some_iff _ _ _).mp motiveStep with ⟨M, motiveEvaluated, last⟩
      have checked := last
      rw [ModelData.sumEliminate?] at checked
      rcases (bindResult_eq_some_iff _ _ _).mp checked with ⟨b, branchChecked, rest⟩
      rcases (bindResult_eq_some_iff _ _ _).mp rest with ⟨p, pairChecked, _⟩
      have branchRead := (ModelData.check?_eq_some_iff _ _ _).mp branchChecked
      have pairRead := (ModelData.check?_eq_some_iff _ _ _).mp pairChecked
      rw [branchRead, pairRead, ModelData.sumEliminate?_supplied] at last
      rcases evaluateType_image mapping domain Γ Γ' contexts A domainRead with
        ⟨A', domainImage, domains⟩
      have extended := contexts.snoc mapping.morphism domains
      rcases evaluateType_image mapping body (Γ.snoc A) (Γ'.snoc A') extended B bodyRead with
        ⟨B', bodyImage, codomains⟩
      have sumsImage := mapping.logical.sums.formation contexts.contexts domains codomains
      have sumContexts := contexts.snoc mapping.morphism sumsImage
      rcases evaluateType_image mapping motive _ _ sumContexts M motiveEvaluated with
        ⟨M', motiveImage, motives⟩
      have tupleContexts := extended.snoc mapping.morphism codomains
      have branchTypes := substituted_type_heq mapping.morphism tupleContexts.contexts
        sumContexts.contexts motives
        (pack_heq mapping.morphism sourceModel.sums targetModel.sums mapping.logical.sums
          contexts.contexts domains codomains)
      rcases evaluateTerm_image mapping branch _ _ tupleContexts _ branchRead with
        ⟨bValue', branchImage, branchRelated⟩
      rcases ValueImage.at_type mapping.morphism tupleContexts.contexts branchTypes b bValue' branchRelated with
        ⟨b', bValueRead, bodies⟩
      rcases evaluateTerm_image mapping pair Γ Γ' contexts _ pairRead with
        ⟨pValue', pairImage, pairRelated⟩
      rcases ValueImage.at_type mapping.morphism contexts.contexts sumsImage p pValue' pairRelated with
        ⟨p', pValueRead, pairs⟩
      rw [bValueRead] at branchImage
      rw [pValueRead] at pairImage
      refine ⟨_, target.evaluate_sumElimination Γ' domain body A' B' domainImage bodyImage
        motive branch pair M' b' p' motiveImage branchImage pairImage, ?_⟩
      rw [← Option.some.inj last]
      exact mapping.sumElimination_image contexts.contexts domains codomains M M' motives b b' bodies p p' pairs
  | _, .quote predicate, Γ, Γ', contexts, value, evaluated => by
      change bindResult (source.evaluatePredicate Γ predicate)
        (fun φ => some (⟨sourceModel.propositions.omega Γ.1,
          sourceModel.propositions.quote φ⟩ : Value C.toCwf Γ.1)) = some value at evaluated
      rcases (bindResult_eq_some_iff _ _ _).mp evaluated with ⟨φ, predicateRead, last⟩
      rcases evaluatePredicate_image mapping predicate Γ Γ' contexts φ predicateRead with
        ⟨φ', predicateImage, predicates⟩
      refine ⟨_, target.evaluate_quote Γ' predicate φ' predicateImage, ?_⟩
      rw [← Option.some.inj last]
      exact mapping.quote_image contexts.contexts predicates
  | _, .refine domain predicate term, Γ, Γ', contexts, value, evaluated => by
      change bindResult (source.evaluateType Γ domain) (fun A =>
        bindResult (source.evaluatePredicate (Γ.snoc A) predicate)
          (fun φ => ModelData.refine? sourceModel A φ (source.evaluateTerm Γ term))) =
            some value at evaluated
      rcases (bindResult_eq_some_iff _ _ _).mp evaluated with ⟨A, domainRead, remaining⟩
      rcases (bindResult_eq_some_iff _ _ _).mp remaining with ⟨φ, predicateRead, last⟩
      rcases evaluateType_image mapping domain Γ Γ' contexts A domainRead with
        ⟨A', domainImage, domains⟩
      rcases evaluatePredicate_image mapping predicate (Γ.snoc A) (Γ'.snoc A')
        (contexts.snoc mapping.morphism domains) φ predicateRead with
        ⟨φ', predicateImage, predicates⟩
      have termImages : ∀ value, source.evaluateTerm Γ term = some value →
          ∃ value', target.evaluateTerm Γ' term = some value' ∧
            ValueImage mapping.morphism value value' := by
        intro value read
        exact evaluateTerm_image mapping term Γ Γ' contexts value read
      rcases mapping.refinementCheck_image (contexts := contexts.contexts) (types := domains)
        (result := source.evaluateTerm Γ term) (result' := target.evaluateTerm Γ' term)
        (values := termImages) (predicates := predicates) value last with
          ⟨value', targetChecked, related⟩
      refine ⟨value', ?_, related⟩
      change bindResult (target.evaluateType Γ' domain) (fun A =>
        bindResult (target.evaluatePredicate (Γ'.snoc A) predicate)
          (fun φ => ModelData.refine? targetModel A φ (target.evaluateTerm Γ' term))) = _
      rw [domainImage]
      change bindResult (target.evaluatePredicate (Γ'.snoc A') predicate) _ = _
      rw [predicateImage]
      exact targetChecked
  | _, .forget domain predicate term, Γ, Γ', contexts, value, evaluated => by
      change bindResult (source.evaluateType Γ domain) (fun A =>
        bindResult (source.evaluatePredicate (Γ.snoc A) predicate)
          (fun φ => ModelData.forget? sourceModel A φ (source.evaluateTerm Γ term))) =
            some value at evaluated
      rcases (bindResult_eq_some_iff _ _ _).mp evaluated with ⟨A, domainRead, remaining⟩
      rcases (bindResult_eq_some_iff _ _ _).mp remaining with ⟨φ, predicateRead, last⟩
      rcases evaluateType_image mapping domain Γ Γ' contexts A domainRead with
        ⟨A', domainImage, domains⟩
      rcases evaluatePredicate_image mapping predicate (Γ.snoc A) (Γ'.snoc A')
        (contexts.snoc mapping.morphism domains) φ predicateRead with
        ⟨φ', predicateImage, predicates⟩
      have termImages : ∀ value, source.evaluateTerm Γ term = some value →
          ∃ value', target.evaluateTerm Γ' term = some value' ∧
            ValueImage mapping.morphism value value' := by
        intro value read
        exact evaluateTerm_image mapping term Γ Γ' contexts value read
      rcases mapping.forgettingCheck_image (contexts := contexts.contexts) (types := domains)
        (result := source.evaluateTerm Γ term) (result' := target.evaluateTerm Γ' term)
        (predicates := predicates) termImages value last with ⟨value', targetChecked, related⟩
      refine ⟨value', ?_, related⟩
      change bindResult (target.evaluateType Γ' domain) (fun A =>
        bindResult (target.evaluatePredicate (Γ'.snoc A) predicate)
          (fun φ => ModelData.forget? targetModel A φ (target.evaluateTerm Γ' term))) = _
      rw [domainImage]
      change bindResult (target.evaluatePredicate (Γ'.snoc A') predicate) _ = _
      rw [predicateImage]
      exact targetChecked

theorem evaluatePredicate_image (mapping : ModelMap source target) :
    {n : Nat} → (predicate : PropExpr S n) → (Γ : ModelScope C sourceModel n) →
    (Γ' : ModelScope D targetModel n) → (contexts : ScopeImage mapping.morphism Γ Γ') →
    (φ : sourceModel.doctrine.Predicate Γ.1) → source.evaluatePredicate Γ predicate = some φ →
    ∃ φ' : targetModel.doctrine.Predicate Γ'.1, target.evaluatePredicate Γ' predicate = some φ' ∧
      HEq (mapping.predicates.doctrine.hom Γ.1 φ) φ'
  | _, .atom symbol arguments, Γ, Γ', contexts, predicate, evaluated => by
      change bindResult ((source.predicateParameters symbol).2.assemble?
        (fun index => source.evaluateTerm Γ (arguments index)))
        (fun actual => some (source.predicateAt symbol actual)) = some predicate at evaluated
      rcases (bindResult_eq_some_iff _ _ _).mp evaluated with ⟨actual, assembled, last⟩
      have argumentImages : ∀ index value,
          source.evaluateTerm Γ (arguments index) = some value →
          ∃ value', target.evaluateTerm Γ' (arguments index) = some value' ∧
            ValueImage mapping.morphism value value' := by
        intro index value read
        exact evaluateTerm_image mapping (arguments index) Γ Γ' contexts value read
      have targetAssembled := (mapping.predicateParameters symbol).assemble mapping.morphism
        contexts.contexts _ _ actual assembled argumentImages
      refine ⟨target.predicateAt symbol (imageArrow mapping.morphism contexts.contexts
        (mapping.predicateParameters symbol).contexts actual), ?_, ?_⟩
      · change bindResult ((target.predicateParameters symbol).2.assemble?
          (fun index => target.evaluateTerm Γ' (arguments index))) _ = _
        rw [targetAssembled]
        rfl
      · rw [← Option.some.inj last]
        exact mapping.predicateAt_image contexts.contexts symbol actual
  | _, .truth, Γ, Γ', contexts, predicate, evaluated => by
      change some (⊤ : sourceModel.doctrine.Predicate Γ.1) = some predicate at evaluated
      refine ⟨⊤, rfl, ?_⟩
      rw [← Option.some.inj evaluated]
      exact mapping.truth_image contexts.contexts
  | _, .falsehood, Γ, Γ', contexts, predicate, evaluated => by
      change some (⊥ : sourceModel.doctrine.Predicate Γ.1) = some predicate at evaluated
      refine ⟨⊥, rfl, ?_⟩
      rw [← Option.some.inj evaluated]
      exact mapping.falsehood_image contexts.contexts
  | _, .and first second, Γ, Γ', contexts, predicate, evaluated => by
      change bindResult (source.evaluatePredicate Γ first) (fun φ =>
        bindResult (source.evaluatePredicate Γ second) (fun ψ => some (φ ⊓ ψ))) =
          some predicate at evaluated
      rcases (bindResult_eq_some_iff _ _ _).mp evaluated with ⟨φ, firstRead, remaining⟩
      rcases (bindResult_eq_some_iff _ _ _).mp remaining with ⟨ψ, secondRead, last⟩
      rcases evaluatePredicate_image mapping first Γ Γ' contexts φ firstRead with
        ⟨φ', firstImage, firsts⟩
      rcases evaluatePredicate_image mapping second Γ Γ' contexts ψ secondRead with
        ⟨ψ', secondImage, seconds⟩
      refine ⟨φ' ⊓ ψ', target.evaluate_and Γ' first second φ' ψ' firstImage secondImage, ?_⟩
      rw [← Option.some.inj last]
      exact mapping.and_image contexts.contexts firsts seconds
  | _, .or first second, Γ, Γ', contexts, predicate, evaluated => by
      change bindResult (source.evaluatePredicate Γ first) (fun φ =>
        bindResult (source.evaluatePredicate Γ second) (fun ψ => some (φ ⊔ ψ))) =
          some predicate at evaluated
      rcases (bindResult_eq_some_iff _ _ _).mp evaluated with ⟨φ, firstRead, remaining⟩
      rcases (bindResult_eq_some_iff _ _ _).mp remaining with ⟨ψ, secondRead, last⟩
      rcases evaluatePredicate_image mapping first Γ Γ' contexts φ firstRead with
        ⟨φ', firstImage, firsts⟩
      rcases evaluatePredicate_image mapping second Γ Γ' contexts ψ secondRead with
        ⟨ψ', secondImage, seconds⟩
      refine ⟨φ' ⊔ ψ', target.evaluate_or Γ' first second φ' ψ' firstImage secondImage, ?_⟩
      rw [← Option.some.inj last]
      exact mapping.or_image contexts.contexts firsts seconds
  | _, .implies first second, Γ, Γ', contexts, predicate, evaluated => by
      change bindResult (source.evaluatePredicate Γ first) (fun φ =>
        bindResult (source.evaluatePredicate Γ second) (fun ψ => some (φ ⇨ ψ))) =
          some predicate at evaluated
      rcases (bindResult_eq_some_iff _ _ _).mp evaluated with ⟨φ, firstRead, remaining⟩
      rcases (bindResult_eq_some_iff _ _ _).mp remaining with ⟨ψ, secondRead, last⟩
      rcases evaluatePredicate_image mapping first Γ Γ' contexts φ firstRead with
        ⟨φ', firstImage, firsts⟩
      rcases evaluatePredicate_image mapping second Γ Γ' contexts ψ secondRead with
        ⟨ψ', secondImage, seconds⟩
      refine ⟨φ' ⇨ ψ', target.evaluate_implies Γ' first second φ' ψ' firstImage secondImage, ?_⟩
      rw [← Option.some.inj last]
      exact mapping.implication_image contexts.contexts firsts seconds
  | _, .all domain predicate, Γ, Γ', contexts, result, evaluated => by
      change bindResult (source.evaluateType Γ domain) (fun A =>
        bindResult (source.evaluatePredicate (Γ.snoc A) predicate)
          (fun φ => some (sourceModel.doctrine.all A φ))) = some result at evaluated
      rcases (bindResult_eq_some_iff _ _ _).mp evaluated with ⟨A, domainRead, remaining⟩
      rcases (bindResult_eq_some_iff _ _ _).mp remaining with ⟨φ, predicateRead, last⟩
      rcases evaluateType_image mapping domain Γ Γ' contexts A domainRead with
        ⟨A', domainImage, domains⟩
      rcases evaluatePredicate_image mapping predicate (Γ.snoc A) (Γ'.snoc A')
        (contexts.snoc mapping.morphism domains) φ predicateRead with
        ⟨φ', predicateImage, predicates⟩
      refine ⟨targetModel.doctrine.all A' φ',
        target.evaluate_all Γ' domain predicate A' φ' domainImage predicateImage, ?_⟩
      rw [← Option.some.inj last]
      exact mapping.all_image contexts.contexts domains predicates
  | _, .exists domain predicate, Γ, Γ', contexts, result, evaluated => by
      change bindResult (source.evaluateType Γ domain) (fun A =>
        bindResult (source.evaluatePredicate (Γ.snoc A) predicate)
          (fun φ => some (sourceModel.doctrine.some A φ))) = some result at evaluated
      rcases (bindResult_eq_some_iff _ _ _).mp evaluated with ⟨A, domainRead, remaining⟩
      rcases (bindResult_eq_some_iff _ _ _).mp remaining with ⟨φ, predicateRead, last⟩
      rcases evaluateType_image mapping domain Γ Γ' contexts A domainRead with
        ⟨A', domainImage, domains⟩
      rcases evaluatePredicate_image mapping predicate (Γ.snoc A) (Γ'.snoc A')
        (contexts.snoc mapping.morphism domains) φ predicateRead with
        ⟨φ', predicateImage, predicates⟩
      refine ⟨targetModel.doctrine.some A' φ',
        target.evaluate_exists Γ' domain predicate A' φ' domainImage predicateImage, ?_⟩
      rw [← Option.some.inj last]
      exact mapping.exists_image contexts.contexts domains predicates
  | _, .holds term, Γ, Γ', contexts, result, evaluated => by
      change bindResult (ModelData.check? (source.evaluateTerm Γ term)
        (sourceModel.propositions.omega Γ.1))
          (fun value => some (sourceModel.propositions.holds value)) = some result at evaluated
      rcases (bindResult_eq_some_iff _ _ _).mp evaluated with ⟨value, checked, last⟩
      have termRead := (ModelData.check?_eq_some_iff _ _ _).mp checked
      rcases evaluateTerm_image mapping term Γ Γ' contexts _ termRead with
        ⟨value', termImage, related⟩
      rcases ValueImage.at_type mapping.morphism contexts.contexts
        (mapping.proposition_image contexts.contexts) value value' related with
          ⟨term', valueRead, terms⟩
      rw [valueRead] at termImage
      refine ⟨targetModel.propositions.holds term', target.evaluate_holds Γ' term term' termImage, ?_⟩
      rw [← Option.some.inj last]
      exact mapping.holds_image contexts.contexts value term' terms
  | _, .image type, Γ, Γ', contexts, result, evaluated => by
      change bindResult (source.evaluateType Γ type)
        (fun A => some (sourceModel.doctrine.some A ⊤)) = some result at evaluated
      rcases (bindResult_eq_some_iff _ _ _).mp evaluated with ⟨A, typeRead, last⟩
      rcases evaluateType_image mapping type Γ Γ' contexts A typeRead with
        ⟨A', typeImage, types⟩
      refine ⟨targetModel.doctrine.some A' ⊤, target.evaluate_image Γ' type A' typeImage, ?_⟩
      rw [← Option.some.inj last]
      exact mapping.exists_image contexts.contexts types
        (mapping.truth_image (extension_images mapping.morphism contexts.contexts types))

end

end ModelMap

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Abstract
