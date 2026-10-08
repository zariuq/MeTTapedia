import Mettapedia.TypeTheory.Calculi.NativeDependent.ExternalModelMap

/-!
# External interpretation commutes with local model maps

Mutual induction visits the independent raw type and term syntax, including
every primitive argument, binder annotation and complete sum motive.
Successful source readouts commute using only the local contextual,
logical-constructor and primitive-meaning capabilities. Failed source
checks are not reflected by an arbitrary noninjective model map.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.External

open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.ContextualModelTelescopes
open Mettapedia.TypeTheory.ContextualComprehensionMorphism
open Mettapedia.TypeTheory.ContextualTelescopeMorphism
open Mettapedia.TypeTheory.ContextualLogicalMorphism
open Mettapedia.TypeTheory.ContextualSumComprehension
open Mettapedia.TypeTheory.ContextualProductComparison (selfExtend)
open Mettapedia.TypeTheory.ContextualTypeOperations

universe a c s t m

variable {S : Symbols.{a}} {C D : CwfWithTerminal.{c, s, t, m}}
  {source : ModelData S C} {target : ModelData S D}

namespace ModelMap

mutual

theorem evaluateType_image (mapping : ModelMap source target) :
    {n : Nat} → (type : TypeExpr S n) → (Γ : Context C n) → (Γ' : Context D n) →
    (contexts : ContextImage mapping.morphism Γ Γ') → (A : C.toCwf.Ty Γ.1) →
    source.evaluateType Γ type = some A →
    ∃ A' : D.toCwf.Ty Γ'.1, target.evaluateType Γ' type = some A' ∧
      HEq (mapping.morphism.toFamilyMorphism.mapType A) A'
  | _, .family symbol arguments, Γ, Γ', contexts, A, evaluated => by
      have lifted := (source.evaluateType_eq_some_iff _ _ _).mp evaluated
      rw [ModelData.evaluateTypeLifted] at lifted
      rcases (bindResult_eq_some_iff _ _ _).mp lifted with ⟨actual, assembled, last⟩
      have actualType : source.familyAt symbol actual = A :=
        congrArg ULift.down (Option.some.inj last)
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
      · apply (target.evaluateType_eq_some_iff _ _ _).mpr
        simp only [ModelData.evaluateTypeLifted, targetAssembled, bindResult_some]
      · rw [← actualType]
        exact mapping.familyAt_image contexts.contexts symbol actual
  | _, .pi domain body, Γ, Γ', contexts, result, evaluated => by
      have lifted := (source.evaluateType_eq_some_iff _ _ _).mp evaluated
      rcases (source.dependentAnnotations_eq_some_iff Γ domain body
        (fun A B => some (ULift.up (source.products.pi A B))) (ULift.up result)).mp lifted with
        ⟨A, B, domainRead, bodyRead, last⟩
      have actualType : source.products.pi A B = result :=
        congrArg ULift.down (Option.some.inj last)
      rcases evaluateType_image mapping domain Γ Γ' contexts A domainRead with
        ⟨A', domainImage, domains⟩
      rcases evaluateType_image mapping body (Γ.snoc A) (Γ'.snoc A')
        (contexts.snoc mapping.morphism domains) B bodyRead with ⟨B', bodyImage, codomains⟩
      refine ⟨target.products.pi A' B', target.evaluate_pi Γ' domain body A' B' domainImage bodyImage, ?_⟩
      rw [← actualType]
      exact mapping.logical.products.formation contexts.contexts domains codomains
  | _, .sigma domain body, Γ, Γ', contexts, result, evaluated => by
      have lifted := (source.evaluateType_eq_some_iff _ _ _).mp evaluated
      rcases (source.dependentAnnotations_eq_some_iff Γ domain body
        (fun A B => some (ULift.up (source.sums.operations.sigma A B))) (ULift.up result)).mp lifted with
        ⟨A, B, domainRead, bodyRead, last⟩
      have actualType : source.sums.operations.sigma A B = result :=
        congrArg ULift.down (Option.some.inj last)
      rcases evaluateType_image mapping domain Γ Γ' contexts A domainRead with
        ⟨A', domainImage, domains⟩
      rcases evaluateType_image mapping body (Γ.snoc A) (Γ'.snoc A')
        (contexts.snoc mapping.morphism domains) B bodyRead with ⟨B', bodyImage, codomains⟩
      refine ⟨target.sums.operations.sigma A' B',
        target.evaluate_sigma Γ' domain body A' B' domainImage bodyImage, ?_⟩
      rw [← actualType]
      exact mapping.logical.sums.formation contexts.contexts domains codomains

theorem evaluateTerm_image (mapping : ModelMap source target) :
    {n : Nat} → (term : TermExpr S n) → (Γ : Context C n) → (Γ' : Context D n) →
    (contexts : ContextImage mapping.morphism Γ Γ') → (value : Value C.toCwf Γ.1) →
    source.evaluateTerm Γ term = some value →
    ∃ value' : Value D.toCwf Γ'.1, target.evaluateTerm Γ' term = some value' ∧
      ValueImage mapping.morphism value value'
  | _, .var index, Γ, Γ', contexts, value, evaluated => by
      have actual : Γ.2.lookup index = value := Option.some.inj evaluated
      refine ⟨Γ'.2.lookup index, rfl, ?_⟩
      rw [← actual]
      exact contexts.variableReadouts index
  | _, .primitive symbol arguments, Γ, Γ', contexts, value, evaluated => by
      rw [ModelData.evaluateTerm] at evaluated
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
      · simp only [ModelData.evaluateTerm, targetAssembled, bindResult_some]
      · rw [← actualValue]
        exact mapping.primitiveAt_image contexts.contexts symbol actual
  | _, .lam domain body term, Γ, Γ', contexts, value, evaluated => by
      rcases (source.dependentAnnotations_eq_some_iff Γ domain body
        (fun A B => source.lambda? A B (source.evaluateTerm (Γ.snoc A) term)) value).mp evaluated with
        ⟨A, B, domainRead, bodyRead, last⟩
      have checked := last
      rw [ModelData.lambda?] at checked
      rcases (bindResult_eq_some_iff _ _ _).mp checked with ⟨b, bodyChecked, _⟩
      have termRead := (ModelData.check?_eq_some_iff _ _ _).mp bodyChecked
      rw [termRead, ModelData.lambda?_supplied] at last
      have actualValue : (⟨source.products.pi A B, source.products.lam b⟩ : Value C.toCwf Γ.1) = value :=
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
      refine ⟨⟨target.products.pi A' B', target.products.lam b'⟩,
        target.evaluate_lambda Γ' domain body A' B' domainImage bodyImage term b' termImage, ?_⟩
      rw [← actualValue]
      exact mapping.lambda_image contexts.contexts domains codomains b b' bodies
  | _, .app domain body function argument, Γ, Γ', contexts, value, evaluated => by
      rcases (source.dependentAnnotations_eq_some_iff Γ domain body
        (fun A B => source.application? A B (source.evaluateTerm Γ function)
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
        (fun A B => source.pair? A B (source.evaluateTerm Γ first) (source.evaluateTerm Γ second))
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
        (fun A B => source.first? A B (source.evaluateTerm Γ pair)) value).mp evaluated with
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
        (fun A B => source.second? A B (source.evaluateTerm Γ pair)) value).mp evaluated with
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
        (fun A B => bindResult (source.evaluateTypeLifted
          (Γ.snoc (source.sums.operations.sigma A B)) motive) (fun M =>
          source.sumEliminate? A B M.down (source.evaluateTerm ((Γ.snoc A).snoc B) branch)
            (source.evaluateTerm Γ pair))) value).mp evaluated with
        ⟨A, B, domainRead, bodyRead, motiveStep⟩
      rcases (bindResult_eq_some_iff _ _ _).mp motiveStep with ⟨liftedM, motiveRead, last⟩
      let M := liftedM.down
      have motiveEvaluated : source.evaluateType (Γ.snoc (source.sums.operations.sigma A B)) motive = some M :=
        (source.evaluateType_eq_some_iff _ _ _).mpr motiveRead
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
        (pack_heq mapping.morphism source.sums target.sums mapping.logical.sums
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

end

end ModelMap

end Mettapedia.TypeTheory.Calculi.NativeDependent.External
