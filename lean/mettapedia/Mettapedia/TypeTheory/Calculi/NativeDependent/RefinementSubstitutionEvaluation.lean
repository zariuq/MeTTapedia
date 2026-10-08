import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementSubstitutionInterpretation
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementPredicateCommutation

/-!
# Interpretation commutes with authored substitution

Mutual induction traverses every independent type, term and predicate
constructor. Successful evaluation commutes with a supplied raw substitution
whose components evaluate to one actual map, including all target assumptions. Binder maps, dependent pair witnesses and
full sum motives use their earned contextual substitution equations.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement

open _root_.CategoryTheory
open NativeLocalTypeFormers PresheafNativePropositionReadout
open PresheafNativePropositionSubstitution PresheafNativeRefinementTermSubstitution
open PresheafNativePredicateQuantifierSubstitution
open Mettapedia.GSLT.Topos
open External (bindResult bindResult_eq_some_iff)
open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.ContextualModelTelescopes
open Mettapedia.TypeTheory.ContextualSumComprehension
open Mettapedia.TypeTheory.ContextualProductComparison (selfExtend)
open Mettapedia.TypeTheory.ContextualTypeOperations

universe u v

variable {S : Symbols.{v}} {C : Type u} [Category.{u} C]

namespace ModelData

attribute [local irreducible] products sums ContextualSumComprehension.normalize
  ContextualSumComprehension.reindexBody TypeOver.extensionSubstitution

set_option backward.isDefEq.respectTransparency false in
mutual

theorem evaluateType_substitute (model : ModelData S C) (stable : StrictPiSubstitution model.products) :
    {n k : Nat} → (type : TypeExpr S n) → (Γ : Scope C k) → (Δ : Scope C n) →
    (substitution : Substitution S n k) → (modelMap : ModelSubstitution model Γ Δ substitution) →
    (A : (NativeModel C).toCwf.Ty Δ.1) → model.evaluateType Δ type = some A →
    model.evaluateType Γ (type.substitute substitution) = some ((NativeModel C).toCwf.tySub A modelMap.arrow)
  | _, _, .family symbol arguments, Γ, Δ, substitution, modelMap, A, evaluated => by
      rw [evaluateType] at evaluated
      rcases (bindResult_eq_some_iff _ _ _).mp evaluated with ⟨actual, assembled, last⟩
      have sourceType : model.familyAt symbol actual = A :=
        Option.some.inj last
      have argumentsRead := ScopeData.assemble?_sound _ _ actual assembled
      have targetRead : ∀ index, model.evaluateTerm Γ ((arguments index).substitute substitution) =
          some ((model.typeParameters symbol).2.components
            (modelMap.arrow ≫ actual) index) := by
        intro index
        rw [ScopeData.components_composition]
        exact evaluateTerm_substitute model stable (arguments index) Γ Δ substitution modelMap _
          (argumentsRead index)
      rw [TypeExpr.substitute, ← sourceType]
      change model.evaluateType Γ (.family symbol fun index => (arguments index).substitute substitution) =
        some ((model.familyAt symbol actual).reindex modelMap.arrow)
      rw [model.familyAt_substitution]
      exact model.evaluate_family Γ _ _ _ targetRead
  | _, _, .pi domain body, Γ, Δ, substitution, modelMap, result, evaluated => by
      rcases (model.dependentAnnotations_eq_some_iff Δ domain body
        (fun A B => some (model.products.pi A B)) result).mp evaluated with
        ⟨A, B, domainRead, bodyRead, last⟩
      have sourceType : model.products.pi A B = result := Option.some.inj last
      have domainRenamed := evaluateType_substitute model stable domain Γ Δ substitution modelMap A domainRead
      have bodyRenamed := evaluateType_substitute model stable body _ _ (liftSubstitution substitution)
        (modelMap.lift stable A) B bodyRead
      rw [TypeExpr.substitute, ← sourceType, stable.1]
      exact model.evaluate_pi Γ _ _ _ _ domainRenamed bodyRenamed
  | _, _, .sigma domain body, Γ, Δ, substitution, modelMap, result, evaluated => by
      rcases (model.dependentAnnotations_eq_some_iff Δ domain body
        (fun A B => some (model.sums.operations.sigma A B)) result).mp evaluated with
        ⟨A, B, domainRead, bodyRead, last⟩
      have sourceType : model.sums.operations.sigma A B = result :=
        Option.some.inj last
      have domainRenamed := evaluateType_substitute model stable domain Γ Δ substitution modelMap A domainRead
      have bodyRenamed := evaluateType_substitute model stable body _ _ (liftSubstitution substitution)
        (modelMap.lift stable A) B bodyRead
      rw [TypeExpr.substitute, ← sourceType, model.sums.substitution.1]
      exact model.evaluate_sigma Γ _ _ _ _ domainRenamed bodyRenamed

  | _, _, .propositions, Γ, Δ, substitution, modelMap, result, evaluated => by
      have actual : nativeOmega Δ.1 = result := Option.some.inj evaluated
      rw [TypeExpr.substitute, evaluateType, ← actual]
      exact congrArg some (nativeOmega_reindex modelMap.arrow).symm
  | _, _, .comprehension domain predicate, Γ, Δ, substitution, modelMap, result, evaluated => by
      rw [evaluateType] at evaluated
      rcases (bindResult_eq_some_iff _ _ _).mp evaluated with ⟨A, domainRead, rest⟩
      change bindResult (model.evaluatePredicate (Δ.snoc A) predicate) _ = some result at rest
      rcases (bindResult_eq_some_iff _ _ _).mp rest with ⟨φ, predicateRead, last⟩
      have actual : PresheafNativeStableRefinement.chosen A φ = result := Option.some.inj last
      have domainRenamed := evaluateType_substitute model stable domain Γ Δ substitution modelMap A domainRead
      have predicateRenamed := evaluatePredicate_substitute model stable predicate _ _
        (liftSubstitution substitution) (modelMap.lift stable A) φ predicateRead
      change model.evaluatePredicate (Γ.snoc ((NativeModel C).toCwf.tySub A modelMap.arrow))
        (predicate.substitute (liftSubstitution substitution)) =
          some (φ.preimage (TypeOver.extensionSubstitution (C := (NativeModel C).toCwf)
            modelMap.arrow A)) at predicateRenamed
      rw [NativeLocalTypeOperations.local_extensionSubstitution] at predicateRenamed
      rw [TypeExpr.substitute, ← actual]
      change model.evaluateType Γ
        (.comprehension (domain.substitute substitution) (predicate.substitute (liftSubstitution substitution))) =
          some ((PresheafNativeStableRefinement.chosen A φ).reindex modelMap.arrow)
      rw [PresheafNativeStableRefinement.chosen_reindex]
      exact model.evaluate_comprehension Γ _ _ _ _ domainRenamed predicateRenamed

theorem evaluateTerm_substitute (model : ModelData S C) (stable : StrictPiSubstitution model.products) :
    {n k : Nat} → (term : TermExpr S n) → (Γ : Scope C k) → (Δ : Scope C n) →
    (substitution : Substitution S n k) → (modelMap : ModelSubstitution model Γ Δ substitution) →
    (value : Value ((NativeModel C).toCwf) Δ.1) → model.evaluateTerm Δ term = some value →
    model.evaluateTerm Γ (term.substitute substitution) = some (value.substitute modelMap.arrow)
  | _, _, .var index, Γ, Δ, substitution, modelMap, value, evaluated => by
      have actual : Δ.2.lookup index = value := Option.some.inj evaluated
      rw [TermExpr.substitute, modelMap.readout, actual]
  | _, _, .primitive symbol arguments, Γ, Δ, substitution, modelMap, value, evaluated => by
      rw [evaluateTerm] at evaluated
      rcases (bindResult_eq_some_iff _ _ _).mp evaluated with ⟨actual, assembled, last⟩
      have actualValue : model.primitiveAt symbol actual = value := Option.some.inj last
      have argumentsRead := ScopeData.assemble?_sound _ _ actual assembled
      have targetRead : ∀ index, model.evaluateTerm Γ ((arguments index).substitute substitution) =
          some ((model.termParameters symbol).2.components
            (modelMap.arrow ≫ actual) index) := by
        intro index
        rw [ScopeData.components_composition]
        exact evaluateTerm_substitute model stable (arguments index) Γ Δ substitution modelMap _
          (argumentsRead index)
      rw [TermExpr.substitute, ← actualValue, model.primitiveAt_substitution]
      exact model.evaluate_primitive Γ _ _ _ targetRead
  | _, _, .lam domain body term, Γ, Δ, substitution, modelMap, value, evaluated => by
      rcases (model.dependentAnnotations_eq_some_iff Δ domain body
        (fun A B => model.lambda? A B (model.evaluateTerm (Δ.snoc A) term)) value).mp evaluated with
        ⟨A, B, domainRead, bodyRead, last⟩
      have checked := last
      rw [lambda?] at checked
      rcases (bindResult_eq_some_iff _ _ _).mp checked with ⟨bodyValue, bodyChecked, _⟩
      have termRead := (check?_eq_some_iff _ _ _).mp bodyChecked
      have domainRenamed := evaluateType_substitute model stable domain Γ Δ substitution modelMap A domainRead
      have bodyRenamed := evaluateType_substitute model stable body _ _ (liftSubstitution substitution)
        (modelMap.lift stable A) B bodyRead
      have termRenamed := evaluateTerm_substitute model stable term _ _ (liftSubstitution substitution)
        (modelMap.lift stable A) ⟨B, bodyValue⟩ termRead
      have target := model.evaluate_lambda Γ _ _ _ _ domainRenamed bodyRenamed _ _ termRenamed
      have commute := model.lambda?_substitution stable modelMap.arrow A B bodyValue
      rw [termRead] at last
      rw [last, Option.map_some, lambda?_supplied] at commute
      exact target.trans commute.symm
  | _, _, .app domain body function argument, Γ, Δ, substitution, modelMap, value, evaluated => by
      rcases (model.dependentAnnotations_eq_some_iff Δ domain body
        (fun A B => model.application? A B (model.evaluateTerm Δ function)
          (model.evaluateTerm Δ argument)) value).mp evaluated with
        ⟨A, B, domainRead, bodyRead, last⟩
      have checked := last
      rw [application?] at checked
      rcases (bindResult_eq_some_iff _ _ _).mp checked with ⟨f, functionChecked, rest⟩
      rcases (bindResult_eq_some_iff _ _ _).mp rest with ⟨a, argumentChecked, _⟩
      have functionRead := (check?_eq_some_iff _ _ _).mp functionChecked
      have argumentRead := (check?_eq_some_iff _ _ _).mp argumentChecked
      have domainRenamed := evaluateType_substitute model stable domain Γ Δ substitution modelMap A domainRead
      have bodyRenamed := evaluateType_substitute model stable body _ _ (liftSubstitution substitution)
        (modelMap.lift stable A) B bodyRead
      have functionRenamed := evaluateTerm_substitute model stable function Γ Δ substitution modelMap _ functionRead
      rw [model.product_value_substitute stable modelMap.arrow A B f] at functionRenamed
      have argumentRenamed := evaluateTerm_substitute model stable argument Γ Δ substitution modelMap _ argumentRead
      have target := model.evaluate_application Γ _ _ _ _ domainRenamed bodyRenamed _ _ _ _
        functionRenamed argumentRenamed
      have commute := model.application?_substitution stable modelMap.arrow A B f a
      rw [functionRead, argumentRead] at last
      rw [last, Option.map_some, application?_supplied] at commute
      exact target.trans commute.symm
  | _, _, .pair domain body first second, Γ, Δ, substitution, modelMap, value, evaluated => by
      rcases (model.dependentAnnotations_eq_some_iff Δ domain body
        (fun A B => model.pair? A B (model.evaluateTerm Δ first)
          (model.evaluateTerm Δ second)) value).mp evaluated with
        ⟨A, B, domainRead, bodyRead, last⟩
      have checked := last
      rw [pair?] at checked
      rcases (bindResult_eq_some_iff _ _ _).mp checked with ⟨a, firstChecked, rest⟩
      rcases (bindResult_eq_some_iff _ _ _).mp rest with ⟨b, secondChecked, _⟩
      have firstRead := (check?_eq_some_iff _ _ _).mp firstChecked
      have secondRead := (check?_eq_some_iff _ _ _).mp secondChecked
      have domainRenamed := evaluateType_substitute model stable domain Γ Δ substitution modelMap A domainRead
      have bodyRenamed := evaluateType_substitute model stable body _ _ (liftSubstitution substitution)
        (modelMap.lift stable A) B bodyRead
      have firstRenamed := evaluateTerm_substitute model stable first Γ Δ substitution modelMap _ firstRead
      have secondRenamed := evaluateTerm_substitute model stable second Γ Δ substitution modelMap _ secondRead
      rw [second_value_substitute modelMap.arrow A B a b] at secondRenamed
      have target := model.evaluate_pair Γ _ _ _ _ domainRenamed bodyRenamed _ _ _ _
        firstRenamed secondRenamed
      have commute := model.pair?_substitution modelMap.arrow A B a b
      rw [firstRead, secondRead] at last
      rw [last, Option.map_some, pair?_supplied] at commute
      exact target.trans commute.symm
  | _, _, .fst domain body pair, Γ, Δ, substitution, modelMap, value, evaluated => by
      rcases (model.dependentAnnotations_eq_some_iff Δ domain body
        (fun A B => model.first? A B (model.evaluateTerm Δ pair)) value).mp evaluated with
        ⟨A, B, domainRead, bodyRead, last⟩
      have checked := last
      rw [first?] at checked
      rcases (bindResult_eq_some_iff _ _ _).mp checked with ⟨p, pairChecked, _⟩
      have pairRead := (check?_eq_some_iff _ _ _).mp pairChecked
      have domainRenamed := evaluateType_substitute model stable domain Γ Δ substitution modelMap A domainRead
      have bodyRenamed := evaluateType_substitute model stable body _ _ (liftSubstitution substitution)
        (modelMap.lift stable A) B bodyRead
      have pairRenamed := evaluateTerm_substitute model stable pair Γ Δ substitution modelMap _ pairRead
      rw [model.sum_value_substitute modelMap.arrow A B p] at pairRenamed
      have target := model.evaluate_first Γ _ _ _ _ domainRenamed bodyRenamed _ _ pairRenamed
      have commute := model.first?_substitution modelMap.arrow A B p
      rw [pairRead] at last
      rw [last, Option.map_some, first?_supplied] at commute
      exact target.trans commute.symm
  | _, _, .snd domain body pair, Γ, Δ, substitution, modelMap, value, evaluated => by
      rcases (model.dependentAnnotations_eq_some_iff Δ domain body
        (fun A B => model.second? A B (model.evaluateTerm Δ pair)) value).mp evaluated with
        ⟨A, B, domainRead, bodyRead, last⟩
      have checked := last
      rw [second?] at checked
      rcases (bindResult_eq_some_iff _ _ _).mp checked with ⟨p, pairChecked, _⟩
      have pairRead := (check?_eq_some_iff _ _ _).mp pairChecked
      have domainRenamed := evaluateType_substitute model stable domain Γ Δ substitution modelMap A domainRead
      have bodyRenamed := evaluateType_substitute model stable body _ _ (liftSubstitution substitution)
        (modelMap.lift stable A) B bodyRead
      have pairRenamed := evaluateTerm_substitute model stable pair Γ Δ substitution modelMap _ pairRead
      rw [model.sum_value_substitute modelMap.arrow A B p] at pairRenamed
      have target := model.evaluate_second Γ _ _ _ _ domainRenamed bodyRenamed _ _ pairRenamed
      have commute := model.second?_substitution modelMap.arrow A B p
      rw [pairRead] at last
      rw [last, Option.map_some, second?_supplied] at commute
      exact target.trans commute.symm
  | _, _, .sigmaElim domain body motive branch pair, Γ, Δ, substitution, modelMap, value, evaluated => by
      rcases (model.dependentAnnotations_eq_some_iff Δ domain body
        (fun A B => bindResult (model.evaluateType
          (Δ.snoc (model.sums.operations.sigma A B)) motive) (fun M =>
          model.sumEliminate? A B M (model.evaluateTerm ((Δ.snoc A).snoc B) branch)
            (model.evaluateTerm Δ pair))) value).mp evaluated with
        ⟨A, B, domainRead, bodyRead, motiveStep⟩
      rcases (bindResult_eq_some_iff _ _ _).mp motiveStep with ⟨M, motiveRead, last⟩
      have motiveEvaluated : model.evaluateType (Δ.snoc (model.sums.operations.sigma A B)) motive = some M :=
        motiveRead
      have checked := last
      rw [sumEliminate?] at checked
      rcases (bindResult_eq_some_iff _ _ _).mp checked with ⟨b, branchChecked, rest⟩
      rcases (bindResult_eq_some_iff _ _ _).mp rest with ⟨p, pairChecked, _⟩
      have branchRead := (check?_eq_some_iff _ _ _).mp branchChecked
      have pairRead := (check?_eq_some_iff _ _ _).mp pairChecked
      have domainRenamed := evaluateType_substitute model stable domain Γ Δ substitution modelMap A domainRead
      have bodyRenamed := evaluateType_substitute model stable body _ _ (liftSubstitution substitution)
        (modelMap.lift stable A) B bodyRead
      let newSum := model.sums.operations.sigma ((NativeModel C).toCwf.tySub A modelMap.arrow)
        ((NativeModel C).toCwf.tySub B
          (TypeOver.extensionSubstitution (C := (NativeModel C).toCwf) modelMap.arrow A))
      let motiveMap := modelMap.liftAlong stable (model.sums.operations.sigma A B) newSum
        (model.sums.substitution.1 modelMap.arrow A B)
      have motiveArrow : motiveMap.arrow = sumReindex model.sums modelMap.arrow A B :=
        (modelMap.liftAlong_arrow stable _ _ _).trans
          (ContextualSumSectionSubstitution.sumReindex_eq_extensionCast
            model.sums modelMap.arrow A B).symm
      have motiveRenamed := evaluateType_substitute model stable motive _ _ (liftSubstitution substitution)
        motiveMap M motiveEvaluated
      rw [motiveArrow] at motiveRenamed
      have branchRenamed := evaluateTerm_substitute model stable branch _ _
        (liftSubstitution (liftSubstitution substitution)) ((modelMap.lift stable A).lift stable B) _ branchRead
      have branchValue := ContextualSumSectionSubstitution.body_value_substitution
        model.sums modelMap.arrow A B M b
      change model.evaluateTerm
        ((Γ.snoc ((NativeModel C).toCwf.tySub A modelMap.arrow)).snoc
          ((NativeModel C).toCwf.tySub B
            (TypeOver.extensionSubstitution (C := (NativeModel C).toCwf) modelMap.arrow A)))
        (branch.substitute (liftSubstitution (liftSubstitution substitution))) =
        some (Value.substitute (K := (NativeModel C).toCwf)
          (⟨_, b⟩ : NativeValue _)
          (tupleReindex (C := (NativeModel C).toCwf) modelMap.arrow A B))
        at branchRenamed
      rw [branchValue] at branchRenamed
      have pairRenamed := evaluateTerm_substitute model stable pair Γ Δ substitution modelMap _ pairRead
      rw [model.sum_value_substitute modelMap.arrow A B p] at pairRenamed
      have target := model.evaluate_sumElimination Γ _ _ _ _ domainRenamed bodyRenamed _ _ _ _ _ _
        motiveRenamed branchRenamed pairRenamed
      have commute := model.sumEliminate?_substitution modelMap.arrow A B M b p
      rw [branchRead, pairRead] at last
      rw [last, Option.map_some, sumEliminate?_supplied] at commute
      exact target.trans commute.symm

  | _, _, .quote predicate, Γ, Δ, substitution, modelMap, value, evaluated => by
      change bindResult (model.evaluatePredicate Δ predicate) _ = some value at evaluated
      rcases (bindResult_eq_some_iff _ _ _).mp evaluated with ⟨φ, predicateRead, last⟩
      have actual : (⟨nativeOmega Δ.1, nativeQuote φ⟩ : NativeValue Δ.1) = value := Option.some.inj last
      have predicateRenamed := evaluatePredicate_substitute model stable predicate Γ Δ substitution modelMap φ predicateRead
      rw [TermExpr.substitute, ← actual, quote_value_substitute]
      exact model.evaluate_quote Γ _ _ predicateRenamed
  | _, _, .refine domain predicate term, Γ, Δ, substitution, modelMap, value, evaluated => by
      rw [evaluateTerm] at evaluated
      rcases (bindResult_eq_some_iff _ _ _).mp evaluated with ⟨A, domainRead, rest⟩
      change bindResult (model.evaluatePredicate (Δ.snoc A) predicate) _ = some value at rest
      rcases (bindResult_eq_some_iff _ _ _).mp rest with ⟨φ, predicateRead, last⟩
      rcases (refine?_eq_some_iff _ _ _ _).mp last with ⟨termValue, satisfies, termRead, actual⟩
      have domainRenamed := evaluateType_substitute model stable domain Γ Δ substitution modelMap A domainRead
      have predicateRenamed := evaluatePredicate_substitute model stable predicate _ _
        (liftSubstitution substitution) (modelMap.lift stable A) φ predicateRead
      change model.evaluatePredicate (Γ.snoc ((NativeModel C).toCwf.tySub A modelMap.arrow))
        (predicate.substitute (liftSubstitution substitution)) =
          some (φ.preimage (TypeOver.extensionSubstitution (C := (NativeModel C).toCwf)
            modelMap.arrow A)) at predicateRenamed
      rw [NativeLocalTypeOperations.local_extensionSubstitution] at predicateRenamed
      have termRenamed := evaluateTerm_substitute model stable term Γ Δ substitution modelMap _ termRead
      rw [TermExpr.substitute, evaluateTerm, domainRenamed, bindResult]
      change bindResult (model.evaluatePredicate (Γ.snoc _)
        (predicate.substitute (liftSubstitution substitution))) _ = _
      rw [predicateRenamed]
      change refine? _ _ (model.evaluateTerm Γ (term.substitute substitution)) = _
      rw [termRenamed, ← actual]
      have commute := refine?_substitution modelMap.arrow A φ termValue satisfies
      rw [refine?_supplied A φ termValue satisfies, Option.map_some] at commute
      exact commute.symm
  | _, _, .forget domain predicate term, Γ, Δ, substitution, modelMap, value, evaluated => by
      rw [evaluateTerm] at evaluated
      rcases (bindResult_eq_some_iff _ _ _).mp evaluated with ⟨A, domainRead, rest⟩
      change bindResult (model.evaluatePredicate (Δ.snoc A) predicate) _ = some value at rest
      rcases (bindResult_eq_some_iff _ _ _).mp rest with ⟨φ, predicateRead, last⟩
      have checked := last
      rw [forget?] at checked
      rcases (bindResult_eq_some_iff _ _ _).mp checked with ⟨termValue, termChecked, _⟩
      have termRead := (check?_eq_some_iff _ _ _).mp termChecked
      have domainRenamed := evaluateType_substitute model stable domain Γ Δ substitution modelMap A domainRead
      have predicateRenamed := evaluatePredicate_substitute model stable predicate _ _
        (liftSubstitution substitution) (modelMap.lift stable A) φ predicateRead
      change model.evaluatePredicate (Γ.snoc ((NativeModel C).toCwf.tySub A modelMap.arrow))
        (predicate.substitute (liftSubstitution substitution)) =
          some (φ.preimage (TypeOver.extensionSubstitution (C := (NativeModel C).toCwf)
            modelMap.arrow A)) at predicateRenamed
      rw [NativeLocalTypeOperations.local_extensionSubstitution] at predicateRenamed
      have termRenamed := evaluateTerm_substitute model stable term Γ Δ substitution modelMap _ termRead
      rw [refinement_value_substitute] at termRenamed
      rw [TermExpr.substitute, evaluateTerm, domainRenamed, bindResult]
      change bindResult (model.evaluatePredicate (Γ.snoc _)
        (predicate.substitute (liftSubstitution substitution))) _ = _
      rw [predicateRenamed]
      change forget? _ _ (model.evaluateTerm Γ (term.substitute substitution)) = _
      rw [termRenamed]
      have commute := forget?_substitution modelMap.arrow A φ termValue
      rw [termRead] at last
      rw [last, Option.map_some] at commute
      exact commute.symm

theorem evaluatePredicate_substitute (model : ModelData S C) (stable : StrictPiSubstitution model.products) :
    {n k : Nat} → (predicate : PropExpr S n) → (Γ : Scope C k) → (Δ : Scope C n) →
    (substitution : Substitution S n k) → (modelMap : ModelSubstitution model Γ Δ substitution) →
    (φ : Subfunctor Δ.1) → model.evaluatePredicate Δ predicate = some φ →
    model.evaluatePredicate Γ (predicate.substitute substitution) = some (φ.preimage modelMap.arrow)
  | _, _, .atom symbol arguments, Γ, Δ, substitution, modelMap, result, evaluated => by
      change bindResult ((model.predicateParameters symbol).2.assemble?
        (fun index => model.evaluateTerm Δ (arguments index))) _ = some result at evaluated
      rcases (bindResult_eq_some_iff _ _ _).mp evaluated with ⟨actual, assembled, last⟩
      have source : model.predicateAt symbol actual = result := Option.some.inj last
      have argumentsRead := ScopeData.assemble?_sound _ _ actual assembled
      have targetRead : ∀ index, model.evaluateTerm Γ ((arguments index).substitute substitution) =
          some ((model.predicateParameters symbol).2.components (modelMap.arrow ≫ actual) index) := by
        intro index
        rw [ScopeData.components_composition]
        exact evaluateTerm_substitute model stable (arguments index) Γ Δ substitution modelMap _ (argumentsRead index)
      rw [PropExpr.substitute, ← source, model.predicateAt_substitution]
      exact model.evaluate_predicateAtom Γ _ _ _ targetRead
  | _, _, .truth, Γ, Δ, substitution, modelMap, result, evaluated => by
      have source : (⊤ : Subfunctor Δ.1) = result := Option.some.inj evaluated
      rw [← source]
      rfl
  | _, _, .falsehood, Γ, Δ, substitution, modelMap, result, evaluated => by
      have source : (⊥ : Subfunctor Δ.1) = result := Option.some.inj evaluated
      rw [← source]
      rfl
  | _, _, .and first second, Γ, Δ, substitution, modelMap, result, evaluated => by
      change bindResult (model.evaluatePredicate Δ first) (fun first =>
        bindResult (model.evaluatePredicate Δ second) (fun second => some (first ⊓ second))) = some result at evaluated
      rcases (bindResult_eq_some_iff _ _ _).mp evaluated with ⟨φ, firstRead, rest⟩
      rcases (bindResult_eq_some_iff _ _ _).mp rest with ⟨ψ, secondRead, last⟩
      have firstRenamed := evaluatePredicate_substitute model stable first Γ Δ substitution modelMap φ firstRead
      have secondRenamed := evaluatePredicate_substitute model stable second Γ Δ substitution modelMap ψ secondRead
      have target := model.evaluate_and Γ _ _ _ _ firstRenamed secondRenamed
      rw [PropExpr.substitute]
      have source : φ ⊓ ψ = result := Option.some.inj last
      rw [← source]
      exact target
  | _, _, .or first second, Γ, Δ, substitution, modelMap, result, evaluated => by
      change bindResult (model.evaluatePredicate Δ first) (fun first =>
        bindResult (model.evaluatePredicate Δ second) (fun second => some (first ⊔ second))) = some result at evaluated
      rcases (bindResult_eq_some_iff _ _ _).mp evaluated with ⟨φ, firstRead, rest⟩
      rcases (bindResult_eq_some_iff _ _ _).mp rest with ⟨ψ, secondRead, last⟩
      have firstRenamed := evaluatePredicate_substitute model stable first Γ Δ substitution modelMap φ firstRead
      have secondRenamed := evaluatePredicate_substitute model stable second Γ Δ substitution modelMap ψ secondRead
      have target := model.evaluate_or Γ _ _ _ _ firstRenamed secondRenamed
      rw [PropExpr.substitute]
      have source : φ ⊔ ψ = result := Option.some.inj last
      rw [← source]
      exact target
  | _, _, .implies first second, Γ, Δ, substitution, modelMap, result, evaluated => by
      change bindResult (model.evaluatePredicate Δ first) (fun first =>
        bindResult (model.evaluatePredicate Δ second) (fun second => some (himpPointwise first second))) = some result at evaluated
      rcases (bindResult_eq_some_iff _ _ _).mp evaluated with ⟨φ, firstRead, rest⟩
      rcases (bindResult_eq_some_iff _ _ _).mp rest with ⟨ψ, secondRead, last⟩
      have firstRenamed := evaluatePredicate_substitute model stable first Γ Δ substitution modelMap φ firstRead
      have secondRenamed := evaluatePredicate_substitute model stable second Γ Δ substitution modelMap ψ secondRead
      have target := model.evaluate_implies Γ _ _ _ _ firstRenamed secondRenamed
      rw [PropExpr.substitute]
      have source : himpPointwise φ ψ = result := Option.some.inj last
      rw [← source, himpPointwise_eq_himp, preimage_himp, ← himpPointwise_eq_himp]
      exact target
  | _, _, .all domain predicate, Γ, Δ, substitution, modelMap, result, evaluated => by
      change bindResult (model.evaluateType Δ domain) (fun A =>
        bindResult (model.evaluatePredicate (Δ.snoc A) predicate)
          (fun φ => some (forallAlong ((NativeModel C).toCwf.wk A) φ))) = some result at evaluated
      rcases (bindResult_eq_some_iff _ _ _).mp evaluated with ⟨A, domainRead, rest⟩
      rcases (bindResult_eq_some_iff _ _ _).mp rest with ⟨φ, predicateRead, last⟩
      have source : forallAlong ((NativeModel C).toCwf.wk A) φ = result := Option.some.inj last
      have domainRenamed := evaluateType_substitute model stable domain Γ Δ substitution modelMap A domainRead
      have predicateRenamed := evaluatePredicate_substitute model stable predicate _ _
        (liftSubstitution substitution) (modelMap.lift stable A) φ predicateRead
      have target := model.evaluate_all Γ _ _ _ _ domainRenamed predicateRenamed
      have comparison := nativeForall_substitution modelMap.arrow A φ
      rw [PropExpr.substitute, ← source]
      exact target.trans (congrArg some comparison).symm
  | _, _, .exists domain predicate, Γ, Δ, substitution, modelMap, result, evaluated => by
      change bindResult (model.evaluateType Δ domain) (fun A =>
        bindResult (model.evaluatePredicate (Δ.snoc A) predicate)
          (fun φ => some (φ.image ((NativeModel C).toCwf.wk A)))) = some result at evaluated
      rcases (bindResult_eq_some_iff _ _ _).mp evaluated with ⟨A, domainRead, rest⟩
      rcases (bindResult_eq_some_iff _ _ _).mp rest with ⟨φ, predicateRead, last⟩
      have source : φ.image ((NativeModel C).toCwf.wk A) = result := Option.some.inj last
      have domainRenamed := evaluateType_substitute model stable domain Γ Δ substitution modelMap A domainRead
      have predicateRenamed := evaluatePredicate_substitute model stable predicate _ _
        (liftSubstitution substitution) (modelMap.lift stable A) φ predicateRead
      have target := model.evaluate_exists Γ _ _ _ _ domainRenamed predicateRenamed
      have comparison := nativeExists_substitution modelMap.arrow A φ
      rw [PropExpr.substitute, ← source]
      exact target.trans (congrArg some comparison).symm
  | _, _, .holds term, Γ, Δ, substitution, modelMap, result, evaluated => by
      change bindResult (check? (model.evaluateTerm Δ term) (nativeOmega Δ.1)) _ = some result at evaluated
      rcases (bindResult_eq_some_iff _ _ _).mp evaluated with ⟨value, checked, last⟩
      have termRead := (check?_eq_some_iff _ _ _).mp checked
      have termRenamed := evaluateTerm_substitute model stable term Γ Δ substitution modelMap _ termRead
      rw [proposition_value_substitute] at termRenamed
      have source : nativeHolds value = result := Option.some.inj last
      rw [PropExpr.substitute, ← source, ← nativeHolds_substituteNative]
      exact model.evaluate_holds Γ _ _ termRenamed
  | _, _, .image type, Γ, Δ, substitution, modelMap, result, evaluated => by
      change bindResult (model.evaluateType Δ type) _ = some result at evaluated
      rcases (bindResult_eq_some_iff _ _ _).mp evaluated with ⟨A, typeRead, last⟩
      have source : Subfunctor.range ((NativeModel C).toCwf.wk A) = result := Option.some.inj last
      have typeRenamed := evaluateType_substitute model stable type Γ Δ substitution modelMap A typeRead
      have target := model.evaluate_image Γ _ _ typeRenamed
      have comparison := nativeImage_substitution modelMap.arrow A
      rw [PropExpr.substitute, ← source]
      exact target.trans (congrArg some comparison).symm

end

end ModelData

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement
