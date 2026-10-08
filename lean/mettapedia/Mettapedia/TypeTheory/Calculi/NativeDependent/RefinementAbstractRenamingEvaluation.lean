import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementAbstractModelRenaming
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementAbstractModelCommutation
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementAbstractPredicateCommutation

/-!
# Interpretation commutes with authored renaming

Mutual induction traverses every external type, term and predicate constructor. A
successful source evaluation commutes with an actual model renaming whose
finite variable readouts agree. Binder maps, dependent pair witnesses and
full sum motives use their earned contextual substitution equations.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Abstract

open Mettapedia.TypeTheory.ContextualPredicateModel
open Mettapedia.TypeTheory.ContextualPredicateModelScopes
open External (bindResult bindResult_eq_some_iff)
open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.ContextualModelTelescopes
open Mettapedia.TypeTheory.ContextualSumComprehension
open Mettapedia.TypeTheory.ContextualProductComparison (selfExtend)
open Mettapedia.TypeTheory.ContextualTypeOperations

universe a c s t m p

variable {S : Symbols.{a}} {C : CwfWithTerminal.{c, s, t, m}}
  {localModel : LocalModel.{c, s, t, m, p} C}

namespace ModelData

attribute [local irreducible] ContextualSumComprehension.normalize
  ContextualSumComprehension.reindexBody TypeOver.extensionSubstitution

set_option backward.isDefEq.respectTransparency false in
mutual

theorem evaluateType_rename (model : ModelData S C localModel) (stable : StrictPiSubstitution localModel.products) :
    {n k : Nat} → (type : TypeExpr S n) → (Γ : ModelScope C localModel k) → (Δ : ModelScope C localModel n) →
    (mapping : Renaming n k) → (modelMap : ModelRenaming Γ Δ mapping) →
    (A : C.toCwf.Ty Δ.1) → model.evaluateType Δ type = some A →
    model.evaluateType Γ (type.rename mapping) = some (C.toCwf.tySub A modelMap.arrow)
  | _, _, .family symbol arguments, Γ, Δ, mapping, modelMap, A, evaluated => by
      change bindResult ((model.typeParameters symbol).2.assemble?
        (fun index => model.evaluateTerm Δ (arguments index))) _ = some A at evaluated
      rcases (bindResult_eq_some_iff _ _ _).mp evaluated with ⟨actual, assembled, last⟩
      have sourceType : model.familyAt symbol actual = A :=
        Option.some.inj last
      have argumentsRead := ContextualPredicateModelScopes.ScopeData.assemble?_sound _ _ actual assembled
      have targetRead : ∀ index, model.evaluateTerm Γ ((arguments index).rename mapping) =
          some ((model.typeParameters symbol).2.components
            (C.toCwf.compS actual modelMap.arrow) index) := by
        intro index
        rw [ContextualPredicateModelScopes.ScopeData.components_composition]
        exact evaluateTerm_rename model stable (arguments index) Γ Δ mapping modelMap _
          (argumentsRead index)
      rw [TypeExpr.rename, ← sourceType]
      change model.evaluateType Γ (.family symbol fun index => (arguments index).rename mapping) =
        some (C.toCwf.tySub (model.familyAt symbol actual) modelMap.arrow)
      rw [model.familyAt_substitution]
      exact model.evaluate_family Γ _ _ _ targetRead
  | _, _, .pi domain body, Γ, Δ, mapping, modelMap, result, evaluated => by
      rcases (model.dependentAnnotations_eq_some_iff Δ domain body
        (fun A B => some (localModel.products.pi A B)) result).mp evaluated with
        ⟨A, B, domainRead, bodyRead, last⟩
      have sourceType : localModel.products.pi A B = result := Option.some.inj last
      have domainRenamed := evaluateType_rename model stable domain Γ Δ mapping modelMap A domainRead
      have bodyRenamed := evaluateType_rename model stable body _ _ (liftRenaming mapping)
        (modelMap.lift A) B bodyRead
      rw [TypeExpr.rename, ← sourceType, stable.1]
      exact model.evaluate_pi Γ _ _ _ _ domainRenamed bodyRenamed
  | _, _, .sigma domain body, Γ, Δ, mapping, modelMap, result, evaluated => by
      rcases (model.dependentAnnotations_eq_some_iff Δ domain body
        (fun A B => some (localModel.sums.operations.sigma A B)) result).mp evaluated with
        ⟨A, B, domainRead, bodyRead, last⟩
      have sourceType : localModel.sums.operations.sigma A B = result :=
        Option.some.inj last
      have domainRenamed := evaluateType_rename model stable domain Γ Δ mapping modelMap A domainRead
      have bodyRenamed := evaluateType_rename model stable body _ _ (liftRenaming mapping)
        (modelMap.lift A) B bodyRead
      rw [TypeExpr.rename, ← sourceType, localModel.sums.substitution.1]
      exact model.evaluate_sigma Γ _ _ _ _ domainRenamed bodyRenamed

  | _, _, .propositions, Γ, Δ, mapping, modelMap, result, evaluated => by
      have actual : localModel.propositions.omega Δ.1 = result := Option.some.inj evaluated
      rw [TypeExpr.rename, ← actual, model.evaluate_propositions]
      exact congrArg some (localModel.propositions.omega_substitution modelMap.arrow).symm
  | _, _, .comprehension domain predicate, Γ, Δ, mapping, modelMap, result, evaluated => by
      change bindResult (model.evaluateType Δ domain) (fun A =>
        bindResult (model.evaluatePredicate (Δ.snoc A) predicate)
          (fun φ => some (localModel.refinements.refined A φ))) = some result at evaluated
      rcases (bindResult_eq_some_iff _ _ _).mp evaluated with ⟨A, domainRead, rest⟩
      rcases (bindResult_eq_some_iff _ _ _).mp rest with ⟨φ, predicateRead, last⟩
      have actual : localModel.refinements.refined A φ = result := Option.some.inj last
      have domainRenamed := evaluateType_rename model stable domain Γ Δ mapping modelMap A domainRead
      have predicateRenamed := evaluatePredicate_rename model stable predicate _ _
        (liftRenaming mapping) (modelMap.lift A) φ predicateRead
      rw [TypeExpr.rename, ← actual, localModel.refinements.formation_substitution]
      exact model.evaluate_comprehension Γ _ _ _ _ domainRenamed predicateRenamed

theorem evaluateTerm_rename (model : ModelData S C localModel) (stable : StrictPiSubstitution localModel.products) :
    {n k : Nat} → (term : TermExpr S n) → (Γ : ModelScope C localModel k) → (Δ : ModelScope C localModel n) →
    (mapping : Renaming n k) → (modelMap : ModelRenaming Γ Δ mapping) →
    (value : Value (C.toCwf) Δ.1) → model.evaluateTerm Δ term = some value →
    model.evaluateTerm Γ (term.rename mapping) = some (value.substitute modelMap.arrow)
  | _, _, .var index, Γ, Δ, mapping, modelMap, value, evaluated => by
      have actual : Δ.2.lookup index = value := Option.some.inj evaluated
      rw [TermExpr.rename, evaluateTerm, evaluateTermLift, modelMap.readout, actual]
  | _, _, .primitive symbol arguments, Γ, Δ, mapping, modelMap, value, evaluated => by
      change bindResult ((model.termParameters symbol).2.assemble?
        (fun index => model.evaluateTerm Δ (arguments index))) _ = some value at evaluated
      rcases (bindResult_eq_some_iff _ _ _).mp evaluated with ⟨actual, assembled, last⟩
      have actualValue : model.primitiveAt symbol actual = value := Option.some.inj last
      have argumentsRead := ContextualPredicateModelScopes.ScopeData.assemble?_sound _ _ actual assembled
      have targetRead : ∀ index, model.evaluateTerm Γ ((arguments index).rename mapping) =
          some ((model.termParameters symbol).2.components
            (C.toCwf.compS actual modelMap.arrow) index) := by
        intro index
        rw [ContextualPredicateModelScopes.ScopeData.components_composition]
        exact evaluateTerm_rename model stable (arguments index) Γ Δ mapping modelMap _
          (argumentsRead index)
      rw [TermExpr.rename, ← actualValue, model.primitiveAt_substitution]
      exact model.evaluate_primitive Γ _ _ _ targetRead
  | _, _, .lam domain body term, Γ, Δ, mapping, modelMap, value, evaluated => by
      rcases (model.dependentAnnotations_eq_some_iff Δ domain body
        (fun A B => lambda? localModel A B (model.evaluateTerm (Δ.snoc A) term)) value).mp evaluated with
        ⟨A, B, domainRead, bodyRead, last⟩
      have checked := last
      rw [lambda?] at checked
      rcases (bindResult_eq_some_iff _ _ _).mp checked with ⟨bodyValue, bodyChecked, _⟩
      have termRead := (check?_eq_some_iff _ _ _).mp bodyChecked
      have domainRenamed := evaluateType_rename model stable domain Γ Δ mapping modelMap A domainRead
      have bodyRenamed := evaluateType_rename model stable body _ _ (liftRenaming mapping)
        (modelMap.lift A) B bodyRead
      have termRenamed := evaluateTerm_rename model stable term _ _ (liftRenaming mapping)
        (modelMap.lift A) ⟨B, bodyValue⟩ termRead
      have target := model.evaluate_lambda Γ _ _ _ _ domainRenamed bodyRenamed _ _ termRenamed
      have commute := lambda?_substitution localModel stable modelMap.arrow A B bodyValue
      rw [termRead] at last
      rw [last, Option.map_some, lambda?_supplied localModel] at commute
      exact target.trans commute.symm
  | _, _, .app domain body function argument, Γ, Δ, mapping, modelMap, value, evaluated => by
      rcases (model.dependentAnnotations_eq_some_iff Δ domain body
        (fun A B => application? localModel A B (model.evaluateTerm Δ function)
          (model.evaluateTerm Δ argument)) value).mp evaluated with
        ⟨A, B, domainRead, bodyRead, last⟩
      have checked := last
      rw [application?] at checked
      rcases (bindResult_eq_some_iff _ _ _).mp checked with ⟨f, functionChecked, rest⟩
      rcases (bindResult_eq_some_iff _ _ _).mp rest with ⟨a, argumentChecked, _⟩
      have functionRead := (check?_eq_some_iff _ _ _).mp functionChecked
      have argumentRead := (check?_eq_some_iff _ _ _).mp argumentChecked
      have domainRenamed := evaluateType_rename model stable domain Γ Δ mapping modelMap A domainRead
      have bodyRenamed := evaluateType_rename model stable body _ _ (liftRenaming mapping)
        (modelMap.lift A) B bodyRead
      have functionRenamed := evaluateTerm_rename model stable function Γ Δ mapping modelMap _ functionRead
      rw [product_value_substitute localModel stable modelMap.arrow A B f] at functionRenamed
      have argumentRenamed := evaluateTerm_rename model stable argument Γ Δ mapping modelMap _ argumentRead
      have target := model.evaluate_application Γ _ _ _ _ domainRenamed bodyRenamed _ _ _ _
        functionRenamed argumentRenamed
      have commute := application?_substitution localModel stable modelMap.arrow A B f a
      rw [functionRead, argumentRead] at last
      rw [last, Option.map_some, application?_supplied localModel] at commute
      exact target.trans commute.symm
  | _, _, .pair domain body first second, Γ, Δ, mapping, modelMap, value, evaluated => by
      rcases (model.dependentAnnotations_eq_some_iff Δ domain body
        (fun A B => pair? localModel A B (model.evaluateTerm Δ first)
          (model.evaluateTerm Δ second)) value).mp evaluated with
        ⟨A, B, domainRead, bodyRead, last⟩
      have checked := last
      rw [pair?] at checked
      rcases (bindResult_eq_some_iff _ _ _).mp checked with ⟨a, firstChecked, rest⟩
      rcases (bindResult_eq_some_iff _ _ _).mp rest with ⟨b, secondChecked, _⟩
      have firstRead := (check?_eq_some_iff _ _ _).mp firstChecked
      have secondRead := (check?_eq_some_iff _ _ _).mp secondChecked
      have domainRenamed := evaluateType_rename model stable domain Γ Δ mapping modelMap A domainRead
      have bodyRenamed := evaluateType_rename model stable body _ _ (liftRenaming mapping)
        (modelMap.lift A) B bodyRead
      have firstRenamed := evaluateTerm_rename model stable first Γ Δ mapping modelMap _ firstRead
      have secondRenamed := evaluateTerm_rename model stable second Γ Δ mapping modelMap _ secondRead
      rw [second_value_substitute modelMap.arrow A B a b] at secondRenamed
      have target := model.evaluate_pair Γ _ _ _ _ domainRenamed bodyRenamed _ _ _ _
        firstRenamed secondRenamed
      have commute := pair?_substitution localModel modelMap.arrow A B a b
      rw [firstRead, secondRead] at last
      rw [last, Option.map_some, pair?_supplied localModel] at commute
      exact target.trans commute.symm
  | _, _, .fst domain body pair, Γ, Δ, mapping, modelMap, value, evaluated => by
      rcases (model.dependentAnnotations_eq_some_iff Δ domain body
        (fun A B => first? localModel A B (model.evaluateTerm Δ pair)) value).mp evaluated with
        ⟨A, B, domainRead, bodyRead, last⟩
      have checked := last
      rw [first?] at checked
      rcases (bindResult_eq_some_iff _ _ _).mp checked with ⟨p, pairChecked, _⟩
      have pairRead := (check?_eq_some_iff _ _ _).mp pairChecked
      have domainRenamed := evaluateType_rename model stable domain Γ Δ mapping modelMap A domainRead
      have bodyRenamed := evaluateType_rename model stable body _ _ (liftRenaming mapping)
        (modelMap.lift A) B bodyRead
      have pairRenamed := evaluateTerm_rename model stable pair Γ Δ mapping modelMap _ pairRead
      rw [sum_value_substitute localModel modelMap.arrow A B p] at pairRenamed
      have target := model.evaluate_first Γ _ _ _ _ domainRenamed bodyRenamed _ _ pairRenamed
      have commute := first?_substitution localModel modelMap.arrow A B p
      rw [pairRead] at last
      rw [last, Option.map_some, first?_supplied localModel] at commute
      exact target.trans commute.symm
  | _, _, .snd domain body pair, Γ, Δ, mapping, modelMap, value, evaluated => by
      rcases (model.dependentAnnotations_eq_some_iff Δ domain body
        (fun A B => second? localModel A B (model.evaluateTerm Δ pair)) value).mp evaluated with
        ⟨A, B, domainRead, bodyRead, last⟩
      have checked := last
      rw [second?] at checked
      rcases (bindResult_eq_some_iff _ _ _).mp checked with ⟨p, pairChecked, _⟩
      have pairRead := (check?_eq_some_iff _ _ _).mp pairChecked
      have domainRenamed := evaluateType_rename model stable domain Γ Δ mapping modelMap A domainRead
      have bodyRenamed := evaluateType_rename model stable body _ _ (liftRenaming mapping)
        (modelMap.lift A) B bodyRead
      have pairRenamed := evaluateTerm_rename model stable pair Γ Δ mapping modelMap _ pairRead
      rw [sum_value_substitute localModel modelMap.arrow A B p] at pairRenamed
      have target := model.evaluate_second Γ _ _ _ _ domainRenamed bodyRenamed _ _ pairRenamed
      have commute := second?_substitution localModel modelMap.arrow A B p
      rw [pairRead] at last
      rw [last, Option.map_some, second?_supplied localModel] at commute
      exact target.trans commute.symm
  | _, _, .sigmaElim domain body motive branch pair, Γ, Δ, mapping, modelMap, value, evaluated => by
      rcases (model.dependentAnnotations_eq_some_iff Δ domain body
        (fun A B => bindResult (model.evaluateType
          (Δ.snoc (localModel.sums.operations.sigma A B)) motive) (fun M =>
          sumEliminate? localModel A B M (model.evaluateTerm ((Δ.snoc A).snoc B) branch)
            (model.evaluateTerm Δ pair))) value).mp evaluated with
        ⟨A, B, domainRead, bodyRead, motiveStep⟩
      rcases (bindResult_eq_some_iff _ _ _).mp motiveStep with ⟨M, motiveRead, last⟩
      have motiveEvaluated : model.evaluateType (Δ.snoc (localModel.sums.operations.sigma A B)) motive = some M :=
        motiveRead
      have checked := last
      rw [sumEliminate?] at checked
      rcases (bindResult_eq_some_iff _ _ _).mp checked with ⟨b, branchChecked, rest⟩
      rcases (bindResult_eq_some_iff _ _ _).mp rest with ⟨p, pairChecked, _⟩
      have branchRead := (check?_eq_some_iff _ _ _).mp branchChecked
      have pairRead := (check?_eq_some_iff _ _ _).mp pairChecked
      have domainRenamed := evaluateType_rename model stable domain Γ Δ mapping modelMap A domainRead
      have bodyRenamed := evaluateType_rename model stable body _ _ (liftRenaming mapping)
        (modelMap.lift A) B bodyRead
      let newSum := localModel.sums.operations.sigma (C.toCwf.tySub A modelMap.arrow)
        (C.toCwf.tySub B
          (TypeOver.extensionSubstitution (C := C.toCwf) modelMap.arrow A))
      let motiveMap := modelMap.liftAlong (localModel.sums.operations.sigma A B) newSum
        (localModel.sums.substitution.1 modelMap.arrow A B)
      have motiveArrow : motiveMap.arrow = sumReindex localModel.sums modelMap.arrow A B :=
        (modelMap.liftAlong_arrow _ _ _).trans
          (ContextualSumSectionSubstitution.sumReindex_eq_extensionCast
            localModel.sums modelMap.arrow A B).symm
      have motiveRenamed := evaluateType_rename model stable motive _ _ (liftRenaming mapping)
        motiveMap M motiveEvaluated
      rw [motiveArrow] at motiveRenamed
      have branchRenamed := evaluateTerm_rename model stable branch _ _
        (liftRenaming (liftRenaming mapping)) ((modelMap.lift A).lift B) _ branchRead
      have branchValue := ContextualSumSectionSubstitution.body_value_substitution
        localModel.sums modelMap.arrow A B M b
      change model.evaluateTerm
        ((Γ.snoc (C.toCwf.tySub A modelMap.arrow)).snoc
          (C.toCwf.tySub B
            (TypeOver.extensionSubstitution (C := C.toCwf) modelMap.arrow A)))
        (branch.rename (liftRenaming (liftRenaming mapping))) =
        some (Value.substitute (K := C.toCwf)
          (⟨_, b⟩ : Value C.toCwf _)
          (tupleReindex (C := C.toCwf) modelMap.arrow A B))
        at branchRenamed
      rw [branchValue] at branchRenamed
      have pairRenamed := evaluateTerm_rename model stable pair Γ Δ mapping modelMap _ pairRead
      rw [sum_value_substitute localModel modelMap.arrow A B p] at pairRenamed
      have target := model.evaluate_sumElimination Γ _ _ _ _ domainRenamed bodyRenamed _ _ _ _ _ _
        motiveRenamed branchRenamed pairRenamed
      have commute := sumEliminate?_substitution localModel modelMap.arrow A B M b p
      rw [branchRead, pairRead] at last
      rw [last, Option.map_some, sumEliminate?_supplied localModel] at commute
      exact target.trans commute.symm

  | _, _, .quote predicate, Γ, Δ, mapping, modelMap, value, evaluated => by
      change bindResult (model.evaluatePredicate Δ predicate) _ = some value at evaluated
      rcases (bindResult_eq_some_iff _ _ _).mp evaluated with ⟨φ, predicateRead, last⟩
      have actual : (⟨localModel.propositions.omega Δ.1, localModel.propositions.quote φ⟩ :
          Value C.toCwf Δ.1) = value := Option.some.inj last
      have predicateRenamed := evaluatePredicate_rename model stable predicate Γ Δ mapping modelMap φ predicateRead
      rw [TermExpr.rename, ← actual, quote_value_substitute]
      exact model.evaluate_quote Γ _ _ predicateRenamed
  | _, _, .refine domain predicate term, Γ, Δ, mapping, modelMap, value, evaluated => by
      change bindResult (model.evaluateType Δ domain) (fun A =>
        bindResult (model.evaluatePredicate (Δ.snoc A) predicate)
          (fun φ => refine? localModel A φ (model.evaluateTerm Δ term))) = some value at evaluated
      rcases (bindResult_eq_some_iff _ _ _).mp evaluated with ⟨A, domainRead, rest⟩
      rcases (bindResult_eq_some_iff _ _ _).mp rest with ⟨φ, predicateRead, last⟩
      rcases (refine?_eq_some_iff localModel _ _ _ _).mp last with
        ⟨termValue, satisfies, termRead, actual⟩
      have domainRenamed := evaluateType_rename model stable domain Γ Δ mapping modelMap A domainRead
      have predicateRenamed := evaluatePredicate_rename model stable predicate _ _
        (liftRenaming mapping) (modelMap.lift A) φ predicateRead
      have termRenamed := evaluateTerm_rename model stable term Γ Δ mapping modelMap _ termRead
      rw [TermExpr.rename]
      change bindResult (model.evaluateType Γ (domain.rename mapping)) (fun A =>
        bindResult (model.evaluatePredicate (Γ.snoc A) (predicate.rename (liftRenaming mapping)))
          (fun φ => refine? localModel A φ (model.evaluateTerm Γ (term.rename mapping)))) = _
      rw [domainRenamed]
      change bindResult (model.evaluatePredicate (Γ.snoc _)
        (predicate.rename (liftRenaming mapping))) _ = _
      rw [predicateRenamed]
      change refine? localModel _ _ (model.evaluateTerm Γ (term.rename mapping)) = _
      rw [termRenamed, ← actual]
      have commute := refine?_substitution modelMap.arrow A φ termValue satisfies
      rw [refine?_supplied A φ termValue satisfies, Option.map_some] at commute
      exact commute.symm
  | _, _, .forget domain predicate term, Γ, Δ, mapping, modelMap, value, evaluated => by
      change bindResult (model.evaluateType Δ domain) (fun A =>
        bindResult (model.evaluatePredicate (Δ.snoc A) predicate)
          (fun φ => forget? localModel A φ (model.evaluateTerm Δ term))) = some value at evaluated
      rcases (bindResult_eq_some_iff _ _ _).mp evaluated with ⟨A, domainRead, rest⟩
      rcases (bindResult_eq_some_iff _ _ _).mp rest with ⟨φ, predicateRead, last⟩
      have checked := last
      rw [forget?] at checked
      rcases (bindResult_eq_some_iff _ _ _).mp checked with ⟨termValue, termChecked, _⟩
      have termRead := (check?_eq_some_iff _ _ _).mp termChecked
      have domainRenamed := evaluateType_rename model stable domain Γ Δ mapping modelMap A domainRead
      have predicateRenamed := evaluatePredicate_rename model stable predicate _ _
        (liftRenaming mapping) (modelMap.lift A) φ predicateRead
      have termRenamed := evaluateTerm_rename model stable term Γ Δ mapping modelMap _ termRead
      rw [refinement_value_substitute] at termRenamed
      rw [TermExpr.rename]
      change bindResult (model.evaluateType Γ (domain.rename mapping)) (fun A =>
        bindResult (model.evaluatePredicate (Γ.snoc A) (predicate.rename (liftRenaming mapping)))
          (fun φ => forget? localModel A φ (model.evaluateTerm Γ (term.rename mapping)))) = _
      rw [domainRenamed]
      change bindResult (model.evaluatePredicate (Γ.snoc _)
        (predicate.rename (liftRenaming mapping))) _ = _
      rw [predicateRenamed]
      change forget? localModel _ _ (model.evaluateTerm Γ (term.rename mapping)) = _
      rw [termRenamed]
      have commute := forget?_substitution modelMap.arrow A φ termValue
      rw [termRead] at last
      rw [last, Option.map_some] at commute
      exact commute.symm

theorem evaluatePredicate_rename (model : ModelData S C localModel)
    (stable : StrictPiSubstitution localModel.products) :
    {n k : Nat} → (predicate : PropExpr S n) → (Γ : ModelScope C localModel k) →
    (Δ : ModelScope C localModel n) → (mapping : Renaming n k) →
    (modelMap : ModelRenaming Γ Δ mapping) → (φ : localModel.doctrine.Predicate Δ.1) →
    model.evaluatePredicate Δ predicate = some φ →
    model.evaluatePredicate Γ (predicate.rename mapping) =
      some (localModel.doctrine.reindex modelMap.arrow φ)
  | _, _, .atom symbol arguments, Γ, Δ, mapping, modelMap, result, evaluated => by
      change bindResult ((model.predicateParameters symbol).2.assemble?
        (fun index => model.evaluateTerm Δ (arguments index))) _ = some result at evaluated
      rcases (bindResult_eq_some_iff _ _ _).mp evaluated with ⟨actual, assembled, last⟩
      have source : model.predicateAt symbol actual = result := Option.some.inj last
      have argumentsRead := ContextualPredicateModelScopes.ScopeData.assemble?_sound _ _ actual assembled
      have targetRead : ∀ index, model.evaluateTerm Γ ((arguments index).rename mapping) =
          some ((model.predicateParameters symbol).2.components
            (C.toCwf.compS actual modelMap.arrow) index) := by
        intro index
        rw [ContextualPredicateModelScopes.ScopeData.components_composition]
        exact evaluateTerm_rename model stable (arguments index) Γ Δ mapping modelMap _ (argumentsRead index)
      rw [PropExpr.rename, ← source, model.predicateAt_substitution]
      exact model.evaluate_predicateAtom Γ _ _ _ targetRead
  | _, _, .truth, Γ, Δ, mapping, modelMap, result, evaluated => by
      have source : (⊤ : localModel.doctrine.Predicate Δ.1) = result := Option.some.inj evaluated
      rw [PropExpr.rename, ← source, model.evaluate_truth, map_top]
  | _, _, .falsehood, Γ, Δ, mapping, modelMap, result, evaluated => by
      have source : (⊥ : localModel.doctrine.Predicate Δ.1) = result := Option.some.inj evaluated
      rw [PropExpr.rename, ← source, model.evaluate_falsehood, map_bot]
  | _, _, .and first second, Γ, Δ, mapping, modelMap, result, evaluated => by
      change bindResult (model.evaluatePredicate Δ first) (fun first =>
        bindResult (model.evaluatePredicate Δ second) (fun second => some (first ⊓ second))) = some result at evaluated
      rcases (bindResult_eq_some_iff _ _ _).mp evaluated with ⟨φ, firstRead, rest⟩
      rcases (bindResult_eq_some_iff _ _ _).mp rest with ⟨ψ, secondRead, last⟩
      have firstRenamed := evaluatePredicate_rename model stable first Γ Δ mapping modelMap φ firstRead
      have secondRenamed := evaluatePredicate_rename model stable second Γ Δ mapping modelMap ψ secondRead
      have target := model.evaluate_and Γ _ _ _ _ firstRenamed secondRenamed
      rw [PropExpr.rename]
      have source : φ ⊓ ψ = result := Option.some.inj last
      rw [← source, map_inf]
      exact target
  | _, _, .or first second, Γ, Δ, mapping, modelMap, result, evaluated => by
      change bindResult (model.evaluatePredicate Δ first) (fun first =>
        bindResult (model.evaluatePredicate Δ second) (fun second => some (first ⊔ second))) = some result at evaluated
      rcases (bindResult_eq_some_iff _ _ _).mp evaluated with ⟨φ, firstRead, rest⟩
      rcases (bindResult_eq_some_iff _ _ _).mp rest with ⟨ψ, secondRead, last⟩
      have firstRenamed := evaluatePredicate_rename model stable first Γ Δ mapping modelMap φ firstRead
      have secondRenamed := evaluatePredicate_rename model stable second Γ Δ mapping modelMap ψ secondRead
      have target := model.evaluate_or Γ _ _ _ _ firstRenamed secondRenamed
      rw [PropExpr.rename]
      have source : φ ⊔ ψ = result := Option.some.inj last
      rw [← source, map_sup]
      exact target
  | _, _, .implies first second, Γ, Δ, mapping, modelMap, result, evaluated => by
      change bindResult (model.evaluatePredicate Δ first) (fun first =>
        bindResult (model.evaluatePredicate Δ second) (fun second => some (first ⇨ second))) = some result at evaluated
      rcases (bindResult_eq_some_iff _ _ _).mp evaluated with ⟨φ, firstRead, rest⟩
      rcases (bindResult_eq_some_iff _ _ _).mp rest with ⟨ψ, secondRead, last⟩
      have firstRenamed := evaluatePredicate_rename model stable first Γ Δ mapping modelMap φ firstRead
      have secondRenamed := evaluatePredicate_rename model stable second Γ Δ mapping modelMap ψ secondRead
      have target := model.evaluate_implies Γ _ _ _ _ firstRenamed secondRenamed
      rw [PropExpr.rename]
      have source : φ ⇨ ψ = result := Option.some.inj last
      rw [← source, map_himp]
      exact target
  | _, _, .all domain predicate, Γ, Δ, mapping, modelMap, result, evaluated => by
      change bindResult (model.evaluateType Δ domain) (fun A =>
        bindResult (model.evaluatePredicate (Δ.snoc A) predicate)
          (fun φ => some (localModel.doctrine.all A φ))) = some result at evaluated
      rcases (bindResult_eq_some_iff _ _ _).mp evaluated with ⟨A, domainRead, rest⟩
      rcases (bindResult_eq_some_iff _ _ _).mp rest with ⟨φ, predicateRead, last⟩
      have source : localModel.doctrine.all A φ = result := Option.some.inj last
      have domainRenamed := evaluateType_rename model stable domain Γ Δ mapping modelMap A domainRead
      have predicateRenamed := evaluatePredicate_rename model stable predicate _ _
        (liftRenaming mapping) (modelMap.lift A) φ predicateRead
      have target := model.evaluate_all Γ _ _ _ _ domainRenamed predicateRenamed
      rw [PropExpr.rename, ← source, localModel.doctrine.all_reindex]
      exact target
  | _, _, .exists domain predicate, Γ, Δ, mapping, modelMap, result, evaluated => by
      change bindResult (model.evaluateType Δ domain) (fun A =>
        bindResult (model.evaluatePredicate (Δ.snoc A) predicate)
          (fun φ => some (localModel.doctrine.some A φ))) = some result at evaluated
      rcases (bindResult_eq_some_iff _ _ _).mp evaluated with ⟨A, domainRead, rest⟩
      rcases (bindResult_eq_some_iff _ _ _).mp rest with ⟨φ, predicateRead, last⟩
      have source : localModel.doctrine.some A φ = result := Option.some.inj last
      have domainRenamed := evaluateType_rename model stable domain Γ Δ mapping modelMap A domainRead
      have predicateRenamed := evaluatePredicate_rename model stable predicate _ _
        (liftRenaming mapping) (modelMap.lift A) φ predicateRead
      have target := model.evaluate_exists Γ _ _ _ _ domainRenamed predicateRenamed
      rw [PropExpr.rename, ← source, localModel.doctrine.some_reindex]
      exact target
  | _, _, .holds term, Γ, Δ, mapping, modelMap, result, evaluated => by
      change bindResult (check? (model.evaluateTerm Δ term) (localModel.propositions.omega Δ.1)) _ =
        some result at evaluated
      rcases (bindResult_eq_some_iff _ _ _).mp evaluated with ⟨value, checked, last⟩
      have termRead := (check?_eq_some_iff _ _ _).mp checked
      have termRenamed := evaluateTerm_rename model stable term Γ Δ mapping modelMap _ termRead
      rw [proposition_value_substitute] at termRenamed
      have source : localModel.propositions.holds value = result := Option.some.inj last
      rw [PropExpr.rename, ← source,
        ← ContextualPredicateValueSubstitution.PropositionOperations.holds_substitute
          localModel.propositions modelMap.arrow value]
      exact model.evaluate_holds Γ _ _ termRenamed
  | _, _, .image type, Γ, Δ, mapping, modelMap, result, evaluated => by
      change bindResult (model.evaluateType Δ type) _ = some result at evaluated
      rcases (bindResult_eq_some_iff _ _ _).mp evaluated with ⟨A, typeRead, last⟩
      have source : localModel.doctrine.some A ⊤ = result := Option.some.inj last
      have typeRenamed := evaluateType_rename model stable type Γ Δ mapping modelMap A typeRead
      have target := model.evaluate_image Γ _ _ typeRenamed
      rw [PropExpr.rename, ← source, localModel.doctrine.some_reindex, map_top]
      exact target

end

end ModelData

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Abstract
