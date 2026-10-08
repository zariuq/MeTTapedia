import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementAbstractModelSubstitution
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementAbstractModelCommutation
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementAbstractPredicateCommutation

/-!
# Interpretation commutes with authored substitution

Mutual induction traverses every external type, term and predicate constructor. A
successful source evaluation commutes with one actual map whose
supplied raw components retain the ordered variable readouts and assumption guards. Binder maps, dependent pair witnesses and
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

theorem evaluateType_substitute (model : ModelData S C localModel) (stable : StrictPiSubstitution localModel.products) :
    {n k : Nat} → (type : TypeExpr S n) → (Γ : ModelScope C localModel k) → (Δ : ModelScope C localModel n) →
    (substitution : Substitution S n k) → (modelMap : ModelSubstitution model Γ Δ substitution) →
    (A : C.toCwf.Ty Δ.1) → model.evaluateType Δ type = some A →
    model.evaluateType Γ (type.substitute substitution) = some (C.toCwf.tySub A modelMap.arrow)
  | _, _, .family symbol arguments, Γ, Δ, substitution, modelMap, A, evaluated => by
      change bindResult ((model.typeParameters symbol).2.assemble?
        (fun index => model.evaluateTerm Δ (arguments index))) _ = some A at evaluated
      rcases (bindResult_eq_some_iff _ _ _).mp evaluated with ⟨actual, assembled, last⟩
      have sourceType : model.familyAt symbol actual = A :=
        Option.some.inj last
      have argumentsRead := ContextualPredicateModelScopes.ScopeData.assemble?_sound _ _ actual assembled
      have targetRead : ∀ index, model.evaluateTerm Γ ((arguments index).substitute substitution) =
          some ((model.typeParameters symbol).2.components
            (C.toCwf.compS actual modelMap.arrow) index) := by
        intro index
        rw [ContextualPredicateModelScopes.ScopeData.components_composition]
        exact evaluateTerm_substitute model stable (arguments index) Γ Δ substitution modelMap _
          (argumentsRead index)
      rw [TypeExpr.substitute, ← sourceType]
      change model.evaluateType Γ (.family symbol fun index => (arguments index).substitute substitution) =
        some (C.toCwf.tySub (model.familyAt symbol actual) modelMap.arrow)
      rw [model.familyAt_substitution]
      exact model.evaluate_family Γ _ _ _ targetRead
  | _, _, .pi domain body, Γ, Δ, substitution, modelMap, result, evaluated => by
      rcases (model.dependentAnnotations_eq_some_iff Δ domain body
        (fun A B => some (localModel.products.pi A B)) result).mp evaluated with
        ⟨A, B, domainRead, bodyRead, last⟩
      have sourceType : localModel.products.pi A B = result := Option.some.inj last
      have domainSubstituted := evaluateType_substitute model stable domain Γ Δ substitution modelMap A domainRead
      have bodySubstituted := evaluateType_substitute model stable body _ _ (liftSubstitution substitution)
        (modelMap.lift stable A) B bodyRead
      rw [TypeExpr.substitute, ← sourceType, stable.1]
      exact model.evaluate_pi Γ _ _ _ _ domainSubstituted bodySubstituted
  | _, _, .sigma domain body, Γ, Δ, substitution, modelMap, result, evaluated => by
      rcases (model.dependentAnnotations_eq_some_iff Δ domain body
        (fun A B => some (localModel.sums.operations.sigma A B)) result).mp evaluated with
        ⟨A, B, domainRead, bodyRead, last⟩
      have sourceType : localModel.sums.operations.sigma A B = result :=
        Option.some.inj last
      have domainSubstituted := evaluateType_substitute model stable domain Γ Δ substitution modelMap A domainRead
      have bodySubstituted := evaluateType_substitute model stable body _ _ (liftSubstitution substitution)
        (modelMap.lift stable A) B bodyRead
      rw [TypeExpr.substitute, ← sourceType, localModel.sums.substitution.1]
      exact model.evaluate_sigma Γ _ _ _ _ domainSubstituted bodySubstituted

  | _, _, .propositions, Γ, Δ, substitution, modelMap, result, evaluated => by
      have actual : localModel.propositions.omega Δ.1 = result := Option.some.inj evaluated
      rw [TypeExpr.substitute, ← actual, model.evaluate_propositions]
      exact congrArg some (localModel.propositions.omega_substitution modelMap.arrow).symm
  | _, _, .comprehension domain predicate, Γ, Δ, substitution, modelMap, result, evaluated => by
      change bindResult (model.evaluateType Δ domain) (fun A =>
        bindResult (model.evaluatePredicate (Δ.snoc A) predicate)
          (fun φ => some (localModel.refinements.refined A φ))) = some result at evaluated
      rcases (bindResult_eq_some_iff _ _ _).mp evaluated with ⟨A, domainRead, rest⟩
      rcases (bindResult_eq_some_iff _ _ _).mp rest with ⟨φ, predicateRead, last⟩
      have actual : localModel.refinements.refined A φ = result := Option.some.inj last
      have domainSubstituted := evaluateType_substitute model stable domain Γ Δ substitution modelMap A domainRead
      have predicateSubstituted := evaluatePredicate_substitute model stable predicate _ _
        (liftSubstitution substitution) (modelMap.lift stable A) φ predicateRead
      rw [TypeExpr.substitute, ← actual, localModel.refinements.formation_substitution]
      exact model.evaluate_comprehension Γ _ _ _ _ domainSubstituted predicateSubstituted

theorem evaluateTerm_substitute (model : ModelData S C localModel) (stable : StrictPiSubstitution localModel.products) :
    {n k : Nat} → (term : TermExpr S n) → (Γ : ModelScope C localModel k) → (Δ : ModelScope C localModel n) →
    (substitution : Substitution S n k) → (modelMap : ModelSubstitution model Γ Δ substitution) →
    (value : Value (C.toCwf) Δ.1) → model.evaluateTerm Δ term = some value →
    model.evaluateTerm Γ (term.substitute substitution) = some (value.substitute modelMap.arrow)
  | _, _, .var index, Γ, Δ, substitution, modelMap, value, evaluated => by
      have actual : Δ.2.lookup index = value := Option.some.inj evaluated
      rw [TermExpr.substitute, modelMap.readout, actual]
  | _, _, .primitive symbol arguments, Γ, Δ, substitution, modelMap, value, evaluated => by
      change bindResult ((model.termParameters symbol).2.assemble?
        (fun index => model.evaluateTerm Δ (arguments index))) _ = some value at evaluated
      rcases (bindResult_eq_some_iff _ _ _).mp evaluated with ⟨actual, assembled, last⟩
      have actualValue : model.primitiveAt symbol actual = value := Option.some.inj last
      have argumentsRead := ContextualPredicateModelScopes.ScopeData.assemble?_sound _ _ actual assembled
      have targetRead : ∀ index, model.evaluateTerm Γ ((arguments index).substitute substitution) =
          some ((model.termParameters symbol).2.components
            (C.toCwf.compS actual modelMap.arrow) index) := by
        intro index
        rw [ContextualPredicateModelScopes.ScopeData.components_composition]
        exact evaluateTerm_substitute model stable (arguments index) Γ Δ substitution modelMap _
          (argumentsRead index)
      rw [TermExpr.substitute, ← actualValue, model.primitiveAt_substitution]
      exact model.evaluate_primitive Γ _ _ _ targetRead
  | _, _, .lam domain body term, Γ, Δ, substitution, modelMap, value, evaluated => by
      rcases (model.dependentAnnotations_eq_some_iff Δ domain body
        (fun A B => lambda? localModel A B (model.evaluateTerm (Δ.snoc A) term)) value).mp evaluated with
        ⟨A, B, domainRead, bodyRead, last⟩
      have checked := last
      rw [lambda?] at checked
      rcases (bindResult_eq_some_iff _ _ _).mp checked with ⟨bodyValue, bodyChecked, _⟩
      have termRead := (check?_eq_some_iff _ _ _).mp bodyChecked
      have domainSubstituted := evaluateType_substitute model stable domain Γ Δ substitution modelMap A domainRead
      have bodySubstituted := evaluateType_substitute model stable body _ _ (liftSubstitution substitution)
        (modelMap.lift stable A) B bodyRead
      have termSubstituted := evaluateTerm_substitute model stable term _ _ (liftSubstitution substitution)
        (modelMap.lift stable A) ⟨B, bodyValue⟩ termRead
      have target := model.evaluate_lambda Γ _ _ _ _ domainSubstituted bodySubstituted _ _ termSubstituted
      have commute := lambda?_substitution localModel stable modelMap.arrow A B bodyValue
      rw [termRead] at last
      rw [last, Option.map_some, lambda?_supplied localModel] at commute
      exact target.trans commute.symm
  | _, _, .app domain body function argument, Γ, Δ, substitution, modelMap, value, evaluated => by
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
      have domainSubstituted := evaluateType_substitute model stable domain Γ Δ substitution modelMap A domainRead
      have bodySubstituted := evaluateType_substitute model stable body _ _ (liftSubstitution substitution)
        (modelMap.lift stable A) B bodyRead
      have functionSubstituted := evaluateTerm_substitute model stable function Γ Δ substitution modelMap _ functionRead
      rw [product_value_substitute localModel stable modelMap.arrow A B f] at functionSubstituted
      have argumentSubstituted := evaluateTerm_substitute model stable argument Γ Δ substitution modelMap _ argumentRead
      have target := model.evaluate_application Γ _ _ _ _ domainSubstituted bodySubstituted _ _ _ _
        functionSubstituted argumentSubstituted
      have commute := application?_substitution localModel stable modelMap.arrow A B f a
      rw [functionRead, argumentRead] at last
      rw [last, Option.map_some, application?_supplied localModel] at commute
      exact target.trans commute.symm
  | _, _, .pair domain body first second, Γ, Δ, substitution, modelMap, value, evaluated => by
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
      have domainSubstituted := evaluateType_substitute model stable domain Γ Δ substitution modelMap A domainRead
      have bodySubstituted := evaluateType_substitute model stable body _ _ (liftSubstitution substitution)
        (modelMap.lift stable A) B bodyRead
      have firstSubstituted := evaluateTerm_substitute model stable first Γ Δ substitution modelMap _ firstRead
      have secondSubstituted := evaluateTerm_substitute model stable second Γ Δ substitution modelMap _ secondRead
      rw [second_value_substitute modelMap.arrow A B a b] at secondSubstituted
      have target := model.evaluate_pair Γ _ _ _ _ domainSubstituted bodySubstituted _ _ _ _
        firstSubstituted secondSubstituted
      have commute := pair?_substitution localModel modelMap.arrow A B a b
      rw [firstRead, secondRead] at last
      rw [last, Option.map_some, pair?_supplied localModel] at commute
      exact target.trans commute.symm
  | _, _, .fst domain body pair, Γ, Δ, substitution, modelMap, value, evaluated => by
      rcases (model.dependentAnnotations_eq_some_iff Δ domain body
        (fun A B => first? localModel A B (model.evaluateTerm Δ pair)) value).mp evaluated with
        ⟨A, B, domainRead, bodyRead, last⟩
      have checked := last
      rw [first?] at checked
      rcases (bindResult_eq_some_iff _ _ _).mp checked with ⟨p, pairChecked, _⟩
      have pairRead := (check?_eq_some_iff _ _ _).mp pairChecked
      have domainSubstituted := evaluateType_substitute model stable domain Γ Δ substitution modelMap A domainRead
      have bodySubstituted := evaluateType_substitute model stable body _ _ (liftSubstitution substitution)
        (modelMap.lift stable A) B bodyRead
      have pairSubstituted := evaluateTerm_substitute model stable pair Γ Δ substitution modelMap _ pairRead
      rw [sum_value_substitute localModel modelMap.arrow A B p] at pairSubstituted
      have target := model.evaluate_first Γ _ _ _ _ domainSubstituted bodySubstituted _ _ pairSubstituted
      have commute := first?_substitution localModel modelMap.arrow A B p
      rw [pairRead] at last
      rw [last, Option.map_some, first?_supplied localModel] at commute
      exact target.trans commute.symm
  | _, _, .snd domain body pair, Γ, Δ, substitution, modelMap, value, evaluated => by
      rcases (model.dependentAnnotations_eq_some_iff Δ domain body
        (fun A B => second? localModel A B (model.evaluateTerm Δ pair)) value).mp evaluated with
        ⟨A, B, domainRead, bodyRead, last⟩
      have checked := last
      rw [second?] at checked
      rcases (bindResult_eq_some_iff _ _ _).mp checked with ⟨p, pairChecked, _⟩
      have pairRead := (check?_eq_some_iff _ _ _).mp pairChecked
      have domainSubstituted := evaluateType_substitute model stable domain Γ Δ substitution modelMap A domainRead
      have bodySubstituted := evaluateType_substitute model stable body _ _ (liftSubstitution substitution)
        (modelMap.lift stable A) B bodyRead
      have pairSubstituted := evaluateTerm_substitute model stable pair Γ Δ substitution modelMap _ pairRead
      rw [sum_value_substitute localModel modelMap.arrow A B p] at pairSubstituted
      have target := model.evaluate_second Γ _ _ _ _ domainSubstituted bodySubstituted _ _ pairSubstituted
      have commute := second?_substitution localModel modelMap.arrow A B p
      rw [pairRead] at last
      rw [last, Option.map_some, second?_supplied localModel] at commute
      exact target.trans commute.symm
  | _, _, .sigmaElim domain body motive branch pair, Γ, Δ, substitution, modelMap, value, evaluated => by
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
      have domainSubstituted := evaluateType_substitute model stable domain Γ Δ substitution modelMap A domainRead
      have bodySubstituted := evaluateType_substitute model stable body _ _ (liftSubstitution substitution)
        (modelMap.lift stable A) B bodyRead
      let newSum := localModel.sums.operations.sigma (C.toCwf.tySub A modelMap.arrow)
        (C.toCwf.tySub B
          (TypeOver.extensionSubstitution (C := C.toCwf) modelMap.arrow A))
      let motiveMap := modelMap.liftAlong stable (localModel.sums.operations.sigma A B) newSum
        (localModel.sums.substitution.1 modelMap.arrow A B)
      have motiveArrow : motiveMap.arrow = sumReindex localModel.sums modelMap.arrow A B :=
        (modelMap.liftAlong_arrow stable _ _ _).trans
          (ContextualSumSectionSubstitution.sumReindex_eq_extensionCast
            localModel.sums modelMap.arrow A B).symm
      have motiveSubstituted := evaluateType_substitute model stable motive _ _ (liftSubstitution substitution)
        motiveMap M motiveEvaluated
      rw [motiveArrow] at motiveSubstituted
      have branchSubstituted := evaluateTerm_substitute model stable branch _ _
        (liftSubstitution (liftSubstitution substitution)) ((modelMap.lift stable A).lift stable B) _ branchRead
      have branchValue := ContextualSumSectionSubstitution.body_value_substitution
        localModel.sums modelMap.arrow A B M b
      change model.evaluateTerm
        ((Γ.snoc (C.toCwf.tySub A modelMap.arrow)).snoc
          (C.toCwf.tySub B
            (TypeOver.extensionSubstitution (C := C.toCwf) modelMap.arrow A)))
        (branch.substitute (liftSubstitution (liftSubstitution substitution))) =
        some (Value.substitute (K := C.toCwf)
          (⟨_, b⟩ : Value C.toCwf _)
          (tupleReindex (C := C.toCwf) modelMap.arrow A B))
        at branchSubstituted
      rw [branchValue] at branchSubstituted
      have pairSubstituted := evaluateTerm_substitute model stable pair Γ Δ substitution modelMap _ pairRead
      rw [sum_value_substitute localModel modelMap.arrow A B p] at pairSubstituted
      have target := model.evaluate_sumElimination Γ _ _ _ _ domainSubstituted bodySubstituted _ _ _ _ _ _
        motiveSubstituted branchSubstituted pairSubstituted
      have commute := sumEliminate?_substitution localModel modelMap.arrow A B M b p
      rw [branchRead, pairRead] at last
      rw [last, Option.map_some, sumEliminate?_supplied localModel] at commute
      exact target.trans commute.symm

  | _, _, .quote predicate, Γ, Δ, substitution, modelMap, value, evaluated => by
      change bindResult (model.evaluatePredicate Δ predicate) _ = some value at evaluated
      rcases (bindResult_eq_some_iff _ _ _).mp evaluated with ⟨φ, predicateRead, last⟩
      have actual : (⟨localModel.propositions.omega Δ.1, localModel.propositions.quote φ⟩ :
          Value C.toCwf Δ.1) = value := Option.some.inj last
      have predicateSubstituted := evaluatePredicate_substitute model stable predicate Γ Δ substitution modelMap φ predicateRead
      rw [TermExpr.substitute, ← actual, quote_value_substitute]
      exact model.evaluate_quote Γ _ _ predicateSubstituted
  | _, _, .refine domain predicate term, Γ, Δ, substitution, modelMap, value, evaluated => by
      change bindResult (model.evaluateType Δ domain) (fun A =>
        bindResult (model.evaluatePredicate (Δ.snoc A) predicate)
          (fun φ => refine? localModel A φ (model.evaluateTerm Δ term))) = some value at evaluated
      rcases (bindResult_eq_some_iff _ _ _).mp evaluated with ⟨A, domainRead, rest⟩
      rcases (bindResult_eq_some_iff _ _ _).mp rest with ⟨φ, predicateRead, last⟩
      rcases (refine?_eq_some_iff localModel _ _ _ _).mp last with
        ⟨termValue, satisfies, termRead, actual⟩
      have domainSubstituted := evaluateType_substitute model stable domain Γ Δ substitution modelMap A domainRead
      have predicateSubstituted := evaluatePredicate_substitute model stable predicate _ _
        (liftSubstitution substitution) (modelMap.lift stable A) φ predicateRead
      have termSubstituted := evaluateTerm_substitute model stable term Γ Δ substitution modelMap _ termRead
      rw [TermExpr.substitute]
      change bindResult (model.evaluateType Γ (domain.substitute substitution)) (fun A =>
        bindResult (model.evaluatePredicate (Γ.snoc A) (predicate.substitute (liftSubstitution substitution)))
          (fun φ => refine? localModel A φ (model.evaluateTerm Γ (term.substitute substitution)))) = _
      rw [domainSubstituted]
      change bindResult (model.evaluatePredicate (Γ.snoc _)
        (predicate.substitute (liftSubstitution substitution))) _ = _
      rw [predicateSubstituted]
      change refine? localModel _ _ (model.evaluateTerm Γ (term.substitute substitution)) = _
      rw [termSubstituted, ← actual]
      have commute := refine?_substitution modelMap.arrow A φ termValue satisfies
      rw [refine?_supplied A φ termValue satisfies, Option.map_some] at commute
      exact commute.symm
  | _, _, .forget domain predicate term, Γ, Δ, substitution, modelMap, value, evaluated => by
      change bindResult (model.evaluateType Δ domain) (fun A =>
        bindResult (model.evaluatePredicate (Δ.snoc A) predicate)
          (fun φ => forget? localModel A φ (model.evaluateTerm Δ term))) = some value at evaluated
      rcases (bindResult_eq_some_iff _ _ _).mp evaluated with ⟨A, domainRead, rest⟩
      rcases (bindResult_eq_some_iff _ _ _).mp rest with ⟨φ, predicateRead, last⟩
      have checked := last
      rw [forget?] at checked
      rcases (bindResult_eq_some_iff _ _ _).mp checked with ⟨termValue, termChecked, _⟩
      have termRead := (check?_eq_some_iff _ _ _).mp termChecked
      have domainSubstituted := evaluateType_substitute model stable domain Γ Δ substitution modelMap A domainRead
      have predicateSubstituted := evaluatePredicate_substitute model stable predicate _ _
        (liftSubstitution substitution) (modelMap.lift stable A) φ predicateRead
      have termSubstituted := evaluateTerm_substitute model stable term Γ Δ substitution modelMap _ termRead
      rw [refinement_value_substitute] at termSubstituted
      rw [TermExpr.substitute]
      change bindResult (model.evaluateType Γ (domain.substitute substitution)) (fun A =>
        bindResult (model.evaluatePredicate (Γ.snoc A) (predicate.substitute (liftSubstitution substitution)))
          (fun φ => forget? localModel A φ (model.evaluateTerm Γ (term.substitute substitution)))) = _
      rw [domainSubstituted]
      change bindResult (model.evaluatePredicate (Γ.snoc _)
        (predicate.substitute (liftSubstitution substitution))) _ = _
      rw [predicateSubstituted]
      change forget? localModel _ _ (model.evaluateTerm Γ (term.substitute substitution)) = _
      rw [termSubstituted]
      have commute := forget?_substitution modelMap.arrow A φ termValue
      rw [termRead] at last
      rw [last, Option.map_some] at commute
      exact commute.symm

theorem evaluatePredicate_substitute (model : ModelData S C localModel)
    (stable : StrictPiSubstitution localModel.products) :
    {n k : Nat} → (predicate : PropExpr S n) → (Γ : ModelScope C localModel k) →
    (Δ : ModelScope C localModel n) → (substitution : Substitution S n k) →
    (modelMap : ModelSubstitution model Γ Δ substitution) → (φ : localModel.doctrine.Predicate Δ.1) →
    model.evaluatePredicate Δ predicate = some φ →
    model.evaluatePredicate Γ (predicate.substitute substitution) =
      some (localModel.doctrine.reindex modelMap.arrow φ)
  | _, _, .atom symbol arguments, Γ, Δ, substitution, modelMap, result, evaluated => by
      change bindResult ((model.predicateParameters symbol).2.assemble?
        (fun index => model.evaluateTerm Δ (arguments index))) _ = some result at evaluated
      rcases (bindResult_eq_some_iff _ _ _).mp evaluated with ⟨actual, assembled, last⟩
      have source : model.predicateAt symbol actual = result := Option.some.inj last
      have argumentsRead := ContextualPredicateModelScopes.ScopeData.assemble?_sound _ _ actual assembled
      have targetRead : ∀ index, model.evaluateTerm Γ ((arguments index).substitute substitution) =
          some ((model.predicateParameters symbol).2.components
            (C.toCwf.compS actual modelMap.arrow) index) := by
        intro index
        rw [ContextualPredicateModelScopes.ScopeData.components_composition]
        exact evaluateTerm_substitute model stable (arguments index) Γ Δ substitution modelMap _ (argumentsRead index)
      rw [PropExpr.substitute, ← source, model.predicateAt_substitution]
      exact model.evaluate_predicateAtom Γ _ _ _ targetRead
  | _, _, .truth, Γ, Δ, substitution, modelMap, result, evaluated => by
      have source : (⊤ : localModel.doctrine.Predicate Δ.1) = result := Option.some.inj evaluated
      rw [PropExpr.substitute, ← source, model.evaluate_truth, map_top]
  | _, _, .falsehood, Γ, Δ, substitution, modelMap, result, evaluated => by
      have source : (⊥ : localModel.doctrine.Predicate Δ.1) = result := Option.some.inj evaluated
      rw [PropExpr.substitute, ← source, model.evaluate_falsehood, map_bot]
  | _, _, .and first second, Γ, Δ, substitution, modelMap, result, evaluated => by
      change bindResult (model.evaluatePredicate Δ first) (fun first =>
        bindResult (model.evaluatePredicate Δ second) (fun second => some (first ⊓ second))) = some result at evaluated
      rcases (bindResult_eq_some_iff _ _ _).mp evaluated with ⟨φ, firstRead, rest⟩
      rcases (bindResult_eq_some_iff _ _ _).mp rest with ⟨ψ, secondRead, last⟩
      have firstSubstituted := evaluatePredicate_substitute model stable first Γ Δ substitution modelMap φ firstRead
      have secondSubstituted := evaluatePredicate_substitute model stable second Γ Δ substitution modelMap ψ secondRead
      have target := model.evaluate_and Γ _ _ _ _ firstSubstituted secondSubstituted
      rw [PropExpr.substitute]
      have source : φ ⊓ ψ = result := Option.some.inj last
      rw [← source, map_inf]
      exact target
  | _, _, .or first second, Γ, Δ, substitution, modelMap, result, evaluated => by
      change bindResult (model.evaluatePredicate Δ first) (fun first =>
        bindResult (model.evaluatePredicate Δ second) (fun second => some (first ⊔ second))) = some result at evaluated
      rcases (bindResult_eq_some_iff _ _ _).mp evaluated with ⟨φ, firstRead, rest⟩
      rcases (bindResult_eq_some_iff _ _ _).mp rest with ⟨ψ, secondRead, last⟩
      have firstSubstituted := evaluatePredicate_substitute model stable first Γ Δ substitution modelMap φ firstRead
      have secondSubstituted := evaluatePredicate_substitute model stable second Γ Δ substitution modelMap ψ secondRead
      have target := model.evaluate_or Γ _ _ _ _ firstSubstituted secondSubstituted
      rw [PropExpr.substitute]
      have source : φ ⊔ ψ = result := Option.some.inj last
      rw [← source, map_sup]
      exact target
  | _, _, .implies first second, Γ, Δ, substitution, modelMap, result, evaluated => by
      change bindResult (model.evaluatePredicate Δ first) (fun first =>
        bindResult (model.evaluatePredicate Δ second) (fun second => some (first ⇨ second))) = some result at evaluated
      rcases (bindResult_eq_some_iff _ _ _).mp evaluated with ⟨φ, firstRead, rest⟩
      rcases (bindResult_eq_some_iff _ _ _).mp rest with ⟨ψ, secondRead, last⟩
      have firstSubstituted := evaluatePredicate_substitute model stable first Γ Δ substitution modelMap φ firstRead
      have secondSubstituted := evaluatePredicate_substitute model stable second Γ Δ substitution modelMap ψ secondRead
      have target := model.evaluate_implies Γ _ _ _ _ firstSubstituted secondSubstituted
      rw [PropExpr.substitute]
      have source : φ ⇨ ψ = result := Option.some.inj last
      rw [← source, map_himp]
      exact target
  | _, _, .all domain predicate, Γ, Δ, substitution, modelMap, result, evaluated => by
      change bindResult (model.evaluateType Δ domain) (fun A =>
        bindResult (model.evaluatePredicate (Δ.snoc A) predicate)
          (fun φ => some (localModel.doctrine.all A φ))) = some result at evaluated
      rcases (bindResult_eq_some_iff _ _ _).mp evaluated with ⟨A, domainRead, rest⟩
      rcases (bindResult_eq_some_iff _ _ _).mp rest with ⟨φ, predicateRead, last⟩
      have source : localModel.doctrine.all A φ = result := Option.some.inj last
      have domainSubstituted := evaluateType_substitute model stable domain Γ Δ substitution modelMap A domainRead
      have predicateSubstituted := evaluatePredicate_substitute model stable predicate _ _
        (liftSubstitution substitution) (modelMap.lift stable A) φ predicateRead
      have target := model.evaluate_all Γ _ _ _ _ domainSubstituted predicateSubstituted
      rw [PropExpr.substitute, ← source, localModel.doctrine.all_reindex]
      exact target
  | _, _, .exists domain predicate, Γ, Δ, substitution, modelMap, result, evaluated => by
      change bindResult (model.evaluateType Δ domain) (fun A =>
        bindResult (model.evaluatePredicate (Δ.snoc A) predicate)
          (fun φ => some (localModel.doctrine.some A φ))) = some result at evaluated
      rcases (bindResult_eq_some_iff _ _ _).mp evaluated with ⟨A, domainRead, rest⟩
      rcases (bindResult_eq_some_iff _ _ _).mp rest with ⟨φ, predicateRead, last⟩
      have source : localModel.doctrine.some A φ = result := Option.some.inj last
      have domainSubstituted := evaluateType_substitute model stable domain Γ Δ substitution modelMap A domainRead
      have predicateSubstituted := evaluatePredicate_substitute model stable predicate _ _
        (liftSubstitution substitution) (modelMap.lift stable A) φ predicateRead
      have target := model.evaluate_exists Γ _ _ _ _ domainSubstituted predicateSubstituted
      rw [PropExpr.substitute, ← source, localModel.doctrine.some_reindex]
      exact target
  | _, _, .holds term, Γ, Δ, substitution, modelMap, result, evaluated => by
      change bindResult (check? (model.evaluateTerm Δ term) (localModel.propositions.omega Δ.1)) _ =
        some result at evaluated
      rcases (bindResult_eq_some_iff _ _ _).mp evaluated with ⟨value, checked, last⟩
      have termRead := (check?_eq_some_iff _ _ _).mp checked
      have termSubstituted := evaluateTerm_substitute model stable term Γ Δ substitution modelMap _ termRead
      rw [proposition_value_substitute] at termSubstituted
      have source : localModel.propositions.holds value = result := Option.some.inj last
      rw [PropExpr.substitute, ← source,
        ← ContextualPredicateValueSubstitution.PropositionOperations.holds_substitute
          localModel.propositions modelMap.arrow value]
      exact model.evaluate_holds Γ _ _ termSubstituted
  | _, _, .image type, Γ, Δ, substitution, modelMap, result, evaluated => by
      change bindResult (model.evaluateType Δ type) _ = some result at evaluated
      rcases (bindResult_eq_some_iff _ _ _).mp evaluated with ⟨A, typeRead, last⟩
      have source : localModel.doctrine.some A ⊤ = result := Option.some.inj last
      have typeSubstituted := evaluateType_substitute model stable type Γ Δ substitution modelMap A typeRead
      have target := model.evaluate_image Γ _ _ typeSubstituted
      rw [PropExpr.substitute, ← source, localModel.doctrine.some_reindex, map_top]
      exact target

end

end ModelData

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Abstract
