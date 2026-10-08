import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementSyntacticScope
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementSyntacticPrimitiveReadout
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementSyntacticSigmaReadout
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementSyntacticRefinementReadout
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementAbstractConstructorInterpretation
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementAbstractPredicateCommutation

/-!
# Simultaneous mixed-source readout induction

The induction visits the independently authored type, term and predicate expressions, including every primitive argument,
dependent annotation and logical binder. All source
constructor readouts are earned locally, including the full-motive sum case
and its typed packing comparison. No whole-evaluator or whole-derivation
soundness assumption is used.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Contextual.SyntacticReification

open _root_.CategoryTheory
open Mettapedia.TypeTheory.ContextualModelTelescopes
open Mettapedia.TypeTheory.ContextualSumComprehension
open Mettapedia.TypeTheory.ContextualProductComparison (selfExtend)
open SyntacticModel
open External (bindResult bindResult_eq_some_iff)

universe u
variable {S : Symbols.{u}} {D : Signature S}



set_option backward.isDefEq.respectTransparency false

mutual

theorem raw_type_readout (headers : HeaderFormation D) : {n : Nat} →
    (type : TypeExpr S n) → (scope : Scope D n) →
    (value : QuotientCwf.Ty ((quotientProjection D).obj scope.source)) →
    (data headers).evaluateType scope.semantic type = some value →
    TypeReadout ((quotientProjection D).obj scope.source) type value
  | _, .family symbol arguments, scope, value, evaluated => by
      change bindResult (((data headers).typeParameters symbol).2.assemble?
        (fun index => (data headers).evaluateTerm scope.semantic (arguments index)))
        (fun actual => some ((data headers).familyAt symbol actual)) = some value at evaluated
      rcases (bindResult_eq_some_iff _ _ _).mp evaluated with ⟨actual, assembled, last⟩
      rw [← Option.some.inj last]
      exact family_readout headers scope.source symbol arguments _
        (fun index value read => raw_term_readout headers (arguments index) scope value read) actual assembled
  | _, .propositions, scope, value, evaluated => by
      have same : PropositionModel.omega ((quotientProjection D).obj scope.source) = value :=
        Option.some.inj evaluated
      rw [← same]
      exact propositions_readout _
  | _, .pi domain body, scope, value, evaluated => by
      rcases ((data headers).dependentAnnotations_eq_some_iff scope.semantic domain body
        (fun A B => some (Products.pi A B)) value).mp evaluated with
        ⟨A, B, domainRead, bodyRead, last⟩
      rw [← Option.some.inj last]
      exact pi_readout (raw_type_readout headers domain scope A domainRead)
        (raw_type_readout headers body (scope.snoc A) B bodyRead)
  | _, .sigma domain body, scope, value, evaluated => by
      rcases ((data headers).dependentAnnotations_eq_some_iff scope.semantic domain body
        (fun A B => some (Sums.sigma A B)) value).mp evaluated with
        ⟨A, B, domainRead, bodyRead, last⟩
      rw [← Option.some.inj last]
      exact sigma_readout (raw_type_readout headers domain scope A domainRead)
        (raw_type_readout headers body (scope.snoc A) B bodyRead)
  | _, .comprehension domain predicate, scope, value, evaluated => by
      change bindResult ((data headers).evaluateType scope.semantic domain) (fun A =>
        bindResult ((data headers).evaluatePredicate (scope.semantic.snoc A) predicate)
          (fun body => some (Refinements.type A body))) = some value at evaluated
      rcases (bindResult_eq_some_iff _ _ _).mp evaluated with ⟨A, domainRead, rest⟩
      rcases (bindResult_eq_some_iff _ _ _).mp rest with ⟨body, bodyRead, last⟩
      rw [← Option.some.inj last]
      exact comprehension_readout (raw_type_readout headers domain scope A domainRead)
        (raw_predicate_readout headers predicate (scope.snoc A) body bodyRead)

theorem raw_term_readout (headers : HeaderFormation D) : {n : Nat} →
    (term : TermExpr S n) → (scope : Scope D n) →
    (value : Value (QuotientCwf.cwf D) ((quotientProjection D).obj scope.source)) →
    (data headers).evaluateTerm scope.semantic term = some value →
    TermReadout ((quotientProjection D).obj scope.source) term value
  | _, .var index, scope, value, evaluated => by
      have result : scope.mixed.lookup index = value := Option.some.inj evaluated
      rw [← result]
      exact scope.variable_readout index
  | _, .primitive symbol arguments, scope, value, evaluated => by
      change bindResult (((data headers).termParameters symbol).2.assemble?
        (fun index => (data headers).evaluateTerm scope.semantic (arguments index)))
        (fun actual => some ((data headers).primitiveAt symbol actual)) = some value at evaluated
      rcases (bindResult_eq_some_iff _ _ _).mp evaluated with ⟨actual, assembled, last⟩
      have result : (data headers).primitiveAt symbol actual = value := Option.some.inj last
      rw [← result]
      exact primitive_readout headers scope.source symbol arguments _
        (fun index value read => raw_term_readout headers (arguments index) scope value read) actual assembled
  | _, .lam domain body term, scope, value, evaluated => by
      rcases ((data headers).dependentAnnotations_eq_some_iff scope.semantic domain body
        (fun A B => Abstract.ModelData.lambda? (generatedModel D) A B ((data headers).evaluateTerm (scope.semantic.snoc A) term))
        value).mp evaluated with ⟨A, B, domainRead, bodyRead, last⟩
      have checked := last
      rw [Abstract.ModelData.lambda?] at checked
      rcases (bindResult_eq_some_iff _ _ _).mp checked with ⟨b, bodyChecked, _⟩
      have termRead := (Abstract.ModelData.check?_eq_some_iff _ _ _).mp bodyChecked
      rw [termRead, Abstract.ModelData.lambda?_supplied] at last
      rw [← Option.some.inj last]
      exact lambda_readout (raw_type_readout headers domain scope A domainRead)
        (raw_type_readout headers body (scope.snoc A) B bodyRead) b
        (raw_term_readout headers term (scope.snoc A) _ termRead)
  | _, .app domain body function argument, scope, value, evaluated => by
      rcases ((data headers).dependentAnnotations_eq_some_iff scope.semantic domain body
        (fun A B => Abstract.ModelData.application? (generatedModel D) A B ((data headers).evaluateTerm scope.semantic function)
          ((data headers).evaluateTerm scope.semantic argument)) value).mp evaluated with
        ⟨A, B, domainRead, bodyRead, last⟩
      have checked := last
      rw [Abstract.ModelData.application?] at checked
      rcases (bindResult_eq_some_iff _ _ _).mp checked with ⟨f, functionChecked, rest⟩
      rcases (bindResult_eq_some_iff _ _ _).mp rest with ⟨a, argumentChecked, _⟩
      have functionRead := (Abstract.ModelData.check?_eq_some_iff _ _ _).mp functionChecked
      have argumentRead := (Abstract.ModelData.check?_eq_some_iff _ _ _).mp argumentChecked
      rw [functionRead, argumentRead, Abstract.ModelData.application?_supplied] at last
      rw [← Option.some.inj last]
      exact application_readout (raw_type_readout headers domain scope A domainRead)
        (raw_type_readout headers body (scope.snoc A) B bodyRead) f a
        (raw_term_readout headers function scope _ functionRead)
        (raw_term_readout headers argument scope _ argumentRead)
  | _, .pair domain body first second, scope, value, evaluated => by
      rcases ((data headers).dependentAnnotations_eq_some_iff scope.semantic domain body
        (fun A B => Abstract.ModelData.pair? (generatedModel D) A B ((data headers).evaluateTerm scope.semantic first)
          ((data headers).evaluateTerm scope.semantic second)) value).mp evaluated with
        ⟨A, B, domainRead, bodyRead, last⟩
      have checked := last
      rw [Abstract.ModelData.pair?] at checked
      rcases (bindResult_eq_some_iff _ _ _).mp checked with ⟨a, firstChecked, rest⟩
      rcases (bindResult_eq_some_iff _ _ _).mp rest with ⟨b, secondChecked, _⟩
      have firstRead := (Abstract.ModelData.check?_eq_some_iff _ _ _).mp firstChecked
      have secondRead := (Abstract.ModelData.check?_eq_some_iff _ _ _).mp secondChecked
      rw [firstRead, secondRead, Abstract.ModelData.pair?_supplied] at last
      rw [← Option.some.inj last]
      exact pair_readout (raw_type_readout headers domain scope A domainRead)
        (raw_type_readout headers body (scope.snoc A) B bodyRead) a b
        (raw_term_readout headers first scope _ firstRead)
        (raw_term_readout headers second scope _ secondRead)
  | _, .fst domain body pair, scope, value, evaluated => by
      rcases ((data headers).dependentAnnotations_eq_some_iff scope.semantic domain body
        (fun A B => Abstract.ModelData.first? (generatedModel D) A B ((data headers).evaluateTerm scope.semantic pair))
        value).mp evaluated with ⟨A, B, domainRead, bodyRead, last⟩
      have checked := last
      rw [Abstract.ModelData.first?] at checked
      rcases (bindResult_eq_some_iff _ _ _).mp checked with ⟨p, pairChecked, _⟩
      have pairRead := (Abstract.ModelData.check?_eq_some_iff _ _ _).mp pairChecked
      rw [pairRead, Abstract.ModelData.first?_supplied] at last
      rw [← Option.some.inj last]
      exact first_readout (raw_type_readout headers domain scope A domainRead)
        (raw_type_readout headers body (scope.snoc A) B bodyRead) p
        (raw_term_readout headers pair scope _ pairRead)
  | _, .snd domain body pair, scope, value, evaluated => by
      rcases ((data headers).dependentAnnotations_eq_some_iff scope.semantic domain body
        (fun A B => Abstract.ModelData.second? (generatedModel D) A B ((data headers).evaluateTerm scope.semantic pair))
        value).mp evaluated with ⟨A, B, domainRead, bodyRead, last⟩
      have checked := last
      rw [Abstract.ModelData.second?] at checked
      rcases (bindResult_eq_some_iff _ _ _).mp checked with ⟨p, pairChecked, _⟩
      have pairRead := (Abstract.ModelData.check?_eq_some_iff _ _ _).mp pairChecked
      rw [pairRead, Abstract.ModelData.second?_supplied] at last
      rw [← Option.some.inj last]
      exact second_readout (raw_type_readout headers domain scope A domainRead)
        (raw_type_readout headers body (scope.snoc A) B bodyRead) p
        (raw_term_readout headers pair scope _ pairRead)
  | _, .sigmaElim domain body motive branch pair, scope, value, evaluated => by
      rcases ((data headers).dependentAnnotations_eq_some_iff scope.semantic domain body
        (fun A B => bindResult
          ((data headers).evaluateType (scope.semantic.snoc (Sums.sigma A B)) motive)
          (fun M => Abstract.ModelData.sumEliminate? (generatedModel D) A B M
            ((data headers).evaluateTerm ((scope.semantic.snoc A).snoc B) branch)
            ((data headers).evaluateTerm scope.semantic pair))) value).mp evaluated with
        ⟨A, B, domainRead, bodyRead, motiveLast⟩
      rcases (bindResult_eq_some_iff _ _ _).mp motiveLast with ⟨M, motiveRead, last⟩
      have checked := last
      rw [Abstract.ModelData.sumEliminate?] at checked
      rcases (bindResult_eq_some_iff _ _ _).mp checked with ⟨b, branchChecked, rest⟩
      rcases (bindResult_eq_some_iff _ _ _).mp rest with ⟨p, pairChecked, _⟩
      have branchRead := (Abstract.ModelData.check?_eq_some_iff _ _ _).mp branchChecked
      have pairRead := (Abstract.ModelData.check?_eq_some_iff _ _ _).mp pairChecked
      rw [branchRead, pairRead, Abstract.ModelData.sumEliminate?_supplied] at last
      rw [← Option.some.inj last]
      exact sigma_elimination_readout
        (raw_type_readout headers domain scope A domainRead)
        (raw_type_readout headers body (scope.snoc A) B bodyRead)
        (raw_type_readout headers motive (scope.snoc (Sums.sigma A B)) M motiveRead)
        b p (raw_term_readout headers branch ((scope.snoc A).snoc B) _ branchRead)
        (raw_term_readout headers pair scope _ pairRead)
  | _, .quote predicate, scope, value, evaluated => by
      change bindResult ((data headers).evaluatePredicate scope.semantic predicate)
        (fun body => some (⟨PropositionModel.omega _, PropositionModel.quote body⟩ : Value _ _)) =
          some value at evaluated
      rcases (bindResult_eq_some_iff _ _ _).mp evaluated with ⟨body, bodyRead, last⟩
      rw [← Option.some.inj last]
      exact quote_readout (raw_predicate_readout headers predicate scope body bodyRead)
  | _, .refine domain predicate term, scope, value, evaluated => by
      change bindResult ((data headers).evaluateType scope.semantic domain) (fun A =>
        bindResult ((data headers).evaluatePredicate (scope.semantic.snoc A) predicate)
          (fun body => Abstract.ModelData.refine? (generatedModel D) A body
            ((data headers).evaluateTerm scope.semantic term))) = some value at evaluated
      rcases (bindResult_eq_some_iff _ _ _).mp evaluated with ⟨A, domainRead, rest⟩
      rcases (bindResult_eq_some_iff _ _ _).mp rest with ⟨body, bodyRead, last⟩
      rcases (Abstract.ModelData.refine?_eq_some_iff (generatedModel D) A body _ value).mp last with
        ⟨termValue, guard, termRead, actual⟩
      rw [← actual]
      exact refine_readout (raw_type_readout headers domain scope A domainRead)
        (raw_predicate_readout headers predicate (scope.snoc A) body bodyRead) termValue guard
        (raw_term_readout headers term scope _ termRead)
  | _, .forget domain predicate term, scope, value, evaluated => by
      change bindResult ((data headers).evaluateType scope.semantic domain) (fun A =>
        bindResult ((data headers).evaluatePredicate (scope.semantic.snoc A) predicate)
          (fun body => Abstract.ModelData.forget? (generatedModel D) A body
            ((data headers).evaluateTerm scope.semantic term))) = some value at evaluated
      rcases (bindResult_eq_some_iff _ _ _).mp evaluated with ⟨A, domainRead, rest⟩
      rcases (bindResult_eq_some_iff _ _ _).mp rest with ⟨body, bodyRead, last⟩
      have checked := last
      rw [Abstract.ModelData.forget?] at checked
      rcases (bindResult_eq_some_iff _ _ _).mp checked with ⟨termValue, termChecked, _⟩
      have termRead := (Abstract.ModelData.check?_eq_some_iff _ _ _).mp termChecked
      rw [termRead, Abstract.ModelData.forget?_supplied] at last
      rw [← Option.some.inj last]
      exact forget_readout (raw_type_readout headers domain scope A domainRead)
        (raw_predicate_readout headers predicate (scope.snoc A) body bodyRead) termValue
        (raw_term_readout headers term scope _ termRead)

theorem raw_predicate_readout (headers : HeaderFormation D) : {n : Nat} →
    (predicate : PropExpr S n) → (scope : Scope D n) →
    (value : QPredicate scope.source) →
    (data headers).evaluatePredicate scope.semantic predicate = some value →
    PredicateReadout ((quotientProjection D).obj scope.source) predicate value
  | _, .atom symbol arguments, scope, value, evaluated => by
      change bindResult (((data headers).predicateParameters symbol).2.assemble?
        (fun index => (data headers).evaluateTerm scope.semantic (arguments index)))
        (fun actual => some ((data headers).predicateAt symbol actual)) = some value at evaluated
      rcases (bindResult_eq_some_iff _ _ _).mp evaluated with ⟨actual, assembled, last⟩
      rw [← Option.some.inj last]
      exact predicate_primitive_readout headers scope.source symbol arguments _
        (fun index value read => raw_term_readout headers (arguments index) scope value read) actual assembled
  | _, .truth, scope, value, evaluated => by
      have same : (⊤ : QPredicate scope.source) = value := Option.some.inj evaluated
      rw [← same]
      exact truth_readout _
  | _, .falsehood, scope, value, evaluated => by
      have same : (⊥ : QPredicate scope.source) = value := Option.some.inj evaluated
      rw [← same]
      exact falsehood_readout _
  | _, .and first second, scope, value, evaluated => by
      change bindResult ((data headers).evaluatePredicate scope.semantic first) (fun first =>
        bindResult ((data headers).evaluatePredicate scope.semantic second)
          (fun second => some (first ⊓ second))) = some value at evaluated
      rcases (bindResult_eq_some_iff _ _ _).mp evaluated with ⟨left, leftRead, rest⟩
      rcases (bindResult_eq_some_iff _ _ _).mp rest with ⟨right, rightRead, last⟩
      rw [← Option.some.inj last]
      exact conjunction_readout (raw_predicate_readout headers first scope left leftRead)
        (raw_predicate_readout headers second scope right rightRead)
  | _, .or first second, scope, value, evaluated => by
      change bindResult ((data headers).evaluatePredicate scope.semantic first) (fun first =>
        bindResult ((data headers).evaluatePredicate scope.semantic second)
          (fun second => some (first ⊔ second))) = some value at evaluated
      rcases (bindResult_eq_some_iff _ _ _).mp evaluated with ⟨left, leftRead, rest⟩
      rcases (bindResult_eq_some_iff _ _ _).mp rest with ⟨right, rightRead, last⟩
      rw [← Option.some.inj last]
      exact disjunction_readout (raw_predicate_readout headers first scope left leftRead)
        (raw_predicate_readout headers second scope right rightRead)
  | _, .implies first second, scope, value, evaluated => by
      change bindResult ((data headers).evaluatePredicate scope.semantic first) (fun first =>
        bindResult ((data headers).evaluatePredicate scope.semantic second)
          (fun second => some (first ⇨ second))) = some value at evaluated
      rcases (bindResult_eq_some_iff _ _ _).mp evaluated with ⟨left, leftRead, rest⟩
      rcases (bindResult_eq_some_iff _ _ _).mp rest with ⟨right, rightRead, last⟩
      rw [← Option.some.inj last]
      exact implication_readout (raw_predicate_readout headers first scope left leftRead)
        (raw_predicate_readout headers second scope right rightRead)
  | _, .all domain predicate, scope, value, evaluated => by
      change bindResult ((data headers).evaluateType scope.semantic domain) (fun A =>
        bindResult ((data headers).evaluatePredicate (scope.semantic.snoc A) predicate)
          (fun body => some (Quantifiers.all A body))) = some value at evaluated
      rcases (bindResult_eq_some_iff _ _ _).mp evaluated with ⟨A, domainRead, rest⟩
      rcases (bindResult_eq_some_iff _ _ _).mp rest with ⟨body, bodyRead, last⟩
      rw [← Option.some.inj last]
      exact universal_readout (raw_type_readout headers domain scope A domainRead)
        (raw_predicate_readout headers predicate (scope.snoc A) body bodyRead)
  | _, .exists domain predicate, scope, value, evaluated => by
      change bindResult ((data headers).evaluateType scope.semantic domain) (fun A =>
        bindResult ((data headers).evaluatePredicate (scope.semantic.snoc A) predicate)
          (fun body => some (Quantifiers.some A body))) = some value at evaluated
      rcases (bindResult_eq_some_iff _ _ _).mp evaluated with ⟨A, domainRead, rest⟩
      rcases (bindResult_eq_some_iff _ _ _).mp rest with ⟨body, bodyRead, last⟩
      rw [← Option.some.inj last]
      exact existential_readout (raw_type_readout headers domain scope A domainRead)
        (raw_predicate_readout headers predicate (scope.snoc A) body bodyRead)
  | _, .holds term, scope, value, evaluated => by
      change bindResult (Abstract.ModelData.check? ((data headers).evaluateTerm scope.semantic term)
        (PropositionModel.omega _)) (fun term => some (PropositionModel.holds term)) =
          some value at evaluated
      rcases (bindResult_eq_some_iff _ _ _).mp evaluated with ⟨termValue, checked, last⟩
      have termRead := (Abstract.ModelData.check?_eq_some_iff _ _ _).mp checked
      rw [← Option.some.inj last]
      exact holds_readout termValue (raw_term_readout headers term scope _ termRead)
  | _, .image domain, scope, value, evaluated => by
      change bindResult ((data headers).evaluateType scope.semantic domain)
        (fun A => some (Quantifiers.some A ⊤)) = some value at evaluated
      rcases (bindResult_eq_some_iff _ _ _).mp evaluated with ⟨A, domainRead, last⟩
      rw [← Option.some.inj last]
      exact image_readout (raw_type_readout headers domain scope A domainRead)

end

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Contextual.SyntacticReification
