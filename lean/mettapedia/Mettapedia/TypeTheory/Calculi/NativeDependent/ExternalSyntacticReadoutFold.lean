import Mettapedia.TypeTheory.Calculi.NativeDependent.ExternalSyntacticScope
import Mettapedia.TypeTheory.Calculi.NativeDependent.ExternalSyntacticPrimitiveReadout
import Mettapedia.TypeTheory.Calculi.NativeDependent.ExternalSyntacticSigmaReadout

/-!
# Simultaneous source readout induction

The induction visits the independently authored type and term expressions,
including every primitive argument and dependent annotation. All source
constructor readouts are earned locally, including the full-motive sum case
and its typed packing comparison. No whole-evaluator or whole-derivation
soundness assumption is used.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.External.Contextual.SyntacticReification

open _root_.CategoryTheory
open Mettapedia.TypeTheory.ContextualModelTelescopes
open Mettapedia.TypeTheory.ContextualSumComprehension
open Mettapedia.TypeTheory.ContextualProductComparison (selfExtend)
open SyntacticModel

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
      have lifted := ((data headers).evaluateType_eq_some_iff _ _ _).mp evaluated
      rw [ModelData.evaluateTypeLifted] at lifted
      rcases (bindResult_eq_some_iff _ _ _).mp lifted with ⟨actual, assembled, last⟩
      have result : (data headers).familyAt symbol actual = value :=
        congrArg ULift.down (Option.some.inj last)
      rw [← result]
      exact family_readout headers scope.source symbol arguments _
        (fun index value read => raw_term_readout headers (arguments index) scope value read) actual assembled
  | _, .pi domain body, scope, value, evaluated => by
      have lifted := ((data headers).evaluateType_eq_some_iff _ _ _).mp evaluated
      rcases ((data headers).dependentAnnotations_eq_some_iff scope.semantic domain body
        (fun A B => some (ULift.up ((data headers).products.pi A B))) (ULift.up value)).mp lifted with
        ⟨A, B, domainRead, bodyRead, last⟩
      have result : Products.pi A B = value := congrArg ULift.down (Option.some.inj last)
      rw [← result]
      exact pi_readout (raw_type_readout headers domain scope A domainRead)
        (raw_type_readout headers body (scope.snoc A) B bodyRead)
  | _, .sigma domain body, scope, value, evaluated => by
      have lifted := ((data headers).evaluateType_eq_some_iff _ _ _).mp evaluated
      rcases ((data headers).dependentAnnotations_eq_some_iff scope.semantic domain body
        (fun A B => some (ULift.up ((data headers).sums.operations.sigma A B))) (ULift.up value)).mp lifted with
        ⟨A, B, domainRead, bodyRead, last⟩
      have result : Sums.sigma A B = value := congrArg ULift.down (Option.some.inj last)
      rw [← result]
      exact sigma_readout (raw_type_readout headers domain scope A domainRead)
        (raw_type_readout headers body (scope.snoc A) B bodyRead)

theorem raw_term_readout (headers : HeaderFormation D) : {n : Nat} →
    (term : TermExpr S n) → (scope : Scope D n) →
    (value : Value (QuotientCwf.cwf D) ((quotientProjection D).obj scope.source)) →
    (data headers).evaluateTerm scope.semantic term = some value →
    TermReadout ((quotientProjection D).obj scope.source) term value
  | _, .var index, scope, value, evaluated => by
      have result : scope.telescope.lookup index = value := Option.some.inj evaluated
      rw [← result]
      exact scope.variable_readout index
  | _, .primitive symbol arguments, scope, value, evaluated => by
      rw [ModelData.evaluateTerm] at evaluated
      rcases (bindResult_eq_some_iff _ _ _).mp evaluated with ⟨actual, assembled, last⟩
      have result : (data headers).primitiveAt symbol actual = value := Option.some.inj last
      rw [← result]
      exact primitive_readout headers scope.source symbol arguments _
        (fun index value read => raw_term_readout headers (arguments index) scope value read) actual assembled
  | _, .lam domain body term, scope, value, evaluated => by
      rcases ((data headers).dependentAnnotations_eq_some_iff scope.semantic domain body
        (fun A B => (data headers).lambda? A B ((data headers).evaluateTerm (scope.semantic.snoc A) term))
        value).mp evaluated with ⟨A, B, domainRead, bodyRead, last⟩
      have checked := last
      rw [ModelData.lambda?] at checked
      rcases (bindResult_eq_some_iff _ _ _).mp checked with ⟨b, bodyChecked, _⟩
      have termRead := (ModelData.check?_eq_some_iff _ _ _).mp bodyChecked
      rw [termRead, ModelData.lambda?_supplied] at last
      rw [← Option.some.inj last]
      exact lambda_readout (raw_type_readout headers domain scope A domainRead)
        (raw_type_readout headers body (scope.snoc A) B bodyRead) b
        (raw_term_readout headers term (scope.snoc A) _ termRead)
  | _, .app domain body function argument, scope, value, evaluated => by
      rcases ((data headers).dependentAnnotations_eq_some_iff scope.semantic domain body
        (fun A B => (data headers).application? A B ((data headers).evaluateTerm scope.semantic function)
          ((data headers).evaluateTerm scope.semantic argument)) value).mp evaluated with
        ⟨A, B, domainRead, bodyRead, last⟩
      have checked := last
      rw [ModelData.application?] at checked
      rcases (bindResult_eq_some_iff _ _ _).mp checked with ⟨f, functionChecked, rest⟩
      rcases (bindResult_eq_some_iff _ _ _).mp rest with ⟨a, argumentChecked, _⟩
      have functionRead := (ModelData.check?_eq_some_iff _ _ _).mp functionChecked
      have argumentRead := (ModelData.check?_eq_some_iff _ _ _).mp argumentChecked
      rw [functionRead, argumentRead, ModelData.application?_supplied] at last
      rw [← Option.some.inj last]
      exact application_readout (raw_type_readout headers domain scope A domainRead)
        (raw_type_readout headers body (scope.snoc A) B bodyRead) f a
        (raw_term_readout headers function scope _ functionRead)
        (raw_term_readout headers argument scope _ argumentRead)
  | _, .pair domain body first second, scope, value, evaluated => by
      rcases ((data headers).dependentAnnotations_eq_some_iff scope.semantic domain body
        (fun A B => (data headers).pair? A B ((data headers).evaluateTerm scope.semantic first)
          ((data headers).evaluateTerm scope.semantic second)) value).mp evaluated with
        ⟨A, B, domainRead, bodyRead, last⟩
      have checked := last
      rw [ModelData.pair?] at checked
      rcases (bindResult_eq_some_iff _ _ _).mp checked with ⟨a, firstChecked, rest⟩
      rcases (bindResult_eq_some_iff _ _ _).mp rest with ⟨b, secondChecked, _⟩
      have firstRead := (ModelData.check?_eq_some_iff _ _ _).mp firstChecked
      have secondRead := (ModelData.check?_eq_some_iff _ _ _).mp secondChecked
      rw [firstRead, secondRead, ModelData.pair?_supplied] at last
      rw [← Option.some.inj last]
      exact pair_readout (raw_type_readout headers domain scope A domainRead)
        (raw_type_readout headers body (scope.snoc A) B bodyRead) a b
        (raw_term_readout headers first scope _ firstRead)
        (raw_term_readout headers second scope _ secondRead)
  | _, .fst domain body pair, scope, value, evaluated => by
      rcases ((data headers).dependentAnnotations_eq_some_iff scope.semantic domain body
        (fun A B => (data headers).first? A B ((data headers).evaluateTerm scope.semantic pair))
        value).mp evaluated with ⟨A, B, domainRead, bodyRead, last⟩
      have checked := last
      rw [ModelData.first?] at checked
      rcases (bindResult_eq_some_iff _ _ _).mp checked with ⟨p, pairChecked, _⟩
      have pairRead := (ModelData.check?_eq_some_iff _ _ _).mp pairChecked
      rw [pairRead, ModelData.first?_supplied] at last
      rw [← Option.some.inj last]
      exact first_readout (raw_type_readout headers domain scope A domainRead)
        (raw_type_readout headers body (scope.snoc A) B bodyRead) p
        (raw_term_readout headers pair scope _ pairRead)
  | _, .snd domain body pair, scope, value, evaluated => by
      rcases ((data headers).dependentAnnotations_eq_some_iff scope.semantic domain body
        (fun A B => (data headers).second? A B ((data headers).evaluateTerm scope.semantic pair))
        value).mp evaluated with ⟨A, B, domainRead, bodyRead, last⟩
      have checked := last
      rw [ModelData.second?] at checked
      rcases (bindResult_eq_some_iff _ _ _).mp checked with ⟨p, pairChecked, _⟩
      have pairRead := (ModelData.check?_eq_some_iff _ _ _).mp pairChecked
      rw [pairRead, ModelData.second?_supplied] at last
      rw [← Option.some.inj last]
      exact second_readout (raw_type_readout headers domain scope A domainRead)
        (raw_type_readout headers body (scope.snoc A) B bodyRead) p
        (raw_term_readout headers pair scope _ pairRead)
  | _, .sigmaElim domain body motive branch pair, scope, value, evaluated => by
      rcases ((data headers).dependentAnnotations_eq_some_iff scope.semantic domain body
        (fun A B => bindResult
          ((data headers).evaluateTypeLifted (scope.semantic.snoc ((data headers).sums.operations.sigma A B)) motive)
          (fun liftedM => (data headers).sumEliminate? A B liftedM.down
            ((data headers).evaluateTerm ((scope.semantic.snoc A).snoc B) branch)
            ((data headers).evaluateTerm scope.semantic pair))) value).mp evaluated with
        ⟨A, B, domainRead, bodyRead, motiveLast⟩
      rcases (bindResult_eq_some_iff _ _ _).mp motiveLast with ⟨liftedM, motiveRead, last⟩
      have motiveOrdinary := ((data headers).evaluateType_eq_some_iff _ _ _).mpr motiveRead
      have checked := last
      rw [ModelData.sumEliminate?] at checked
      rcases (bindResult_eq_some_iff _ _ _).mp checked with ⟨b, branchChecked, rest⟩
      rcases (bindResult_eq_some_iff _ _ _).mp rest with ⟨p, pairChecked, _⟩
      have branchRead := (ModelData.check?_eq_some_iff _ _ _).mp branchChecked
      have pairRead := (ModelData.check?_eq_some_iff _ _ _).mp pairChecked
      rw [branchRead, pairRead, ModelData.sumEliminate?_supplied] at last
      rw [← Option.some.inj last]
      exact sigma_elimination_readout
        (raw_type_readout headers domain scope A domainRead)
        (raw_type_readout headers body (scope.snoc A) B bodyRead)
        (raw_type_readout headers motive (scope.snoc (Sums.sigma A B)) liftedM.down motiveOrdinary)
        b p (raw_term_readout headers branch ((scope.snoc A).snoc B) _ branchRead)
        (raw_term_readout headers pair scope _ pairRead)

end

end Mettapedia.TypeTheory.Calculi.NativeDependent.External.Contextual.SyntacticReification
