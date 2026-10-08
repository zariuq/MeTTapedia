import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementAbstractModelUniverseLift
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementAbstractSoundnessLogic
import Mettapedia.TypeTheory.ContextualPredicateModelValueUniverseLift

/-!
# Authored refinement readouts through carrier changes

The mutually recursive comparison visits every annotated type, term and
predicate constructor. Each successful read retains its family, complete
section and predicate. Primitive arguments retain all mixed-scope guards.
The carrier change introduces no object-language universe or data choice.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Abstract

open Mettapedia.GSLT.Core.ContextualLadder
open ContextualPredicateModel ContextualPredicateModelScopes ContextualModelTelescopes
open ContextualCwfUniverseLift ContextualPredicateModelScopeUniverseLift
open ContextualSumComprehension
open ContextualProductComparison (selfExtend)
open External (bindResult)

attribute [local instance] ContextualPredicateModelUniverseLift.liftedHeytingAlgebra

universe a c s t m p uc vs wt ms ps
variable {S : Symbols.{a}} {C : CwfWithTerminal.{c,s,t,m}}
variable {localModel : LocalModel.{c,s,t,m,p} C}

namespace ModelData

mutual

theorem evaluateType_carrierLift (model : ModelData S C localModel) :
    {n : Nat} → (type : TypeExpr S n) → (Γ : ModelScope C localModel n) → (A : C.toCwf.Ty Γ.1) →
    model.evaluateType Γ type = some A →
    (model.lift.{a, c, s, t, m, p, uc, vs, wt, ms, ps}).evaluateType
      (liftScope.{c, s, t, m, p, uc, vs, wt, ms, ps} Γ) type = some (ULift.up A)
  | _, .family symbol arguments, Γ, A, evaluated => by
      change bindResult ((model.typeParameters symbol).2.assemble?
        (fun index => model.evaluateTerm Γ (arguments index))) _ = some A at evaluated
      rcases (External.bindResult_eq_some_iff _ _ _).mp evaluated with ⟨σ, assembled, last⟩
      have actual : model.familyAt symbol σ = A := Option.some.inj last
      rw [← actual]
      apply model.lift.{a, c, s, t, m, p, uc, vs, wt, ms, ps}.evaluate_family (liftScope.{c, s, t, m, p, uc, vs, wt, ms, ps} Γ) symbol arguments (ULift.up σ)
      intro index
      have read := (ScopeData.assemble?_eq_some_iff _ _ σ).mp assembled index
      exact (evaluateTerm_carrierLift model (arguments index) Γ _ read).trans
        (congrArg some (liftScopeData_components.{c, s, t, m, p, uc, vs, wt, ms, ps} (model.typeParameters symbol).2 σ index).symm)
  | _, .pi domain body, Γ, result, evaluated => by
      rcases (model.dependentAnnotations_eq_some_iff Γ domain body
        (fun A B => some (localModel.products.pi A B)) result).mp evaluated with
        ⟨A, B, domainRead, bodyRead, last⟩
      have actual : localModel.products.pi A B = result := Option.some.inj last
      rw [← actual]
      exact model.lift.{a, c, s, t, m, p, uc, vs, wt, ms, ps}.evaluate_pi (liftScope.{c, s, t, m, p, uc, vs, wt, ms, ps} Γ) domain body (ULift.up A) (ULift.up B)
        (evaluateType_carrierLift model domain Γ A domainRead)
        (evaluateType_carrierLift model body (Γ.snoc A) B bodyRead)
  | _, .sigma domain body, Γ, result, evaluated => by
      rcases (model.dependentAnnotations_eq_some_iff Γ domain body
        (fun A B => some (localModel.sums.operations.sigma A B)) result).mp evaluated with
        ⟨A, B, domainRead, bodyRead, last⟩
      have actual : localModel.sums.operations.sigma A B = result := Option.some.inj last
      rw [← actual]
      exact model.lift.{a, c, s, t, m, p, uc, vs, wt, ms, ps}.evaluate_sigma (liftScope.{c, s, t, m, p, uc, vs, wt, ms, ps} Γ) domain body (ULift.up A) (ULift.up B)
        (evaluateType_carrierLift model domain Γ A domainRead)
        (evaluateType_carrierLift model body (Γ.snoc A) B bodyRead)
  | _, .propositions, Γ, result, evaluated => by
      have actual : localModel.propositions.omega Γ.1 = result := Option.some.inj evaluated
      rw [← actual]
      rfl
  | _, .comprehension domain predicate, Γ, result, evaluated => by
      change bindResult (model.evaluateType Γ domain) (fun A =>
        bindResult (model.evaluatePredicate (Γ.snoc A) predicate)
          (fun φ => some (localModel.refinements.refined A φ))) = some result at evaluated
      rcases (External.bindResult_eq_some_iff _ _ _).mp evaluated with ⟨A, domainRead, rest⟩
      rcases (External.bindResult_eq_some_iff _ _ _).mp rest with ⟨φ, predicateRead, last⟩
      rw [← Option.some.inj last]
      exact model.lift.{a,c,s,t,m,p,uc,vs,wt,ms,ps}.evaluate_comprehension
        (liftScope.{c,s,t,m,p,uc,vs,wt,ms,ps} Γ) domain predicate (ULift.up A) (ULift.up φ)
        (evaluateType_carrierLift model domain Γ A domainRead)
        (evaluatePredicate_carrierLift model predicate (Γ.snoc A) φ predicateRead)

theorem evaluateTerm_carrierLift (model : ModelData S C localModel) :
    {n : Nat} → (term : TermExpr S n) → (Γ : ModelScope C localModel n) → (value : Value C.toCwf Γ.1) →
    model.evaluateTerm Γ term = some value →
    (model.lift.{a, c, s, t, m, p, uc, vs, wt, ms, ps}).evaluateTerm
      (liftScope.{c, s, t, m, p, uc, vs, wt, ms, ps} Γ) term = some (liftValue.{c, s, t, m, uc, vs, wt, ms} value)
  | _, .var index, Γ, value, evaluated => by
      have actual : Γ.2.lookup index = value := Option.some.inj evaluated
      rw [← actual]
      exact congrArg some (liftScopeData_lookup.{c, s, t, m, p, uc, vs, wt, ms, ps} Γ.2 index)
  | _, .primitive symbol arguments, Γ, value, evaluated => by
      change bindResult ((model.termParameters symbol).2.assemble?
        (fun index => model.evaluateTerm Γ (arguments index))) _ = some value at evaluated
      rcases (External.bindResult_eq_some_iff _ _ _).mp evaluated with ⟨σ, assembled, last⟩
      have actual : model.primitiveAt symbol σ = value := Option.some.inj last
      rw [← actual]
      apply model.lift.{a, c, s, t, m, p, uc, vs, wt, ms, ps}.evaluate_primitive (liftScope.{c, s, t, m, p, uc, vs, wt, ms, ps} Γ) symbol arguments (ULift.up σ)
      intro index
      have read := (ScopeData.assemble?_eq_some_iff _ _ σ).mp assembled index
      exact (evaluateTerm_carrierLift model (arguments index) Γ _ read).trans
        (congrArg some (liftScopeData_components.{c, s, t, m, p, uc, vs, wt, ms, ps} (model.termParameters symbol).2 σ index).symm)
  | _, .lam domain body term, Γ, value, evaluated => by
      rcases (model.dependentAnnotations_eq_some_iff Γ domain body
        (fun A B => lambda? localModel A B (model.evaluateTerm (Γ.snoc A) term)) value).mp evaluated with
        ⟨A, B, domainRead, bodyRead, last⟩
      have checked := last
      rw [lambda?] at checked
      rcases (External.bindResult_eq_some_iff _ _ _).mp checked with ⟨b, bodyChecked, _⟩
      have termRead := (check?_eq_some_iff _ _ _).mp bodyChecked
      rw [termRead, lambda?_supplied] at last
      have actual : (⟨localModel.products.pi A B, localModel.products.lam b⟩ : Value C.toCwf Γ.1) = value :=
        Option.some.inj last
      rw [← actual]
      exact model.lift.{a, c, s, t, m, p, uc, vs, wt, ms, ps}.evaluate_lambda (liftScope.{c, s, t, m, p, uc, vs, wt, ms, ps} Γ) domain body (ULift.up A) (ULift.up B)
        (evaluateType_carrierLift model domain Γ A domainRead)
        (evaluateType_carrierLift model body (Γ.snoc A) B bodyRead) term (ULift.up b)
        (evaluateTerm_carrierLift model term (Γ.snoc A) _ termRead)
  | _, .app domain body function argument, Γ, value, evaluated => by
      rcases (model.dependentAnnotations_eq_some_iff Γ domain body
        (fun A B => application? localModel A B (model.evaluateTerm Γ function)
          (model.evaluateTerm Γ argument)) value).mp evaluated with
        ⟨A, B, domainRead, bodyRead, last⟩
      have checked := last
      rw [application?] at checked
      rcases (External.bindResult_eq_some_iff _ _ _).mp checked with ⟨f, functionChecked, rest⟩
      rcases (External.bindResult_eq_some_iff _ _ _).mp rest with ⟨a, argumentChecked, _⟩
      have functionRead := (check?_eq_some_iff _ _ _).mp functionChecked
      have argumentRead := (check?_eq_some_iff _ _ _).mp argumentChecked
      rw [functionRead, argumentRead, application?_supplied] at last
      rw [← Option.some.inj last]
      exact (model.lift.{a, c, s, t, m, p, uc, vs, wt, ms, ps}.evaluate_application (liftScope.{c, s, t, m, p, uc, vs, wt, ms, ps} Γ) domain body (ULift.up A) (ULift.up B)
        (evaluateType_carrierLift model domain Γ A domainRead)
        (evaluateType_carrierLift model body (Γ.snoc A) B bodyRead) function argument
        (ULift.up f) (ULift.up a)
        (evaluateTerm_carrierLift model function Γ _ functionRead)
        (evaluateTerm_carrierLift model argument Γ _ argumentRead)).trans
          (congrArg some (ContextualPredicateModelUniverseLift.lift_application_value localModel A B f a))
  | _, .pair domain body first second, Γ, value, evaluated => by
      rcases (model.dependentAnnotations_eq_some_iff Γ domain body
        (fun A B => pair? localModel A B (model.evaluateTerm Γ first)
          (model.evaluateTerm Γ second)) value).mp evaluated with
        ⟨A, B, domainRead, bodyRead, last⟩
      have checked := last
      rw [pair?] at checked
      rcases (External.bindResult_eq_some_iff _ _ _).mp checked with ⟨a, firstChecked, rest⟩
      rcases (External.bindResult_eq_some_iff _ _ _).mp rest with ⟨b, secondChecked, _⟩
      have firstRead := (check?_eq_some_iff _ _ _).mp firstChecked
      have secondRead := (check?_eq_some_iff _ _ _).mp secondChecked
      rw [firstRead, secondRead, pair?_supplied] at last
      rw [← Option.some.inj last]
      rcases liftedValue_at_type.{c, s, t, m, uc, vs, wt, ms} (C.toCwf.tySub B (selfExtend C.toCwf a)) b
        ((Raised.{c, s, t, m, uc, vs, wt, ms} C.toCwf).tySub (ULift.up B) (selfExtend (Raised.{c, s, t, m, uc, vs, wt, ms} C.toCwf) (ULift.up a)))
        (congrArg (C.toCwf.tySub B) (selfExtend_readout.{c, s, t, m, uc, vs, wt, ms} (C := C.toCwf) (context := ULift.up Γ.1) (ULift.up a))) with ⟨b', valueRead, bodies⟩
      have secondImage := (evaluateTerm_carrierLift model second Γ _ secondRead).trans
        (congrArg some valueRead)
      exact (model.lift.{a, c, s, t, m, p, uc, vs, wt, ms, ps}.evaluate_pair (liftScope.{c, s, t, m, p, uc, vs, wt, ms, ps} Γ) domain body (ULift.up A) (ULift.up B)
        (evaluateType_carrierLift model domain Γ A domainRead)
        (evaluateType_carrierLift model body (Γ.snoc A) B bodyRead) first second (ULift.up a) b'
        (evaluateTerm_carrierLift model first Γ _ firstRead) secondImage).trans
          (congrArg some (ContextualPredicateModelUniverseLift.lift_pair_value localModel A B a b b' bodies))
  | _, .fst domain body pair, Γ, value, evaluated => by
      rcases (model.dependentAnnotations_eq_some_iff Γ domain body
        (fun A B => first? localModel A B (model.evaluateTerm Γ pair)) value).mp evaluated with
        ⟨A, B, domainRead, bodyRead, last⟩
      have checked := last
      rw [first?] at checked
      rcases (External.bindResult_eq_some_iff _ _ _).mp checked with ⟨p, pairChecked, _⟩
      have pairRead := (check?_eq_some_iff _ _ _).mp pairChecked
      rw [pairRead, first?_supplied] at last
      rw [← Option.some.inj last]
      exact model.lift.{a, c, s, t, m, p, uc, vs, wt, ms, ps}.evaluate_first (liftScope.{c, s, t, m, p, uc, vs, wt, ms, ps} Γ) domain body (ULift.up A) (ULift.up B)
        (evaluateType_carrierLift model domain Γ A domainRead)
        (evaluateType_carrierLift model body (Γ.snoc A) B bodyRead) pair (ULift.up p)
        (evaluateTerm_carrierLift model pair Γ _ pairRead)
  | _, .snd domain body pair, Γ, value, evaluated => by
      rcases (model.dependentAnnotations_eq_some_iff Γ domain body
        (fun A B => second? localModel A B (model.evaluateTerm Γ pair)) value).mp evaluated with
        ⟨A, B, domainRead, bodyRead, last⟩
      have checked := last
      rw [second?] at checked
      rcases (External.bindResult_eq_some_iff _ _ _).mp checked with ⟨p, pairChecked, _⟩
      have pairRead := (check?_eq_some_iff _ _ _).mp pairChecked
      rw [pairRead, second?_supplied] at last
      rw [← Option.some.inj last]
      exact (model.lift.{a, c, s, t, m, p, uc, vs, wt, ms, ps}.evaluate_second (liftScope.{c, s, t, m, p, uc, vs, wt, ms, ps} Γ) domain body (ULift.up A) (ULift.up B)
        (evaluateType_carrierLift model domain Γ A domainRead)
        (evaluateType_carrierLift model body (Γ.snoc A) B bodyRead) pair (ULift.up p)
        (evaluateTerm_carrierLift model pair Γ _ pairRead)).trans
          (congrArg some (ContextualPredicateModelUniverseLift.lift_second_value localModel A B p))
  | _, .sigmaElim domain body motive branch pair, Γ, value, evaluated => by
      rcases (model.dependentAnnotations_eq_some_iff Γ domain body
        (fun A B => bindResult
          (model.evaluateType (Γ.snoc (localModel.sums.operations.sigma A B)) motive)
          (fun M => sumEliminate? localModel A B M
            (model.evaluateTerm ((Γ.snoc A).snoc B) branch) (model.evaluateTerm Γ pair))) value).mp
              evaluated with ⟨A, B, domainRead, bodyRead, rest⟩
      rcases (External.bindResult_eq_some_iff _ _ _).mp rest with ⟨M, motiveRead, last⟩
      have checked := last
      rw [sumEliminate?] at checked
      rcases (External.bindResult_eq_some_iff _ _ _).mp checked with ⟨b, branchChecked, remaining⟩
      rcases (External.bindResult_eq_some_iff _ _ _).mp remaining with ⟨p, pairChecked, _⟩
      have branchRead := (check?_eq_some_iff _ _ _).mp branchChecked
      have pairRead := (check?_eq_some_iff _ _ _).mp pairChecked
      rw [branchRead, pairRead, sumEliminate?_supplied] at last
      rw [← Option.some.inj last]
      rcases liftedValue_at_type.{c, s, t, m, uc, vs, wt, ms} (C.toCwf.tySub M (pack localModel.sums A B)) b
        ((Raised.{c, s, t, m, uc, vs, wt, ms} C.toCwf).tySub (ULift.up M)
          (pack (Γ := ULift.up Γ.1) (liftStableSums localModel.sums) (ULift.up A) (ULift.up B)))
        (congrArg (C.toCwf.tySub M) (pack_down.{c, s, t, m, uc, vs, wt, ms} (C := C.toCwf) (Γ := ULift.up Γ.1) localModel.sums (ULift.up A) (ULift.up B))) with
          ⟨b', valueRead, branches⟩
      have branchImage := (evaluateTerm_carrierLift model branch ((Γ.snoc A).snoc B) _ branchRead).trans
        (congrArg some valueRead)
      exact (model.lift.{a, c, s, t, m, p, uc, vs, wt, ms, ps}.evaluate_sumElimination (liftScope.{c, s, t, m, p, uc, vs, wt, ms, ps} Γ) domain body (ULift.up A) (ULift.up B)
        (evaluateType_carrierLift model domain Γ A domainRead)
        (evaluateType_carrierLift model body (Γ.snoc A) B bodyRead) motive branch pair (ULift.up M) b'
        (ULift.up p)
        (evaluateType_carrierLift model motive (Γ.snoc (localModel.sums.operations.sigma A B)) M motiveRead)
        branchImage (evaluateTerm_carrierLift model pair Γ _ pairRead)).trans
          (congrArg some (ContextualPredicateModelUniverseLift.lift_elimination_value localModel A B M b b' branches p))
  | _, .quote predicate, Γ, value, evaluated => by
      change bindResult (model.evaluatePredicate Γ predicate)
        (fun φ => some (⟨localModel.propositions.omega Γ.1,
          localModel.propositions.quote φ⟩ : Value C.toCwf Γ.1)) = some value at evaluated
      rcases (External.bindResult_eq_some_iff _ _ _).mp evaluated with ⟨φ, predicateRead, last⟩
      rw [← Option.some.inj last]
      exact model.lift.{a,c,s,t,m,p,uc,vs,wt,ms,ps}.evaluate_quote
        (liftScope.{c,s,t,m,p,uc,vs,wt,ms,ps} Γ) predicate (ULift.up φ)
        (evaluatePredicate_carrierLift model predicate Γ φ predicateRead)
  | _, .refine domain predicate term, Γ, value, evaluated => by
      change bindResult (model.evaluateType Γ domain) (fun A =>
        bindResult (model.evaluatePredicate (Γ.snoc A) predicate)
          (fun φ => refine? localModel A φ (model.evaluateTerm Γ term))) = some value at evaluated
      rcases (External.bindResult_eq_some_iff _ _ _).mp evaluated with ⟨A, domainRead, rest⟩
      rcases (External.bindResult_eq_some_iff _ _ _).mp rest with ⟨φ, predicateRead, last⟩
      rcases (refine?_eq_some_iff localModel A φ _ value).mp last with
        ⟨supplied, guard, termRead, actual⟩
      rw [← actual]
      have liftedGuard :
          (ContextualPredicateModelUniverseLift.liftDoctrine.{c,s,t,m,p,uc,vs,wt,ms,ps} localModel.doctrine).reindex
            (selfExtend (Raised.{c,s,t,m,uc,vs,wt,ms} C.toCwf)
              (context := ULift.up Γ.1) (type := ULift.up A) (ULift.up supplied)) (ULift.up φ) =
                (⊤ : ULift.{ps} (localModel.doctrine.Predicate Γ.1)) := by
        apply ULift.ext
        change localModel.doctrine.reindex
          (selfExtend (Raised.{c,s,t,m,uc,vs,wt,ms} C.toCwf)
            (context := ULift.up Γ.1) (type := ULift.up A) (ULift.up supplied)).down φ = ⊤
        exact (congrArg (fun substitution => localModel.doctrine.reindex substitution φ)
          (selfExtend_readout.{c,s,t,m,uc,vs,wt,ms} (C := C.toCwf)
            (context := ULift.up Γ.1) (type := ULift.up A) (ULift.up supplied))).trans guard
      exact model.lift.{a,c,s,t,m,p,uc,vs,wt,ms,ps}.evaluate_refine
        (liftScope.{c,s,t,m,p,uc,vs,wt,ms,ps} Γ) domain predicate term
        (ULift.up A) (ULift.up φ) (ULift.up supplied)
        (evaluateType_carrierLift model domain Γ A domainRead)
        (evaluatePredicate_carrierLift model predicate (Γ.snoc A) φ predicateRead)
        (evaluateTerm_carrierLift model term Γ _ termRead) liftedGuard
  | _, .forget domain predicate term, Γ, value, evaluated => by
      change bindResult (model.evaluateType Γ domain) (fun A =>
        bindResult (model.evaluatePredicate (Γ.snoc A) predicate)
          (fun φ => forget? localModel A φ (model.evaluateTerm Γ term))) = some value at evaluated
      rcases (External.bindResult_eq_some_iff _ _ _).mp evaluated with ⟨A, domainRead, rest⟩
      rcases (External.bindResult_eq_some_iff _ _ _).mp rest with ⟨φ, predicateRead, last⟩
      have checked := last
      rw [forget?] at checked
      rcases (External.bindResult_eq_some_iff _ _ _).mp checked with ⟨supplied, termChecked, _⟩
      have termRead := (check?_eq_some_iff _ _ _).mp termChecked
      rw [termRead, forget?_supplied] at last
      rw [← Option.some.inj last]
      exact model.lift.{a,c,s,t,m,p,uc,vs,wt,ms,ps}.evaluate_forget
        (liftScope.{c,s,t,m,p,uc,vs,wt,ms,ps} Γ) domain predicate term
        (ULift.up A) (ULift.up φ) (ULift.up supplied)
        (evaluateType_carrierLift model domain Γ A domainRead)
        (evaluatePredicate_carrierLift model predicate (Γ.snoc A) φ predicateRead)
        (evaluateTerm_carrierLift model term Γ _ termRead)

theorem evaluatePredicate_carrierLift (model : ModelData S C localModel) :
    {n : Nat} → (predicate : PropExpr S n) → (Γ : ModelScope C localModel n) →
    (φ : localModel.doctrine.Predicate Γ.1) → model.evaluatePredicate Γ predicate = some φ →
    (model.lift.{a,c,s,t,m,p,uc,vs,wt,ms,ps}).evaluatePredicate
      (liftScope.{c,s,t,m,p,uc,vs,wt,ms,ps} Γ) predicate = some (ULift.up φ)
  | _, .atom symbol arguments, Γ, φ, evaluated => by
      change bindResult ((model.predicateParameters symbol).2.assemble?
        (fun index => model.evaluateTerm Γ (arguments index))) _ = some φ at evaluated
      rcases (External.bindResult_eq_some_iff _ _ _).mp evaluated with ⟨σ, assembled, last⟩
      rw [← Option.some.inj last]
      apply model.lift.{a,c,s,t,m,p,uc,vs,wt,ms,ps}.evaluate_predicateAtom
        (liftScope.{c,s,t,m,p,uc,vs,wt,ms,ps} Γ) symbol arguments (ULift.up σ)
      intro index
      have read := (ScopeData.assemble?_eq_some_iff _ _ σ).mp assembled index
      exact (evaluateTerm_carrierLift model (arguments index) Γ _ read).trans
        (congrArg some (liftScopeData_components.{c,s,t,m,p,uc,vs,wt,ms,ps}
          (model.predicateParameters symbol).2 σ index).symm)
  | _, .truth, Γ, φ, evaluated => by
      have actual : (⊤ : localModel.doctrine.Predicate Γ.1) = φ := Option.some.inj evaluated
      rw [← actual]
      rfl
  | _, .falsehood, Γ, φ, evaluated => by
      have actual : (⊥ : localModel.doctrine.Predicate Γ.1) = φ := Option.some.inj evaluated
      rw [← actual]
      rfl
  | _, .and first second, Γ, φ, evaluated => by
      change bindResult (model.evaluatePredicate Γ first) (fun first =>
        bindResult (model.evaluatePredicate Γ second) (fun second => some (first ⊓ second))) = some φ at evaluated
      rcases (External.bindResult_eq_some_iff _ _ _).mp evaluated with ⟨φ₁, firstRead, rest⟩
      rcases (External.bindResult_eq_some_iff _ _ _).mp rest with ⟨φ₂, secondRead, last⟩
      rw [← Option.some.inj last]
      exact model.lift.{a,c,s,t,m,p,uc,vs,wt,ms,ps}.evaluate_and
        (liftScope.{c,s,t,m,p,uc,vs,wt,ms,ps} Γ) first second (ULift.up φ₁) (ULift.up φ₂)
        (evaluatePredicate_carrierLift model first Γ φ₁ firstRead)
        (evaluatePredicate_carrierLift model second Γ φ₂ secondRead)
  | _, .or first second, Γ, φ, evaluated => by
      change bindResult (model.evaluatePredicate Γ first) (fun first =>
        bindResult (model.evaluatePredicate Γ second) (fun second => some (first ⊔ second))) = some φ at evaluated
      rcases (External.bindResult_eq_some_iff _ _ _).mp evaluated with ⟨φ₁, firstRead, rest⟩
      rcases (External.bindResult_eq_some_iff _ _ _).mp rest with ⟨φ₂, secondRead, last⟩
      rw [← Option.some.inj last]
      exact model.lift.{a,c,s,t,m,p,uc,vs,wt,ms,ps}.evaluate_or
        (liftScope.{c,s,t,m,p,uc,vs,wt,ms,ps} Γ) first second (ULift.up φ₁) (ULift.up φ₂)
        (evaluatePredicate_carrierLift model first Γ φ₁ firstRead)
        (evaluatePredicate_carrierLift model second Γ φ₂ secondRead)
  | _, .implies first second, Γ, φ, evaluated => by
      change bindResult (model.evaluatePredicate Γ first) (fun first =>
        bindResult (model.evaluatePredicate Γ second) (fun second => some (first ⇨ second))) = some φ at evaluated
      rcases (External.bindResult_eq_some_iff _ _ _).mp evaluated with ⟨φ₁, firstRead, rest⟩
      rcases (External.bindResult_eq_some_iff _ _ _).mp rest with ⟨φ₂, secondRead, last⟩
      rw [← Option.some.inj last]
      exact model.lift.{a,c,s,t,m,p,uc,vs,wt,ms,ps}.evaluate_implies
        (liftScope.{c,s,t,m,p,uc,vs,wt,ms,ps} Γ) first second (ULift.up φ₁) (ULift.up φ₂)
        (evaluatePredicate_carrierLift model first Γ φ₁ firstRead)
        (evaluatePredicate_carrierLift model second Γ φ₂ secondRead)
  | _, .all domain predicate, Γ, φ, evaluated => by
      change bindResult (model.evaluateType Γ domain) (fun A =>
        bindResult (model.evaluatePredicate (Γ.snoc A) predicate)
          (fun φ => some (localModel.doctrine.all A φ))) = some φ at evaluated
      rcases (External.bindResult_eq_some_iff _ _ _).mp evaluated with ⟨A, domainRead, rest⟩
      rcases (External.bindResult_eq_some_iff _ _ _).mp rest with ⟨body, predicateRead, last⟩
      rw [← Option.some.inj last]
      exact model.lift.{a,c,s,t,m,p,uc,vs,wt,ms,ps}.evaluate_all
        (liftScope.{c,s,t,m,p,uc,vs,wt,ms,ps} Γ) domain predicate (ULift.up A) (ULift.up body)
        (evaluateType_carrierLift model domain Γ A domainRead)
        (evaluatePredicate_carrierLift model predicate (Γ.snoc A) body predicateRead)
  | _, .exists domain predicate, Γ, φ, evaluated => by
      change bindResult (model.evaluateType Γ domain) (fun A =>
        bindResult (model.evaluatePredicate (Γ.snoc A) predicate)
          (fun φ => some (localModel.doctrine.some A φ))) = some φ at evaluated
      rcases (External.bindResult_eq_some_iff _ _ _).mp evaluated with ⟨A, domainRead, rest⟩
      rcases (External.bindResult_eq_some_iff _ _ _).mp rest with ⟨body, predicateRead, last⟩
      rw [← Option.some.inj last]
      exact model.lift.{a,c,s,t,m,p,uc,vs,wt,ms,ps}.evaluate_exists
        (liftScope.{c,s,t,m,p,uc,vs,wt,ms,ps} Γ) domain predicate (ULift.up A) (ULift.up body)
        (evaluateType_carrierLift model domain Γ A domainRead)
        (evaluatePredicate_carrierLift model predicate (Γ.snoc A) body predicateRead)
  | _, .holds term, Γ, φ, evaluated => by
      change bindResult (check? (model.evaluateTerm Γ term) (localModel.propositions.omega Γ.1))
        (fun supplied => some (localModel.propositions.holds supplied)) = some φ at evaluated
      rcases (External.bindResult_eq_some_iff _ _ _).mp evaluated with ⟨supplied, checked, last⟩
      have termRead := (check?_eq_some_iff _ _ _).mp checked
      rw [← Option.some.inj last]
      exact model.lift.{a,c,s,t,m,p,uc,vs,wt,ms,ps}.evaluate_holds
        (liftScope.{c,s,t,m,p,uc,vs,wt,ms,ps} Γ) term (ULift.up supplied)
        (evaluateTerm_carrierLift model term Γ _ termRead)
  | _, .image type, Γ, φ, evaluated => by
      change bindResult (model.evaluateType Γ type)
        (fun A => some (localModel.doctrine.some A ⊤)) = some φ at evaluated
      rcases (External.bindResult_eq_some_iff _ _ _).mp evaluated with ⟨A, typeRead, last⟩
      rw [← Option.some.inj last]
      exact model.lift.{a,c,s,t,m,p,uc,vs,wt,ms,ps}.evaluate_image
        (liftScope.{c,s,t,m,p,uc,vs,wt,ms,ps} Γ) type (ULift.up A)
        (evaluateType_carrierLift model type Γ A typeRead)


end

end ModelData
end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Abstract
