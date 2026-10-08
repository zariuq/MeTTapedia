import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementPrimitiveCellIdentity
import Mettapedia.TypeTheory.ContextualProductCellUniqueness
import Mettapedia.TypeTheory.ContextualPredicateRefinementDisplayPreservation

/-!
# Constructor propagation from local declaration readings

Actual successful evaluation supplies each dependent domain and codomain,
refinement predicate and satisfying assumption. Cartesian naturality forces
primitive and ordinary proposition displays. Dependent function evaluation
and target eta force products; tuple comprehension forces sums. The earned
mapped monicity of refinement forgetting and assumption inclusion forces
their complete context components. No equality at all generated contexts,
families or predicates is assumed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Abstract.ModelCellIdentity

open _root_.CategoryTheory
open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.ContextualPredicateModel
open Mettapedia.TypeTheory.ContextualPredicateModelScopes
open Mettapedia.TypeTheory.ContextualPredicateMorphism
open Mettapedia.TypeTheory.ContextualPredicateCellIdentity
open Mettapedia.TypeTheory.ContextualCartesianCellIdentity
open Mettapedia.TypeTheory.ContextualTypeOperations
open Mettapedia.TypeTheory.ContextualPiEta
open Mettapedia.TypeTheory.ContextualLogicalMorphism
open External (bindResult_eq_some_iff)

universe a c s t m p q
variable {S : Symbols.{a}} {C E : CwfWithTerminal.{c,s,t,m}}
  {sourceModel : LocalModel.{c,s,t,m,p} C}
  {targetModel : LocalModel.{c,s,t,m,q} E}
variable (source : ModelData S C sourceModel)
  (mapping : StrictCwfMorphism C E)
  (cell : mapping.toFamilyMorphism.base ⟶ mapping.toFamilyMorphism.base)
  (sourceStable : StrictPiSubstitution sourceModel.products)
  (targetStable : StrictPiSubstitution targetModel.products)
  (targetEta : PiEta targetModel.products targetStable.1)
  (products : PiPreservation mapping sourceModel.products targetModel.products)
  (predicates : PredicateLogicalPreservation mapping sourceModel targetModel)
  (primitive : PrimitiveIdentity source mapping cell)

include sourceStable targetStable targetEta products predicates primitive

theorem type_success_fixed : {n : Nat} →
    (Γ : ModelScope C sourceModel n) → (type : TypeExpr S n) → (A : C.toCwf.Ty Γ.1) →
    source.evaluateType Γ type = some A →
    cell.app ⟨Γ.1⟩ = 𝟙 (mapping.toFamilyMorphism.base.obj ⟨Γ.1⟩) →
    cell.app ⟨C.toCwf.ext Γ.1 A⟩ =
      𝟙 (mapping.toFamilyMorphism.base.obj ⟨C.toCwf.ext Γ.1 A⟩)
  | _, Γ, .family symbol arguments, A, evaluated, baseFixed =>
      family_success_fixed source mapping cell primitive Γ symbol arguments A evaluated baseFixed
  | _, Γ, .propositions, A, evaluated, baseFixed => by
      have actual : sourceModel.propositions.omega Γ.1 = A := Option.some.inj evaluated
      rw [← actual]
      exact omega_fixed mapping cell sourceModel.propositions Γ.1 baseFixed primitive.propositions
  | _, Γ, .pi domain body, A, evaluated, baseFixed => by
      rcases (source.dependentAnnotations_eq_some_iff Γ domain body
        (fun first second => some (sourceModel.products.pi first second)) A).mp evaluated with
          ⟨actualA,actualB,first,second,last⟩
      have result : sourceModel.products.pi actualA actualB = A := Option.some.inj last
      have domainFixed := type_success_fixed Γ domain actualA first baseFixed
      have codomainFixed := type_success_fixed (Γ.snoc actualA) body actualB second domainFixed
      rw [← result]
      exact Mettapedia.TypeTheory.ContextualProductCellUniqueness.product_fixed
        mapping cell sourceModel.products targetModel.products sourceStable.1
          targetStable targetEta products actualA actualB baseFixed domainFixed codomainFixed
  | _, Γ, .sigma domain body, A, evaluated, baseFixed => by
      rcases (source.dependentAnnotations_eq_some_iff Γ domain body
        (fun first second => some (sourceModel.sums.operations.sigma first second)) A).mp
          evaluated with ⟨actualA,actualB,first,second,last⟩
      have result : sourceModel.sums.operations.sigma actualA actualB = A := Option.some.inj last
      have domainFixed := type_success_fixed Γ domain actualA first baseFixed
      have codomainFixed := type_success_fixed (Γ.snoc actualA) body actualB second domainFixed
      rw [← result]
      exact sum_fixed mapping.toFamilyMorphism.base cell sourceModel.sums actualA actualB codomainFixed
  | _, Γ, .comprehension domain predicate, A, evaluated, baseFixed => by
      change External.bindResult (source.evaluateType Γ domain) (fun actualA =>
        External.bindResult (source.evaluatePredicate (Γ.snoc actualA) predicate)
          (fun actualPredicate => some (sourceModel.refinements.refined actualA actualPredicate))) =
            some A at evaluated
      rcases (bindResult_eq_some_iff _ _ _).mp evaluated with ⟨actualA,domainRead,rest⟩
      rcases (bindResult_eq_some_iff _ _ _).mp rest with ⟨actualPredicate,_predicateRead,last⟩
      rw [← Option.some.inj last]
      have ambientFixed := type_success_fixed Γ domain actualA domainRead baseFixed
      exact Mettapedia.TypeTheory.ContextualPredicateRefinementDisplayPreservation.refined_fixed
        predicates.refinements cell actualA actualPredicate ambientFixed
termination_by _ Γ type _ _ _ => sizeOf type

/-- Both binder sorts propagate fixed components through their actual
context construction. The empty case is earned by terminal uniqueness. -/
theorem context_success_fixed : {n : Nat} → (raw : ContextExpr S n) →
    (Γ : ModelScope C sourceModel n) → source.evaluateContext raw = some Γ →
    cell.app ⟨Γ.1⟩ = 𝟙 (mapping.toFamilyMorphism.base.obj ⟨Γ.1⟩)
  | _, .nil, Γ, evaluated => by
      have actual : Scope.nil C sourceModel.doctrine sourceModel.assumptions = Γ :=
        Option.some.inj evaluated
      rw [← actual]
      exact empty_fixed mapping cell
  | _, .snoc previous type, Γ, evaluated => by
      rw [ModelData.evaluateContext] at evaluated
      rcases (bindResult_eq_some_iff _ _ _).mp evaluated with ⟨Δ,first,rest⟩
      rcases (bindResult_eq_some_iff _ _ _).mp rest with ⟨A,second,last⟩
      have actual : Δ.snoc A = Γ := Option.some.inj last
      rw [← actual]
      exact type_success_fixed source mapping cell sourceStable targetStable targetEta
        products predicates primitive Δ type A second (context_success_fixed previous Δ first)
  | _, .assume previous predicate, Γ, evaluated => by
      rw [ModelData.evaluateContext] at evaluated
      rcases (bindResult_eq_some_iff _ _ _).mp evaluated with ⟨Δ,first,rest⟩
      rcases (bindResult_eq_some_iff _ _ _).mp rest with ⟨φ,_predicateRead,last⟩
      have actual : Δ.assume φ = Γ := Option.some.inj last
      rw [← actual]
      exact assumption_fixed predicates.assumptions cell φ (context_success_fixed previous Δ first)

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Abstract.ModelCellIdentity
