import Mettapedia.OSLF.Syntax.RhoFreePresheafEvents
import Mettapedia.OSLF.Syntax.RepresentedReductionTheory
import Mettapedia.GSLT.Topos.PredicateFibration

/-!
# Represented reduction for the authored reflective rho presentation

The Chapter 7 COMM/Drop graph retains firing occurrences. Its endpoint image
also supplies a represented rewrite relation in the presheaf lambda theory
over the intrinsic substitution-context category. The representation theorem
relates all generalized terms, not just closed process states.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.RhoRepresentedReduction

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open Mettapedia.GSLT.Core
open Mettapedia.GSLT.Meredith
open Mettapedia.OSLF.Binding.RhoFreePresheafEvents
open Mettapedia.OSLF.Binding.RepresentedReductionTheory
open Mettapedia.OSLF.Binding.RhoSchema (sig)
open Mettapedia.OSLF.Binding.StableRewriteRelationBoundary
open Mettapedia.OSLF.Binding.FreePresheafEventExtension

/-- The actual presheaf category of rho substitution contexts, with its
categorical predicate fibers. -/
noncomputable def baseTheory : LambdaTheoryWithEquality where
  Obj := base ⥤ Type
  instCategory := inferInstance
  instCartesianMonoidal := inferInstance
  instMonoidalClosed := inferInstance
  instHasFiniteLimits := inferInstance
  fibration :=
    (Mettapedia.GSLT.Topos.presheafPredicateFib
      (C := Mettapedia.OSLF.Binding.Syntactic.Ctxt
        Mettapedia.OSLF.Binding.RhoSchema.sig)).toSubobjectFibration

/-- The stable operational interface does not erase the distinction between
its event graph and its endpoint-existence relation. -/
noncomputable def operationalTheory : LambdaTheory where
  toLambdaTheoryWithEquality := baseTheory
  Pr := states
  rewriteRel := AuthoredContextualReduction
  rewriteRel_nat := by
    intro Γ Δ substitution source target fires
    exact authoredReduction_precomp substitution source target fires

/-- The proved representation of rho's authored reduction in the operational
theory's actual categorical product of process-state presheaves. -/
noncomputable def representation : ReductionRepresentation operationalTheory where
  subobject := by
    change Subobject (states ⨯ states)
    exact sourceReductionSubobject
  represents := by
    intro Γ source target
    change AuthoredContextualReduction source target ↔
      sourceReductionSubobject.Factors (prod.lift source target)
    exact authoredReduction_iff_factors source target

/-- A retained authored step is a point of the categorical reduction
subobject; the mono forgets which event supplied it. -/
theorem authored_rewrite_iff_factors {test : base ⥤ Type}
    (source target : test ⟶ states) :
    operationalTheory.rewriteRel source target ↔
      representation.subobject.Factors (prod.lift source target) := by
  exact representation.rewrite_iff_factors operationalTheory source target

/-- The internal truth-value map for rho's endpoint-existence reduction.
It factors through the chosen product comparison, so its domain is the actual
categorical pair of state presheaves. -/
noncomputable def reductionCharacteristic :
    states ⨯ states ⟶
      Mettapedia.GSLT.Topos.omegaFunctor
        (C := Mettapedia.OSLF.Binding.Syntactic.Ctxt sig) :=
  stateProductIso.hom ≫
    Mettapedia.GSLT.Topos.chiOfSubfunctor _ sourceReduction

/-- At every generalized context, an authored rewrite is true at the identity
of the characteristic sieve exactly when its endpoint pair is admitted. -/
theorem authored_rewrite_iff_characteristic_truth {test : base ⥤ Type}
    (source target : test ⟶ states) :
    operationalTheory.rewriteRel source target ↔
      ∀ (X : base) (point : test.obj X),
        (reductionCharacteristic.app X
          ((prod.lift source target).app X point)).arrows (𝟙 X.unop) := by
  rw [authored_rewrite_iff_factors]
  change sourceReductionSubobject.Factors (prod.lift source target) ↔ _
  rw [sourceReductionSubobject_factors_iff]
  have factorization := subfunctor_factors_iff_pointwise sourceReduction
    (prod.lift source target ≫ stateProductIso.hom)
  have truth := subfunctor_factors_iff_characteristic_truth sourceReduction
    (prod.lift source target ≫ stateProductIso.hom)
  change (∀ (X : base) (point : test.obj X),
      (prod.lift source target ≫ stateProductIso.hom).app X point ∈
        sourceReduction.obj X) ↔
    ∀ (X : base) (point : test.obj X),
      ((Mettapedia.GSLT.Topos.chiOfSubfunctor _ sourceReduction).app X
        ((prod.lift source target ≫ stateProductIso.hom).app X point)).arrows
          (𝟙 X.unop)
  exact factorization.symm.trans truth

/-- The proposition-valued reduction is inhabited by an authored firing at
every generalized point. These witnesses retain rule and location data in the
edge presheaf, even if distinct witnesses have the same endpoint pair. -/
theorem authored_rewrite_iff_event_witnesses {test : base ⥤ Type}
    (source target : test ⟶ states) :
    operationalTheory.rewriteRel source target ↔
      ∀ (X : base) (point : test.obj X),
        ∃ event :
          (freeObject sourceEvents (emptyGraph states)).graph.edge.obj X,
          (freeObject sourceEvents (emptyGraph states)).graph.source.app X event =
            source.app X point ∧
          (freeObject sourceEvents (emptyGraph states)).graph.target.app X event =
            target.app X point := by
  change AuthoredContextualReduction source target ↔ _
  unfold AuthoredContextualReduction
  constructor
  · intro held X point
    exact (free_endpoint_image_iff_reduction X
      (source.app X point, target.app X point)).2 (held X point)
  · intro held X point
    exact (free_endpoint_image_iff_reduction X
      (source.app X point, target.app X point)).1 (held X point)

end Mettapedia.OSLF.Binding.RhoRepresentedReduction
