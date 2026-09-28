import Mettapedia.OSLF.Syntax.FreePresheafEventExtension
import Mettapedia.OSLF.Syntax.RhoSourceEventComparison
import Mettapedia.OSLF.Syntax.ContextualReductionSubobject
import Mathlib.CategoryTheory.Subfunctor.Subobject
import Mathlib.CategoryTheory.Limits.Shapes.FunctorToTypes
import Mettapedia.OSLF.Syntax.StableRewriteRelationBoundary

/-!
# The Chapter 7 rho event generators over source equation classes

The scoped COMM and Drop occurrences form a genuine edge presheaf over the
free source equation model. Their source and target maps are natural under
context substitution. The generic free-event adjunction is instantiated on
this graph, and a concrete Drop firing witnesses that the adjoined summand is
inhabited. This is the graph layer, not the finite-limit/cartesian-closed
classifying theory of the full conditional language.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.RhoFreePresheafEvents

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open Mettapedia.OSLF.Binding.RhoSchema
open Mettapedia.OSLF.Binding.ContextualEquationClassEvents
open Mettapedia.OSLF.Binding.FreePresheafEventExtension
open Mettapedia.OSLF.Binding.ContextualReductionSubobject
open Mettapedia.OSLF.Binding.StableRewriteRelationBoundary

/-- The substitution category in the contravariant direction used by both
equation classes and located event occurrences. -/
abbrev base := (Syntactic.Ctxt sig)ᵒᵖ

/-- Source equation classes, indexed by the ambient context. -/
abbrev states : base ⥤ Type := termQPresheaf rhoSourceE Srt.pr

/-- The actual authored COMM/Drop event graph over those classes. -/
def sourceEvents : Graph states where
  edge := presentationEventPresheaf rhoSourceWithDrop.toUnpositioned Srt.pr
  source := presentationSourceNatural rhoSourceWithDrop.toUnpositioned Srt.pr
  target := presentationTargetNatural rhoSourceWithDrop.toUnpositioned Srt.pr

/-- Adding the Chapter 7 events to any graph over source equation classes is
left adjoint to forgetting their chosen interpretation. -/
def sourceEventAdjunction :
    free sourceEvents ⊣ forget sourceEvents :=
  freeAdjunction sourceEvents

/-- The source event graph freely extends the no-event graph, as an initial
object among graphs equipped with interpretations of the authored firings. -/
def sourceEventsFreeInitial :
    IsInitial (freeObject sourceEvents (emptyGraph states)) :=
  freeGeneratedIsInitial sourceEvents

/-- The closed context as an object of the substitution category. -/
def closedContext : base := Opposite.op ⟨[]⟩

/-- At closed contexts, an edge in the source graph exists exactly when the
actual intrinsic Chapter 7 presentation steps modulo its equations. The edge
itself retains its rule and location beyond this endpoint proposition. -/
theorem closed_endpoints_iff_sourceStep
    (source target : Term sig [] Srt.pr) :
    (∃ event : sourceEvents.edge.obj closedContext,
      sourceEvents.source.app closedContext event =
        (Quotient.mk _ source : TermQ rhoSourceE [] Srt.pr) ∧
      sourceEvents.target.app closedContext event =
        (Quotient.mk _ target : TermQ rhoSourceE [] Srt.pr)) ↔
      rhoSourceWithDrop.StepModE source target := by
  exact (authored_class_endpoints_iff_stepModE
    rhoSourceWithDrop.toUnpositioned Srt.pr source target).trans
      (rhoSourceWithDrop.stepModE_iff_toUnpositioned).symm

/-- The free extension really adds an authored Drop event at the closed
context, from the class of `*(@0)` to the class of `0`. -/
theorem free_extension_contains_drop :
    ∃ event :
      (freeObject sourceEvents (emptyGraph states)).graph.edge.obj closedContext,
      (freeObject sourceEvents (emptyGraph states)).graph.source.app
          closedContext event =
        (Quotient.mk _ dropChan : TermQ rhoSourceE [] Srt.pr) ∧
      (freeObject sourceEvents (emptyGraph states)).graph.target.app
          closedContext event =
        (Quotient.mk _ nilP : TermQ rhoSourceE [] Srt.pr) := by
  obtain ⟨event, before, after⟩ :=
    Mettapedia.OSLF.Binding.RhoSourceEventComparison.source_drop_has_class_event
  exact ⟨Sum.inr event, before, after⟩

/-- There were no old events at that context. The Drop edge above is in the
genuinely adjoined summand. -/
theorem no_old_closed_event :
    ¬ Nonempty ((emptyGraph states).edge.obj closedContext) := by
  rintro ⟨event⟩
  exact event.elim

/-! ## Comparison with the proposition-valued reduction subobject -/

/-- The endpoint-image subobject already constructed for contextual events,
specialized to the complete source equations and both operational rules. -/
abbrev sourceReduction :=
  stepSubfunctor rhoSourceWithDrop.toUnpositioned Srt.pr

/-- The freely adjoined event graph and the existing contextual reduction
subobject have exactly the same endpoint pairs at every context. The event
graph retains which firing gave a pair; the subobject forgets that identity. -/
theorem free_endpoint_image_iff_reduction
    (X : base) (pair : states.obj X × states.obj X) :
    (∃ event :
        (freeObject sourceEvents (emptyGraph states)).graph.edge.obj X,
      (freeObject sourceEvents (emptyGraph states)).graph.source.app X event =
        pair.1 ∧
      (freeObject sourceEvents (emptyGraph states)).graph.target.app X event =
        pair.2) ↔ sourceReduction.obj X pair := by
  constructor
  · rintro ⟨event, before, after⟩
    cases event with
    | inl old => exact old.elim
    | inr authored => exact ⟨authored, before, after⟩
  · rintro ⟨authored, before, after⟩
    exact ⟨Sum.inr authored, before, after⟩

/-- The endpoint-image map from the freely generated event presheaf is
natural, so erasing event identity commutes with substitution. -/
def freeIncidence :
    (freeObject sourceEvents (emptyGraph states)).graph.edge ⟶
      sourceReduction.toFunctor where
  app X := TypeCat.ofHom (fun
    | .inl old => old.elim
    | .inr authored =>
        (incidence rhoSourceWithDrop.toUnpositioned Srt.pr).app X authored)
  naturality X Y f := by
    apply ConcreteCategory.hom_ext
    intro event
    cases event with
    | inl old => exact old.elim
    | inr authored =>
        exact congrArg
          (fun morphism :
            (presentationEventPresheaf rhoSourceWithDrop.toUnpositioned Srt.pr).obj X ⟶
              sourceReduction.toFunctor.obj Y => morphism authored)
          ((incidence rhoSourceWithDrop.toUnpositioned Srt.pr).naturality f)

/-- Every reduction-subobject point is the image of an authored event in the
free extension. The map can still identify distinct firing occurrences. -/
theorem freeIncidence_surjective (X : base) :
    Function.Surjective (freeIncidence.app X) := by
  intro pair
  obtain ⟨event, equal⟩ :=
    incidence_surjective rhoSourceWithDrop.toUnpositioned Srt.pr X pair
  exact ⟨Sum.inr event, equal⟩

/-! ## The actual product subobject in the presheaf model -/

/-- The previously constructed pair presheaf is the explicit categorical
product of the rho state presheaf with itself. -/
theorem pairPresheaf_eq_explicitProduct :
    pairPresheaf rhoSourceWithDrop.toUnpositioned Srt.pr =
      FunctorToTypes.prod states states := by
  rfl

/-- The categorical binary product represents the pointwise endpoint pairs
used by the event graph and the reduction image. -/
noncomputable def stateProductIso :
    states ⨯ states ≅
      pairPresheaf rhoSourceWithDrop.toUnpositioned Srt.pr :=
  FunctorToTypes.binaryProductIso states states

/-- The reduction relation is a categorical subobject of the actual binary
product of state presheaves. -/
noncomputable def sourceReductionSubobject : Subobject (states ⨯ states) :=
  Subobject.mk (sourceReduction.ι ≫ stateProductIso.inv)

/-- Factoring through the actual reduction subobject is exactly the authored
one-step relation at every stage and element of an arbitrary test presheaf.
This is the representability condition missing from mere substitution-stable
families of contextual rewrite propositions. -/
theorem sourceReductionSubobject_factors_iff
    {test : base ⥤ Type} (map : test ⟶ states ⨯ states) :
    sourceReductionSubobject.Factors map ↔
      ∀ (X : base) (point : test.obj X),
        (map ≫ stateProductIso.hom).app X point ∈ sourceReduction.obj X := by
  have pointwise := subfunctor_factors_iff_pointwise
    sourceReduction (map ≫ stateProductIso.hom)
  constructor
  · intro factors
    obtain ⟨lift, equal⟩ :=
      (Subobject.mk_factors_iff _ _).mp factors
    change lift ≫ (sourceReduction.ι ≫ stateProductIso.inv) = map at equal
    apply pointwise.mp
    apply (Subobject.mk_factors_iff _ _).mpr
    refine ⟨lift, ?_⟩
    change lift ≫ sourceReduction.ι = map ≫ stateProductIso.hom
    have afterIso := congrArg (fun arrow => arrow ≫ stateProductIso.hom) equal
    calc
      lift ≫ sourceReduction.ι =
          (lift ≫ sourceReduction.ι) ≫
            (stateProductIso.inv ≫ stateProductIso.hom) := by simp
      _ = (lift ≫ (sourceReduction.ι ≫ stateProductIso.inv)) ≫
            stateProductIso.hom :=
              congrArg (fun arrow => arrow ≫ stateProductIso.hom)
                (Category.assoc lift sourceReduction.ι stateProductIso.inv)
      _ = map ≫ stateProductIso.hom := afterIso
  · intro held
    obtain ⟨lift, equal⟩ :=
      (Subobject.mk_factors_iff _ _).mp (pointwise.mpr held)
    change lift ≫ sourceReduction.ι = map ≫ stateProductIso.hom at equal
    apply (Subobject.mk_factors_iff _ _).mpr
    refine ⟨lift, ?_⟩
    change lift ≫ (sourceReduction.ι ≫ stateProductIso.inv) = map
    have afterIso := congrArg (fun arrow => arrow ≫ stateProductIso.inv) equal
    calc
      lift ≫ (sourceReduction.ι ≫ stateProductIso.inv) =
          (lift ≫ sourceReduction.ι) ≫ stateProductIso.inv := by
            exact (Category.assoc _ _ _).symm
      _ = (map ≫ stateProductIso.hom) ≫ stateProductIso.inv := afterIso
      _ = map := by simp [Category.assoc]

/-- The authored contextual relation on arbitrary test presheaves: every
instantiated endpoint pair is witnessed by some retained rule occurrence. -/
def AuthoredContextualReduction {test : base ⥤ Type}
    (source target : test ⟶ states) : Prop :=
  ∀ (X : base) (point : test.obj X),
    (source.app X point, target.app X point) ∈ sourceReduction.obj X

private theorem productEndpointPair {test : base ⥤ Type}
    (source target : test ⟶ states) :
    prod.lift source target ≫ stateProductIso.hom =
      FunctorToTypes.prod.lift source target := by
  change prod.lift source target ≫
    (FunctorToTypes.binaryProductIso states states).hom =
      FunctorToTypes.prod.lift source target
  ext X point
  · have projection :
        (prod.lift source target ≫
          (FunctorToTypes.binaryProductIso states states).hom ≫
          (FunctorToTypes.prod.fst (F := states) (G := states))).app X point =
            source.app X point := by
      rw [FunctorToTypes.binaryProductIso_hom_comp_fst, prod.lift_fst]
    exact projection
  · have projection :
        (prod.lift source target ≫
          (FunctorToTypes.binaryProductIso states states).hom ≫
          (FunctorToTypes.prod.snd (F := states) (G := states))).app X point =
            target.app X point := by
      rw [FunctorToTypes.binaryProductIso_hom_comp_snd, prod.lift_snd]
    exact projection

/-- The authored contextual rho relation is represented by the categorical
reduction subobject: the factorization test and the retained-event predicate
agree for every test presheaf, not just closed terms. -/
theorem authoredReduction_iff_factors {test : base ⥤ Type}
    (source target : test ⟶ states) :
    AuthoredContextualReduction source target ↔
      RepresentedRewrite states sourceReductionSubobject source target := by
  rw [RepresentedRewrite, sourceReductionSubobject_factors_iff,
    productEndpointPair]
  rfl

/-- The authored relation is stable under every natural transformation of
test presheaves, because its actual representing subobject supplies the
factorization law. -/
theorem authoredReduction_precomp {test later : base ⥤ Type}
    (substitution : later ⟶ test)
    (source target : test ⟶ states)
    (fires : AuthoredContextualReduction source target) :
    AuthoredContextualReduction
      (substitution ≫ source) (substitution ≫ target) := by
  apply (authoredReduction_iff_factors _ _).mpr
  exact representedRewrite_precomp states sourceReductionSubobject
    substitution source target
    ((authoredReduction_iff_factors source target).mp fires)

/-- Erasing event identity gives the natural endpoint-pair map. -/
def freeEndpointPair :
    (freeObject sourceEvents (emptyGraph states)).graph.edge ⟶
      pairPresheaf rhoSourceWithDrop.toUnpositioned Srt.pr :=
  freeIncidence ≫ sourceReduction.ι

/-- The range of the free event endpoint map is exactly the authored
reduction subfunctor, at every context. -/
theorem freeEndpointPair_range :
    Subfunctor.range freeEndpointPair = sourceReduction := by
  ext X pair
  constructor
  · rintro ⟨event, equal⟩
    rw [← equal]
    exact (freeIncidence.app X event).property
  · intro membership
    obtain ⟨event, equal⟩ := freeIncidence_surjective X ⟨pair, membership⟩
    exact ⟨event, congrArg Subtype.val equal⟩

/-- Under the order isomorphism between type-valued subfunctors and
categorical subobjects, the image of the free event endpoint map is exactly
the authored reduction subobject. -/
theorem freeEndpointPair_subobjectImage :
    Subfunctor.orderIsoSubobject
      (pairPresheaf rhoSourceWithDrop.toUnpositioned Srt.pr)
      (Subfunctor.range freeEndpointPair) =
        Subobject.mk sourceReduction.ι := by
  rw [freeEndpointPair_range]
  rfl

end Mettapedia.OSLF.Binding.RhoFreePresheafEvents
