import Mettapedia.OSLF.Syntax.FiniteLimitGeneratedWithObjects
import Mettapedia.OSLF.Syntax.RhoEventQuotientDescentBoundary
import Mettapedia.OSLF.Syntax.RhoFreePresheafEvents
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Images

/-!
# A finite-limit setting for the authored rho operational graph

The raw context base retains located firing occurrences. Over it, state
objects already carry the complete authored equation quotient. Closing these
objects, their paired endpoints, the event object, and its reduction image
under finite limits places the actual graph and its image factorization in
one finitely complete category. This is a concrete ambient construction; a
free classifying property and cartesian closure require further work.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.RhoOperationalFiniteLimitCategory

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open Mettapedia.OSLF.FiniteLimitYoneda
open Mettapedia.OSLF.Binding.RhoSchema
open Mettapedia.OSLF.Binding.RhoFreePresheafEvents
open Mettapedia.OSLF.Binding.ContextualReductionSubobject

abbrev RawContexts := Syntactic.Ctxt sig
abbrev Presheaf := (RawContexts)ᵒᵖ ⥤ Type

/-- The four nonrepresentable objects needed by the actual operational
presentation: quotient-valued states, located events, their endpoint image,
and the paired endpoint object. -/
def operationalObjects : Set Presheaf :=
  {states, sourceEvents.edge, sourceReduction.toFunctor,
    pairPresheaf rhoSourceWithDrop.toUnpositioned Srt.pr}

abbrev OperationalCategory :=
  (GeneratedWithObjects RawContexts operationalObjects).FullSubcategory

theorem operationalCategory_hasFiniteLimits : HasFiniteLimits OperationalCategory :=
  inferInstance

/-- Raw substitution contexts enter the operational category by Yoneda.
They retain their pre-existing finite products and all substitution arrows. -/
def contextEmbedding : RawContexts ⥤ OperationalCategory :=
  intoGeneratedWithObjects RawContexts operationalObjects

theorem contextEmbedding_preservesFiniteProducts :
    PreservesFiniteProducts contextEmbedding :=
  intoGeneratedWithObjects_preservesFiniteProducts
    RawContexts operationalObjects

instance contextEmbedding_full : contextEmbedding.Full :=
  intoGeneratedWithObjects_full RawContexts operationalObjects

instance contextEmbedding_faithful : contextEmbedding.Faithful :=
  intoGeneratedWithObjects_faithful RawContexts operationalObjects

def stateObject : OperationalCategory :=
  ⟨states, extraInGenerated RawContexts operationalObjects (by
    simp [operationalObjects])⟩

def eventObject : OperationalCategory :=
  ⟨sourceEvents.edge, extraInGenerated RawContexts operationalObjects (by
    simp [operationalObjects])⟩

def relationObject : OperationalCategory :=
  ⟨sourceReduction.toFunctor,
    extraInGenerated RawContexts operationalObjects (by
      simp [operationalObjects])⟩

def pairObject : OperationalCategory :=
  ⟨pairPresheaf rhoSourceWithDrop.toUnpositioned Srt.pr,
    extraInGenerated RawContexts operationalObjects (by
      simp [operationalObjects])⟩

/-- The two incidence maps retain their quotient-valued endpoints. -/
def source : eventObject ⟶ stateObject :=
  ObjectProperty.homMk sourceEvents.source

def target : eventObject ⟶ stateObject :=
  ObjectProperty.homMk sourceEvents.target

/-- The occurrence-to-relation map forgets the firing's rule and location. -/
def incidence : eventObject ⟶ relationObject :=
  ObjectProperty.homMk
    (ContextualReductionSubobject.incidence
      rhoSourceWithDrop.toUnpositioned Srt.pr)

/-- The reduction predicate is a subobject of paired states. -/
def relationInclusion : relationObject ⟶ pairObject :=
  ObjectProperty.homMk sourceReduction.ι

/-- Paired endpoints of a retained event, before erasing its occurrence. -/
def endpoints : eventObject ⟶ pairObject :=
  ObjectProperty.homMk
    (endpointsNatural rhoSourceWithDrop.toUnpositioned Srt.pr)

/-- The paired map really is the pair of the two graph endpoints. -/
theorem endpoints_coordinates
    (X : (RawContexts)ᵒᵖ) (event : eventObject.1.obj X) :
    endpoints.hom.app X event =
      (source.hom.app X event, target.hom.app X event) := rfl

/-- The actual authored endpoint map factors through the selected reduction
object inside the finitely complete category. -/
theorem endpoints_factorization :
    incidence ≫ relationInclusion = endpoints := by
  apply ObjectProperty.hom_ext
  change (ContextualReductionSubobject.incidence
      rhoSourceWithDrop.toUnpositioned Srt.pr) ≫ sourceReduction.ι =
    endpointsNatural rhoSourceWithDrop.toUnpositioned Srt.pr
  exact ContextualReductionSubobject.endpoints_factorization _ _

/-- Every point of the reduction object is an endpoint image of a retained
firing, so the occurrence-erasing factor is epic in this full subcategory. -/
theorem incidence_epi : Epi incidence := by
  have rawEpi : Epi
      (ContextualReductionSubobject.incidence
        rhoSourceWithDrop.toUnpositioned Srt.pr) := by
    apply (NatTrans.epi_iff_epi_app _).2
    intro X
    exact (epi_iff_surjective _).2
      (ContextualReductionSubobject.incidence_surjective
        rhoSourceWithDrop.toUnpositioned Srt.pr X)
  constructor
  intro Z f g equal
  apply ObjectProperty.hom_ext
  have rawEqual := congrArg
    (fun arrow : eventObject ⟶ Z => arrow.hom) equal
  change (ContextualReductionSubobject.incidence
      rhoSourceWithDrop.toUnpositioned Srt.pr) ≫ f.hom =
    (ContextualReductionSubobject.incidence
      rhoSourceWithDrop.toUnpositioned Srt.pr) ≫ g.hom at rawEqual
  exact rawEpi.left_cancellation f.hom g.hom rawEqual

/-- The relation inclusion remains monic because it is the same pointwise
injective subfunctor inclusion in the ambient presheaf category. -/
theorem relationInclusion_mono : Mono relationInclusion := by
  have rawMono : Mono sourceReduction.ι := inferInstance
  constructor
  intro Z f g equal
  apply ObjectProperty.hom_ext
  have rawEqual := congrArg
    (fun arrow : Z ⟶ pairObject => arrow.hom) equal
  change f.hom ≫ sourceReduction.ι = g.hom ≫ sourceReduction.ι at rawEqual
  exact rawMono.right_cancellation f.hom g.hom rawEqual

/-- In ambient presheaves the selected relation is exactly the range of the
authored endpoint map, not an arbitrary additional predicate. -/
theorem endpoints_range :
    Subfunctor.range
      (endpointsNatural rhoSourceWithDrop.toUnpositioned Srt.pr) =
        sourceReduction := by
  ext X pair
  constructor
  · rintro ⟨event, equal⟩
    rw [← equal]
    exact (ContextualReductionSubobject.incidence
      rhoSourceWithDrop.toUnpositioned Srt.pr).app X event |>.property
  · intro membership
    obtain ⟨event, equal⟩ :=
      ContextualReductionSubobject.incidence_surjective
        rhoSourceWithDrop.toUnpositioned Srt.pr X ⟨pair, membership⟩
    refine ⟨event, ?_⟩
    exact congrArg Subtype.val equal

/-- The endpoint map's concrete mono factorisation in the operational
category. The following image question asks for its universal property. -/
def endpointMonoFactorisation : MonoFactorisation endpoints where
  I := relationObject
  m := relationInclusion
  m_mono := relationInclusion_mono
  e := incidence
  fac := endpoints_factorization

private def ambientAlternative
    (alternative : MonoFactorisation endpoints) :
    MonoFactorisation
      (endpointsNatural rhoSourceWithDrop.toUnpositioned Srt.pr) where
  I := alternative.I.1
  m := alternative.m.hom
  m_mono := inclusion_preserves_mono RawContexts operationalObjects
    alternative.m
  e := alternative.e.hom
  fac := by
    have equality := congrArg
      (fun arrow : eventObject ⟶ pairObject => arrow.hom) alternative.fac
    change alternative.e.hom ≫ alternative.m.hom =
      endpointsNatural rhoSourceWithDrop.toUnpositioned Srt.pr at equality
    exact equality

private theorem subfunctor_eqToHom_comp_inclusion
    {F : Presheaf} {P Q : Subfunctor F} (h : P = Q) :
    eqToHom (congrArg Subfunctor.toFunctor h) ≫ Q.ι = P.ι := by
  cases h
  simp

private theorem range_cast_inclusion :
    eqToHom (congrArg Subfunctor.toFunctor endpoints_range.symm) ≫
      (Subfunctor.range
        (endpointsNatural rhoSourceWithDrop.toUnpositioned Srt.pr)).ι =
      sourceReduction.ι :=
  subfunctor_eqToHom_comp_inclusion endpoints_range.symm

/-- Every mono factorisation of the rho endpoint map receives the canonical
map from its reduction object. This is the categorical image universal
property, now tested against all monomorphisms of the generated category. -/
noncomputable def endpointImageLift
    (alternative : MonoFactorisation endpoints) :
    relationObject ⟶ alternative.I :=
  ObjectProperty.homMk
    (eqToHom (congrArg Subfunctor.toFunctor endpoints_range.symm) ≫
      (FunctorToTypes.monoFactorisationIsImage
        (endpointsNatural rhoSourceWithDrop.toUnpositioned Srt.pr)).lift
          (ambientAlternative alternative))

theorem endpointImageLift_fac
    (alternative : MonoFactorisation endpoints) :
    endpointImageLift alternative ≫ alternative.m =
      relationInclusion := by
  apply ObjectProperty.hom_ext
  let cast : sourceReduction.toFunctor ⟶
      (Subfunctor.range
        (endpointsNatural rhoSourceWithDrop.toUnpositioned Srt.pr)).toFunctor :=
    eqToHom (congrArg Subfunctor.toFunctor endpoints_range.symm)
  let lift :
      (Subfunctor.range
        (endpointsNatural rhoSourceWithDrop.toUnpositioned Srt.pr)).toFunctor ⟶
        alternative.I.1 :=
    (FunctorToTypes.monoFactorisationIsImage
      (endpointsNatural rhoSourceWithDrop.toUnpositioned Srt.pr)).lift
        (ambientAlternative alternative)
  have lift_fac : lift ≫ alternative.m.hom =
      (Subfunctor.range
        (endpointsNatural rhoSourceWithDrop.toUnpositioned Srt.pr)).ι := by
    exact (FunctorToTypes.monoFactorisationIsImage
      (endpointsNatural rhoSourceWithDrop.toUnpositioned Srt.pr)).lift_fac
        (ambientAlternative alternative)
  change (cast ≫ lift) ≫ alternative.m.hom = sourceReduction.ι
  rw [Category.assoc, lift_fac]
  exact range_cast_inclusion

/-- The selected epi–mono factorisation is the actual categorical image of
authored rho endpoints in the operational finite-limit category. -/
noncomputable def endpointIsImage : IsImage endpointMonoFactorisation where
  lift := endpointImageLift
  lift_fac := endpointImageLift_fac

/-- The operational object contains the actual authored Drop firing, with
its source and target in the full source equation quotient. -/
theorem authored_drop_event :
    ∃ event : eventObject.1.obj closedContext,
      source.hom.app closedContext event =
        (Quotient.mk _ dropChan : TermQ rhoSourceE [] Srt.pr) ∧
      target.hom.app closedContext event =
        (Quotient.mk _ nilP : TermQ rhoSourceE [] Srt.pr) := by
  exact Mettapedia.OSLF.Binding.RhoSourceEventComparison.source_drop_has_class_event

end Mettapedia.OSLF.Binding.RhoOperationalFiniteLimitCategory
