import Mettapedia.OSLF.Syntax.PresheafEventGraphTransport
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Images
import Mathlib.CategoryTheory.Subobject.Limits

/-!
# Event graphs as a slice over paired programs

The event graph of a presheaf-valued program object is equivalent to the
ordinary slice category over its paired endpoint object. This comparison
identifies the retained event object and its incidence map, not merely the
predicate that some event exists. The slice presentation is the general
categorical interface: in another target it requires products, while images
and coproducts are separate additional structure.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.EventGraphSlice

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open Mettapedia.OSLF.Binding.FreePresheafEventExtension
open Mettapedia.OSLF.Binding.FreePresheafEventImage
open Mettapedia.OSLF.Binding.PresheafEventGraphTransport

universe u v w

variable {C : Type u} [Category.{v} C]
variable (V : C ⥤ Type w)

private abbrev Pair := FunctorToTypes.prod V V

/-- In a type-valued functor category, the categorical image of a map is
the subfunctor of its pointwise range. This compares the generic image API
with the concrete endpoint predicates used by operational semantics. -/
theorem imageSubobject_eq_range {F G : C ⥤ Type w} (f : F ⟶ G) :
    imageSubobject f = Subobject.mk (Subfunctor.range f).ι := by
  exact Subobject.mk_eq_mk_of_comm _ _
    (IsImage.isoExt (Image.isImage f)
      (FunctorToTypes.monoFactorisationIsImage f))
    (IsImage.isoExt_hom_m (Image.isImage f)
      (FunctorToTypes.monoFactorisationIsImage f))

/-- Changing the chosen endpoint-pair representation by an isomorphism
transports the image subobject along that same isomorphism. -/
theorem imageSubobject_postIso {F G H : C ⥤ Type w}
    (f : F ⟶ G) (e : G ≅ H) :
    imageSubobject (f ≫ e.hom) =
      (Subobject.map e.hom).obj (imageSubobject f) := by
  change Subobject.mk (image.ι (f ≫ e.hom)) =
    Subobject.mk (image.ι f ≫ e.hom)
  exact (Subobject.mk_eq_mk_of_comm _ _ (image.compIso f e.hom)
    (image.compIso_hom_comp_image_ι f e.hom)).symm

/-- The two injections of a disjoint event sum, as a binary cofan in the
category of endpoint-preserving graphs. -/
def graphSumCofan (G K : Graph V) : BinaryCofan G K :=
  BinaryCofan.mk (graphInl G K) (graphInr G K)

/-- The disjoint sum is the categorical coproduct of event graphs. This is
the universal property underlying free adjoining, not merely a pointwise
description of its edge presheaf. -/
def graphSumIsColimit (G K : Graph V) :
    IsColimit (graphSumCofan V G K) :=
  BinaryCofan.isColimitMk
    (fun s => graphCopair s.inl s.inr)
    (fun s => graphInl_copair s.inl s.inr)
    (fun s => graphInr_copair s.inl s.inr)
    (fun s m leftEq rightEq =>
      graphCopair_unique s.inl s.inr m leftEq rightEq)

/-- An event graph is a map from firing occurrences to their endpoint pair. -/
def toSlice (G : Graph V) : Over (Pair V) :=
  Over.mk (endpointMap G)

/-- An endpoint-preserving graph map is a map in the endpoint slice. -/
def toSliceHom {G K : Graph V} (f : Hom G K) :
    toSlice V G ⟶ toSlice V K :=
  Over.homMk f.edgeMap (by
    ext X event
    · exact congrArg
        (fun t : G.edge ⟶ V => t.app X event) f.source_comm
    · exact congrArg
        (fun t : G.edge ⟶ V => t.app X event) f.target_comm)

/-- Read a slice object as its event object and two endpoint projections. -/
def fromSlice (O : Over (Pair V)) : Graph V where
  edge := O.left
  source := O.hom ≫ FunctorToTypes.prod.fst
  target := O.hom ≫ FunctorToTypes.prod.snd

/-- A slice map preserves both projected endpoints. -/
def fromSliceHom {O P : Over (Pair V)} (f : O ⟶ P) :
    Hom (fromSlice V O) (fromSlice V P) where
  edgeMap := f.left
  source_comm := by
    simpa only [fromSlice, Category.assoc] using
      congrArg (fun t : O.left ⟶ Pair V =>
        t ≫ FunctorToTypes.prod.fst) (Over.w f)
  target_comm := by
    simpa only [fromSlice, Category.assoc] using
      congrArg (fun t : O.left ⟶ Pair V =>
        t ≫ FunctorToTypes.prod.snd) (Over.w f)

/-- Passage from event graphs to the endpoint slice acts on all graph maps. -/
def toSliceFunctor : Graph V ⥤ Over (Pair V) where
  obj := toSlice V
  map := toSliceHom V
  map_id := by
    intro G
    apply Over.OverMorphism.ext
    rfl
  map_comp := by
    intro G K T f g
    apply Over.OverMorphism.ext
    rfl

/-- Passage from the endpoint slice to event graphs acts on all slice maps. -/
def fromSliceFunctor : Over (Pair V) ⥤ Graph V where
  obj := fromSlice V
  map := fromSliceHom V
  map_id := by
    intro O
    apply Hom.ext
    rfl
  map_comp := by
    intro O P Q f g
    apply Hom.ext
    rfl

/-- Splitting a paired endpoint map and pairing it again recovers the
original event graph without changing any firing occurrence. -/
def graphRoundtrip (G : Graph V) : fromSlice V (toSlice V G) ≅ G where
  hom :=
    { edgeMap := 𝟙 G.edge
      source_comm := by simp [fromSlice, toSlice, endpointMap]
      target_comm := by simp [fromSlice, toSlice, endpointMap] }
  inv :=
    { edgeMap := 𝟙 G.edge
      source_comm := by simp [fromSlice, toSlice, endpointMap]
      target_comm := by simp [fromSlice, toSlice, endpointMap] }
  hom_inv_id := by apply Hom.ext; rfl
  inv_hom_id := by apply Hom.ext; rfl

/-- Splitting an arrow into its two endpoint projections and pairing them
again recovers that same arrow of the slice. -/
def sliceRoundtrip (O : Over (Pair V)) :
    toSlice V (fromSlice V O) ≅ O :=
  Over.isoMk (Iso.refl O.left) (by
    ext X event
    · rfl
    · simp [toSlice, fromSlice, endpointMap]
      rfl)

/-- Event graphs and endpoint-slice objects form equivalent categories.
The equivalence is on objects and maps, with coherent inverse comparisons. -/
def graphSliceEquivalence : Graph V ≌ Over (Pair V) where
  functor := toSliceFunctor V
  inverse := fromSliceFunctor V
  unitIso := NatIso.ofComponents (fun G => (graphRoundtrip V G).symm)
    (by intro G K f; apply Hom.ext; rfl)
  counitIso := NatIso.ofComponents (sliceRoundtrip V)
    (by intro O P f; apply Over.OverMorphism.ext; rfl)
  functor_unitIso_comp := by
    intro G
    apply Over.OverMorphism.ext
    rfl

/-- The same equivalence using the category's chosen binary product, rather
than the explicit pointwise pair presheaf. -/
noncomputable def graphProductSliceEquivalence :
    Graph V ≌ Over (V ⨯ V) :=
  (graphSliceEquivalence V).trans
    (Over.mapIso (FunctorToTypes.binaryProductIso V V).symm)

/-- Transporting graph vertices along an isomorphism agrees with
postcomposing their endpoint slice arrows. -/
def toSlice_changeVertex_iso {W : C ⥤ Type w}
    (i : V ≅ W) (G : Graph V) :
    toSlice W (changeVertex i G) ≅
      (Over.map (pairMap i.hom)).obj (toSlice V G) :=
  Over.isoMk (Iso.refl G.edge) (by
    change endpointMap G ≫ pairMap i.hom =
      endpointMap (changeVertex i G)
    exact (endpointMap_changeVertex i G).symm)

/-- The graph–slice comparison is natural in isomorphisms of the program
object, including every map between retained event graphs. -/
def toSlice_changeVertex_natural {W : C ⥤ Type w} (i : V ≅ W) :
    changeVertexFunctor i ⋙ toSliceFunctor W ≅
      toSliceFunctor V ⋙ Over.map (pairMap i.hom) :=
  NatIso.ofComponents (toSlice_changeVertex_iso V i)
    (by intro G K f; apply Over.OverMorphism.ext; rfl)

/-- Under the graph–slice equivalence, free adjoining is a categorical
binary coproduct in the slice over paired endpoints. -/
noncomputable def sliceGraphSumIsColimit (G K : Graph V) :
    IsColimit ((toSliceFunctor V).mapCocone (graphSumCofan V G K)) := by
  letI : (toSliceFunctor V).IsEquivalence :=
    (graphSliceEquivalence V).isEquivalence_functor
  exact isColimitOfPreserves (toSliceFunctor V) (graphSumIsColimit V G K)

end Mettapedia.OSLF.Binding.EventGraphSlice

namespace Mettapedia.OSLF.Binding.EventGraphSlice.Categorical

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits

universe u v

variable {D : Type u} [Category.{v} D]
variable (programs : D) [HasBinaryProduct programs programs]

/-- In any category with the paired program object, an internal event graph
is an arrow from its event object to paired programs. -/
abbrev EventGraph := Over (programs ⨯ programs)

/-- A reduction predicate is the image of the event endpoint arrow when
this particular image exists. This definition assumes no global regularity,
stable images, or truth classifier. -/
noncomputable def reductionImage (G : EventGraph programs) [HasImage G.hom] :
    Subobject (programs ⨯ programs) :=
  imageSubobject G.hom

/-- Every firing factors through the endpoint predicate obtained from its
image. The factorization retains an event object before this erasure. -/
theorem firingFactorsReduction (G : EventGraph programs) [HasImage G.hom] :
    (reductionImage programs G).Factors G.hom := by
  simpa [reductionImage] using
    (imageSubobject_factors_comp_self G.hom (𝟙 G.left))

/-- Only when the endpoint map is monic can its event object itself be read
as the subobject representing reduction. -/
theorem reductionImage_of_monic (G : EventGraph programs)
    [HasImage G.hom] [Mono G.hom] :
    reductionImage programs G = Subobject.mk G.hom :=
  imageSubobject_mono G.hom

end Mettapedia.OSLF.Binding.EventGraphSlice.Categorical

namespace Mettapedia.OSLF.Binding.EventGraphSlice.RhoExample

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open Mettapedia.OSLF.Binding.FreePresheafEventImage
open Mettapedia.OSLF.Binding.RhoFreePresheafEvents

/-- The actual source COMM/Drop firings as a slice object over paired rho
process states. -/
def sourceEventSlice : Over (FunctorToTypes.prod states states) :=
  toSlice states sourceEvents

/-- Its categorical endpoint image is exactly the existing authored
one-step reduction predicate. -/
theorem sourceEventSlice_image :
    Subfunctor.range sourceEventSlice.hom = sourceReduction :=
  FreePresheafEventImage.RhoExample.source_image_eq_reduction

/-- The same authored graph in the general slice over the category's chosen
product object. -/
noncomputable def sourceProductEventSlice :
    Categorical.EventGraph states :=
  (graphProductSliceEquivalence states).functor.obj sourceEvents

/-- Its endpoint arrow is precisely the original paired source/target map,
followed by the proven comparison with the chosen binary product. -/
theorem sourceProductEventSlice_endpointMap :
    sourceProductEventSlice.hom =
      endpointMap sourceEvents ≫ stateProductIso.inv := rfl

/-- The categorical image interface applies to the actual authored rho
events in the chosen binary-product representation. -/
theorem sourceProductFiringFactors :
    (Categorical.reductionImage states sourceProductEventSlice).Factors
      sourceProductEventSlice.hom :=
  Categorical.firingFactorsReduction states sourceProductEventSlice

/-- The generic categorical image of the authored event arrow in the
chosen product is exactly the rho reduction subobject already consumed by
the operational semantics. -/
theorem sourceProductImage_eq_reduction :
    Categorical.reductionImage states sourceProductEventSlice =
      sourceReductionSubobject := by
  unfold Categorical.reductionImage sourceReductionSubobject
  rw [sourceProductEventSlice_endpointMap]
  change imageSubobject (endpointMap sourceEvents ≫ stateProductIso.symm.hom) =
    Subobject.mk (sourceReduction.ι ≫ stateProductIso.symm.hom)
  rw [imageSubobject_postIso (endpointMap sourceEvents) stateProductIso.symm]
  rw [imageSubobject_eq_range]
  have rangeEq : Subfunctor.range (endpointMap sourceEvents) = sourceReduction :=
    FreePresheafEventImage.RhoExample.source_image_eq_reduction
  rw [rangeEq]
  rfl

/-- An authored duplicate COMM occurrence makes the event-to-endpoint map
non-monic. Thus the event slice object is not itself a reduction subobject:
the subobject arises only after taking an image. -/
theorem duplicatedEventSlice_not_mono :
    ¬ Mono (toSlice _ FreePresheafEventImage.RhoExample.duplicatedGraph).hom := by
  intro mono
  have atClosed := (NatTrans.mono_iff_mono_app _).mp mono closedContext
  exact FreePresheafEventImage.RhoExample.duplicated_endpoint_map_not_injective
    ((mono_iff_injective _).mp atClosed)

end Mettapedia.OSLF.Binding.EventGraphSlice.RhoExample
