import Mettapedia.OSLF.Syntax.EventGraphSlice

/-!
# Transport of event images across program isomorphisms

For any presheaf of programs and retained firing graph, changing the program
representation transports its event-to-endpoint arrow and its categorical
image through the induced isomorphism of chosen binary products. No firing
event is identified by this operation.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.EventGraphImageTransport.Categorical

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits

universe uD vD

/-- In a category with equalizers and the displayed image, postcomposing an
event arrow with an isomorphism transports its image subobject. This does not
infer image existence from finite limits. -/
theorem imageSubobject_postIso {D : Type uD} [Category.{vD} D]
    [HasEqualizers D]
    {E X Y : D} (f : E ⟶ X) (i : X ≅ Y)
    [HasImage f] [HasImage (f ≫ i.hom)] :
    imageSubobject (f ≫ i.hom) =
      (Subobject.map i.hom).obj (imageSubobject f) := by
  change Subobject.mk (image.ι (f ≫ i.hom)) =
    Subobject.mk (image.ι f ≫ i.hom)
  exact (Subobject.mk_eq_mk_of_comm _ _ (image.compIso f i.hom)
    (image.compIso_hom_comp_image_ι f i.hom)).symm

end Mettapedia.OSLF.Binding.EventGraphImageTransport.Categorical

namespace Mettapedia.OSLF.Binding.EventGraphImageTransport

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open Mettapedia.OSLF.Binding.FreePresheafEventExtension
open Mettapedia.OSLF.Binding.FreePresheafEventImage
open Mettapedia.OSLF.Binding.PresheafEventGraphTransport
open Mettapedia.OSLF.Binding.EventGraphSlice

universe u v w

variable {C : Type u} [Category.{v} C]

/-- A pointwise pair map agrees with the map between chosen binary products. -/
theorem pairMap_toChosen_natural {V W : C ⥤ Type w}
    (map : V ⟶ W) :
    pairMap map ≫ (FunctorToTypes.binaryProductIso W W).inv =
      (FunctorToTypes.binaryProductIso V V).inv ≫ prod.map map map := by
  apply prod.hom_ext
  · calc
      (pairMap map ≫ (FunctorToTypes.binaryProductIso W W).inv) ≫
          prod.fst =
        pairMap map ≫ FunctorToTypes.prod.fst := by
          rw [Category.assoc,
            FunctorToTypes.binaryProductIso_inv_comp_fst]
      _ = FunctorToTypes.prod.fst ≫ map := by
        simp [pairMap]
      _ = ((FunctorToTypes.binaryProductIso V V).inv ≫
          prod.map map map) ≫ prod.fst := by
        rw [Category.assoc, prod.map_fst]
        rw [← Category.assoc,
          FunctorToTypes.binaryProductIso_inv_comp_fst]
  · calc
      (pairMap map ≫ (FunctorToTypes.binaryProductIso W W).inv) ≫
          prod.snd =
        pairMap map ≫ FunctorToTypes.prod.snd := by
          rw [Category.assoc,
            FunctorToTypes.binaryProductIso_inv_comp_snd]
      _ = FunctorToTypes.prod.snd ≫ map := by
        simp [pairMap]
      _ = ((FunctorToTypes.binaryProductIso V V).inv ≫
          prod.map map map) ≫ prod.snd := by
        rw [Category.assoc, prod.map_snd]
        rw [← Category.assoc,
          FunctorToTypes.binaryProductIso_inv_comp_snd]

/-- The actual graph-to-product-slice endpoint arrow commutes with a change
of program representation. The event object itself is unchanged. -/
theorem graphProductSlice_hom_changeVertex {V W : C ⥤ Type w}
    (i : V ≅ W) (G : Graph V) :
    ((graphProductSliceEquivalence W).functor.obj (changeVertex i G)).hom =
      ((graphProductSliceEquivalence V).functor.obj G).hom ≫
        prod.map i.hom i.hom := by
  change endpointMap (changeVertex i G) ≫
      (FunctorToTypes.binaryProductIso W W).inv =
    (endpointMap G ≫ (FunctorToTypes.binaryProductIso V V).inv) ≫
      prod.map i.hom i.hom
  rw [endpointMap_changeVertex]
  calc
    (endpointMap G ≫ pairMap i.hom) ≫
        (FunctorToTypes.binaryProductIso W W).inv =
      endpointMap G ≫ (pairMap i.hom ≫
        (FunctorToTypes.binaryProductIso W W).inv) :=
          Category.assoc _ _ _
    _ = endpointMap G ≫
        ((FunctorToTypes.binaryProductIso V V).inv ≫
          prod.map i.hom i.hom) := by
            rw [pairMap_toChosen_natural]
    _ = (endpointMap G ≫
        (FunctorToTypes.binaryProductIso V V).inv) ≫
          prod.map i.hom i.hom :=
            (Category.assoc _ _ _).symm

/-- The endpoint image of any retained event graph is transported by the
chosen-product isomorphism. This uses images in the presheaf target; it does
not infer them from finite limits in an arbitrary target. -/
theorem graphProductSlice_image_changeVertex {V W : C ⥤ Type w}
    (i : V ≅ W) (G : Graph V) :
    imageSubobject
        ((graphProductSliceEquivalence W).functor.obj
          (changeVertex i G)).hom =
      (Subobject.map (prod.mapIso i i).hom).obj
        (imageSubobject
          ((graphProductSliceEquivalence V).functor.obj G).hom) := by
  rw [graphProductSlice_hom_changeVertex]
  exact Categorical.imageSubobject_postIso
    (((graphProductSliceEquivalence V).functor.obj G).hom)
    (prod.mapIso i i)

end Mettapedia.OSLF.Binding.EventGraphImageTransport
