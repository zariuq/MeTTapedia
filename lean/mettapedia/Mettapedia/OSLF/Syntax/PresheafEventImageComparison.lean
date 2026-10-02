import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Images
import Mathlib.CategoryTheory.Limits.Shapes.FunctorToTypes
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Shapes.RegularMono
import Mathlib.CategoryTheory.Subfunctor.Subobject
import Mathlib.CategoryTheory.Subobject.Limits
import Mettapedia.GSLT.Topos.PresheafEventModalities

/-!
# Endpoint images and cocontinuous transport

The range of a natural map is a coequalizer of its pointwise kernel relation.
Consequently a functor preserving these coequalizers sends the retained event
quotient onto the image of the transported endpoint map. The transported range
inclusion need not be mono. The comparison becomes an isomorphism when that
particular inclusion remains mono.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Binding.PresheafEventImageComparison

open CategoryTheory CategoryTheory.Limits

universe u v w uD vD

variable {C : Type u} [Category.{v} C]
variable {E P : C ⥤ Type w} (f : E ⟶ P)

/-- Pairs of individual sections with the same observed image. -/
def kernelRelation : C ⥤ Type w where
  obj X := { pair : E.obj X × E.obj X // f.app X pair.1 = f.app X pair.2 }
  map {X Y} k := TypeCat.ofHom fun pair =>
    ⟨(E.map k pair.1.1, E.map k pair.1.2), by
      rw [NatTrans.naturality_apply, NatTrans.naturality_apply, pair.2]⟩
  map_id X := by ext pair <;> simp
  map_comp k l := by ext pair <;> simp

def kernelLeft : kernelRelation f ⟶ E where
  app _ := TypeCat.ofHom fun pair => pair.1.1
  naturality _ _ _ := rfl

def kernelRight : kernelRelation f ⟶ E where
  app _ := TypeCat.ofHom fun pair => pair.1.2
  naturality _ _ _ := rfl

theorem kernel_endpoint : kernelLeft f ≫ f = kernelRight f ≫ f := by
  ext X pair
  exact pair.2

theorem kernel_quotient :
    kernelLeft f ≫ Subfunctor.toRange f = kernelRight f ≫ Subfunctor.toRange f := by
  apply (cancel_mono (Subfunctor.range f).ι).1
  simp only [Category.assoc, Subfunctor.toRange_ι]
  exact kernel_endpoint f

/-- The actual range quotient, with the individual event carrier retained
as the domain of its two relation projections. -/
def rangeCofork : Cofork (kernelLeft f) (kernelRight f) :=
  Cofork.ofπ (Subfunctor.toRange f) (kernel_quotient f)

private theorem cofork_components (s : Cofork (kernelLeft f) (kernelRight f))
    (X : C) (x y : E.obj X) (same : f.app X x = f.app X y) :
    s.π.app X x = s.π.app X y :=
  congrArg (fun arrow => arrow.app X ⟨(x, y), same⟩) s.condition

private def rangeDesc (s : Cofork (kernelLeft f) (kernelRight f)) :
    (Subfunctor.range f).toFunctor ⟶ s.pt where
  app X := TypeCat.ofHom fun point => s.π.app X point.2.choose
  naturality X Y k := by
    ext point
    change s.π.app Y
        (show ∃ e, f.app Y e = P.map k point.1 from
          ((Subfunctor.range f).toFunctor.map k point).2).choose =
      s.pt.map k (s.π.app X point.2.choose)
    rw [← NatTrans.naturality_apply s.π k point.2.choose]
    apply cofork_components f s Y
    have chosen : f.app Y
        (((Subfunctor.range f).toFunctor.map k point).2.choose) = P.map k point.1 :=
      ((Subfunctor.range f).toFunctor.map k point).2.choose_spec
    exact chosen.trans ((NatTrans.naturality_apply f k point.2.choose).trans
      (congrArg (P.map k) point.2.choose_spec)).symm

private theorem rangeDesc_fac (s : Cofork (kernelLeft f) (kernelRight f)) :
    Subfunctor.toRange f ≫ rangeDesc f s = s.π := by
  ext X event
  apply cofork_components f s X
  exact ((Subfunctor.toRange f).app X event).2.choose_spec

/-- The pointwise endpoint image is an actual categorical quotient of its
kernel relation, rather than merely a proposition about its sections. -/
def rangeCoforkIsColimit : IsColimit (rangeCofork f) :=
  Cofork.IsColimit.mk _ (rangeDesc f) (rangeDesc_fac f)
    (fun s _m same => (cancel_epi (Subfunctor.toRange f)).1
      (same.trans (rangeDesc_fac f s).symm))

/-- An explicit regular-epimorphism witness for the range quotient. -/
def rangeRegularEpi : RegularEpi (Subfunctor.toRange f) where
  W := kernelRelation f
  left := kernelLeft f
  right := kernelRight f
  w := kernel_quotient f
  isColimit := rangeCoforkIsColimit f

section Transport

variable {D : Type uD} [Category.{vD} D]
variable (L : (C ⥤ Type w) ⥤ D)
variable [PreservesColimitsOfShape WalkingParallelPair L]

/-- Coequalizer preservation suffices to preserve the event-to-range
quotient. No finite-limit or mono-preservation assumption is used. -/
def transportedRangeRegularEpi : RegularEpi (L.map (Subfunctor.toRange f)) where
  W := L.obj (kernelRelation f)
  left := L.map (kernelLeft f)
  right := L.map (kernelRight f)
  w := by rw [← L.map_comp, ← L.map_comp, kernel_quotient f]
  isColimit := isColimitCoforkMapOfIsColimit L _ (rangeCoforkIsColimit f)

theorem transportedRange_epi : Epi (L.map (Subfunctor.toRange f)) :=
  (transportedRangeRegularEpi f L).epi _

variable [HasImage (L.map f)]

omit [PreservesColimitsOfShape WalkingParallelPair L] in
private theorem transportedRelation_image :
    L.map (kernelLeft f) ≫ factorThruImage (L.map f) =
      L.map (kernelRight f) ≫ factorThruImage (L.map f) := by
  apply (cancel_mono (image.ι (L.map f))).1
  simp only [Category.assoc, image.fac, ← L.map_comp, kernel_endpoint f]

/-- The transported generic reduction maps to the actual image of the
transported event endpoint arrow. The map is constructed by the preserved
coequalizer, even when the transported reduction inclusion is not mono. -/
def transportedImageComparison :
    L.obj (Subfunctor.range f).toFunctor ⟶ image (L.map f) :=
  ((transportedRangeRegularEpi f L).desc' (factorThruImage (L.map f))
    (transportedRelation_image f L)).1

theorem transportedImageComparison_events :
    L.map (Subfunctor.toRange f) ≫ transportedImageComparison f L =
      factorThruImage (L.map f) :=
  ((transportedRangeRegularEpi f L).desc' (factorThruImage (L.map f))
    (transportedRelation_image f L)).2

theorem transportedImageComparison_ι :
    transportedImageComparison f L ≫ image.ι (L.map f) =
      L.map (Subfunctor.range f).ι := by
  let := transportedRange_epi f L
  apply (cancel_epi (L.map (Subfunctor.toRange f))).1
  rw [← Category.assoc, transportedImageComparison_events, image.fac,
    ← L.map_comp, Subfunctor.toRange_ι]

theorem transportedImageComparison_unique
    (comparison : L.obj (Subfunctor.range f).toFunctor ⟶ image (L.map f))
    (same : L.map (Subfunctor.toRange f) ≫ comparison = factorThruImage (L.map f)) :
    comparison = transportedImageComparison f L := by
  let := transportedRange_epi f L
  exact (cancel_epi (L.map (Subfunctor.toRange f))).1
    (same.trans (transportedImageComparison_events f L).symm)

variable [HasEqualizers D]

/-- Colimit preservation gives coverage of the transported endpoint image,
without identifying the transported reduction object as a subobject. -/
theorem transportedImageComparison_epi : Epi (transportedImageComparison f L) :=
  epi_of_epi_fac (transportedImageComparison_events f L)

omit [HasEqualizers D] in
/-- The additional relevant mono-preservation hypothesis upgrades the
comparison to an isomorphism. The coequalizer comparison alone does not. -/
theorem transportedImageComparison_isIso [Mono (L.map (Subfunctor.range f).ι)] :
    IsIso (transportedImageComparison f L) := by
  let factor : MonoFactorisation (L.map f) :=
    { I := L.obj (Subfunctor.range f).toFunctor
      m := L.map (Subfunctor.range f).ι
      e := L.map (Subfunctor.toRange f)
      fac := by rw [← L.map_comp, Subfunctor.toRange_ι] }
  refine ⟨⟨image.lift factor, ?_, ?_⟩⟩
  · apply (cancel_mono (L.map (Subfunctor.range f).ι)).1
    rw [Category.assoc, image.lift_fac factor, transportedImageComparison_ι]
    exact (Category.id_comp _).symm
  · apply (cancel_mono (image.ι (L.map f))).1
    rw [Category.assoc, transportedImageComparison_ι, image.lift_fac factor]
    exact (Category.id_comp _).symm

variable {Q : D} (i : L.obj P ≅ Q)

/-- Comparing the transported pair object with an actual semantic pair
object changes the codomain, retaining the same individual events. -/
abbrev transportedEndpoint : L.obj E ⟶ Q := L.map f ≫ i.hom

def transportedImageComparisonPostIso :
    L.obj (Subfunctor.range f).toFunctor ⟶ image (transportedEndpoint f L i) :=
  transportedImageComparison f L ≫ (image.compIso (L.map f) i.hom).hom

theorem transportedImageComparisonPostIso_ι :
    transportedImageComparisonPostIso f L i ≫ image.ι (transportedEndpoint f L i) =
      L.map (Subfunctor.range f).ι ≫ i.hom := by
  rw [transportedImageComparisonPostIso, Category.assoc,
    image.compIso_hom_comp_image_ι, ← Category.assoc, transportedImageComparison_ι]

theorem transportedImageComparisonPostIso_events :
    L.map (Subfunctor.toRange f) ≫ transportedImageComparisonPostIso f L i =
      factorThruImage (transportedEndpoint f L i) := by
  apply (cancel_mono (image.ι (transportedEndpoint f L i))).1
  rw [Category.assoc, transportedImageComparisonPostIso_ι,
    ← Category.assoc, ← L.map_comp, Subfunctor.toRange_ι, image.fac]

theorem transportedImageComparisonPostIso_epi :
    Epi (transportedImageComparisonPostIso f L i) := by
  let := transportedImageComparison_epi f L
  exact epi_comp _ _

theorem transportedImageComparisonPostIso_isIso
    [Mono (L.map (Subfunctor.range f).ι)] :
    IsIso (transportedImageComparisonPostIso f L i) := by
  let := transportedImageComparison_isIso f L
  change IsIso (transportedImageComparison f L ≫ (image.compIso (L.map f) i.hom).hom)
  infer_instance

end Transport

section EventGraph

open Mettapedia.GSLT.Topos.ConstructivePresheaf (EventGraph)
open Mettapedia.GSLT.Topos.PresheafEventModalities

variable (G : EventGraph.{u, v, w} C)

/-- Pairing preserves the retained carrier; only its range forgets which
individual event witnessed a pair of endpoints. -/
def endpointMap : G.edge ⟶ FunctorToTypes.prod G.vertex G.vertex :=
  FunctorToTypes.prod.lift G.source G.target

def reduction : Subfunctor (FunctorToTypes.prod G.vertex G.vertex) :=
  Subfunctor.range (endpointMap G)

def reductionSubobject : Subobject (FunctorToTypes.prod G.vertex G.vertex) :=
  Subobject.mk (reduction G).ι

theorem mem_reduction_iff (X : C) (pair : G.vertex.obj X × G.vertex.obj X) :
    pair ∈ (reduction G).obj X ↔
      ∃ event : G.edge.obj X,
        G.source.app X event = pair.1 ∧ G.target.app X event = pair.2 := by
  change (∃ event, (G.source.app X event, G.target.app X event) = pair) ↔ _
  constructor
  · rintro ⟨event, same⟩
    exact ⟨event, congrArg Prod.fst same, congrArg Prod.snd same⟩
  · rintro ⟨event, first, second⟩
    exact ⟨event, Prod.ext first second⟩

/-- The pointwise reduction inclusion satisfies the categorical image
universal property against every mono factorization. -/
def reductionIsImage : IsImage (FunctorToTypes.monoFactorisation (endpointMap G)) :=
  FunctorToTypes.monoFactorisationIsImage (endpointMap G)

def reductionImageIso : image (endpointMap G) ≅ (reduction G).toFunctor :=
  IsImage.isoExt (Image.isImage (endpointMap G)) (reductionIsImage G)

theorem reductionImageIso_ι :
    (reductionImageIso G).hom ≫ (reduction G).ι = image.ι (endpointMap G) :=
  IsImage.isoExt_hom_m (Image.isImage (endpointMap G)) (reductionIsImage G)

theorem reductionSubobject_eq_image :
    reductionSubobject G = imageSubobject (endpointMap G) :=
  (Subobject.mk_eq_mk_of_comm _ _ (reductionImageIso G) (reductionImageIso_ι G)).symm

theorem reduction_factorization :
    Subfunctor.toRange (endpointMap G) ≫ (reduction G).ι = endpointMap G :=
  Subfunctor.toRange_ι _

theorem reduction_quotient_surjective (X : C) :
    Function.Surjective ((Subfunctor.toRange (endpointMap G)).app X) := by
  rintro ⟨pair, event, same⟩
  exact ⟨event, Subtype.ext same⟩

/-- The constructive image operation agrees with Mathlib's subfunctor
direct image on the same actual natural map. -/
theorem constructiveImage_eq {A B : C ⥤ Type w} (map : A ⟶ B) (predicate : Subfunctor A) :
    Mettapedia.GSLT.Topos.ConstructivePresheaf.image map predicate = predicate.image map := rfl

theorem constructivePreimage_eq {A B : C ⥤ Type w} (map : A ⟶ B) (predicate : Subfunctor B) :
    Mettapedia.GSLT.Topos.ConstructivePresheaf.preimage map predicate = predicate.preimage map :=
  rfl

/-- The shared may-step modality depends precisely on the endpoint image;
the full event witness still appears in its independent graph definition. -/
theorem diamond_reduction_spec (predicate : Subfunctor G.vertex) (X : C)
    (x : G.vertex.obj X) :
    x ∈ (diamond G predicate).obj X ↔
      ∃ y : G.vertex.obj X, (x, y) ∈ (reduction G).obj X ∧ y ∈ predicate.obj X := by
  rw [diamond_spec]
  constructor
  · rintro ⟨event, target, source⟩
    exact ⟨G.target.app X event, (mem_reduction_iff G X _).2 ⟨event, source, rfl⟩, target⟩
  · rintro ⟨y, step, target⟩
    obtain ⟨event, source, endpoint⟩ := (mem_reduction_iff G X _).1 step
    exact ⟨event, endpoint ▸ target, source⟩

/-- The right adjoint is the step-past box and quantifies over all further
restrictions, including sections of newly available event carriers. -/
theorem box_reduction_spec (predicate : Subfunctor G.vertex) (X : C)
    (x : G.vertex.obj X) :
    x ∈ (box G predicate).obj X ↔
      ∀ (Y : C) (k : X ⟶ Y) (y : G.vertex.obj Y),
        (y, G.vertex.map k x) ∈ (reduction G).obj Y → y ∈ predicate.obj Y := by
  rw [box_spec]
  constructor
  · intro holds Y k y step
    obtain ⟨event, source, target⟩ := (mem_reduction_iff G Y _).1 step
    change G.source.app Y event = y at source
    exact source ▸ holds Y k event target
  · intro holds Y k event target
    exact holds Y k (G.source.app Y event)
      ((mem_reduction_iff G Y _).2 ⟨event, rfl, target⟩)

theorem forwardBox_reduction_spec (predicate : Subfunctor G.vertex) (X : C)
    (x : G.vertex.obj X) :
    x ∈ (forwardBox G predicate).obj X ↔
      ∀ (Y : C) (k : X ⟶ Y) (y : G.vertex.obj Y),
        (G.vertex.map k x, y) ∈ (reduction G).obj Y → y ∈ predicate.obj Y := by
  rw [forwardBox_spec]
  constructor
  · intro holds Y k y step
    obtain ⟨event, source, target⟩ := (mem_reduction_iff G Y _).1 step
    change G.target.app Y event = y at target
    exact target ▸ holds Y k event source
  · intro holds Y k event source
    exact holds Y k (G.target.app Y event)
      ((mem_reduction_iff G Y _).2 ⟨event, source, rfl⟩)

theorem diamond_box_adjunction :
    GaloisConnection (diamond G) (box G) :=
  Mettapedia.GSLT.Topos.PresheafEventModalities.galois G

end EventGraph


end Mettapedia.OSLF.Binding.PresheafEventImageComparison

end
