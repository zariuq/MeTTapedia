import Mettapedia.TypeTheory.ContextualSiteW
import Mettapedia.TypeTheory.ContextualSmallFamilyWTypes

/-!
# Complete future cone W transport with wider retained parameters

The actual future category on the raised site is explicitly isomorphic to
the raised original future category. Worlds and every actual arrival and
continuation arrow are kept. Independently formed future signatures compare
through those category maps; structural indexed W transport then compares
their complete natural trees at the roots.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualFutureSiteWCones

open CategoryTheory MaterialSets.Hypersets
open PowerClassPresheafBaseChange

universe u v
variable {D : Type u} [Category.{u} D]

def toRaisedCone (point : PresheafSiteLift.Site D) :
    Future.Objects point ⥤ PresheafSiteLift.Site (Future.Objects point.down) where
  obj future := ⟨⟨future.1.down, future.2.down⟩⟩
  map step := ⟨⟨step.1.down, congrArg ULift.down step.2⟩⟩
  map_id _ := rfl
  map_comp _ _ := rfl

def fromRaisedCone (point : PresheafSiteLift.Site D) :
    PresheafSiteLift.Site (Future.Objects point.down) ⥤ Future.Objects point where
  obj future := ⟨⟨future.down.1⟩, ⟨future.down.2⟩⟩
  map step := ⟨⟨step.down.1⟩, congrArg ULift.up step.down.2⟩
  map_id _ := rfl
  map_comp _ _ := rfl

theorem to_from (point : PresheafSiteLift.Site D) :
    PresheafSiteLift.compose (toRaisedCone point) (fromRaisedCone point) =
      PresheafSiteLift.identity (Future.Objects point) := by
  refine Functor.hext (fun _ => rfl) ?_
  intro _ _ _
  rfl

theorem from_to (point : PresheafSiteLift.Site D) :
    PresheafSiteLift.compose (fromRaisedCone point) (toRaisedCone point) =
      PresheafSiteLift.identity (PresheafSiteLift.Site (Future.Objects point.down)) := by
  refine Functor.hext (fun _ => rfl) ?_
  intro _ _ _
  rfl

def change (point : PresheafSiteLift.Site D) :
    ContextualWLocalChange.LocalFutures (Future.Objects point)
      (PresheafSiteLift.Site (Future.Objects point.down)) where
  functor := toRaisedCone point
  backward future := Future.map (fromRaisedCone point) ((toRaisedCone point).obj future)
  left _ := by
    refine Functor.hext (fun _ => rfl) ?_
    intro _ _ _
    rfl
  right _ := by
    refine Functor.hext (fun _ => rfl) ?_
    intro _ _ _
    rfl

variable {P : D ⥤ Type v} (domain : P.Elements ⥤ Type u) (body : domain.Elements ⥤ Type u)

def oldSignature (point : (ContextualFutureSiteLift.base P).Elements) :=
  ContextualSmallFamilyWTypes.signature domain body ((ContextualFutureSiteLift.elementsDown P).obj point)

def raisedSignature (point : (ContextualFutureSiteLift.base P).Elements) :
    ContextualWReindexing.Signature (PresheafSiteLift.Site (Future.Objects point.1.down)) :=
  ⟨ContextualSiteW.shapeUp (oldSignature domain body point).1,
    ContextualSiteW.positionUp (oldSignature domain body point).1 (oldSignature domain body point).2⟩

theorem domain_comparison (point : (ContextualFutureSiteLift.base P).Elements) :
    ContextualWLocalChange.sourceDomain (change point.1) (raisedSignature domain body point).1 =
      ContextualSmallFamilyTypeFormers.futureDomain (ContextualFutureSiteLift.family P domain) point := by
  refine Functor.hext (fun _ => rfl) ?_
  intro _ _ _
  rfl

theorem signature_comparison (point : (ContextualFutureSiteLift.base P).Elements) :
    ContextualWReindexing.under (toRaisedCone point.1) (raisedSignature domain body point) =
      ContextualSmallFamilyWTypes.signature (ContextualFutureSiteLift.family P domain)
        (ContextualFutureSiteLift.body P domain body) point := by
  apply Sigma.ext (domain_comparison domain body point)
  apply ContextualWReindexing.position_transport_heq (domain_comparison domain body point)
  refine Functor.hext (fun _ => rfl) ?_
  intro _ _ _
  rfl

noncomputable def equiv (point : (ContextualFutureSiteLift.base P).Elements) :
    ContextualSmallFamilyWTypes.WAt (ContextualFutureSiteLift.family P domain)
        (ContextualFutureSiteLift.body P domain body) point ≃
      ContextualSmallFamilyWTypes.WAt domain body ((ContextualFutureSiteLift.elementsDown P).obj point) :=
  (ContextualWReindexing.signatureEquiv (signature_comparison domain body point).symm
    (ContextualSmallFamilyUniverse.root point.1)).trans
    ((ContextualWLocalChange.naturalEquiv (change point.1) (raisedSignature domain body point).1
      (raisedSignature domain body point).2 (ContextualSmallFamilyUniverse.root point.1)).symm.trans
        (ContextualSiteW.naturalEquiv (oldSignature domain body point).1 (oldSignature domain body point).2
          ((toRaisedCone point.1).obj (ContextualSmallFamilyUniverse.root point.1))))

end Mettapedia.TypeTheory.ContextualFutureSiteWCones
