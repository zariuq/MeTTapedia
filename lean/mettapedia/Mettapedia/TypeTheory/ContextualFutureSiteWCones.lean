import Mettapedia.TypeTheory.ContextualSiteW
import Mettapedia.TypeTheory.ContextualSmallFamilyWTypes
import Mettapedia.TypeTheory.ContextualSiteWReindexing

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

private theorem signatureEquiv_symm_raw
    {E : Type u} [Category.{u} E] {first second : ContextualWReindexing.Signature E}
    (same : first = second) (point : E) (tree : ContextualWReindexing.Tree second point) :
    HEq ((ContextualWReindexing.signatureEquiv same point).symm tree).val tree.val := by
  cases same
  rfl

theorem inverse_raw (point : (ContextualFutureSiteLift.base P).Elements)
    (tree : ContextualSmallFamilyWTypes.WAt domain body ((ContextualFutureSiteLift.elementsDown P).obj point)) :
    HEq ((equiv domain body point).symm tree).val
      (ContextualWReindexing.pull (toRaisedCone point.1) (raisedSignature domain body point)
        (ContextualSmallFamilyUniverse.root point.1)
        (ContextualSiteW.raiseRaw (oldSignature domain body point).1 (oldSignature domain body point).2
          ((toRaisedCone point.1).obj (ContextualSmallFamilyUniverse.root point.1)) tree.val)) := by
  exact signatureEquiv_symm_raw (signature_comparison domain body point).symm _ _

theorem prefix_square {first second : (ContextualFutureSiteLift.base P).Elements} (step : first ⟶ second) :
    PresheafSiteLift.compose (ContextualSmallFamilyUniverse.futurePrefix step.1) (toRaisedCone first.1) =
      PresheafSiteLift.compose (toRaisedCone second.1)
        (ContextualSiteWReindexing.liftFunctor (ContextualSmallFamilyUniverse.futurePrefix step.1.down)) := by
  refine Functor.hext (fun _ => rfl) ?_
  intro _ _ _
  rfl

theorem inverse_natural {first second : (ContextualFutureSiteLift.base P).Elements} (step : first ⟶ second)
    (tree : ContextualSmallFamilyWTypes.WAt domain body ((ContextualFutureSiteLift.elementsDown P).obj first)) :
    ContextualSmallFamilyWTypes.wMap (ContextualFutureSiteLift.family P domain)
        (ContextualFutureSiteLift.body P domain body) step ((equiv domain body first).symm tree) =
      (equiv domain body second).symm
        (ContextualSmallFamilyWTypes.wMap domain body ((ContextualFutureSiteLift.elementsDown P).map step) tree) := by
  apply Subtype.ext
  apply eq_of_heq
  let old := oldSignature domain body first
  let raised := raisedSignature domain body first
  let downStep := (ContextualFutureSiteLift.elementsDown P).map step
  let oldPrefix := ContextualSmallFamilyUniverse.futurePrefix step.1.down
  let newPrefix := ContextualSmallFamilyUniverse.futurePrefix step.1
  let sourceRoot := ContextualSmallFamilyUniverse.root first.1
  let targetRoot := ContextualSmallFamilyUniverse.root second.1
  let oldRootArrow := ContextualSmallFamilyUniverse.rootArrow step.1.down
  let raisedTree := ContextualSiteW.raiseRaw old.1 old.2 ((toRaisedCone first.1).obj sourceRoot) tree.val
  let moved := ContextualWTypes.restrict old.1 old.2 oldRootArrow tree.val
  let raisedMoved := ContextualSiteW.raiseRaw old.1 old.2
    ((ContextualSiteWReindexing.liftFunctor oldPrefix).obj ((toRaisedCone second.1).obj targetRoot)) moved
  have lowerSignature := ContextualSmallFamilyWTypes.signature_prefix domain body downStep
  have upperSignature := signature_comparison domain body first
  have restrictOld := ContextualWReindexing.restrict_signature_heq upperSignature.symm
    (ContextualSmallFamilyUniverse.rootArrow step.1)
    ((equiv domain body first).symm tree).val
    (ContextualWReindexing.pull (toRaisedCone first.1) raised sourceRoot raisedTree)
    (inverse_raw domain body first tree)
  have leftCast := ContextualWReindexing.pull_congr (first := newPrefix) rfl upperSignature.symm rfl _ _ restrictOld
  have leftRestrict := ContextualWReindexing.pull_restrict (toRaisedCone first.1) raised
    (ContextualSmallFamilyUniverse.rootArrow step.1) raisedTree
  have leftPull := ContextualWReindexing.pull_congr (first := newPrefix) rfl
    (leftSignature := ContextualWReindexing.under (toRaisedCone first.1) raised) rfl rfl _ _
    (heq_of_eq leftRestrict.symm)
  have leftComp := ContextualWReindexing.pull_comp newPrefix (toRaisedCone first.1) raised targetRoot
    (ContextualWTypes.restrict raised.1 raised.2
      ((toRaisedCone first.1).map (ContextualSmallFamilyUniverse.rootArrow step.1)) raisedTree)
  have lowered := ContextualSmallFamilyWTypes.wMap_raw domain body downStep tree
  have raisedCast := ContextualSiteWReindexing.raise_congr lowerSignature.symm
    (leftPoint := (toRaisedCone second.1).obj targetRoot) rfl _ _ lowered
  have rightCast := ContextualWReindexing.pull_congr (first := toRaisedCone second.1) rfl
    (congrArg ContextualSiteWReindexing.signatureUp lowerSignature.symm) rfl _ _ raisedCast
  have raisedPull := ContextualSiteWReindexing.raise_pull oldPrefix old
    ((toRaisedCone second.1).obj targetRoot) moved
  have rightPull := ContextualWReindexing.pull_congr (first := toRaisedCone second.1) rfl
    (ContextualSiteWReindexing.signature_under oldPrefix old).symm rfl _ _ raisedPull
  have rightComp := ContextualWReindexing.pull_comp (toRaisedCone second.1)
    (ContextualSiteWReindexing.liftFunctor oldPrefix) raised targetRoot raisedMoved
  have raisedRestrict : raisedMoved = ContextualWTypes.restrict raised.1 raised.2
      ((toRaisedCone first.1).map (ContextualSmallFamilyUniverse.rootArrow step.1)) raisedTree :=
    ContextualSiteW.raise_restrict old.1 old.2
      ((toRaisedCone first.1).map (ContextualSmallFamilyUniverse.rootArrow step.1)) tree.val
  have square := ContextualWReindexing.pull_congr (prefix_square step).symm
    (leftSignature := raised) rfl rfl _ _ (heq_of_eq raisedRestrict)
  exact (ContextualSmallFamilyWTypes.wMap_raw (ContextualFutureSiteLift.family P domain)
    (ContextualFutureSiteLift.body P domain body) step ((equiv domain body first).symm tree)).trans
      (leftCast.trans (leftPull.trans (leftComp.trans
        ((inverse_raw domain body second (ContextualSmallFamilyWTypes.wMap domain body downStep tree)).trans
          (rightCast.trans (rightPull.trans (rightComp.trans square)))).symm)))

theorem equiv_natural {first second : (ContextualFutureSiteLift.base P).Elements} (step : first ⟶ second)
    (tree : ContextualSmallFamilyWTypes.WAt (ContextualFutureSiteLift.family P domain)
      (ContextualFutureSiteLift.body P domain body) first) :
    ContextualSmallFamilyWTypes.wMap domain body ((ContextualFutureSiteLift.elementsDown P).map step)
        (equiv domain body first tree) =
      equiv domain body second
        (ContextualSmallFamilyWTypes.wMap (ContextualFutureSiteLift.family P domain)
          (ContextualFutureSiteLift.body P domain body) step tree) := by
  apply (equiv domain body second).symm.injective
  rw [Equiv.symm_apply_apply, ← inverse_natural, Equiv.symm_apply_apply]

noncomputable def forward : WiderPresheafDependentFunctions.Hom
    (ContextualFutureSiteLift.retained P (ContextualSmallFamilyWTypes.w domain body))
    (ContextualSmallFamilyWTypes.w (ContextualFutureSiteLift.family P domain)
      (ContextualFutureSiteLift.body P domain body)) where
  app point := (equiv domain body point).symm
  naturality step tree := inverse_natural domain body step tree

noncomputable def backward : WiderPresheafDependentFunctions.Hom
    (ContextualSmallFamilyWTypes.w (ContextualFutureSiteLift.family P domain)
      (ContextualFutureSiteLift.body P domain body))
    (ContextualFutureSiteLift.retained P (ContextualSmallFamilyWTypes.w domain body)) where
  app point := equiv domain body point
  naturality step tree := equiv_natural domain body step tree

theorem forward_backward : (forward domain body).comp (backward domain body) =
    WiderPresheafDependentFunctions.Hom.identity _ := by
  apply WiderPresheafDependentFunctions.Hom.ext
  intro point tree
  exact (equiv domain body point).apply_symm_apply tree

theorem backward_forward : (backward domain body).comp (forward domain body) =
    WiderPresheafDependentFunctions.Hom.identity _ := by
  apply WiderPresheafDependentFunctions.Hom.ext
  intro point tree
  exact (equiv domain body point).symm_apply_apply tree

noncomputable def sections : (ContextualSmallFamilyWTypes.w domain body).sections ≃
    (ContextualSmallFamilyWTypes.w (ContextualFutureSiteLift.family P domain)
      (ContextualFutureSiteLift.body P domain body)).sections :=
  (ContextualFutureSiteLift.retainedSections P (ContextualSmallFamilyWTypes.w domain body)).trans {
    toFun := (forward domain body).mapSection
    invFun := (backward domain body).mapSection
    left_inv tree := by
      apply Subtype.ext
      funext point
      exact (equiv domain body point).apply_symm_apply (tree.val point)
    right_inv tree := by
      apply Subtype.ext
      funext point
      exact (equiv domain body point).symm_apply_apply (tree.val point) }

end Mettapedia.TypeTheory.ContextualFutureSiteWCones
