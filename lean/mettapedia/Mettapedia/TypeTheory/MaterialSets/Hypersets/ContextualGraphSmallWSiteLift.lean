import Mettapedia.TypeTheory.ContextualSmallFamilyWObservedLift
import Mettapedia.TypeTheory.ContextualSmallFamilyWObservedSubstitution
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphMaterialLift

/-!
# Native future W transport on the actual raised material parameter base

The upper material base raises parameter occurrences as well as worlds.
Lowering the raised parameter is an actual natural map to the retained
parameter base. The complete future-cone W equivalence is composed with
the constructed parameter substitution, preserving whole trees and their
root and branch observations.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphSmallWSiteLift

open CategoryTheory Mettapedia.TypeTheory ContextualWitnessCover
open ContextualSmallFamilyUniverse ContextualSmallFamilyTypeFormers ContextualSmallFamilyTypeFormerCoherence
open ContextualSmallFamilyWTypes ContextualSmallFamilyWSubstitution ContextualSmallFamilyWObservedLift
open ContextualGraphDiagrams ContextualRealizedGraphs
universe u
variable {D : Type u} [Category.{u} D] (base : D ⥤ Type u)

def parameterDown : NaturalHom (ContextualGraphMaterialLift.base base) (ContextualFutureSiteLift.base base) where
  app _ parameter := parameter.down
  naturality _ _ := rfl

variable {base} (domain : base.Elements ⥤ Type u) (body : domain.Elements ⥤ Type u)

abbrev upperDomain := domainUnder (parameterDown base) (ContextualFutureSiteLift.family base domain)
abbrev upperBody := bodyUnder (parameterDown base) (ContextualFutureSiteLift.family base domain)
  (ContextualFutureSiteLift.body base domain body)

abbrev retainedPoint (point : (ContextualGraphMaterialLift.base base).Elements) :=
  (elementMap (parameterDown base)).obj point
abbrev originalPoint (point : (ContextualGraphMaterialLift.base base).Elements) :=
  (ContextualGraphMaterialLift.elementsDown base).obj point

def equiv (point : (ContextualGraphMaterialLift.base base).Elements) :
    WAt (upperDomain domain) (upperBody domain body) point ≃ WAt domain body (originalPoint point) :=
  (wComparison (parameterDown base) (ContextualFutureSiteLift.family base domain)
    (ContextualFutureSiteLift.body base domain body) point).symm.trans
      (ContextualFutureSiteWCones.equiv domain body (retainedPoint point))

theorem inverse_natural {first second : (ContextualGraphMaterialLift.base base).Elements}
    (step : first ⟶ second) (tree : WAt domain body (originalPoint first)) :
    wMap (upperDomain domain) (upperBody domain body) step ((equiv domain body first).symm tree) =
      (equiv domain body second).symm
        (wMap domain body ((ContextualGraphMaterialLift.elementsDown base).map step) tree) :=
  (wComparison_natural (parameterDown base) (ContextualFutureSiteLift.family base domain)
    (ContextualFutureSiteLift.body base domain body) step
      ((ContextualFutureSiteWCones.equiv domain body (retainedPoint first)).symm tree)).symm.trans
        (congrArg (wComparison (parameterDown base) (ContextualFutureSiteLift.family base domain)
          (ContextualFutureSiteLift.body base domain body) second)
          (ContextualFutureSiteWCones.inverse_natural domain body ((elementMap (parameterDown base)).map step) tree))

theorem equiv_natural {first second : (ContextualGraphMaterialLift.base base).Elements}
    (step : first ⟶ second) (tree : WAt (upperDomain domain) (upperBody domain body) first) :
    wMap domain body ((ContextualGraphMaterialLift.elementsDown base).map step) (equiv domain body first tree) =
      equiv domain body second (wMap (upperDomain domain) (upperBody domain body) step tree) := by
  apply (equiv domain body second).symm.injective
  rw [Equiv.symm_apply_apply, ← inverse_natural, Equiv.symm_apply_apply]

theorem signature_comparison (point : (ContextualGraphMaterialLift.base base).Elements) :
    ContextualWReindexing.under (ContextualFutureSiteWCones.toRaisedCone point.1)
      (ContextualFutureSiteWCones.raisedSignature domain body (retainedPoint point)) =
      signature (upperDomain domain) (upperBody domain body) point :=
  (ContextualFutureSiteWCones.signature_comparison domain body (retainedPoint point)).trans
    (signature_change (parameterDown base) (ContextualFutureSiteLift.family base domain)
      (ContextualFutureSiteLift.body base domain body) point)

theorem inverse_raw (point : (ContextualGraphMaterialLift.base base).Elements)
    (tree : WAt domain body (originalPoint point)) :
    HEq ((equiv domain body point).symm tree).val
      (liftedRaw domain body (retainedPoint point) tree.val) :=
  (wComparison_raw (parameterDown base) (ContextualFutureSiteLift.family base domain)
    (ContextualFutureSiteLift.body base domain body) point
      ((ContextualFutureSiteWCones.equiv domain body (retainedPoint point)).symm tree)).trans
        (ContextualFutureSiteWCones.inverse_raw domain body (retainedPoint point) tree)

theorem label_inverse (point : (ContextualGraphMaterialLift.base base).Elements)
    (tree : WAt domain body (originalPoint point)) :
    rootNative (upperDomain domain) (upperBody domain body) point ((equiv domain body point).symm tree) =
        ULift.up (rootNative domain body (originalPoint point) tree) := by
  have heads := Raw.label_signature (signature_comparison domain body point).symm
    _ _ (inverse_raw domain body point tree)
  exact eq_of_heq ((native_label_raw (upperDomain domain) (upperBody domain body) point
    ((equiv domain body point).symm tree)).trans
      (heads.trans ((heq_of_eq (lifted_label domain body (retainedPoint point) tree.val)).trans
        (up_heq (native_label_raw domain body (originalPoint point) tree)).symm)))

theorem child_inverse (point : (ContextualGraphMaterialLift.base base).Elements)
    (tree : WAt domain body (originalPoint point))
    (branch : body.obj ⟨originalPoint point, rootNative domain body (originalPoint point) tree⟩)
    (raisedBranch : (upperBody domain body).obj ⟨point,
      rootNative (upperDomain domain) (upperBody domain body) point ((equiv domain body point).symm tree)⟩)
    (positions : HEq raisedBranch (ULift.up branch : ULift.{u+1,u} _)) :
    childNative (upperDomain domain) (upperBody domain body) point ((equiv domain body point).symm tree) raisedBranch =
        (equiv domain body point).symm (childNative domain body (originalPoint point) tree branch) := by
  let upperTree := (equiv domain body point).symm tree
  let rawTree := liftedRaw domain body (retainedPoint point) tree.val
  let rawEq := (inverse_raw domain body point tree).symm
  let signatures := signature_comparison domain body point
  let newPosition := nativePosition (upperDomain domain) (upperBody domain body) point upperTree raisedBranch
  let converted := rawPositionCast signatures rawTree upperTree.val rawEq newPosition
  have argumentEq := (rawPositionCast_heq signatures rawTree upperTree.val rawEq newPosition).trans
    ((nativePosition_heq (upperDomain domain) (upperBody domain body) point upperTree raisedBranch).trans
      (positions.trans (up_heq (nativePosition_heq domain body (originalPoint point) tree branch)).symm))
  have currentEq := Raw.child_signature signatures rawTree upperTree.val rawEq converted newPosition
    (rawPositionCast_heq signatures rawTree upperTree.val rawEq newPosition)
  have rawChildEq := native_child_raw domain body (originalPoint point) tree branch
  apply Subtype.ext
  apply eq_of_heq
  exact (native_child_raw (upperDomain domain) (upperBody domain body) point upperTree raisedBranch).trans
    (currentEq.symm.trans ((heq_of_eq (lifted_child domain body (retainedPoint point) tree.val
      (nativePosition domain body (originalPoint point) tree branch) converted argumentEq)).trans
        ((heq_of_eq (congrArg (liftedRaw domain body (retainedPoint point)) (eq_of_heq rawChildEq))).symm.trans
          (inverse_raw domain body point (childNative domain body (originalPoint point) tree branch)).symm)))


/-- The image of the actual hereditary constructor is the independently
raised constructor. Every future world, arrow and dependent position is
retained in its complete branch function. -/
theorem constructor_raw (point : (ContextualGraphMaterialLift.base base).Elements)
    (label : (futureDomain domain (originalPoint point)).obj (root point.1.down))
    (children : (next : PowerClassPresheafBaseChange.Future.Objects point.1.down) →
      (arrow : root point.1.down ⟶ next) →
      ContextualWTypes.Position (futureDomain domain (originalPoint point)) (futureBody domain body (originalPoint point))
        label arrow → ContextualWTypes.RawTree (futureDomain domain (originalPoint point))
          (futureBody domain body (originalPoint point)) next)
    (natural : ContextualWTypes.Natural (futureDomain domain (originalPoint point))
      (futureBody domain body (originalPoint point)) (.sup label children)) :
    HEq ((equiv domain body point).symm ⟨.sup label children, natural⟩).val
      (ContextualWTypes.RawTree.sup (X := root point.1) (shape :=
        (ContextualWReindexing.under (ContextualFutureSiteWCones.toRaisedCone point.1)
          (ContextualFutureSiteWCones.raisedSignature domain body (retainedPoint point))).1)
        (position := (ContextualWReindexing.under (ContextualFutureSiteWCones.toRaisedCone point.1)
          (ContextualFutureSiteWCones.raisedSignature domain body (retainedPoint point))).2)
        (ULift.up label) (fun next arrow branch =>
          ContextualWReindexing.pull (ContextualFutureSiteWCones.toRaisedCone point.1)
            (ContextualFutureSiteWCones.raisedSignature domain body (retainedPoint point)) next
            (ContextualSiteW.raiseRaw (futureDomain domain (originalPoint point)) (futureBody domain body (originalPoint point))
              ((ContextualFutureSiteWCones.toRaisedCone point.1).obj next)
              (children ((ContextualFutureSiteWCones.toRaisedCone point.1).obj next).down
                ((ContextualFutureSiteWCones.toRaisedCone point.1).map arrow).down branch.down)))) :=
  inverse_raw domain body point ⟨.sup label children, natural⟩

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphSmallWSiteLift
