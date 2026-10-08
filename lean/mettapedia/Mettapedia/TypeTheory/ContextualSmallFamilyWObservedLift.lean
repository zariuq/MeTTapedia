import Mettapedia.TypeTheory.ContextualFutureSiteWCones
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphSmallWBranchSpan

/-!
# Actual W root and branch observations across a successor site

The independently formed upper W trees retain the complete hereditary
future branches. Their existing whole-tree equivalence is compared with
root-label and current-branch observations by inspecting the actual
indexed raw trees, including their signature transports.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.TypeTheory.ContextualSmallFamilyWObservedLift

open CategoryTheory MaterialSets.Hypersets
open ContextualSmallFamilyUniverse ContextualSmallFamilyTypeFormers
open ContextualSmallFamilyWTypes ContextualSmallFamilyWAlgebra
open ContextualGraphSmallWBranchSpan ContextualSmallFamilyWObservation
open PowerClassPresheafBaseChange
universe u v

namespace Raw
variable {D : Type u} [Category.{u} D] (shape : D ⥤ Type u) (position : shape.Elements ⥤ Type u)

def label {point : D} : ContextualWTypes.RawTree shape position point → shape.obj point
  | .sup label _ => label

def child {point : D} (tree : ContextualWTypes.RawTree shape position point)
    (branch : ContextualWTypes.Position shape position (label shape position tree) (𝟙 point)) :
    ContextualWTypes.RawTree shape position point :=
  match tree with
  | .sup _ children => children point (𝟙 point) branch

theorem label_signature {first second : ContextualWReindexing.Signature D} (signatures : first = second)
    {point : D} (left : ContextualWReindexing.Raw first point) (right : ContextualWReindexing.Raw second point)
    (same : HEq left right) : HEq (label first.1 first.2 left) (label second.1 second.2 right) := by
  cases signatures
  cases eq_of_heq same
  rfl

theorem child_signature {first second : ContextualWReindexing.Signature D} (signatures : first = second)
    {point : D} (left : ContextualWReindexing.Raw first point) (right : ContextualWReindexing.Raw second point)
    (same : HEq left right)
    (firstBranch : ContextualWTypes.Position first.1 first.2 (label first.1 first.2 left) (𝟙 point))
    (secondBranch : ContextualWTypes.Position second.1 second.2 (label second.1 second.2 right) (𝟙 point))
    (branches : HEq firstBranch secondBranch) :
    HEq (child first.1 first.2 left firstBranch) (child second.1 second.2 right secondBranch) := by
  cases signatures
  cases eq_of_heq same
  cases eq_of_heq branches
  rfl

end Raw

variable {D : Type u} [Category.{u} D] {base : D ⥤ Type v}
variable (domain : base.Elements ⥤ Type u) (body : domain.Elements ⥤ Type u)


def rootNative (point : base.Elements) (tree : WAt domain body point) : domain.obj point :=
  rootLabel domain body (w domain body) point (destructorValue domain body point tree)

def childNative (point : base.Elements) (tree : WAt domain body point)
    (branch : body.obj ⟨point, rootNative domain body point tree⟩) : WAt domain body point :=
  evaluate domain body (w domain body) point (destructorValue domain body point tree) branch

theorem native_label_raw (point : base.Elements) (tree : WAt domain body point) :
    HEq (rootNative domain body point tree)
      (Raw.label (futureDomain domain point) (futureBody domain body point) tree.val) := by
  rcases tree with ⟨tree, natural⟩
  cases tree with
  | sup label children => exact rootLabel_heq domain body (w domain body) point _

def nativePosition (point : base.Elements) (tree : WAt domain body point)
    (branch : body.obj ⟨point, rootNative domain body point tree⟩) :
    ContextualWTypes.Position (futureDomain domain point) (futureBody domain body point)
      (Raw.label (futureDomain domain point) (futureBody domain body point) tree.val) (𝟙 (root point.1)) := by
  rcases tree with ⟨tree, natural⟩
  cases tree with
  | sup label children =>
    exact rootPosition domain body (w domain body) point
      (destructorValue domain body point ⟨.sup label children, natural⟩) branch

theorem nativePosition_heq (point : base.Elements) (tree : WAt domain body point)
    (branch : body.obj ⟨point, rootNative domain body point tree⟩) :
    HEq (nativePosition domain body point tree branch) branch := by
  rcases tree with ⟨tree, natural⟩
  cases tree with
  | sup label children => exact rootPosition_heq domain body (w domain body) point _ branch

theorem native_child_raw (point : base.Elements) (tree : WAt domain body point)
    (branch : body.obj ⟨point, rootNative domain body point tree⟩) :
    HEq (childNative domain body point tree branch).val
      (Raw.child (futureDomain domain point) (futureBody domain body point) tree.val
        (nativePosition domain body point tree branch)) := by
  rcases tree with ⟨tree, natural⟩
  cases tree with
  | sup label children =>
    let current := nativePosition domain body point ⟨.sup label children, natural⟩ branch
    let rawChild : WAt domain body point :=
      ⟨children (root point.1) (𝟙 (root point.1)) current, natural.1 _ _ current⟩
    have evaluated := evaluate_heq domain body (w domain body) point
      (destructorValue domain body point ⟨.sup label children, natural⟩) branch
    have whole := evaluated.trans (ContextualSmallFamilyWCone.coneEquiv_root_heq domain body point rawChild)
    exact heq_of_eq (congrArg Subtype.val (eq_of_heq whole))


theorem up_heq {A B : Type u} {first : A} {second : B} (same : HEq first second) :
    HEq (ULift.up first : ULift.{u+1,u} A) (ULift.up second : ULift.{u+1,u} B) := by
  cases same
  rfl

abbrev raisedDomain := ContextualFutureSiteLift.family base domain
abbrev raisedBody := ContextualFutureSiteLift.body base domain body

abbrev downPoint (point : (ContextualFutureSiteLift.base base).Elements) :=
  (ContextualFutureSiteLift.elementsDown base).obj point

abbrev liftedRaw (point : (ContextualFutureSiteLift.base base).Elements)
    (tree : ContextualWReindexing.Raw (signature domain body (downPoint point)) (root point.1.down)) :=
  ContextualWReindexing.pull (ContextualFutureSiteWCones.toRaisedCone point.1)
    (ContextualFutureSiteWCones.raisedSignature domain body point) (root point.1)
    (ContextualSiteW.raiseRaw (futureDomain domain (downPoint point)) (futureBody domain body (downPoint point))
      ((ContextualFutureSiteWCones.toRaisedCone point.1).obj (root point.1)) tree)

theorem lifted_label (point : (ContextualFutureSiteLift.base base).Elements)
    (tree : ContextualWReindexing.Raw (signature domain body (downPoint point)) (root point.1.down)) :
    Raw.label _ _ (liftedRaw domain body point tree) =
      ULift.up (Raw.label _ _ tree) := by
  cases tree
  rfl

theorem label_inverse (point : (ContextualFutureSiteLift.base base).Elements)
    (tree : WAt domain body (downPoint point)) :
    rootNative (raisedDomain domain) (raisedBody domain body) point
      ((ContextualFutureSiteWCones.equiv domain body point).symm tree) =
        ULift.up (rootNative domain body (downPoint point) tree) := by
  have heads := Raw.label_signature (ContextualFutureSiteWCones.signature_comparison domain body point).symm
    _ _ (ContextualFutureSiteWCones.inverse_raw domain body point tree)
  exact eq_of_heq ((native_label_raw (raisedDomain domain) (raisedBody domain body) point
    ((ContextualFutureSiteWCones.equiv domain body point).symm tree)).trans
      (heads.trans ((heq_of_eq (lifted_label domain body point tree.val)).trans
        (up_heq (native_label_raw domain body (downPoint point) tree)).symm)))

def rawPositionCast {E : Type u} [Category.{u} E]
    {first second : ContextualWReindexing.Signature E} (signatures : first = second)
    {point : E} (left : ContextualWReindexing.Raw first point) (right : ContextualWReindexing.Raw second point)
    (same : HEq left right)
    (branch : ContextualWTypes.Position second.1 second.2 (Raw.label second.1 second.2 right) (𝟙 point)) :
    ContextualWTypes.Position first.1 first.2 (Raw.label first.1 first.2 left) (𝟙 point) := by
  cases signatures
  cases eq_of_heq same
  exact branch

theorem rawPositionCast_heq {E : Type u} [Category.{u} E]
    {first second : ContextualWReindexing.Signature E} (signatures : first = second)
    {point : E} (left : ContextualWReindexing.Raw first point) (right : ContextualWReindexing.Raw second point)
    (same : HEq left right)
    (branch : ContextualWTypes.Position second.1 second.2 (Raw.label second.1 second.2 right) (𝟙 point)) :
    HEq (rawPositionCast signatures left right same branch) branch := by
  cases signatures
  cases eq_of_heq same
  rfl

theorem lifted_child (point : (ContextualFutureSiteLift.base base).Elements)
    (tree : ContextualWReindexing.Raw (signature domain body (downPoint point)) (root point.1.down))
    (branch : ContextualWTypes.Position (futureDomain domain (downPoint point)) (futureBody domain body (downPoint point))
      (Raw.label _ _ tree) (𝟙 (root point.1.down)))
    (raisedBranch : ContextualWTypes.Position _ _ (Raw.label _ _ (liftedRaw domain body point tree)) (𝟙 (root point.1)))
    (positions : HEq raisedBranch (ULift.up branch : ULift.{u+1,u} _)) :
    Raw.child _ _ (liftedRaw domain body point tree) raisedBranch =
      liftedRaw domain body point (Raw.child _ _ tree branch) := by
  cases tree with
  | sup label children =>
    cases eq_of_heq positions
    rfl

theorem child_inverse (point : (ContextualFutureSiteLift.base base).Elements)
    (tree : WAt domain body (downPoint point))
    (branch : body.obj ⟨downPoint point, rootNative domain body (downPoint point) tree⟩)
    (raisedBranch : (raisedBody domain body).obj ⟨point,
      rootNative (raisedDomain domain) (raisedBody domain body) point
        ((ContextualFutureSiteWCones.equiv domain body point).symm tree)⟩)
    (positions : HEq raisedBranch (ULift.up branch : ULift.{u+1,u} _)) :
    childNative (raisedDomain domain) (raisedBody domain body) point
      ((ContextualFutureSiteWCones.equiv domain body point).symm tree) raisedBranch =
        (ContextualFutureSiteWCones.equiv domain body point).symm (childNative domain body (downPoint point) tree branch) := by
  let upperTree := (ContextualFutureSiteWCones.equiv domain body point).symm tree
  let rawTree := liftedRaw domain body point tree.val
  let rawEq := (ContextualFutureSiteWCones.inverse_raw domain body point tree).symm
  let signatures := ContextualFutureSiteWCones.signature_comparison domain body point
  let newPosition := nativePosition (raisedDomain domain) (raisedBody domain body) point upperTree raisedBranch
  let converted := rawPositionCast signatures rawTree upperTree.val rawEq newPosition
  have argumentEq := (rawPositionCast_heq signatures rawTree upperTree.val rawEq newPosition).trans
    ((nativePosition_heq (raisedDomain domain) (raisedBody domain body) point upperTree raisedBranch).trans
      (positions.trans (up_heq (nativePosition_heq domain body (downPoint point) tree branch)).symm))
  have currentEq := Raw.child_signature signatures rawTree upperTree.val rawEq converted newPosition
    (rawPositionCast_heq signatures rawTree upperTree.val rawEq newPosition)
  have rawChildEq := native_child_raw domain body (downPoint point) tree branch
  apply Subtype.ext
  apply eq_of_heq
  exact (native_child_raw (raisedDomain domain) (raisedBody domain body) point upperTree raisedBranch).trans
    (currentEq.symm.trans ((heq_of_eq (lifted_child domain body point tree.val
      (nativePosition domain body (downPoint point) tree branch) converted argumentEq)).trans
        ((heq_of_eq (congrArg (liftedRaw domain body point) (eq_of_heq rawChildEq))).symm.trans
          (ContextualFutureSiteWCones.inverse_raw domain body point
            (childNative domain body (downPoint point) tree branch)).symm)))

end Mettapedia.TypeTheory.ContextualSmallFamilyWObservedLift
