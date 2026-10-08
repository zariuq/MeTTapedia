import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphSmallWReadoutLift

/-!
# Whole material W carriers and sections across universe raising

Arbitrary upper graph members are recovered in both directions. The
fresh upper literal decoder retains the original complete future tree;
whole compatible sections are transported with both inverse laws. The
material square uses the actual independently rebuilt W body reading.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphSmallWCarrierLift

open CategoryTheory Mettapedia.TypeTheory ContextualWitnessCover
open ContextualSmallFamilyUniverse ContextualSmallFamilyComprehension
open ContextualSmallFamilyWTypes ContextualGraphSmallWBranchSpan ContextualGraphSmallWSiteLift
open ContextualGraphSmallWReadoutLift ContextualGraphDiagrams ContextualRealizedGraphs
universe u
variable {D : Type u} [Category.{u} D] {base : D ⥤ Type u}
variable (domain : base.Elements ⥤ Type u) (body : domain.Elements ⥤ Type u)
variable (domainReading : NaturalHom (total domain) (values D))
variable (positionReading : NaturalHom (total (displayedBody domain body)) (values D))

def lowerFamily : ContextualGraphMaterialFamilies.Family base :=
  ⟨w domain body, (original domain body domainReading positionReading).read⟩

def upperFamily : ContextualGraphMaterialFamilies.Family (ContextualGraphMaterialLift.base base) :=
  ⟨w (upperDomain domain) (upperBody domain body), (rebuilt domain body domainReading positionReading).read⟩

def oldParent := ContextualGraphFamilyBodies.parent (w domain body)
  (original domain body domainReading positionReading).read

def newParent := ContextualGraphFamilyBodies.parent (w (upperDomain domain) (upperBody domain body))
  (rebuilt domain body domainReading positionReading).read

def retainedParent : NaturalHom (ContextualGraphMaterialLift.base base)
    (values (ContextualGraphMaterialLift.Upper (D := D))) where
  app _ parameter := ContextualGraphUniverseLift.value ((oldParent domain body domainReading positionReading).app _ parameter.down)
  naturality {_first _second} arrival parameter := congrArg ContextualGraphUniverseLift.value
    ((oldParent domain body domainReading positionReading).naturality arrival.down parameter.down)

def forwardComparison (point : (ContextualGraphMaterialLift.base base).Elements)
    (tree : WAt domain body (originalPoint point)) :
    Equal (ContextualGraphUniverseLift.value ((original domain body domainReading positionReading).read.app point.1.down
      ⟨point.2.down, tree⟩))
      ((rebuilt domain body domainReading positionReading).read.app point.1
        ⟨point.2, (equiv domain body point).symm tree⟩) :=
  (Equal.ofEq (congrArg (fun value => ContextualGraphUniverseLift.value
    ((original domain body domainReading positionReading).read.app point.1.down ⟨point.2.down, value⟩))
    ((equiv domain body point).apply_symm_apply tree).symm)).trans
      (comparison domain body domainReading positionReading point ((equiv domain body point).symm tree))

/-- Universe raising and fresh W formation preserve and reflect the
exact declared material observation kernel, including distinct retained
parameter occurrences. -/
theorem material_kernel (point : ContextualGraphMaterialLift.Upper (D := D))
    (left right : (total (w domain body)).obj point.down) :
    Nonempty (Equal
      ((rebuilt domain body domainReading positionReading).read.app point
        ⟨ULift.up left.1, (equiv domain body ⟨point, ULift.up left.1⟩).symm left.2⟩)
      ((rebuilt domain body domainReading positionReading).read.app point
        ⟨ULift.up right.1, (equiv domain body ⟨point, ULift.up right.1⟩).symm right.2⟩)) ↔
    Nonempty (Equal ((original domain body domainReading positionReading).read.app point.down left)
      ((original domain body domainReading positionReading).read.app point.down right)) := by
  let first := forwardComparison domain body domainReading positionReading ⟨point, ULift.up left.1⟩ left.2
  let second := forwardComparison domain body domainReading positionReading ⟨point, ULift.up right.1⟩ right.2
  constructor
  · rintro ⟨same⟩
    exact ⟨ContextualGraphUniverseLift.reflect (first.trans (same.trans second.symm))⟩
  · rintro ⟨same⟩
    exact ⟨first.symm.trans ((ContextualGraphUniverseLift.preserve same).trans second)⟩

def carrierForth (point : (ContextualGraphMaterialLift.base base).Elements)
    (element : Value (ContextualGraphMaterialLift.Upper (D := D)) point.1)
    (membership : Member element ((retainedParent domain body domainReading positionReading).app point.1 point.2)) :
    Member element ((newParent domain body domainReading positionReading).app point.1 point.2) := by
  let parent := (oldParent domain body domainReading positionReading).app point.1.down point.2.down
  let child := ContextualGraphUniverseLift.childDecoder parent membership.1
  let decoded := ContextualGraphFamilyBodyComparison.memberDecode (w domain body)
    (original domain body domainReading positionReading).read (originalPoint point) (childValue D parent child)
    (Member.atChild parent child)
  exact ContextualGraphFamilyBodyComparison.memberIntro (w (upperDomain domain) (upperBody domain body))
    (rebuilt domain body domainReading positionReading).read point element ((equiv domain body point).symm decoded.1)
    (membership.2.trans ((ContextualGraphUniverseLift.preserve decoded.2).trans
      (forwardComparison domain body domainReading positionReading point decoded.1)))

def carrierBack (point : (ContextualGraphMaterialLift.base base).Elements)
    (element : Value (ContextualGraphMaterialLift.Upper (D := D)) point.1)
    (membership : Member element ((newParent domain body domainReading positionReading).app point.1 point.2)) :
    Member element ((retainedParent domain body domainReading positionReading).app point.1 point.2) := by
  let decoded := ContextualGraphFamilyBodyComparison.memberDecode (w (upperDomain domain) (upperBody domain body))
    (rebuilt domain body domainReading positionReading).read point element membership
  let oldTree := equiv domain body point decoded.1
  let oldReading := (original domain body domainReading positionReading).read.app point.1.down ⟨point.2.down, oldTree⟩
  let member := ContextualGraphFamilyBodyComparison.memberIntro (w domain body)
    (original domain body domainReading positionReading).read (originalPoint point) oldReading oldTree (Equal.refl oldReading)
  exact Member.transportChild
    (decoded.2.trans (comparison domain body domainReading positionReading point decoded.1).symm).symm
    (ContextualGraphUniverseLift.memberPreserve member)

def carrierComparison (point : (ContextualGraphMaterialLift.base base).Elements) :
    Equal ((retainedParent domain body domainReading positionReading).app point.1 point.2)
      ((newParent domain body domainReading positionReading).app point.1 point.2) :=
  extensionality
    (fun target arrival element membership =>
      Member.transportParent (Equal.ofEq ((newParent domain body domainReading positionReading).naturality arrival point.2)).symm
        (carrierForth domain body domainReading positionReading
          ⟨target, (ContextualGraphMaterialLift.base base).map arrival point.2⟩ element
          (Member.transportParent (Equal.ofEq ((retainedParent domain body domainReading positionReading).naturality
            arrival point.2)) membership)))
    (fun target arrival element membership =>
      Member.transportParent (Equal.ofEq ((retainedParent domain body domainReading positionReading).naturality arrival point.2)).symm
        (carrierBack domain body domainReading positionReading
          ⟨target, (ContextualGraphMaterialLift.base base).map arrival point.2⟩ element
          (Member.transportParent (Equal.ofEq ((newParent domain body domainReading positionReading).naturality
            arrival point.2)) membership)))

abbrev oldLiteral := ContextualGraphFamilyBodies.literal (w domain body)
  (original domain body domainReading positionReading).read
abbrev newLiteral := ContextualGraphFamilyBodies.literal (w (upperDomain domain) (upperBody domain body))
  (rebuilt domain body domainReading positionReading).read

def decoder (point : (ContextualGraphMaterialLift.base base).Elements) :
    (newLiteral domain body domainReading positionReading).obj point ≃ (w domain body).obj (originalPoint point) :=
  (ContextualGraphFamilyBodies.decoder (w (upperDomain domain) (upperBody domain body))
    (rebuilt domain body domainReading positionReading).read point).trans (equiv domain body point)

def raiseSection (terms : (w domain body).sections) : (w (upperDomain domain) (upperBody domain body)).sections :=
  ⟨fun point => (equiv domain body point).symm (terms.val (originalPoint point)), by
    intro first second step
    exact (inverse_natural domain body step (terms.val (originalPoint first))).trans
      (congrArg (equiv domain body second).symm (terms.property ((ContextualGraphMaterialLift.elementsDown base).map step)))⟩

def lowerSection (terms : (w (upperDomain domain) (upperBody domain body)).sections) : (w domain body).sections :=
  ⟨fun point => equiv domain body ((ContextualGraphMaterialLift.elementsUp base).obj point)
    (terms.val ((ContextualGraphMaterialLift.elementsUp base).obj point)), by
    intro first second step
    exact (equiv_natural domain body ((ContextualGraphMaterialLift.elementsUp base).map step)
      (terms.val ((ContextualGraphMaterialLift.elementsUp base).obj first))).trans
        (congrArg (equiv domain body ((ContextualGraphMaterialLift.elementsUp base).obj second))
          (terms.property ((ContextualGraphMaterialLift.elementsUp base).map step)))⟩

def treeSections : (w domain body).sections ≃ (w (upperDomain domain) (upperBody domain body)).sections where
  toFun := raiseSection domain body
  invFun := lowerSection domain body
  left_inv terms := by
    apply Subtype.ext
    funext point
    exact (equiv domain body ((ContextualGraphMaterialLift.elementsUp base).obj point)).apply_symm_apply (terms.val point)
  right_inv terms := by
    apply Subtype.ext
    funext point
    exact (equiv domain body point).symm_apply_apply (terms.val point)

def sections : (oldLiteral domain body domainReading positionReading).sections ≃
    (newLiteral domain body domainReading positionReading).sections :=
  (ContextualGraphFamilyBodies.sectionDecoder (w domain body) (original domain body domainReading positionReading).read).trans
    ((treeSections domain body).trans
      (ContextualGraphFamilyBodies.sectionDecoder (w (upperDomain domain) (upperBody domain body))
        (rebuilt domain body domainReading positionReading).read).symm)

theorem section_decoder_square (terms : (oldLiteral domain body domainReading positionReading).sections)
    (point : (ContextualGraphMaterialLift.base base).Elements) :
    decoder domain body domainReading positionReading point ((sections domain body domainReading positionReading terms).val point) =
      (ContextualGraphFamilyBodies.sectionDecoder (w domain body)
        (original domain body domainReading positionReading).read terms).val (originalPoint point) :=
  (equiv domain body point).apply_symm_apply _

def section_material_square (terms : (w domain body).sections)
    (point : (ContextualGraphMaterialLift.base base).Elements) :
    Equal (ContextualGraphUniverseLift.value ((original domain body domainReading positionReading).read.app point.1.down
      ⟨point.2.down, terms.val (originalPoint point)⟩))
      ((rebuilt domain body domainReading positionReading).read.app point.1
        ⟨point.2, (raiseSection domain body terms).val point⟩) :=
  forwardComparison domain body domainReading positionReading point (terms.val (originalPoint point))

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphSmallWCarrierLift
