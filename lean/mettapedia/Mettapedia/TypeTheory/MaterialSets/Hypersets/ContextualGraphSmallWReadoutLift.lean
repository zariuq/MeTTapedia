import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphSmallWSiteLift
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphPolynomialReadoutSiteMatching
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphSmallWReadoutSubstitution

/-!
# Independent material W formation commutes with universe raising

The upper W family is formed afresh over raised parameters, labels and
dependent positions. Its actual material label and argument bodies are
raised lower readings. Native future-tree transport supplies both branch
lifts for a constructed material matching, rather than equating carriers
merely because their native fibres are equivalent.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphSmallWReadoutLift

open CategoryTheory Mettapedia.TypeTheory ContextualWitnessCover
open ContextualSmallFamilyUniverse ContextualSmallFamilyComprehension
open ContextualSmallFamilyWTypes ContextualSmallFamilyWObservedLift
open ContextualGraphSmallWBranchSpan ContextualGraphSmallWSiteLift
open ContextualGraphDiagrams ContextualRealizedGraphs ContextualGraphPolynomialReadoutMatching

universe u
variable {D : Type u} [Category.{u} D] {base : D ⥤ Type u}
variable (domain : base.Elements ⥤ Type u) (body : domain.Elements ⥤ Type u)
variable (domainReading : NaturalHom (total domain) (values D))
variable (positionReading : NaturalHom (total (displayedBody domain body)) (values D))

def raisedDomainReading : NaturalHom (total (upperDomain domain)) (values (ContextualGraphMaterialLift.Upper (D := D))) where
  app _ receipt := ContextualGraphUniverseLift.value (domainReading.app _ ⟨receipt.1.down, receipt.2.down⟩)
  naturality {_first _second} arrival receipt :=
    congrArg ContextualGraphUniverseLift.value (domainReading.naturality arrival.down ⟨receipt.1.down, receipt.2.down⟩)

def raisedPositionReading : NaturalHom (total (displayedBody (upperDomain domain) (upperBody domain body)))
    (values (ContextualGraphMaterialLift.Upper (D := D))) where
  app _ receipt := ContextualGraphUniverseLift.value
    (positionReading.app _ ⟨⟨receipt.1.1.down, receipt.1.2.down⟩, receipt.2.down⟩)
  naturality {_first _second} arrival receipt :=
    congrArg ContextualGraphUniverseLift.value
      (positionReading.naturality arrival.down ⟨⟨receipt.1.1.down, receipt.1.2.down⟩, receipt.2.down⟩)

def original : System D := ContextualGraphSmallWReadoutSubstitution.original domain body domainReading positionReading

def rebuilt : System (ContextualGraphMaterialLift.Upper (D := D)) :=
  ContextualGraphSmallWReadoutSubstitution.original (upperDomain domain) (upperBody domain body)
    (raisedDomainReading domain domainReading) (raisedPositionReading domain body positionReading)

def project : NaturalHom (total (w (upperDomain domain) (upperBody domain body)))
    (ContextualFutureSiteLift.base (total (w domain body))) where
  app point receipt := ⟨receipt.1.down, equiv domain body ⟨point, receipt.1⟩ receipt.2⟩
  naturality {first second} arrival receipt :=
    congrArg (Sigma.mk (base.map arrival.down receipt.1.down))
      (equiv_natural domain body (CategoryOfElements.homMk (F := ContextualGraphMaterialLift.base base)
        ⟨first, receipt.1⟩ ⟨second, (ContextualGraphMaterialLift.base base).map arrival receipt.1⟩ arrival rfl) receipt.2)

theorem label_lower (point : (ContextualGraphMaterialLift.base base).Elements)
    (tree : WAt (upperDomain domain) (upperBody domain body) point) :
    (labelNative (upperDomain domain) (upperBody domain body)).app point tree =
      ULift.up ((labelNative domain body).app (originalPoint point) (equiv domain body point tree)) :=
  (congrArg (rootNative (upperDomain domain) (upperBody domain body) point)
    ((equiv domain body point).symm_apply_apply tree)).symm.trans
      (ContextualGraphSmallWSiteLift.label_inverse domain body point (equiv domain body point tree))

def branchComparison (point : (ContextualGraphMaterialLift.base base).Elements)
    (tree : WAt (upperDomain domain) (upperBody domain body) point) :
    body.obj ⟨originalPoint point, (labelNative domain body).app (originalPoint point) (equiv domain body point tree)⟩ ≃
      (upperBody domain body).obj ⟨point, (labelNative (upperDomain domain) (upperBody domain body)).app point tree⟩ :=
  Equiv.ulift.symm.trans (ContextualGraphSmallWReadoutSubstitution.castEquivalence
    (congrArg (fun label => (upperBody domain body).obj ⟨point, label⟩) (label_lower domain body point tree).symm))

theorem branch_value (point : (ContextualGraphMaterialLift.base base).Elements)
    (tree : WAt (upperDomain domain) (upperBody domain body) point)
    (branch : body.obj ⟨originalPoint point, (labelNative domain body).app (originalPoint point) (equiv domain body point tree)⟩) :
    HEq (branchComparison domain body point tree branch) (ULift.up branch : ULift.{u+1,u} _) :=
  ContextualSmallFamilyUniverse.cast_heq _ _

theorem ulift_down_heq {A B : Type u} (types : A = B)
    (left : ULift.{u+1,u} A) (right : ULift.{u+1,u} B) (same : HEq left right) :
    HEq left.down right.down := by
  cases types
  exact heq_of_eq (congrArg ULift.down (eq_of_heq same))

theorem branch_down (point : (ContextualGraphMaterialLift.base base).Elements)
    (tree : WAt (upperDomain domain) (upperBody domain body) point)
    (branch : body.obj ⟨originalPoint point, (labelNative domain body).app (originalPoint point) (equiv domain body point tree)⟩) :
    HEq (branchComparison domain body point tree branch).down branch := by
  exact ulift_down_heq (congrArg (fun label => body.obj ⟨originalPoint point, label⟩)
    (congrArg ULift.down (label_lower domain body point tree)))
    (branchComparison domain body point tree branch) (ULift.up branch)
    (branch_value domain body point tree branch)

theorem argument_comparison (point : (ContextualGraphMaterialLift.base base).Elements)
    (tree : WAt (upperDomain domain) (upperBody domain body) point)
    (branch : (branches domain body).obj ⟨point.1.down, (project domain body).app point.1 ⟨point.2, tree⟩⟩) :
    ContextualGraphUniverseLift.value ((original domain body domainReading positionReading).arguments.app point.1.down
        ⟨(project domain body).app point.1 ⟨point.2, tree⟩, branch⟩) =
      (rebuilt domain body domainReading positionReading).arguments.app point.1
        ⟨⟨point.2, tree⟩, branchComparison domain body point tree branch⟩ := by
  apply congrArg ContextualGraphUniverseLift.value
  apply congrArg (positionReading.app point.1.down)
  apply Sigma.ext
  · exact Sigma.ext rfl (heq_of_eq (congrArg ULift.down (label_lower domain body point tree)).symm)
  · exact (branch_down domain body point tree branch).symm

theorem child_comparison (point : (ContextualGraphMaterialLift.base base).Elements)
    (tree : WAt (upperDomain domain) (upperBody domain body) point)
    (branch : (branches domain body).obj ⟨point.1.down, (project domain body).app point.1 ⟨point.2, tree⟩⟩) :
    (childTarget domain body).app point.1.down ⟨(project domain body).app point.1 ⟨point.2, tree⟩, branch⟩ =
      (project domain body).app point.1
        ((childTarget (upperDomain domain) (upperBody domain body)).app point.1
          ⟨⟨point.2, tree⟩, branchComparison domain body point tree branch⟩) := by
  apply congrArg (Sigma.mk point.2.down)
  let oldTree := equiv domain body point tree
  let property := fun (nextTree : WAt (upperDomain domain) (upperBody domain body) point) =>
    ∀ (nextBranch : (upperBody domain body).obj
      ⟨point, (labelNative (upperDomain domain) (upperBody domain body)).app point nextTree⟩),
      HEq nextBranch (ULift.up branch : ULift.{u+1,u} _) →
        child (upperDomain domain) (upperBody domain body) point nextTree nextBranch =
          (equiv domain body point).symm (child domain body (originalPoint point) oldTree branch)
  have observed : property ((equiv domain body point).symm oldTree) :=
    ContextualGraphSmallWSiteLift.child_inverse domain body point oldTree branch
  have transported : property tree := ((equiv domain body point).symm_apply_apply tree) ▸ observed
  exact ((congrArg (equiv domain body point)
    (transported (branchComparison domain body point tree branch) (branch_value domain body point tree branch))).trans
      ((equiv domain body point).apply_symm_apply _)).symm

def matching : ContextualGraphPolynomialReadoutSiteMatching.Matching (original domain body domainReading positionReading)
    (rebuilt domain body domainReading positionReading) where
  relation point left right := ULift.{u+1,0} (PLift (left = (project domain body).app point right))
  stable := fun {_ _} arrival {_ _} related =>
    ⟨⟨(congrArg ((total (w domain body)).map arrival.down) related.down.down).trans
      ((project domain body).naturality arrival _)⟩⟩
  labels := by
    intro point left right related
    rcases right with ⟨parameter, tree⟩
    rcases related with ⟨⟨same⟩⟩
    subst left
    exact Equal.ofEq (congrArg ContextualGraphUniverseLift.value
      (congrArg (fun label => domainReading.app point.down ⟨parameter.down, label⟩)
        (congrArg ULift.down (label_lower domain body ⟨point, parameter⟩ tree)).symm))
  forth := by
    intro point left right related branch
    rcases right with ⟨parameter, tree⟩
    rcases related with ⟨⟨same⟩⟩
    subst left
    exact ⟨branchComparison domain body ⟨point, parameter⟩ tree branch,
      Equal.ofEq (argument_comparison domain body domainReading positionReading ⟨point, parameter⟩ tree branch),
      ⟨⟨child_comparison domain body ⟨point, parameter⟩ tree branch⟩⟩⟩
  back := by
    intro point left right related branch
    rcases right with ⟨parameter, tree⟩
    rcases related with ⟨⟨same⟩⟩
    subst left
    let recovered := (branchComparison domain body ⟨point, parameter⟩ tree).symm branch
    have roundtrip := (branchComparison domain body ⟨point, parameter⟩ tree).apply_symm_apply branch
    refine ⟨recovered, ?_, ?_⟩
    · exact Equal.ofEq ((argument_comparison domain body domainReading positionReading
        ⟨point, parameter⟩ tree recovered).trans
          (congrArg (fun argument => (rebuilt domain body domainReading positionReading).arguments.app point
            ⟨⟨parameter, tree⟩, argument⟩) roundtrip))
    · exact ⟨⟨(child_comparison domain body ⟨point, parameter⟩ tree recovered).trans
        (congrArg (fun argument => (project domain body).app point
          ((childTarget (upperDomain domain) (upperBody domain body)).app point
            ⟨⟨parameter, tree⟩, argument⟩)) roundtrip)⟩⟩

def comparison (point : (ContextualGraphMaterialLift.base base).Elements)
    (tree : WAt (upperDomain domain) (upperBody domain body) point) :
    Equal (ContextualGraphUniverseLift.value ((original domain body domainReading positionReading).read.app point.1.down
      ((project domain body).app point.1 ⟨point.2, tree⟩)))
      ((rebuilt domain body domainReading positionReading).read.app point.1 ⟨point.2, tree⟩) :=
  ContextualGraphPolynomialReadoutSiteMatching.comparison (matching domain body domainReading positionReading) ⟨⟨rfl⟩⟩

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphSmallWReadoutLift
