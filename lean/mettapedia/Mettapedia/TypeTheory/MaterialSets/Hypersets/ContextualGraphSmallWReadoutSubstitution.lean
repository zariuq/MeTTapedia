import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphPolynomialReadoutMatching
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphSmallWReadout
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphFamilyBodySubstitution
import Mettapedia.TypeTheory.ContextualSmallFamilyWObservedSubstitution

/-!
# Independently rebuilt material W readings under substitution

The whole native W substitution has inverse maps. Its root labels and
evaluated branches induce a concrete two-sided state matching between
the original graph and the independently rebuilt graph. Their material
readings therefore agree at every future context, even for parameter
maps which forget coordinates. The attached W carriers and their whole
sections retain the same native decoder.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphSmallWReadoutSubstitution

open CategoryTheory Mettapedia.TypeTheory ContextualWitnessCover
open ContextualSmallFamilyUniverse ContextualSmallFamilyComprehension
open ContextualSmallFamilyTypeFormerCoherence ContextualSmallFamilyWTypes ContextualSmallFamilyWAlgebra
open ContextualSmallFamilyWSubstitution ContextualSmallFamilyWObservedSubstitution
open ContextualGraphDiagrams ContextualRealizedGraphs ContextualGraphSmallWBranchSpan
open ContextualGraphPolynomialReadoutMatching

universe u
variable {D : Type u} [Category.{u} D] {base other : D ⥤ Type u}
variable (change : NaturalHom other base) (domain : base.Elements ⥤ Type u) (body : domain.Elements ⥤ Type u)
variable (domainReading : NaturalHom (total domain) (values D))
variable (positionReading : NaturalHom (total (displayedBody domain body)) (values D))

abbrev newDomain := domainUnder change domain
abbrev newBody := bodyUnder change domain body

theorem displayed_substitution : displayedBody (newDomain change domain) (newBody change domain body) =
    restrict (elementMap (totalChange domain change)) (displayedBody domain body) := by
  refine Functor.hext (fun _ => rfl) ?_
  intro _ _ step
  apply heq_of_eq
  apply congrArg body.map
  apply Subtype.ext
  apply Subtype.ext
  rfl

def domainReadingUnder : NaturalHom (total (newDomain change domain)) (values D) :=
  (totalChange domain change).comp domainReading

def positionReadingUnder : NaturalHom (total (displayedBody (newDomain change domain) (newBody change domain body))) (values D) :=
  ((totalCast (displayed_substitution change domain body)).comp
    (totalChange (displayedBody domain body) (totalChange domain change))).comp positionReading

def original : System D where
  states := total (w domain body)
  branches := branches domain body
  labels := ContextualGraphSmallWReadout.labels domain body domainReading
  arguments := ContextualGraphSmallWReadout.arguments domain body positionReading
  successor := childTarget domain body

def rebuilt : System D := original (newDomain change domain) (newBody change domain body)
  (domainReadingUnder change domain domainReading) (positionReadingUnder change domain body positionReading)

def project : NaturalHom (total (w (newDomain change domain) (newBody change domain body))) (total (w domain body)) :=
  (totalOperation (wSubstitutionInverse change domain body)).comp (totalChange (w domain body) change)

theorem label_inverse (point : other.Elements)
    (tree : (w (newDomain change domain) (newBody change domain body)).obj point) :
    (labelNative (newDomain change domain) (newBody change domain body)).app point tree =
      (labelNative domain body).app ((elementMap change).obj point) ((wComparison change domain body point).symm tree) := by
  have result := label_wComparison change domain body point ((wComparison change domain body point).symm tree)
  exact (congrArg ((labelNative (newDomain change domain) (newBody change domain body)).app point)
    ((wComparison change domain body point).apply_symm_apply tree)).symm.trans result

def castEquivalence {A B : Type u} (same : A = B) : A ≃ B where
  toFun := cast same
  invFun := cast same.symm
  left_inv value := by cases same; rfl
  right_inv value := by cases same; rfl

def branchComparison (point : other.Elements)
    (tree : (w (newDomain change domain) (newBody change domain body)).obj point) :
    body.obj ⟨(elementMap change).obj point,
      (labelNative domain body).app ((elementMap change).obj point) ((wComparison change domain body point).symm tree)⟩ ≃
    (newBody change domain body).obj ⟨point,
      (labelNative (newDomain change domain) (newBody change domain body)).app point tree⟩ :=
  castEquivalence (congrArg (fun label => (newBody change domain body).obj ⟨point, label⟩)
    (label_inverse change domain body point tree).symm)

theorem branch_value (point : other.Elements)
    (tree : (w (newDomain change domain) (newBody change domain body)).obj point)
    (branch : body.obj ⟨(elementMap change).obj point,
      (labelNative domain body).app ((elementMap change).obj point) ((wComparison change domain body point).symm tree)⟩) :
    HEq (branchComparison change domain body point tree branch) branch := ContextualSmallFamilyUniverse.cast_heq _ _

theorem argument_comparison (point : other.Elements)
    (tree : (w (newDomain change domain) (newBody change domain body)).obj point)
    (branch : (branches domain body).obj ⟨point.1, (project change domain body).app point.1 ⟨point.2, tree⟩⟩) :
    (original domain body domainReading positionReading).arguments.app point.1
        ⟨(project change domain body).app point.1 ⟨point.2, tree⟩, branch⟩ =
    (rebuilt change domain body domainReading positionReading).arguments.app point.1
      ⟨⟨point.2, tree⟩, branchComparison change domain body point tree branch⟩ := by
  apply congrArg (positionReading.app point.1)
  apply Sigma.ext
  · exact Sigma.ext rfl (heq_of_eq (label_inverse change domain body point tree).symm)
  · exact (branch_value change domain body point tree branch).symm

theorem child_comparison (point : other.Elements)
    (tree : (w (newDomain change domain) (newBody change domain body)).obj point)
    (branch : (branches domain body).obj ⟨point.1, (project change domain body).app point.1 ⟨point.2, tree⟩⟩) :
    (childTarget domain body).app point.1 ⟨(project change domain body).app point.1 ⟨point.2, tree⟩, branch⟩ =
      (project change domain body).app point.1
        ((childTarget (newDomain change domain) (newBody change domain body)).app point.1
          ⟨⟨point.2, tree⟩, branchComparison change domain body point tree branch⟩) := by
  apply congrArg (Sigma.mk (change.app point.1 point.2))
  let oldTree := (wComparison change domain body point).symm tree
  let property := fun (nextTree : (w (newDomain change domain) (newBody change domain body)).obj point) =>
    ∀ (nextBranch : (newBody change domain body).obj
      ⟨point, (labelNative (newDomain change domain) (newBody change domain body)).app point nextTree⟩),
      HEq branch nextBranch →
        wComparison change domain body point (child domain body ((elementMap change).obj point) oldTree branch) =
          child (newDomain change domain) (newBody change domain body) point nextTree nextBranch
  have observed : property ((wComparison change domain body point) oldTree) :=
    child_wComparison change domain body point oldTree branch
  have transported : property tree := ((wComparison change domain body point).apply_symm_apply tree) ▸ observed
  apply (wComparison change domain body point).injective
  exact (transported (branchComparison change domain body point tree branch)
    (branch_value change domain body point tree branch).symm).trans
      ((wComparison change domain body point).apply_symm_apply
        (child (newDomain change domain) (newBody change domain body) point tree
          (branchComparison change domain body point tree branch))).symm

def matching : Matching (original domain body domainReading positionReading)
    (rebuilt change domain body domainReading positionReading) where
  relation point left right := ULift.{u,0} (PLift (left = (project change domain body).app point right))
  stable := fun {_ _} arrival {_ _} related =>
    ⟨⟨(congrArg ((total (w domain body)).map arrival) related.down.down).trans ((project change domain body).naturality arrival _)⟩⟩
  labels := by
    intro point left right related
    rcases right with ⟨parameter, tree⟩
    rcases related with ⟨⟨same⟩⟩
    subst left
    exact Equal.ofEq (congrArg (fun label => domainReading.app point ⟨change.app point parameter, label⟩)
      (label_inverse change domain body ⟨point, parameter⟩ tree).symm)
  forth := by
    intro point left right related branch
    rcases right with ⟨parameter, tree⟩
    rcases related with ⟨⟨same⟩⟩
    subst left
    exact ⟨branchComparison change domain body ⟨point, parameter⟩ tree branch,
      Equal.ofEq (argument_comparison change domain body domainReading positionReading ⟨point, parameter⟩ tree branch),
      ⟨⟨child_comparison change domain body ⟨point, parameter⟩ tree branch⟩⟩⟩
  back := by
    intro point left right related branch
    rcases right with ⟨parameter, tree⟩
    rcases related with ⟨⟨same⟩⟩
    subst left
    let recovered := (branchComparison change domain body ⟨point, parameter⟩ tree).symm branch
    have roundtrip := (branchComparison change domain body ⟨point, parameter⟩ tree).apply_symm_apply branch
    refine ⟨recovered, ?_, ?_⟩
    · exact Equal.ofEq ((argument_comparison change domain body domainReading positionReading
        ⟨point, parameter⟩ tree recovered).trans
          (congrArg (fun argument => (rebuilt change domain body domainReading positionReading).arguments.app point
            ⟨⟨parameter, tree⟩, argument⟩) roundtrip))
    · exact ⟨⟨(child_comparison change domain body ⟨point, parameter⟩ tree recovered).trans
        (congrArg (fun argument => (project change domain body).app point
          ((childTarget (newDomain change domain) (newBody change domain body)).app point
            ⟨⟨parameter, tree⟩, argument⟩)) roundtrip)⟩⟩

def comparison (point : other.Elements)
    (tree : (w (newDomain change domain) (newBody change domain body)).obj point) :
    Equal ((ContextualGraphSmallWReadout.reading domain body domainReading positionReading).app point.1
      ((project change domain body).app point.1 ⟨point.2, tree⟩))
      ((ContextualGraphSmallWReadout.reading (newDomain change domain) (newBody change domain body)
        (domainReadingUnder change domain domainReading) (positionReadingUnder change domain body positionReading)).app
          point.1 ⟨point.2, tree⟩) :=
  ContextualGraphPolynomialReadoutMatching.comparison (matching change domain body domainReading positionReading) ⟨⟨rfl⟩⟩

def forwardComparison (point : other.Elements) (tree : (w domain body).obj ((elementMap change).obj point)) :
    Equal ((ContextualGraphSmallWReadout.reading domain body domainReading positionReading).app point.1
      ⟨change.app point.1 point.2, tree⟩)
      ((rebuilt change domain body domainReading positionReading).read.app point.1
        ⟨point.2, wComparison change domain body point tree⟩) :=
  (Equal.ofEq (congrArg (fun value => (ContextualGraphSmallWReadout.reading domain body domainReading positionReading).app
    point.1 ⟨change.app point.1 point.2, value⟩) ((wComparison change domain body point).symm_apply_apply tree).symm)).trans
      (comparison change domain body domainReading positionReading point (wComparison change domain body point tree))

def retainedParent : NaturalHom other (values D) :=
  change.comp (ContextualGraphSmallWReadout.carrier domain body domainReading positionReading)

def rebuiltParent : NaturalHom other (values D) :=
  ContextualGraphSmallWReadout.carrier (newDomain change domain) (newBody change domain body)
    (domainReadingUnder change domain domainReading) (positionReadingUnder change domain body positionReading)

def carrierForth (point : other.Elements) (element : Value D point.1)
    (membership : Member element ((retainedParent change domain body domainReading positionReading).app point.1 point.2)) :
    Member element ((rebuiltParent change domain body domainReading positionReading).app point.1 point.2) :=
  let decoded := ContextualGraphFamilyBodyComparison.memberDecode (w domain body)
    (ContextualGraphSmallWReadout.reading domain body domainReading positionReading)
    ((elementMap change).obj point) element membership
  ContextualGraphFamilyBodyComparison.memberIntro (w (newDomain change domain) (newBody change domain body))
    (rebuilt change domain body domainReading positionReading).read point element
    (wComparison change domain body point decoded.1)
    (decoded.2.trans (forwardComparison change domain body domainReading positionReading point decoded.1))

def carrierBack (point : other.Elements) (element : Value D point.1)
    (membership : Member element ((rebuiltParent change domain body domainReading positionReading).app point.1 point.2)) :
    Member element ((retainedParent change domain body domainReading positionReading).app point.1 point.2) :=
  let decoded := ContextualGraphFamilyBodyComparison.memberDecode
    (w (newDomain change domain) (newBody change domain body))
    (rebuilt change domain body domainReading positionReading).read point element membership
  ContextualGraphFamilyBodyComparison.memberIntro (w domain body)
    (ContextualGraphSmallWReadout.reading domain body domainReading positionReading) ((elementMap change).obj point) element
    ((wComparison change domain body point).symm decoded.1)
    (decoded.2.trans (comparison change domain body domainReading positionReading point decoded.1).symm)

/-- The newly formed material carrier agrees with the substituted old
carrier for arbitrary graph members and every future context. -/
def carrierComparison (point : other.Elements) :
    Equal ((retainedParent change domain body domainReading positionReading).app point.1 point.2)
      ((rebuiltParent change domain body domainReading positionReading).app point.1 point.2) :=
  extensionality
    (fun target arrival element membership =>
      Member.transportParent (Equal.ofEq ((rebuiltParent change domain body domainReading positionReading).naturality
        arrival point.2)).symm (carrierForth change domain body domainReading positionReading
          ⟨target, other.map arrival point.2⟩ element (Member.transportParent
            (Equal.ofEq ((retainedParent change domain body domainReading positionReading).naturality arrival point.2)) membership)))
    (fun target arrival element membership =>
      Member.transportParent (Equal.ofEq ((retainedParent change domain body domainReading positionReading).naturality
        arrival point.2)).symm (carrierBack change domain body domainReading positionReading
          ⟨target, other.map arrival point.2⟩ element (Member.transportParent
            (Equal.ofEq ((rebuiltParent change domain body domainReading positionReading).naturality arrival point.2)) membership)))

abbrev retained := ContextualGraphReceiptFamilies.along (retainedParent change domain body domainReading positionReading)
abbrev rebuiltReceipts := ContextualGraphReceiptFamilies.along (rebuiltParent change domain body domainReading positionReading)

def receiptForward : NaturalHom (retained change domain body domainReading positionReading)
    (rebuiltReceipts change domain body domainReading positionReading) :=
  ((NaturalHom.ofNatTrans (restrictNat (elementMap change)
    (ContextualGraphFamilyBodies.toNative (w domain body)
      (ContextualGraphSmallWReadout.reading domain body domainReading positionReading)).toNatTrans)).comp
      (NaturalHom.ofNatTrans (wSubstitution change domain body))).comp
        (ContextualGraphFamilyBodies.toLiteral (w (newDomain change domain) (newBody change domain body))
          (rebuilt change domain body domainReading positionReading).read)

def receiptBackward : NaturalHom (rebuiltReceipts change domain body domainReading positionReading)
    (retained change domain body domainReading positionReading) :=
  ((ContextualGraphFamilyBodies.toNative (w (newDomain change domain) (newBody change domain body))
    (rebuilt change domain body domainReading positionReading).read).comp
      (NaturalHom.ofNatTrans (wSubstitutionInverse change domain body))).comp
        (NaturalHom.ofNatTrans (restrictNat (elementMap change)
          (ContextualGraphFamilyBodies.toLiteral (w domain body)
            (ContextualGraphSmallWReadout.reading domain body domainReading positionReading)).toNatTrans))

theorem receipt_left : (receiptForward change domain body domainReading positionReading).comp
    (receiptBackward change domain body domainReading positionReading) =
      ContextualSmallMapConstructions.identity (retained change domain body domainReading positionReading) := by
  apply NaturalHom.ext
  intro point receipt
  exact (congrArg (ContextualGraphFamilyBodies.encode (w domain body)
      (ContextualGraphSmallWReadout.reading domain body domainReading positionReading) ((elementMap change).obj point))
    ((wComparison change domain body point).symm_apply_apply _)).trans
      (ContextualGraphFamilyBodies.encode_decode (w domain body)
        (ContextualGraphSmallWReadout.reading domain body domainReading positionReading) ((elementMap change).obj point) receipt)

theorem receipt_right : (receiptBackward change domain body domainReading positionReading).comp
    (receiptForward change domain body domainReading positionReading) =
      ContextualSmallMapConstructions.identity (rebuiltReceipts change domain body domainReading positionReading) := by
  apply NaturalHom.ext
  intro point receipt
  exact (congrArg (ContextualGraphFamilyBodies.encode (w (newDomain change domain) (newBody change domain body))
      (rebuilt change domain body domainReading positionReading).read point)
    ((wComparison change domain body point).apply_symm_apply _)).trans
      (ContextualGraphFamilyBodies.encode_decode (w (newDomain change domain) (newBody change domain body))
        (rebuilt change domain body domainReading positionReading).read point receipt)

def sections : (retained change domain body domainReading positionReading).sections ≃
    (rebuiltReceipts change domain body domainReading positionReading).sections where
  toFun := (receiptForward change domain body domainReading positionReading).mapSection
  invFun := (receiptBackward change domain body domainReading positionReading).mapSection
  left_inv terms := by
    apply Subtype.ext
    funext point
    exact congrArg (fun operation => operation.app point (terms.val point))
      (receipt_left change domain body domainReading positionReading)
  right_inv terms := by
    apply Subtype.ext
    funext point
    exact congrArg (fun operation => operation.app point (terms.val point))
      (receipt_right change domain body domainReading positionReading)

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphSmallWReadoutSubstitution
