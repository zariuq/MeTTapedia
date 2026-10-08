import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphSmallWBranchSpan
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphPolynomialReadout

/-!
# Material readings of original-small contextual W families

The native W object is built on complete future cones. Its proved
destructor supplies a global natural branch span, from which an actual
labelled graph is constructed. Attaching that graph to every native tree
gives a material carrier with inverse literal decoders on whole sections.
Native folds retain their declared result bodies; their observations do
not automatically descend through material matching of the input trees.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphSmallWReadout

open CategoryTheory Mettapedia.TypeTheory ContextualWitnessCover
open ContextualSmallFamilyUniverse ContextualSmallFamilyWTypes ContextualSmallFamilyWAlgebra
open ContextualGraphDiagrams ContextualRealizedGraphs
open ContextualGraphSmallWBranchSpan

universe u
variable {D : Type u} [Category.{u} D] {base : D ⥤ Type u}
variable (domain : base.Elements ⥤ Type u) (body : domain.Elements ⥤ Type u)
variable (domainReading : NaturalHom (total domain) (values D))
variable (positionReading : NaturalHom (total (displayedBody domain body)) (values D))

noncomputable def labels : NaturalHom (total (w domain body)) (values D) :=
  (labelTarget domain body).comp domainReading

noncomputable def arguments : NaturalHom (total (branches domain body)) (values D) :=
  (argumentTarget domain body).comp positionReading

noncomputable def reading : NaturalHom (total (w domain body)) (values D) :=
  ContextualGraphPolynomialReadoutNodes.reading (branches domain body)
    (labels domain body domainReading) (arguments domain body positionReading) (childTarget domain body)

noncomputable def branchReading : NaturalHom (total (branches domain body)) (values D) :=
  ContextualGraphPolynomialReadout.branchReading (branches domain body)
    (labels domain body domainReading) (arguments domain body positionReading) (childTarget domain body)

noncomputable def branchCollection : NaturalHom (total (w domain body)) (values D) :=
  ContextualGraphPolynomialReadout.collectionReading (branches domain body)
    (labels domain body domainReading) (arguments domain body positionReading) (childTarget domain body)

noncomputable def carrier : NaturalHom base (values D) :=
  ContextualGraphFamilyBodies.parent (w domain body) (reading domain body domainReading positionReading)

noncomputable def literal : base.Elements ⥤ Type u :=
  ContextualGraphFamilyBodies.literal (w domain body) (reading domain body domainReading positionReading)

noncomputable def sectionDecoder : (literal domain body domainReading positionReading).sections ≃
    (w domain body).sections :=
  ContextualGraphFamilyBodies.sectionDecoder (w domain body) (reading domain body domainReading positionReading)

noncomputable def unfold (point : base.Elements) (tree : (w domain body).obj point) :
    Equal ((reading domain body domainReading positionReading).app point.1 ⟨point.2, tree⟩)
      (ContextualGraphOrderedPairs.orderedPair
        (domainReading.app point.1 ⟨point.2, (labelNative domain body).app point tree⟩)
        ((branchCollection domain body domainReading positionReading).app point.1 ⟨point.2, tree⟩)) :=
  ContextualGraphPolynomialReadout.unfold (branches domain body)
    (labels domain body domainReading) (arguments domain body positionReading) (childTarget domain body) ⟨point.2, tree⟩

theorem constructor_label (point : base.Elements)
    (node : ContextualSmallFamilyWPolynomial.At domain body (w domain body) point) :
    (labelNative domain body).app point (constructorValue domain body point node) =
      ContextualSmallFamilyWObservation.rootLabel domain body (w domain body) point node :=
  congrArg (ContextualSmallFamilyWObservation.rootLabel domain body (w domain body) point)
    (destructor_constructor domain body point node)

noncomputable def constructorComparison (point : base.Elements)
    (node : ContextualSmallFamilyWPolynomial.At domain body (w domain body) point) :
    Equal ((reading domain body domainReading positionReading).app point.1
      ⟨point.2, constructorValue domain body point node⟩)
      (ContextualGraphOrderedPairs.orderedPair
        (domainReading.app point.1 ⟨point.2, ContextualSmallFamilyWObservation.rootLabel domain body (w domain body) point node⟩)
        ((branchCollection domain body domainReading positionReading).app point.1
          ⟨point.2, constructorValue domain body point node⟩)) :=
  (unfold domain body domainReading positionReading point (constructorValue domain body point node)).trans
    (ContextualGraphOrderedPairs.orderedPairCongr
      (Equal.ofEq (congrArg (fun label => domainReading.app point.1 ⟨point.2, label⟩)
        (constructor_label domain body point node))) (Equal.refl _))

noncomputable def memberDecode (point : base.Elements) (element : Value D point.1)
    (membership : Member element ((carrier domain body domainReading positionReading).app point.1 point.2)) :
    Σ tree : (w domain body).obj point,
      Equal element ((reading domain body domainReading positionReading).app point.1 ⟨point.2, tree⟩) :=
  ContextualGraphFamilyBodyComparison.memberDecode (w domain body)
    (reading domain body domainReading positionReading) point element membership

noncomputable def sectionComparison
    (terms : (literal domain body domainReading positionReading).sections) (point : base.Elements) :
    Equal ((reading domain body domainReading positionReading).app point.1
      ⟨point.2, (sectionDecoder domain body domainReading positionReading terms).val point⟩)
      ((ContextualGraphReceiptFamilies.sectionReading
        (carrier domain body domainReading positionReading) terms).app point.1 point.2) :=
  ContextualGraphFamilyBodyComparison.sectionComparison (w domain body)
    (reading domain body domainReading positionReading) terms point

section Fold
variable {target : base.Elements ⥤ Type u}
variable (algebra : Algebra domain body (target := target))
variable (targetReading : NaturalHom (total target) (values D))

noncomputable def receiptFold : NaturalHom (literal domain body domainReading positionReading)
    (ContextualGraphFamilyBodies.literal target targetReading) :=
  ((ContextualGraphFamilyBodies.toNative (w domain body) (reading domain body domainReading positionReading)).comp
    (NaturalHom.ofNatTrans (ContextualSmallFamilyWRecursion.foldMap domain body algebra))).comp
      (ContextualGraphFamilyBodies.toLiteral target targetReading)

/-- This is a square of whole natural families, hence preserves every
future argument of a section, not only its current root. -/
theorem receiptFold_native_whole :
    (receiptFold domain body domainReading positionReading algebra targetReading).comp
      (ContextualGraphFamilyBodies.toNative target targetReading) =
    (ContextualGraphFamilyBodies.toNative (w domain body) (reading domain body domainReading positionReading)).comp
      (NaturalHom.ofNatTrans (ContextualSmallFamilyWRecursion.foldMap domain body algebra)) := by
  apply NaturalHom.ext
  intro point receipt
  rfl

theorem receiptFold_sections (terms : (literal domain body domainReading positionReading).sections) :
    ContextualGraphFamilyBodies.sectionDecoder target targetReading
      ((receiptFold domain body domainReading positionReading algebra targetReading).mapSection terms) =
    (NaturalHom.ofNatTrans (ContextualSmallFamilyWRecursion.foldMap domain body algebra)).mapSection
      (sectionDecoder domain body domainReading positionReading terms) := by
  apply Subtype.ext
  funext point
  rfl

theorem folded_constructor (point : base.Elements)
    (node : ContextualSmallFamilyWPolynomial.At domain body (w domain body) point) :
    targetReading.app point.1 ⟨point.2, foldValue domain body algebra point (constructorValue domain body point node)⟩ =
      targetReading.app point.1 ⟨point.2, algebra.app point
        (ContextualSmallFamilyWAction.mapValue domain body
          (ContextualSmallFamilyWRecursion.foldMap domain body algebra) point node)⟩ :=
  congrArg (fun result => targetReading.app point.1 ⟨point.2, result⟩)
    (ContextualSmallFamilyWInitiality.fold_beta domain body algebra point node)

noncomputable def receiptFold_material
    (terms : (literal domain body domainReading positionReading).sections) (point : base.Elements) :
    Equal (targetReading.app point.1 ⟨point.2, foldValue domain body algebra point
      ((sectionDecoder domain body domainReading positionReading terms).val point)⟩)
      ((ContextualGraphReceiptFamilies.sectionReading (ContextualGraphFamilyBodies.parent target targetReading)
        ((receiptFold domain body domainReading positionReading algebra targetReading).mapSection terms)).app point.1 point.2) :=
  ContextualGraphFamilyBodyComparison.sectionComparison target targetReading
    ((receiptFold domain body domainReading positionReading algebra targetReading).mapSection terms) point

end Fold

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphSmallWReadout
