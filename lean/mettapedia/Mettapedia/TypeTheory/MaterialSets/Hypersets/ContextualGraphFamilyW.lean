import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphFamilySubstitution
import Mettapedia.TypeTheory.ContextualSmallFamilyWSubstitutionCoherence

/-!
# Full contextual W recursion through actual graph receipt families

Both the constructed hereditary future trees and their complete polynomial
nodes are represented in the same contextual graph universe. Constructor,
fold and the polynomial action are natural receipt maps. Their initiality
and parameter substitution laws retain all future branches.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphFamilyW

open CategoryTheory Mettapedia.TypeTheory ContextualWitnessCover
open ContextualSmallFamilyUniverse ContextualSmallFamilyWTypes ContextualSmallFamilyWAlgebra
open ContextualGraphFamilyRepresentation ContextualGraphFamilySubstitution

universe u
variable {D : Type u} [Category.{u} D] {base : D ⥤ Type u}
variable (domain : base.Elements ⥤ Type u) (body : domain.Elements ⥤ Type u)
variable {target : base.Elements ⥤ Type u}

noncomputable def receiptConstructor :
    NaturalHom (literal (ContextualSmallFamilyWPolynomial.polynomial domain body (w domain body)))
      (literal (w domain body)) :=
  consumer _ (NaturalHom.ofNatTrans (ContextualSmallFamilyWConstructor.constructor domain body))

def receiptAlgebra (algebra : Algebra domain body (target := target)) :
    NaturalHom (literal (ContextualSmallFamilyWPolynomial.polynomial domain body target)) (literal target) :=
  consumer _ (NaturalHom.ofNatTrans algebra)

noncomputable def receiptPolynomialAction (candidate : NaturalHom (literal (w domain body)) (literal target)) :
    NaturalHom (literal (ContextualSmallFamilyWPolynomial.polynomial domain body (w domain body)))
      (literal (ContextualSmallFamilyWPolynomial.polynomial domain body target)) :=
  consumer _ (NaturalHom.ofNatTrans (ContextualSmallFamilyWAction.map domain body
    ((homDecoder (w domain body) target candidate).toNatTrans)))

noncomputable def receiptFold (algebra : Algebra domain body (target := target)) :
    NaturalHom (literal (w domain body)) (literal target) :=
  consumer _ (NaturalHom.ofNatTrans (ContextualSmallFamilyWRecursion.foldMap domain body algebra))

theorem receiptFold_native (algebra : Algebra domain body (target := target))
    (point : base.Elements) (tree : (literal (w domain body)).obj point) :
    decode target point ((receiptFold domain body algebra).app point tree) =
      ContextualSmallFamilyWAlgebra.foldValue domain body algebra point (decode (w domain body) point tree) := rfl

theorem receiptFold_beta (algebra : Algebra domain body (target := target)) :
    (receiptConstructor domain body).comp (receiptFold domain body algebra) =
      (receiptPolynomialAction domain body (receiptFold domain body algebra)).comp (receiptAlgebra domain body algebra) := by
  apply NaturalHom.ext
  intro point node
  apply (decoder target point).injective
  exact ContextualSmallFamilyWInitiality.fold_beta domain body algebra point
    (decode (ContextualSmallFamilyWPolynomial.polynomial domain body (w domain body)) point node)

/-- Uniqueness ranges over every natural map of literal receipt families,
not merely maps first presented as native folds. -/
theorem receiptFold_unique (algebra : Algebra domain body (target := target))
    (candidate : NaturalHom (literal (w domain body)) (literal target))
    (constructorLaw : (receiptConstructor domain body).comp candidate =
      (receiptPolynomialAction domain body candidate).comp (receiptAlgebra domain body algebra)) :
    candidate = receiptFold domain body algebra := by
  have nativeLaw : ∀ (point : base.Elements)
      (node : ContextualSmallFamilyWPolynomial.At domain body (w domain body) point),
      ((homDecoder (w domain body) target candidate).toNatTrans).app point (constructorValue domain body point node) =
        algebra.app point (ContextualSmallFamilyWAction.mapValue domain body
          ((homDecoder (w domain body) target candidate).toNatTrans) point node) := by
    intro point node
    exact congrArg (fun operation => decode target point (operation.app point
      (encode (ContextualSmallFamilyWPolynomial.polynomial domain body (w domain body)) point node))) constructorLaw
  have unique := ContextualSmallFamilyWInitiality.fold_unique domain body algebra
    ((homDecoder (w domain body) target candidate).toNatTrans) nativeLaw
  apply (homDecoder (w domain body) target).injective
  apply NaturalHom.ext
  intro point tree
  exact congrArg (fun operation => operation.app point tree) unique

theorem receipt_initiality (algebra : Algebra domain body (target := target)) :
    ∃! candidate : NaturalHom (literal (w domain body)) (literal target),
      (receiptConstructor domain body).comp candidate =
        (receiptPolynomialAction domain body candidate).comp (receiptAlgebra domain body algebra) :=
  ⟨receiptFold domain body algebra, receiptFold_beta domain body algebra,
    fun candidate law => receiptFold_unique domain body algebra candidate law⟩

theorem receiptFold_sections (algebra : Algebra domain body (target := target))
    (term : (literal (w domain body)).sections) :
    sectionDecoder target ((receiptFold domain body algebra).mapSection term) =
      (NaturalHom.ofNatTrans (ContextualSmallFamilyWRecursion.foldMap domain body algebra)).mapSection
        (sectionDecoder (w domain body) term) := by
  apply Subtype.ext
  funext point
  rfl

section Substitution
open ContextualSmallFamilyTypeFormerCoherence ContextualSmallFamilyWSubstitution
variable {other : D ⥤ Type u} (change : NaturalHom other base)

noncomputable def treeComparison :
    NaturalHom (literal (nativeUnder (w domain body) change))
      (literal (w (domainUnder change domain) (bodyUnder change domain body))) :=
  consumer _ (NaturalHom.ofNatTrans (wSubstitution change domain body))

noncomputable def restrictedFold (algebra : Algebra domain body (target := target)) :
    NaturalHom (literal (nativeUnder (w domain body) change)) (literal (nativeUnder target change)) :=
  consumer _ (NaturalHom.ofNatTrans (restrictNat (elementMap change)
    (ContextualSmallFamilyWRecursion.foldMap domain body algebra)))

theorem receiptFold_substitution (algebra : Algebra domain body (target := target)) :
    restrictedFold domain body change algebra =
      (treeComparison domain body change).comp
        (receiptFold (domainUnder change domain) (bodyUnder change domain body)
          (ContextualSmallFamilyWSubstitutionCoherence.substitutedAlgebra change domain body algebra)) := by
  apply NaturalHom.ext
  intro point receipt
  apply (decoder (nativeUnder target change) point).injective
  exact ContextualSmallFamilyWSubstitutionCoherence.fold_substitution change domain body algebra point
    (decode (nativeUnder (w domain body) change) point receipt)

end Substitution

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphFamilyW
