import Mettapedia.TypeTheory.Calculi.NativeDependent.ExternalPresheafCertificates
import Mettapedia.TypeTheory.DisplayedPresheafSliceSubstitution

/-!
# Interface substitution for complete generated native certificates

A natural program map composes with the explicit semantic-variable
interface. The resulting certificates are canonically isomorphic to
pullback of the original certificates. Both directions retain the entire
authored derivation and the checked native value, including dependence on
the interface input. The comparison is natural in program-client arrows.

This is substitution within one presheaf category. It does not assert
that a change of indexing theory preserves native products, or that the
attached certificate is a dependent typing derivation for a guest program.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.ExternalPresheafCertificateSubstitution

open CategoryTheory
open Mettapedia.TypeTheory
open DisplayedPresheafTransport DisplayedPresheafComprehension
open DisplayedPresheafSliceSubstitution
open ExternalPresheafCertificates

universe u
variable {C : Type u} [Category.{u} C]
variable {S : External.Symbols.{u}} {D : External.Signature S}
variable {n : Nat} {context : External.ContextExpr S n}
variable {term : External.TermExpr S n} {type : External.TypeExpr S n}
variable {P Q R : Cᵒᵖ ⥤ Type u}

def reindex (interpretation : Interpretation D context term type P) (f : Q ⟶ P) :
    Interpretation D context term type Q where
  model := interpretation.model
  realization := interpretation.realization
  stable := interpretation.stable
  beta := interpretation.beta
  eta := interpretation.eta
  semanticContext := interpretation.semanticContext
  semanticType := interpretation.semanticType
  contextRead := interpretation.contextRead
  typeRead := interpretation.typeRead
  interface := f ≫ interpretation.interface

variable (interpretation : Interpretation D context term type P) (f : Q ⟶ P)

local instance semanticCategory : Category.{u} interpretation.semanticContext.1.Elements :=
  categoryOfElements (interpretation.semanticContext.1 : Cᵒᵖ ⥤ Type u)

theorem valueFamily_substitution :
    (reindex interpretation f).valueFamily = reindexDisplayed f interpretation.valueFamily :=
  reindexDisplayed_comp interpretation.interface interpretation.decodedFamily f

theorem valueSection_substitution
    (tree : External.Derivation D (.term context term type)) :
    (reindex interpretation f).valueSection tree =
      reindexDisplayedSection f interpretation.valueFamily (interpretation.valueSection tree) :=
  reindexDisplayedSection_comp interpretation.interface interpretation.decodedFamily f
    (interpretation.nativeSection tree)

def forward : (reindex interpretation f).certificates ⟶
    reindexDisplayed f interpretation.certificates where
  app point := TypeCat.ofHom fun certificate =>
    ⟨certificate.tree, certificate.value, certificate.checked⟩
  naturality := by
    intro first second arrow
    apply ConcreteCategory.hom_ext
    intro certificate
    apply Interpretation.Certificate.ext interpretation
    · rfl
    · rfl

def backward : reindexDisplayed f interpretation.certificates ⟶
    (reindex interpretation f).certificates where
  app point := TypeCat.ofHom fun certificate =>
    ⟨certificate.tree, certificate.value, certificate.checked⟩
  naturality := by
    intro first second arrow
    apply ConcreteCategory.hom_ext
    intro certificate
    apply Interpretation.Certificate.ext (reindex interpretation f)
    · rfl
    · rfl

def comparison : (reindex interpretation f).certificates ≅
    reindexDisplayed f interpretation.certificates where
  hom := forward interpretation f
  inv := backward interpretation f
  hom_inv_id := by
    apply NatTrans.ext
    funext point
    apply ConcreteCategory.hom_ext
    intro certificate
    apply Interpretation.Certificate.ext (reindex interpretation f)
    · rfl
    · rfl
  inv_hom_id := by
    apply NatTrans.ext
    funext point
    apply ConcreteCategory.hom_ext
    intro certificate
    apply Interpretation.Certificate.ext interpretation
    · rfl
    · rfl

theorem forward_tree (point : Q.Elements)
    (certificate : (reindex interpretation f).Certificate point) :
    ((comparison interpretation f).hom.app point certificate).tree = certificate.tree := rfl

theorem forward_value (point : Q.Elements)
    (certificate : (reindex interpretation f).Certificate point) :
    ((comparison interpretation f).hom.app point certificate).value = certificate.value := rfl

theorem native_value_substitution (point : Q.Elements)
    (tree : External.Derivation D (.term context term type)) :
    ((reindex interpretation f).valueSection tree).val point =
      (interpretation.nativeSection tree).val
        (interpretation.interface.mapElements.obj (f.mapElements.obj point)) := rfl

theorem tree_readout_square :
    (comparison interpretation f).hom ≫
        (reindexFunctor f).map interpretation.treeReadout =
      (reindex interpretation f).treeReadout := by
  apply NatTrans.ext
  funext point
  rfl

theorem value_readout_square :
    (comparison interpretation f).hom ≫
        (reindexFunctor f).map interpretation.valueReadout =
      (reindex interpretation f).valueReadout := by
  apply NatTrans.ext
  funext point
  rfl

theorem certificateSection_substitution
    (tree : External.Derivation D (.term context term type)) :
    (Functor.sectionsFunctor Q.Elements).map (comparison interpretation f).hom
        ((reindex interpretation f).certificateSection tree) =
      reindexDisplayedSection f interpretation.certificates
        (interpretation.certificateSection tree) := by
  apply Functor.sections_ext_iff.mpr
  intro point
  apply Interpretation.Certificate.ext interpretation
  · rfl
  · rfl

theorem comparison_identity :
    (comparison interpretation (𝟙 P)).hom = 𝟙 interpretation.certificates := by
  apply NatTrans.ext
  funext point
  apply ConcreteCategory.hom_ext
  intro certificate
  apply Interpretation.Certificate.ext interpretation
  · rfl
  · rfl

theorem comparison_composition (g : R ⟶ Q) :
    (comparison interpretation (g ≫ f)).hom =
      (comparison (reindex interpretation f) g).hom ≫
        (reindexFunctor g).map (comparison interpretation f).hom := by
  apply NatTrans.ext
  funext point
  apply ConcreteCategory.hom_ext
  intro certificate
  apply Interpretation.Certificate.ext interpretation
  · rfl
  · rfl

end Mettapedia.TypeTheory.Calculi.NativeDependent.ExternalPresheafCertificateSubstitution
