import Mettapedia.TypeTheory.DisplayedPresheafEvidenceBaseChange

/-!
# Joint program-and-evidence terms in the native total category

A source evidence map into a substituted target family corresponds
bijectively to a commuting square of the actual presheaf comprehension
projections. Its total map sends the supplied program and certificate
together. Identity and composition agree with the existing arrow category,
so no separate total category of native types is introduced.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.DisplayedPresheafTotalTerms

open _root_.CategoryTheory
open DisplayedPresheafTransport DisplayedPresheafComprehension DisplayedPresheafSlice
open DisplayedPresheafSliceSubstitution DisplayedPresheafEvidenceTransport
open DisplayedPresheafEvidenceUniversal DisplayedPresheafEvidenceBaseChange

universe u
variable {C : Type u} [Category.{u} C] {P Q R : Cᵒᵖ ⥤ Type u}

/-- The paper's joint term judgment is a commuting square over its supplied
base map, rather than an existential statement about evidence support. -/
def homEquiv (f : P ⟶ Q) (A : DisplayedFamily P) (B : DisplayedFamily Q) :
    (A ⟶ reindexDisplayed f B) ≃
      (Over.mk (totalProjection A ≫ f) ⟶ Over.mk (totalProjection B)) :=
  (specificationEquiv f A B).symm.trans
    (((equivalence Q).fullyFaithfulFunctor.homEquiv).trans
      (Iso.homCongr ((transportSliceComparison f).app A) (Iso.refl _)))

theorem homEquiv_left (f : P ⟶ Q) {A : DisplayedFamily P} {B : DisplayedFamily Q}
    (body : A ⟶ reindexDisplayed f B) :
    (homEquiv f A B body).left = evidenceTotalMap f body := by
  ext world value
  rfl

/-- Joint interpretation uses the already maintained native dependent-type
total category: actual presheaf arrows and actual commuting squares. -/
def interpret (f : P ⟶ Q) {A : DisplayedFamily P} {B : DisplayedFamily Q}
    (body : A ⟶ reindexDisplayed f B) :
    Arrow.mk (totalProjection A) ⟶ Arrow.mk (totalProjection B) :=
  Arrow.homMk (evidenceTotalMap f body) f (evidenceTotalMap_projection f body)

theorem interpret_identity (A : DisplayedFamily P) :
    interpret (𝟙 P) (𝟙 A) = 𝟙 (Arrow.mk (totalProjection A)) := by
  apply Arrow.hom_ext
  · ext world value
    rfl
  · rfl

theorem interpret_composition (f : P ⟶ Q) (g : Q ⟶ R)
    {A : DisplayedFamily P} {B : DisplayedFamily Q} {D : DisplayedFamily R}
    (before : A ⟶ reindexDisplayed f B) (after : B ⟶ reindexDisplayed g D) :
    interpret (f ≫ g) (before ≫ (reindexFunctor f).map after) =
      interpret f before ≫ interpret g after := by
  apply Arrow.hom_ext
  · ext world value
    rfl
  · rfl

theorem interpret_supplied_value (f : P ⟶ Q)
    {A : DisplayedFamily P} {B : DisplayedFamily Q}
    (body : A ⟶ reindexDisplayed f B) (point : P.Elements) (evidence : A.obj point) :
    (interpret f body).left.app point.1 ⟨point.2, evidence⟩ =
      (⟨f.app point.1 point.2, body.app point evidence⟩ : (totalSpace B).obj point.1) := rfl

/-- The family-level specification determines the joint square uniquely
at its given base map, and conversely every such square has a unique family
interpretation. This is a semantic hom-set universal property. -/
theorem interpretation_exists_unique (f : P ⟶ Q)
    (A : DisplayedFamily P) (B : DisplayedFamily Q)
    (square : Over.mk (totalProjection A ≫ f) ⟶ Over.mk (totalProjection B)) :
    ∃! body : A ⟶ reindexDisplayed f B, homEquiv f A B body = square := by
  refine ⟨(homEquiv f A B).symm square, (homEquiv f A B).apply_symm_apply square, ?_⟩
  intro body same
  exact (homEquiv f A B).injective
    (same.trans ((homEquiv f A B).apply_symm_apply square).symm)

end Mettapedia.TypeTheory.DisplayedPresheafTotalTerms
