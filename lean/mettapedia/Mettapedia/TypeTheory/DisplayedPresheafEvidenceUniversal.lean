import Mettapedia.TypeTheory.DisplayedPresheafEvidenceCoherence
import Mettapedia.TypeTheory.PresheafDependentAdjunction

/-!
# Universal target specifications for retained dependent evidence

For a natural map inside a single presheaf category, a source evidence map
into a substituted target family extends uniquely to the dependent sum.
The extension computes on the original certificate, without selecting a
preimage or truncating the fibre. This is different from changing the
indexing category, where dependent products need additional hypotheses.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.DisplayedPresheafEvidenceUniversal

open CategoryTheory
open DisplayedPresheafTransport DisplayedPresheafComprehension
open DisplayedPresheafSlice DisplayedPresheafSliceSubstitution
open DisplayedPresheafEvidenceTransport

universe u
variable {C : Type u} [Category.{u} C]
variable {P Q R : Cᵒᵖ ⥤ Type u}

/-- Evaluate a source evidence map at its supplied source program and emit
the same target index as the program map. -/
def evidenceTotalMap (f : P ⟶ Q) {A : DisplayedFamily P} {B : DisplayedFamily Q}
    (body : A ⟶ reindexDisplayed f B) : totalSpace A ⟶ totalSpace B :=
  totalHom body ≫ totalReindexMap f B

theorem evidenceTotalMap_projection (f : P ⟶ Q)
    {A : DisplayedFamily P} {B : DisplayedFamily Q}
    (body : A ⟶ reindexDisplayed f B) :
    evidenceTotalMap f body ≫ totalProjection B = totalProjection A ≫ f := by
  ext world value
  rfl

/-- Extension to every receipt, including receipts with distinct origins
at the same target program. -/
def descend (f : P ⟶ Q) {A : DisplayedFamily P} {B : DisplayedFamily Q}
    (body : A ⟶ reindexDisplayed f B) : transport f A ⟶ B :=
  fibreHom (X := Over.mk (totalProjection A ≫ f)) (Y := Over.mk (totalProjection B))
    (Over.homMk (evidenceTotalMap f body) (evidenceTotalMap_projection f body)) ≫
    (projectionFibreIso B).inv

def restrict (f : P ⟶ Q) {A : DisplayedFamily P} {B : DisplayedFamily Q}
    (target : transport f A ⟶ B) : A ⟶ reindexDisplayed f B :=
  unit f A ≫ (reindexFunctor f).map target

theorem descend_unit (f : P ⟶ Q) {A : DisplayedFamily P} {B : DisplayedFamily Q}
    (body : A ⟶ reindexDisplayed f B) (point : P.Elements) (evidence : A.obj point) :
    (descend f body).app (f.mapElements.obj point) ((unit f A).app point evidence) =
      body.app point evidence := by
  cases point
  rfl

theorem beta (f : P ⟶ Q) {A : DisplayedFamily P} {B : DisplayedFamily Q}
    (body : A ⟶ reindexDisplayed f B) : restrict f (descend f body) = body := by
  ext point evidence
  exact descend_unit f body point evidence

theorem eta (f : P ⟶ Q) {A : DisplayedFamily P} {B : DisplayedFamily Q}
    (target : transport f A ⟶ B) : descend f (restrict f target) = target := by
  ext point receipt
  rcases point with ⟨world, targetProgram⟩
  rcases receipt with ⟨⟨sourceProgram, evidence⟩, emitted⟩
  change f.app world sourceProgram = targetProgram at emitted
  change P.obj world at sourceProgram
  change A.obj ⟨world, sourceProgram⟩ at evidence
  subst targetProgram
  rfl

/-- Target specification maps and their source implementations correspond
bijectively, with computation on every supplied certificate. -/
def specificationEquiv (f : P ⟶ Q) (A : DisplayedFamily P) (B : DisplayedFamily Q) :
    (transport f A ⟶ B) ≃ (A ⟶ reindexDisplayed f B) where
  toFun := restrict f
  invFun := descend f
  left_inv := eta f
  right_inv := beta f

theorem descend_unique (f : P ⟶ Q) {A : DisplayedFamily P} {B : DisplayedFamily Q}
    (body : A ⟶ reindexDisplayed f B) (target : transport f A ⟶ B)
    (computes : restrict f target = body) : target = descend f body := by
  rw [← computes, eta]

theorem descend_naturality (f : P ⟶ Q)
    {A : DisplayedFamily P} {B D : DisplayedFamily Q}
    (body : A ⟶ reindexDisplayed f B) (changeEvidence : B ⟶ D) :
    descend f (body ≫ (reindexFunctor f).map changeEvidence) =
      descend f body ≫ changeEvidence := by
  ext point receipt
  rcases point with ⟨world, targetProgram⟩
  rcases receipt with ⟨⟨sourceProgram, evidence⟩, emitted⟩
  change f.app world sourceProgram = targetProgram at emitted
  change P.obj world at sourceProgram
  change A.obj ⟨world, sourceProgram⟩ at evidence
  subst targetProgram
  rfl

theorem restrict_naturality_left (f : P ⟶ Q)
    {A D : DisplayedFamily P} {B : DisplayedFamily Q}
    (changeEvidence : A ⟶ D) (target : transport f D ⟶ B) :
    restrict f ((transportFunctor f).map changeEvidence ≫ target) =
      changeEvidence ≫ restrict f target := by
  ext point evidence
  cases point
  rfl

theorem restrict_naturality_right (f : P ⟶ Q)
    {A : DisplayedFamily P} {B D : DisplayedFamily Q}
    (target : transport f A ⟶ B) (changeEvidence : B ⟶ D) :
    restrict f (target ≫ changeEvidence) =
      restrict f target ≫ (reindexFunctor f).map changeEvidence := by
  ext point evidence
  rfl

/-- The computational universal property supplies an adjunction on the
existing family functors, with the explicitly retained unit. -/
def receiptAdjunction (f : P ⟶ Q) : transportFunctor f ⊣ reindexFunctor f :=
  Adjunction.mkOfHomEquiv
    { homEquiv := specificationEquiv f
      homEquiv_naturality_left_symm := by
        intro A D B changeEvidence body
        ext point receipt
        rcases point with ⟨world, targetProgram⟩
        rcases receipt with ⟨⟨sourceProgram, evidence⟩, emitted⟩
        change f.app world sourceProgram = targetProgram at emitted
        change P.obj world at sourceProgram
        change A.obj ⟨world, sourceProgram⟩ at evidence
        subst targetProgram
        rfl
      homEquiv_naturality_right := restrict_naturality_right f }

/-- Descending through two compilation stages agrees with descending
once along their composite, after flattening the retained origins. -/
theorem descend_composition (f : P ⟶ Q) (g : Q ⟶ R)
    {A : DisplayedFamily P} {B : DisplayedFamily R}
    (body : A ⟶ reindexDisplayed (f ≫ g) B) :
    (compositionIso f g A).inv ≫ descend g (descend f body) =
      descend (f ≫ g) body := by
  apply descend_unique
  ext point evidence
  cases point
  rfl

theorem descend_identity {A B : DisplayedFamily P} (body : A ⟶ B) :
    descend (𝟙 P) body = (DisplayedPresheafEvidenceCoherence.identityIso A).hom ≫ body := by
  symm
  apply descend_unique
  ext point evidence
  cases point
  rfl

theorem descend_naturality_left (f : P ⟶ Q)
    {A D : DisplayedFamily P} {B : DisplayedFamily Q}
    (changeEvidence : A ⟶ D) (body : D ⟶ reindexDisplayed f B) :
    descend f (changeEvidence ≫ body) =
      (transportFunctor f).map changeEvidence ≫ descend f body := by
  apply (specificationEquiv f A B).injective
  change restrict f (descend f (changeEvidence ≫ body)) =
    restrict f ((transportFunctor f).map changeEvidence ≫ descend f body)
  rw [beta, restrict_naturality_left, beta]

/-- The source evidence requirement has a solution exactly when the
transported target family has a map into the requested specification. -/
theorem specification_exists_iff (f : P ⟶ Q)
    (A : DisplayedFamily P) (B : DisplayedFamily Q) :
    Nonempty (transport f A ⟶ B) ↔ Nonempty (A ⟶ reindexDisplayed f B) :=
  (specificationEquiv f A B).nonempty_congr

theorem receiptAdjunction_unit (f : P ⟶ Q) (A : DisplayedFamily P) :
    (receiptAdjunction f).unit.app A = unit f A := by
  ext point evidence
  rfl

/-- Both native quantifiers are adjoints to substitution along this
presheaf map. No coverage condition on another context category is needed. -/
noncomputable def familyAdjointTriple (f : P ⟶ Q) :
    (transportFunctor f ⊣ reindexFunctor f) ×
      (reindexFunctor f ⊣ f.mapElements.ran) :=
  ⟨receiptAdjunction f, PresheafDependentAdjunction.familyAdjunction f⟩

end Mettapedia.TypeTheory.DisplayedPresheafEvidenceUniversal
