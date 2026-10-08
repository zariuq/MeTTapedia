import Mettapedia.TypeTheory.DisplayedPresheafEvidenceBaseChange
import Mettapedia.TypeTheory.DisplayedPresheafClassifier

/-!
# Dependent certificates for contextual events

An event has natural source and target maps. A certificate for a possible
event retains that event and a witness in the family at its actual target.
The dependent sum is formed over the source map, so distinct occurrences
with the same endpoints remain distinct. Its target readout is natural and
its substitution comparison uses the actual event pullback.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.PresheafEventCertificates

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open DisplayedPresheafTransport DisplayedPresheafComprehension
open DisplayedPresheafSlice DisplayedPresheafSliceSubstitution
open DisplayedPresheafEvidenceTransport DisplayedPresheafEvidenceUniversal

universe u
variable {C : Type u} [Category.{u} C]

/-- An independently supplied contextual family of events with both endpoints. -/
structure EventSpan (P Q : Cᵒᵖ ⥤ Type u) where
  events : Cᵒᵖ ⥤ Type u
  source : events ⟶ P
  target : events ⟶ Q

namespace EventSpan

variable {P Q R : Cᵒᵖ ⥤ Type u} (span : EventSpan P Q)

/-- A possible-event certificate retains its occurrence and target evidence. -/
def certificates (A : DisplayedFamily Q) : DisplayedFamily P :=
  transport span.source (reindexDisplayed span.target A)

/-- The certificate's complete event and evidence, before source indexing. -/
def certificateTotalIso (A : DisplayedFamily Q) :
    totalSpace (span.certificates A) ≅ totalSpace (reindexDisplayed span.target A) :=
  totalIso span.source (reindexDisplayed span.target A)

/-- Forget the postcondition witness, retaining the exact event occurrence. -/
def eventReadout (A : DisplayedFamily Q) :
    totalSpace (span.certificates A) ⟶ span.events :=
  (span.certificateTotalIso A).hom ≫ totalProjection (reindexDisplayed span.target A)

/-- Read the actual endpoint together with its supplied postcondition witness. -/
def resultReadout (A : DisplayedFamily Q) :
    totalSpace (span.certificates A) ⟶ totalSpace A :=
  (span.certificateTotalIso A).hom ≫ totalReindexMap span.target A

theorem eventReadout_source (A : DisplayedFamily Q) :
    span.eventReadout A ≫ span.source = totalProjection (span.certificates A) :=
  totalIso_projection span.source (reindexDisplayed span.target A)

theorem resultReadout_target (A : DisplayedFamily Q) :
    span.resultReadout A ≫ totalProjection A = span.eventReadout A ≫ span.target := by
  simp only [resultReadout, eventReadout, Category.assoc, totalReindexMap_square]

/-- The actual native fibre consists of every source-compatible event and
the witness in the genuinely dependent family at that event's target. -/
def fibreEquiv (A : DisplayedFamily Q) (world : Cᵒᵖ) (program : P.obj world) :
    (span.certificates A).obj ⟨world, program⟩ ≃
      Σ event : { e : span.events.obj world // span.source.app world e = program },
        A.obj ⟨world, span.target.app world event.val⟩ where
  toFun receipt := ⟨⟨receipt.val.1, receipt.property⟩, receipt.val.2⟩
  invFun pair := ⟨⟨pair.1.val, pair.2⟩, pair.1.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Introduction stores a supplied event and its supplied target certificate. -/
def introduce (A : DisplayedFamily Q) (world : Cᵒᵖ)
    (event : span.events.obj world)
    (evidence : A.obj ⟨world, span.target.app world event⟩) :
    (span.certificates A).obj ⟨world, span.source.app world event⟩ :=
  (unit span.source (reindexDisplayed span.target A)).app ⟨world, event⟩ evidence

theorem introduce_event (A : DisplayedFamily Q) (world : Cᵒᵖ)
    (event : span.events.obj world)
    (evidence : A.obj ⟨world, span.target.app world event⟩) :
    (span.eventReadout A).app world
      ⟨span.source.app world event, span.introduce A world event evidence⟩ = event := rfl

theorem introduce_result (A : DisplayedFamily Q) (world : Cᵒᵖ)
    (event : span.events.obj world)
    (evidence : A.obj ⟨world, span.target.app world event⟩) :
    (span.resultReadout A).app world
      ⟨span.source.app world event, span.introduce A world event evidence⟩ =
        ⟨span.target.app world event, evidence⟩ := rfl

/-- The full event-and-evidence total is recovered, so its distinctions
cannot be lost by the source-indexed representation. -/
theorem certificateTotal_injective (A : DisplayedFamily Q) (world : Cᵒᵖ) :
    Function.Injective ((span.certificateTotalIso A).hom.app world) :=
  ((span.certificateTotalIso A).app world).toEquiv.injective

/-- Universal elimination into an independently specified source family. -/
def eliminationEquiv (A : DisplayedFamily Q) (D : DisplayedFamily P) :
    (span.certificates A ⟶ D) ≃
      (reindexDisplayed span.target A ⟶ reindexDisplayed span.source D) :=
  specificationEquiv span.source (reindexDisplayed span.target A) D

def mapPostcondition {A B : DisplayedFamily Q} (change : A ⟶ B) :
    span.certificates A ⟶ span.certificates B :=
  (transportFunctor span.source).map ((reindexFunctor span.target).map change)

theorem mapPostcondition_introduce {A B : DisplayedFamily Q} (change : A ⟶ B)
    (world : Cᵒᵖ) (event : span.events.obj world)
    (evidence : A.obj ⟨world, span.target.app world event⟩) :
    (span.mapPostcondition change).app ⟨world, span.source.app world event⟩
        (span.introduce A world event evidence) =
      span.introduce B world event (change.app ⟨world, span.target.app world event⟩ evidence) :=
  rfl

theorem mapPostcondition_event {A B : DisplayedFamily Q} (change : A ⟶ B) :
    totalHom (span.mapPostcondition change) ≫ span.eventReadout B =
      span.eventReadout A := by
  ext world receipt
  rfl

theorem mapPostcondition_result {A B : DisplayedFamily Q} (change : A ⟶ B) :
    totalHom (span.mapPostcondition change) ≫ span.resultReadout B =
      span.resultReadout A ≫ totalHom change := by
  ext world receipt
  rfl

/-- Restricting the source interface retains the actual compatible events. -/
noncomputable def restrictSource (change : R ⟶ P) : EventSpan R Q where
  events := pullback span.source change
  source := pullback.snd span.source change
  target := pullback.fst span.source change ≫ span.target

/-- Complete possible-event certificates commute with source substitution
through the actual event pullback, naturally in all postcondition maps. -/
noncomputable def sourceSubstitution (change : R ⟶ P) (A : DisplayedFamily Q) :
    (span.restrictSource change).certificates A ≅
      reindexDisplayed change (span.certificates A) :=
  (DisplayedPresheafEvidenceBaseChange.sumBaseChange
    (IsPullback.of_hasPullback span.source change)).app
      (reindexDisplayed span.target A)

end EventSpan

end Mettapedia.TypeTheory.PresheafEventCertificates
