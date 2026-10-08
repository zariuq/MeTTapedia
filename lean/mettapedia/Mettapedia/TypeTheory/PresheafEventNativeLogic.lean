import Mettapedia.TypeTheory.PresheafEventCertificates
import Mettapedia.TypeTheory.DisplayedPresheafEvidenceSupportTransport
import Mettapedia.TypeTheory.PresheafDependentAdjunction
import Mettapedia.GSLT.Topos.PresheafEventModalities

/-!
# Native dependent logic of contextual events

The possible-event functor is the actual dependent sum along the source
after substitution along the target. Its right adjoint is the dependent
product along the target after source substitution. Predicate support of
the sum agrees with the existing event diamond. The native construction
retains the full occurrence and certificate which that predicate forgets.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.PresheafEventCertificates

open _root_.CategoryTheory
open DisplayedPresheafTransport DisplayedPresheafComprehension
open DisplayedPresheafSliceSubstitution DisplayedPresheafEvidenceTransport
open DisplayedPresheafEvidenceUniversal
open Mettapedia.GSLT.Topos

universe u
variable {C : Type u} [Category.{u} C]
variable {P Q : Cᵒᵖ ⥤ Type u}

namespace EventSpan

variable (span : EventSpan P Q)

/-- The proof-retaining may-event action on independent postcondition maps. -/
def possibleFunctor : DisplayedFamily Q ⥤ DisplayedFamily P :=
  reindexFunctor span.target ⋙ transportFunctor span.source

/-- The incoming-event right adjoint retains a complete natural function
over every future event argument. It is not a pointwise Boolean box. -/
noncomputable def pastFunctor : DisplayedFamily P ⥤ DisplayedFamily Q :=
  reindexFunctor span.source ⋙ span.target.mapElements.ran

/-- The dependent event adjunction uses the same chosen sums and products. -/
noncomputable def eventAdjunction : span.possibleFunctor ⊣ span.pastFunctor :=
  (PresheafDependentAdjunction.familyAdjunction span.target).comp
    (receiptAdjunction span.source)

/-- Natural event-certificate implementations and natural dependent
incoming-event specifications correspond, with their complete evidence. -/
noncomputable def eventHomEquiv (A : DisplayedFamily Q) (D : DisplayedFamily P) :
    (span.certificates A ⟶ D) ≃ (A ⟶ span.pastFunctor.obj D) :=
  (span.eventAdjunction).homEquiv A D

theorem eventHomEquiv_beta (A : DisplayedFamily Q) (D : DisplayedFamily P)
    (implementation : span.certificates A ⟶ D) :
    (span.eventHomEquiv A D).symm (span.eventHomEquiv A D implementation) = implementation :=
  (span.eventHomEquiv A D).symm_apply_apply implementation

theorem eventHomEquiv_eta (A : DisplayedFamily Q) (D : DisplayedFamily P)
    (specification : A ⟶ span.pastFunctor.obj D) :
    span.eventHomEquiv A D ((span.eventHomEquiv A D).symm specification) = specification :=
  (span.eventHomEquiv A D).apply_symm_apply specification

/-- Existential event support is the source image of target support. -/
theorem support_certificates (A : DisplayedFamily Q) :
    support (span.certificates A) = ((support A).preimage span.target).image span.source := by
  rw [certificates, DisplayedPresheafEvidenceSupportTransport.support_transport,
    reindexDisplayed, support_reindex]

/-- Introduction and context substitution commute on the full receipt. -/
theorem introduce_reindex_total (A : DisplayedFamily Q) {U V : Cᵒᵖ}
    (arrow : U ⟶ V) (event : span.events.obj U)
    (evidence : A.obj ⟨U, span.target.app U event⟩) :
    (totalSpace (span.certificates A)).map arrow
        ⟨span.source.app U event, span.introduce A U event evidence⟩ =
      (span.certificateTotalIso A).inv.app V
        ((totalSpace (reindexDisplayed span.target A)).map arrow ⟨event, evidence⟩) :=
  (NatTrans.naturality_apply (span.certificateTotalIso A).inv arrow ⟨event, evidence⟩).symm

theorem eventReadout_reindex (A : DisplayedFamily Q) {U V : Cᵒᵖ}
    (arrow : U ⟶ V) (receipt : (totalSpace (span.certificates A)).obj U) :
    (span.eventReadout A).app V ((totalSpace (span.certificates A)).map arrow receipt) =
      span.events.map arrow ((span.eventReadout A).app U receipt) :=
  NatTrans.naturality_apply (span.eventReadout A) arrow receipt

theorem resultReadout_reindex (A : DisplayedFamily Q) {U V : Cᵒᵖ}
    (arrow : U ⟶ V) (receipt : (totalSpace (span.certificates A)).obj U) :
    (span.resultReadout A).app V ((totalSpace (span.certificates A)).map arrow receipt) =
      (totalSpace A).map arrow ((span.resultReadout A).app U receipt) :=
  NatTrans.naturality_apply (span.resultReadout A) arrow receipt

variable (same : EventSpan P P)

/-- The existing event-graph interpretation of a span of endo-events. -/
def eventGraph : ConstructivePresheaf.EventGraph Cᵒᵖ where
  vertex := P
  edge := same.events
  source := same.source
  target := same.target

/-- The native evidence construction interprets the independently defined
internal event diamond, with no change in the observation predicate. -/
theorem support_eq_eventDiamond (A : DisplayedFamily P) :
    support (same.certificates A) =
      PresheafEventModalities.diamond same.eventGraph (support A) := by
  rw [same.support_certificates]
  ext world program
  rfl

end EventSpan

end Mettapedia.TypeTheory.PresheafEventCertificates
