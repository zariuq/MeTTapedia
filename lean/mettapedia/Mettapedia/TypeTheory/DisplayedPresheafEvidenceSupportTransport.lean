import Mettapedia.TypeTheory.DisplayedPresheafEvidenceUniversal
import Mettapedia.GSLT.Topos.PresheafEvidenceSupport

/-!
# Existential specifications of native evidence transport

Forgetting witnesses after the native sum gives the exact existential
image of their source support. This is the strongest target predicate
entailed by those source certificates, in the precise inverse-image
adjunction sense. Its proof-irrelevant readout still cannot recover the
original certificates or their multiplicity.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.DisplayedPresheafEvidenceSupportTransport

open _root_.CategoryTheory
open DisplayedPresheafTransport DisplayedPresheafEvidenceTransport
open Mettapedia.GSLT.Topos

universe u
variable {C : Type u} [Category.{u} C] {P Q : Cᵒᵖ ⥤ Type u}

theorem support_transport (f : P ⟶ Q) (A : DisplayedFamily P) :
    support (transport f A) = (support A).image f := by
  ext world value
  constructor
  · rintro ⟨receipt⟩
    exact ⟨receipt.val.1, ⟨receipt.val.2⟩, receipt.property⟩
  · rintro ⟨source, ⟨evidence⟩, emitted⟩
    exact ⟨⟨⟨source, evidence⟩, emitted⟩⟩

theorem strongest_predicate (f : P ⟶ Q) (A : DisplayedFamily P) (predicate : Subfunctor Q) :
    support (transport f A) ≤ predicate ↔ support A ≤ predicate.preimage f := by
  rw [support_transport]
  exact Subfunctor.image_le_iff _ _ _

/-- A supported target predicate has a unique proof-irrelevant evidence
readout. The preceding universal family theorem also covers proof-relevant
target families, where this readout need not erase distinctions. -/
def predicateReadout (f : P ⟶ Q) (A : DisplayedFamily P) (predicate : Subfunctor Q)
    (sourceValid : support A ≤ predicate.preimage f) :
    transport f A ⟶ trivialFamily predicate :=
  mapToTrivialFamily (transport f A) predicate
    ((strongest_predicate f A predicate).mpr sourceValid)

theorem predicateReadout_valid (f : P ⟶ Q) (A : DisplayedFamily P)
    (predicate : Subfunctor Q) (sourceValid : support A ≤ predicate.preimage f)
    (point : Q.Elements) (receipt : (transport f A).obj point) :
    point.2 ∈ predicate.obj point.1 :=
  ((predicateReadout f A predicate sourceValid).app point receipt).down.down

theorem predicateReadout_erases_witnesses (f : P ⟶ Q) (A : DisplayedFamily P)
    (predicate : Subfunctor Q) (sourceValid : support A ≤ predicate.preimage f)
    (point : Q.Elements) (first second : (transport f A).obj point) :
    (predicateReadout f A predicate sourceValid).app point first =
      (predicateReadout f A predicate sourceValid).app point second :=
  trivialFamily_subsingleton predicate point.1 point.2 _ _

end Mettapedia.TypeTheory.DisplayedPresheafEvidenceSupportTransport
