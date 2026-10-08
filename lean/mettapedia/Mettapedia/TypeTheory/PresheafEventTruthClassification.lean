import Mettapedia.TypeTheory.PresheafScopedEvents
import Mettapedia.TypeTheory.PresheafEventNativeLogic
import Mettapedia.GSLT.Topos.PresheafPredicateGenericTruth

/-!
# Generic truth for scopes and possible-event specifications

The same event comprehension used by native certificates is the inverse
image of the actual sieve-valued generic truth predicate. Its characteristic
map is the name map followed by the scope classifier. Classification uses
the full Cartesian universal property in the actual predicate fibration.
The classifier of an event certificate describes its exact existential
support; it does not select or recover a proof-relevant receipt.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.PresheafEventCertificates.EventSpan

open _root_.CategoryTheory _root_.CategoryTheory.Functor
open Mettapedia.GSLT.Topos
open Mettapedia.GSLT.Topos.PresheafPredicateGenericTruth
open DisplayedPresheafTransport

universe u
variable {C : Type u} [Category.{u} C]
variable {P Q N : Cᵒᵖ ⥤ Type u} (span : EventSpan P Q)

/-- The actual scope comprehension has the composed name/scope classifier. -/
theorem scope_characteristic (name : span.events ⟶ N) (scope : Subfunctor N) :
    chiOfSubfunctor span.events (scope.preimage name) =
      name ≫ chiOfSubfunctor N scope :=
  characteristic_substitution name scope

/-- Taking generic truth along that composite recovers precisely the
admitted event predicate, including all its future-context restrictions. -/
theorem scope_truth_preimage (name : span.events ⟶ N) (scope : Subfunctor N) :
    (truthPredicate C).preimage (name ≫ chiOfSubfunctor N scope) =
      scope.preimage name := by
  rw [← span.scope_characteristic name scope]
  exact characteristic_classifies span.events (scope.preimage name)

/-- Erasure of the actual scoped event comprehension has exactly the
classified range; it cannot add an event outside the supplied scope. -/
theorem scopeErasure_range (name : span.events ⟶ N) (scope : Subfunctor N) :
    Subfunctor.range (span.scopeErasure name scope) = scope.preimage name := by
  ext world event
  constructor
  · rintro ⟨selected, same⟩
    change selected.val = event at same
    exact same ▸ selected.property
  · intro admitted
    exact ⟨⟨event, admitted⟩, rfl⟩

/-- Generic classification is a unique Cartesian arrow for the same
scope predicate that supplied the event comprehension. -/
theorem scope_cartesian_classification (name : span.events ⟶ N) (scope : Subfunctor N) :
    ∃! arrow : totalOfPredicate span.events (scope.preimage name) ⟶ totalTruth C,
      IsStronglyCartesian (presheafPredicateProjection C) arrow.base arrow :=
  unique_cartesian_classification _

theorem scope_classification_base (name : span.events ⟶ N) (scope : Subfunctor N) :
    (classify (totalOfPredicate span.events (scope.preimage name))).base =
      name ≫ chiOfSubfunctor N scope :=
  span.scope_characteristic name scope

/-- Native event evidence and the independently formed existential event
predicate have the same actual sieve-valued characteristic map. -/
theorem certificate_characteristic (A : DisplayedFamily Q) :
    chiOfSubfunctor P (support (span.certificates A)) =
      chiOfSubfunctor P (((support A).preimage span.target).image span.source) := by
  rw [span.support_certificates]

/-- The classified possible-event predicate is precisely native certificate
inhabitation. Full certificates remain in the separate dependent family. -/
theorem certificate_truth_preimage (A : DisplayedFamily Q) :
    (truthPredicate C).preimage
      (chiOfSubfunctor P (((support A).preimage span.target).image span.source)) =
        support (span.certificates A) := by
  rw [← span.certificate_characteristic A]
  exact characteristic_classifies P (support (span.certificates A))

theorem certificate_cartesian_classification (A : DisplayedFamily Q) :
    ∃! arrow : totalOfPredicate P (support (span.certificates A)) ⟶ totalTruth C,
      IsStronglyCartesian (presheafPredicateProjection C) arrow.base arrow :=
  unique_cartesian_classification _

end Mettapedia.TypeTheory.PresheafEventCertificates.EventSpan
