import Mettapedia.TypeTheory.MaterialSets.Hypersets.MaterialDisplayedIdentitySiteLift

/-!
# Successor identity controls on the infinite observed material site

The endpoint-dependent motive returns an actual cyclic hyperset payload
through the full raised J operation and its constructed member decoder.
Both endpoints remain in the complete material context label. A distinct
empty-versus-cyclic endpoint pair has no raised material identity witness.
These are controls for the discrete profile, not rules for native identity.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.MaterialDisplayedIdentitySiteLiftControls

open CategoryTheory ContextualGeneratedUniverse
open Mettapedia.TypeTheory

abbrev domain := Growing.input
abbrev original := Growing.context
abbrev context := MaterialDisplayedIdentitySiteLift.identityContext domain
abbrev upperContext := MaterialDisplayedIdentitySiteLift.upperContext domain
abbrev basePoint := Growing.newPoint
abbrev cyclicArgument := Growing.positiveSection.val basePoint

def motive : MaterialFamily context :=
  domain.reindex (other := context) (Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent.compose
    (DisplayedPresheafIdentity.readLeft domain.family) (PowerClassPresheafProducts.projection domain.family))

def method : (PowerClassPresheafProducts.reindex (DisplayedPresheafIdentity.diagonal domain.family) motive.family).sections :=
  DisplayedPresheafIdentity.endpointMethod domain.family

def receipt : context.base.Elements :=
  ⟨basePoint.1, ⟨⟨⟨basePoint.2, cyclicArgument⟩, cyclicArgument⟩, PresheafIdentityWitness.encode rfl⟩⟩

def upperReceipt : upperContext.base.Elements :=
  (PowerClassPresheafProducts.elementMap (DisplayedPresheafIdentitySiteLift.contextTo original.base domain.family)).obj
    ((PresheafSiteLift.elementsUp context.base).obj receipt)

theorem lower_upper_receipt : MaterialDisplayedIdentitySiteLift.lowerPoint domain upperReceipt = receipt := by
  rfl

theorem cyclic_argument : (domain.model basePoint).value cyclicArgument = HSet.quineAtom :=
  Growing.positiveSection_value Growing.newRaw

theorem lower_endpoint_value :
    (motive.model receipt).value ((DisplayedPresheafIdentity.J domain.family motive.family method).val receipt) = HSet.quineAtom := by
  have selected := DisplayedPresheafIdentity.J_endpoint_value domain.family receipt
  exact (congrArg (domain.model basePoint).value selected).trans cyclic_argument

theorem J_returns_cyclic_payload :
    ((MaterialDisplayedIdentitySiteLift.upperMotive domain motive).model upperReceipt).value
      ((MaterialDisplayedIdentitySiteLift.J domain motive method).val upperReceipt) = HSet.lift HSet.quineAtom := by
  exact (MaterialDisplayedIdentitySiteLift.J_value domain motive method upperReceipt).trans
    (congrArg HSet.lift lower_endpoint_value)

theorem decoded_J_returns_endpoint :
    (motive.model receipt).decode
      (MaterialDisplayedIdentitySiteLift.memberEquiv domain motive upperReceipt
        (((MaterialDisplayedIdentitySiteLift.upperMotive domain motive).model upperReceipt).decode.symm
          ((MaterialDisplayedIdentitySiteLift.J domain motive method).val upperReceipt))) = cyclicArgument :=
  (MaterialDisplayedIdentitySiteLift.J_decoder domain motive method upperReceipt).trans
    (DisplayedPresheafIdentity.J_endpoint_value domain.family receipt)

theorem full_upper_context_label : upperContext.labels.reading upperReceipt =
    HSet.kpair (HSet.kpair (HSet.kpair (HSet.lift (original.labels.reading basePoint)) (HSet.lift HSet.quineAtom))
      (HSet.lift HSet.quineAtom)) ∅ := by
  rw [MaterialDisplayedIdentitySiteLift.upper_context_label, lower_upper_receipt,
    MaterialDisplayedIdentitySiteLift.context_label, HSet.lift_kpair, HSet.lift_kpair, HSet.lift_kpair, HSet.lift_empty]
  exact congrArg (fun payload => HSet.kpair
    (HSet.kpair (HSet.kpair (HSet.lift (original.labels.reading basePoint)) (HSet.lift payload)) (HSet.lift payload)) ∅)
    cyclic_argument

theorem raised_distinct_endpoints_empty :
    ¬ Nonempty (PresheafIdentityWitness.Witness
      (ULift.up (Growing.emptySection.val basePoint) : ULift.{1, 0} (domain.family.obj basePoint))
      (ULift.up cyclicArgument)) := by
  rintro ⟨witness⟩
  have endpoints := congrArg ULift.down (PresheafIdentityWitness.decode witness)
  have reading := congrArg (domain.model basePoint).value endpoints
  exact HSet.empty_ne_quineAtom ((Growing.emptySection_value Growing.newRaw).symm.trans (reading.trans cyclic_argument))

theorem diagonal_reflexivity_inhabited : Nonempty (PresheafIdentityWitness.Witness
    (ULift.up cyclicArgument : ULift.{1, 0} (domain.family.obj basePoint)) (ULift.up cyclicArgument)) :=
  ⟨PresheafIdentityWitness.encode rfl⟩

end Mettapedia.TypeTheory.MaterialSets.Hypersets.MaterialDisplayedIdentitySiteLiftControls
