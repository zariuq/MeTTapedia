import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ExecutableBudgetAcceptance
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationAtomicPathControls
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.SourceAssociatedLocatedControls

/-!
# Prices observe execution and do not grant authority

A real two-firing path obeys every prefix of a nonnegative price account.
Assigning a negative price to the second authority makes the initial inventory
look cheaper than the first firing, even though exact physical conservation
still holds. Finally, a zero-priced wrong key remains unable to fund a real
source-associated communication.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ExecutableBudgetControls

open ActivationAtomicPathControls
open ActivationGenerated

def nonnegativePrice (atom : String) : Nat := if atom = "a" then 2 else 3

theorem actual_nonnegative_prefixes : path.PrefixAccepted nonnegativePrice
    (CostSig.additiveFold nonnegativePrice
      (decodeRawConfig (initial.map RawTraceComponent.term)).storedSignatures) := by
  apply path.executable_prefixAccepted_initial_inventory
    (initialTraceComponents_canonical source)
  · apply initialTraceComponents_resourceSeparated
    simp [source, contact, payload, channel, decodeCostTerm, decodeCostProc, decodeCostName,
      CostTerm.components, CostConfig.ResourceSeparated, CostTerm.ResourceSeparated,
      CostTerm.PurseFree, CostTerm.purseInventory, CostName.purseInventory, CostProc.purseInventory]
  · exact fun _ => Nat.zero_le _

def refundPrice (atom : String) : Int :=
  if atom = "a" then 6 else if atom = "b" then -2 else 0

theorem actual_refund_account : path.additiveAccount refundPrice = [6, -2] := by
  decide +kernel

theorem actual_refund_inventory :
    CostSig.additiveFold refundPrice
      (decodeRawConfig (initial.map RawTraceComponent.term)).storedSignatures = 4 := by
  decide +kernel

/-- The real first firing overshoots this refund-valued inventory; the
nonnegative-price hypothesis of the general prefix theorem is essential. -/
theorem negative_price_prefix_rejected :
    ¬ path.PrefixAccepted refundPrice
      (CostSig.additiveFold refundPrice
        (decodeRawConfig (initial.map RawTraceComponent.term)).storedSignatures) := by
  rw [actual_refund_inventory, path.prefixAccepted_iff_orderedAccount, actual_refund_account]
  intro accepted
  have first := accepted 1 (by decide +kernel)
  norm_num [CostPath.OrderedAccount.prefixCost] at first

theorem zero_prices_identify_distinct_authorities :
    CostSig.additiveFold (fun _ : String => (0 : Nat))
      {literalAuthorityKey SourceAssociatedLocatedControls.originalKey} =
    CostSig.additiveFold (fun _ : String => (0 : Nat))
      {literalAuthorityKey ActivationLocatedControls.unitSource} := by
  simp

/-- Equal numerical prices do not make the unit key into the original
program's literal commitment. The actual catalogue remains empty. -/
theorem zero_price_wrong_key_still_blocked :
    runtimeCostCandidatesFromConfig
      [.signed (.par
        (.recv (literalEncodeName ActivationLocatedControls.channel) (.drop (.bvar 0)))
        (.send (literalEncodeName ActivationLocatedControls.channel)
          (literalEncodeTerm ActivationLocatedControls.payload)))
        [literalAuthorityKey SourceAssociatedLocatedControls.originalKey],
       .purse (literalEncodeName ActivationLocatedControls.channel)
         [[literalAuthorityKey ActivationLocatedControls.unitSource]]] = [] :=
  SourceAssociatedLocatedControls.unit_key_cannot_authorize_original

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ExecutableBudgetControls
