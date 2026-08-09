import Mettapedia.MachineLearning.NeuralNetworks.LocalLearning.WeightedGSLTCausalCredit

/-!
# Commuting independent causal-credit redemptions

The explicit receipt, signal, and credit slots expose a precise independence
criterion.  Two redemption effects commute when all three pairs of slots are
distinct.  This is a local diamond theorem: independent causal-credit rewrites
have the same joint successor in either order.

The theorem is intentionally about state, not merely derived weights.  Receipt
consumption, signal consumption, and credit reassignment all commute together.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.LocalLearning
namespace WeightedGSLTCausalCreditConcurrency

open WeightedGSLTConservedCredit
open WeightedGSLTCausalCredit

/-- The total state effect of an already-certified redemption.  Enabling is
kept separate so the algebra of independent effects can be stated directly. -/
def redemptionEffect {Synapse Neuron : Type*}
    {receiptSlots signalSlots creditBudget : ℕ}
    [DecidableEq Synapse] [DecidableEq Neuron]
    (state : CausalCreditState Synapse Neuron receiptSlots signalSlots creditBudget)
    (receiptSlot : Fin receiptSlots) (signalSlot : Fin signalSlots)
    (creditSlot : Fin creditBudget) (synapse : Synapse) :
    CausalCreditState Synapse Neuron receiptSlots signalSlots creditBudget :=
  consumeSignal
    (replaceCore state
      (assignCredit (consumeReceipt state.core receiptSlot)
        creditSlot (.synapse synapse)))
    signalSlot

/-- The exact success equation for one enabled redemption. -/
theorem causalIntegratedStep_redeem_eq_effect {Synapse Neuron : Type*}
    {receiptSlots signalSlots creditBudget : ℕ}
    [DecidableEq Synapse] [DecidableEq Neuron]
    (post : Synapse → Neuron)
    (state : CausalCreditState Synapse Neuron receiptSlots signalSlots creditBudget)
    (receiptSlot : Fin receiptSlots) (signalSlot : Fin signalSlots)
    (creditSlot : Fin creditBudget) (synapse : Synapse)
    (hreceipt : state.core.receipts receiptSlot = some synapse)
    (hsignal : state.signals signalSlot = some (post synapse))
    (hlocal : LocalDonor post synapse (state.core.allocation creditSlot))
    (hmove : state.core.allocation creditSlot ≠ .synapse synapse) :
    causalIntegratedStep post state
      (.redeem receiptSlot signalSlot creditSlot synapse) =
        some (redemptionEffect state receiptSlot signalSlot creditSlot synapse) := by
  simp [causalIntegratedStep, integratedStep, hreceipt, hsignal, hlocal, hmove,
    redemptionEffect, consumeSignal, replaceCore, assignCredit, consumeReceipt]

/-- Slotwise independence: all resources used by the two redemptions are
distinct. -/
structure IndependentSlots {receiptSlots signalSlots creditBudget : ℕ}
    (firstReceipt secondReceipt : Fin receiptSlots)
    (firstSignal secondSignal : Fin signalSlots)
    (firstCredit secondCredit : Fin creditBudget) : Prop where
  receipts : firstReceipt ≠ secondReceipt
  signals : firstSignal ≠ secondSignal
  credits : firstCredit ≠ secondCredit

/-- Independent redemption effects commute on the complete state. -/
theorem redemptionEffect_commutes {Synapse Neuron : Type*}
    {receiptSlots signalSlots creditBudget : ℕ}
    [DecidableEq Synapse] [DecidableEq Neuron]
    (state : CausalCreditState Synapse Neuron receiptSlots signalSlots creditBudget)
    (firstReceipt secondReceipt : Fin receiptSlots)
    (firstSignal secondSignal : Fin signalSlots)
    (firstCredit secondCredit : Fin creditBudget)
    (firstSynapse secondSynapse : Synapse)
    (hindependent : IndependentSlots firstReceipt secondReceipt
      firstSignal secondSignal firstCredit secondCredit) :
    redemptionEffect
        (redemptionEffect state firstReceipt firstSignal firstCredit firstSynapse)
        secondReceipt secondSignal secondCredit secondSynapse =
      redemptionEffect
        (redemptionEffect state secondReceipt secondSignal secondCredit secondSynapse)
        firstReceipt firstSignal firstCredit firstSynapse := by
  rcases hindependent with ⟨hreceipt, hsignal, hcredit⟩
  cases state with
  | mk core signals =>
      cases core with
      | mk receipts allocation =>
          apply congrArg₂ CausalCreditState.mk
          · apply congrArg₂ CreditState.mk
            · exact Function.update_comm hreceipt none none receipts
            · exact Function.update_comm hcredit
                (CreditAccount.synapse firstSynapse)
                (CreditAccount.synapse secondSynapse) allocation
          · exact Function.update_comm hsignal none none signals

/-- The first independent effect leaves every enabling resource of the second
redemption unchanged. -/
theorem redemptionEffect_preserves_independent_enabling {Synapse Neuron : Type*}
    {receiptSlots signalSlots creditBudget : ℕ}
    [DecidableEq Synapse] [DecidableEq Neuron]
    (state : CausalCreditState Synapse Neuron receiptSlots signalSlots creditBudget)
    (firstReceipt secondReceipt : Fin receiptSlots)
    (firstSignal secondSignal : Fin signalSlots)
    (firstCredit secondCredit : Fin creditBudget)
    (firstSynapse : Synapse)
    (hindependent : IndependentSlots firstReceipt secondReceipt
      firstSignal secondSignal firstCredit secondCredit) :
    let afterFirst := redemptionEffect state firstReceipt firstSignal firstCredit firstSynapse
    afterFirst.core.receipts secondReceipt = state.core.receipts secondReceipt ∧
      afterFirst.signals secondSignal = state.signals secondSignal ∧
      afterFirst.core.allocation secondCredit = state.core.allocation secondCredit := by
  rcases hindependent with ⟨hreceipt, hsignal, hcredit⟩
  simp [redemptionEffect, consumeSignal, replaceCore, assignCredit, consumeReceipt,
    Function.update_of_ne hreceipt.symm, Function.update_of_ne hsignal.symm,
    Function.update_of_ne hcredit.symm]

/-- Operational diamond: two enabled independent redemption transitions reach
the same state in either order. -/
theorem independent_redemptions_form_diamond {Synapse Neuron : Type*}
    {receiptSlots signalSlots creditBudget : ℕ}
    [DecidableEq Synapse] [DecidableEq Neuron]
    (post : Synapse → Neuron)
    (state : CausalCreditState Synapse Neuron receiptSlots signalSlots creditBudget)
    (firstReceipt secondReceipt : Fin receiptSlots)
    (firstSignal secondSignal : Fin signalSlots)
    (firstCredit secondCredit : Fin creditBudget)
    (firstSynapse secondSynapse : Synapse)
    (hindependent : IndependentSlots firstReceipt secondReceipt
      firstSignal secondSignal firstCredit secondCredit)
    (hfirstReceipt : state.core.receipts firstReceipt = some firstSynapse)
    (hsecondReceipt : state.core.receipts secondReceipt = some secondSynapse)
    (hfirstSignal : state.signals firstSignal = some (post firstSynapse))
    (hsecondSignal : state.signals secondSignal = some (post secondSynapse))
    (hfirstLocal : LocalDonor post firstSynapse (state.core.allocation firstCredit))
    (hsecondLocal : LocalDonor post secondSynapse (state.core.allocation secondCredit))
    (hfirstMove : state.core.allocation firstCredit ≠ .synapse firstSynapse)
    (hsecondMove : state.core.allocation secondCredit ≠ .synapse secondSynapse) :
    causalRun post state
        [ .redeem firstReceipt firstSignal firstCredit firstSynapse
        , .redeem secondReceipt secondSignal secondCredit secondSynapse ] =
      causalRun post state
        [ .redeem secondReceipt secondSignal secondCredit secondSynapse
        , .redeem firstReceipt firstSignal firstCredit firstSynapse ] := by
  have hfirst := causalIntegratedStep_redeem_eq_effect post state
    firstReceipt firstSignal firstCredit firstSynapse
    hfirstReceipt hfirstSignal hfirstLocal hfirstMove
  have hsecond := causalIntegratedStep_redeem_eq_effect post state
    secondReceipt secondSignal secondCredit secondSynapse
    hsecondReceipt hsecondSignal hsecondLocal hsecondMove
  rcases redemptionEffect_preserves_independent_enabling state
    firstReceipt secondReceipt firstSignal secondSignal firstCredit secondCredit
    firstSynapse hindependent with
    ⟨hsecondReceiptAfter, hsecondSignalAfter, hsecondCreditAfter⟩
  have hsecondAfterFirst := causalIntegratedStep_redeem_eq_effect post
    (redemptionEffect state firstReceipt firstSignal firstCredit firstSynapse)
    secondReceipt secondSignal secondCredit secondSynapse
    (hsecondReceiptAfter.trans hsecondReceipt)
    (hsecondSignalAfter.trans hsecondSignal)
    (by rw [hsecondCreditAfter]; exact hsecondLocal)
    (by rw [hsecondCreditAfter]; exact hsecondMove)
  rcases redemptionEffect_preserves_independent_enabling state
    secondReceipt firstReceipt secondSignal firstSignal secondCredit firstCredit
    secondSynapse
    ⟨hindependent.receipts.symm, hindependent.signals.symm,
      hindependent.credits.symm⟩ with
    ⟨hfirstReceiptAfter, hfirstSignalAfter, hfirstCreditAfter⟩
  have hfirstAfterSecond := causalIntegratedStep_redeem_eq_effect post
    (redemptionEffect state secondReceipt secondSignal secondCredit secondSynapse)
    firstReceipt firstSignal firstCredit firstSynapse
    (hfirstReceiptAfter.trans hfirstReceipt)
    (hfirstSignalAfter.trans hfirstSignal)
    (by rw [hfirstCreditAfter]; exact hfirstLocal)
    (by rw [hfirstCreditAfter]; exact hfirstMove)
  simp [causalRun, hfirst, hsecond, hsecondAfterFirst, hfirstAfterSecond,
    redemptionEffect_commutes state firstReceipt secondReceipt firstSignal secondSignal
      firstCredit secondCredit firstSynapse secondSynapse hindependent]

#print axioms redemptionEffect_commutes
#print axioms redemptionEffect_preserves_independent_enabling
#print axioms independent_redemptions_form_diamond

end WeightedGSLTCausalCreditConcurrency
end Mettapedia.MachineLearning.NeuralNetworks.LocalLearning
