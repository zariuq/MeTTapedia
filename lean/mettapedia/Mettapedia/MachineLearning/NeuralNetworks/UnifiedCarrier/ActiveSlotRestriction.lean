import Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier.RoutedTensorTransition

/-!
# Active-slot restriction for routed unified-carrier updates

The post-routing unified-carrier transition is pointwise in the slot index.
Consequently, after neural routing has produced its packet, restricting a
state and packet along any slot embedding commutes exactly with the routed
transition.

This theorem does not license restricting packet production itself.  Attention
and other global readers can couple retained and discarded slots.  The final
fixture gives an explicit two-slot producer for which producing then
restricting differs from restricting then producing.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier

namespace RoutedTensorState

/-- Restrict a routed state along a chosen map of small slots into large
slots.  Injectivity is not needed for naturality, although an active-frontier
embedding will normally be injective. -/
def reindexSlots
    {large small contentWidth evidenceWidth : ℕ}
    (route : Fin small → Fin large)
    (state : RoutedTensorState large contentWidth evidenceWidth) :
    RoutedTensorState small contentWidth evidenceWidth where
  content slot := state.content (route slot)
  nPlus slot := state.nPlus (route slot)
  nMinus slot := state.nMinus (route slot)
  innovationPlus slot := state.innovationPlus (route slot)
  innovationMinus slot := state.innovationMinus (route slot)

end RoutedTensorState

namespace RoutedTensorPacket

/-- Restrict only the slot-indexed parts of an already-produced packet.
Operator candidates remain shared across the retained slots. -/
def reindexSlots
    {operators large small contentWidth evidenceWidth : ℕ}
    (route : Fin small → Fin large)
    (packet : RoutedTensorPacket operators large contentWidth evidenceWidth) :
    RoutedTensorPacket operators small contentWidth evidenceWidth where
  precision slot := packet.precision (route slot)
  freshPlus slot := packet.freshPlus (route slot)
  freshMinus slot := packet.freshMinus (route slot)
  retention slot := packet.retention (route slot)
  candidate := packet.candidate
  learnedGate operator slot := packet.learnedGate operator (route slot)

end RoutedTensorPacket

namespace RoutedTensorResult

/-- Restrict a routed result, including its per-slot Bayes gain and effective
write gates. -/
def reindexSlots
    {operators large small contentWidth evidenceWidth : ℕ}
    (route : Fin small → Fin large)
    (result : RoutedTensorResult operators large contentWidth evidenceWidth) :
    RoutedTensorResult operators small contentWidth evidenceWidth where
  state := result.state.reindexSlots route
  bayesGain slot := result.bayesGain (route slot)
  effectiveGate operator slot := result.effectiveGate operator (route slot)

end RoutedTensorResult

/-- The already-routed state transition is natural under arbitrary slot
restriction.  This is the exact boundary that permits compact post-routing
replay on a declared active subspace. -/
theorem routedTensorStep_reindexSlots
    {operators large small contentWidth evidenceWidth : ℕ}
    (route : Fin small → Fin large)
    (useBayesGain : Bool)
    (current : RoutedTensorState large contentWidth evidenceWidth)
    (packet : RoutedTensorPacket operators large contentWidth evidenceWidth) :
    (routedTensorStep useBayesGain current packet).reindexSlots route =
      routedTensorStep useBayesGain (current.reindexSlots route)
        (packet.reindexSlots route) := by
  rfl

/-! ## Packet-production boundary -/

/-- A deliberately coupled packet producer: every output slot receives the
sum of all input slots. -/
noncomputable def coupledFresh
    {slots : ℕ} (content : Fin slots → ℚ) : Fin slots → ℚ :=
  fun _ => ∑ slot, content slot

def keepFirst : Fin 1 → Fin 2 := fun _ => 0

def twoSlotContent : Fin 2 → ℚ := ![1, 2]

/-- Global packet production need not commute with slot restriction.  The
discarded second slot contributes to the packet produced for the retained
first slot. -/
theorem coupled_packet_production_does_not_commute :
    (fun slot => coupledFresh twoSlotContent (keepFirst slot)) ≠
      coupledFresh (fun slot => twoSlotContent (keepFirst slot)) := by
  intro equality
  have first := congrFun equality 0
  norm_num [coupledFresh, twoSlotContent, keepFirst, Fin.sum_univ_succ] at first

#print axioms routedTensorStep_reindexSlots
#print axioms coupled_packet_production_does_not_commute

end Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier
