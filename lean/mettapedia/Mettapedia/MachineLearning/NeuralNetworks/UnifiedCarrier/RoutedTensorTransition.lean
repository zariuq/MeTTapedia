import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Float32CheckpointMatrix
import Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier.Core

/-!
# Routed tensor transition for the unified carrier

This module isolates the tensor-shaped state-transition waist used after
neural routing has produced content candidates, learned gates, and fresh
evidence packets.  It models the runtime's exact-real equations over rational
coordinates:

* retained precision is retention times current precision;
* Bayes gain is fresh precision divided by total routed precision;
* the content plane applies the mean gated candidate displacement;
* posterior evidence fades then fuses;
* episode innovations receive only the fresh packet.

The neural production of routed packets and binary32 rounding remain separate
obligations.  `packRoutedState` fixes the product-state plane order shared with
the executable carrier.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier

open Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
open Float32CheckpointMatrix
open scoped BigOperators

/-- Tensor-shaped content, posterior evidence, and episode innovations. -/
@[ext] structure RoutedTensorState
    (slots contentWidth evidenceWidth : ℕ) where
  content : Fin slots → Fin contentWidth → ℚ
  nPlus : Fin slots → Fin evidenceWidth → ℚ
  nMinus : Fin slots → Fin evidenceWidth → ℚ
  innovationPlus : Fin slots → Fin evidenceWidth → ℚ
  innovationMinus : Fin slots → Fin evidenceWidth → ℚ

/-- Already-routed inputs for one unified-carrier transition. -/
@[ext] structure RoutedTensorPacket
    (operators slots contentWidth evidenceWidth : ℕ) where
  precision : Fin slots → Fin evidenceWidth → ℚ
  freshPlus : Fin slots → Fin evidenceWidth → ℚ
  freshMinus : Fin slots → Fin evidenceWidth → ℚ
  retention : Fin slots → Fin evidenceWidth → ℚ
  candidate : Fin operators → Fin contentWidth → ℚ
  learnedGate : Fin operators → Fin slots → ℚ

/-- State result together with the routed gain and effective write gates. -/
@[ext] structure RoutedTensorResult
    (operators slots contentWidth evidenceWidth : ℕ) where
  state : RoutedTensorState slots contentWidth evidenceWidth
  bayesGain : Fin slots → ℚ
  effectiveGate : Fin operators → Fin slots → ℚ

/-- Arithmetic mean used by the runtime across an explicitly finite axis.
The executable configuration excludes a zero operator and evidence width. -/
def finiteMean {size : ℕ} (values : Fin size → ℚ) : ℚ :=
  (∑ index, values index) / size

/-- Source-faithful scalar precision gain, including its no-information
boundary. -/
def routedPrecisionGain (retained fresh : ℚ) : ℚ :=
  if 0 < retained + fresh then fresh / (retained + fresh) else 0

/-- Exact rational semantics of one already-routed runtime transition. -/
def routedTensorStep
    {operators slots contentWidth evidenceWidth : ℕ}
    (useBayesGain : Bool)
    (current : RoutedTensorState slots contentWidth evidenceWidth)
    (packet : RoutedTensorPacket operators slots contentWidth evidenceWidth) :
    RoutedTensorResult operators slots contentWidth evidenceWidth :=
  let freshPrecision := fun slot feature =>
    packet.freshPlus slot feature + packet.freshMinus slot feature
  let retainedPrecision := fun slot feature =>
    packet.retention slot feature * packet.precision slot feature
  let bayesGain := fun slot =>
    routedPrecisionGain
      (finiteMean fun feature => retainedPrecision slot feature)
      (finiteMean fun feature => freshPrecision slot feature)
  let effectiveGate := fun operator slot =>
    if useBayesGain then
      packet.learnedGate operator slot * bayesGain slot
    else
      packet.learnedGate operator slot
  { state :=
      { content := fun slot coordinate =>
          current.content slot coordinate +
            finiteMean fun operator =>
              effectiveGate operator slot *
                (packet.candidate operator coordinate -
                  current.content slot coordinate)
        nPlus := fun slot feature =>
          packet.retention slot feature * current.nPlus slot feature +
            packet.freshPlus slot feature
        nMinus := fun slot feature =>
          packet.retention slot feature * current.nMinus slot feature +
            packet.freshMinus slot feature
        innovationPlus := fun slot feature =>
          current.innovationPlus slot feature + packet.freshPlus slot feature
        innovationMinus := fun slot feature =>
          current.innovationMinus slot feature + packet.freshMinus slot feature }
    bayesGain := bayesGain
    effectiveGate := effectiveGate }

/-- Metadata occupying the discrete tail of the common floating row. -/
@[ext] structure RoutedTensorMetadata (slots controlWidth : ℕ) where
  slotTypes : Fin slots → ℚ
  frontier : Fin slots → ℚ
  control : Fin controlWidth → ℚ
  frontierLength : ℚ
  nextFree : ℚ

/-- Row-major list view of a two-dimensional finite family. -/
def rowMajorList {rows columns : ℕ} {α : Type*}
    (entries : Fin rows → Fin columns → α) : List α :=
  List.ofFn (rowMajorFlatten entries)

/-- Fail-closed decoder from an arbitrary natural word.  Unlike a raw
`FiniteFloat32Word`, malformed infinity and NaN words cannot inhabit the
successful branch. -/
def decodeFiniteFloat32? (word : ℕ) : Option ℚ :=
  if hword : word < 4294967296 then
    if hexponent : float32Exponent word < 255 then
      some (FiniteFloat32Word.toRat ⟨word, hword, hexponent⟩)
    else
      none
  else
    none

/-- Decode an entire runtime word row, rejecting it if any component is not a
finite binary32 value. -/
def decodeFiniteFloat32Words (words : List ℕ) : Option (List ℚ) :=
  words.mapM decodeFiniteFloat32?

/-- Runtime product-state order:
content, posterior positive/negative, innovation positive/negative, then
slot types, frontier, recurrent control, frontier length, and allocation
cursor. -/
def packRoutedState
    {slots contentWidth evidenceWidth controlWidth : ℕ}
    (state : RoutedTensorState slots contentWidth evidenceWidth)
    (metadata : RoutedTensorMetadata slots controlWidth) : List ℚ :=
  rowMajorList state.content ++
  rowMajorList state.nPlus ++
  rowMajorList state.nMinus ++
  rowMajorList state.innovationPlus ++
  rowMajorList state.innovationMinus ++
  List.ofFn metadata.slotTypes ++
  List.ofFn metadata.frontier ++
  List.ofFn metadata.control ++
  [metadata.frontierLength, metadata.nextFree]

/-- The product-state row has exactly the source-level packed width. -/
theorem packRoutedState_length
    {slots contentWidth evidenceWidth controlWidth : ℕ}
    (state : RoutedTensorState slots contentWidth evidenceWidth)
    (metadata : RoutedTensorMetadata slots controlWidth) :
    (packRoutedState state metadata).length =
      packedStateWidth slots contentWidth evidenceWidth controlWidth := by
  simp [packRoutedState, rowMajorList, packedStateWidth]
  ring

/-- Innovation accumulation is independent of posterior retention. -/
@[simp] theorem routedTensorStep_innovationPlus
    {operators slots contentWidth evidenceWidth : ℕ}
    (useBayesGain : Bool)
    (current : RoutedTensorState slots contentWidth evidenceWidth)
    (packet : RoutedTensorPacket operators slots contentWidth evidenceWidth)
    (slot : Fin slots) (feature : Fin evidenceWidth) :
    (routedTensorStep useBayesGain current packet).state.innovationPlus
        slot feature =
      current.innovationPlus slot feature + packet.freshPlus slot feature := rfl

/-- Disabling Bayes coupling leaves the learned gate unchanged. -/
@[simp] theorem routedTensorStep_effectiveGate_withoutBayes
    {operators slots contentWidth evidenceWidth : ℕ}
    (current : RoutedTensorState slots contentWidth evidenceWidth)
    (packet : RoutedTensorPacket operators slots contentWidth evidenceWidth)
    (operator : Fin operators) (slot : Fin slots) :
    (routedTensorStep false current packet).effectiveGate operator slot =
      packet.learnedGate operator slot := rfl

/-- At the no-information boundary the coupled content gate is zero. -/
theorem routedPrecisionGain_zero_zero :
    routedPrecisionGain 0 0 = 0 := by
  norm_num [routedPrecisionGain]

/-- Positive equal routed precisions give the nontrivial half-gain used by the
runtime conformance fixture. -/
theorem routedPrecisionGain_one_one :
    routedPrecisionGain 1 1 = 1 / 2 := by
  norm_num [routedPrecisionGain]

/-- Infinity is rejected before it can enter a routed transition fixture. -/
theorem decode_positiveInfinity_is_none :
    decodeFiniteFloat32? 2139095040 = none := by
  norm_num [decodeFiniteFloat32?, float32Exponent]

/-- A plane swap is observable even when the packed row lengths agree. -/
theorem posterior_plane_swap_changes_row :
    let state : RoutedTensorState 1 1 1 :=
      { content := fun _ _ => 0
        nPlus := fun _ _ => 1
        nMinus := fun _ _ => 2
        innovationPlus := fun _ _ => 3
        innovationMinus := fun _ _ => 4 }
    let swapped : RoutedTensorState 1 1 1 :=
      { state with nPlus := state.nMinus, nMinus := state.nPlus }
    let metadata : RoutedTensorMetadata 1 1 :=
      { slotTypes := fun _ => 0
        frontier := fun _ => 0
        control := fun _ => 0
        frontierLength := 1
        nextFree := 1 }
    packRoutedState state metadata ≠ packRoutedState swapped metadata := by
  norm_num [packRoutedState, rowMajorList, rowMajorFlatten, rowMajorIndex]

#print axioms packRoutedState_length
#print axioms routedTensorStep_innovationPlus
#print axioms routedTensorStep_effectiveGate_withoutBayes
#print axioms routedPrecisionGain_one_one
#print axioms decode_positiveInfinity_is_none
#print axioms posterior_plane_swap_changes_row

end Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier
