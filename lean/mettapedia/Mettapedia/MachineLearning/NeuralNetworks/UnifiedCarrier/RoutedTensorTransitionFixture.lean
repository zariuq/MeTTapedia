import Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier.RoutedTensorTransition

/-!
# Executable routed-transition fixture

This fixture records one two-slot binary32 transition emitted by the executable
unified carrier.  The input exercises nonzero retained precision, distinct
per-slot retention, learned and Bayes write damping, posterior fusion,
innovation-only accumulation, and every packed-state plane.

The model source and JSON artifact are authenticated by the external fixture
verifier.  The theorems below independently decode the recorded binary32 rows
and check the exact rational transition in the Lean kernel.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier

noncomputable section

open Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Float32CheckpointMatrix

def runtimeInput : RoutedTensorState 2 1 1 where
  content := fun slot _ => ![0, 2] slot
  nPlus := fun slot _ => ![2, 4] slot
  nMinus := fun _ _ => 0
  innovationPlus := fun slot _ => ![1 / 2, 1] slot
  innovationMinus := fun slot _ => ![3 / 2, 2] slot

def runtimePacket : RoutedTensorPacket 1 2 1 1 where
  precision := fun slot _ => ![2, 4] slot
  freshPlus := fun slot _ => ![3 / 4, 1 / 4] slot
  freshMinus := fun slot _ => ![1 / 4, 3 / 4] slot
  retention := fun slot _ => ![1 / 2, 1 / 4] slot
  candidate := fun _ _ => 4
  learnedGate := fun _ slot => ![1, 1 / 2] slot

def runtimeObserved : RoutedTensorResult 1 2 1 1 where
  state :=
    { content := fun slot _ => ![2, 5 / 2] slot
      nPlus := fun slot _ => ![7 / 4, 5 / 4] slot
      nMinus := fun slot _ => ![1 / 4, 3 / 4] slot
      innovationPlus := fun _ _ => 5 / 4
      innovationMinus := fun slot _ => ![7 / 4, 11 / 4] slot }
  bayesGain := fun _ => 1 / 2
  effectiveGate := fun _ slot => ![1 / 2, 1 / 4] slot

def runtimeMetadata : RoutedTensorMetadata 2 2 where
  slotTypes := fun slot => ![3, 7] slot
  frontier := fun slot => ![1, -1] slot
  control := fun coordinate => ![1 / 2, -1 / 2] coordinate
  frontierLength := 1
  nextFree := 2

def runtimeInputPackedWords : List ℕ :=
  [0, 1073741824, 1073741824, 1082130432, 0, 0,
   1056964608, 1065353216, 1069547520, 1073741824,
   1077936128, 1088421888, 1065353216, 3212836864,
   1056964608, 3204448256, 1065353216, 1073741824]

def runtimeOutputPackedWords : List ℕ :=
  [1073741824, 1075838976, 1071644672, 1067450368,
   1048576000, 1061158912, 1067450368, 1067450368,
   1071644672, 1076887552, 1077936128, 1088421888,
   1065353216, 3212836864, 1056964608, 3204448256,
   1065353216, 1073741824]

@[simp] theorem finTwoByOne_divNat_zero :
    (0 : Fin (2 * 1)).divNat = (0 : Fin 2) := by
  ext
  norm_num

@[simp] theorem finTwoByOne_divNat_one :
    (1 : Fin (2 * 1)).divNat = (1 : Fin 2) := by
  ext
  norm_num

/-- The actual routed operation is exactly the expected nontrivial
three-plane transition. -/
theorem runtime_routed_transition_is_exact :
    routedTensorStep true runtimeInput runtimePacket = runtimeObserved := by
  apply RoutedTensorResult.ext
  · apply RoutedTensorState.ext <;>
      funext slot coordinate <;>
      fin_cases slot <;>
      fin_cases coordinate <;>
      norm_num [routedTensorStep, runtimeInput, runtimePacket, runtimeObserved,
        finiteMean, routedPrecisionGain, Fin.sum_univ_succ]
  · funext slot
    fin_cases slot <;>
      dsimp [routedTensorStep, runtimeInput, runtimePacket, runtimeObserved] <;>
      norm_num [finiteMean, routedPrecisionGain, Fin.sum_univ_succ]
  · funext operator slot
    fin_cases operator
    fin_cases slot <;>
      norm_num [routedTensorStep, runtimeInput, runtimePacket, runtimeObserved,
        finiteMean, routedPrecisionGain, Fin.sum_univ_succ]

/-- The recorded input row decodes to the specified product-state order. -/
theorem runtime_input_packed_words_are_exact :
    decodeFiniteFloat32Words runtimeInputPackedWords =
      some (packRoutedState runtimeInput runtimeMetadata) := by
  norm_num [runtimeInputPackedWords, decodeFiniteFloat32Words,
    decodeFiniteFloat32?, FiniteFloat32Word.toRat, float32Exponent,
    float32Mantissa, packRoutedState, rowMajorList, rowMajorFlatten,
    finProdFinEquiv, runtimeInput, runtimeMetadata]

/-- The recorded output row decodes to the exact routed-transition result
without trusting a Python-derived ideal value. -/
theorem runtime_output_packed_words_are_exact :
    decodeFiniteFloat32Words runtimeOutputPackedWords =
      some (packRoutedState runtimeObserved.state runtimeMetadata) := by
  norm_num [runtimeOutputPackedWords, decodeFiniteFloat32Words,
    decodeFiniteFloat32?, FiniteFloat32Word.toRat, float32Exponent,
    float32Mantissa, packRoutedState, rowMajorList, rowMajorFlatten,
    finProdFinEquiv, runtimeObserved, runtimeMetadata]

/-- Removing Bayes damping changes the first observed content coordinate, so
the fixture cannot pass at the workspace endpoint by coincidence. -/
theorem runtime_fixture_detects_bayes_bypass :
    (routedTensorStep false runtimeInput runtimePacket).state.content 0 0 ≠
      runtimeObserved.state.content 0 0 := by
  norm_num [routedTensorStep, runtimeInput, runtimePacket, runtimeObserved,
    finiteMean, routedPrecisionGain]

#print axioms runtime_routed_transition_is_exact
#print axioms runtime_input_packed_words_are_exact
#print axioms runtime_output_packed_words_are_exact
#print axioms runtime_fixture_detects_bayes_bypass

end

end Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier
