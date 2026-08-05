import Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier.ActiveSlotRestriction
import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.FixedAddressFrontier

/-!
# Production addressed-packet fixture

This fixture binds one source-authenticated unified-carrier scoring invocation
to both sides of the carrier waist.  The previous ternary operator consumes
the root fixed address and allocates three typed children in preorder.  The
same invocation produces nonzero neural evidence packets and calls the shared
routed transition exactly once.

The external verifier owns source, corpus, seeded-model, and invocation
identity.  Lean checks the discrete address transition, mixed-radix child
types, finite binary32 packet payload, nonvacuity, and compact row widths.
The packet-producing nonlinear heads and their floating-point evaluation are
not reimplemented here.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier
namespace MixedRadixAddressTransition

open Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder

def recordedCaptureSHA256 : String :=
  "98dfc272cbd68c40c0a17c8cbcfb17d48f7b1996c42f06591dbe11daa3f077d2"

def addressBefore : FixedAddressState Unit where
  contents := List.replicate 60 ()
  frontier := [0]
  nextFree := 1

def addressAfter : FixedAddressState Unit :=
  addressBefore.applyPreviousAction 1 3 (fun _ => ())

def recordedChildTypeIndices : List ℕ := [220, 136, 137]

def codeChildType : HoleType 16 :=
  (⟨2, by omega⟩, (⟨10, by omega⟩, ⟨0, by omega⟩))

def firstValueChildType : HoleType 16 :=
  (⟨1, by omega⟩, (⟨10, by omega⟩, ⟨1, by omega⟩))

def secondValueChildType : HoleType 16 :=
  (⟨1, by omega⟩, (⟨10, by omega⟩, ⟨2, by omega⟩))

def routedInputStateWords : List ℕ :=
[
  3215217700, 1039363806, 3194614848, 3176990112, 3222042874, 3223830655,
  3218508827, 3212774101, 3209652699, 3206329884, 3195136974, 3201331204,
  3209717716, 3206967597, 3196437220, 1044798783, 1048579648, 1043556232,
  0, 0, 0, 0, 0, 0,
  1043512651, 1045961728, 0, 0, 0, 0,
  0, 0, 1048579648, 1043556232, 0, 0,
  0, 0, 0, 0, 1043512651, 1045961728,
  0, 0, 0, 0, 0, 0
]

def routedPacketWords : List ℕ :=
[
  1054436582, 1053147588, 0, 0, 0, 0,
  0, 0, 1049313903, 1045408716, 1044520105, 1041284134,
  1048796165, 1044636638, 1048726355, 1044532533, 1044619315, 1046929509,
  1040733967, 1042344041, 1043892019, 1046071158, 1043793952, 1045955420,
  1064669779, 1064729304, 1065353216, 1065353216, 1065353216, 1065353216,
  1065353216, 1065353216, 3209121660, 1046098205, 1057896200, 1058575670,
  1056801458, 1051766453, 1055858959, 1055731874
]

def routedOutputStateWords : List ℕ :=
[
  3214098007, 1041445879, 3165582776, 1039214384, 3218760341, 3218231488,
  3211260422, 3202662770, 3209404678, 3194498028, 1040761056, 1031505384,
  3209441586, 3196068282, 1039131128, 1052941118, 1057164450, 1052652464,
  1044520105, 1041284134, 1048796165, 1044636638, 1048726355, 1044532533,
  1052216003, 1054570880, 1040733967, 1042344041, 1043892019, 1046071158,
  1043793952, 1045955420, 1057335384, 1052871082, 1044520105, 1041284134,
  1048796165, 1044636638, 1048726355, 1044532533, 1052454591, 1054834226,
  1040733967, 1042344041, 1043892019, 1046071158, 1043793952, 1045955420
]

def recordedFreshPlusWords : List ℕ :=
[
  1049313903, 1045408716, 1044520105, 1041284134, 1048796165, 1044636638,
  1048726355, 1044532533
]

theorem recorded_address_transition_exact :
    addressAfter.frontier = [1, 2, 3] ∧ addressAfter.nextFree = 4 := by
  decide

theorem recorded_child_type_indices_exact :
    [(holeTypeIndex 16 codeChildType).val,
      (holeTypeIndex 16 firstValueChildType).val,
      (holeTypeIndex 16 secondValueChildType).val] =
      recordedChildTypeIndices := by
  decide

theorem recorded_packet_words_are_finite :
    (decodeFiniteFloat32Words routedPacketWords).isSome = true := by
  decide

theorem recorded_fresh_packet_is_nonzero :
    recordedFreshPlusWords ≠ List.replicate 8 0 := by
  decide

theorem recorded_input_state_width :
    routedInputStateWords.length = 48 := by
  decide

theorem recorded_output_state_width :
    routedOutputStateWords.length = 48 := by
  decide

theorem reversed_child_order_is_wrong :
    [3, 2, 1] ≠ addressAfter.frontier := by
  decide

structure AddressedPacketCertificate : Prop where
  addressTransition :
    addressAfter.frontier = [1, 2, 3] ∧ addressAfter.nextFree = 4
  childTypes :
    [(holeTypeIndex 16 codeChildType).val,
      (holeTypeIndex 16 firstValueChildType).val,
      (holeTypeIndex 16 secondValueChildType).val] =
      recordedChildTypeIndices
  packetFinite :
    (decodeFiniteFloat32Words routedPacketWords).isSome = true
  packetNonzero : recordedFreshPlusWords ≠ List.replicate 8 0
  inputWidth : routedInputStateWords.length = 48
  outputWidth : routedOutputStateWords.length = 48

theorem productionInvocation_certificate : AddressedPacketCertificate where
  addressTransition := recorded_address_transition_exact
  childTypes := recorded_child_type_indices_exact
  packetFinite := recorded_packet_words_are_finite
  packetNonzero := recorded_fresh_packet_is_nonzero
  inputWidth := recorded_input_state_width
  outputWidth := recorded_output_state_width

#print axioms recorded_address_transition_exact
#print axioms recorded_child_type_indices_exact
#print axioms recorded_packet_words_are_finite
#print axioms recorded_fresh_packet_is_nonzero
#print axioms reversed_child_order_is_wrong
#print axioms productionInvocation_certificate

end MixedRadixAddressTransition
end Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier
