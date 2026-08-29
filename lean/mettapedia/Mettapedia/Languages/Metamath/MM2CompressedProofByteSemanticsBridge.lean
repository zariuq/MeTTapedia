import Mettapedia.Languages.Metamath.MM2CompressedProofSourceBridge

/-!
# Parametric compressed-byte semantics bridge

The target verifier classifies bytes with finite MM2 rows and retains a compact
least-significant-first prefix.  The authored source semantics uses the
Appendix-B numeric accumulator.  These theorems relate the two representations
for complete byte families; they do not expand a compressed proof into a
normal-label trace.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofByteSemanticsBridge

open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.Metamath.SourceGSLTCompressedTheorem

/-- Every `A`--`T` row denotes exactly the authored terminal action when the
compact reversed prefix and source accumulator agree. -/
theorem terminal_byte_family_exact
    (phase : CompressedPhase) (prefixDigits : List Nat)
    (terminalDigit : Nat)
    (digitBound : terminalDigit < 20)
    (accumulatorAgreement :
      phase.accumulator = prefixDigits.foldl
        (fun accumulator digit => 5 * accumulator + digit) 0) :
    compressedTerminalByteRow (65 + terminalDigit) terminalDigit ∈
        compressedTerminalByteRows ∧
      decodeByte phase (UInt8.ofNat (65 + terminalDigit)) =
        some
          ([.step
            (compressedIndexValue prefixDigits.reverse terminalDigit)],
            .justCompletedStep) := by
  constructor
  · exact List.mem_map.mpr
      ⟨terminalDigit, List.mem_range.mpr digitBound, rfl⟩
  · have byteExact :
    (UInt8.ofNat (65 + terminalDigit)).toNat = 65 + terminalDigit := by
        simp
        omega
    rw [compressedIndexValue_reverse_eq_sourceAccumulator,
      ← accumulatorAgreement]
    simp only [decodeByte]
    rw [byteExact]
    rw [if_pos (by omega)]
    congr 4
    all_goals omega

/-- Every `U`--`Y` row extends both representations by the same bijective
base-five digit. -/
theorem prefix_byte_family_exact
    (phase : CompressedPhase) (reversePrefixDigits : List Nat)
    (prefixDigit : Nat)
    (digitLower : 1 ≤ prefixDigit) (digitUpper : prefixDigit ≤ 5)
    (accumulatorAgreement :
      phase.accumulator = compressedPrefixValue reversePrefixDigits) :
    compressedPrefixByteRow (84 + prefixDigit) prefixDigit ∈
        compressedPrefixByteRows ∧
      decodeByte phase (UInt8.ofNat (84 + prefixDigit)) =
        some
          ([], .openIndex
            (compressedPrefixValue (prefixDigit :: reversePrefixDigits))) := by
  constructor
  · refine List.mem_map.mpr ⟨prefixDigit - 1, ?_, ?_⟩
    · exact List.mem_range.mpr (by omega)
    · have byteEq : 85 + (prefixDigit - 1) = 84 + prefixDigit := by
        omega
      have digitEq : prefixDigit - 1 + 1 = prefixDigit := by omega
      rw [byteEq, digitEq]
  · have byteExact :
        (UInt8.ofNat (84 + prefixDigit)).toNat = 84 + prefixDigit := by
        simp
        omega
    rw [show compressedPrefixValue (prefixDigit :: reversePrefixDigits) =
        5 * compressedPrefixValue reversePrefixDigits + prefixDigit by rfl,
      ← accumulatorAgreement]
    simp only [decodeByte]
    rw [byteExact]
    rw [if_neg (by omega), if_pos (by omega)]
    congr 3
    all_goals omega

/-- `Z` is enabled precisely after a completed step in the authored decoder;
the target's disallowed-phase inventory excludes that phase. -/
theorem save_phase_exact :
    decodeByte .justCompletedStep (UInt8.ofNat 90) =
        some ([.save], .betweenSteps) ∧
      compressedSaveDisallowedPhaseRow
          (.symbol "mm-compressed-just-completed-step") ∉
        compressedSaveDisallowedPhaseRows := by
  decide

/-- Negative save control: between-step and open-index phases are explicit
target faults and are rejected by the authored decoder. -/
theorem save_disallowed_phases_exact (accumulator : Nat) :
    decodeByte .betweenSteps (UInt8.ofNat 90) = none ∧
      decodeByte (.openIndex accumulator) (UInt8.ofNat 90) = none ∧
      compressedSaveDisallowedPhaseRow
          (.symbol "mm-compressed-between-steps") ∈
        compressedSaveDisallowedPhaseRows ∧
      compressedSaveDisallowedPhaseRow
          (.symbol "mm-compressed-open-index") ∈
        compressedSaveDisallowedPhaseRows := by
  simp [decodeByte, compressedSaveDisallowedPhaseRows,
    compressedSaveDisallowedPhaseRow]

/-- `?` is an explicit incomplete-proof action outside an open index and is
not silently absorbed into the invalid-byte class. -/
theorem question_phase_exact :
    decodeByte .betweenSteps (UInt8.ofNat 63) =
        some ([.unknown], .betweenSteps) ∧
      decodeByte .justCompletedStep (UInt8.ofNat 63) =
        some ([.unknown], .betweenSteps) ∧
      compressedInvalidByteRow 63 ∉ compressedInvalidByteRows := by
  decide

#print axioms terminal_byte_family_exact
#print axioms prefix_byte_family_exact
#print axioms save_phase_exact
#print axioms save_disallowed_phases_exact
#print axioms question_phase_exact

end Mettapedia.Languages.Metamath.MM2CompressedProofByteSemanticsBridge
