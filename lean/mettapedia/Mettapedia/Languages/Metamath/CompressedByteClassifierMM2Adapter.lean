import Mettapedia.Languages.Metamath.CompressedByteClassifierCore
import Mettapedia.Languages.Metamath.MM2CompressedByteScannerGSLT

/-!
# Compact compressed-byte classifier to MM2 row adapter

This adapter connects the dependency-light compact classifier to the existing
MM2 scanner row vocabulary.  The source operation remains in the compact
classifier and the MM2 scanner remains independently executable; this module
proves their shared phase, classification, and public-row boundary.

It does not claim that an MM2 row has fired in an assembled program.  That
requires the later owner, cursor, and scheduler execution bridge.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.CompressedByteClassifierCore.MM2Adapter

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2CompressedProofExecution

abbrev MM2ScannerPhase :=
  Mettapedia.Languages.Metamath.MM2CompressedByteScannerGSLT.ScannerPhase

abbrev MM2ByteClass :=
  Mettapedia.Languages.Metamath.MM2CompressedByteScannerGSLT.ByteClass

/-- The compact phase has the exact same retained prefix representation as the
existing MM2 scanner phase. -/
def phaseToMM2 : Phase -> MM2ScannerPhase
  | .between => .between
  | .open reversePrefix => .open reversePrefix
  | .completed => .completed

theorem phaseToMM2_reversePrefix (phase : Phase) :
    Mettapedia.Languages.Metamath.MM2CompressedByteScannerGSLT.ScannerPhase.reversePrefix
      (phaseToMM2 phase) =
      Phase.reversePrefix phase := by
  cases phase <;> rfl

/-- Map the abstract target classifier family into the corresponding concrete
MM2 scanner classifier family. -/
def classToMM2 : ByteClass -> MM2ByteClass
  | .terminal digit => .terminal digit
  | .prefix digit => .prefix digit
  | .save => .save
  | .saveFault phase => .saveFault (phaseToMM2 phase)
  | .question phase => .question (phaseToMM2 phase)
  | .questionOpenFault => .questionOpenFault
  | .invalid byte => .invalid byte

/-- Render one abstract target-row constructor into the exact public MM2 row
used by the concrete scanner inventory. -/
def targetRowToMM2 : TargetRow -> Atom
  | .terminalByte code digit => compressedTerminalByteRow code digit
  | .prefixByte code digit => compressedPrefixByteRow code digit
  | .saveRule => compressedOwnedRuntimeRuleRow "save" compressedSaveRule
  | .saveDisallowed phase =>
      compressedSaveDisallowedPhaseRow
        (Mettapedia.Languages.Metamath.MM2CompressedByteScannerGSLT.ScannerPhase.atom
          (phaseToMM2 phase))
  | .questionAllowed phase =>
      compressedQuestionAllowedPhaseRow
        (Mettapedia.Languages.Metamath.MM2CompressedByteScannerGSLT.ScannerPhase.atom
          (phaseToMM2 phase))
  | .questionOpenFaultRule =>
      compressedOwnedRuntimeRuleRow "question-open-fault"
        compressedQuestionOpenFaultRule
  | .invalidByte code => compressedInvalidByteRow code

/-- Row mapping commutes with classifier-family mapping. -/
theorem targetRowToMM2_classToMM2_row (byteClass : ByteClass) :
    targetRowToMM2 (ByteClass.row byteClass) =
      Mettapedia.Languages.Metamath.MM2CompressedByteScannerGSLT.ByteClass.row
        (classToMM2 byteClass) := by
  cases byteClass <;> rfl

/-- The abstract classifier selects exactly the same concrete MM2 classifier
family at the corresponding retained phase. -/
theorem classToMM2_classify (phase : Phase) (byte : UInt8) :
    classToMM2 (classify phase byte) =
      Mettapedia.Languages.Metamath.MM2CompressedByteScannerGSLT.classifyByte
        (phaseToMM2 phase) byte := by
  cases phase <;>
    simp only [classify,
      Mettapedia.Languages.Metamath.MM2CompressedByteScannerGSLT.classifyByte,
      classToMM2, phaseToMM2]
  all_goals
    by_cases terminalCase : 65 <= byte.toNat ∧ byte.toNat <= 84
    · have terminalBool :
        (decide (65 <= byte.toNat) && decide (byte.toNat <= 84)) = true := by
          simp [terminalCase]
      simp only [if_pos terminalBool, if_pos terminalCase]
    · have terminalBool :
          ¬((decide (65 <= byte.toNat) && decide (byte.toNat <= 84)) = true) := by
            simp [terminalCase]
      simp only [if_neg terminalBool, if_neg terminalCase]
      by_cases prefixCase : 85 <= byte.toNat ∧ byte.toNat <= 89
      · have prefixBool :
          (decide (85 <= byte.toNat) && decide (byte.toNat <= 89)) = true := by
            simp [prefixCase]
        simp only [if_pos prefixBool, if_pos prefixCase]
      · have prefixBool :
            ¬((decide (85 <= byte.toNat) && decide (byte.toNat <= 89)) = true) := by
              simp [prefixCase]
        simp only [if_neg prefixBool, if_neg prefixCase]
        by_cases saveCase : byte.toNat = 90
        · simp only [if_pos saveCase]
        · by_cases questionCase : byte.toNat = 63
          · simp only [if_neg saveCase, if_pos questionCase]
          · simp only [if_neg saveCase, if_neg questionCase]

/-- The row selected by the abstract classifier is exactly the row selected
by the existing MM2 scanner classifier. -/
theorem targetRowToMM2_classify_row (phase : Phase) (byte : UInt8) :
    targetRowToMM2 (ByteClass.row (classify phase byte)) =
      Mettapedia.Languages.Metamath.MM2CompressedByteScannerGSLT.ByteClass.row
        (Mettapedia.Languages.Metamath.MM2CompressedByteScannerGSLT.classifyByte
          (phaseToMM2 phase) byte) := by
  rw [targetRowToMM2_classToMM2_row, classToMM2_classify]

/-- A terminal classification retains the exact existing MM2 terminal row. -/
theorem terminal_A_maps_to_mm2_terminal_row :
    targetRowToMM2 (ByteClass.row (classify .between (UInt8.ofNat 65))) =
      compressedTerminalByteRow 65 0 := by
  decide +kernel

/-- A malformed byte remains an explicit MM2 invalid-byte row rather than
falling through to a compact proof action. -/
theorem invalid_byte_maps_to_mm2_fault_row :
    targetRowToMM2 (ByteClass.row (classify .between (UInt8.ofNat 48))) =
      compressedInvalidByteRow 48 := by
  decide +kernel

/-- The compact terminal control maps into the actual static MM2 verifier
inventory, rather than an adapter-only row vocabulary. -/
theorem terminal_A_mm2_row_is_static :
    targetRowToMM2 (ByteClass.row (classify .between (UInt8.ofNat 65))) ∈
      compressedVerifierStaticRows := by
  decide +kernel

/-- The malformed-byte control maps into the verifier's explicit static
invalid-byte profile, so it cannot fall through to a compact proof action. -/
theorem invalid_byte_mm2_row_is_static :
    targetRowToMM2 (ByteClass.row (classify .between (UInt8.ofNat 48))) ∈
      compressedVerifierStaticRows := by
  decide +kernel

#print axioms phaseToMM2_reversePrefix
#print axioms targetRowToMM2_classToMM2_row
#print axioms classToMM2_classify
#print axioms targetRowToMM2_classify_row
#print axioms terminal_A_maps_to_mm2_terminal_row
#print axioms invalid_byte_maps_to_mm2_fault_row
#print axioms terminal_A_mm2_row_is_static
#print axioms invalid_byte_mm2_row_is_static

end Mettapedia.Languages.Metamath.CompressedByteClassifierCore.MM2Adapter
