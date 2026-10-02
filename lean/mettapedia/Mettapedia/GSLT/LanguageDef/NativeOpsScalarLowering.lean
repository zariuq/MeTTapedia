import Mettapedia.GSLT.LanguageDef.NativeOpsLowering
import Mettapedia.GSLT.LanguageDef.NativeOpsSourceEval
import Mettapedia.GSLT.LanguageDef.NativeOpsTargetEval
import Mettapedia.GSLT.LanguageDef.NativeOpsValueDeterminism

/-!
# Preservation and reflection of emitted scalar fragments

These laws concern the actual ordered IR suffix emitted after operand
evaluation: explicit numeric guards followed by a fresh pure temporary.
Faulting guards return the function's typed default and retain the complete
poisoned post-state. Undefined unsigned division or shifting is not admitted
as an additional value. Operand evaluation and whole-function compilation
are separate composition obligations.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeOps

open NativeIR (Atom Instruction PureOperation)
open NativeWord64 (Word Fault WordOp encode)

theorem numeric_guard_fault_iff (operation : WordOp) (left right : Word) (fault : Fault) :
    targetNumericFault operation (encode right) = some fault ↔
      NativeWord64.sourceBinary operation left right = .error fault := by
  have zero : encode right = (0 : BitVec 64) ↔ right.val = 0 :=
    NativeWord64.encode_eq_zero right
  have value : (encode right).toNat = right.val := rfl
  cases operation with
  | div | mod =>
      by_cases isZero : right.val = 0
      · have encodedZero := zero.mpr isZero
        simp only [targetNumericFault, NativeWord64.sourceBinary]
        rw [if_pos encodedZero, if_pos isZero]
        simp
      · have encodedNonzero : encode right ≠ (0 : BitVec 64) := fun same => isZero (zero.mp same)
        simp only [targetNumericFault, NativeWord64.sourceBinary]
        rw [if_neg encodedNonzero, if_neg isZero]
        simp
  | shl | shr =>
      by_cases outside : 64 ≤ right.val
      · have encodedOutside : 64 ≤ (encode right).toNat := by rw [value]; exact outside
        simp only [targetNumericFault, NativeWord64.sourceBinary]
        rw [if_pos encodedOutside, if_pos outside]
        simp
      · have encodedInside : ¬ 64 ≤ (encode right).toNat := by rw [value]; exact outside
        simp only [targetNumericFault, NativeWord64.sourceBinary]
        rw [if_neg encodedInside, if_neg outside]
        simp
  | add | sub | mul | band | bor | bxor => simp [targetNumericFault, NativeWord64.sourceBinary]

theorem numeric_guard_clear_of_success (operation : WordOp) (left right value : Word)
    (computed : NativeWord64.sourceBinary operation left right = .ok value) :
    targetNumericFault operation (encode right) = none := by
  cases found : targetNumericFault operation (encode right) with
  | none => rfl
  | some fault =>
      have refused := (numeric_guard_fault_iff operation left right fault).mp found
      rw [computed] at refused
      cases refused

theorem target_run_empty_exact {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {result : NativeType}
    (root : List Instruction) (frame : TargetFrame) (state : TargetState World)
    (out : TargetBlockOutcome World) :
    TargetRun interface heap calls result root [] frame state out ↔
      out = ⟨.normal, frame, state⟩ := by
  constructor
  · intro ran; cases ran; rfl
  · intro same; subst out; exact .nil _ _ _

theorem target_temporary_instruction_exact {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {result : NativeType}
    {frame : TargetFrame} {state : TargetState World} {identity : Nat} {type : NativeType}
    {operation : PureOperation} {value : TargetValue}
    (unused : frame.temporaryNames.contains identity = false)
    (computed : TargetPureEval interface frame state operation value)
    (out : TargetBlockOutcome World) :
    TargetInstructionEval interface heap calls result (.temporary identity type operation)
      frame state out ↔ out = ⟨.normal, targetDeclareTemporary frame identity value, state⟩ := by
  constructor
  · intro ran
    cases ran with
    | temporary _ otherComputed =>
        cases target_pure_unique computed otherComputed
        rfl
  · intro same; subst out; exact .temporary unused computed

theorem target_run_temporary_exact {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {result : NativeType}
    {frame : TargetFrame} {state : TargetState World} {identity : Nat} {type : NativeType}
    {operation : PureOperation} {value : TargetValue}
    (unused : frame.temporaryNames.contains identity = false)
    (computed : TargetPureEval interface frame state operation value)
    (root : List Instruction) (out : TargetBlockOutcome World) :
    TargetRun interface heap calls result root [.temporary identity type operation] frame state out ↔
      out = ⟨.normal, targetDeclareTemporary frame identity value, state⟩ := by
  constructor
  · intro ran
    cases ran with
    | next first rest =>
        cases (target_temporary_instruction_exact unused computed _).mp first
        exact (target_run_empty_exact _ _ _ _).mp rest
    | «return» first => cases (target_temporary_instruction_exact unused computed _).mp first
    | resume first _ _ => cases (target_temporary_instruction_exact unused computed _).mp first
    | escape first _ => cases (target_temporary_instruction_exact unused computed _).mp first
  · intro same; subst out
    exact .next (.temporary unused computed) (.nil _ _ _)

theorem target_numeric_clear_instruction_exact {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {result : NativeType}
    {frame : TargetFrame} {state : TargetState World} {operation : WordOp} {right : Atom}
    {value : BitVec 64} (read : TargetAtomEval interface frame state right (.word value))
    (clear : targetNumericFault operation value = none) (out : TargetBlockOutcome World) :
    TargetInstructionEval interface heap calls result (.checkedNumericGuard operation right)
      frame state out ↔ out = ⟨.normal, frame, state⟩ := by
  constructor
  · intro ran
    cases ran with
    | numericClear _ _ => rfl
    | numericFault otherRead failed _ =>
        cases target_atom_unique read otherRead
        rw [clear] at failed
        cases failed
  · intro same; subst out; exact .numericClear read clear

theorem target_numeric_fault_instruction_exact {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {result : NativeType}
    {frame : TargetFrame} {state : TargetState World} {operation : WordOp} {right : Atom}
    {value : BitVec 64} {fault : Fault} {default : TargetValue}
    (read : TargetAtomEval interface frame state right (.word value))
    (failed : targetNumericFault operation value = some fault)
    (zero : TargetZero interface result default) (out : TargetBlockOutcome World) :
    TargetInstructionEval interface heap calls result (.checkedNumericGuard operation right)
      frame state out ↔ out = ⟨.returned default, frame, targetPoison state fault⟩ := by
  constructor
  · intro ran
    cases ran with
    | numericClear otherRead clear =>
        cases target_atom_unique read otherRead
        rw [failed] at clear
        cases clear
    | numericFault otherRead otherFailed otherZero =>
        cases target_atom_unique read otherRead
        cases Option.some.inj (failed.symm.trans otherFailed)
        cases target_zero_unique zero otherZero
        rfl
  · intro same; subst out; exact .numericFault read failed zero

theorem target_numeric_clear_then_exact {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {result : NativeType}
    {frame : TargetFrame} {state : TargetState World} {operation : WordOp} {right : Atom}
    {value : BitVec 64} (read : TargetAtomEval interface frame state right (.word value))
    (clear : targetNumericFault operation value = none)
    (root rest : List Instruction) (out : TargetBlockOutcome World) :
    TargetRun interface heap calls result root (.checkedNumericGuard operation right :: rest)
      frame state out ↔ TargetRun interface heap calls result root rest frame state out := by
  constructor
  · intro ran
    cases ran with
    | next first rest =>
        cases (target_numeric_clear_instruction_exact read clear _).mp first
        exact rest
    | «return» first => cases (target_numeric_clear_instruction_exact read clear _).mp first
    | resume first _ _ => cases (target_numeric_clear_instruction_exact read clear _).mp first
    | escape first _ => cases (target_numeric_clear_instruction_exact read clear _).mp first
  · intro ran; exact .next (.numericClear read clear) ran

theorem target_numeric_fault_then_exact {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {result : NativeType}
    {frame : TargetFrame} {state : TargetState World} {operation : WordOp} {right : Atom}
    {value : BitVec 64} {fault : Fault} {default : TargetValue}
    (read : TargetAtomEval interface frame state right (.word value))
    (failed : targetNumericFault operation value = some fault)
    (zero : TargetZero interface result default)
    (root rest : List Instruction) (out : TargetBlockOutcome World) :
    TargetRun interface heap calls result root (.checkedNumericGuard operation right :: rest)
      frame state out ↔ out = ⟨.returned default, frame, targetPoison state fault⟩ := by
  constructor
  · intro ran
    cases ran with
    | next first _ => cases (target_numeric_fault_instruction_exact read failed zero _).mp first
    | «return» first => exact (target_numeric_fault_instruction_exact read failed zero _).mp first
    | resume first _ _ => cases (target_numeric_fault_instruction_exact read failed zero _).mp first
    | escape first _ => cases (target_numeric_fault_instruction_exact read failed zero _).mp first
  · intro same; subst out; exact .return (.numericFault read failed zero)

theorem lowered_word_success_exact {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {result : NativeType}
    {frame : TargetFrame} {state : TargetState World} {identity : Nat} {left right : Atom}
    (operation : WordOp) (first second value : Word)
    (readLeft : TargetAtomEval interface frame state left (.word (encode first)))
    (readRight : TargetAtomEval interface frame state right (.word (encode second)))
    (unused : frame.temporaryNames.contains identity = false)
    (computed : NativeWord64.sourceBinary operation first second = .ok value)
    (root : List Instruction) (out : TargetBlockOutcome World) :
    TargetRun interface heap calls result root
      (NativeLowering.numericGuard (.word operation) right ++
        [.temporary identity .word (.binary (.word operation) left right)]) frame state out ↔
      out = ⟨.normal, targetDeclareTemporary frame identity (.word (encode value)), state⟩ := by
  have numeric : targetUncheckedBinary (.word operation) (.word (encode first))
      (.word (encode second)) = some (.word (encode value)) := by
    simp only [targetUncheckedBinary, targetBinaryOp]
    rw [(NativeWord64.binary_success_iff operation first second value).mpr computed]
    rfl
  have pure : TargetPureEval interface frame state (.binary (.word operation) left right)
      (.word (encode value)) := .binary readLeft readRight numeric
  have clear := numeric_guard_clear_of_success operation first second value computed
  cases operation <;> simp only [NativeLowering.numericGuard, List.nil_append, List.cons_append]
  all_goals first
    | exact target_run_temporary_exact unused pure root out
    | rw [target_numeric_clear_then_exact readRight clear]
      exact target_run_temporary_exact unused pure root out

theorem lowered_word_fault_exact {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {result : NativeType}
    {frame : TargetFrame} {state : TargetState World} {identity : Nat} {left right : Atom}
    (operation : WordOp) (first second : Word) (fault : Fault) {default : TargetValue}
    (readRight : TargetAtomEval interface frame state right (.word (encode second)))
    (refused : NativeWord64.sourceBinary operation first second = .error fault)
    (zero : TargetZero interface result default)
    (root : List Instruction) (out : TargetBlockOutcome World) :
    TargetRun interface heap calls result root
      (NativeLowering.numericGuard (.word operation) right ++
        [.temporary identity .word (.binary (.word operation) left right)]) frame state out ↔
      out = ⟨.returned default, frame, targetPoison state fault⟩ := by
  have failed := (numeric_guard_fault_iff operation first second fault).mpr refused
  cases operation <;> simp only [NativeLowering.numericGuard, List.nil_append, List.cons_append]
  all_goals first
    | exact target_numeric_fault_then_exact readRight failed zero root _ out
    | simp [NativeWord64.sourceBinary] at refused

theorem lowered_unary_success_exact {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {result : NativeType}
    {frame : TargetFrame} {state : TargetState World} {identity : Nat} {type : NativeType}
    {operand : Atom} (operation : Unary) (input value : SourceValue)
    (read : TargetAtomEval interface frame state operand (encodeValue input))
    (unused : frame.temporaryNames.contains identity = false)
    (computed : sourceUnaryOp operation input = some value)
    (root : List Instruction) (out : TargetBlockOutcome World) :
    TargetRun interface heap calls result root
      [.temporary identity type (.unary operation operand)] frame state out ↔
      out = ⟨.normal, targetDeclareTemporary frame identity (encodeValue value), state⟩ := by
  have targetComputed := (unary_value_result_iff operation input value).mpr computed
  exact target_run_temporary_exact unused (.unary read targetComputed) root out

theorem lowered_comparison_success_exact {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {result : NativeType}
    {frame : TargetFrame} {state : TargetState World} {identity : Nat} {left right : Atom}
    (operation : NativeWord64.Comparison) (first second : SourceValue) (value : Bool)
    (readLeft : TargetAtomEval interface frame state left (encodeValue first))
    (readRight : TargetAtomEval interface frame state right (encodeValue second))
    (unused : frame.temporaryNames.contains identity = false)
    (computed : sourceBinaryOp (.compare operation) first second = some (.ok (.bool value)))
    (root : List Instruction) (out : TargetBlockOutcome World) :
    TargetRun interface heap calls result root
      (NativeLowering.numericGuard (.compare operation) right ++
        [.temporary identity .bool (.binary (.compare operation) left right)]) frame state out ↔
      out = ⟨.normal, targetDeclareTemporary frame identity (.bool value), state⟩ := by
  have targetComputed : targetUncheckedBinary (.compare operation) (encodeValue first)
      (encodeValue second) = some (.bool value) := by
    unfold targetUncheckedBinary
    rw [binary_value_correspondence, computed]
    rfl
  exact target_run_temporary_exact unused (.binary readLeft readRight targetComputed) root out

end Mettapedia.GSLT.LanguageDef.NativeOps
