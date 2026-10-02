import Mettapedia.GSLT.LanguageDef.NativeExecutionPublication
import Mettapedia.GSLT.LanguageDef.NativeOpsAllocationGuards

/-!
The native execution wrapper and physical callee's entry refusals in the
64-bit size_t profile. The wrapper checks scope/output pointers and allocates
its node before the callee validates borrowed inputs or the output extent.
These guards do not dereference input contents or the caller's output slot.
Successful prefixes still require allocation, copying, mapping, execution and
publication; those effects are not hidden in an entry-guard contract.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeExecutionEntryGuards

open NativeOps (Address)
open NativeWord64 (Word encode bound)

structure SourceBytes where
  pointer : Option Address
  length : Word
  deriving DecidableEq, Repr

structure TargetBytes where
  pointer : Option Address
  length : BitVec 64
  deriving DecidableEq, Repr

def encodeBytes (bytes : SourceBytes) : TargetBytes := ⟨bytes.pointer, encode bytes.length⟩

def sourceValid (bytes : SourceBytes) : Bool :=
  decide (bytes.length.val < bound) && (bytes.length.val == 0 || bytes.pointer.isSome)

def targetValid (bytes : TargetBytes) : Bool :=
  decide (bytes.length ≤ BitVec.allOnes 64) &&
    (bytes.length == 0 || bytes.pointer.isSome)

theorem bytes_valid_correspondence (bytes : SourceBytes) :
    targetValid (encodeBytes bytes) = sourceValid bytes := by
  have finite : bytes.length.val < bound := bytes.length.isLt
  have belowMaximum : encode bytes.length ≤ BitVec.allOnes 64 := by
    rw [BitVec.le_def, NativeWord64.encode_toNat, BitVec.toNat_allOnes]
    have positive : 0 < bound := Nat.two_pow_pos 64
    change bytes.length.val ≤ bound - 1
    omega
  have zero : (encode bytes.length == 0) = (bytes.length.val == 0) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, NativeWord64.encode_eq_zero]
  simp only [targetValid, sourceValid, encodeBytes, belowMaximum, finite, decide_true,
    Bool.true_and, zero]

def sourcePhysical (output : Option Address) (code input1 input2 : SourceBytes)
    (length : Word) : Option Word :=
  if output.isNone || !sourceValid code || !sourceValid input1 || !sourceValid input2 then some 1
  else if bound ≤ length.val + 8 then some 2 else none

def targetPhysical (output : Option Address) (code input1 input2 : TargetBytes)
    (length : BitVec 64) : Option (BitVec 64) :=
  if output.isNone then some 1
  else if targetValid code = false then some 1
  else if targetValid input1 = false then some 1
  else if targetValid input2 = false then some 1
  else if BitVec.allOnes 64 - 8 < length then some 2 else none

theorem output_extent_correspondence (length : Word) :
    BitVec.allOnes 64 - 8 < encode length ↔ bound ≤ length.val + 8 := by
  have guard := NativeOpsAllocationGuards.additive_capacity_guard (8 : Word) length
  change BitVec.allOnes 64 - 8 < encode length ↔ bound ≤ 8 + length.val at guard
  simpa only [Nat.add_comm] using guard

theorem physical_guard_correspondence (output : Option Address) (code input1 input2 : SourceBytes)
    (length : Word) :
    targetPhysical output (encodeBytes code) (encodeBytes input1) (encodeBytes input2)
      (encode length) = (sourcePhysical output code input1 input2 length).map encode := by
  simp only [targetPhysical, sourcePhysical, bytes_valid_correspondence, output_extent_correspondence]
  by_cases overflow : bound ≤ length.val + 8 <;>
    cases output <;> cases sourceValid code <;> cases sourceValid input1 <;>
    cases sourceValid input2 <;> simp only [Option.isNone_none, Option.isNone_some, Bool.not_true,
      Bool.not_false, Bool.true_or, Bool.false_or, Bool.false_eq_true, Bool.or_false, if_true,
      if_false, Bool.true_eq_false, overflow, Option.map_some, Option.map_none] <;> rfl

def sourcePrefix (scope caller : Option Address) (nodeAvailable : Bool)
    (code input1 input2 : SourceBytes) (length : Word) : Option Word :=
  match NativeExecutionPublication.sourcePrecheck scope caller with
  | some status => some status
  | none => if nodeAvailable then sourcePhysical (some ⟨0, 0, []⟩) code input1 input2 length
    else some 2

def targetPrefix (scope caller : Option Address) (nodeAvailable : Bool)
    (code input1 input2 : TargetBytes) (length : BitVec 64) : Option (BitVec 64) :=
  match NativeExecutionPublication.targetPrecheck scope caller with
  | some status => some status
  | none => if nodeAvailable = false then some 2
    else targetPhysical (some ⟨0, 0, []⟩) code input1 input2 length

theorem wrapper_prefix_correspondence (scope caller : Option Address) (nodeAvailable : Bool)
    (code input1 input2 : SourceBytes) (length : Word) :
    targetPrefix scope caller nodeAvailable (encodeBytes code) (encodeBytes input1)
        (encodeBytes input2) (encode length) =
      (sourcePrefix scope caller nodeAvailable code input1 input2 length).map encode := by
  simp only [targetPrefix, sourcePrefix, NativeExecutionPublication.precheck_correspondence]
  cases NativeExecutionPublication.sourcePrecheck scope caller with
  | some status => rfl
  | none =>
    simp only [Option.map_none]
    cases nodeAvailable with
    | false => rfl
    | true =>
      simp only [Bool.true_eq_false, if_false, if_true]
      exact physical_guard_correspondence _ code input1 input2 length

private def pointer : Address := ⟨1, 0, []⟩
private def empty : SourceBytes := ⟨none, 0⟩
private def invalid : SourceBytes := ⟨none, 1⟩
private def maximal : Word := ⟨bound - 1, by
  change bound - 1 < bound
  have p : 0 < bound := Nat.two_pow_pos 64
  omega⟩

theorem empty_null_bytes_are_valid : sourceValid empty = true := rfl

theorem nonempty_null_bytes_are_invalid : sourceValid invalid = false := rfl

theorem null_output_precedes_node_allocation :
    sourcePrefix (some pointer) none false invalid invalid invalid maximal = some 1 := rfl

theorem node_resource_failure_precedes_input_validation :
    sourcePrefix (some pointer) (some pointer) false invalid invalid invalid maximal = some 2 := rfl

theorem valid_node_allocation_exposes_input_refusal :
    sourcePrefix (some pointer) (some pointer) true invalid empty empty 0 = some 1 := rfl

theorem maximal_output_refused_without_wraparound :
    sourcePhysical (some pointer) empty empty empty maximal = some 2 := by decide +kernel

theorem zero_output_passes_entry_guards :
    sourcePrefix (some pointer) (some pointer) true empty empty empty 0 = none := rfl

end Mettapedia.GSLT.LanguageDef.NativeExecutionEntryGuards
