import Mettapedia.GSLT.LanguageDef.CompiledPlanAdmission
import Mettapedia.GSLT.LanguageDef.CompiledPlanLowering
import Mettapedia.GSLT.LanguageDef.FiniteSupportBitVecCompilation

/-!
# Packed finite-support admission for compiled plans

The compiled-plan wire format declares a finite dense variable inventory for
each rule.  Structural admission currently states that property with lists:
every used slot is in range and every declared slot occurs.  This module
derives the equivalent packed representation from that local property.

The result licenses a generic runtime implementation with one bit per dense
slot.  No source-language variable name, proof rule, or guest vocabulary is
part of the transformation.
-/

namespace Mettapedia.GSLT.LanguageDef.CompiledPlanFiniteSupportCompilation

open CompiledPlanAdmission
open CompiledPlanLowering
open FiniteEnvironmentCompilation
open FiniteSupportBitVecCompilation

/-- The generated inventory for a rule declaring `width` dense slots. -/
def slotInventory (width : Nat) : Inventory Nat where
  keys := List.range width
  nodup := List.nodup_range

/-- Packed admission performs the two independent obligations of dense
variable admission: every observed slot is declared, and every declared slot
is observed. -/
def packedDenseVariables (width : Nat) (usedVariables : List Nat) : Bool :=
  let inventory := slotInventory width
  supported? inventory usedVariables &&
    packedFull? inventory (encode inventory usedVariables)

/-- The finite-support recognizer is exactly the in-range half of dense
compiled-plan admission. -/
theorem supported?_slotInventory_eq_true_iff
    (width : Nat) (usedVariables : List Nat) :
    supported? (slotInventory width) usedVariables = true ↔
      usedVariables.all (fun slot => slot < width) = true := by
  rw [supported?_eq_true_iff, List.all_eq_true]
  simp [slotInventory, List.mem_range]

/-- Full packed coverage is exactly the no-holes half of dense
compiled-plan admission. -/
theorem packedFull?_slotInventory_encode_eq_true_iff
    (width : Nat) (usedVariables : List Nat) :
    packedFull? (slotInventory width)
        (encode (slotInventory width) usedVariables) = true ↔
      (List.range width).all
        (fun slot => usedVariables.contains slot) = true := by
  rw [packedFull?_encode_eq_true_iff, List.all_eq_true]
  simp [slotInventory, List.contains_eq_mem]

/-- Packed support admission accepts exactly the structurally admitted dense
variable lists.  This is the representation-refinement certificate used by
the generic C plan loader. -/
theorem packedDenseVariables_eq_true_iff
    (width : Nat) (usedVariables : List Nat) :
    packedDenseVariables width usedVariables = true ↔
      denseVariables width usedVariables = true := by
  simp only [packedDenseVariables, Bool.and_eq_true]
  rw [supported?_slotInventory_eq_true_iff,
    packedFull?_slotInventory_encode_eq_true_iff]
  simp [denseVariables, Bool.and_eq_true]

/-- Variable observations made by one typed source rule, in structural source
order.  Repetition is retained because dense admission permits repeated uses. -/
def ruleUsedVariables (rule : TypedRule) : List Nat :=
  termUsedVariables rule.head ++ rule.body.flatMap termUsedVariables

/-- The ordinary typed-rule recognizer directly licenses packed dense support
for that rule.  No additional guest-specific analysis is required. -/
theorem packedDenseVariables_of_rule_locallySupported
    (rule : TypedRule) (supported : rule.locallySupported = true) :
    packedDenseVariables rule.variableCount.toNat
      (ruleUsedVariables rule) = true := by
  apply (packedDenseVariables_eq_true_iff
    rule.variableCount.toNat (ruleUsedVariables rule)).2
  have dense :
      denseVariables rule.variableCount.toNat
        (termUsedVariables rule.head ++
          rule.body.flatMap termUsedVariables) = true := by
    simp [TypedRule.locallySupported] at supported
    aesop
  exact dense

/-! ## Positive and negative structural canaries -/

/-- Repeated and out-of-order observations still cover a dense inventory. -/
example : packedDenseVariables 5 [4, 1, 0, 3, 2, 4] = true := by
  decide

/-- Missing declared slots fail the packed coverage test. -/
example : packedDenseVariables 5 [1, 2] = false := by
  decide

/-- An out-of-range observation fails even when all lower slots occur. -/
example : packedDenseVariables 3 [0, 1, 2, 3] = false := by
  decide

end Mettapedia.GSLT.LanguageDef.CompiledPlanFiniteSupportCompilation
