import Mettapedia.GSLT.LanguageDef.NativeOpsCIdentityScan
import Mettapedia.Machines.OrderedDependencyCPreparationAdmission

/-!
# The retained preparation body's existing and pending identity scans

Both scan nodes are extracted from the independently authored complete
preparation syntax. Execution uses their actual conditions and assignments
through the shared scalar-read fragment. The independent observations are
membership of the initialized old list and membership of the initialized
pending list. This boundary does not execute the surrounding allocation,
append, capacity or cleanup statements.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.OrderedDependencyCPreparationScan

open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC
open ScalarRead IdentityScan
open OrderedDependencyCPreparationSource

variable {Ptr : Type} [DecidableEq Ptr]

def loopBody? : CStatement → Option (List CStatement)
  | .forLoop _ _ _ _ _ body => some body
  | _ => none

def scanAt (function : CDeclaratorFunction) (outer inner : Nat) : Option CStatement := do
  let loop ← function.body[outer]?
  let body ← loopBody? loop
  body[inner]?

def existingScan : Option CStatement := scanAt preparationFunction 10 3

def validationScan : Option CStatement := scanAt preparationFunction 3 3

def pendingScan : Option CStatement := scanAt preparationFunction 10 4

def quotedScan (outer inner : Nat) : Option CStatement :=
  (declaratorFunctionText? typeNames preparationSource.toList).bind
    (fun function => scanAt function outer inner)

theorem quoted_existing_node_is_actual : quotedScan 10 3 = existingScan := by
  rw [quotedScan, complete_preparation_source_admitted]
  rfl

theorem quoted_pending_node_is_actual : quotedScan 10 4 = pendingScan := by
  rw [quotedScan, complete_preparation_source_admitted]
  rfl

theorem quoted_validation_node_is_actual : quotedScan 3 3 = validationScan := by
  rw [quotedScan, complete_preparation_source_admitted]
  rfl

def oldArray : CExpr := .field (.identifier "importer".toList) "deps".toList true
def oldLimit : CExpr := .field (.identifier "importer".toList) "dep_count".toList true
def pendingArray : CExpr := .identifier "pending".toList
def pendingLimit : CExpr := .identifier "added".toList
def needle : CExpr := .identifier "dependency".toList

theorem existing_node_is_retained :
    existingScan = some (scanStatement oldArray oldLimit needle) := rfl

theorem validation_uses_same_retained_scan : validationScan = existingScan := rfl

theorem pending_node_is_retained :
    pendingScan = some (scanStatement pendingArray pendingLimit needle) := rfl

def bindings (reader source : Ptr) (pending : List Ptr) (added : UInt32) : Environment Ptr :=
  fun name => if name = "importer".toList then some (.identity (some reader))
    else if name = "dependency".toList then some (.identity (some source))
    else if name = "pending".toList then some (.identities (pending.map some))
    else if name = "added".toList then some (.unsigned added) else none

def fields (reader : Ptr) (existing : List Ptr) (count : UInt32) : FieldReader Ptr :=
  fun owner name => if owner = reader then
    if name = "deps".toList then some (.identities (existing.map some))
    else if name = "dep_count".toList then some (.unsigned count) else none
  else none

theorem existing_operands (reader source : Ptr) (existing pending : List Ptr)
    (count added : UInt32) :
    Operands (bindings reader source pending added) (fields reader existing count)
      oldArray oldLimit needle (existing.map some) count (some source) := by
  constructor <;> intro index seen <;>
    simp [oldArray, oldLimit, needle, expression, locals, bindings, fields, counter, flag]

theorem pending_operands (reader source : Ptr) (existing pending : List Ptr)
    (count added : UInt32) :
    Operands (bindings reader source pending added) (fields reader existing count)
      pendingArray pendingLimit needle (pending.map some) added (some source) := by
  constructor <;> intro index seen <;>
    simp [pendingArray, pendingLimit, needle, expression, locals, bindings, counter, flag]

def executeNode (node : Option CStatement) (reader source : Ptr)
    (existing pending : List Ptr) (count added : UInt32)
    (savedCounter : UInt32) (seen : Bool) (fuel : Nat) : Option (Result Ptr) :=
  node.bind (countedLoop (fields reader existing count) fuel
    (locals (bindings reader source pending added) savedCounter seen))

theorem existing_scan_refines_membership (reader source : Ptr) (existing pending : List Ptr)
    (count added savedCounter : UInt32) (seen : Bool)
    (exactCount : count.toNat = existing.length) :
    executeNode existingScan reader source existing pending count added savedCounter seen
      existing.length = some (.finished (some
        (locals (bindings reader source pending added) savedCounter
          (decide (seen = true ∨ source ∈ existing))))) := by
  rw [executeNode, existing_node_is_retained]
  simp only [Option.bind_some]
  have bound : count.toNat = (existing.map some).length := by simpa using exactCount
  simpa using counted_scan_refines_membership
    (existing_operands reader source existing pending count added) bound savedCounter seen

theorem pending_scan_refines_membership (reader source : Ptr) (existing pending : List Ptr)
    (count added savedCounter : UInt32) (seen : Bool)
    (exactAdded : added.toNat = pending.length) :
    executeNode pendingScan reader source existing pending count added savedCounter seen
      pending.length = some (.finished (some
        (locals (bindings reader source pending added) savedCounter
          (decide (seen = true ∨ source ∈ pending))))) := by
  rw [executeNode, pending_node_is_retained]
  simp only [Option.bind_some]
  have bound : added.toNat = (pending.map some).length := by simpa using exactAdded
  simpa using counted_scan_refines_membership
    (pending_operands reader source existing pending count added) bound savedCounter seen

/-- Spare slots are retained in the reader service but excluded by the actual
counter test. An identity in unused capacity is not an existing dependency. -/
theorem existing_scan_refines_active_slots (reader source : Ptr)
    (array : PostIndex.Array32 Ptr) (pending : List Ptr)
    (added savedCounter : UInt32) (seen : Bool)
    (liveCount : array.count.toNat ≤ array.slots.length) :
    executeNode existingScan reader source array.slots pending array.count added
      savedCounter seen array.count.toNat = some (.finished (some
        (locals (bindings reader source pending added) savedCounter
          (decide (seen = true ∨ source ∈ array.active))))) := by
  rw [executeNode, existing_node_is_retained]
  simp only [Option.bind_some]
  exact counted_scan_refines_pointer_slots array source
    (existing_operands reader source array.slots pending array.count added) liveCount savedCounter seen

theorem pending_scan_refines_active_slots (reader source : Ptr) (existing : List Ptr)
    (array : PostIndex.Array32 Ptr) (count savedCounter : UInt32) (seen : Bool)
    (liveCount : array.count.toNat ≤ array.slots.length) :
    executeNode pendingScan reader source existing array.slots count array.count
      savedCounter seen array.count.toNat = some (.finished (some
        (locals (bindings reader source array.slots array.count) savedCounter
          (decide (seen = true ∨ source ∈ array.active))))) := by
  rw [executeNode, pending_node_is_retained]
  simp only [Option.bind_some]
  exact counted_scan_refines_pointer_slots array source
    (pending_operands reader source existing array.slots count array.count) liveCount savedCounter seen

theorem quoted_existing_scan_refines_active_slots (reader source : Ptr)
    (array : PostIndex.Array32 Ptr) (pending : List Ptr)
    (added savedCounter : UInt32) (seen : Bool)
    (liveCount : array.count.toNat ≤ array.slots.length) :
    executeNode (quotedScan 10 3) reader source array.slots pending array.count added
      savedCounter seen array.count.toNat = some (.finished (some
        (locals (bindings reader source pending added) savedCounter
          (decide (seen = true ∨ source ∈ array.active))))) := by
  rw [quoted_existing_node_is_actual]
  exact existing_scan_refines_active_slots reader source array pending added savedCounter seen liveCount

theorem quoted_pending_scan_refines_active_slots (reader source : Ptr) (existing : List Ptr)
    (array : PostIndex.Array32 Ptr) (count savedCounter : UInt32) (seen : Bool)
    (liveCount : array.count.toNat ≤ array.slots.length) :
    executeNode (quotedScan 10 4) reader source existing array.slots count array.count
      savedCounter seen array.count.toNat = some (.finished (some
        (locals (bindings reader source array.slots array.count) savedCounter
          (decide (seen = true ∨ source ∈ array.active))))) := by
  rw [quoted_pending_node_is_actual]
  exact pending_scan_refines_active_slots reader source existing array count savedCounter seen liveCount

theorem consecutive_active_scans_refine_union (reader source : Ptr)
    (existing pending : PostIndex.Array32 Ptr) (savedCounter : UInt32)
    (oldLive : existing.count.toNat ≤ existing.slots.length)
    (pendingLive : pending.count.toNat ≤ pending.slots.length) :
    let base := bindings reader source pending.slots pending.count
    let readerFields := fields reader existing.slots existing.count
    (existingScan.bind (countedLoop readerFields existing.count.toNat
      (locals base savedCounter false))).bind (fun result =>
        match result with
        | .finished (some environment) => pendingScan.bind
            (countedLoop readerFields pending.count.toNat environment)
        | _ => none) = some (.finished (some
          (locals base savedCounter
            (decide (source ∈ existing.active ∨ source ∈ pending.active))))) := by
  change (executeNode existingScan reader source existing.slots pending.slots existing.count
    pending.count savedCounter false existing.count.toNat).bind _ = _
  rw [existing_scan_refines_active_slots reader source existing pending.slots pending.count
    savedCounter false oldLive]
  simp only [Bool.false_eq_true, false_or, Option.bind_some]
  change executeNode pendingScan reader source existing.slots pending.slots existing.count
    pending.count savedCounter (decide (source ∈ existing.active)) pending.count.toNat = _
  rw [pending_scan_refines_active_slots reader source existing.slots pending existing.count
    savedCounter (decide (source ∈ existing.active)) pendingLive]
  simp

/-- The old scan can stop true; the pending scan must then skip its body.
An initialized pending list is required for the general second-read contract. -/
theorem consecutive_actual_scans_refine_union (reader source : Ptr)
    (existing pending : List Ptr) (count added savedCounter : UInt32)
    (exactCount : count.toNat = existing.length) (exactAdded : added.toNat = pending.length) :
    let base := bindings reader source pending added
    let readerFields := fields reader existing count
    (existingScan.bind (countedLoop readerFields existing.length
      (locals base savedCounter false))).bind (fun result =>
        match result with
        | .finished (some environment) => pendingScan.bind
            (countedLoop readerFields pending.length environment)
        | _ => none) = some (.finished (some
          (locals base savedCounter (decide (source ∈ existing ∨ source ∈ pending))))) := by
  change (executeNode existingScan reader source existing pending count added savedCounter
    false existing.length).bind _ = _
  rw [existing_scan_refines_membership reader source existing pending count added savedCounter
    false exactCount]
  simp only [Bool.false_eq_true, false_or, Option.bind_some]
  change executeNode pendingScan reader source existing pending count added savedCounter
    (decide (source ∈ existing)) pending.length = _
  rw [pending_scan_refines_membership reader source existing pending count added savedCounter
    (decide (source ∈ existing)) exactAdded]
  simp

def observeFlag : Result Ptr → Option Bool
  | .finished (some environment) => (environment flag).bind truth?
  | _ => none

namespace Controls

theorem old_membership_survives_empty_pending :
    (executeNode existingScan (0 : Nat) 1 [1, 2] [] 2 0 91 false 2).bind observeFlag =
      some true := by decide +kernel

theorem pending_duplicate_is_seen :
    (executeNode pendingScan (0 : Nat) 2 [] [1, 2] 0 2 91 false 2).bind observeFlag =
      some true := by decide +kernel

theorem absent_identity_is_not_invented :
    (executeNode pendingScan (0 : Nat) 3 [] [1, 2] 0 2 91 false 2).bind observeFlag =
      some false := by decide +kernel

theorem previously_seen_skips_invalid_array_extent :
    (executeNode pendingScan (0 : Nat) 1 [] [] 0 1 91 true 0).bind observeFlag =
      some true := by decide +kernel

theorem bad_extent_without_short_circuit_has_no_execution :
    executeNode pendingScan (0 : Nat) 1 [] [] 0 1 91 false 1 =
      some (.finished none) := rfl

def withoutAssignment : Option CStatement :=
  some (.forLoop ⟨"uint32_t".toList, 0⟩ counter (.unsignedInteger 0)
    (condition pendingLimit) step [])

theorem removed_assignment_changes_actual_observation :
    (executeNode withoutAssignment (0 : Nat) 2 [] [1, 2] 0 2 91 false 2).bind observeFlag =
      some false := by decide +kernel

def changedNeedle : Option CStatement :=
  some (scanStatement pendingArray pendingLimit (.identifier "importer".toList))

theorem changed_identity_operand_changes_actual_observation :
    (executeNode changedNeedle (0 : Nat) 2 [] [1, 2] 0 2 91 false 2).bind observeFlag =
      some false := by decide +kernel

theorem declaration_restores_shadowed_counter :
    (executeNode pendingScan (0 : Nat) 2 [] [1, 2] 0 2 91 false 2).bind
      (fun result => match result with
        | .finished (some environment) => environment counter
        | _ => none) = some (.unsigned 91) := by decide +kernel

theorem spare_identity_is_not_an_existing_dependency :
    (executeNode existingScan (0 : Nat) 3 [1, 3] [] 1 0 91 false 1).bind observeFlag =
      some false := by decide +kernel

theorem confusing_capacity_with_count_changes_membership :
    (executeNode existingScan (0 : Nat) 3 [1, 3] [] 2 0 91 false 2).bind observeFlag =
      some true := by decide +kernel

theorem spare_identity_is_not_a_pending_duplicate :
    (executeNode pendingScan (0 : Nat) 3 [] [1, 3] 0 1 91 false 1).bind observeFlag =
      some false := by decide +kernel

theorem confusing_pending_capacity_with_added_changes_membership :
    (executeNode pendingScan (0 : Nat) 3 [] [1, 3] 0 2 91 false 2).bind observeFlag =
      some true := by decide +kernel

end Controls

#print axioms existing_node_is_retained
#print axioms validation_uses_same_retained_scan
#print axioms pending_node_is_retained
#print axioms quoted_existing_node_is_actual
#print axioms quoted_pending_node_is_actual
#print axioms quoted_validation_node_is_actual
#print axioms existing_operands
#print axioms pending_operands
#print axioms existing_scan_refines_membership
#print axioms pending_scan_refines_membership
#print axioms existing_scan_refines_active_slots
#print axioms pending_scan_refines_active_slots
#print axioms quoted_existing_scan_refines_active_slots
#print axioms quoted_pending_scan_refines_active_slots
#print axioms consecutive_active_scans_refine_union
#print axioms consecutive_actual_scans_refine_union
#print axioms Controls.old_membership_survives_empty_pending
#print axioms Controls.pending_duplicate_is_seen
#print axioms Controls.absent_identity_is_not_invented
#print axioms Controls.previously_seen_skips_invalid_array_extent
#print axioms Controls.bad_extent_without_short_circuit_has_no_execution
#print axioms Controls.removed_assignment_changes_actual_observation
#print axioms Controls.changed_identity_operand_changes_actual_observation
#print axioms Controls.declaration_restores_shadowed_counter
#print axioms Controls.spare_identity_is_not_an_existing_dependency
#print axioms Controls.confusing_capacity_with_count_changes_membership
#print axioms Controls.spare_identity_is_not_a_pending_duplicate
#print axioms Controls.confusing_pending_capacity_with_added_changes_membership

end Mettapedia.Machines.OrderedDependencyCPreparationScan
