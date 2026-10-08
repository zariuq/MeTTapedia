import Mettapedia.Machines.OrderedDependencyCPreparationAdmission
import Mettapedia.GSLT.LanguageDef.NativeOpsCLocalLoop
import Mettapedia.Machines.OrderedDependencyCReserve

/-!
# Executed unsigned growth in retained dependency reservation source

The actual reserve helper's while condition, boundary branch, assignment,
break and compound multiplication execute through the shared typed C services.
Their result is related to the independent natural-number growth algorithm.
The positive starting-capacity requirement remains explicit until the initial
pointee read and declaration are connected. Allocation, byte-size checks and
physical pointer/layout contracts are separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.OrderedDependencyCReserveGrowth

open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC
open ScalarRead
open PostIndex
open OrderedDependencyCapacity OrderedDependencyCPreparationSource

variable {Ptr : Type} [DecidableEq Ptr]

def condition : CExpr := .binary .lt (.identifier "next".toList) (.identifier "required".toList)

def boundary : CExpr := .binary .gt (.identifier "next".toList)
  (.binary .div (.identifier "UINT32_MAX".toList) (.unsignedInteger 2))

def body : List CStatement := [
  .branch boundary [.assign (.identifier "next".toList) (.identifier "required".toList), .break] [],
  .compoundAssign .mul (.identifier "next".toList) (.unsignedInteger 2)]

def actualLoop : Option CStatement := reserveFunction.body[2]?

theorem actual_loop_is_retained : actualLoop = some (.whileLoop condition body) := rfl

def quotedLoop : Option CStatement :=
  (declaratorFunctionText? typeNames reserveSource.toList).bind fun function => function.body[2]?

theorem quoted_loop_is_actual : quotedLoop = actualLoop := by
  rw [quotedLoop, complete_reserve_source_admitted]
  rfl

def frame (base : Environment Ptr) (required next : UInt32) : Environment Ptr :=
  Function.update (Function.update (Function.update base "UINT32_MAX".toList
    (some (.unsigned 4294967295))) "required".toList (some (.unsigned required)))
    "next".toList (some (.unsigned next))

omit [DecidableEq Ptr] in
theorem frame_next (base : Environment Ptr) (required next : UInt32) :
    frame base required next "next".toList = some (.unsigned next) := rfl

omit [DecidableEq Ptr] in
theorem frame_required (base : Environment Ptr) (required next : UInt32) :
    frame base required next "required".toList = some (.unsigned required) := rfl

omit [DecidableEq Ptr] in
theorem frame_maximum (base : Environment Ptr) (required next : UInt32) :
    frame base required next "UINT32_MAX".toList = some (.unsigned 4294967295) := rfl

omit [DecidableEq Ptr] in
theorem frame_updates_next (base : Environment Ptr) (required next after : UInt32) :
    Function.update (frame base required next) "next".toList (some (.unsigned after)) =
      frame base required after := by simp only [frame, Function.update_idem]

theorem condition_reads_actual_operands (base : Environment Ptr) (fields : FieldReader Ptr)
    (required next : UInt32) :
    (expression (frame base required next) fields condition).bind truth? =
      some (decide (next < required)) := by
  simp only [condition, expression, frame_next, frame_required, numericBinary,
    truth?, bind, Option.bind, ↓reduceIte]

theorem boundary_reads_actual_division (base : Environment Ptr) (fields : FieldReader Ptr)
    (required next : UInt32) :
    (expression (frame base required next) fields boundary).bind truth? =
      some (decide (2147483647 < next)) := by
  simp only [boundary, expression, frame_next, frame_maximum, bind, Option.bind]
  rfl

theorem high_iteration_assigns_and_breaks (base : Environment Ptr) (fields : FieldReader Ptr)
    (required next : UInt32) (high : 2147483647 < next) :
    LocalBlock.execute fields 4 (frame base required next) body =
      .finished (some (.broken (frame base required required))) := by
  rw [show body = .branch boundary
      [.assign (.identifier "next".toList) (.identifier "required".toList), .break] [] ::
      [.compoundAssign .mul (.identifier "next".toList) (.unsignedInteger 2)] from rfl,
    LocalBlock.branch_executes_retained_continuation fields 3 _ _ _ _ _ true
      (by simp [boundary_reads_actual_division, high])]
  rw [if_pos (rfl : true = true)]
  simp only [LocalBlock.execute, LocalBlock.assign, assignment, expression,
    frame_next, frame_required, assignValue?, frame_updates_next, LocalBlock.resume, bind, Option.bind]

theorem low_iteration_executes_unsigned_multiplication (base : Environment Ptr)
    (fields : FieldReader Ptr) (required next : UInt32) (low : ¬2147483647 < next) :
    LocalBlock.execute fields 4 (frame base required next) body =
      .finished (some (.next (frame base required (next * 2)))) := by
  rw [show body = .branch boundary
      [.assign (.identifier "next".toList) (.identifier "required".toList), .break] [] ::
      [.compoundAssign .mul (.identifier "next".toList) (.unsignedInteger 2)] from rfl,
    LocalBlock.branch_executes_retained_continuation fields 3 _ _ _ _ _ false
      (by simp [boundary_reads_actual_division, low])]
  rw [if_neg Bool.false_ne_true]
  have assigned := unsigned_multiply_assignment_reads_actual_operands
    (frame base required next) fields "next".toList (.unsignedInteger 2) next 2
    (frame_next base required next) (by rfl)
  rw [frame_updates_next] at assigned
  simp only [LocalBlock.execute, LocalBlock.resume, LocalBlock.assign, assigned]

/-- Completion executes the retained statements. Positive capacity is needed:
zero doubled forever would never reach a positive request. -/
theorem actual_growth_refines_independent_algorithm (base : Environment Ptr)
    (fields : FieldReader Ptr) (required : UInt32) (fuel : Nat) :
    ∀ next : UInt32, 0 < next.toNat → required.toNat ≤ next.toNat * 2 ^ fuel →
      ∃ after : UInt32, after.toNat = grow required.toNat next.toNat ∧
        LocalLoop.whileRun fields condition body 4 fuel (frame base required next) =
          .finished (some (.next (frame base required after))) := by
  induction fuel with
  | zero =>
      intro next _ enough
      have fits : required.toNat ≤ next.toNat := by simpa using enough
      refine ⟨next, (sufficient_capacity_is_unchanged _ _ fits).symm, ?_⟩
      apply LocalLoop.while_false_condition_skips_body
      simp [condition_reads_actual_operands, UInt32.lt_iff_toNat_lt, Nat.not_lt.mpr fits]
  | succ fuel ih =>
      intro next positive enough
      by_cases pending : next < required
      · have pendingNat : next.toNat < required.toNat := UInt32.lt_iff_toNat_lt.mp pending
        have test : (expression (frame base required next) fields condition).bind truth? =
            some true := by simp [condition_reads_actual_operands, pending]
        by_cases high : 2147483647 < next
        · have highNat : next.toNat > maximum / 2 := by
            simpa [maximum, UInt32.lt_iff_toNat_lt] using high
          refine ⟨required, ?_, ?_⟩
          · rw [grow]
            simp [pendingNat, highNat]
          · exact LocalLoop.while_break_completes fields condition body 4 fuel _ _ test
              (high_iteration_assigns_and_breaks base fields required next high)
        · have exactDouble : (next * 2).toNat = next.toNat * 2 := by
            have step := unsignedStep_realizes_natural_step required next
            have lowNat : ¬next.toNat > maximum / 2 := by
              simpa [maximum, UInt32.lt_iff_toNat_lt] using high
            simpa [unsignedStep, high, lowNat] using step
          have positiveDouble : 0 < (next * 2).toNat := by rw [exactDouble]; omega
          have remaining : required.toNat ≤ (next * 2).toNat * 2 ^ fuel := by
            rw [exactDouble]
            simpa [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using enough
          obtain ⟨after, agrees, completed⟩ := ih (next * 2) positiveDouble remaining
          refine ⟨after, ?_, ?_⟩
          · have lowNat : ¬next.toNat > maximum / 2 := by
              simpa [maximum, UInt32.lt_iff_toNat_lt] using high
            rw [grow, dif_pos pendingNat, if_neg lowNat, dif_pos positive]
            rw [exactDouble] at agrees
            exact agrees
          · rw [LocalLoop.while_true_condition_executes_body fields condition body 4 fuel _ _ test
                (low_iteration_executes_unsigned_multiplication base fields required next high)]
            exact completed
      · refine ⟨next, ?_, ?_⟩
        · have fits : required.toNat ≤ next.toNat := by
            simpa [UInt32.lt_iff_toNat_lt] using pending
          exact (sufficient_capacity_is_unchanged _ _ fits).symm
        · apply LocalLoop.while_false_condition_skips_body
          simp [condition_reads_actual_operands, pending]

def execute (node : Option CStatement) (fields : FieldReader Ptr) (fuel : Nat)
    (base : Environment Ptr) (required next : UInt32) : Option (LocalBlock.Result Ptr) :=
  node.bind (LocalLoop.whileStatement fields 4 fuel (frame base required next))

theorem retained_growth_covers_and_preserves_capacity (base : Environment Ptr)
    (fields : FieldReader Ptr) (required next : UInt32) (fuel : Nat)
    (positive : 0 < next.toNat) (enough : required.toNat ≤ next.toNat * 2 ^ fuel) :
    ∃ after : UInt32,
      execute actualLoop fields fuel base required next =
        some (.finished (some (.next (frame base required after)))) ∧
      after.toNat = grow required.toNat next.toNat ∧
      required.toNat ≤ after.toNat ∧ next.toNat ≤ after.toNat ∧ after.toNat ≤ maximum := by
  obtain ⟨after, agrees, completed⟩ :=
    actual_growth_refines_independent_algorithm base fields required fuel next positive enough
  refine ⟨after, ?_, agrees, ?_, ?_, ?_⟩
  · simp [execute, actual_loop_is_retained, LocalLoop.whileStatement, completed]
  · rw [agrees]; exact grow_covers_request _ _
  · rw [agrees]; exact grow_preserves_capacity _ _
  · have bound := after.toNat_lt
    simp only [maximum]
    omega

/-- Every positive uint32 starting capacity completes within 32 body
iterations, including the near-overflow branch. No capacity-proportional
execution budget is needed. -/
theorem retained_growth_completes_with_32_iterations (base : Environment Ptr)
    (fields : FieldReader Ptr) (required next : UInt32) (positive : 0 < next.toNat) :
    ∃ after : UInt32,
      execute actualLoop fields 32 base required next =
        some (.finished (some (.next (frame base required after)))) ∧
      after.toNat = grow required.toNat next.toNat ∧
      required.toNat ≤ after.toNat ∧ next.toNat ≤ after.toNat ∧ after.toNat ≤ maximum := by
  apply retained_growth_covers_and_preserves_capacity base fields required next 32 positive
  have bound := required.toNat_lt
  norm_num at bound ⊢
  omega

theorem quoted_growth_executes_retained_loop (base : Environment Ptr)
    (fields : FieldReader Ptr) (required next : UInt32) (fuel : Nat) :
    execute quotedLoop fields fuel base required next =
      execute actualLoop fields fuel base required next := by rw [quoted_loop_is_actual]

/-- The logical array boundary supplies the starting capacity. This definition
does not claim execution of the C pointee read or local declaration. -/
def startingCapacity {Value : Type} (before : Array32 Value) : UInt32 :=
  if before.slots.length = 0 then 4 else UInt32.ofNat before.slots.length

omit [DecidableEq Ptr] in
theorem starting_capacity_has_exact_extent {Value : Type} (before : Array32 Value)
    (sized : before.Sized) :
    (startingCapacity before).toNat = if before.slots.length = 0 then 4 else before.slots.length := by
  by_cases empty : before.slots.length = 0
  · simp [startingCapacity, empty]
  · have bound : before.slots.length < 2 ^ 32 := by
      change before.slots.length ≤ 4294967295 at sized
      omega
    simp only [startingCapacity, if_neg empty]
    exact Nat.mod_eq_of_lt bound

omit [DecidableEq Ptr] in
theorem starting_capacity_is_positive {Value : Type} (before : Array32 Value)
    (sized : before.Sized) : 0 < (startingCapacity before).toNat := by
  rw [starting_capacity_has_exact_extent before sized]
  split <;> omega

/-- The actual loop produces the extent subsequently requested by the logical
fallible allocator service. Its value is derived from executed C statements. -/
theorem executed_growth_supplies_allocator_request {Value : Type}
    (base : Environment Ptr) (fields : FieldReader Ptr) (before : Array32 Value)
    (required : UInt32) (sized : before.Sized) :
    ∃ capacity : UInt32,
      execute actualLoop fields 32 base required (startingCapacity before) =
        some (.finished (some (.next (frame base required capacity)))) ∧
      capacity.toNat = OrderedDependencyCReserve.chosenCapacity before required ∧
      required.toNat ≤ capacity.toNat ∧ before.slots.length ≤ capacity.toNat ∧
      capacity.toNat ≤ maximum := by
  obtain ⟨capacity, completed, agrees, covers, _, bounded⟩ :=
    retained_growth_completes_with_32_iterations base fields required (startingCapacity before)
      (starting_capacity_is_positive before sized)
  have chosen : capacity.toNat = OrderedDependencyCReserve.chosenCapacity before required := by
    rw [agrees, starting_capacity_has_exact_extent before sized]
    rfl
  refine ⟨capacity, completed, chosen, covers, ?_, bounded⟩
  rw [chosen]
  exact OrderedDependencyCReserve.chosen_capacity_preserves_extent before required

/-- On a genuine growth request, the remaining allocator service uses the
executed extent, preserves the initialized observation on success, and leaves
the original array on allocation failure. The service law remains explicit. -/
theorem executed_extent_connects_fallible_reservation {Value : Type}
    (base : Environment Ptr) (fields : FieldReader Ptr) (before : Array32 Value)
    (required : UInt32) (sized : before.Sized)
    (live : before.count.toNat ≤ before.slots.length)
    (needsGrowth : before.slots.length < required.toNat)
    (allocate : OrderedDependencyCReserve.Allocator Value)
    (law : OrderedDependencyCReserve.AllocationLaw allocate) (pointerBytes sizeMaximum : Nat) :
    ∃ capacity : UInt32,
      execute actualLoop fields 32 base required (startingCapacity before) =
        some (.finished (some (.next (frame base required capacity)))) ∧
      OrderedDependencyCReserve.reserve allocate pointerBytes sizeMaximum before required =
        (if capacity.toNat * pointerBytes > sizeMaximum then (false, before)
         else match allocate before.slots capacity.toNat with
           | none => (false, before)
           | some grown => (true, ⟨grown, before.count⟩)) ∧
      (∀ grown, allocate before.slots capacity.toNat = some grown →
        (Array32.mk grown before.count).active = before.active ∧
        required.toNat ≤ grown.length ∧ (Array32.mk grown before.count).Sized) := by
  obtain ⟨capacity, completed, chosen, covers, _, bounded⟩ :=
    executed_growth_supplies_allocator_request base fields before required sized
  refine ⟨capacity, completed, ?_, ?_⟩
  · rw [OrderedDependencyCReserve.reserve, if_neg (by omega), ← chosen]
    rfl
  · intro grown allocated
    obtain ⟨extent, retained⟩ := law before.slots capacity.toNat grown allocated
    refine ⟨?_, ?_, ?_⟩
    · change grown.take before.count.toNat = before.slots.take before.count.toNat
      calc
        grown.take before.count.toNat = (grown.take before.slots.length).take before.count.toNat := by
          rw [List.take_take, Nat.min_eq_left live]
        _ = before.slots.take before.count.toNat := by rw [retained]
    · rw [extent]; exact covers
    · change grown.length ≤ maximum
      rw [extent]; exact bounded

namespace Controls

def empty : Environment Nat := fun _ => none
def noFields : FieldReader Nat := fun _ _ => none

def observe : Option (LocalBlock.Result Nat) → Option UInt32
  | some (.finished (some (.next environment))) => do
      let .unsigned value ← environment "next".toList | none
      some value
  | _ => none

theorem ordinary_growth_rounds_up :
    observe (execute actualLoop noFields 3 empty 17 4) = some 32 := by decide +kernel

theorem boundary_uses_request_without_overflow :
    observe (execute actualLoop noFields 1 empty 4294967295 2147483648) =
      some 4294967295 := by decide +kernel

theorem half_maximum_still_doubles :
    observe (execute actualLoop noFields 1 empty 2147483648 2147483647) =
      some 4294967294 := by decide +kernel

theorem sufficient_capacity_needs_no_iteration_fuel :
    observe (execute actualLoop noFields 0 empty 4 8) = some 8 := by decide +kernel

theorem zero_capacity_requires_initialization :
    execute actualLoop noFields 3 empty 4 0 = some .exhausted := rfl

theorem removed_guard_wraps_and_fails_to_finish :
    execute (some (.whileLoop condition
      [.compoundAssign .mul (.identifier "next".toList) (.unsignedInteger 2)]))
      noFields 3 empty 4294967295 2147483648 = some .exhausted := rfl

theorem removed_assignment_does_not_cover_request :
    observe (execute (some (.whileLoop condition
      [.branch boundary [.break] [],
       .compoundAssign .mul (.identifier "next".toList) (.unsignedInteger 2)]))
      noFields 1 empty 4294967295 2147483648) = some 2147483648 := by decide +kernel

theorem removed_break_multiplies_the_assigned_request :
    observe (execute (some (.whileLoop condition
      [.branch boundary [.assign (.identifier "next".toList) (.identifier "required".toList)] [],
       .compoundAssign .mul (.identifier "next".toList) (.unsignedInteger 2)]))
      noFields 2 empty 2147483649 2147483648) = none := by decide +kernel

end Controls

#print axioms actual_loop_is_retained
#print axioms quoted_loop_is_actual
#print axioms frame_next
#print axioms frame_required
#print axioms frame_maximum
#print axioms frame_updates_next
#print axioms condition_reads_actual_operands
#print axioms boundary_reads_actual_division
#print axioms high_iteration_assigns_and_breaks
#print axioms low_iteration_executes_unsigned_multiplication
#print axioms actual_growth_refines_independent_algorithm
#print axioms retained_growth_covers_and_preserves_capacity
#print axioms retained_growth_completes_with_32_iterations
#print axioms quoted_growth_executes_retained_loop
#print axioms starting_capacity_has_exact_extent
#print axioms starting_capacity_is_positive
#print axioms executed_growth_supplies_allocator_request
#print axioms executed_extent_connects_fallible_reservation
#print axioms Controls.ordinary_growth_rounds_up
#print axioms Controls.boundary_uses_request_without_overflow
#print axioms Controls.half_maximum_still_doubles
#print axioms Controls.sufficient_capacity_needs_no_iteration_fuel
#print axioms Controls.zero_capacity_requires_initialization
#print axioms Controls.removed_guard_wraps_and_fails_to_finish
#print axioms Controls.removed_assignment_does_not_cover_request
#print axioms Controls.removed_break_multiplies_the_assigned_request

end Mettapedia.Machines.OrderedDependencyCReserveGrowth
