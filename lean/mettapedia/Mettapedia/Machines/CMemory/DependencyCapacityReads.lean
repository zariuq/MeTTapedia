import Mettapedia.Machines.CMemory.DependencyReads
import Mettapedia.Machines.OrderedDependencyCReserveGrowth

/-!
# Source-linked capacity initialization and growth

The existing C parser supplies the actual initializer and while statement.
Initialization performs its pointee loads on block memory; the retained loop
then executes through the shared typed local-loop service. The computed extent
agrees with the independent allocator-request function.

This closes the positive-starting-capacity premise at this source boundary.
The enclosing early return, byte arithmetic, allocator call, pointer stores and
cleanup still need a complete source-to-memory operation connection.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.CMemory.DependencyCapacityReads

open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open scoped Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.Machines.CMemory
open Mettapedia.Machines.CMemory.Lift
open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC
open PostIndex (Array32)

universe u

abbrev Pointers := Name → Option Ptr
abbrev Words := Name → Option UInt32

/-- A typed UInt32 expression fragment. Conditional evaluation selects only
one branch; absent bindings and unsupported syntax are not zero values. -/
def readWord (pointers : Pointers) (words : Words) : CExpr → CProg CVal UInt32
  | .identifier name => match words name with
    | some value => pure value
    | none => CProg.undefined
  | .unsignedInteger value =>
      if value < 2 ^ 32 then pure (UInt32.ofNat value) else CProg.undefined
  | .unary .dereference (.identifier name) => match pointers name with
    | some pointer => CProg.loadU32 pointer
    | none => CProg.undefined
  | .conditional condition yes no => do
      let value ← readWord pointers words condition
      if value = 0 then readWord pointers words no else readWord pointers words yes
  | _ => CProg.undefined

theorem undefined_bind {α β : Type} (continuation : α → CProg CVal β) :
    (CProg.undefined >>= continuation) = CProg.undefined := by
  simp only [CProg.undefined, Prog.bind_eq, Prog.bind]
  congr 1
  funext impossible
  cases impossible

structure CapacityCode where
  initializer : CExpr
  loop : CStatement

/-- The lowering retains both expressions, rather than supplying a known
growth value. This intentionally lowers only the initializer/loop boundary. -/
def lowerFunction? (function : CDeclaratorFunction) : Option CapacityCode := do
  let .declare type name initializer ← function.body[1]? | none
  if type = ⟨"uint32_t".toList, 0⟩ ∧ name = "next".toList then do
    let loop ← function.body[2]?
    match loop with
    | .whileLoop _ _ => some ⟨initializer, loop⟩
    | _ => none
  else none

def lowerText? (text : String) : Option CapacityCode :=
  (declaratorFunctionText? OrderedDependencyCPreparationSource.typeNames text.toList).bind
    lowerFunction?

def capacityInitialization : CExpr :=
  .conditional (.unary .dereference (.identifier "capacity".toList))
    (.unary .dereference (.identifier "capacity".toList)) (.unsignedInteger 4)

def capacityCode : CapacityCode := ⟨capacityInitialization,
  .whileLoop OrderedDependencyCReserveGrowth.condition OrderedDependencyCReserveGrowth.body⟩

theorem source_lowers_actual_initialization_and_loop :
    lowerText? OrderedDependencyCPreparationSource.reserveSource = some capacityCode := by
  rw [lowerText?, OrderedDependencyCPreparationSource.complete_reserve_source_admitted]
  rfl

inductive GrowthResult where
  | completed (capacity : UInt32)
  | exhausted
  | invalid
  deriving DecidableEq

def observe : Option (LocalBlock.Result Ptr) → GrowthResult
  | some (.finished (some (.next environment))) => match environment "next".toList with
    | some (.unsigned value) => .completed value
    | _ => .invalid
  | some .exhausted => .exhausted
  | _ => .invalid

def run (code : CapacityCode) (pointers : Pointers) (words : Words)
    (base : ScalarRead.Environment Ptr) (required : UInt32) (fuel : Nat) :
    CProg CVal GrowthResult := do
  let next ← readWord pointers words code.initializer
  pure (observe (OrderedDependencyCReserveGrowth.execute (some code.loop)
    (fun _ _ => none) fuel base required next))

def runText? (text : String) (pointers : Pointers) (words : Words)
    (base : ScalarRead.Environment Ptr) (required : UInt32) (fuel : Nat) :
    Option (CProg CVal GrowthResult) :=
  (lowerText? text).map fun code => run code pointers words base required fuel

theorem parsed_source_uses_loaded_initialization (pointers : Pointers) (words : Words)
    (base : ScalarRead.Environment Ptr) (required : UInt32) (fuel : Nat) :
    runText? OrderedDependencyCPreparationSource.reserveSource pointers words base required fuel =
      some (run capacityCode pointers words base required fuel) := by
  rw [runText?, source_lowers_actual_initialization_and_loop]
  rfl

variable {L : Type u} [Zero L] [Add L] [SepAlgebra L]
  [CellPermission L (Option CVal)]

/-- The actual conditional loads `capacity` once when zero and twice when
nonzero. Both loads preserve the current value and the entire frame. -/
theorem initialized_capacity_reads_current_value (pointers : Pointers) (words : Words)
    (capacity : Ptr) (cap : UInt32) (P : Heap L → Prop)
    (pointer : pointers "capacity".toList = some capacity)
    (reads : ∀ σ, P σ → CellPermission.read ((σ capacity.block).2 capacity.offset) =
      some (some (.u32 cap))) :
    CTriple (L := L) P (readWord pointers words capacityInitialization)
      (fun next σ => next = (if cap = 0 then 4 else cap) ∧ P σ) := by
  simp only [capacityInitialization, readWord, pointer, Prog.bind_eq]
  change CTriple P (CProg.loadU32 capacity >>= fun test =>
    if test = 0 then Prog.ret 4 else CProg.loadU32 capacity) _
  refine triple_bind _ (loadU32_rule reads) fun test => ?_
  apply triple_pure
  intro same
  subst test
  by_cases zero : cap = 0
  · rw [if_pos zero]
    exact triple_pre _ (fun _ holds => ⟨by simp [zero], holds⟩) (triple_ret _ 4 _)
  · rw [if_neg zero]
    refine triple_post _ (loadU32_rule reads) ?_
    intro next σ result
    simpa only [if_neg zero] using result

theorem starting_capacity_from_exact_counted_extent {Id : Type} (before : Array32 Id)
    (sized : before.Sized) :
    (if UInt32.ofNat before.slots.length = 0 then 4 else UInt32.ofNat before.slots.length) =
      OrderedDependencyCReserveGrowth.startingCapacity before := by
  have extent := DependencyReads.capacity_toNat_is_extent before sized
  by_cases empty : before.slots.length = 0
  · simp [OrderedDependencyCReserveGrowth.startingCapacity, empty]
  · have nonzero : UInt32.ofNat before.slots.length ≠ 0 := by
      intro zero
      rw [zero] at extent
      exact empty extent.symm
    simp [OrderedDependencyCReserveGrowth.startingCapacity, nonzero, empty]

/-- The source boundary no longer assumes a positive local `next`: the
actual conditional initializes it from the represented capacity, including
zero capacity. The retained loop then supplies the exact allocation request. -/
theorem loaded_growth_refines_request {Id : Type} (addr : Id → Ptr)
    (items count capacity : Ptr) (before : Array32 Id) (sized : before.Sized)
    (required : UInt32) (pointers : Pointers) (words : Words)
    (base : ScalarRead.Environment Ptr) (F : Heap L → Prop)
    (pointer : pointers "capacity".toList = some capacity) :
    CTriple (L := L) (CountedArray addr items count capacity before ∗ F)
      (run capacityCode pointers words base required 32)
      (fun result σ => ∃ chosen,
        result = .completed chosen ∧
        chosen.toNat = OrderedDependencyCReserve.chosenCapacity before required ∧
        required.toNat ≤ chosen.toNat ∧ before.slots.length ≤ chosen.toNat ∧
        chosen.toNat ≤ OrderedDependencyCapacity.maximum ∧
        (CountedArray addr items count capacity before ∗ F) σ) := by
  unfold run
  simp only [Prog.bind_eq]
  refine triple_bind _ (initialized_capacity_reads_current_value pointers words capacity
    (UInt32.ofNat before.slots.length) _ pointer fun σ holds =>
      DependencyReads.counted_capacity_read addr holds) fun next => ?_
  apply triple_pure
  intro same
  rw [starting_capacity_from_exact_counted_extent before sized] at same
  subst next
  obtain ⟨chosen, executed, agrees, covers, preserves, bounded⟩ :=
    OrderedDependencyCReserveGrowth.executed_growth_supplies_allocator_request base
      (fun _ _ => none) before required sized
  have loop : some capacityCode.loop = OrderedDependencyCReserveGrowth.actualLoop :=
    OrderedDependencyCReserveGrowth.actual_loop_is_retained.symm
  rw [loop, executed]
  change CTriple _ (Prog.ret (GrowthResult.completed chosen)) _
  refine triple_pre _ ?_ (triple_ret _ (GrowthResult.completed chosen) _)
  intro σ holds
  exact ⟨chosen, rfl, agrees, covers, preserves, bounded, holds⟩

/-- The proof starts from complete source text admitted by the shared parser;
the executable initializer/loop program is obtained by lowering that text. -/
theorem parsed_growth_refines_request {Id : Type} (addr : Id → Ptr)
    (items count capacity : Ptr) (before : Array32 Id) (sized : before.Sized)
    (required : UInt32) (pointers : Pointers) (words : Words)
    (base : ScalarRead.Environment Ptr) (F : Heap L → Prop)
    (pointer : pointers "capacity".toList = some capacity) :
    ∃ program,
      runText? OrderedDependencyCPreparationSource.reserveSource pointers words base required 32 =
        some program ∧
      CTriple (L := L) (CountedArray addr items count capacity before ∗ F) program
        (fun result σ => ∃ chosen,
          result = .completed chosen ∧
          chosen.toNat = OrderedDependencyCReserve.chosenCapacity before required ∧
          required.toNat ≤ chosen.toNat ∧ before.slots.length ≤ chosen.toNat ∧
          chosen.toNat ≤ OrderedDependencyCapacity.maximum ∧
          (CountedArray addr items count capacity before ∗ F) σ) :=
  ⟨_, parsed_source_uses_loaded_initialization pointers words base required 32,
    loaded_growth_refines_request addr items count capacity before sized required pointers words
      base F pointer⟩

/-- The extent produced by the source-linked reads and loop is the exact
request of the shared block-memory reserve, not merely a covering capacity. -/
theorem loaded_growth_matches_block_request {Id : Type} (addr : Id → Ptr)
    (items count capacity : Ptr) (before : Array32 Id) (sized : before.Sized)
    (required : UInt32) (pointers : Pointers) (words : Words)
    (base : ScalarRead.Environment Ptr) (F : Heap L → Prop)
    (pointer : pointers "capacity".toList = some capacity) :
    CTriple (L := L) (CountedArray addr items count capacity before ∗ F)
      (run capacityCode pointers words base required 32)
      (fun result σ => ∃ chosen, result = .completed chosen ∧
        chosen.toNat = nextCapacity required (UInt32.ofNat before.slots.length) ∧
        (CountedArray addr items count capacity before ∗ F) σ) := by
  refine triple_post _ (loaded_growth_refines_request addr items count capacity before sized
    required pointers words base F pointer) ?_
  rintro result σ ⟨chosen, completed, agrees, -, -, -, holds⟩
  refine ⟨chosen, completed, ?_, holds⟩
  rw [nextCapacity_eq_chosenCapacity required (UInt32.ofNat before.slots.length) before
    (DependencyReads.capacity_toNat_is_extent before sized).symm]
  exact agrees

namespace Controls

def noPointers : Pointers := fun _ => none
def noWords : Words := fun _ => none
def empty : ScalarRead.Environment Ptr := fun _ => none

theorem absent_capacity_binding_is_not_zero :
    readWord noPointers noWords capacityInitialization = CProg.undefined := by
  simp only [capacityInitialization, readWord, noPointers, Prog.bind_eq]
  exact undefined_bind _

theorem zero_condition_does_not_read_unselected_binding :
    readWord noPointers noWords
      (.conditional (.unsignedInteger 0) (.identifier "missing".toList) (.unsignedInteger 4)) =
      Prog.ret 4 := rfl

theorem nonzero_condition_does_read_selected_binding :
    readWord noPointers noWords
      (.conditional (.unsignedInteger 1) (.identifier "missing".toList) (.unsignedInteger 4)) =
      CProg.undefined := rfl

theorem oversized_literal_is_not_wrapped_to_zero :
    readWord noPointers noWords (.unsignedInteger 4294967296) = CProg.undefined := rfl

theorem altered_initializer_is_retained :
    lowerFunction? { OrderedDependencyCPreparationSource.reserveFunction with
      body := OrderedDependencyCPreparationSource.reserveFunction.body.set 1
        (.declare ⟨"uint32_t".toList, 0⟩ "next".toList (.unsignedInteger 13)) } =
      some { capacityCode with initializer := .unsignedInteger 13 } := rfl

theorem missing_growth_is_not_synthesized :
    lowerFunction? { OrderedDependencyCPreparationSource.reserveFunction with
      body := OrderedDependencyCPreparationSource.reserveFunction.body.set 2
        (.return (some (.bool true))) } = none := rfl

theorem changed_initial_capacity_changes_request :
    run { capacityCode with initializer := .unsignedInteger 13 } noPointers noWords empty 17 32 =
      Prog.ret (.completed 26) := rfl

theorem growth_fuel_exhaustion_is_not_success :
    run { capacityCode with initializer := .unsignedInteger 4 } noPointers noWords empty 17 0 =
      Prog.ret .exhausted := rfl

theorem removed_boundary_can_wrap_and_exhaust :
    run ⟨.unsignedInteger 2147483648,
      .whileLoop OrderedDependencyCReserveGrowth.condition
        [.compoundAssign .mul (.identifier "next".toList) (.unsignedInteger 2)]⟩
      noPointers noWords empty 4294967295 3 = Prog.ret .exhausted := rfl

end Controls

end Mettapedia.Machines.CMemory.DependencyCapacityReads
