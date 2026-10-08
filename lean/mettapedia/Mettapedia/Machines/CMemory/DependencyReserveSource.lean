import Mettapedia.Machines.CMemory.LocalMemory
import Mettapedia.Machines.CMemory.DependencyReserve

/-!
# The complete parsed dependency-reserve helper on block memory

The shared source reader retains the full function body. Typed local control
then executes its guards, growth loop, byte request, allocation and field
stores. The resulting program is connected to the independent exact reserve
contract; repeated readonly loads are discharged from owned field values.

The interpretation uses the declared moving-or-failing allocator service.
Native ABI layout, in-place realloc and whole-operation synchronization remain
separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.CMemory.DependencyReserveSource

open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open scoped Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC
open Lift
open ScalarBytes LocalMemory

universe u

def services (abi : ABI) : Services :=
  ⟨abi, "space_module_link_try_reallocate".toList⟩

def base : Context :=
  ⟨fun name => if name = "UINT32_MAX".toList then some (.unsigned 4294967295) else none,
    fun name => if name = "UINT32_MAX".toList then some ⟨"uint32_t".toList, 0⟩ else none⟩

def input (items capacity : Ptr) (required : UInt32) : Context :=
  ((base.bind ⟨"Space".toList, 3⟩ "items".toList (.identity (some items))).bind
    ⟨"uint32_t".toList, 1⟩ "capacity".toList (.identity (some capacity))).bind
      ⟨"uint32_t".toList, 0⟩ "required".toList (.unsigned required)

def withNext (items capacity : Ptr) (required next : UInt32) : Context :=
  (input items capacity required).bind ⟨"uint32_t".toList, 0⟩ "next".toList (.unsigned next)

def program (abi : ABI) (items capacity : Ptr) (required : UInt32) : CProg CVal Result :=
  execute (services abi) 32 64 (input items capacity required)
    OrderedDependencyCPreparationSource.reserveFunction.body >>= fun flow => pure (result flow)

theorem parsed_source_supplies_complete_program (abi : ABI) (items capacity : Ptr)
    (required : UInt32) :
    runText? OrderedDependencyCPreparationSource.typeNames
      OrderedDependencyCPreparationSource.reserveSource (services abi) base
      [.identity (some items), .identity (some capacity), .unsigned required] 64 32 =
        some (program abi items capacity required) := by
  rw [runText?, OrderedDependencyCPreparationSource.complete_reserve_source_admitted]
  rfl

variable {L : Type u} [Zero L] [Add L] [SepAlgebra L]
  [CellPermission L (Option CVal)]

/-- A known readonly prefix can be removed from a checked program. The prefix
must actually execute to the supplied value without changing the heap. -/
theorem triple_after_known_read {α β : Type} {P : Heap L → Prop}
    {first : CProg CVal α} {continuation : α → CProg CVal β}
    {Q : β → Heap L → Prop} (value : α)
    (reads : ∀ σ, P σ → first.Runs act σ value σ)
    (whole : CTriple (L := L) P (first >>= continuation) Q) :
    CTriple (L := L) P (continuation value) Q := by
  intro σ holds
  obtain ⟨safe, post⟩ := whole σ holds
  have safeAfter := (Prog.safe_bind act first continuation σ).mp safe
  refine ⟨safeAfter.2 value σ (reads σ holds), ?_⟩
  intro answer after executed
  exact post answer after ((Prog.runs_bind act first continuation σ answer after).mpr
    ⟨value, σ, reads σ holds, executed⟩)

theorem load_word_runs_current (p : Ptr) (value : UInt32) (σ : Heap L)
    (read : CellPermission.read ((σ p.block).2 p.offset) = some (some (.u32 value))) :
    (CProg.loadU32 p).Runs act σ value σ := by
  exact ⟨.u32 value, σ, ⟨read, rfl⟩, rfl, rfl⟩

/-- The checked shared reserve continuation, after its actual initial load. -/
def afterCapacity (abi : ABI) (items capacity : Ptr) (required cap : UInt32) :
    CProg CVal Bool :=
  if required ≤ cap then pure true
  else if abi.sizeMaximum < nextCapacity required cap * abi.pointerBytes then pure false
  else do
    let old ← CProg.loadPtr items
    match ← CProg.realloc old (nextCapacity required cap) with
    | none => pure false
    | some grown => do
        CProg.store items (.ptr (some grown))
        CProg.store capacity (.u32 (UInt32.ofNat (nextCapacity required cap)))
        pure true

theorem checked_capacity_continuation (abi : ABI) (items capacity : Ptr)
    (required cap : UInt32) (a : Option Ptr) (xs : List CVal) :
    CTriple (L := L) (ArrayFields items capacity a cap xs)
      (afterCapacity abi items capacity required cap)
      (DependencyReserve.ReserveResult abi.pointerBytes abi.sizeMaximum items capacity
        required cap a xs) := by
  have reserveSpec := DependencyReserve.reserve_exact_spec (L := L)
    abi.pointerBytes abi.sizeMaximum items capacity required a cap xs
  change CTriple _ (CProg.loadU32 capacity >>= afterCapacity abi items capacity required) _
    at reserveSpec
  refine triple_after_known_read cap (fun σ holds => ?_) reserveSpec
  apply load_word_runs_current
  rw [ArrayFields, sepConj_left_comm] at holds
  exact read_of_pointsTo holds

theorem loop_frame_is_next_context (items capacity : Ptr) (required next : UInt32) :
    OrderedDependencyCReserveGrowth.frame (input items capacity required).values required next =
      (withNext items capacity required next).values := by
  have maximum : (input items capacity required).values "UINT32_MAX".toList =
      some (.unsigned 4294967295) := rfl
  have request : (input items capacity required).values "required".toList =
      some (.unsigned required) := rfl
  change Function.update (Function.update (Function.update
    (input items capacity required).values "UINT32_MAX".toList
      (some (.unsigned 4294967295))) "required".toList (some (.unsigned required)))
        "next".toList (some (.unsigned next)) = _
  rw [← maximum, Function.update_eq_self, ← request, Function.update_eq_self]
  rfl

theorem source_growth_executes_exact_extent (items capacity : Ptr) (required cap : UInt32) :
    ∃ next : UInt32,
      LocalLoop.whileStatement (fun _ _ => none) 4 32
        (withNext items capacity required (if cap = 0 then 4 else cap)).values
        (.whileLoop OrderedDependencyCReserveGrowth.condition
          OrderedDependencyCReserveGrowth.body) =
          some (.finished (some (.next (withNext items capacity required next).values))) ∧
      next.toNat = nextCapacity required cap := by
  have capZero : cap.toNat = 0 ↔ cap = 0 := by
    constructor
    · intro same
      exact UInt32.toNat_inj.mp same
    · rintro rfl
      rfl
  have start : (if cap = 0 then (4 : UInt32) else cap).toNat =
      if cap.toNat = 0 then 4 else cap.toNat := by
    by_cases zero : cap = 0 <;> simp [zero, capZero]
  have positive : 0 < (if cap = 0 then (4 : UInt32) else cap).toNat := by
    rw [start]
    split <;> omega
  obtain ⟨next, executed, agrees, -, -, -⟩ :=
    OrderedDependencyCReserveGrowth.retained_growth_completes_with_32_iterations
      (input items capacity required).values (fun _ _ => none) required
      (if cap = 0 then 4 else cap) positive
  simp only [OrderedDependencyCReserveGrowth.execute,
    OrderedDependencyCReserveGrowth.actual_loop_is_retained, Option.bind_some,
    loop_frame_is_next_context] at executed
  refine ⟨next, executed, ?_⟩
  rw [agrees, start]
  rfl

def guardProduct : CExpr :=
  .binary .mul (.cast ⟨"uint64_t".toList, 0⟩ (.identifier "next".toList))
    (.sizeOfExpr (.unary .dereference (.unary .dereference (.identifier "items".toList))))

def allocationProduct : CExpr :=
  .binary .mul
    (.sizeOfExpr (.unary .dereference (.unary .dereference (.identifier "items".toList))))
    (.cast ⟨"size_t".toList, 0⟩ (.identifier "next".toList))

theorem guard_operand_uses_unsigned64 (abi : ABI) (items capacity : Ptr)
    (required next : UInt32) :
    wide? abi (withNext items capacity required next).types
      (withNext items capacity required next).values guardProduct =
        some ⟨.unsigned64, next.toNat * abi.pointerBytes⟩ := by
  change some (multiply abi ⟨.unsigned64, next.toNat⟩ ⟨.size, abi.pointerBytes⟩) = _
  rw [unsigned64_guard_product_exact]

theorem allocator_operand_uses_guarded_size (abi : ABI) (items capacity : Ptr)
    (required next : UInt32) (guard : next.toNat * abi.pointerBytes ≤ abi.sizeMaximum) :
    wide? abi (withNext items capacity required next).types
      (withNext items capacity required next).values allocationProduct =
        some ⟨.size, abi.pointerBytes * next.toNat⟩ := by
  change some (multiply abi ⟨.size, abi.pointerBytes⟩
    ⟨.size, next.toNat % abi.sizeWidth.modulus⟩) = _
  rw [guarded_size_product_exact abi next guard]

theorem allocation_conversion_keeps_guarded_bytes (abi : ABI) (next : UInt32)
    (guard : next.toNat * abi.pointerBytes ≤ abi.sizeMaximum) :
    (abi.pointerBytes * next.toNat) % abi.sizeWidth.modulus = abi.pointerBytes * next.toNat := by
  have positive := size_modulus_positive abi.sizeWidth
  simp only [ABI.sizeMaximum] at guard
  have below : abi.pointerBytes * next.toNat < abi.sizeWidth.modulus := by
    rw [Nat.mul_comm]
    omega
  exact Nat.mod_eq_of_lt below

theorem guarded_allocator_uses_actual_extent (abi : ABI) (items capacity : Ptr)
    (required next : UInt32) (guard : next.toNat * abi.pointerBytes ≤ abi.sizeMaximum) :
    readPointer (services abi) (withNext items capacity required next)
      (.call "space_module_link_try_reallocate".toList
        [.unary .dereference (.identifier "items".toList), allocationProduct]) =
      (CProg.loadPtr items >>= fun old => CProg.realloc old next.toNat) := by
  change (CProg.loadPtr items >>= fun old =>
    match wide? abi (withNext items capacity required next).types
        (withNext items capacity required next).values allocationProduct with
    | some bytes => match cells? abi (bytes.value % abi.sizeWidth.modulus) with
        | some extent => CProg.realloc old extent
        | none => CProg.undefined
    | none => CProg.undefined) = _
  rw [allocator_operand_uses_guarded_size abi items capacity required next guard]
  simp only [allocation_conversion_keeps_guarded_bytes abi next guard, whole_cell_request_exact]

theorem source_tail_executes_actual_allocation_and_stores (abi : ABI)
    (items capacity : Ptr) (required next : UInt32) (fuel : Nat) :
    execute (services abi) 32 (fuel + 8) (withNext items capacity required next)
      (OrderedDependencyCPreparationSource.reserveBody.drop 3) =
      (if abi.sizeMaximum < next.toNat * abi.pointerBytes then pure (.returned false)
       else do
         let old ← CProg.loadPtr items
         match ← CProg.realloc old next.toNat with
         | none => pure (.returned false)
         | some grown => do
             CProg.store items (.ptr (some grown))
             CProg.store capacity (.u32 next)
             pure (.returned true)) := by
  change (readTruth (services abi) (withNext items capacity required next)
      (.binary .gt guardProduct (.identifier "SIZE_MAX".toList)) >>= fun test =>
    execute (services abi) 32 (fuel + 7) (withNext items capacity required next)
      (if test then [.return (some (.bool false))] else []) >>= fun flow =>
        match flow with
        | .next context => execute (services abi) 32 (fuel + 7) context
            (OrderedDependencyCPreparationSource.reserveBody.drop 4)
        | other => pure other) = _
  simp only [readTruth, services, guard_operand_uses_unsigned64, wide?,
    ↓reduceIte, Prog.bind_eq, Prog.pure_eq, Prog.ret_bind]
  by_cases tooLarge : abi.sizeMaximum < next.toNat * abi.pointerBytes
  · simp only [tooLarge, decide_true, ↓reduceIte,
      execute, readTruth, Prog.bind_eq, Prog.pure_eq, Prog.ret_bind]
  · have guard : next.toNat * abi.pointerBytes ≤ abi.sizeMaximum := Nat.le_of_not_lt tooLarge
    simp only [tooLarge, decide_false, Bool.false_eq_true, ↓reduceIte,
      execute, Prog.pure_eq, Prog.ret_bind]
    change ((readPointer (services abi) (withNext items capacity required next)
      (.call "space_module_link_try_reallocate".toList
        [.unary .dereference (.identifier "items".toList), allocationProduct]) >>=
          fun grown => pure (ScalarRead.Value.identity grown)) >>= fun value =>
          execute (services abi) 32 (fuel + 6)
            ((withNext items capacity required next).bind ⟨"Space".toList, 2⟩
              "grown".toList value)
              (OrderedDependencyCPreparationSource.reserveBody.drop 5) >>= fun flow =>
                pure (restore (withNext items capacity required next) "grown".toList flow)) = _
    simp only [Prog.bind_eq]
    rw [Prog.bind_assoc]
    simp only [Prog.pure_eq, Prog.ret_bind]
    rw [guarded_allocator_uses_actual_extent abi items capacity required next guard]
    change ((CProg.loadPtr items >>= fun old => CProg.realloc old next.toNat) >>= _) = _
    simp only [Prog.bind_eq]
    rw [Prog.bind_assoc]
    congr 1
    funext old
    congr 1
    funext grown
    cases grown with
    | none => rfl
    | some grown => rfl

theorem source_head_keeps_actual_early_return (abi : ABI) (items capacity : Ptr)
    (required : UInt32) :
    execute (services abi) 32 64 (input items capacity required)
      OrderedDependencyCPreparationSource.reserveBody =
      (CProg.loadU32 capacity >>= fun cap =>
        if required ≤ cap then pure (.returned true)
        else execute (services abi) 32 63 (input items capacity required)
          (OrderedDependencyCPreparationSource.reserveBody.drop 1)) := by
  change ((CProg.loadU32 capacity >>= fun cap => pure (decide (required ≤ cap))) >>= fun test =>
    execute (services abi) 32 63 (input items capacity required)
      (if test then [.return (some (.bool true))] else []) >>= fun flow =>
        match flow with
        | .next context => execute (services abi) 32 63 context
            (OrderedDependencyCPreparationSource.reserveBody.drop 1)
        | other => pure other) = _
  simp only [Prog.bind_eq, Prog.pure_eq]
  rw [Prog.bind_assoc]
  simp only [Prog.ret_bind]
  congr 1
  funext cap
  by_cases fits : required ≤ cap
  · simp only [fits, decide_true, ↓reduceIte]
    rfl
  · simp only [fits, decide_false, Bool.false_eq_true, ↓reduceIte]
    rfl

theorem source_initializer_keeps_actual_reads (abi : ABI) (items capacity : Ptr)
    (required : UInt32) :
    execute (services abi) 32 63 (input items capacity required)
      (OrderedDependencyCPreparationSource.reserveBody.drop 1) =
      (readWord (input items capacity required) DependencyCapacityReads.capacityInitialization >>=
        fun next => execute (services abi) 32 62 (withNext items capacity required next)
          (OrderedDependencyCPreparationSource.reserveBody.drop 2) >>= fun flow =>
            pure (restore (input items capacity required) "next".toList flow)) := by
  change ((readWord (input items capacity required) DependencyCapacityReads.capacityInitialization >>=
    fun next => pure (ScalarRead.Value.unsigned next)) >>= fun value =>
      execute (services abi) 32 62
        ((input items capacity required).bind ⟨"uint32_t".toList, 0⟩ "next".toList value)
          (OrderedDependencyCPreparationSource.reserveBody.drop 2) >>= fun flow =>
            pure (restore (input items capacity required) "next".toList flow)) = _
  simp only [Prog.bind_eq, Prog.pure_eq]
  rw [Prog.bind_assoc]
  rfl

theorem actual_tail_refines_checked_continuation (abi : ABI) (items capacity : Ptr)
    (required cap next : UInt32) (grows : ¬ required ≤ cap)
    (extent : next.toNat = nextCapacity required cap) (fuel : Nat) :
    execute (services abi) 32 (fuel + 8) (withNext items capacity required next)
      (OrderedDependencyCPreparationSource.reserveBody.drop 3) =
        (afterCapacity abi items capacity required cap >>= fun ok => pure (.returned ok)) := by
  rw [source_tail_executes_actual_allocation_and_stores]
  simp only [afterCapacity, if_neg grows, ← extent, UInt32.ofNat_toNat,
    Prog.bind_eq, Prog.pure_eq]
  split
  · rfl
  · simp only [Prog.bind_assoc]
    congr 1
    funext old
    congr 1
    funext grown
    cases grown <;> rfl

/-- All statements of the parsed helper now participate in the exact contract.
The result cannot be proof-fuel exhaustion or a missing return on owned inputs. -/
theorem complete_body_reserve_spec (abi : ABI) (items capacity : Ptr)
    (required cap : UInt32) (a : Option Ptr) (xs : List CVal) :
    CTriple (L := L) (ArrayFields items capacity a cap xs)
      (execute (services abi) 32 64 (input items capacity required)
        OrderedDependencyCPreparationSource.reserveBody)
      (fun flow σ => ∃ ok, flow = .returned ok ∧
        DependencyReserve.ReserveResult abi.pointerBytes abi.sizeMaximum items capacity
          required cap a xs ok σ) := by
  rw [source_head_keeps_actual_early_return]
  simp only [Prog.bind_eq]
  refine triple_bind _ (loadU32_rule (n := cap) fun σ holds => ?_) fun loaded => ?_
  · rw [ArrayFields, sepConj_left_comm] at holds
    exact read_of_pointsTo holds
  apply triple_pure
  intro same
  subst loaded
  by_cases fits : required ≤ cap
  · rw [if_pos fits]
    refine triple_pre _ ?_ (triple_ret _ (Flow.returned true) _)
    intro σ holds
    exact ⟨true, rfl, Or.inl ⟨rfl, fits, holds⟩⟩
  rw [if_neg fits, source_initializer_keeps_actual_reads]
  simp only [Prog.bind_eq]
  refine triple_bind _ (DependencyCapacityReads.initialized_capacity_reads_current_value
    (pointers (input items capacity required)) (words (input items capacity required))
      capacity cap (ArrayFields items capacity a cap xs) (by rfl) fun σ holds => ?_)
    fun start => ?_
  · rw [ArrayFields, sepConj_left_comm] at holds
    exact read_of_pointsTo holds
  apply triple_pure
  intro same
  subst start
  obtain ⟨next, executed, extent⟩ := source_growth_executes_exact_extent items capacity required cap
  change CTriple _ ((match LocalLoop.whileStatement (fun _ _ => none) 4 32
      (withNext items capacity required (if cap = 0 then 4 else cap)).values
      (.whileLoop OrderedDependencyCReserveGrowth.condition OrderedDependencyCReserveGrowth.body) with
    | some (.finished (some (.next values))) => execute (services abi) 32 61
        ⟨values, (withNext items capacity required (if cap = 0 then 4 else cap)).types⟩
        (OrderedDependencyCPreparationSource.reserveBody.drop 3)
    | some (.finished (some (.returned _ (some (.boolean value))))) => pure (.returned value)
    | some .exhausted => pure .exhausted
    | _ => CProg.undefined) >>= fun flow =>
      pure (restore (input items capacity required) "next".toList flow)) _
  rw [executed]
  change CTriple _ (execute (services abi) 32 (53 + 8)
    (withNext items capacity required next)
    (OrderedDependencyCPreparationSource.reserveBody.drop 3) >>= fun flow =>
      pure (restore (input items capacity required) "next".toList flow)) _
  rw [actual_tail_refines_checked_continuation abi items capacity required cap next fits extent 53]
  simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind, restore]
  refine triple_bind _ (checked_capacity_continuation abi items capacity required cap a xs) fun ok => ?_
  refine triple_pre _ (fun σ holds => ⟨ok, rfl, holds⟩) (triple_ret _ (Flow.returned ok) _)

theorem complete_parsed_reserve_spec (abi : ABI) (items capacity : Ptr)
    (required cap : UInt32) (a : Option Ptr) (xs : List CVal) :
    ∃ executable,
      runText? OrderedDependencyCPreparationSource.typeNames
        OrderedDependencyCPreparationSource.reserveSource (services abi) base
        [.identity (some items), .identity (some capacity), .unsigned required] 64 32 =
          some executable ∧
      CTriple (L := L) (ArrayFields items capacity a cap xs) executable
        (fun answer σ => ∃ ok, answer = .completed ok ∧
          DependencyReserve.ReserveResult abi.pointerBytes abi.sizeMaximum items capacity
            required cap a xs ok σ) := by
  refine ⟨program abi items capacity required,
    parsed_source_supplies_complete_program abi items capacity required, ?_⟩
  unfold program
  simp only [OrderedDependencyCPreparationSource.reserveFunction, Prog.bind_eq]
  refine triple_bind _ (complete_body_reserve_spec abi items capacity required cap a xs) fun flow => ?_
  refine triple_exists _ fun ok => triple_pure _ fun same => ?_
  subst flow
  exact triple_pre _ (fun σ holds => ⟨ok, rfl, holds⟩) (triple_ret _ (Result.completed ok) _)

variable {Id : Type} (addr : Id → Ptr)

theorem complete_parsed_counted_reserve_spec (abi : ABI) (items count capacity : Ptr)
    (a : Option Ptr) (before : PostIndex.Array32 Id) (required : UInt32) (filler : Id)
    (sized : before.Sized) (within : before.count.toNat ≤ before.slots.length) :
    CTriple (L := L) (Lift.CountedFields addr items count capacity a before)
      (program abi items capacity required)
      (fun answer σ => ∃ ok, answer = .completed ok ∧
        DependencyReserve.CountedReserveResult addr abi.pointerBytes abi.sizeMaximum
          items count capacity a before required filler ok σ) := by
  obtain ⟨executable, produced, checked⟩ := complete_parsed_reserve_spec (L := L)
    abi items capacity required (UInt32.ofNat before.slots.length) a
      (before.active.map (Lift.spacePtr ∘ addr))
  rw [parsed_source_supplies_complete_program] at produced
  cases produced
  refine triple_post _ (triple_pre _ (fun σ holds => ?_)
    (frame checked (PointsTo count (.u32 before.count)))) ?_
  · rwa [DependencyReserve.counted_fields_as_array_fields addr items count capacity a before sized]
      at holds
  rintro answer σ ⟨x, y, separate, rfl, ⟨ok, same, result⟩, counter⟩
  exact ⟨ok, same, DependencyReserve.reserve_result_with_counter addr abi.pointerBytes
    abi.sizeMaximum items count capacity a before required filler sized within ok (x + y)
      ⟨x, y, separate, rfl, result, counter⟩⟩

theorem complete_parsed_reserve_refines_array (abi : ABI) (items count capacity : Ptr)
    (before : PostIndex.Array32 Id) (required : UInt32) (filler : Id) (sized : before.Sized) :
    CTriple (L := L) (Lift.CountedArray addr items count capacity before)
      (program abi items capacity required)
      (fun answer σ => ∃ ok old, answer = .completed ok ∧
        DependencyReserve.ReservationRel addr abi.pointerBytes abi.sizeMaximum items count capacity
          old before required filler ok σ) := by
  apply triple_pure
  intro within
  apply triple_exists
  intro old
  refine triple_post _ (complete_parsed_counted_reserve_spec addr abi items count capacity
    old before required filler sized within) ?_
  rintro answer σ ⟨ok, same, result⟩
  exact ⟨ok, old, same, DependencyReserve.exact_result_refines_array addr abi.pointerBytes
    abi.sizeMaximum items count capacity old before required filler sized within ok σ result⟩

section Store

variable [DecidableEq Id]

/-- The complete parsed helper reserves either direction inside the represented
store, preserving both published observations and all other owners' arrays. -/
theorem complete_parsed_store_reserve_refines (abi : ABI) (layout : Lift.SpaceLayout)
    {D : List Id} (distinct : D.Nodup) (H : SplitHeap Id)
    (owner : Id) (member : owner ∈ D) (direction : OrderedDependencyCSource.ArrayField)
    (required : UInt32) (filler : Id) (sized : H.Sized) :
    CTriple (L := L) (Lift.StoreRep addr layout D H)
      (program abi
        (addr owner + (DependencyReads.arrayOffsets layout direction).1)
        (addr owner + (DependencyReads.arrayOffsets layout direction).2.2) required)
      (fun answer σ => ∃ (ok : Bool) (old : Option Ptr) (after : PostIndex.Array32 Id)
          (available : Bool),
        answer = .completed ok ∧
        OrderedDependencyCReserve.reserve (OrderedDependencyCReserve.paddingAllocator filler available)
          abi.pointerBytes abi.sizeMaximum (DependencyReads.selectedArray H owner direction)
            required = (ok, after) ∧
        after.count = (DependencyReads.selectedArray H owner direction).count ∧
        (ok = true → required.toNat ≤ after.slots.length) ∧
        OrderedDependencyCArray.observe (DependencyReserve.updateArray H owner direction after) =
          OrderedDependencyCArray.observe H ∧
        (DependencyReserve.updateArray H owner direction after).Sized ∧
        (Lift.StoreRep addr layout D (DependencyReserve.updateArray H owner direction after) ∗
          (if (DependencyReads.selectedArray H owner direction).slots.length < required.toNat ∧
              ok = true then
            DeadStorage old (DependencyReads.selectedArray H owner direction).slots.length
            else emp)) σ) := by
  obtain ⟨F, beforeFrame, afterFrame⟩ :=
    DependencyReserve.store_array_update_frame (L := L) addr layout distinct H owner member direction
  have arraySized : (DependencyReads.selectedArray H owner direction).Sized := by
    cases direction
    · exact sized.1 owner
    · exact sized.2 owner
  refine triple_post _ (triple_pre _ (fun σ holds => beforeFrame ▸ holds)
    (frame (complete_parsed_reserve_refines_array addr abi _ _ _
      (DependencyReads.selectedArray H owner direction) required filler arraySized) F)) ?_
  rintro answer σ ⟨x, y, separate, rfl,
    ⟨ok, old, same, after, available, allocated, count, active, afterSized, covers, fields⟩, frame⟩
  refine ⟨ok, old, after, available, same, allocated, count, covers,
    DependencyReserve.update_array_observation H owner direction after active,
    DependencyReserve.update_array_sized H owner direction after sized afterSized, ?_⟩
  rw [afterFrame]
  simpa only [sepConj_assoc, sepConj_comm, sepConj_left_comm] using
    (show ((_ ∗ _) ∗ F) (x + y) from ⟨x, y, separate, rfl, fields, frame⟩)

end Store

namespace Controls

theorem complete_source_no_growth_reads_only_capacity (abi : ABI) (items capacity : Ptr)
    (required cap : UInt32) (fits : required ≤ cap) :
    CTriple (L := L) (PointsTo capacity (.u32 cap)) (program abi items capacity required)
      (fun answer σ => answer = .completed true ∧ PointsTo capacity (.u32 cap) σ) := by
  unfold program
  change CTriple _ (execute (services abi) 32 64 (input items capacity required)
    OrderedDependencyCPreparationSource.reserveBody >>= fun flow => pure (result flow)) _
  rw [source_head_keeps_actual_early_return]
  simp only [Prog.bind_eq, Prog.bind_assoc]
  refine triple_bind _ (loadU32_rule (n := cap) fun σ holds => ?_) fun loaded => ?_
  · exact read_of_pointsTo (F := emp) (by simpa only [sepConj_emp] using holds)
  apply triple_pure
  intro same
  subst loaded
  rw [if_pos fits]
  exact triple_pre _ (fun σ holds => ⟨rfl, holds⟩)
    (triple_ret _ (Result.completed true) _)

theorem source_byte_guard_rejects_before_reading_items (items capacity : Ptr) (required : UInt32) :
    execute (services ScalarBytes.Controls.abi32) 32 61
      (withNext items capacity required 1073741824)
      (OrderedDependencyCPreparationSource.reserveBody.drop 3) = pure (.returned false) := by
  rw [source_tail_executes_actual_allocation_and_stores
    ScalarBytes.Controls.abi32 items capacity required 1073741824 53]
  rfl

/-- Dropping the guard exposes size_t's wrapped zero request, rather than the
unwrapped natural-number extent. This is why the source guard is substantive. -/
theorem unguarded_request_wraps_to_zero_cells (items capacity : Ptr) (required : UInt32) :
    readPointer (services ScalarBytes.Controls.abi32)
      (withNext items capacity required 1073741824)
      (.call "space_module_link_try_reallocate".toList
        [.unary .dereference (.identifier "items".toList), allocationProduct]) =
      (CProg.loadPtr items >>= fun old => CProg.realloc old 0) := rfl

theorem changed_request_is_not_substituted_with_next (items capacity : Ptr)
    (required next : UInt32) :
    readPointer (services ScalarBytes.Controls.abi64) (withNext items capacity required next)
      (.call "space_module_link_try_reallocate".toList
        [.unary .dereference (.identifier "items".toList),
         .binary .mul
           (.sizeOfExpr (.unary .dereference (.unary .dereference (.identifier "items".toList))))
           (.cast ⟨"size_t".toList, 0⟩ (.unsignedInteger 17))]) =
      (CProg.loadPtr items >>= fun old => CProg.realloc old 17) := rfl

theorem complete_function_empty_body_is_not_filled_in (abi : ABI) (items capacity : Ptr)
    (required : UInt32) :
    runFunction? (services abi) base
      [.identity (some items), .identity (some capacity), .unsigned required] 64 32
      { OrderedDependencyCPreparationSource.reserveFunction with body := [] } =
        some (pure .missingReturn) := rfl

theorem mismatched_argument_type_not_admitted (abi : ABI) (items capacity : Ptr)
    (required : UInt32) :
    runFunction? (services abi) base
      [.identity (some items), .identity (some capacity), .unsigned required] 64 32
      { OrderedDependencyCPreparationSource.reserveFunction with
        parameters := [⟨⟨"Space".toList, false, [false, false, false]⟩, "items".toList⟩,
          ⟨⟨"uint32_t".toList, false, [false]⟩, "capacity".toList⟩,
          ⟨⟨"uint64_t".toList, false, []⟩, "required".toList⟩] } = none := rfl

theorem missing_argument_not_defaulted (abi : ABI) (items capacity : Ptr) :
    runFunction? (services abi) base [.identity (some items), .identity (some capacity)]
      64 32 OrderedDependencyCPreparationSource.reserveFunction = none := rfl

theorem changed_function_return_keeps_false (abi : ABI) (items capacity : Ptr)
    (required : UInt32) :
    runFunction? (services abi) base
      [.identity (some items), .identity (some capacity), .unsigned required] 64 32
      { OrderedDependencyCPreparationSource.reserveFunction with
        body := [.return (some (.bool false))] } = some (pure (.completed false)) := rfl

theorem source_loop_insufficient_fuel_is_not_false (abi : ABI) (items capacity : Ptr) :
    execute (services abi) 0 62 (withNext items capacity 17 4)
      (OrderedDependencyCPreparationSource.reserveBody.drop 2) = pure .exhausted := rfl

end Controls

end Mettapedia.Machines.CMemory.DependencyReserveSource
