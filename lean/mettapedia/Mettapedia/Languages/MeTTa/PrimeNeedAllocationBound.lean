import Mettapedia.Languages.MeTTa.PrimeNeedCacheLaws

/-!
# Fresh allocation along owned Need executions

Every occupied cell slot lies strictly below the world's next allocation
slot. Empty heaps satisfy this invariant, and every actual reference-machine
successor preserves it, for arbitrary language specifications and generations.
Consequently a world reached from an empty heap can allocate its next cell;
this is a property of the allocator and machine, not a caller-supplied
freshness assumption.

The invariant concerns current heap entries. It neither licenses arbitrary
cache replacement nor asserts logical typing, termination or effect rollback.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeNeedAllocationBound

open PrimeNeedReference

variable {Origin Local Resume Rule Value StableFault RetryableFault Effect : Type*}

/-- The next allocation slot is strictly greater than every occupied slot. -/
def SlotBound (world : World Origin Rule Value StableFault RetryableFault Effect) : Prop :=
  ∀ cell record, world.heap.lookup cell = some record → cell.slot < world.nextCell

namespace SlotBound

theorem of_empty (world : World Origin Rule Value StableFault RetryableFault Effect)
    (empty : world.heap = Heap.empty) : SlotBound world := by
  intro cell record present
  rw [empty, Heap.empty_lookup] at present
  cases present

theorem recorded {world : World Origin Rule Value StableFault RetryableFault Effect}
    (bounded : SlotBound world)
    (payload : ReceiptPayload Origin Rule Value StableFault RetryableFault Effect) :
    SlotBound (PrimeNeedReference.recorded world payload) := bounded

theorem fork {world : World Origin Rule Value StableFault RetryableFault Effect}
    (bounded : SlotBound world) (branch : Nat) : SlotBound (world.fork branch) := bounded

theorem setKnownCache {world : World Origin Rule Value StableFault RetryableFault Effect}
    (bounded : SlotBound world) {cell : CellId}
    {record : CellRecord Origin Value StableFault}
    (present : world.heap.lookup cell = some record) (state : Cache Value StableFault) :
    SlotBound (world.setKnownCache cell record state) := by
  intro other found lookup
  change other.slot < world.nextCell
  by_cases equal : other = cell
  · subst other
    exact bounded cell record present
  · change (world.heap.setKnownCache cell record state).lookup other = some found at lookup
    rw [Heap.setKnownCache_preserves_other world.heap record state equal] at lookup
    exact bounded other found lookup

/-- Allocation increments the counter after inserting exactly its old slot. -/
theorem allocate {world next : World Origin Rule Value StableFault RetryableFault Effect}
    (bounded : SlotBound world) {origin : Origin} {generation : Nat} {cell : CellId}
    (allocated : world.allocate? origin generation = some (next, cell)) : SlotBound next := by
  intro other record present
  rw [World.allocate?_nextCell allocated]
  by_cases equal : other = cell
  · subst other
    rw [World.allocate?_fresh_cell allocated]
    exact Nat.lt_succ_self world.nextCell
  · rw [World.allocate?_preserves_other allocated equal] at present
    exact Nat.lt_trans (bounded other record present) (Nat.lt_succ_self world.nextCell)

/-- No generation at the next slot can already be occupied. -/
theorem fresh_absent {world : World Origin Rule Value StableFault RetryableFault Effect}
    (bounded : SlotBound world) (generation : Nat) :
    world.heap.lookup (world.freshCell generation) = none := by
  cases present : world.heap.lookup (world.freshCell generation) with
  | none => rfl
  | some record =>
      have impossible := bounded _ record present
      exact (Nat.lt_irrefl world.nextCell impossible).elim

/-- The actual executable allocator succeeds at the actual fresh identity,
including the generations used for explicit resampling. -/
theorem allocate_succeeds {world : World Origin Rule Value StableFault RetryableFault Effect}
    (bounded : SlotBound world) (origin : Origin) (generation : Nat) :
    ∃ next, world.allocate? origin generation = some (next, world.freshCell generation) := by
  have absent := bounded.fresh_absent generation
  simp only [World.allocate?, Heap.allocate?, absent]
  exact ⟨_, rfl⟩

theorem allocation_not_none {world : World Origin Rule Value StableFault RetryableFault Effect}
    (bounded : SlotBound world) (origin : Origin) (generation : Nat) :
    world.allocate? origin generation ≠ none := by
  obtain ⟨next, allocated⟩ := bounded.allocate_succeeds origin generation
  rw [allocated]
  intro impossible
  cases impossible

end SlotBound

/-- Every occurrence in a first-force branch retains the slot bound. Forks
change only the branch path, and beginning evaluation changes only one cache. -/
theorem branchAlternatives_slotBound
    (machine : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect)
    {base : World Origin Rule Value StableFault RetryableFault Effect}
    (bounded : SlotBound base) (cell : CellId) (record : CellRecord Origin Value StableFault)
    (present : base.heap.lookup cell = some record) (owner : EvaluatorId)
    (stack : List (Frame Resume)) (start : Nat) (alternatives : List (Rule × Local))
    {candidate : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect}
    (member : candidate ∈ branchAlternatives machine base cell record owner stack start alternatives) :
    SlotBound candidate.world := by
  induction alternatives generalizing start candidate with
  | nil => simp [branchAlternatives] at member
  | cons head tail ih =>
      simp only [branchAlternatives, List.mem_cons] at member
      rcases member with equal | member
      · subst candidate
        exact (((bounded.fork start).setKnownCache present (.evaluating owner)).recorded
          (.evaluate cell owner)).recorded (.chooseRule cell head.1)
      · exact ih (start + 1) member

/-- The slot bound is preserved by every successor occurrence of the existing
machine, including allocation, resampling, branch creation and failed commits. -/
theorem step_slotBound
    (spec : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (machine next : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (bounded : SlotBound machine.world) (member : next ∈ step spec machine) :
    SlotBound next.world := by
  rcases machine with ⟨world, control, work⟩
  change SlotBound world at bounded
  cases control with
  | halted outcome => simp [step] at member
  | force cell stack =>
      cases present : world.heap.lookup cell with
      | none =>
          simp only [step, present, List.mem_singleton] at member
          subst next
          exact bounded
      | some record =>
          obtain ⟨origin, cache⟩ := record
          cases cache with
          | suspended =>
              cases rules : spec.alternatives origin with
              | nil =>
                  simp only [step, present, rules, List.mem_singleton] at member
                  subst next
                  exact bounded
              | cons head tail =>
                  simp only [step, present, rules] at member
                  exact branchAlternatives_slotBound _
                    (base := { world with nextEvaluator := world.nextEvaluator + 1 })
                    bounded cell ⟨origin, .suspended⟩
                    present world.nextEvaluator stack 0 (head :: tail) member
          | evaluating owner =>
              simp only [step, present, List.mem_singleton] at member
              subst next
              exact bounded
          | value value =>
              simp only [step, present, List.mem_singleton] at member
              subst next
              exact bounded
          | stableFault fault =>
              simp only [step, present, List.mem_singleton] at member
              subst next
              exact bounded
  | run state stack =>
      cases action : spec.action state with
      | done outcome =>
          simp only [step, action, List.mem_singleton] at member
          subst next
          exact bounded
      | demand cell resume =>
          simp only [step, action, List.mem_singleton] at member
          subst next
          exact bounded
      | allocate origin resume =>
          cases allocated : world.allocate? origin with
          | none =>
              simp only [step, action, allocated, List.mem_singleton] at member
              subst next
              exact bounded
          | some result =>
              obtain ⟨nextWorld, fresh⟩ := result
              simp only [step, action, allocated, List.mem_singleton] at member
              subst next
              exact bounded.allocate allocated
      | resample source resume =>
          cases present : world.heap.lookup source with
          | none =>
              simp only [step, action, present, List.mem_singleton] at member
              subst next
              exact bounded
          | some record =>
              cases allocated : world.allocate? record.origin (source.generation + 1) with
              | none =>
                  simp only [step, action, present, allocated, List.mem_singleton] at member
                  subst next
                  exact bounded
              | some result =>
                  obtain ⟨nextWorld, fresh⟩ := result
                  simp only [step, action, present, allocated, List.mem_singleton] at member
                  subst next
                  exact (bounded.allocate allocated).recorded (.resample source fresh)
      | perform effect nextLocal =>
          simp only [step, action, List.mem_singleton] at member
          subst next
          exact bounded
  | returned outcome stack =>
      cases stack with
      | nil =>
          simp only [step, List.mem_singleton] at member
          subst next
          exact bounded
      | cons frame rest =>
          cases frame with
          | resume token =>
              simp only [step, List.mem_singleton] at member
              subst next
              exact bounded
          | commit cell owner =>
              cases present : world.heap.lookup cell with
              | none =>
                  simp only [step, present, List.mem_singleton] at member
                  subst next
                  exact bounded
              | some record =>
                  obtain ⟨origin, cache⟩ := record
                  cases cache with
                  | evaluating actual =>
                      by_cases sameOwner : actual = owner
                      · cases outcome with
                        | value value =>
                            simp only [step, present, dif_pos sameOwner, List.mem_singleton] at member
                            subst next
                            exact bounded.setKnownCache present (.value value)
                        | stableFault fault =>
                            simp only [step, present, dif_pos sameOwner, List.mem_singleton] at member
                            subst next
                            exact bounded.setKnownCache present (.stableFault fault)
                        | retryableFault reason =>
                            simp only [step, present, dif_pos sameOwner, List.mem_singleton] at member
                            subst next
                            exact bounded.setKnownCache present .suspended
                      · simp only [step, present, dif_neg sameOwner, List.mem_singleton] at member
                        subst next
                        exact bounded
                  | _ =>
                      simp only [step, present, List.mem_singleton] at member
                      subst next
                      exact bounded

theorem steps_slotBound
    (spec : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)
    {length : Nat}
    {initial final : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect}
    (execution : Steps spec length initial final) (bounded : SlotBound initial.world) :
    SlotBound final.world := by
  induction execution with
  | refl => exact bounded
  | cons successor _ ih =>
      exact ih (step_slotBound spec _ _ bounded (successor.mem spec))

/-- Every world reached from an empty heap has a fresh next allocation slot,
regardless of the source language, selected branch or resampling generation. -/
theorem reachable_allocate_succeeds
    (spec : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)
    {length : Nat}
    {initial final : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect}
    (execution : Steps spec length initial final) (empty : initial.world.heap = Heap.empty)
    (origin : Origin) (generation : Nat) :
    ∃ next, final.world.allocate? origin generation =
      some (next, final.world.freshCell generation) :=
  (steps_slotBound spec execution (SlotBound.of_empty initial.world empty)).allocate_succeeds
    origin generation

theorem reachable_allocation_not_none
    (spec : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)
    {length : Nat}
    {initial final : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect}
    (execution : Steps spec length initial final) (empty : initial.world.heap = Heap.empty)
    (origin : Origin) (generation : Nat) : final.world.allocate? origin generation ≠ none :=
  (steps_slotBound spec execution (SlotBound.of_empty initial.world empty)).allocation_not_none
    origin generation

/-- An arbitrary supplied heap can violate the bound: an occupied next slot
is not a valid initial state for the reachable-freshness theorem. -/
theorem occupied_next_slot_not_bounded
    {world : World Origin Rule Value StableFault RetryableFault Effect}
    {cell : CellId} {record : CellRecord Origin Value StableFault}
    (present : world.heap.lookup cell = some record) (slot : cell.slot = world.nextCell) :
    ¬ SlotBound world := by
  intro bounded
  have impossible := bounded cell record present
  rw [slot] at impossible
  exact Nat.lt_irrefl world.nextCell impossible

/-- The allocator remains fail-closed on malformed externally supplied
worlds. The invariant proves this branch unreachable; it does not delete it. -/
theorem occupied_fresh_allocation_fails
    {world : World Origin Rule Value StableFault RetryableFault Effect}
    {record : CellRecord Origin Value StableFault} {generation : Nat}
    (present : world.heap.lookup (world.freshCell generation) = some record) (origin : Origin) :
    world.allocate? origin generation = none := by
  simp only [World.allocate?, Heap.allocate?, present]

#print axioms SlotBound.of_empty
#print axioms SlotBound.allocate
#print axioms SlotBound.fresh_absent
#print axioms SlotBound.allocate_succeeds
#print axioms step_slotBound
#print axioms steps_slotBound
#print axioms reachable_allocate_succeeds
#print axioms reachable_allocation_not_none
#print axioms occupied_next_slot_not_bounded
#print axioms occupied_fresh_allocation_fails

end Mettapedia.Languages.MeTTa.PrimeNeedAllocationBound
