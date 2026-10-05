-- LLM primer: Models the running-stack contract from CeTTa's 2026-04-06
-- contract cleanup. Three-way target safety: ownedResumeSafe (can defer),
-- borrowedUnsafe (heap but borrows stack data), stackLocal (directly stack).
-- Only ownedResumeSafe targets may be deferred onto a running stack.
-- This catches the eval_visit_append_outcome bug (heap ptr to stack OutcomeSet).

import Mettapedia.Languages.MeTTa.HE.ArgFrameMachine
import Mettapedia.Machines.ResourceOwnership
import Mettapedia.Machines.RootFramePrecision

/-!
# Target-Sensitive Ownership Invariant

Formalizes CeTTa's running-stack contract after the 2026-04-06 cleanup:
> If the stack is running, only truly owned-resume-safe continuations
> may be deferred. Targets that borrow stack-local state are refused
> even if they are themselves heap-allocated.

This catches three bug classes:
1. Stack-local struct deferred directly (Bugs A-G from prior analysis)
2. Heap object that borrows stack-local callback state (eval_visit_append_outcome bug)
3. Any target not classified as owned-resume-safe

## C Seam Mapping

| Lean | C (eval.c) |
|------|-----------|
| `TargetSafety.ownedResumeSafe` | targets passing `native_resume_stack_can_defer_target` |
| `TargetSafety.borrowedUnsafe` | `eval_visit_append_outcome` (heap ptr to stack OutcomeSet) |
| `TargetSafety.stackLocal` | `QueryEvalVisitorCtx` on C stack |
| `canDefer` | `native_resume_stack_can_defer_target(stack, target)` |
| `stackForTarget` | `native_resume_stack_for_target(stack, target)` |
| `DeferSafe` | the running-stack contract invariant |
-/

namespace Mettapedia.Languages.MeTTa.HE

/-! ## Target Safety Classification -/

/-- Three-way classification of continuation target safety.

    This models CeTTa's `native_resume_stack_can_defer_target`:
    - `ownedResumeSafe`: target owns all its state, safe to outlive creator
    - `borrowedUnsafe`: target is heap-allocated but borrows stack-local data
    - `stackLocal`: target itself is on the C stack -/
inductive TargetSafety where
  | ownedResumeSafe
  | borrowedUnsafe
  | stackLocal
  deriving DecidableEq, Repr

/-- Can this target be deferred onto a running stack? -/
def TargetSafety.canDefer : TargetSafety → Bool
  | .ownedResumeSafe => true
  | .borrowedUnsafe => false
  | .stackLocal => false

/-! ## Machine State -/

/-- A worklist entry: a continuation with its target safety classification. -/
structure WorkEntry where
  safety : TargetSafety
  deriving DecidableEq, Repr

/-- Abstract machine with call stack and worklist (NativeResumeStack). -/
structure DeferMachine where
  stack    : List WorkEntry
  worklist : List WorkEntry
  deriving Repr

namespace DeferMachine

def empty : DeferMachine := ⟨[], []⟩

def pushImmediate (m : DeferMachine) (s : TargetSafety) : DeferMachine :=
  { m with stack := ⟨s⟩ :: m.stack }

def popStack (m : DeferMachine) : DeferMachine :=
  { m with stack := m.stack.tail }

/-- Defer a target onto the worklist. The contract check is EXTERNAL —
    callers must verify `canDefer` before calling this. -/
def deferToWorklist (m : DeferMachine) (s : TargetSafety) : DeferMachine :=
  { m with worklist := ⟨s⟩ :: m.worklist }

def popWorklist (m : DeferMachine) : DeferMachine :=
  { m with worklist := m.worklist.tail }

/-- The target-filtered stack: returns `some m` only if the target is safe to defer.
    Models `native_resume_stack_for_target(stack, target)`. -/
def stackForTarget (m : DeferMachine) (s : TargetSafety) : Option DeferMachine :=
  if s.canDefer then some m else none

end DeferMachine

/-! ## The Strengthened Invariant -/

/-- The running-stack deferral invariant: every entry in the worklist
    has `ownedResumeSafe` target safety.

    This is STRONGER than the old "not stackLocal" check:
    it also rejects `borrowedUnsafe` targets (heap objects that
    borrow stack-local data). -/
def DeferSafe (m : DeferMachine) : Prop :=
  ∀ e, e ∈ m.worklist → e.safety = .ownedResumeSafe

/-! ## Preservation Theorems -/

theorem deferSafe_initial : DeferSafe DeferMachine.empty := by
  intro e h; simp [DeferMachine.empty] at h

theorem deferSafe_pushImmediate (m : DeferMachine) (s : TargetSafety)
    (h : DeferSafe m) : DeferSafe (m.pushImmediate s) := by
  intro e he; simp [DeferMachine.pushImmediate] at he; exact h e he

theorem deferSafe_popStack (m : DeferMachine)
    (h : DeferSafe m) : DeferSafe (m.popStack) := h

theorem deferSafe_deferOwned (m : DeferMachine)
    (h : DeferSafe m) : DeferSafe (m.deferToWorklist .ownedResumeSafe) := by
  intro e he
  simp [DeferMachine.deferToWorklist] at he
  cases he with
  | inl heq => rw [heq]
  | inr hmem => exact h e hmem

theorem deferSafe_popWorklist (m : DeferMachine)
    (h : DeferSafe m) : DeferSafe (m.popWorklist) := by
  intro e he
  simp [DeferMachine.popWorklist] at he
  exact h e (List.tail_subset _ he)

/-! ## Violation Witnesses -/

/-- Violation 1: deferring a stack-local target breaks the invariant. -/
theorem deferStackLocal_unsafe (m : DeferMachine) :
    ¬DeferSafe (m.deferToWorklist .stackLocal) := by
  intro hsafe
  have := hsafe ⟨.stackLocal⟩ (by simp [DeferMachine.deferToWorklist])
  simp at this

/-- Violation 2: deferring a borrowedUnsafe target ALSO breaks the invariant.

    This is the NEW bug class Codex found: `eval_visit_append_outcome` is
    heap-allocated but borrows a stack-local `OutcomeSet`. The old 2-way
    model (stackLocal vs heapOwned) would NOT catch this. The 3-way model does. -/
theorem deferBorrowedUnsafe_unsafe (m : DeferMachine) :
    ¬DeferSafe (m.deferToWorklist .borrowedUnsafe) := by
  intro hsafe
  have := hsafe ⟨.borrowedUnsafe⟩ (by simp [DeferMachine.deferToWorklist])
  simp at this

/-- The stackForTarget gate: if it returns `some`, deferral is safe.
    If the target is unsafe, it returns `none`, forcing the caller
    to fall back to a non-deferred path. -/
theorem stackForTarget_safe (m : DeferMachine) (s : TargetSafety)
    (h : DeferSafe m)
    (h_some : m.stackForTarget s = some m) :
    DeferSafe (m.deferToWorklist s) := by
  simp [DeferMachine.stackForTarget, TargetSafety.canDefer] at h_some
  split at h_some <;> simp at h_some
  -- s = .ownedResumeSafe
  exact deferSafe_deferOwned m h

theorem stackForTarget_none_borrowedUnsafe (m : DeferMachine) :
    m.stackForTarget .borrowedUnsafe = none := by
  simp [DeferMachine.stackForTarget, TargetSafety.canDefer]

theorem stackForTarget_none_stackLocal (m : DeferMachine) :
    m.stackForTarget .stackLocal = none := by
  simp [DeferMachine.stackForTarget, TargetSafety.canDefer]

/-! ## Safe Operations -/

inductive SafeOp where
  | pushImmediate (s : TargetSafety)
  | popStack
  | deferOwned  -- only ownedResumeSafe may be deferred
  | popWorklist

def SafeOp.apply (m : DeferMachine) : SafeOp → DeferMachine
  | .pushImmediate s => m.pushImmediate s
  | .popStack => m.popStack
  | .deferOwned => m.deferToWorklist .ownedResumeSafe
  | .popWorklist => m.popWorklist

theorem safeOp_preserves (m : DeferMachine) (op : SafeOp)
    (h : DeferSafe m) : DeferSafe (op.apply m) := by
  cases op with
  | pushImmediate s => exact deferSafe_pushImmediate m s h
  | popStack => exact deferSafe_popStack m h
  | deferOwned => exact deferSafe_deferOwned m h
  | popWorklist => exact deferSafe_popWorklist m h

theorem safeOps_preserves (m : DeferMachine) (ops : List SafeOp)
    (h : DeferSafe m) :
    DeferSafe (ops.foldl SafeOp.apply m) := by
  induction ops generalizing m with
  | nil => exact h
  | cons op rest ih => exact ih _ (safeOp_preserves m op h)

/-! ## Examples -/

/-- Safe sequence: push borrowed (immediate only), defer owned, pop. -/
example : DeferSafe
    ([.pushImmediate .borrowedUnsafe, .deferOwned, .popWorklist].foldl
      SafeOp.apply DeferMachine.empty) :=
  safeOps_preserves _ _ deferSafe_initial

/-- The gate refuses borrowedUnsafe. -/
example : DeferMachine.empty.stackForTarget .borrowedUnsafe = none :=
  stackForTarget_none_borrowedUnsafe _

/-- The gate refuses stackLocal. -/
example : DeferMachine.empty.stackForTarget .stackLocal = none :=
  stackForTarget_none_stackLocal _

/-- The gate accepts ownedResumeSafe. -/
example : DeferMachine.empty.stackForTarget .ownedResumeSafe = some DeferMachine.empty := rfl

/-! ## Roots of the owned canonical HE frontier

The fields below follow the native frame's root registrations.  Address lists
retain slot order and multiplicity; graph collection deduplicates addresses only
for reachability.  In particular, a saved producer and a pending publication are
roots even while neither is the current task.  Root discovery in C remains a
correspondence obligation, rather than a consequence of allocating a frame on
the heap.
-/

/-- Atom-bearing field classes registered by the canonical HE frame. -/
structure HeOwnedRoots (Address : Type) where
  lexical : List Address
  live : List Address
  childAndTarget : List Address
  workAndPaths : List Address
  savedProducer : List Address
  typesAndRegisters : List Address
  argumentAndTuple : List Address
  instructions : List Address
  deriving DecidableEq

namespace HeOwnedRoots

/-- Enumerate every registered field class, including inactive saved state. -/
def slots {Address : Type} (frame : HeOwnedRoots Address) : List Address :=
  frame.lexical ++ frame.live ++ frame.childAndTarget ++ frame.workAndPaths ++
    frame.savedProducer ++ frame.typesAndRegisters ++ frame.argumentAndTuple ++ frame.instructions

/-- Transport the actual slot contents, including repeated aliases. -/
def relocate {Address Destination : Type} (f : Address → Destination)
    (frame : HeOwnedRoots Address) : HeOwnedRoots Destination where
  lexical := frame.lexical.map f
  live := frame.live.map f
  childAndTarget := frame.childAndTarget.map f
  workAndPaths := frame.workAndPaths.map f
  savedProducer := frame.savedProducer.map f
  typesAndRegisters := frame.typesAndRegisters.map f
  argumentAndTuple := frame.argumentAndTuple.map f
  instructions := frame.instructions.map f

theorem slots_relocate {Address Destination : Type} (f : Address → Destination)
    (frame : HeOwnedRoots Address) :
    (frame.relocate f).slots = frame.slots.map f := by
  simp only [slots, relocate, List.map_append]

end HeOwnedRoots

/-- Stable native frame identities label the roots they retain. -/
abbrev HeOwnedFrontier (Address : Type) := List (Nat × HeOwnedRoots Address)

def heFrontierEntries {Address : Type} (frontier : HeOwnedFrontier Address) :
    List (Nat × Address) :=
  frontier.flatMap fun frame => frame.2.slots.map fun a => (frame.1, a)

def heFrontierRoots {Address : Type} [DecidableEq Address]
    (frontier : HeOwnedFrontier Address) :
    Mettapedia.Machines.ResourceOwnership.Roots Nat Address :=
  (heFrontierEntries frontier).toFinset

@[simp] theorem mem_heFrontierRoots {Address : Type} [DecidableEq Address]
    (frontier : HeOwnedFrontier Address) (owner : Nat) (a : Address) :
    (owner, a) ∈ heFrontierRoots frontier ↔
      ∃ frame, (owner, frame) ∈ frontier ∧ a ∈ frame.slots := by
  simp only [heFrontierRoots, List.mem_toFinset, heFrontierEntries,
    List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨⟨id, frame⟩, member, slot, present, equal⟩
    cases equal
    exact ⟨frame, member, present⟩
  · rintro ⟨frame, member, present⟩
    exact ⟨(owner, frame), member, a, present, rfl⟩

def heRelocateFrontier {Address Destination : Type} (f : Address → Destination)
    (frontier : HeOwnedFrontier Address) : HeOwnedFrontier Destination :=
  frontier.map fun frame => (frame.1, frame.2.relocate f)

/-- Relocation leaves the physical slot sequence intact, including duplicates. -/
theorem heFrontierEntries_relocate {Address Destination : Type}
    (f : Address → Destination) (frontier : HeOwnedFrontier Address) :
    heFrontierEntries (heRelocateFrontier f frontier) =
      (heFrontierEntries frontier).map (fun pair => (pair.1, f pair.2)) := by
  induction frontier with
  | nil => rfl
  | cons frame rest ih =>
      simp only [heRelocateFrontier, List.map_cons, heFrontierEntries,
        List.flatMap_cons, HeOwnedRoots.slots_relocate, List.map_map, List.map_append] at *
      rw [ih]
      rfl

open Mettapedia.Machines.ResourceOwnership in
/-- The native slot transport agrees with the heap relocation's owner roots. -/
theorem heFrontierRoots_relocate {Address Destination : Type}
    {Value DestinationValue : Type} [DecidableEq Address] [DecidableEq Destination]
    {source : Heap Address Value} {destination : Heap Destination DestinationValue}
    (copy : Relocation source destination) (frontier : HeOwnedFrontier Address) :
    heFrontierRoots (heRelocateFrontier copy.address frontier) =
      copy.roots (heFrontierRoots frontier) := by
  simp only [heFrontierRoots, heFrontierEntries_relocate, Relocation.roots]
  ext pair
  simp only [List.mem_toFinset, List.mem_map, Finset.mem_image]

open Mettapedia.Machines.ResourceOwnership in
/-- Any discovered slot protects its whole transitive path, not just its payload. -/
theorem heFrontier_saved_path_survives {Address Value : Type} [DecidableEq Address]
    (heap : Heap Address Value) (frontier : HeOwnedFrontier Address)
    (owner : Nat) (frame : HeOwnedRoots Address) (a : Address) (path : List Address)
    (held : (owner, frame) ∈ frontier) (slot : a ∈ frame.slots)
    (allocated : a ∈ heap.allocated) :
    walk (collect heap (heFrontierRoots frontier)) a path = walk heap a path := by
  exact walk_collect heap _ (live_of_root heap _
    ((mem_heFrontierRoots frontier owner a).mpr ⟨frame, held, slot⟩) allocated) path

open Mettapedia.Machines.ResourceOwnership in
/-- Saved aliases remain aliases after collection; equal values do not suffice. -/
theorem heFrontier_saved_aliases {Address Value : Type} [DecidableEq Address]
    (heap : Heap Address Value) (frontier : HeOwnedFrontier Address)
    (first second : Nat) (one two : HeOwnedRoots Address) (a b : Address)
    (left right : List Address) (heldOne : (first, one) ∈ frontier)
    (heldTwo : (second, two) ∈ frontier) (slotOne : a ∈ one.slots)
    (slotTwo : b ∈ two.slots) (allocatedOne : a ∈ heap.allocated)
    (allocatedTwo : b ∈ heap.allocated) :
    Aliases (collect heap (heFrontierRoots frontier)) a left b right ↔
      Aliases heap a left b right := by
  exact aliases_collect heap _
    (live_of_root heap _ ((mem_heFrontierRoots frontier first a).mpr
      ⟨one, heldOne, slotOne⟩) allocatedOne)
    (live_of_root heap _ ((mem_heFrontierRoots frontier second b).mpr
      ⟨two, heldTwo, slotTwo⟩) allocatedTwo) left right

open Mettapedia.Machines.ResourceOwnership in
/-- Copying and collecting a frontier preserves every saved reference path. -/
theorem heFrontier_relocated_path {Address Destination Value DestinationValue : Type}
    [DecidableEq Address] [DecidableEq Destination]
    {source : Heap Address Value} {destination : Heap Destination DestinationValue}
    (copy : Relocation source destination) (frontier : HeOwnedFrontier Address)
    (owner : Nat) (frame : HeOwnedRoots Address) (a : Address) (path : List Address)
    (held : (owner, frame) ∈ frontier) (slot : a ∈ frame.slots)
    (allocated : a ∈ source.allocated) :
    walk (collect destination (heFrontierRoots (heRelocateFrontier copy.address frontier)))
      (copy.address a) (path.map copy.address) =
      (walk source a path).map fun pair =>
        (copy.address pair.1, pair.2.relocate copy.address copy.payload) := by
  rw [heFrontierRoots_relocate]
  exact copy.walk_collect_eq _ a (live_of_root source _
    ((mem_heFrontierRoots frontier owner a).mpr ⟨frame, held, slot⟩) allocated) path

/-- Cancellation removes exactly the cancelled frames' ownership labels. -/
def heCancelFrontier {Address : Type} (frontier : HeOwnedFrontier Address)
    (dead : Nat) : HeOwnedFrontier Address :=
  frontier.filter fun frame => frame.1 != dead

open Mettapedia.Machines.ResourceOwnership in
theorem heFrontierRoots_cancel {Address : Type} [DecidableEq Address]
    (frontier : HeOwnedFrontier Address) (dead : Nat) :
    heFrontierRoots (heCancelFrontier frontier dead) =
      release (heFrontierRoots frontier) dead := by
  ext pair
  rcases pair with ⟨owner, a⟩
  simp only [mem_heFrontierRoots, mem_release, heCancelFrontier,
    List.mem_filter, bne_iff_ne]
  aesop

/-- Root count is bounded by the slots actually present, including duplicate slots. -/
theorem heFrontier_root_count {Address : Type} [DecidableEq Address]
    (frontier : HeOwnedFrontier Address) :
    (heFrontierRoots frontier).card ≤ (heFrontierEntries frontier).length := by
  exact List.toFinset_card_le _

/-- Uniform per-frame slot bounds compose over a multi-frame suspended frontier. -/
theorem heFrontier_slot_bound {Address : Type} (frontier : HeOwnedFrontier Address)
    (slots : Nat) (bounded : ∀ frame ∈ frontier, frame.2.slots.length ≤ slots) :
    (heFrontierEntries frontier).length ≤ frontier.length * slots := by
  induction frontier with
  | nil => simp [heFrontierEntries]
  | cons frame rest ih =>
      have first := bounded frame (by simp)
      have later := ih (fun entry member => bounded entry (by simp [member]))
      simpa only [heFrontierEntries, List.flatMap_cons, List.length_append,
        List.length_map, List.length_cons, Nat.add_mul, Nat.one_mul, Nat.add_comm] using
        Nat.add_le_add first later

open Mettapedia.Machines.ResourceOwnership in
/-- A bound on roots alone is insufficient: each root's transitive footprint
and the byte weights must also be bounded. Shared descendants are counted once. -/
theorem heFrontier_retention_bound {Address Value : Type} [DecidableEq Address]
    (heap : Heap Address Value) (frontier : HeOwnedFrontier Address)
    (slots descendants bytes : Nat)
    (slotBound : ∀ frame ∈ frontier, frame.2.slots.length ≤ slots)
    (descendantBound : ∀ pair ∈ heFrontierRoots frontier,
      (footprint heap {pair}).card ≤ descendants)
    (byteBound : ∀ a ∈ footprint heap (heFrontierRoots frontier), cellBytes heap a ≤ bytes) :
    retainedBytes heap (heFrontierRoots frontier) ≤
      frontier.length * slots * descendants * bytes := by
  exact retainedBytes_le_root_footprints heap _ _ _ _
    ((heFrontier_root_count frontier).trans (heFrontier_slot_bound frontier slots slotBound))
    descendantBound byteBound

namespace HeOwnedRootControls

open Mettapedia.Machines.ResourceOwnership

/-- The only root is a paused producer; its two references alias a shared cycle. -/
def paused : HeOwnedRoots (Fin 3) := ⟨[], [], [], [], [0, 0], [], [], []⟩

def missing : HeOwnedRoots (Fin 3) := ⟨[], [], [], [], [], [], [], []⟩

theorem paused_producer_is_a_root :
    heFrontierEntries [(7, paused)] = [(7, 0), (7, 0)] ∧
      (collect Examples.cyclicHeap (heFrontierRoots [(7, paused)])).lookup 2 =
        Examples.cyclicHeap.lookup 2 := by
  refine ⟨rfl, ?_⟩
  apply lookup_collect_of_live
  apply live_step _ _ (a := 1) (b := 2) (c := Examples.cyclicCell 1)
  · apply live_step _ _ (a := 0) (b := 1) (c := Examples.cyclicCell 0)
    · exact live_of_root _ _ (owner := 7) (a := 0)
        (by simp [paused, HeOwnedRoots.slots]) (by decide)
    · rfl
    · decide
  · rfl
  · decide

theorem omitted_paused_producer_destroys_live_lookup :
    (collect Examples.cyclicHeap (heFrontierRoots [(7, missing)])).lookup 2 = none ∧
      Examples.cyclicHeap.lookup 2 ≠ none := by
  refine ⟨?_, by simp [Examples.cyclicHeap]⟩
  apply lookup_collect_of_not_live
  simpa [heFrontierRoots, heFrontierEntries, missing, HeOwnedRoots.slots] using
    not_live_empty Examples.cyclicHeap 2

theorem cancellation_keeps_sibling_aliases :
    Aliases (collect Examples.cyclicHeap
      (heFrontierRoots (heCancelFrontier [(7, paused), (8, paused)] 7)))
      0 [1, 2] 0 [1, 2] := by
  have live : Live Examples.cyclicHeap
      (heFrontierRoots (heCancelFrontier [(7, paused), (8, paused)] 7)) 0 :=
    live_of_root _ _ (owner := 8) (a := 0)
      (by simp [heCancelFrontier, paused, HeOwnedRoots.slots]) (by decide)
  exact (aliases_collect _ _ live live _ _).mpr ⟨2, by decide, by decide⟩

end HeOwnedRootControls

end Mettapedia.Languages.MeTTa.HE
