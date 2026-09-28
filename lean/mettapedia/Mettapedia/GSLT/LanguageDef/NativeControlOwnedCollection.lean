import Mettapedia.GSLT.LanguageDef.NativeControlBoundedCursor
import Mettapedia.Machines.Cursor.OwnedLifecycle

/-!
# Pinning answer graphs between bounded collection polls

The adapter roots each yielded address under a buffer owner before another
provider poll can run. A raw provider must already return an allocated exported
answer, and each raw transition must preserve the buffer's existing roots and
the full cells reachable from them. These are local transition obligations;
other cells, other roots, branch state and the semantic world may change.

Induction over the existing bounded collector proves that every occurrence in
every returned prefix is still pinned and allocated. Independently capturing
the full cell at each yield gives exactly the final cell observations, including
duplicates. Publication can then transfer the answers to an owner outside the
cancelled scope and release the buffer roots without losing those observations.

The model does not discover C roots or repair a raw provider that rolls back an
answer before exporting it. Complete strong-reference interpretation, concrete
handle lifetimes, moving collection and effectful finalization remain runtime
obligations. Buffer protection here promises immutable cell observations;
clients choosing shared mutable answers need a different observation contract.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeControlOwnedCollection

open Mettapedia.Machines.ResourceOwnership
open Mettapedia.Machines.Cursor
open Mettapedia.Machines.Cursor.OwnedLifecycle (Session observe)
open HostCalls (Pull)
open NativeControlBoundedCursor (collectBounded)

variable {Owner Address Value World HState : Type}
  [DecidableEq Owner] [DecidableEq Address]

def bufferRoots (buffer : Owner) (roots : Roots Owner Address) : Roots Owner Address :=
  roots.filter (fun pair => pair.1 = buffer)

omit [DecidableEq Address] in
@[simp] theorem mem_bufferRoots (buffer owner : Owner) (address : Address)
    (roots : Roots Owner Address) :
    (owner, address) ∈ bufferRoots buffer roots ↔
      (owner, address) ∈ roots ∧ owner = buffer := by simp [bufferRoots]

abbrev Protected (buffer : Owner) (state : Session Owner Address Value World)
    (address : Address) : Prop := Live state.heap (bufferRoots buffer state.roots) address

def Pinned (buffer : Owner) (state : Session Owner Address Value World)
    (address : Address) : Prop :=
  (buffer, address) ∈ state.roots ∧ address ∈ state.heap.allocated

def Buffered (buffer : Owner) (state : Session Owner Address Value World)
    (answers : List Address) : Prop := ∀ address ∈ answers, Pinned buffer state address

theorem Pinned.protected {buffer : Owner} {state : Session Owner Address Value World}
    {address : Address} (pinned : Pinned buffer state address) :
    Protected buffer state address :=
  live_of_root state.heap _ ((mem_bufferRoots _ _ _ _).mpr ⟨pinned.1, rfl⟩) pinned.2

/-- Local preservation of root slots and immutable cells, not an assumed
whole-collector observation theorem. -/
structure Protects (buffer : Owner) (before after : Session Owner Address Value World) : Prop where
  roots : ∀ address, (buffer, address) ∈ before.roots → (buffer, address) ∈ after.roots
  cells : ∀ address, Protected buffer before address →
    after.heap.lookup address = before.heap.lookup address

theorem Protects.refl (buffer : Owner) (state : Session Owner Address Value World) :
    Protects buffer state state := ⟨fun _ h => h, fun _ _ => rfl⟩

theorem Protects.allocated {buffer : Owner} {before after : Session Owner Address Value World}
    (protection : Protects buffer before after) {address : Address}
    (live : Protected buffer before address) : address ∈ after.heap.allocated := by
  obtain ⟨cell, found⟩ := (before.heap.allocated_iff address).mp (live_allocated _ _ live)
  exact (after.heap.allocated_iff address).mpr
    ⟨cell, (protection.cells address live).trans found⟩

theorem Protects.live {buffer : Owner} {before after : Session Owner Address Value World}
    (protection : Protects buffer before after) {address : Address}
    (live : Protected buffer before address) : Protected buffer after address := by
  induction live with
  | @root address rooted =>
      obtain ⟨⟨owner, origin⟩, member, same⟩ := Finset.mem_image.mp rooted.2
      have owned := (mem_bufferRoots buffer owner origin before.roots).mp member
      have oldMember : (buffer, origin) ∈ before.roots := owned.2 ▸ owned.1
      exact .root ⟨protection.allocated (.root rooted), Finset.mem_image.mpr
        ⟨(buffer, origin), (mem_bufferRoots _ _ _ _).mpr
          ⟨protection.roots origin oldMember, rfl⟩, same⟩⟩
  | @step previous address prior edge ih =>
      obtain ⟨cell, found, reference⟩ := edge
      exact live_step after.heap _ ih ((protection.cells previous prior).trans found) reference

theorem Protects.trans {buffer : Owner} {first second third : Session Owner Address Value World}
    (left : Protects buffer first second) (right : Protects buffer second third) :
    Protects buffer first third where
  roots address member := right.roots address (left.roots address member)
  cells address live := (right.cells address (left.live live)).trans (left.cells address live)

theorem Protects.pinned {buffer : Owner} {before after : Session Owner Address Value World}
    (protection : Protects buffer before after) {address : Address}
    (pinned : Pinned buffer before address) : Pinned buffer after address :=
  ⟨protection.roots address pinned.1, protection.allocated pinned.protected⟩

theorem Protects.buffered {buffer : Owner} {before after : Session Owner Address Value World}
    (protection : Protects buffer before after) {answers : List Address}
    (buffered : Buffered buffer before answers) : Buffered buffer after answers := by
  intro address member
  exact protection.pinned (buffered address member)

/-- Every finite path through an already pinned graph keeps its full endpoint
observation, even when unrelated cells are removed or changed. -/
theorem Protects.walk {buffer : Owner} {before after : Session Owner Address Value World}
    (protection : Protects buffer before after) {address : Address}
    (live : Protected buffer before address) (path : List Address) :
    walk after.heap address path = walk before.heap address path := by
  induction path generalizing address with
  | nil => simp only [Mettapedia.Machines.ResourceOwnership.walk, protection.cells address live]
  | cons next rest ih =>
      simp only [Mettapedia.Machines.ResourceOwnership.walk, protection.cells address live]
      obtain ⟨cell, found⟩ := (before.heap.allocated_iff address).mp (live_allocated _ _ live)
      simp only [found, Option.bind_some]
      split
      next reference => exact ih (live_step before.heap _ live found reference)
      next _ => rfl

theorem Protects.aliases {buffer : Owner} {before after : Session Owner Address Value World}
    (protection : Protects buffer before after) {left right : Address}
    (leftLive : Protected buffer before left) (rightLive : Protected buffer before right)
    (leftPath rightPath : List Address) :
    Aliases after.heap left leftPath right rightPath ↔
      Aliases before.heap left leftPath right rightPath := by
  simp only [Aliases, protection.walk leftLive, protection.walk rightLive]

def pin (buffer : Owner) (state : Session Owner Address Value World) (answer : Address) :
    Session Owner Address Value World :=
  { state with roots := insert (buffer, answer) state.roots }

theorem pin_protects (buffer : Owner) (state : Session Owner Address Value World)
    (answer : Address) : Protects buffer state (pin buffer state answer) where
  roots _ member := Finset.mem_insert_of_mem member
  cells _ _ := rfl

abbrev RawPull (HState Owner Address Value World : Type)
    [DecidableEq Owner] [DecidableEq Address] :=
  HState → Session Owner Address Value World →
    Session Owner Address Value World × Pull HState Address

/-- The provider's two obligations apply to each individual poll, including
suspension and exhaustion. Its world and unprotected heap are unrestricted. -/
structure LawfulRaw (buffer : Owner) (raw : RawPull HState Owner Address Value World) : Prop where
  preserves : ∀ cursor state, Protects buffer state (raw cursor state).1
  yielded : ∀ cursor state answer residual,
    (raw cursor state).2 = .yield answer residual → answer ∈ (raw cursor state).1.heap.allocated

/-- Root publication is the first adapter action after a raw yield, before
the bounded collector can make any subsequent provider call. -/
def pinPull (buffer : Owner) (raw : RawPull HState Owner Address Value World) :
    RawPull HState Owner Address Value World := fun cursor state =>
  let pulled := raw cursor state
  match pulled.2 with
  | .yield answer residual => (pin buffer pulled.1 answer, .yield answer residual)
  | .suspend residual => (pulled.1, .suspend residual)
  | .done => (pulled.1, .done)

theorem pinPull_protects (buffer : Owner) (raw : RawPull HState Owner Address Value World)
    (lawful : LawfulRaw buffer raw) (cursor : HState) (state : Session Owner Address Value World) :
    Protects buffer state (pinPull buffer raw cursor state).1 := by
  have preserved := lawful.preserves cursor state
  cases pulled : raw cursor state with
  | mk next reply =>
      rw [pulled] at preserved
      cases reply with
      | done => simpa [pinPull, pulled] using preserved
      | suspend residual => simpa [pinPull, pulled] using preserved
      | yield answer residual =>
          simpa [pinPull, pulled] using preserved.trans (pin_protects buffer next answer)

theorem pinPull_yield_pinned (buffer : Owner) (raw : RawPull HState Owner Address Value World)
    (lawful : LawfulRaw buffer raw) (cursor : HState)
    (state next : Session Owner Address Value World) (answer : Address) (residual : HState)
    (yielded : pinPull buffer raw cursor state = (next, .yield answer residual)) :
    Pinned buffer next answer := by
  cases pulled : raw cursor state with
  | mk intermediate reply =>
      cases reply with
      | done => simp [pinPull, pulled] at yielded
      | suspend remaining => simp [pinPull, pulled] at yielded
      | yield value remaining =>
          have allocated := lawful.yielded cursor state value remaining (by rw [pulled])
          rw [pulled] at allocated
          simp only [pinPull, pulled, Prod.mk.injEq, Pull.yield.injEq] at yielded
          rcases yielded with ⟨rfl, rfl, rfl⟩
          exact ⟨Finset.mem_insert_self _ _, allocated⟩

/-- Every bounded prefix, even one stopped by the inspection budget, owns all
its answer occurrences and preserves all graphs pinned before this run. -/
theorem collect_invariant (buffer : Owner) (raw : RawPull HState Owner Address Value World)
    (lawful : LawfulRaw buffer raw) :
    ∀ (fuel allowance : Nat) (cursor : HState) (state : Session Owner Address Value World),
      let result := (collectBounded (pinPull buffer raw) fuel allowance cursor state).2
      Protects buffer state result.world ∧ Buffered buffer result.world result.answers
  | _, 0, _, _ => by
      simp only [collectBounded]
      exact ⟨.refl _ _, by simp [Buffered]⟩
  | 0, _ + 1, _, _ => ⟨.refl _ _, by simp [Buffered, collectBounded]⟩
  | fuel + 1, remaining + 1, cursor, state => by
      have step := pinPull_protects buffer raw lawful cursor state
      cases pulled : pinPull buffer raw cursor state with
      | mk next reply =>
          rw [pulled] at step
          cases reply with
          | done => exact ⟨by simpa [collectBounded, pulled] using step,
              by simp [collectBounded, pulled, Buffered]⟩
          | suspend residual =>
              have rest := collect_invariant buffer raw lawful fuel (remaining + 1) residual next
              simpa only [collectBounded, pulled] using ⟨step.trans rest.1, rest.2⟩
          | yield answer residual =>
              have rest := collect_invariant buffer raw lawful fuel remaining residual next
              have pinned := pinPull_yield_pinned buffer raw lawful cursor state next answer residual pulled
              simp only [collectBounded, pulled, NativeControlBoundedCursor.Snapshot.prefix,
                List.singleton_append]
              refine ⟨step.trans rest.1, ?_⟩
              intro address member
              rcases List.mem_cons.mp member with rfl | member
              · exact rest.1.pinned pinned
              · exact rest.2 address member

/-- Per-yield observations are captured before later polls. This is a ghost
reference traversal, not an additional execution of provider effects. -/
def captured (buffer : Owner) (raw : RawPull HState Owner Address Value World) :
    Nat → Nat → HState → Session Owner Address Value World → List (Option (Cell Address Value))
  | _, 0, _, _ => []
  | 0, _ + 1, _, _ => []
  | fuel + 1, remaining + 1, cursor, state =>
      let pulled := pinPull buffer raw cursor state
      match pulled.2 with
      | .done => []
      | .suspend residual => captured buffer raw fuel (remaining + 1) residual pulled.1
      | .yield answer residual =>
          pulled.1.heap.lookup answer :: captured buffer raw fuel remaining residual pulled.1

/-- Late observation equals the independent full cell snapshot taken at each
yield. The equality is occurrence-wise, so duplicates are not quotiented. -/
theorem captured_eq_final (buffer : Owner) (raw : RawPull HState Owner Address Value World)
    (lawful : LawfulRaw buffer raw) :
    ∀ (fuel allowance : Nat) (cursor : HState) (state : Session Owner Address Value World),
      let result := (collectBounded (pinPull buffer raw) fuel allowance cursor state).2
      captured buffer raw fuel allowance cursor state = observe result.world.heap result.answers
  | _, 0, _, _ => by simp [captured, collectBounded, observe]
  | 0, _ + 1, _, _ => rfl
  | fuel + 1, remaining + 1, cursor, state => by
      cases pulled : pinPull buffer raw cursor state with
      | mk next reply =>
          cases reply with
          | done => simp [captured, collectBounded, pulled, observe]
          | suspend residual =>
              simpa only [captured, collectBounded, pulled] using
                captured_eq_final buffer raw lawful fuel (remaining + 1) residual next
          | yield answer residual =>
              have rest := collect_invariant buffer raw lawful fuel remaining residual next
              have pinned := pinPull_yield_pinned buffer raw lawful cursor state next answer residual pulled
              simp only [captured, collectBounded, pulled,
                NativeControlBoundedCursor.Snapshot.prefix, List.singleton_append,
                observe, List.map_cons]
              rw [captured_eq_final buffer raw lawful fuel remaining residual next]
              rw [rest.1.cells answer pinned.protected]
              rfl

/-- The native reverse-accumulator client inherits the same safety invariant,
including a preexisting pinned prefix when resuming a collecting client. -/
theorem client_buffered (buffer : Owner) (raw : RawPull HState Owner Address Value World)
    (lawful : LawfulRaw buffer raw) (fuel allowance : Nat) (cursor : HState)
    (state : Session Owner Address Value World) (reversed : List Address)
    (previous : Buffered buffer state reversed.reverse) :
    let actual := advance (NativeControlEffectCursor.provider (pinPull buffer raw))
      (NativeControlBoundedCursor.client Address) (fun _ _ => 1) fuel
      (NativeControlBoundedCursor.packet (pinPull buffer raw) allowance cursor state reversed)
    let result := NativeControlBoundedCursor.readout (pinPull buffer raw) actual.2
    Protects buffer state result.world ∧ Buffered buffer result.world result.answers := by
  have observation := congrArg Prod.snd
    (NativeControlBoundedCursor.readout_exact (pinPull buffer raw) fuel allowance cursor state reversed)
  dsimp only at observation ⊢
  rw [observation]
  have invariant := collect_invariant buffer raw lawful fuel allowance cursor state
  refine ⟨invariant.1, ?_⟩
  intro address member
  rcases List.mem_append.mp member with prior | current
  · exact invariant.1.pinned (previous address prior)
  · exact invariant.2 address current

/-- An outside owner receives every answer before the buffer owner is
cancelled. The provider's final world and per-yield observations survive. -/
theorem publish_then_release (buffer : Owner) (raw : RawPull HState Owner Address Value World)
    (lawful : LawfulRaw buffer raw) (fuel allowance : Nat) (cursor : HState)
    (state : Session Owner Address Value World) (dead : Finset Owner) (output : Owner)
    (bufferDead : buffer ∈ dead) (outside : output ∉ dead) :
    let result := (collectBounded (pinPull buffer raw) fuel allowance cursor state).2
    let published := OwnedLifecycle.commit result.world dead output result.answers
    observe published.heap result.answers = captured buffer raw fuel allowance cursor state ∧
      (∀ address, (buffer, address) ∉ published.roots) ∧
      published.world = result.world.world := by
  dsimp only
  have invariant := collect_invariant buffer raw lawful fuel allowance cursor state
  constructor
  · rw [OwnedLifecycle.commit_preserves_selected_observation _ dead output _ outside
      (fun address member => (invariant.2 address member).2)]
    exact (captured_eq_final buffer raw lawful fuel allowance cursor state).symm
  · constructor
    · intro address member
      exact (mem_cancel _ dead (buffer, address)).mp member |>.2 bufferDead
    · rfl

namespace Controls

open Mettapedia.Machines.ResourceOwnership.Examples

abbrev DemoSession := Session Nat (Fin 3) Nat Nat

/-- Every later poll really collects, and changes the semantic world. -/
noncomputable def sweep (state : DemoSession) : DemoSession :=
  ⟨collect state.heap state.roots, state.roots, state.world + 1⟩

theorem sweep_protects (buffer : Nat) (state : DemoSession) :
    Protects buffer state (sweep state) where
  roots _ member := member
  cells _ live := lookup_collect_of_live state.heap state.roots
    (live_mono state.heap (Finset.filter_subset _ _) live)

/-- Two yields of the same address, then suspension and exhaustion. Allocation
is tested at each yield, so this provider is lawful on arbitrary input heaps. -/
noncomputable def raw : RawPull Nat Nat (Fin 3) Nat Nat
  | 0, state =>
      let next := { state with world := state.world + 1 }
      if 1 ∈ state.heap.allocated then (next, .yield 1 1) else (next, .done)
  | 1, state =>
      let next := sweep state
      if 1 ∈ next.heap.allocated then (next, .yield 1 2) else (next, .done)
  | 2, state => (sweep state, .suspend 3)
  | _ + 3, state => (sweep state, .done)

theorem raw_lawful (buffer : Nat) : LawfulRaw buffer raw where
  preserves cursor state := by
    rcases cursor with _ | (_ | (_ | cursor))
    · simp only [raw]
      split <;> exact ⟨fun _ member => member, fun _ _ => rfl⟩
    · simp only [raw]
      split <;> exact sweep_protects buffer state
    · exact sweep_protects buffer state
    · exact sweep_protects buffer state
  yielded cursor state answer residual yielded := by
    rcases cursor with _ | (_ | (_ | cursor))
    · by_cases allocated : 1 ∈ state.heap.allocated
      · simp only [raw, if_pos allocated, Pull.yield.injEq] at yielded
        obtain ⟨rfl, rfl⟩ := yielded
        simp [raw, allocated]
      · simp [raw, allocated] at yielded
    · by_cases allocated : 1 ∈ (sweep state).heap.allocated
      · simp only [raw, if_pos allocated, Pull.yield.injEq] at yielded
        obtain ⟨rfl, rfl⟩ := yielded
        simp [raw, allocated]
      · simp [raw, allocated] at yielded
    · simp [raw] at yielded
    · simp [raw] at yielded

def initial : DemoSession := ⟨cyclicHeap, ∅, 0⟩
def first : DemoSession := pin 0 { initial with world := 1 } 1
noncomputable def second : DemoSession := pin 0 (sweep first) 1
noncomputable def third : DemoSession := sweep second
noncomputable def finalState : DemoSession := sweep third

theorem first_pinned : Pinned 0 first 1 := by
  constructor
  · exact Finset.mem_insert_self _ _
  · exact Finset.mem_univ _

theorem first_poll : pinPull 0 raw 0 initial = (first, .yield 1 1) := by
  simp [pinPull, raw, initial, cyclicHeap, first]

theorem second_poll : pinPull 0 raw 1 first = (second, .yield 1 2) := by
  have allocated := (sweep_protects 0 first).allocated first_pinned.protected
  simp [pinPull, raw, allocated, second]

theorem suspension_poll : pinPull 0 raw 2 second = (third, .suspend 3) := rfl
theorem final_poll : pinPull 0 raw 3 third = (finalState, .done) := rfl

theorem delayed_duplicate_collection :
    collectBounded (pinPull 0 raw) 4 3 0 initial =
      (4, ⟨3, finalState, [1, 1], 1, .exhausted⟩) := by
  simp only [collectBounded, first_poll, second_poll, suspension_poll, final_poll,
    NativeControlBoundedCursor.Snapshot.prefix, List.singleton_append]

theorem final_one : finalState.heap.lookup 1 = some (cyclicCell 1) := by
  have preserved := ((sweep_protects 0 first).trans (pin_protects 0 (sweep first) 1)).trans
    ((sweep_protects 0 second).trans (sweep_protects 0 third))
  exact (preserved.cells 1 first_pinned.protected).trans rfl

/-- No edge in the cycle can reach node zero after its root is absent. -/
theorem first_cannot_reach_zero : ¬ Live first.heap first.roots 0 := by
  intro live
  cases live with
  | root rooted =>
      simpa [Heap.toStore, first, pin, initial, rootAddresses] using rooted.2
  | @step previous _ prior edge =>
      obtain ⟨cell, found, reference⟩ := edge
      change some (cyclicCell previous) = some cell at found
      cases found
      by_cases zero : previous = 0
      · simp [cyclicCell, zero] at reference
      · by_cases one : previous = 1 <;> simp [cyclicCell, zero, one] at reference

theorem sweep_absent (state : DemoSession) (address : Fin 3)
    (absent : state.heap.lookup address = none) :
    (sweep state).heap.lookup address = none := by
  classical
  simp [sweep, collect, absent]

/-- The local protection law still permits real reclamation of unrelated
resources; it does not freeze the entire heap or world. -/
theorem unrelated_cell_reclaimed : finalState.heap.lookup 0 = none := by
  have removed : (sweep first).heap.lookup 0 = none :=
    lookup_collect_of_not_live first.heap first.roots first_cannot_reach_zero
  exact sweep_absent third 0 (sweep_absent second 0 removed)

theorem duplicate_observations_and_effects :
    let result := (collectBounded (pinPull 0 raw) 4 3 0 initial).2
    observe result.world.heap result.answers = [some (cyclicCell 1), some (cyclicCell 1)] ∧
      result.world.world = 4 ∧ result.world.heap.lookup 0 = none := by
  rw [delayed_duplicate_collection]
  exact ⟨by simp [observe, final_one], rfl, unrelated_cell_reclaimed⟩

/-- Budget suspension retains the first occurrence before its duplicate has
been requested, including its allocated resource graph. -/
theorem partial_prefix_is_pinned :
    let result := (collectBounded (pinPull 0 raw) 1 3 0 initial).2
    result.answers = [1] ∧ result.stop = .budget ∧ Buffered 0 result.world result.answers := by
  constructor
  · simp [collectBounded, first_poll, NativeControlBoundedCursor.Snapshot.prefix]
  · constructor
    · simp [collectBounded, first_poll, NativeControlBoundedCursor.Snapshot.prefix]
    · exact (collect_invariant 0 raw (raw_lawful 0) 1 3 0 initial).2

def unpinnedFirst : DemoSession := { initial with world := 1 }

theorem unpinned_first_poll : raw 0 initial = (unpinnedFirst, .yield 1 1) := by
  simp [raw, initial, cyclicHeap, unpinnedFirst]

theorem unpinned_missing : 1 ∉ (sweep unpinnedFirst).heap.allocated := by
  change 1 ∉ footprint cyclicHeap (∅ : Roots Nat (Fin 3))
  rw [mem_footprint]
  exact not_live_empty cyclicHeap 1

theorem unpinned_second_poll : raw 1 unpinnedFirst = (sweep unpinnedFirst, .done) := by
  simp [raw, unpinned_missing]

/-- The same locally lawful raw provider loses its first answer if the adapter
does not pin it: the returned address remains, but its cell is gone. -/
theorem unpinned_early_answer_is_lost :
    let result := (collectBounded raw 4 3 0 initial).2
    result.answers = [1] ∧ observe result.world.heap result.answers = [none] := by
  have missing : (sweep unpinnedFirst).heap.lookup 1 = none :=
    lookup_collect_of_not_live cyclicHeap (∅ : Roots Nat (Fin 3)) (not_live_empty cyclicHeap 1)
  simp only [collectBounded, unpinned_first_poll, unpinned_second_poll,
    NativeControlBoundedCursor.Snapshot.prefix, List.singleton_append]
  exact ⟨by trivial, by simp [observe, missing]⟩

end Controls

end Mettapedia.GSLT.LanguageDef.NativeControlOwnedCollection
