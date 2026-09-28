import Mettapedia.GSLT.LanguageDef.NativeControlBoundedCursor
import Mettapedia.GSLT.LanguageDef.NativeControlTwoStackCut
import Mettapedia.GSLT.LanguageDef.NativeControlOwnedCollection
import Mettapedia.Machines.Cursor.OwnedLifecycle

/-!
# Bounded observation, scoped cancellation, and answer ownership

The bounded client retains its actual residual when a scheduler pauses. Once
the client returns, the adapter publishes its answer roots to an owner outside
the delimiter, cuts both physical stacks, and collects the graph reachable
from the retained owners. This connects the existing cursor execution, the
two-stack decoder, and finite resource ownership without introducing another
evaluator or a language-level stream syntax.

Owner tags identify positions in one stack snapshot. Reusing a physical slot
requires a fresh lifetime identity or an independently enforced linear token.
All references retained by a continuation, closure, pending answer, foreign
value or memo cell must appear in the heap/root interpretation. The adapter
does not discover those C roots or prove an allocator's release operation.

The answer list records occurrences, while the root set records shared storage.
Generic heap payloads may represent higher-order closures. Raised exceptions,
effectful finalizers and concurrent mutation require additional transitions;
they are not encoded as ordinary answer values here.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeControlOwnedCursor

open Mettapedia.Machines.ResourceOwnership
open Mettapedia.Machines.Cursor
open HostCalls (Pull)


variable {Caller Address Value World Task : Type}
  [DecidableEq Caller] [DecidableEq Address]

/-- Positions identify owning root slots in this snapshot, not reusable handles. -/
inductive Owner (Caller : Type) where
  | caller (identity : Caller)
  | tier (position : Nat)
  | host (position : Nat)
  deriving DecidableEq, Repr

def inside (mark : NativeControlTwoStackCut.Mark) : Owner Caller → Bool
  | .caller _ => false
  | .tier position => decide (mark.tierHeight ≤ position)
  | .host position => decide (mark.hostHeight ≤ position)

def deadOwners (roots : Roots (Owner Caller) Address) (mark : NativeControlTwoStackCut.Mark) :
    Finset (Owner Caller) :=
  (roots.image Prod.fst).filter (fun owner => inside mark owner = true)

omit [DecidableEq Address] in
theorem rooted_owner_dead_iff (roots : Roots (Owner Caller) Address)
    (mark : NativeControlTwoStackCut.Mark) (owner : Owner Caller) (address : Address)
    (member : (owner, address) ∈ roots) :
    owner ∈ deadOwners roots mark ↔ inside mark owner = true := by
  constructor
  · intro dead
    exact (Finset.mem_filter.mp dead).2
  · intro dead
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_image.mpr ⟨(owner, address), member, rfl⟩, dead⟩

/-- An export destination survives this cut. It may be an enclosing frame,
so a later outer cut can release it; it need not be a session-wide owner. -/
structure Destination (Caller : Type) (mark : NativeControlTwoStackCut.Mark) where
  owner : Owner Caller
  outside : inside mark owner = false

def Destination.external (mark : NativeControlTwoStackCut.Mark) (caller : Caller) :
    Destination Caller mark := ⟨.caller caller, rfl⟩

def Destination.tier (mark : NativeControlTwoStackCut.Mark) (position : Nat)
    (below : position < mark.tierHeight) : Destination Caller mark :=
  ⟨.tier position, by simp [inside]; omega⟩

def Destination.host (mark : NativeControlTwoStackCut.Mark) (position : Nat)
    (below : position < mark.hostHeight) : Destination Caller mark :=
  ⟨.host position, by simp [inside]; omega⟩

omit [DecidableEq Address] in
@[simp] theorem destination_not_dead (roots : Roots (Owner Caller) Address)
    (mark : NativeControlTwoStackCut.Mark) (destination : Destination Caller mark) :
    destination.owner ∉ deadOwners roots mark := by
  intro member
  have impossible := (Finset.mem_filter.mp member).2
  rw [destination.outside] at impossible
  cases impossible

omit [DecidableEq Address] in
/-- A root survives exactly when its physical owner is below the matching
stack height, or is an external caller. Host and tier heights are independent. -/
theorem retained_root_iff (roots : Roots (Owner Caller) Address)
    (mark : NativeControlTwoStackCut.Mark) (owner : Owner Caller) (address : Address) :
    (owner, address) ∈ cancel roots (deadOwners roots mark) ↔
      (owner, address) ∈ roots ∧ ¬ inside mark owner = true := by
  rw [mem_cancel]
  constructor
  · rintro ⟨member, retained⟩
    exact ⟨member, fun dead => retained
      ((rooted_owner_dead_iff roots mark owner address member).mpr dead)⟩
  · rintro ⟨member, retained⟩
    exact ⟨member, fun dead => retained
      ((rooted_owner_dead_iff roots mark owner address member).mp dead)⟩

abbrev Session (Caller Address Value World : Type)
    [DecidableEq Caller] [DecidableEq Address] :=
  OwnedLifecycle.Session (Owner Caller) Address Value World

abbrev State (Task Caller Address Value World : Type)
    [DecidableEq Caller] [DecidableEq Address] :=
  NativeControlTwoStackCut.State Task (List Address) (Session Caller Address Value World)

/-- Answer publication precedes releasing the delimited frame owners. -/
noncomputable def commit (mark : NativeControlTwoStackCut.Mark) (destination : Destination Caller mark)
    (state : State Task Caller Address Value World) :
    State Task Caller Address Value World :=
  ⟨NativeControlTwoStackCut.truncate mark state.choices, state.selected,
    OwnedLifecycle.commit state.world (deadOwners state.world.roots mark)
      destination.owner state.selected⟩

/-- Resource bookkeeping is erased only after checking its observations. -/
def eraseResources (state : State Task Caller Address Value World) :
    NativeControlTwoStackCut.State Task (List Address) World :=
  ⟨state.choices, state.selected, state.world.world⟩

theorem commit_erases_to_cut (mark : NativeControlTwoStackCut.Mark) (destination : Destination Caller mark)
    (state : State Task Caller Address Value World) :
    eraseResources (commit mark destination state) =
      NativeControlTwoStackCut.commit mark (eraseResources state) := rfl

theorem commit_preserves_answers (mark : NativeControlTwoStackCut.Mark) (destination : Destination Caller mark)
    (state : State Task Caller Address Value World)
    (allocated : ∀ address ∈ state.selected, address ∈ state.world.heap.allocated) :
    OwnedLifecycle.observe (commit mark destination state).world.heap state.selected =
      OwnedLifecycle.observe state.world.heap state.selected :=
  OwnedLifecycle.commit_preserves_selected_observation state.world _ destination.owner
    state.selected (destination_not_dead _ _ _) allocated

/-- Shared descendants of an answer survive even when the old cursor root
that originally reached them is one of the cancelled frame owners. -/
theorem commit_preserves_answer_graph (mark : NativeControlTwoStackCut.Mark) (destination : Destination Caller mark)
    (state : State Task Caller Address Value World) (address : Address)
    (live : Live state.world.heap
      (OwnedLifecycle.answerRoots destination.owner state.selected) address) :
    (commit mark destination state).world.heap.lookup address =
      state.world.heap.lookup address :=
  OwnedLifecycle.commit_preserves_answer_graph state.world _ destination.owner
    state.selected (destination_not_dead _ _ _) live

theorem commit_preserves_retained_graph (mark : NativeControlTwoStackCut.Mark) (destination : Destination Caller mark)
    (state : State Task Caller Address Value World) (address : Address)
    (live : Live state.world.heap
      (cancel state.world.roots (deadOwners state.world.roots mark)) address) :
    (commit mark destination state).world.heap.lookup address =
      state.world.heap.lookup address :=
  OwnedLifecycle.commit_preserves_outer_graph state.world _ destination.owner
    state.selected (destination_not_dead _ _ _) live

theorem commit_reclaims_discarded_graph (mark : NativeControlTwoStackCut.Mark) (destination : Destination Caller mark)
    (state : State Task Caller Address Value World) (address : Address)
    (notOuter : ¬ Live state.world.heap
      (cancel state.world.roots (deadOwners state.world.roots mark)) address)
    (notAnswer : ¬ Live state.world.heap
      (OwnedLifecycle.answerRoots destination.owner state.selected) address) :
    (commit mark destination state).world.heap.lookup address = none :=
  OwnedLifecycle.commit_reclaims_unprotected state.world _ destination.owner
    state.selected (destination_not_dead _ _ _) address notOuter notAnswer

/-- The cut removes every root owned inside its two boundaries, including a
collection buffer. An outside destination cannot reintroduce such an owner. -/
theorem commit_cancels_inner_roots (mark : NativeControlTwoStackCut.Mark)
    (destination : Destination Caller mark) (state : State Task Caller Address Value World)
    (owner : Owner Caller) (internal : inside mark owner = true) (address : Address) :
    (owner, address) ∉ (commit mark destination state).world.roots := by
  intro member
  have parts := (mem_cancel _ _ (owner, address)).mp member
  rcases Finset.mem_union.mp parts.1 with old | exported
  · exact parts.2 ((rooted_owner_dead_iff _ _ _ _ old).mpr internal)
  · have same := (OwnedLifecycle.mem_answerRoots _ _ _ _).mp exported |>.1
    rw [same, destination.outside] at internal
    cases internal

/-- The same cut law preserves its full semantic observation and every
selected cell, not merely the mathematical address of the witness. -/
theorem commit_observation (mark : NativeControlTwoStackCut.Mark) (destination : Destination Caller mark)
    (state : State Task Caller Address Value World)
    (allocated : ∀ address ∈ state.selected, address ∈ state.world.heap.allocated) :
    eraseResources (commit mark destination state) =
        NativeControlTwoStackCut.commit mark (eraseResources state) ∧
      OwnedLifecycle.observe (commit mark destination state).world.heap state.selected =
        OwnedLifecycle.observe state.world.heap state.selected :=
  ⟨commit_erases_to_cut mark destination state,
    commit_preserves_answers mark destination state allocated⟩

section Execution

variable (pull : NativeControlTwoStackCut.Layout Task → Session Caller Address Value World →
  Session Caller Address Value World × Pull (NativeControlTwoStackCut.Layout Task) Address)

/-- A scheduling pause retains the actual packet. Only a client return can
trigger abandonment; a partial answer buffer is not a completed collection. -/
inductive Exit where
  | paused (packet : Packet (NativeControlEffectCursor.provider pull)
      (NativeControlBoundedCursor.client Address) ())
  | selected (selection : NativeControlBoundedCursor.Selection Address)
      (state : State Task Caller Address Value World)

noncomputable def finish (mark : NativeControlTwoStackCut.Mark) (destination : Destination Caller mark) :
    Outcome (NativeControlEffectCursor.provider pull) (NativeControlBoundedCursor.client Address) () →
      Exit pull
  | .paused packet => .paused packet
  | .done ⟨_, selection, (residual, world)⟩ =>
      .selected selection (commit mark destination ⟨residual, selection.answers, world⟩)

noncomputable def run (mark : NativeControlTwoStackCut.Mark) (destination : Destination Caller mark)
    (fuel allowance : Nat) (cursor : NativeControlTwoStackCut.Layout Task)
    (world : Session Caller Address Value World) : Nat × Exit pull :=
  let actual := advance (NativeControlEffectCursor.provider pull)
    (NativeControlBoundedCursor.client Address) (fun _ _ => 1) fuel
    (NativeControlBoundedCursor.packet pull allowance cursor world [])
  (actual.1, finish pull mark destination actual.2)

/-- After a yield at allowance one, publication and the two-stack cut happen
without polling the residual or undoing the world of the successful answer. -/
theorem once_yield_exports_then_cuts (mark : NativeControlTwoStackCut.Mark) (destination : Destination Caller mark)
    (cursor residual : NativeControlTwoStackCut.Layout Task)
    (world nextWorld : Session Caller Address Value World) (answer : Address)
    (yielded : pull cursor world = (nextWorld, .yield answer residual)) :
    run pull mark destination 2 1 cursor world =
      (1, Exit.selected ⟨0, .limit, [answer]⟩
        (commit mark destination ⟨residual, [answer], nextWorld⟩)) := by
  unfold run
  rw [NativeControlBoundedCursor.once_yield_stops pull cursor residual world nextWorld answer yielded]
  rfl

/-- The adapter cannot collect or cut on a scheduler pause, including a pause
that already contains effects and some answer occurrences. -/
theorem paused_retains_actual_packet (mark : NativeControlTwoStackCut.Mark) (destination : Destination Caller mark)
    (packet : Packet (NativeControlEffectCursor.provider pull)
      (NativeControlBoundedCursor.client Address) ()) :
    finish pull mark destination (.paused packet) = Exit.paused packet := rfl

/-- Splitting a scheduler budget and resuming the same packet has precisely
the same publication/cancellation outcome as the uninterrupted inspection. -/
theorem chunk_exact (mark : NativeControlTwoStackCut.Mark) (destination : Destination Caller mark)
    (first second allowance : Nat) (cursor : NativeControlTwoStackCut.Layout Task)
    (world : Session Caller Address Value World) :
    run pull mark destination (first + second) allowance cursor world =
      let resumed := resume (NativeControlEffectCursor.provider pull)
        (NativeControlBoundedCursor.client Address) (fun _ _ => 1) second
        (advance (NativeControlEffectCursor.provider pull) (NativeControlBoundedCursor.client Address)
          (fun _ _ => 1) first (NativeControlBoundedCursor.packet pull allowance cursor world []))
      (resumed.1, finish pull mark destination resumed.2) := by
  unfold run
  rw [NativeControlBoundedCursor.chunk_exact]

end Execution

section ProtectedExecution

open NativeControlOwnedCollection (RawPull LawfulRaw pinPull client_buffered)

/-- Local protection at each poll is sufficient for the completed native
client to publish live cells and cancel the buffer. Allocation is derived from
the collecting execution, rather than assumed of its final answer list. -/
theorem completed_collection_exports
    (buffer : Owner Caller)
    (raw : RawPull (NativeControlTwoStackCut.Layout Task) (Owner Caller) Address Value World)
    (lawful : LawfulRaw buffer raw)
    (mark : NativeControlTwoStackCut.Mark) (destination : Destination Caller mark)
    (bufferInternal : inside mark buffer = true)
    (fuel allowance : Nat) (cursor residual : NativeControlTwoStackCut.Layout Task)
    (world nextWorld : Session Caller Address Value World)
    (selection : NativeControlBoundedCursor.Selection Address) (cost : Nat)
    (completed : advance (NativeControlEffectCursor.provider (pinPull buffer raw))
      (NativeControlBoundedCursor.client Address) (fun _ _ => 1) fuel
      (NativeControlBoundedCursor.packet (pinPull buffer raw) allowance cursor world []) =
        (cost, .done ⟨(), selection, (residual, nextWorld)⟩)) :
    let selected := commit mark destination ⟨residual, selection.answers, nextWorld⟩
    run (pinPull buffer raw) mark destination fuel allowance cursor world =
        (cost, Exit.selected selection selected) ∧
      OwnedLifecycle.observe selected.world.heap selection.answers =
        OwnedLifecycle.observe nextWorld.heap selection.answers ∧
      (∀ address, (buffer, address) ∉ selected.world.roots) := by
  have invariant := client_buffered buffer raw lawful fuel allowance cursor world []
    (by intro address member; cases member)
  rw [completed] at invariant
  dsimp only [NativeControlBoundedCursor.readout] at invariant
  dsimp only
  constructor
  · simp only [run, completed, finish]
  · exact ⟨commit_preserves_answers mark destination _
      (fun address member => (invariant.2 address member).2),
      commit_cancels_inner_roots mark destination _ buffer bufferInternal⟩

end ProtectedExecution

namespace Controls

open Mettapedia.Machines.ResourceOwnership.Examples

def roots : Roots (Owner Nat) (Fin 3) :=
  {(.tier 0, 0), (.tier 4, 1), (.host 2, 2), (.host 6, 1)}

/-- A tier-only cancellation cannot accidentally erase host roots, and vice
versa. The mark uses two independently checked physical heights. -/
theorem roots_follow_both_stack_heights :
    cancel roots (deadOwners roots ⟨3, 4⟩) =
      {(.tier 0, 0), (.host 2, 2)} := by decide

def state : State Nat Nat (Fin 3) Nat Nat :=
  ⟨NativeControlTwoStackCut.Controls.layout, [1, 1], ⟨cyclicHeap, roots, 111⟩⟩

def output : Destination Nat NativeControlTwoStackCut.Controls.localMark :=
  Destination.external _ 7

/-- Two answer occurrences keep their multiplicity after shared storage is
rooted once and both stacks are cut. The world is the post-answer world. -/
theorem cut_preserves_duplicate_cells_and_effects :
    OwnedLifecycle.observe (commit NativeControlTwoStackCut.Controls.localMark output state).world.heap [1, 1] =
        [some (cyclicCell 1), some (cyclicCell 1)] ∧
      (commit NativeControlTwoStackCut.Controls.localMark output state).world.world = 111 ∧
      (commit NativeControlTwoStackCut.Controls.localMark output state).choices.pending = [20, 21, 10, 90] := by
  constructor
  · exact commit_preserves_answers NativeControlTwoStackCut.Controls.localMark output state
      (by intro address _; exact Finset.mem_univ address)
  · exact ⟨rfl, NativeControlTwoStackCut.Controls.cuts_host_and_tier⟩

def nestedDestination : Destination Nat NativeControlTwoStackCut.Controls.localMark :=
  Destination.tier _ 1 (by decide)

def nestedState : State Nat Nat (Fin 3) Nat Nat :=
  ⟨NativeControlTwoStackCut.Controls.layout, [1],
    ⟨cyclicHeap, {(.tier 4, 0)}, 111⟩⟩

/-- An inner selection may export to an enclosing continuation. Its answer
survives the inner cut and is reclaimed when that enclosing owner is cancelled;
export need not extend its lifetime to the whole session. -/
theorem nested_export_then_outer_close :
    let inner := commit NativeControlTwoStackCut.Controls.localMark
      nestedDestination nestedState
    inner.world.heap.lookup 1 = some (cyclicCell 1) ∧
      (OwnedLifecycle.closeScope inner.world
        (deadOwners inner.world.roots ⟨0, 1⟩)).heap.lookup 1 = none ∧
      (OwnedLifecycle.closeScope inner.world
        (deadOwners inner.world.roots ⟨0, 1⟩)).world = 111 := by
  dsimp only
  constructor
  · exact commit_preserves_answer_graph _ nestedDestination nestedState 1
      (live_of_root cyclicHeap _ (owner := .tier 1) (by decide) (by decide))
  · constructor
    · apply OwnedLifecycle.closeScope_reclaims_final_owner
      intro pair member _
      have sole : pair = (.tier 1, (1 : Fin 3)) := by
        have rootsEq : (commit NativeControlTwoStackCut.Controls.localMark
            nestedDestination nestedState).world.roots = {(.tier 1, 1)} := by decide
        simpa only [rootsEq, Finset.mem_singleton] using member
      subst pair
      exact (rooted_owner_dead_iff _ _ _ _ member).mpr (by decide)
    · rfl

end Controls

end Mettapedia.GSLT.LanguageDef.NativeControlOwnedCursor
