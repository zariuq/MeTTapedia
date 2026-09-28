import Mettapedia.Machines.Cursor.OwnedLifecycle
import Mettapedia.GSLT.LanguageDef.NativeControlBoundedCursor
import Mettapedia.GSLT.LanguageDef.NativeControlTwoStackCut

/-!
# Bounded cursor observation followed by scoped publication

This joins three existing constructions: the world-preserving cursor client,
the two-stack cut, and the resource heap's publish-before-cancel operation.
Suspended observations cannot commit. A ready bounded observation publishes
its exact occurrences, preserves their reachable graphs and surviving outer
roots, cancels the designated alternatives, and collects unprotected cells.

The result contains no abandoned cursor continuation. Heap reclamation here
has no user-world effect; a foreign finalizer with visible effects must have
an explicit protocol transition and a separate native implementation proof.
Matching the owner set to native delimiter lifetimes, tracing compiled frames,
and exporting concrete addresses are also native correspondence obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor.ObservationOwnership

open Mettapedia.Machines.ResourceOwnership
open Mettapedia.GSLT.LanguageDef
open HostCalls (Pull)


variable {Owner Address Value World Task HState : Type}
  [DecidableEq Owner] [DecidableEq Address]

/-- The existing heap ownership state and the actual two-stack layout live in
the provider world, so every poll can return their current versions. -/
structure Runtime (Owner Address Value World Task : Type)
    [DecidableEq Owner] [DecidableEq Address] where
  memory : OwnedLifecycle.Session Owner Address Value World
  choices : NativeControlTwoStackCut.Layout Task

/-- Publication transfers answer ownership before removing delimiter owners.
The physical alternative stacks are truncated by their own saved marker. -/
noncomputable def commit (state : Runtime Owner Address Value World Task)
    (mark : NativeControlTwoStackCut.Mark) (dead : Finset Owner) (output : Owner) (answers : List Address) :
    Runtime Owner Address Value World Task :=
  ⟨OwnedLifecycle.commit state.memory dead output answers, NativeControlTwoStackCut.truncate mark state.choices⟩

@[simp] theorem commit_world (state : Runtime Owner Address Value World Task)
    (mark : NativeControlTwoStackCut.Mark) (dead : Finset Owner) (output : Owner) (answers : List Address) :
    (commit state mark dead output answers).memory.world = state.memory.world := rfl

theorem commit_preserves_answer_graph (state : Runtime Owner Address Value World Task)
    (mark : NativeControlTwoStackCut.Mark) (dead : Finset Owner) (output : Owner) (answers : List Address)
    (outside : output ∉ dead) {address : Address}
    (live : Live state.memory.heap (OwnedLifecycle.answerRoots output answers) address) :
    (commit state mark dead output answers).memory.heap.lookup address =
      state.memory.heap.lookup address :=
  OwnedLifecycle.commit_preserves_answer_graph state.memory dead output answers outside live

theorem commit_preserves_outer_graph (state : Runtime Owner Address Value World Task)
    (mark : NativeControlTwoStackCut.Mark) (dead : Finset Owner) (output : Owner) (answers : List Address)
    (outside : output ∉ dead) {address : Address}
    (live : Live state.memory.heap (cancel state.memory.roots dead) address) :
    (commit state mark dead output answers).memory.heap.lookup address =
      state.memory.heap.lookup address :=
  OwnedLifecycle.commit_preserves_outer_graph state.memory dead output answers outside live

theorem commit_reclaims_unprotected (state : Runtime Owner Address Value World Task)
    (mark : NativeControlTwoStackCut.Mark) (dead : Finset Owner) (output : Owner) (answers : List Address)
    (outside : output ∉ dead) (address : Address)
    (notOuter : ¬ Live state.memory.heap (cancel state.memory.roots dead) address)
    (notAnswer : ¬ Live state.memory.heap (OwnedLifecycle.answerRoots output answers) address) :
    (commit state mark dead output answers).memory.heap.lookup address = none :=
  OwnedLifecycle.commit_reclaims_unprotected state.memory dead output answers
    outside address notOuter notAnswer

/-- Cancellation retains precisely the outer two-stack alternative suffix.
The interval assumptions are the previously proved native layout invariant. -/
theorem commit_choice_partition
    (memory : OwnedLifecycle.Session Owner Address Value World)
    (tier : List (Option Task)) (floor base : Nat)
    (inside outside : List (NativeControlTwoStackCut.HostFrame Task)) (ownership : NativeControlTwoStackCut.Ownership)
    (floorFits : floor ≤ tier.length) (baseLe : base ≤ floor)
    (inner : NativeControlTwoStackCut.Above floor tier.length inside) (outer : NativeControlTwoStackCut.Above 0 base outside)
    (dead : Finset Owner) (output : Owner) (answers : List Address) :
    let hostPrefix := (NativeControlTwoStackCut.HostFrame.segment ownership base :: outside).reverse
    let state : Runtime Owner Address Value World Task :=
      ⟨memory, ⟨tier, hostPrefix ++ inside.reverse⟩⟩
    state.choices.pending = NativeControlTwoStackCut.pendingAbove floor tier tier.length inside ++
      (commit state ⟨floor, hostPrefix.length⟩ dead output answers).choices.pending :=
  NativeControlTwoStackCut.pending_partition tier floor base inside outside ownership floorFits baseLe inner outer

/-- A published result exports occurrences but not the discarded continuation. -/
structure Published (Owner Address Value World Task : Type)
    [DecidableEq Owner] [DecidableEq Address] where
  answers : List Address
  remaining : Nat
  reason : NativeControlBoundedCursor.Finish
  state : Runtime Owner Address Value World Task

/-- A pending observation retains its exact cursor, world, occurrences, and
remaining demand. Publication has no abandoned continuation. -/
inductive Observation (HState Owner Address Value World Task : Type)
    [DecidableEq Owner] [DecidableEq Address] where
  | paused (snapshot : NativeControlBoundedCursor.Snapshot HState
      (Runtime Owner Address Value World Task) Address)
  | done (result : Published Owner Address Value World Task)

/-- Only a ready limit/exhaustion observation can cancel its cursor. A
scheduler pause is retained by the caller instead of being misread as empty. -/
noncomputable def publish (mark : NativeControlTwoStackCut.Mark) (dead : Finset Owner) (output : Owner)
    (snapshot : NativeControlBoundedCursor.Snapshot HState (Runtime Owner Address Value World Task) Address) :
    Observation HState Owner Address Value World Task :=
  match snapshot.stop with
  | .budget => .paused snapshot
  | .limit => .done ⟨snapshot.answers, snapshot.remaining, .limit,
      commit snapshot.world mark dead output snapshot.answers⟩
  | .exhausted => .done ⟨snapshot.answers, snapshot.remaining, .exhausted,
      commit snapshot.world mark dead output snapshot.answers⟩

theorem publish_paused_iff (mark : NativeControlTwoStackCut.Mark)
    (dead : Finset Owner) (output : Owner)
    (snapshot : NativeControlBoundedCursor.Snapshot HState
      (Runtime Owner Address Value World Task) Address) :
    (∃ retained, publish mark dead output snapshot = .paused retained) ↔
      snapshot.stop = .budget := by
  cases stop : snapshot.stop <;> simp [publish, stop]

/-- The paused readout contains enough information to reconstruct the exact
protocol packet. Its occurrence prefix is stored forward in a snapshot and
backward in the client, so restoration reverses it once. -/
def restoreSnapshot
    (pull : HState → Runtime Owner Address Value World Task →
      Runtime Owner Address Value World Task × Pull HState Address)
    (snapshot : NativeControlBoundedCursor.Snapshot HState
      (Runtime Owner Address Value World Task) Address) :
    Packet (NativeControlEffectCursor.provider pull)
      (NativeControlBoundedCursor.client Address) () :=
  NativeControlBoundedCursor.packet pull snapshot.remaining snapshot.cursor
    snapshot.world snapshot.answers.reverse

theorem suspended_packet_roundtrip
    (pull : HState → Runtime Owner Address Value World Task →
      Runtime Owner Address Value World Task × Pull HState Address)
    (packet : Packet (NativeControlEffectCursor.provider pull)
      (NativeControlBoundedCursor.client Address) ())
    (paused : (NativeControlBoundedCursor.readout pull (.paused packet)).stop = .budget) :
    restoreSnapshot pull (NativeControlBoundedCursor.readout pull (.paused packet)) =
      packet := by
  rcases packet with ⟨⟨⟩, control, cursor, world⟩
  cases control with
  | pulling remaining reversed =>
      cases remaining with
      | zero => simp [NativeControlBoundedCursor.readout] at paused
      | succ remaining =>
          simp [restoreSnapshot, NativeControlBoundedCursor.readout,
            NativeControlBoundedCursor.packet]
  | exhausted remaining answers =>
      simp [NativeControlBoundedCursor.readout] at paused

/-- Run the existing bounded cursor client, read its retained state without
another poll, and publish only if ready. -/
noncomputable def observeAndCommit
    (pull : HState → Runtime Owner Address Value World Task →
      Runtime Owner Address Value World Task × Pull HState Address)
    (fuel allowance : Nat) (cursor : HState)
    (world : Runtime Owner Address Value World Task)
    (mark : NativeControlTwoStackCut.Mark) (dead : Finset Owner) (output : Owner) :
    Nat × Observation HState Owner Address Value World Task :=
  let execution := advance (NativeControlEffectCursor.provider pull)
    (NativeControlBoundedCursor.client Address) (fun _ _ => 1) fuel
    (NativeControlBoundedCursor.packet pull allowance cursor world [])
  (execution.1, publish mark dead output (NativeControlBoundedCursor.readout pull execution.2))

/-- The publication operation observes the independent collector's exact
receipt and prefix at the same budget, including pending suspensions. -/
theorem observeAndCommit_refines
    (pull : HState → Runtime Owner Address Value World Task →
      Runtime Owner Address Value World Task × Pull HState Address)
    (fuel allowance : Nat) (cursor : HState)
    (world : Runtime Owner Address Value World Task)
    (mark : NativeControlTwoStackCut.Mark) (dead : Finset Owner) (output : Owner) :
    observeAndCommit pull fuel allowance cursor world mark dead output =
      let expected := NativeControlBoundedCursor.collectBounded pull fuel allowance cursor world
      (expected.1, publish mark dead output expected.2) := by
  have agreement := NativeControlBoundedCursor.readout_exact pull fuel allowance cursor world []
  have mapped := congrArg (fun result : Nat × NativeControlBoundedCursor.Snapshot HState
      (Runtime Owner Address Value World Task) Address =>
        (result.1, publish mark dead output result.2)) agreement
  simpa only [observeAndCommit, List.reverse_nil, NativeControlBoundedCursor.Snapshot.prefix,
    List.nil_append] using mapped

/-- An immediate first success performs one poll, publishes that one answer,
and abandons the residual without evaluating it. The world is the post-yield
world; neither effects nor selected answer roots are rolled back. -/
theorem once_yield_commit
    (pull : HState → Runtime Owner Address Value World Task →
      Runtime Owner Address Value World Task × Pull HState Address)
    (cursor residual : HState)
    (world nextWorld : Runtime Owner Address Value World Task)
    (answer : Address) (mark : NativeControlTwoStackCut.Mark) (dead : Finset Owner) (output : Owner)
    (yielded : pull cursor world = (nextWorld, .yield answer residual)) :
    observeAndCommit pull 1 1 cursor world mark dead output =
      (1, .done ⟨[answer], 0, .limit, commit nextWorld mark dead output [answer]⟩) := by
  rw [observeAndCommit_refines]
  simp only [NativeControlBoundedCursor.collectBounded, yielded, NativeControlBoundedCursor.Snapshot.prefix,
    List.singleton_append, publish]

/-- The escaping answer's complete graph survives the same operation that
cuts the pending alternatives. In particular, the answer need not have had
an outer owner before this publication. -/
theorem once_yield_answer_survives
    (pull : HState → Runtime Owner Address Value World Task →
      Runtime Owner Address Value World Task × Pull HState Address)
    (cursor residual : HState)
    (world nextWorld : Runtime Owner Address Value World Task)
    (answer : Address) (mark : NativeControlTwoStackCut.Mark) (dead : Finset Owner) (output : Owner)
    (yielded : pull cursor world = (nextWorld, .yield answer residual))
    (outside : output ∉ dead) (allocated : answer ∈ nextWorld.memory.heap.allocated) :
    ∃ result,
      observeAndCommit pull 1 1 cursor world mark dead output = (1, .done result) ∧
      result.answers = [answer] ∧
      result.state.memory.world = nextWorld.memory.world ∧
      (∀ address,
        Live nextWorld.memory.heap (OwnedLifecycle.answerRoots output [answer]) address →
        result.state.memory.heap.lookup address = nextWorld.memory.heap.lookup address) ∧
      result.state.memory.heap.lookup answer = nextWorld.memory.heap.lookup answer := by
  refine ⟨⟨[answer], 0, .limit, commit nextWorld mark dead output [answer]⟩,
    once_yield_commit pull cursor residual world nextWorld answer mark dead output yielded,
    rfl, rfl, ?_, ?_⟩
  · intro address live
    exact commit_preserves_answer_graph nextWorld mark dead output [answer] outside live
  · apply commit_preserves_answer_graph nextWorld mark dead output [answer] outside
    exact live_of_root nextWorld.memory.heap _ (owner := output) (by simp) allocated

/-- Reaching no answer allowance never polls, including at zero scheduler
budget. Publishing then only applies the explicitly requested local cut. -/
theorem zero_allowance_commits_without_poll
    (pull : HState → Runtime Owner Address Value World Task →
      Runtime Owner Address Value World Task × Pull HState Address)
    (fuel : Nat) (cursor : HState) (world : Runtime Owner Address Value World Task)
    (mark : NativeControlTwoStackCut.Mark) (dead : Finset Owner) (output : Owner) :
    observeAndCommit pull fuel 0 cursor world mark dead output =
      (0, .done ⟨[], 0, .limit, commit world mark dead output []⟩) := by
  rw [observeAndCommit_refines]
  simp only [NativeControlBoundedCursor.collectBounded, publish]

/-- Suspension spends one poll but cannot trigger publication or local cut.
Its residual remains in the bounded client's packet for later resumption. -/
theorem suspend_retains_state
    (pull : HState → Runtime Owner Address Value World Task →
      Runtime Owner Address Value World Task × Pull HState Address)
    (cursor residual : HState)
    (world nextWorld : Runtime Owner Address Value World Task)
    (mark : NativeControlTwoStackCut.Mark) (dead : Finset Owner) (output : Owner)
    (suspended : pull cursor world = (nextWorld, .suspend residual)) :
    observeAndCommit pull 1 1 cursor world mark dead output =
      (1, .paused ⟨residual, nextWorld, [], 1, .budget⟩) := by
  rw [observeAndCommit_refines]
  simp only [NativeControlBoundedCursor.collectBounded, suspended, publish]

/-- A completed observation is also valid when obtaining its selected answer
required any finite number of intervening suspensions. Publication preserves
the entire exported graph in the post-observation heap. -/
theorem completed_observation_survives
    (pull : HState → Runtime Owner Address Value World Task →
      Runtime Owner Address Value World Task × Pull HState Address)
    (fuel allowance : Nat) (cursor finalCursor : HState)
    (world finalWorld : Runtime Owner Address Value World Task)
    (spent remaining : Nat) (answers : List Address)
    (reason : NativeControlBoundedCursor.Finish)
    (mark : NativeControlTwoStackCut.Mark) (dead : Finset Owner) (output : Owner)
    (outside : output ∉ dead)
    (completed : NativeControlBoundedCursor.collectBounded pull fuel allowance cursor world =
      (spent, ⟨finalCursor, finalWorld, answers, remaining, reason.stop⟩)) :
    ∃ result,
      observeAndCommit pull fuel allowance cursor world mark dead output =
        (spent, .done result) ∧
      result.answers = answers ∧
      result.state.memory.world = finalWorld.memory.world ∧
      (∀ address,
        Live finalWorld.memory.heap (OwnedLifecycle.answerRoots output answers) address →
        result.state.memory.heap.lookup address = finalWorld.memory.heap.lookup address) ∧
      (∀ address, Live finalWorld.memory.heap (cancel finalWorld.memory.roots dead) address →
        result.state.memory.heap.lookup address = finalWorld.memory.heap.lookup address) := by
  refine ⟨⟨answers, remaining, reason, commit finalWorld mark dead output answers⟩,
    ?_, rfl, rfl, ?_, ?_⟩
  · rw [observeAndCommit_refines, completed]
    cases reason <;> rfl
  · intro address live
    exact commit_preserves_answer_graph finalWorld mark dead output answers outside live
  · intro address live
    exact commit_preserves_outer_graph finalWorld mark dead output answers outside live

/-- An answer count bounds retained root entries, not transitive bytes. A
byte bound additionally needs a reachable graph bound and a cell-size bound. -/
theorem bounded_commit_byte_bound
    (pull : HState → Runtime Owner Address Value World Task →
      Runtime Owner Address Value World Task × Pull HState Address)
    (fuel allowance : Nat) (cursor : HState)
    (world : Runtime Owner Address Value World Task)
    (mark : NativeControlTwoStackCut.Mark) (dead : Finset Owner) (output : Owner)
    (outside : output ∉ dead) (perRoot bytes : Nat)
    (bounded : let observed := (NativeControlBoundedCursor.collectBounded
        pull fuel allowance cursor world).2
      ∀ pair ∈ OwnedLifecycle.commitRoots observed.world.memory.roots dead
        output observed.answers,
        (footprint observed.world.memory.heap {pair}).card ≤ perRoot)
    (weights : let observed := (NativeControlBoundedCursor.collectBounded
        pull fuel allowance cursor world).2
      ∀ address ∈ footprint observed.world.memory.heap
        (OwnedLifecycle.commitRoots observed.world.memory.roots dead output observed.answers),
        cellBytes observed.world.memory.heap address ≤ bytes) :
    let observed := (NativeControlBoundedCursor.collectBounded
      pull fuel allowance cursor world).2
    allocatedBytes (commit observed.world mark dead output observed.answers).memory.heap ≤
      (observed.world.memory.roots.card + allowance) * perRoot * bytes := by
  dsimp only at bounded weights ⊢
  have accounting := NativeControlBoundedCursor.answer_accounting
    pull fuel allowance cursor world
  have count : (NativeControlBoundedCursor.collectBounded
      pull fuel allowance cursor world).2.answers.length ≤ allowance := by
    dsimp only at accounting
    omega
  apply (OwnedLifecycle.commit_byte_bound _ dead output _ outside perRoot bytes
    bounded weights).trans
  exact Nat.mul_le_mul_right bytes
    (Nat.mul_le_mul_right perRoot (Nat.add_le_add_left count _))

/-- Reclassifying a pause as an empty completed collection would discard its
live continuation. The published and paused constructors cannot coincide. -/
theorem suspension_is_not_empty_completion
    (pull : HState → Runtime Owner Address Value World Task →
      Runtime Owner Address Value World Task × Pull HState Address)
    (cursor residual : HState)
    (world nextWorld : Runtime Owner Address Value World Task)
    (mark : NativeControlTwoStackCut.Mark) (dead : Finset Owner) (output : Owner)
    (suspended : pull cursor world = (nextWorld, .suspend residual)) :
    ¬ ∃ result, observeAndCommit pull 1 1 cursor world mark dead output =
      (1, .done result) := by
  rw [suspend_retains_state pull cursor residual world nextWorld mark dead output suspended]
  simp

#print axioms observeAndCommit_refines
#print axioms once_yield_answer_survives
#print axioms commit_choice_partition
#print axioms commit_reclaims_unprotected
#print axioms suspend_retains_state
#print axioms suspended_packet_roundtrip
#print axioms completed_observation_survives
#print axioms bounded_commit_byte_bound
#print axioms suspension_is_not_empty_completion

end Mettapedia.Machines.Cursor.ObservationOwnership
