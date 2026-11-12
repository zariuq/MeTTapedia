import Mettapedia.Machines.Cursor.ReaderOrderedMergeCursor

/-!
# An already earlier retired head needs no live visibility scan

The native cursor can inspect its cached raw heads before normalizing the
live stream. If the retired head is earlier than every raw live candidate,
it is the next entry-view answer irrespective of their visibility. This
avoids needless first-demand work when later additions sit beyond that head.
The proof requires the raw live index's order, not merely its filtered order.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor.ReaderOrderedMergeShortcut

open ReaderOrderedMerge
open ReaderOrderedMergeCursor (filtered)
open Mettapedia.TypeTheory

variable {Key : Type} [LinearOrder Key]

theorem merge_after_all (eligible : Token Key → Bool) (live : List (Token Key))
    (first : Token Key) (gone : List (Token Key))
    (earlier : ∀ value ∈ live, first < value) :
    meaning (filtered eligible ⟨live, first :: gone⟩) =
      first :: meaning (filtered eligible ⟨live, gone⟩) := by
  induction live with
  | nil => simp [meaning, filtered]
  | cons head tail ih =>
      have before : ¬ head ≤ first := not_le.mpr (earlier head (by simp))
      by_cases accepted : eligible head = true
      · simp [meaning, filtered, accepted, before]
      · simpa [meaning, filtered, accepted] using
          ih (fun value member => earlier value (by simp [member]))

/-- This operation does not inspect eligibility or advance the live stream. -/
def goneShortcut (state : State Key) : Option (Token Key × State Key) :=
  match state.gone, state.live with
  | [], _ => none
  | first :: rest, [] => some (first, ⟨[], rest⟩)
  | first :: rest, liveHead :: _ =>
      if first < liveHead then some (first, ⟨state.live, rest⟩) else none

theorem shortcut_correct (eligible : Token Key → Bool) (state : State Key)
    (ordered : state.live.Pairwise (· ≤ ·)) (first : Token Key) (next : State Key)
    (admitted : goneShortcut state = some (first, next)) :
    meaning (filtered eligible state) = first :: meaning (filtered eligible next) := by
  rcases state with ⟨live, gone⟩
  cases gone with
  | nil => simp [goneShortcut] at admitted
  | cons head tail =>
      cases live with
      | nil =>
          simp only [goneShortcut, Option.some.injEq, Prod.mk.injEq] at admitted
          rcases admitted with ⟨rfl, rfl⟩
          simp [meaning, filtered]
      | cons liveHead rest =>
          by_cases before : head < liveHead
          · simp only [goneShortcut, before, ↓reduceIte, Option.some.injEq,
              Prod.mk.injEq] at admitted
            rcases admitted with ⟨rfl, rfl⟩
            apply merge_after_all
            intro value member
            rcases List.mem_cons.mp member with same | later
            · exact same ▸ before
            · exact before.trans_le ((List.pairwise_cons.mp ordered).1 value later)
          · simp [goneShortcut, before] at admitted

theorem shortcut_keeps_live (state : State Key) (first : Token Key) (next : State Key)
    (admitted : goneShortcut state = some (first, next)) : next.live = state.live := by
  rcases state with ⟨live, gone⟩
  cases gone with
  | nil => simp [goneShortcut] at admitted
  | cons head tail =>
      cases live with
      | nil => simp [goneShortcut] at admitted; exact admitted.2 ▸ rfl
      | cons liveHead rest =>
          by_cases before : head < liveHead
          · simp [goneShortcut, before] at admitted
            exact admitted.2 ▸ rfl
          · simp [goneShortcut, before] at admitted

omit [LinearOrder Key] in
theorem seek_sublist (eligible : Token Key → Bool) (rows : List (Token Key)) :
    List.Sublist (ReaderOrderedMergeCursor.seek eligible rows).2 rows := by
  induction rows with
  | nil => rfl
  | cons first later ih =>
      by_cases accepted : eligible first = true
      · simp [ReaderOrderedMergeCursor.seek, accepted]
      · simpa [ReaderOrderedMergeCursor.seek, accepted] using ih.cons first

theorem pull_keeps_live_order (state : State Key) (ordered : state.live.Pairwise (· ≤ ·)) :
    (pull state).2.live.Pairwise (· ≤ ·) := by
  rcases state with ⟨live, gone⟩
  cases live with
  | nil => cases gone <;> simp [pull]
  | cons first later =>
      cases gone with
      | nil => simpa [pull] using (List.pairwise_cons.mp ordered).2
      | cons second tail =>
          by_cases before : first ≤ second
          · simpa [pull, before] using (List.pairwise_cons.mp ordered).2
          · simpa [pull, before] using ordered

/-- The ordering witness is maintained by the cursor; it is not a request
that a runtime rescan and validate the index on every pull. -/
structure OrderedState (Key : Type) [LinearOrder Key] where
  data : State Key
  ordered : data.live.Pairwise (· ≤ ·)

def nextData (eligible : Token Key → Bool) (state : State Key) : Option (Token Key) × State Key :=
  match goneShortcut state with
  | some (first, later) => (some first, later)
  | none => pull (ReaderOrderedMergeCursor.normalize eligible state)

theorem nextData_refused (eligible : Token Key → Bool) (state : State Key)
    (refused : goneShortcut state = none) :
    nextData eligible state = pull (ReaderOrderedMergeCursor.normalize eligible state) := by
  rw [nextData, refused]

theorem nextData_keeps_order (eligible : Token Key → Bool) (state : State Key)
    (ordered : state.live.Pairwise (· ≤ ·)) :
    (nextData eligible state).2.live.Pairwise (· ≤ ·) := by
  cases admitted : goneShortcut state with
  | none =>
      simpa only [nextData, admitted] using
        pull_keeps_live_order (ReaderOrderedMergeCursor.normalize eligible state)
          (ordered.sublist (seek_sublist eligible state.live))
  | some chosen =>
      rcases chosen with ⟨first, later⟩
      simp only [nextData, admitted]
      rw [shortcut_keeps_live state first later admitted]
      exact ordered

def next (eligible : Token Key → Bool) (state : OrderedState Key) :
    Option (Token Key) × OrderedState Key :=
  let response := nextData eligible state.data
  (response.1, ⟨response.2, nextData_keeps_order eligible state.data state.ordered⟩)

def provider (eligible : Token Key → Bool) : Provider (Sequence.protocol (Token Key)) where
  State _ _ := OrderedState Key
  step state _ := ⟨(next eligible state).1, (next eligible state).2⟩

def refinement (eligible : Token Key → Bool) :
    Hom (provider eligible) (Sequence.tails (Token Key)) where
  map state := meaning (filtered eligible state.data)
  step state request := by
    cases request
    cases admitted : goneShortcut state.data with
    | none =>
        have compared := (ReaderOrderedMergeCursor.sequenceRefinement eligible).step
          (base := ()) (index := ()) state.data ()
        dsimp only [provider, next]
        rw [nextData_refused eligible state.data admitted]
        simpa only [ReaderOrderedMergeCursor.sequenceRefinement,
          Hom.comp, ReaderOrderedMergeCursor.refinement, ReaderOrderedMerge.refinement,
          ReaderOrderedMergeCursor.provider] using compared
    | some chosen =>
        rcases chosen with ⟨first, later⟩
        have before := shortcut_correct eligible state.data state.ordered first later admitted
        simp only [provider, next, nextData, admitted, before, Sequence.tails]

theorem stamped_client_observation {Value : Type} {Return : Unit → Unit → Type}
    (priority : Nat → Key) (store : StampedSnapshots.Store Value)
    (reader : StampedSnapshots.Reader) (eligible : Token Key → Bool) (state : OrderedState Key)
    (valid : Components (filtered eligible state.data)
      (tokens priority (survivingIDs store reader)) (tokens priority (retiredIDs store reader)))
    (client : Client (P := Sequence.protocol (Token Key)) (Return := Return))
    (sourceCost : Charge (provider eligible)) (targetCost : Charge (Sequence.tails (Token Key)))
    (fuel : Nat) (control : client.V () ()) :
    (refinement eligible).outcome client
        (advance (provider eligible) client sourceCost fuel ⟨(), control, state⟩).2 =
      (advance (Sequence.tails (Token Key)) client targetCost fuel
        ⟨(), control, (tokens priority (entryIDs store reader)).sort (· ≤ ·)⟩).2 := by
  have compared := Hom.advance client (refinement eligible) sourceCost targetCost fuel
    ⟨(), control, state⟩
  simpa only [Hom.packet, refinement,
    stamped_entry_source priority store reader (filtered eligible state.data) valid] using compared

/-- The price is for the actual visibility callback on this candidate. It
may depend on the row; no constant matching or key-decoding cost is assumed. -/
def seekCost (eligible : Token Key → Bool) (price : Token Key → Nat) : List (Token Key) → Nat
  | [] => 0
  | first :: later => price first + if eligible first then 0 else seekCost eligible price later

def visibilityCost (eligible : Token Key → Bool) (price : Token Key → Nat)
    (state : State Key) : Nat :=
  match goneShortcut state with
  | some _ => 0
  | none => seekCost eligible price state.live

def shortcutComparisonCost (price : Token Key → Token Key → Nat) (state : State Key) : Nat :=
  match state.gone, state.live with
  | first :: _, second :: _ => price first second
  | _, _ => 0

def mergeComparisonCost (price : Token Key → Token Key → Nat) (state : State Key) : Nat :=
  match state.live, state.gone with
  | first :: _, second :: _ => price first second
  | _, _ => 0

/-- Failed shortcut admission still pays for its cached-head comparison.
The fallback then pays for its actual normalized merge comparison as well. -/
def comparisonCost (eligible : Token Key → Bool) (price : Token Key → Token Key → Nat)
    (state : State Key) : Nat :=
  shortcutComparisonCost price state +
    match goneShortcut state with
    | some _ => 0
    | none => mergeComparisonCost price (ReaderOrderedMergeCursor.normalize eligible state)

theorem admitted_visibility_cost_zero (eligible : Token Key → Bool) (price : Token Key → Nat)
    (state : State Key) (first : Token Key) (later : State Key)
    (admitted : goneShortcut state = some (first, later)) :
    visibilityCost eligible price state = 0 := by simp [visibilityCost, admitted]

theorem admitted_comparison_cost (eligible : Token Key → Bool)
    (price : Token Key → Token Key → Nat) (state : State Key) (first : Token Key) (later : State Key)
    (admitted : goneShortcut state = some (first, later)) :
    comparisonCost eligible price state = shortcutComparisonCost price state := by
  simp [comparisonCost, admitted]

omit [LinearOrder Key] in
theorem rejected_visibility_work (rows : List (Token Key)) :
    seekCost (fun _ => false) (fun _ => 1) rows = rows.length := by
  induction rows with
  | nil => rfl
  | cons first later ih => simp [seekCost, ih, Nat.add_comm]

/-- For an arbitrary number of rejected live candidates, normalization-first
visits all of them before returning an already earlier retired head. The
shortcut returns that same head with zero visibility callbacks. -/
theorem first_demand_gap (state : OrderedState Key) (first : Token Key) (later : State Key)
    (admitted : goneShortcut state.data = some (first, later)) :
    (next (fun _ => false) state).1 = some first ∧
      seekCost (fun _ => false) (fun _ => 1) state.data.live = state.data.live.length ∧
      visibilityCost (fun _ => false) (fun _ => 1) state.data = 0 := by
  simp [next, nextData, admitted, rejected_visibility_work, visibilityCost]

def tok (priority id : Nat) : Token Nat := toLex (priority, id)

example : (goneShortcut (⟨[tok 100 9, tok 101 10], [tok 1 0]⟩ : State Nat)).map
    (fun reply => reply.1) = some (tok 1 0) := by decide

example : (ReaderOrderedMergeCursor.seek (fun _ : Token Nat => false)
    [tok 100 9, tok 101 10]).1 = 2 := by decide

/-- The shortcut must decline when a raw live head stands before it. -/
example : goneShortcut (⟨[tok 0 9], [tok 1 0]⟩ : State Nat) = none := by
  simp [goneShortcut, tok, Prod.Lex.lt_iff]

def sampleState : OrderedState Nat :=
  ⟨⟨[tok 100 1, tok 101 2], [tok 1 0]⟩, by decide⟩

def sampleEligible (value : Token Nat) : Bool := decide ((ofLex value).2 < 1)

example : (next sampleEligible sampleState).1 = some (tok 1 0) ∧
    visibilityCost sampleEligible (fun _ => 1) sampleState.data = 0 ∧
    seekCost sampleEligible (fun _ => 1) sampleState.data.live = 2 := by decide

example : comparisonCost sampleEligible
    (fun first second => 1 + (ofLex first).1 + (ofLex second).1) sampleState.data = 102 := by decide

def sampleOriginal : StampedSnapshots.Store Nat := StampedSnapshots.add StampedSnapshots.empty 1
def sampleReader : StampedSnapshots.Reader := StampedSnapshots.start sampleOriginal
def sampleModified : StampedSnapshots.Store Nat :=
  StampedSnapshots.add (StampedSnapshots.add (StampedSnapshots.remove sampleOriginal 0) 100) 101
def samplePriority (id : Nat) : Nat := if id = 0 then 1 else if id = 1 then 100 else 101

/-- The first-demand counterexample is an actual old entry view: both live
candidates were born after it, while its sole old row is now retired. -/
example : Components (filtered sampleEligible sampleState.data)
    (tokens samplePriority (survivingIDs sampleModified sampleReader))
    (tokens samplePriority (retiredIDs sampleModified sampleReader)) := by
  unfold Components
  decide

/-- Filtered order alone is insufficient for admission: an invisible raw
head can hide an earlier eligible tail when the raw index itself is unsorted. -/
example :
    let state : State Nat := ⟨[tok 100 9, tok 0 10], [tok 1 0]⟩
    let accept := fun value : Token Nat => decide ((ofLex value).2 = 10)
    (goneShortcut state).map Prod.fst = some (tok 1 0) ∧
      (meaning (filtered accept state)).head? = some (tok 0 10) := by
  constructor
  · decide
  · simp [meaning, filtered, tok, Prod.Lex.le_iff]

end Mettapedia.Machines.Cursor.ReaderOrderedMergeShortcut
