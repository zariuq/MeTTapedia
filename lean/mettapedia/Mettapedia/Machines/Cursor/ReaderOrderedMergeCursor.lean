import Mettapedia.Machines.Cursor.ReaderOrderedMerge

/-!
# Retained skipping before a two-head ordered merge

The current-live index may also offer rows born after a reader opened. The
cursor tests and drops rejected heads, then retains the actual suffix reached.
The death stream is already qualified by the entry stamps. Filtering the live
stream is the independent semantic readback, never an opening-time allocation.

Each rejected candidate is consumed once per retained traversal. Two-head
comparisons and a possible accepted-head test require separate constant work
per pull; heap insertion and native successor searches remain unpriced here.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor.ReaderOrderedMergeCursor

open Mettapedia.TypeTheory
open ReaderOrderedMerge

variable {Key : Type}

def seek (eligible : Token Key → Bool) : List (Token Key) → Nat × List (Token Key)
  | [] => (0, [])
  | first :: later =>
      if eligible first then (0, first :: later)
      else
        let next := seek eligible later
        (1 + next.1, next.2)

theorem seek_filter (eligible : Token Key → Bool) (rows : List (Token Key)) :
    (seek eligible rows).2.filter eligible = rows.filter eligible := by
  induction rows with
  | nil => rfl
  | cons first later ih =>
      by_cases accepted : eligible first = true <;> simp [seek, accepted, ih]

theorem seek_head (eligible : Token Key → Bool) (rows : List (Token Key))
    (first : Token Key) (later : List (Token Key))
    (found : (seek eligible rows).2 = first :: later) : eligible first = true := by
  induction rows with
  | nil => simp [seek] at found
  | cons head tail ih =>
      by_cases accepted : eligible head = true
      · simp [seek, accepted] at found
        exact found.1 ▸ accepted
      · apply ih
        simpa [seek, accepted] using found

theorem seek_account (eligible : Token Key → Bool) (rows : List (Token Key)) :
    (seek eligible rows).1 + (seek eligible rows).2.length = rows.length := by
  induction rows with
  | nil => rfl
  | cons first later ih =>
      by_cases accepted : eligible first = true
      · simp [seek, accepted]
      · simp only [seek, accepted, Bool.false_eq_true, ↓reduceIte, List.length_cons]
        omega

theorem seek_idempotent (eligible : Token Key → Bool) (rows : List (Token Key)) :
    seek eligible (seek eligible rows).2 = (0, (seek eligible rows).2) := by
  cases found : (seek eligible rows).2 with
  | nil => rfl
  | cons first later =>
      have accepted := seek_head eligible rows first later found
      simp [seek, accepted]

def filtered (eligible : Token Key → Bool) (state : State Key) : State Key :=
  ⟨state.live.filter eligible, state.gone⟩

def normalize (eligible : Token Key → Bool) (state : State Key) : State Key :=
  ⟨(seek eligible state.live).2, state.gone⟩

theorem normalize_filtered (eligible : Token Key → Bool) (state : State Key) :
    filtered eligible (normalize eligible state) = filtered eligible state := by
  simp [filtered, normalize, seek_filter]

variable [LinearOrder Key]

theorem pull_filtered (eligible : Token Key → Bool) (state : State Key)
    (ready : ∀ first later, state.live = first :: later → eligible first = true) :
    ((pull state).1, filtered eligible (pull state).2) = pull (filtered eligible state) := by
  rcases state with ⟨live, gone⟩
  cases live with
  | nil => cases gone <;> simp [pull, filtered]
  | cons first later =>
      have accepted := ready first later rfl
      cases gone with
      | nil => simp [pull, filtered, accepted]
      | cons second tail =>
          by_cases before : first ≤ second <;> simp [pull, filtered, accepted, before]

def provider (eligible : Token Key → Bool) : Provider (Sequence.protocol (Token Key)) where
  State _ _ := State Key
  step state _ :=
    let response := pull (normalize eligible state)
    ⟨response.1, response.2⟩

def refinement (eligible : Token Key → Bool) :
    Hom (provider eligible) (ReaderOrderedMerge.provider (Key := Key)) where
  map := filtered eligible
  step state _ := by
    have comparison := pull_filtered eligible (normalize eligible state)
      (fun first later same => seek_head eligible state.live first later same)
    rw [normalize_filtered eligible state] at comparison
    change (⟨(pull (normalize eligible state)).1,
        filtered eligible (pull (normalize eligible state)).2⟩ :
        Sigma fun _ : Option (Token Key) => State Key) = _
    have replies := congrArg (fun response : Option (Token Key) × State Key => response.1) comparison
    have residuals := congrArg (fun response : Option (Token Key) × State Key => response.2) comparison
    exact Sigma.ext replies (heq_of_eq residuals)

def volume (state : State Key) : Nat := state.live.length + state.gone.length

def delivered (reply : Option (Token Key)) : Nat := if reply.isSome then 1 else 0

theorem pull_account (state : State Key) :
    volume (pull state).2 + delivered (pull state).1 = volume state := by
  rcases state with ⟨live, gone⟩
  cases live with
  | nil => cases gone <;> simp [pull, volume, delivered]
  | cons first later =>
      cases gone with
      | nil => simp [pull, volume, delivered]
      | cons second tail =>
          by_cases before : first ≤ second <;>
            simp [pull, volume, delivered, before] <;> omega

/-- The account includes rejected row advances as well as returned rows.
Old skipped prefixes do not reappear in the cursor's saved live remainder. -/
theorem step_account (eligible : Token Key → Bool) (state : State Key) :
    (seek eligible state.live).1 +
        volume ((provider eligible).step (base := ()) (index := ()) state ()).2 +
        delivered ((provider eligible).step (base := ()) (index := ()) state ()).1 = volume state := by
  have skipped := seek_account eligible state.live
  have chosen := pull_account (normalize eligible state)
  dsimp only [provider, normalize, volume] at chosen ⊢
  omega

omit [LinearOrder Key] in
theorem normalize_ignores_no_more_rows (eligible : Token Key → Bool) (state : State Key) :
    (seek eligible (normalize eligible state).live).1 = 0 := by
  exact congrArg Prod.fst (seek_idempotent eligible state.live)

/-- Rejected heads each require one eligibility test; a retained accepted
head needs at most one more test and the two-head choice at most one comparison.
This does not price native successor lookup, decoder work or heap operations. -/
def headWork (eligible : Token Key → Bool) : Charge (provider eligible) :=
  fun state _ => (seek eligible state.live).1 + 2

def credit (eligible : Token Key → Bool) : Potential (provider eligible) := volume

def sequenceRefinement (eligible : Token Key → Bool) :
    Hom (provider eligible) (Sequence.tails (Token Key)) :=
  (refinement eligible).comp ReaderOrderedMerge.refinement

theorem head_work_amortized (eligible : Token Key → Bool) :
    Amortized (sequenceRefinement eligible) (headWork eligible)
      (fun _ _ => 2) (credit eligible) := by
  intro base index state request
  cases base; cases index; cases request
  have account := step_account eligible state
  dsimp only [Amortized, headWork, credit, provider, Sequence.protocol] at account ⊢
  omega

/-- The local accounting lifts through the existing cursor machinery to any
reply-dependent prefix, including an early stop or a suspended continuation. -/
theorem head_work_prefix_bound {Return : Unit → Unit → Type}
    (eligible : Token Key → Bool)
    (client : Client (P := Sequence.protocol (Token Key)) (Return := Return))
    (fuel : Nat) (packet : Packet (provider eligible) client ()) :
    (advance (provider eligible) client (headWork eligible) fuel packet).1 +
        outcomePotential client (credit eligible)
          (advance (provider eligible) client (headWork eligible) fuel packet).2 ≤
      (advance (Sequence.tails (Token Key)) client (fun _ _ => 2) fuel
        ((sequenceRefinement eligible).packet client packet)).1 + volume packet.2.2 :=
  advance_amortized client (sequenceRefinement eligible) (headWork eligible)
    (fun _ _ => 2) (credit eligible) (head_work_amortized eligible) fuel packet

/-- The complete retained candidate cursor earns the independently defined
stamped entry sequence once the two native indexes establish their component
invariants. This includes rejected current-live rows and arbitrary client demand. -/
theorem stamped_client_observation {Value : Type} {Return : Unit → Unit → Type}
    (priority : Nat → Key) (store : StampedSnapshots.Store Value)
    (reader : StampedSnapshots.Reader) (eligible : Token Key → Bool) (state : State Key)
    (valid : Components (filtered eligible state)
      (tokens priority (survivingIDs store reader))
      (tokens priority (retiredIDs store reader)))
    (client : Client (P := Sequence.protocol (Token Key)) (Return := Return))
    (sourceCost : Charge (provider eligible))
    (targetCost : Charge (Sequence.tails (Token Key)))
    (fuel : Nat) (control : client.V () ()) :
    (sequenceRefinement eligible).outcome client
        (advance (provider eligible) client sourceCost fuel ⟨(), control, state⟩).2 =
      (advance (Sequence.tails (Token Key)) client targetCost fuel
        ⟨(), control, (tokens priority (entryIDs store reader)).sort (· ≤ ·)⟩).2 := by
  have comparison := Hom.advance client (sequenceRefinement eligible) sourceCost targetCost fuel
    ⟨(), control, state⟩
  simpa only [Hom.packet, sequenceRefinement, Hom.comp, refinement,
    ReaderOrderedMerge.refinement, stamped_entry_source priority store reader
      (filtered eligible state) valid] using comparison

end Mettapedia.Machines.Cursor.ReaderOrderedMergeCursor
