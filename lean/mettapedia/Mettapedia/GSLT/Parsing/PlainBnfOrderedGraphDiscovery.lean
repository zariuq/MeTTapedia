import Mathlib.Data.List.FinRange
import Lean.Elab.Tactic.Omega

/-!
# Ordered discovery for the plain-BNF grammar graph

An alternative retains its reference occurrences, including repeated references.
`leavesAdmitted` records the selected analysis of literal and lexical leaves:
productivity and nullability instantiate that finite classification differently.
Definition positions are their admitted source order, not an inference calculus.

The direct sweep updates known names immediately. Its reference event scheduler
skips positions until the next discovery, then resumes strictly after that
position in the same sweep. It recomputes readiness from grammar data; it is not
the reverse-incidence/counter implementation and carries no improved complexity
claim. The proved factorization identifies the next discovery and preserves the
entire ordered result of the remaining sweep, including its final known state.

The bridge from the actual structured document and the optimized dependency
scheduler are separate obligations. No authored source or runtime is replaced.
-/

namespace Mettapedia.GSLT.Parsing.PlainBnfOrderedGraphDiscovery

structure Alternative (size : Nat) where
  references : List (Fin size)
  leavesAdmitted : Bool
  deriving DecidableEq, Repr

abbrev Grammar (size : Nat) := Fin size → List (Alternative size)
abbrev Known (size : Nat) := Fin size → Bool

def alternativeReady {size : Nat} (known : Known size) (alternative : Alternative size) : Bool :=
  alternative.leavesAdmitted && alternative.references.all known

def ready {size : Nat} (grammar : Grammar size) (known : Known size) (position : Fin size) : Bool :=
  !known position && (grammar position).any (alternativeReady known)

def publish {size : Nat} (known : Known size) (position : Fin size) : Known size :=
  fun other => if other = position then true else known other

/-- Unfulfilled reference occurrences, not distinct names. This is the exact
counter represented by one reverse-incidence edge per authored occurrence. -/
def remainingOccurrences {size : Nat} (known : Known size) : List (Fin size) → Nat
  | [] => 0
  | head :: tail => (if known head then 0 else 1) + remainingOccurrences known tail

theorem remainingOccurrences_zero_iff {size : Nat} (known : Known size)
    (references : List (Fin size)) :
    remainingOccurrences known references = 0 ↔ references.all known = true := by
  induction references with
  | nil => simp [remainingOccurrences]
  | cons head tail ih =>
      cases value : known head <;> simp [remainingOccurrences, value, ih]

theorem alternativeReady_counter_exact {size : Nat} (known : Known size)
    (alternative : Alternative size) :
    alternativeReady known alternative = true ↔
      alternative.leavesAdmitted = true ∧
        remainingOccurrences known alternative.references = 0 := by
  simp [alternativeReady, remainingOccurrences_zero_iff]

/-- Publishing a fresh definition discharges every repeated reference to it.
Deduplicating notification edges while retaining occurrence counters is wrong. -/
theorem remainingOccurrences_publish {size : Nat} (known : Known size)
    (position : Fin size) (fresh : known position = false)
    (references : List (Fin size)) :
    remainingOccurrences (publish known position) references + references.count position =
      remainingOccurrences known references := by
  induction references with
  | nil => simp [remainingOccurrences]
  | cons head tail ih =>
      by_cases same : head = position
      · subst head
        simp [remainingOccurrences, publish, fresh]
        omega
      · cases value : known head <;>
          simp [remainingOccurrences, publish, same, value] <;> omega

structure SweepResult (size : Nat) where
  known : Known size
  discoveries : List (Fin size)

/-- The authored pass's in-place source-order behavior, stated independently. -/
def sweep {size : Nat} (grammar : Grammar size) :
    List (Fin size) → Known size → SweepResult size
  | [], known => ⟨known, []⟩
  | position :: tail, known =>
      if ready grammar known position then
        let rest := sweep grammar tail (publish known position)
        ⟨rest.known, position :: rest.discoveries⟩
      else sweep grammar tail known

/-- Select one enabled position without changing which names are known. -/
def nextReady {size : Nat} (grammar : Grammar size) :
    List (Fin size) → Known size → Option (Fin size × List (Fin size))
  | [], _ => none
  | position :: tail, known =>
      if ready grammar known position then some (position, tail)
      else nextReady grammar tail known

theorem nextReady_none_iff {size : Nat} (grammar : Grammar size)
    (positions : List (Fin size)) (known : Known size) :
    nextReady grammar positions known = none ↔
      ∀ position ∈ positions, ready grammar known position = false := by
  induction positions with
  | nil => simp [nextReady]
  | cons position tail ih =>
      cases enabled : ready grammar known position <;> simp [nextReady, enabled, ih]

theorem nextReady_some_split {size : Nat} (grammar : Grammar size)
    (positions : List (Fin size)) (known : Known size)
    {position : Fin size} {tail : List (Fin size)}
    (selected : nextReady grammar positions known = some (position, tail)) :
    ∃ skipped, positions = skipped ++ position :: tail ∧
      (∀ earlier ∈ skipped, ready grammar known earlier = false) ∧
      ready grammar known position = true := by
  induction positions with
  | nil => simp [nextReady] at selected
  | cons head rest ih =>
      cases enabled : ready grammar known head with
      | false =>
          have selection : nextReady grammar rest known = some (position, tail) := by
            simpa [nextReady, enabled] using selected
          obtain ⟨skipped, split, disabled, found⟩ := ih selection
          refine ⟨head :: skipped, by simp [split], ?_, found⟩
          intro earlier membership
          rcases List.mem_cons.mp membership with same | inside
          · simpa [same] using enabled
          · exact disabled earlier inside
      | true =>
          have fields : head = position ∧ rest = tail := by
            simpa [nextReady, enabled] using selected
          rcases fields with ⟨rfl, rfl⟩
          exact ⟨[], rfl, by simp, enabled⟩

/-- Skipping a disabled skipped cannot alter either ordered results or state. -/
theorem sweep_skip_disabled_prefix {size : Nat} (grammar : Grammar size)
    (skipped tail : List (Fin size)) (known : Known size)
    (disabled : ∀ position ∈ skipped, ready grammar known position = false) :
    sweep grammar (skipped ++ tail) known = sweep grammar tail known := by
  induction skipped with
  | nil => rfl
  | cons head rest ih =>
      have headDisabled := disabled head (by simp)
      have restDisabled : ∀ position ∈ rest, ready grammar known position = false :=
        fun position membership => disabled position (by simp [membership])
      simpa [sweep, headDisabled] using ih restDisabled

/-- Next-event factorization of an entire in-place sweep. The selector reads
the initial known state, while the suffix executes with the published state. -/
theorem sweep_nextReady {size : Nat} (grammar : Grammar size)
    (positions : List (Fin size)) (known : Known size) :
    sweep grammar positions known =
      match nextReady grammar positions known with
      | none => ⟨known, []⟩
      | some (position, tail) =>
          let rest := sweep grammar tail (publish known position)
          ⟨rest.known, position :: rest.discoveries⟩ := by
  induction positions with
  | nil => rfl
  | cons position tail ih =>
      cases enabled : ready grammar known position <;> simp [sweep, nextReady, enabled, ih]

theorem selected_is_next_discovery {size : Nat} (grammar : Grammar size)
    (positions : List (Fin size)) (known : Known size)
    {position : Fin size} {tail : List (Fin size)}
    (selected : nextReady grammar positions known = some (position, tail)) :
    (sweep grammar positions known).discoveries =
      position :: (sweep grammar tail (publish known position)).discoveries := by
  rw [sweep_nextReady, selected]

theorem no_selected_discovery_preserves_state {size : Nat} (grammar : Grammar size)
    (positions : List (Fin size)) (known : Known size)
    (noneReady : nextReady grammar positions known = none) :
    sweep grammar positions known = ⟨known, []⟩ := by
  rw [sweep_nextReady, noneReady]

/-- Execute only selected discoveries inside one sweep. The selector itself
is still a reference scan; this is not a bound on a native priority queue. -/
def sweepEvents {size : Nat} (grammar : Grammar size) :
    Nat → List (Fin size) → Known size → SweepResult size
  | 0, _, known => ⟨known, []⟩
  | fuel + 1, positions, known =>
      match nextReady grammar positions known with
      | none => ⟨known, []⟩
      | some (position, tail) =>
          let rest := sweepEvents grammar fuel tail (publish known position)
          ⟨rest.known, position :: rest.discoveries⟩

/-- Discovery-directed execution has exactly the full ordered result of an
in-place sweep. The bound counts positions, not derivation witnesses. -/
theorem sweepEvents_eq_sweep {size : Nat} (grammar : Grammar size)
    (positions : List (Fin size)) (known : Known size) (fuel : Nat)
    (enough : positions.length ≤ fuel) :
    sweepEvents grammar fuel positions known = sweep grammar positions known := by
  induction positions generalizing fuel known with
  | nil => cases fuel <;> rfl
  | cons position tail ih =>
      cases fuel with
      | zero => simp at enough
      | succ fuel =>
          have tailEnough : tail.length ≤ fuel := Nat.le_of_succ_le_succ enough
          cases enabled : ready grammar known position with
          | true =>
              simp only [sweepEvents, nextReady, enabled, ↓reduceIte, sweep]
              rw [ih (publish known position) fuel tailEnough]
          | false =>
              have skip : sweepEvents grammar (fuel + 1) (position :: tail) known =
                  sweepEvents grammar (fuel + 1) tail known := by
                simp [sweepEvents, nextReady, enabled]
              rw [skip, ih known (fuel + 1) (Nat.le_trans tailEnough (Nat.le_succ fuel))]
              simp [sweep, enabled]

structure Event (size : Nat) where
  round : Nat
  position : Fin size
  deriving DecidableEq, Repr

/-- First scan position after a prerequisite is actually published. -/
def scheduledAfter {size : Nat} (event : Event size) (target : Fin size) : Event size :=
  ⟨if event.position < target then event.round else event.round + 1, target⟩

theorem scheduledAfter_same_round {size : Nat} (event : Event size) (target : Fin size)
    (later : event.position < target) :
    scheduledAfter event target = ⟨event.round, target⟩ := by
  simp [scheduledAfter, later]

theorem scheduledAfter_next_round {size : Nat} (event : Event size) (target : Fin size)
    (earlier : target ≤ event.position) :
    scheduledAfter event target = ⟨event.round + 1, target⟩ := by
  simp [scheduledAfter, not_lt.mpr earlier]

/-- Reference event selection: retain the current sweep suffix, wrapping only
when it contains no enabled unpublished position. No queue entry is published. -/
def nextEvent {size : Nat} (grammar : Grammar size) (known : Known size)
    (round cursor : Nat) : Option (Event size) :=
  let positions := List.finRange size
  match nextReady grammar (positions.drop cursor) known with
  | some (position, _) => some ⟨round, position⟩
  | none =>
      match nextReady grammar positions known with
      | some (position, _) => some ⟨round + 1, position⟩
      | none => none

/-- Bounded reference execution, with fuel counting discoveries rather than
inert definition visits. Publication occurs when an event is selected. -/
def runEvents {size : Nat} (grammar : Grammar size) :
    Nat → Known size → Nat → Nat → List (Event size)
  | 0, _, _, _ => []
  | fuel + 1, known, round, cursor =>
      match nextEvent grammar known round cursor with
      | none => []
      | some event => event :: runEvents grammar fuel (publish known event.position)
          event.round (event.position.val + 1)

private def cascade : Grammar 3 := fun position =>
  if position = 1 then [⟨[0], true⟩] else [⟨[], true⟩]

/-- A newly enabled later definition is discovered in the same sweep, before
an independent later seed. A FIFO seeded with all ready definitions differs. -/
theorem same_round_cascade :
    runEvents cascade 3 (fun _ => false) 0 0 =
      [⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 2⟩] := by decide

private def deferred : Grammar 3 := fun position =>
  if position = 0 then [⟨[1], true⟩]
  else if position = 1 then [⟨[], true⟩]
  else [⟨[0], true⟩]

private def afterMiddle : Known 3 := publish (fun _ => false) 1

/-- Queueing position zero after position one must not publish it early:
doing so spuriously enables position two in the current, rather than next, sweep. -/
theorem enqueue_before_pop_changes_readiness :
    ready deferred afterMiddle 2 = false ∧
      ready deferred (publish afterMiddle 0) 2 = true ∧
      runEvents deferred 3 (fun _ => false) 0 0 =
        [⟨0, 1⟩, ⟨1, 0⟩, ⟨1, 2⟩] := by decide

/-- Both repeated reference occurrences survive; their conjunction can become
true when the one referenced definition is published. -/
theorem repeated_references_retained (known : Known 2) :
    (Alternative.mk [0, 0] true : Alternative 2).references.length = 2 ∧
      alternativeReady known ⟨[0, 0], true⟩ = known 0 := by
  cases equal : known 0 <;> simp [alternativeReady, equal]

theorem unseeded_cycle_has_no_event :
    runEvents (fun _ : Fin 1 => [⟨[0], true⟩]) 1 (fun _ => false) 0 0 = [] := by decide

end Mettapedia.GSLT.Parsing.PlainBnfOrderedGraphDiscovery
