import Mathlib.Logic.Equiv.Defs
import Mathlib.Data.Fin.Basic
import Mathlib.Data.BitVec
import Mathlib.Data.List.Perm.Subperm
import Lean.Elab.Tactic.Omega

/-!
# Values do not determine occurrences

Parallel canonicalization sorts and may collapse, so a proof relating two
parallel frontiers must say *which occurrence corresponds to which*.  The
tempting shortcut is to pair frontier entries by value: if the two sides
carry equal elements, zip them up.  This module shows the shortcut is
unsound in exactly the situation parallel composition creates — repeated
elements — and therefore that a correspondence must be carried as data,
not recovered from values.

The finite-namespace laws also show how successful reservations keep distinct
identities without wrapping, including across resumed batches. Refusal slots
remain in the result list. Atomic implementation and caller-retention laws are
separate from these completed-reservation laws.
-/

namespace Mettapedia.Algebra

namespace OccurrenceIdentity

/-- A two-element frontier whose entries carry the same value — the
minimal duplicate. -/
def duplicateFrontier : Fin 2 → Nat := fun _ => 7

/-- Exchange of the two positions. -/
def exchange : Fin 2 → Fin 2 := fun index => if index = 0 then 1 else 0

theorem exchange_ne_id : exchange ≠ id := by
  intro equal
  have atZero : exchange 0 = id 0 := congrFun equal 0
  simp [exchange] at atZero

/-- **Values do not determine the correspondence.**  On a frontier with a
repeated element, the identity and the exchange are *different* maps that
agree on every value.  A proof that recovers a correspondence from values
alone therefore cannot say which occurrence went where. -/
theorem occurrence_correspondence_not_determined_by_values :
    ∃ first second : Fin 2 → Fin 2,
      first ≠ second ∧
      ∀ index, duplicateFrontier (first index) =
        duplicateFrontier (second index) := by
  refine ⟨id, exchange, ?_, ?_⟩
  · intro equal
    exact exchange_ne_id equal.symm
  · intro index
    simp [duplicateFrontier]

/-- **The consequence for parallel alignment.**  Value-agreement of two
frontiers is strictly weaker than a correspondence: agreement holds for
both candidate maps above, so it cannot single one out.  Any parallel
restoration argument must therefore carry its permutation as evidence and
identify duplicates by position, never by content. -/
theorem value_agreement_does_not_yield_correspondence
    (recover : (Fin 2 → Nat) → (Fin 2 → Fin 2)) :
    ¬ ((recover duplicateFrontier = id) ∧
      (recover duplicateFrontier = exchange)) := by
  rintro ⟨isIdentity, isExchange⟩
  exact exchange_ne_id (isExchange.symm.trans isIdentity)

/-- Positive counterpart: when the frontier entries are pairwise distinct,
a value-preserving map *is* forced to be the identity, so the shortcut is
sound exactly in the duplicate-free case.  This delimits where the
shortcut may be used rather than banning it outright. -/
theorem injective_frontier_forces_identity {Value : Type}
    (frontier : Fin 2 → Value) (distinct : Function.Injective frontier)
    (relabel : Fin 2 → Fin 2)
    (preserves : ∀ index, frontier (relabel index) = frontier index) :
    relabel = id := by
  funext index
  exact distinct (preserves index)

/-! ## Finite namespaces at successful reservation points

Zero denotes refusal and the largest machine value is a permanent exhausted
state. These laws describe completed, linearized reservations. They do not
prove that a weak compare-exchange loop eventually succeeds, that an atomic
ABI implements the linearization, or that a caller retains refused work.
-/

/-- One completed reservation in a namespace with a reserved upper sentinel.
The counter is retained on refusal; a successful result is the old counter. -/
def reserve (maximum current : Nat) : Option Nat × Nat :=
  if current = 0 ∨ maximum ≤ current then (none, current)
  else (some current, current + 1)

theorem reserve_issued_iff (maximum current issued after : Nat) :
    reserve maximum current = (some issued, after) ↔
      0 < current ∧ current < maximum ∧ issued = current ∧ after = current + 1 := by
  by_cases invalid : current = 0 ∨ maximum ≤ current
  · constructor
    · intro granted
      have impossible : (none : Option Nat) = some issued := by
        simpa only [reserve, if_pos invalid] using congrArg Prod.fst granted
      cases impossible
    · rintro ⟨positive, below, _, _⟩
      exfalso
      rcases invalid with zero | exhausted <;> omega
  · have positive : 0 < current := by omega
    have below : current < maximum := by omega
    simp only [reserve, if_neg invalid, Prod.mk.injEq, Option.some.injEq]
    constructor
    · rintro ⟨same, advanced⟩
      exact ⟨positive, below, same.symm, advanced.symm⟩
    · rintro ⟨_, _, same, advanced⟩
      exact ⟨same.symm, advanced.symm⟩

theorem reserve_refused_iff (maximum current after : Nat) :
    reserve maximum current = (none, after) ↔
      (current = 0 ∨ maximum ≤ current) ∧ after = current := by
  by_cases invalid : current = 0 ∨ maximum ≤ current
  · rw [reserve, if_pos invalid]
    constructor
    · intro refused
      exact ⟨invalid, (congrArg Prod.snd refused).symm⟩
    · rintro ⟨_, same⟩
      subst after
      rfl
  · constructor
    · intro refused
      have impossible : some current = (none : Option Nat) := by
        simpa only [reserve, if_neg invalid] using congrArg Prod.fst refused
      cases impossible
    · rintro ⟨refused, _⟩
      exact False.elim (invalid refused)

theorem reserve_monotone (maximum current : Nat) : current ≤ (reserve maximum current).2 := by
  unfold reserve
  split <;> simp

theorem reserve_counter_bounded (maximum current : Nat) (fits : current ≤ maximum) :
    (reserve maximum current).2 ≤ maximum := by
  by_cases invalid : current = 0 ∨ maximum ≤ current
  · simpa only [reserve, if_pos invalid] using fits
  · simp only [reserve, if_neg invalid]
    omega

/-- An issued identity is positive and strictly below both the new counter
and the exhaustion sentinel. Neither sentinel can be a valid occurrence. -/
theorem reserve_identity_bounds (maximum current issued : Nat)
    (granted : (reserve maximum current).1 = some issued) :
    0 < issued ∧ issued < (reserve maximum current).2 ∧ issued < maximum := by
  have full : reserve maximum current = (some issued, (reserve maximum current).2) := by
    rw [← granted]
  obtain ⟨positive, below, same, advanced⟩ := (reserve_issued_iff _ _ _ _).mp full
  subst issued
  rw [advanced]
  exact ⟨positive, by omega, below⟩

/-- The independent unsigned implementation keeps its actual finite word.
Its reserved upper sentinel differs from a saturating cost counter, where
the largest representable total may still be exact. -/
def reserveWord {width : Nat} (current : BitVec width) : BitVec width × BitVec width :=
  if current = 0 ∨ current = BitVec.allOnes width then (0, current)
  else (current, current + 1)

theorem reserveWord_correspondence {width : Nat} (current : BitVec width) :
    let result := reserveWord current
    (if result.1 = 0 then none else some result.1.toNat, result.2.toNat) =
      reserve (2 ^ width - 1) current.toNat := by
  have fits : current.toNat ≤ 2 ^ width - 1 := by
    have bounded := current.isLt
    omega
  have zero : current = 0 ↔ current.toNat = 0 := by
    rw [← BitVec.toNat_inj]
    rfl
  have exhausted : current = BitVec.allOnes width ↔ 2 ^ width - 1 ≤ current.toNat := by
    rw [← BitVec.toNat_inj, BitVec.toNat_allOnes]
    omega
  by_cases refused : current = 0 ∨ current = BitVec.allOnes width
  · simp only [reserveWord, if_pos refused]
    have mathematical : current.toNat = 0 ∨ 2 ^ width - 1 ≤ current.toNat := by
      rcases refused with empty | full
      · exact Or.inl (zero.mp empty)
      · exact Or.inr (exhausted.mp full)
    simp only [ite_true, reserve, if_pos mathematical]
  · have mathematical : ¬(current.toNat = 0 ∨ 2 ^ width - 1 ≤ current.toNat) := by
      intro invalid
      apply refused
      rcases invalid with empty | full
      · exact Or.inl (zero.mpr empty)
      · exact Or.inr (exhausted.mpr full)
    have positiveWidth : 1 < 2 ^ width := by omega
    have oneNat : (1 : BitVec width).toNat = 1 := by
      change (1#width).toNat = 1
      rw [BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt positiveWidth
    have fitsNext : current.toNat + (1 : BitVec width).toNat < 2 ^ width := by
      rw [oneNat]
      omega
    simp only [reserveWord, if_neg refused, reserve, if_neg mathematical]
    rw [if_neg (fun empty => refused (Or.inl empty)), BitVec.toNat_add_of_lt fitsNext,
      oneNat]

/-- Retain one result slot per completed request, including refusals.
The counter and all previous result slots survive a later batch. -/
def reserveMany (maximum : Nat) : Nat → Nat → Nat × List (Option Nat)
  | current, 0 => (current, [])
  | current, count + 1 =>
      let first := reserve maximum current
      let rest := reserveMany maximum first.2 count
      (rest.1, first.1 :: rest.2)

theorem reserveMany_result_count (maximum current count : Nat) :
    (reserveMany maximum current count).2.length = count := by
  induction count generalizing current with
  | zero => rfl
  | succ count ih => simp [reserveMany, ih]

theorem reserveMany_monotone (maximum current count : Nat) :
    current ≤ (reserveMany maximum current count).1 := by
  induction count generalizing current with
  | zero => rfl
  | succ count ih => exact (reserve_monotone maximum current).trans (ih _)

/-- Every issued value lies above the batch's starting counter and below its
ending counter. This also supplies freshness to append-only receipt stores. -/
theorem reserveMany_identity_bounds (maximum current count issued : Nat)
    (present : some issued ∈ (reserveMany maximum current count).2) :
    current ≤ issued ∧ issued < (reserveMany maximum current count).1 := by
  induction count generalizing current with
  | zero => cases present
  | succ count ih =>
    rcases List.mem_cons.mp present with first | later
    · have granted := first.symm
      have full : reserve maximum current =
          (some issued, (reserve maximum current).2) := by rw [← granted]
      obtain ⟨_, _, same, _⟩ := (reserve_issued_iff _ _ _ _).mp full
      have upper := (reserve_identity_bounds maximum current issued granted).2.1
      exact ⟨Nat.le_of_eq same.symm,
        upper.trans_le (reserveMany_monotone maximum _ count)⟩
    · obtain ⟨lower, upper⟩ := ih (reserve maximum current).2 later
      exact ⟨(reserve_monotone maximum current).trans lower, upper⟩

/-- A later successful reservation cannot reuse an identity issued earlier
in the same namespace, even after intervening refused requests. -/
theorem reserveMany_issued_unique (maximum current count : Nat) :
    ((reserveMany maximum current count).2.filterMap id).Nodup := by
  induction count generalizing current with
  | zero => exact List.nodup_nil
  | succ count ih =>
    simp only [reserveMany, List.filterMap_cons]
    cases granted : (reserve maximum current).1 with
    | none => simpa only [granted, id_eq] using ih (reserve maximum current).2
    | some issued =>
      simp only [id_eq, List.nodup_cons]
      refine ⟨?_, ih _⟩
      intro present
      have found : some issued ∈ (reserveMany maximum (reserve maximum current).2 count).2 := by
        obtain ⟨result, occurs, equal⟩ := List.mem_filterMap.mp present
        simpa only [id_eq] using equal ▸ occurs
      have lower := (reserveMany_identity_bounds maximum _ count issued found).1
      have below := (reserve_identity_bounds maximum current issued granted).2.1
      omega

/-- Resuming a batch retains the same counter and complete refusal slots.
Restarting the namespace would violate the identity invariant. -/
theorem reserveMany_add (maximum current first second : Nat) :
    reserveMany maximum current (first + second) =
      let completed := reserveMany maximum current first
      let suffix := reserveMany maximum completed.1 second
      (suffix.1, completed.2 ++ suffix.2) := by
  induction first generalizing current with
  | zero => simp [reserveMany]
  | succ first ih =>
    simpa only [Nat.succ_add, reserveMany, List.cons_append] using
      congrArg (fun result => (result.1, (reserve maximum current).1 :: result.2))
        (ih (reserve maximum current).2)

theorem reserved_sentinel_controls :
    reserveMany 7 5 3 = (7, [some 5, some 6, none]) ∧
      reserveWord (255 : BitVec 8) = (0, 255) ∧
      reserveWord (0 : BitVec 8) = (0, 0) := by decide

/-- Blind machine increment at exhaustion wraps into the refusal sentinel.
Restarting a namespace likewise repeats an already issued identity. -/
theorem wrapping_and_reset_controls :
    (255 : BitVec 8) + 1 = 0 ∧
      ((reserveMany 7 1 2).2 ++ (reserveMany 7 1 2).2).filterMap id = [1, 2, 1, 2] ∧
      ¬ (((reserveMany 7 1 2).2 ++ (reserveMany 7 1 2).2).filterMap id).Nodup := by decide

/-! ## Weak compare-exchange retries and interleaved reservations

This protocol retains each invocation's expected value across arbitrary
interleaving and spurious weak-CAS failure. Successful linearization is derived
from the executable guard and equality test, rather than supplied as a
completed-reservation assumption. Atomic load/CAS implementation, source
admission and eventual success remain separate obligations. Its issued history
is an external observation of the schedule, not runtime receipt storage.
-/

namespace WeakReservation

variable {Caller : Type*} [DecidableEq Caller]

inductive Control where
  | unloaded
  | checking (expected : Nat)
  | returned (identity : Option Nat)
  deriving DecidableEq, Repr

structure State (Caller : Type*) where
  counter : Nat
  invocation : Caller → Control

inductive Request (Caller : Type*) where
  | load (caller : Caller)
  | attempt (caller : Caller) (permitSuccess : Bool)
  deriving DecidableEq, Repr

def initial (counter : Nat) : State Caller := ⟨counter, fun _ => .unloaded⟩

/-- Load and weak CAS are separate atomic boundaries. A failed comparison or
spurious failure refreshes the expected value without issuing an identity.
A finished invocation retains its result and cannot issue a second identity. -/
def step (maximum : Nat) (state : State Caller) :
    Request Caller → State Caller × Option (Caller × Nat)
  | .load caller => match state.invocation caller with
      | .unloaded =>
          ({ state with invocation := Function.update state.invocation caller (.checking state.counter) }, none)
      | _ => (state, none)
  | .attempt caller permitSuccess => match state.invocation caller with
      | .checking expected =>
          if expected = 0 ∨ maximum ≤ expected then
            ({ state with invocation := Function.update state.invocation caller (.returned none) }, none)
          else if permitSuccess = true ∧ state.counter = expected then
            (⟨expected + 1, Function.update state.invocation caller (.returned (some expected))⟩,
              some (caller, expected))
          else
            ({ state with invocation := Function.update state.invocation caller (.checking state.counter) }, none)
      | _ => (state, none)

/-- Any returned identity is the value actually replaced at the atomic
boundary, and the existing independent reservation specification determines
its new counter. A cached expected value alone cannot authorize issuance. -/
theorem issued_linearizes (maximum : Nat) (state : State Caller)
    (request : Request Caller) (caller : Caller) (identity : Nat)
    (issued : (step maximum state request).2 = some (caller, identity)) :
    state.counter = identity ∧
      (step maximum state request).1.counter = identity + 1 ∧
      reserve maximum state.counter = (some identity, identity + 1) := by
  cases request with
  | load selected =>
      cases prior : state.invocation selected <;> simp [step, prior] at issued
  | attempt selected permit =>
      cases prior : state.invocation selected with
      | unloaded => simp [step, prior] at issued
      | returned value => simp [step, prior] at issued
      | checking expected =>
          by_cases invalid : expected = 0 ∨ maximum ≤ expected
          · simp [step, prior, invalid] at issued
          · by_cases accepted : permit = true ∧ state.counter = expected
            · have same : expected = identity := by
                exact (Prod.mk.inj (Option.some.inj
                  (by simpa [step, prior, invalid, accepted] using issued))).2
              subst identity
              refine ⟨accepted.2, by simp [step, prior, invalid, accepted], ?_⟩
              apply (reserve_issued_iff maximum state.counter expected (expected + 1)).mpr
              exact ⟨by omega, by omega, accepted.2.symm, by rw [accepted.2]⟩
            · simp [step, prior, invalid, accepted] at issued

/-- A successful protocol attempt agrees with the independently implemented
finite-word reservation. The protocol maximum is the word's upper sentinel;
the shared counter relation retains the actual unsigned value, without
assuming that a completed atomic operation already implements reservation. -/
theorem issued_word_correspondence {width : Nat} (current : BitVec width)
    (state : State Caller) (request : Request Caller) (caller : Caller) (identity : Nat)
    (counterMatches : state.counter = current.toNat)
    (issued : (step (2 ^ width - 1) state request).2 = some (caller, identity)) :
    let result := reserveWord current
    (if result.1 = 0 then none else some result.1.toNat, result.2.toNat) =
      (some identity, (step (2 ^ width - 1) state request).1.counter) := by
  obtain ⟨_, advanced, reservation⟩ :=
    issued_linearizes (2 ^ width - 1) state request caller identity issued
  have words := reserveWord_correspondence current
  rw [← counterMatches, reservation] at words
  simpa only [advanced] using words

theorem counter_monotone (maximum : Nat) (state : State Caller) (request : Request Caller) :
    state.counter ≤ (step maximum state request).1.counter := by
  cases request with
  | load caller => cases prior : state.invocation caller <;> simp [step, prior]
  | attempt caller permit =>
      cases prior : state.invocation caller with
      | unloaded => simp [step, prior]
      | returned value => simp [step, prior]
      | checking expected =>
          by_cases invalid : expected = 0 ∨ maximum ≤ expected
          · simp [step, prior, invalid]
          · by_cases accepted : permit = true ∧ state.counter = expected
            · simp [step, prior, invalid, accepted]
            · simp [step, prior, invalid, accepted]

theorem counter_bounded (maximum : Nat) (state : State Caller) (request : Request Caller)
    (bounded : state.counter ≤ maximum) :
    (step maximum state request).1.counter ≤ maximum := by
  cases request with
  | load caller => cases prior : state.invocation caller <;> simpa [step, prior] using bounded
  | attempt caller permit =>
      cases prior : state.invocation caller with
      | unloaded => simpa [step, prior] using bounded
      | returned value => simpa [step, prior] using bounded
      | checking expected =>
          by_cases invalid : expected = 0 ∨ maximum ≤ expected
          · simpa [step, prior, invalid] using bounded
          · by_cases accepted : permit = true ∧ state.counter = expected
            · simp only [step, prior, if_neg invalid, if_pos accepted]
              omega
            · simpa [step, prior, invalid, accepted] using bounded

def run (maximum : Nat) :
    List (Request Caller) → State Caller → State Caller × List (Caller × Nat)
  | [], state => (state, [])
  | request :: rest, state =>
      let next := step maximum state request
      let later := run maximum rest next.1
      (later.1, next.2.toList ++ later.2)

theorem run_monotone (maximum : Nat) (requests : List (Request Caller)) (state : State Caller) :
    state.counter ≤ (run maximum requests state).1.counter := by
  induction requests generalizing state with
  | nil => exact le_rfl
  | cons request rest ih =>
      exact (counter_monotone maximum state request).trans (ih (step maximum state request).1)

theorem run_bounded (maximum : Nat) (requests : List (Request Caller)) (state : State Caller)
    (bounded : state.counter ≤ maximum) :
    (run maximum requests state).1.counter ≤ maximum := by
  induction requests generalizing state with
  | nil => exact bounded
  | cons request rest ih => exact ih _ (counter_bounded maximum state request bounded)

/-- Every issued value is strictly below the retained final counter and at
least the initial counter, even with failed comparisons and spurious retries. -/
theorem run_identity_bounds (maximum : Nat) (requests : List (Request Caller))
    (state : State Caller) (caller : Caller) (identity : Nat)
    (issued : (caller, identity) ∈ (run maximum requests state).2) :
    state.counter ≤ identity ∧ identity < (run maximum requests state).1.counter := by
  induction requests generalizing state with
  | nil => simp [run] at issued
  | cons request rest ih =>
      rcases List.mem_append.mp issued with first | later
      · have emission : (step maximum state request).2 = some (caller, identity) := by
          simpa using first
        obtain ⟨same, advanced, _⟩ := issued_linearizes maximum state request caller identity emission
        refine ⟨Nat.le_of_eq same, ?_⟩
        have monotone := run_monotone maximum rest (step maximum state request).1
        change identity < (run maximum rest (step maximum state request).1).1.counter
        rw [advanced] at monotone
        omega
      · obtain ⟨lower, upper⟩ := ih (step maximum state request).1 later
        exact ⟨(counter_monotone maximum state request).trans lower, upper⟩

/-- The whole interleaved protocol issues unique values. This is stronger than
assuming that completed CAS operations already obey sequential reservation. -/
theorem run_unique (maximum : Nat) (requests : List (Request Caller)) (state : State Caller) :
    ((run maximum requests state).2.map Prod.snd).Nodup := by
  induction requests generalizing state with
  | nil => exact List.nodup_nil
  | cons request rest ih =>
      cases emitted : (step maximum state request).2 with
      | none => simpa [run, emitted] using ih (step maximum state request).1
      | some value =>
          have first := issued_linearizes maximum state request value.1 value.2 emitted
          simp only [run, emitted, Option.toList_some, List.singleton_append, List.map_cons,
            List.nodup_cons]
          refine ⟨?_, ih _⟩
          intro repeated
          obtain ⟨later, member, same⟩ := List.mem_map.mp repeated
          have lower := (run_identity_bounds maximum rest (step maximum state request).1
            later.1 later.2 member).1
          rw [first.2.1, same] at lower
          omega

/-- Splitting an interleaving retains every invocation's expected value and
finished result as well as the shared counter and ordered issued history. -/
theorem run_append (maximum : Nat) (first second : List (Request Caller)) (state : State Caller) :
    run maximum (first ++ second) state =
      let before := run maximum first state
      let after := run maximum second before.1
      (after.1, before.2 ++ after.2) := by
  induction first generalizing state with
  | nil => rfl
  | cons request rest ih => simp [run, ih, List.append_assoc]

namespace Controls

def contested : List (Request (Fin 3)) :=
  [.load 0, .load 1, .attempt 0 true, .attempt 1 true, .attempt 1 false,
   .attempt 1 true, .load 2, .attempt 2 true]

/-- Both contenders read five. The first issues five; the second refreshes
after losing, survives a spurious failure, then issues six. The third refuses
at the sentinel, retaining its finished refusal and the counter seven. -/
theorem contested_and_spurious_control :
    (run 7 contested (initial 5)).2 = [(0, 5), (1, 6)] ∧
    (run 7 contested (initial 5)).1.counter = 7 ∧
    (run 7 contested (initial 5)).1.invocation 2 = .returned none := by
  decide

theorem stale_comparison_cannot_issue :
    let before := (run 7 [.load 0, .load 1, .attempt 0 true]
      (initial 5 : State (Fin 2))).1
    (step 7 before (.attempt 1 true)).2 = none ∧
      (step 7 before (.attempt 1 true)).1.invocation 1 = .checking 6 := by
  decide

/-- A well-formed, uncontested weak CAS may fail indefinitely. A bounded
number of attempts cannot establish allocation failure or eventual service. -/
theorem spurious_failure_is_not_exhaustion :
    let before := (step 7 (initial 5 : State Unit) (.load ())).1
    step 7 before (.attempt () false) = (before, none) ∧
      (step 7 before (.attempt () true)).2 = some ((), 5) := by
  constructor
  · rfl
  · decide

end Controls

end WeakReservation

/-! ## Checked coverage of keyed occurrences -/

section Coverage

variable {Entry Key Destination : Type*} [DecidableEq Entry] [DecidableEq Key]

/-- Preparation may enumerate entries in a different order, but must name
every actual occurrence exactly once. Payload equality is not the key. -/
def coverageCheck (key : Entry → Key) (actual proposed : List Entry) : Bool :=
  decide (proposed.length = actual.length) &&
    proposed.all (fun entry => decide (entry ∈ actual)) &&
    decide (proposed.map key).Nodup

/-- Complete coverage preserves all entry fields and multiplicities; the
independent key condition prevents submitting one occurrence twice. -/
def CompleteCoverage (key : Entry → Key) (actual proposed : List Entry) : Prop :=
  proposed.Perm actual ∧ (actual.map key).Nodup

theorem coverageCheck_iff (key : Entry → Key) (actual proposed : List Entry) :
    coverageCheck key actual proposed = true ↔ CompleteCoverage key actual proposed := by
  simp only [coverageCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  constructor
  · rintro ⟨⟨lengths, members⟩, distinct⟩
    have subset : proposed ⊆ actual := fun _ member => members _ member
    have permutation := (List.Nodup.of_map key distinct).subperm subset
    have exactEntries := permutation.perm_of_length_le (by omega)
    exact ⟨exactEntries, (exactEntries.map key).nodup_iff.mp distinct⟩
  · rintro ⟨permutation, distinct⟩
    exact ⟨⟨permutation.length_eq, fun entry member => permutation.mem_iff.mp member⟩,
      (permutation.map key).nodup_iff.mpr distinct⟩

/-- A checked representation change preserves and reflects complete coverage.
Injectivity concerns complete entries; the key law preserves logical identity. -/
theorem coverageCheck_map [DecidableEq Destination] (key : Entry → Key)
    (destinationKey : Destination → Key) (mapping : Entry → Destination)
    (injective : Function.Injective mapping)
    (keyLaw : ∀ entry, destinationKey (mapping entry) = key entry)
    (actual proposed : List Entry) :
    coverageCheck destinationKey (actual.map mapping) (proposed.map mapping) =
      coverageCheck key actual proposed := by
  apply Bool.eq_iff_iff.mpr
  rw [coverageCheck_iff, coverageCheck_iff]
  have keys : (actual.map mapping).map destinationKey = actual.map key := by
    simp only [List.map_map]
    exact List.map_congr_left (fun entry _ => keyLaw entry)
  simp only [CompleteCoverage, keys, List.map_perm_map_iff injective]

namespace CoverageControls

def actual : List (Nat × Nat) := [(1, 7), (2, 7)]

/-- Equal answer values still name two distinct prepared occurrences. -/
theorem duplicate_values_have_complete_coverage :
    coverageCheck Prod.fst actual [(2, 7), (1, 7)] = true ∧
      actual.map Prod.snd = [7, 7] := by decide

/-- Length and membership alone accept an omitted occurrence replaced by
a repeated one. The distinct-key check rejects that preparation. -/
theorem repeated_occurrence_does_not_cover :
    ([(1, 7), (1, 7)] : List (Nat × Nat)).length = actual.length ∧
      ([(1, 7), (1, 7)] : List (Nat × Nat)).all (fun entry => decide (entry ∈ actual)) = true ∧
      coverageCheck Prod.fst actual [(1, 7), (1, 7)] = false := by decide

/-- Correct counts and occurrence keys do not authorize a changed payload. -/
theorem same_keys_wrong_payload_refused :
    ([(1, 8), (2, 7)] : List (Nat × Nat)).map Prod.fst = actual.map Prod.fst ∧
      coverageCheck Prod.fst actual [(1, 8), (2, 7)] = false := by decide

end CoverageControls

end Coverage

/-! ## Ordered first encounters

An injective change of identities preserves the first-encounter sequence,
including the prefix already seen by a resumed computation. This concerns a
memo/census keyed by complete identities, not deduplication of authored rule
occurrences by their answer values. Copying and validation costs are separate
from the number of first encounters.
-/

theorem eraseDups_map_injective {A B : Type*} [BEq A] [LawfulBEq A]
    [BEq B] [LawfulBEq B] (mapping : A → B) (injective : Function.Injective mapping)
    (entries : List A) :
    (entries.map mapping).eraseDups = entries.eraseDups.map mapping := by
  match entries with
  | [] => rfl
  | head :: tail =>
      have comparison : (fun entry => !(mapping entry == mapping head)) =
          (fun entry => !(entry == head)) := by
        funext entry
        have equal : (mapping entry == mapping head) = (entry == head) := by
          apply Bool.eq_iff_iff.mpr
          simp only [beq_iff_eq, injective.eq_iff]
        exact congrArg Bool.not equal
      simp only [List.map_cons, List.eraseDups_cons, List.filter_map]
      change mapping head ::
          ((tail.filter (fun entry => !(mapping entry == mapping head))).map mapping).eraseDups =
        mapping head :: (tail.filter (fun entry => !(entry == head))).eraseDups.map mapping
      rw [comparison, eraseDups_map_injective mapping injective]
termination_by entries.length
decreasing_by
  exact Nat.lt_succ_of_le (List.length_filter_le _ _)

theorem first_seen_count_relocated {A B : Type*} [BEq A] [LawfulBEq A]
    [BEq B] [LawfulBEq B] (mapping : A → B) (injective : Function.Injective mapping)
    (entries : List A) :
    (entries.map mapping).eraseDups.length = entries.eraseDups.length := by
  rw [eraseDups_map_injective mapping injective, List.length_map]

theorem first_seen_resumed_account {A B : Type*} [BEq A] [LawfulBEq A]
    [BEq B] [LawfulBEq B] (mapping : A → B) (injective : Function.Injective mapping)
    (earlier suffix : List A) :
    ((earlier.map mapping ++ suffix.map mapping).eraseDups).length =
      earlier.eraseDups.length + (suffix.removeAll earlier).eraseDups.length := by
  rw [← List.map_append, first_seen_count_relocated mapping injective, List.eraseDups_append,
    List.length_append]

namespace FirstSeenControls

def source : List Nat := [0, 1, 0, 2, 1]
def destination : Nat → Nat := fun identity => 3 * identity + 7

theorem moved_repeated_identities_preserve_first_order :
    (source.map destination).eraseDups = [7, 10, 13] ∧
      source.eraseDups = [0, 1, 2] := by decide +kernel

theorem equal_payload_projection_collapses_productions :
    (([(0, 7), (1, 7), (0, 7)] : List (Nat × Nat)).map Prod.fst).eraseDups.length = 2 ∧
      (([(0, 7), (1, 7), (0, 7)] : List (Nat × Nat)).map Prod.snd).eraseDups.length = 1 :=
  by decide +kernel

theorem copied_carriers_can_split_a_shared_production :
    ([0, 0, 0] : List Nat).eraseDups.length = 1 ∧
      ([7, 8, 7] : List Nat).eraseDups.length = 2 := by decide +kernel

end FirstSeenControls


/-! ## Removing physical slots and reserving inclusive namespaces -/
variable {α β : Type*}

/-- Removing a selected physical slot moves the last slot into its place.
The recursive presentation retains every earlier slot in its original order. -/
def extractByLast : Nat → List α → Option (α × List α)
  | _, [] => none
  | 0, first :: rest =>
      some (first, match rest.getLast? with
        | none => []
        | some last => last :: rest.dropLast)
  | index + 1, first :: rest =>
      (extractByLast index rest).map (fun pair => (pair.1, first :: pair.2))

/-- Independent indexed write followed by shortening the live array. -/
def extractByLastIndexed (index : Nat) (rows : List α) : Option (α × List α) := do
  let selected ← rows[index]?
  let last ← rows.getLast?
  some (selected, (rows.set index last).dropLast)

theorem extractByLast_correspondence (index : Nat) (rows : List α) :
    extractByLast index rows = extractByLastIndexed index rows := by
  induction rows generalizing index with
  | nil => simp [extractByLast, extractByLastIndexed]
  | cons first rest ih =>
      cases index with
      | zero =>
          cases rest with
          | nil => rfl
          | cons second tail =>
              cases last : (second :: tail).getLast? with
              | none => simp only [List.getLast?_eq_none_iff] at last; cases last
              | some final =>
                  simp only [extractByLast, last, extractByLastIndexed,
                    List.getElem?_cons_zero, List.getLast?_cons_cons,
                    List.set_cons_zero, List.dropLast_cons_cons, bind, Option.bind_some]
      | succ index =>
          cases rest with
          | nil => simp [extractByLast, extractByLastIndexed, bind]
          | cons second tail =>
              simp only [extractByLast, ih, extractByLastIndexed,
                List.getElem?_cons_succ, List.getLast?_cons_cons]
              cases selected : (second :: tail)[index]? with
              | none => simp only [bind, Option.bind_none, Option.map_none]
              | some value =>
                  cases last : (second :: tail).getLast? with
                  | none => simp only [List.getLast?_eq_none_iff] at last; cases last
                  | some final =>
                      have nonempty : ((second :: tail).set index final) ≠ [] := by simp
                      simp only [bind, Option.bind_some, Option.map_some,
                        List.set_cons_succ, List.dropLast_cons_of_ne_nil nonempty]

theorem extractByLast_selected (index : Nat) (rows : List α) :
    (extractByLast index rows).map Prod.fst = rows[index]? := by
  induction rows generalizing index with
  | nil => simp [extractByLast]
  | cons first rest ih =>
      cases index with
      | zero => simp [extractByLast]
      | succ index =>
          simp only [extractByLast, Option.map_map, List.getElem?_cons_succ]
          exact ih index

theorem extractByLast_permutation (index : Nat) (rows : List α)
    (selected : α) (remaining : List α)
    (taken : extractByLast index rows = some (selected, remaining)) :
    (selected :: remaining).Perm rows := by
  induction rows generalizing index selected remaining with
  | nil => simp [extractByLast] at taken
  | cons first rest ih =>
      cases index with
      | zero =>
          cases last : rest.getLast? with
          | none =>
              have empty := List.getLast?_eq_none_iff.mp last
              subst rest
              simp only [extractByLast, List.getLast?_nil, Option.some.injEq,
                Prod.mk.injEq] at taken
              rcases taken with ⟨rfl, rfl⟩
              exact List.Perm.refl _
          | some final =>
              simp only [extractByLast, last, Option.some.injEq, Prod.mk.injEq] at taken
              rcases taken with ⟨rfl, rfl⟩
              have split := List.dropLast_append_getLast? final last
              have moved : (final :: rest.dropLast).Perm rest := by
                simpa only [List.singleton_append, split] using
                  (List.perm_append_comm (l₁ := [final]) (l₂ := rest.dropLast))
              exact moved.cons first
      | succ index =>
          simp only [extractByLast] at taken
          obtain ⟨pair, extracted, equal⟩ := Option.map_eq_some_iff.mp taken
          rcases pair with ⟨found, tail⟩
          simp only [Prod.mk.injEq] at equal
          rcases equal with ⟨rfl, rfl⟩
          exact (List.Perm.swap _ _ _).trans ((ih index found tail extracted).cons first)

theorem extractByLast_length (index : Nat) (rows : List α)
    (selected : α) (remaining : List α)
    (taken : extractByLast index rows = some (selected, remaining)) :
    remaining.length + 1 = rows.length := by
  have length := (extractByLast_permutation index rows selected remaining taken).length_eq
  simpa only [List.length_cons] using length

theorem extractByLast_keeps_other [DecidableEq α]
    (index : Nat) (rows : List α) (selected other : α) (remaining : List α)
    (taken : extractByLast index rows = some (selected, remaining))
    (different : other ≠ selected) : other ∈ remaining ↔ other ∈ rows := by
  have same : other ∈ (selected :: remaining) ↔ other ∈ rows :=
    (extractByLast_permutation index rows selected remaining taken).mem_iff
  simpa only [List.mem_cons, different, false_or] using same

theorem extractByLast_removes_unique [DecidableEq α]
    (index : Nat) (rows : List α) (selected : α) (remaining : List α)
    (taken : extractByLast index rows = some (selected, remaining))
    (unique : rows.Nodup) : selected ∉ remaining ∧ remaining.Nodup := by
  have transferred := (extractByLast_permutation index rows selected remaining taken).nodup_iff.mpr unique
  exact List.nodup_cons.mp transferred

theorem extractByLast_map (map : α → β) (index : Nat) (rows : List α) :
    extractByLast index (rows.map map) =
      (extractByLast index rows).map (fun pair => (map pair.1, pair.2.map map)) := by
  induction rows generalizing index with
  | nil => simp [extractByLast]
  | cons first rest ih =>
      cases index with
      | zero =>
          simp only [List.map_cons, extractByLast, List.getLast?_map]
          cases rest.getLast? <;> simp [List.map_dropLast]
      | succ index =>
          simp only [List.map_cons, extractByLast, ih, Option.map_map]
          rfl

/-- This namespace uses every positive machine word, including the largest.
Issuing that final identity exhausts the frontier to zero; it never restarts. -/
def reserveInclusive (maximum current : Nat) : Option Nat × Nat :=
  if current = 0 ∨ maximum < current then (none, current)
  else (some current, if current = maximum then 0 else current + 1)

theorem reserveInclusive_issued_iff (maximum current issued after : Nat) :
    reserveInclusive maximum current = (some issued, after) ↔
      0 < current ∧ current ≤ maximum ∧ issued = current ∧
        after = (if current = maximum then 0 else current + 1) := by
  by_cases invalid : current = 0 ∨ maximum < current
  · constructor
    · intro granted
      have impossible : (none : Option Nat) = some issued := by
        simpa only [reserveInclusive, if_pos invalid] using congrArg Prod.fst granted
      cases impossible
    · rintro ⟨positive, below, _, _⟩
      exfalso
      rcases invalid with zero | exhausted <;> omega
  · have positive : 0 < current := by omega
    have below : current ≤ maximum := by omega
    simp only [reserveInclusive, if_neg invalid, Prod.mk.injEq, Option.some.injEq]
    constructor
    · rintro ⟨same, advanced⟩
      exact ⟨positive, below, same.symm, advanced.symm⟩
    · rintro ⟨_, _, same, advanced⟩
      exact ⟨same.symm, advanced.symm⟩

theorem reserveInclusive_exhausted (maximum : Nat) :
    reserveInclusive maximum 0 = (none, 0) := by simp [reserveInclusive]

def reserveInclusiveWord {width : Nat} (current : BitVec width) : BitVec width × BitVec width :=
  if current = 0 then (0, current)
  else (current, if current = BitVec.allOnes width then 0 else current + 1)

theorem reserveInclusiveWord_correspondence {width : Nat} (current : BitVec width) :
    let result := reserveInclusiveWord current
    (if result.1 = 0 then none else some result.1.toNat, result.2.toNat) =
      reserveInclusive (2 ^ width - 1) current.toNat := by
  have fits : current.toNat ≤ 2 ^ width - 1 := by
    have bounded := current.isLt
    omega
  have zero : current = 0 ↔ current.toNat = 0 := by
    rw [← BitVec.toNat_inj]
    rfl
  have last : current = BitVec.allOnes width ↔ current.toNat = 2 ^ width - 1 := by
    rw [← BitVec.toNat_inj, BitVec.toNat_allOnes]
  by_cases empty : current = 0
  · have mathematical : current.toNat = 0 ∨ 2 ^ width - 1 < current.toNat := Or.inl (zero.mp empty)
    simp only [reserveInclusiveWord, if_pos empty, reserveInclusive, if_pos mathematical]
    rfl
  · have mathematical : ¬(current.toNat = 0 ∨ 2 ^ width - 1 < current.toNat) := by
      rintro (none | outside)
      · exact empty (zero.mpr none)
      · omega
    simp only [reserveInclusiveWord, if_neg empty, reserveInclusive, if_neg mathematical]
    by_cases final : current = BitVec.allOnes width
    · simp only [if_pos final, if_pos (last.mp final)]
      have zeroWord : (0 : BitVec width).toNat = 0 := by
        change (0#width).toNat = 0
        rw [BitVec.toNat_ofNat, Nat.zero_mod]
      exact congrArg (fun number : Nat => (some current.toNat, number)) zeroWord
    · have notFinal := (not_congr last).mp final
      have positiveWidth : 1 < 2 ^ width := by
        have nonzero : current.toNat ≠ 0 := fun h => empty (zero.mpr h)
        omega
      have oneNat : (1 : BitVec width).toNat = 1 := by
        change (1#width).toNat = 1
        rw [BitVec.toNat_ofNat]
        exact Nat.mod_eq_of_lt positiveWidth
      have nextFits : current.toNat + (1 : BitVec width).toNat < 2 ^ width := by
        rw [oneNat]
        omega
      simp only [if_neg final, if_neg notFinal]
      rw [BitVec.toNat_add_of_lt nextFits, oneNat]

namespace Controls

theorem last_identity_is_usable_once :
    reserveInclusive 15 15 = (some 15, 0) ∧ reserveInclusive 15 0 = (none, 0) ∧
      reserve 15 15 = (none, 15) := by decide

theorem inclusive_word_never_restarts_after_final_issue :
    reserveInclusiveWord (15 : BitVec 4) = (15, 0) ∧
      reserveInclusiveWord (0 : BitVec 4) = (0, 0) ∧
      reserveInclusiveWord (14 : BitVec 4) = (14, 15) := by decide

theorem swapped_deletion_changes_order :
    extractByLast 1 [10, 20, 30, 40] = some (20, [10, 40, 30]) ∧
      extractByLast 1 [10, 20, 30, 40] ≠ some (20, [10, 30, 40]) := by decide

theorem equal_payload_occurrences_survive :
    extractByLast 1 [(1, 7), (2, 7), (3, 7)] = some ((2, 7), [(1, 7), (3, 7)]) ∧
      extractByLast 3 [(1, 7), (2, 7), (3, 7)] = none := by decide

end Controls

end OccurrenceIdentity

end Mettapedia.Algebra
