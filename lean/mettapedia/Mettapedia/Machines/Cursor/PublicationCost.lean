import Mettapedia.Machines.Cursor.Fold
import Mettapedia.Machines.Cursor.FairObservation

/-!
# Publication bytes, private working space, and retained execution

The ordinary sequence cursor is charged for each delivered occurrence's
publication payload. Its executed-prefix receipt is exactly the sum of those
payloads. An independently implemented cumulative publication purse succeeds
exactly when that sum fits. The purse therefore rejects some arbitrarily long
streams even when each individual payload has the same bounded size.

This distinguishes output charge from private working space. `transientPeak`
models holding just the current payload; it is not a bound on an arbitrary
producer's stack, retained answers, or allocator overhead. A materializing
consumer still retains its result. Charges are additive payload bytes, not
CPU instructions or a lower bound on a representation that shares payloads.

Retained execution preserves the exact prefix receipt without replay. A
separate trace control shows why irreversible early publication cannot simply
replace an observer which discards all provisional answers on a later error.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor.PublicationCost

open Mettapedia.TypeTheory

variable {Item Accumulator : Type}

def publicationBytes (bytes : Item → Nat) (items : List Item) : Nat :=
  (items.map bytes).sum

def publicationCharge (bytes : Item → Nat) : Charge (Sequence.tails Item) :=
  fun items _ => match items with
    | [] => 0
    | item :: _ => bytes item

/-- This receipt comes from executing the common cursor, not from replacing
its evaluator with a byte-counting function. Duplicate values pay per delivery. -/
theorem prefix_publication_exact (bytes : Item → Nat)
    (consume : Accumulator → Item → Accumulator)
    (items : List Item) (initial : Accumulator) (count : Nat)
    (within : count ≤ items.length) :
    (advance (Sequence.tails Item) (Fold.client consume)
      (publicationCharge bytes) count (Fold.start _ consume items initial)).1 =
      publicationBytes bytes (items.take count) := by
  induction count generalizing items initial with
  | zero => rfl
  | succ count ih =>
      cases items with
      | nil => simp at within
      | cons item rest =>
          have bound : count ≤ rest.length := by simpa using within
          change bytes item +
            (advance (Sequence.tails Item) (Fold.client consume)
              (publicationCharge bytes) count
              (Fold.start _ consume rest (consume initial item))).1 = _
          rw [ih rest (consume initial item) bound]
          rfl

/-- Resumption pays the delivered prefix once, regardless of where the
inspection budget was split. The accumulator and provider residual are kept
by `resume`; no fresh source enumeration is substituted. -/
theorem resumed_prefix_no_replay (bytes : Item → Nat)
    (consume : Accumulator → Item → Accumulator)
    (items : List Item) (initial : Accumulator) (first second : Nat)
    (within : first + second ≤ items.length) :
    (resume (Sequence.tails Item) (Fold.client consume)
      (publicationCharge bytes) second
      (advance (Sequence.tails Item) (Fold.client consume)
        (publicationCharge bytes) first (Fold.start _ consume items initial))).1 =
      publicationBytes bytes (items.take (first + second)) := by
  rw [← advance_add]
  exact prefix_publication_exact bytes consume items initial (first + second) within

/-- Exhaustion and client return do not create another payload. -/
theorem complete_publication_exact (bytes : Item → Nat)
    (consume : Accumulator → Item → Accumulator)
    (items : List Item) (initial : Accumulator) :
    (advance (Sequence.tails Item) (Fold.client consume)
      (publicationCharge bytes) (items.length + 2)
      (Fold.start _ consume items initial)).1 = publicationBytes bytes items := by
  induction items generalizing initial with
  | nil => rfl
  | cons item rest ih =>
      change bytes item +
        (advance (Sequence.tails Item) (Fold.client consume)
          (publicationCharge bytes) (rest.length + 2)
          (Fold.start _ consume rest (consume initial item))).1 = _
      rw [ih]
      rfl

/-- A physical purse charged cumulatively for copied output occurrences. -/
def reserve (bytes : Item → Nat) : Nat → List Item → Option Nat
  | available, [] => some available
  | available, item :: rest =>
      if bytes item ≤ available then reserve bytes (available - bytes item) rest
      else none

/-- Exact characterization of the independently recursive purse algorithm. -/
theorem reserve_eq_some_iff (bytes : Item → Nat)
    (items : List Item) (available remaining : Nat) :
    reserve bytes available items = some remaining ↔
      publicationBytes bytes items + remaining = available := by
  induction items generalizing available with
  | nil => simp [reserve, publicationBytes, eq_comm]
  | cons item rest ih =>
      simp only [reserve]
      by_cases fits : bytes item ≤ available
      · rw [if_pos fits, ih]
        simp only [publicationBytes, List.map_cons, List.sum_cons]
        omega
      · rw [if_neg fits]
        simp only [reduceCtorEq, false_iff, publicationBytes, List.map_cons, List.sum_cons]
        omega

theorem reserve_succeeds_iff (bytes : Item → Nat)
    (items : List Item) (available : Nat) :
    (∃ remaining, reserve bytes available items = some remaining) ↔
      publicationBytes bytes items ≤ available := by
  simp only [reserve_eq_some_iff]
  constructor
  · rintro ⟨remaining, exact⟩
    omega
  · intro fits
    exact ⟨available - publicationBytes bytes items, by omega⟩

theorem reserve_fails_iff (bytes : Item → Nat)
    (items : List Item) (available : Nat) :
    reserve bytes available items = none ↔ available < publicationBytes bytes items := by
  constructor
  · intro failed
    by_contra notLarge
    have fits : publicationBytes bytes items ≤ available := by omega
    obtain ⟨remaining, succeeded⟩ := (reserve_succeeds_iff bytes items available).mpr fits
    rw [failed] at succeeded
    cases succeeded
  · intro tooLarge
    cases result : reserve bytes available items with
    | none => rfl
    | some remaining =>
        have fits := (reserve_eq_some_iff bytes items available remaining).mp result
        omega

/-- A lease which holds one payload at a time, with the previous payload
released before acquiring the next. It excludes any retained result storage. -/
def transientPeak (bytes : Item → Nat) : List Item → Nat
  | [] => 0
  | item :: rest => max (bytes item) (transientPeak bytes rest)

theorem transientPeak_le (bytes : Item → Nat) (items : List Item) (bound : Nat)
    (each : ∀ item ∈ items, bytes item ≤ bound) :
    transientPeak bytes items ≤ bound := by
  induction items with
  | nil => exact Nat.zero_le _
  | cons item rest ih =>
      exact max_le (each item (by simp))
        (ih (by intro other member; exact each other (by simp [member])))

/-- No fixed cumulative output purse admits all streams whose individual
payloads have size one. This is a family, not a single threshold example. -/
theorem bounded_payloads_cross_every_purse (available : Nat) :
    let items := List.replicate (available + 1) ()
    transientPeak (fun _ : Unit => 1) items ≤ 1 ∧
      reserve (fun _ : Unit => 1) available items = none := by
  constructor
  · exact transientPeak_le _ _ _ (by intros; exact Nat.le_refl _)
  · apply (reserve_fails_iff _ _ _).mpr
    simp [publicationBytes]

/-! ## Atomic and irrevocable output are different observers -/

inductive Event (Item Error : Type) where
  | answer (item : Item)
  | raise (error : Error)
  deriving DecidableEq, Repr

/-- An atomic result: a later raise discards preceding tentative answers. -/
def atomicResult {Error : Type} : List (Event Item Error) → Except Error (List Item)
  | [] => .ok []
  | .raise error :: _ => .error error
  | .answer item :: rest =>
      match atomicResult rest with
      | .error error => .error error
      | .ok items => .ok (item :: items)

/-- The externally visible events produced after atomic completion. -/
def atomicEvents {Error : Type} (events : List (Event Item Error)) : List (Event Item Error) :=
  match atomicResult events with
  | .error error => [.raise error]
  | .ok items => items.map Event.answer

/-- Irrevocable delivery stops at the first error, but cannot retract output. -/
def streamingEvents {Error : Type} : List (Event Item Error) → List (Event Item Error)
  | [] => []
  | .raise error :: _ => [.raise error]
  | .answer item :: rest => .answer item :: streamingEvents rest

theorem failure_free_publication_agrees {Error : Type} (items : List Item) :
    atomicEvents (items.map (Event.answer (Error := Error))) =
      streamingEvents (items.map Event.answer) := by
  have atomic : atomicResult (items.map (Event.answer (Error := Error))) = .ok items := by
    induction items with
    | nil => rfl
    | cons item rest ih => simp [atomicResult, ih]
  have streamed : streamingEvents (items.map (Event.answer (Error := Error))) =
      items.map Event.answer := by
    clear atomic
    induction items with
    | nil => rfl
    | cons item rest ih => simp [streamingEvents, ih]
  rw [atomicEvents, atomic, streamed]

theorem late_error_forbids_irrevocable_atomic_publication {Error : Type}
    (item : Item) (error : Error) :
    atomicEvents [.answer item, .raise error] ≠
      streamingEvents [.answer item, .raise error] := by
  simp [atomicEvents, atomicResult, streamingEvents]

/-- A genuinely ongoing producer never supplies a terminal exhaustion reply.
The statement holds for every finite inspection allowance. -/
theorem full_collection_of_stream_never_completes {World : Type}
    (expected : Nat → Item) (fuel index : Nat) (world : World) :
    (Mettapedia.GSLT.LanguageDef.NativeControlEffectCursor.collectCounted
      (FairObservation.streamPull expected) fuel index world).2.2 = none := by
  induction fuel generalizing index with
  | zero => rfl
  | succ fuel ih =>
      simp [Mettapedia.GSLT.LanguageDef.NativeControlEffectCursor.collectCounted,
        FairObservation.streamPull, ih]

/-- Every natural-valued demand is still finite. A physical collection-width
boundary does not license replacing a large demand by unbounded collection.
No large concrete list is allocated in this general proof. -/
theorem finite_demand_is_not_full_collection {World : Type}
    (expected : Nat → Item) (demand index : Nat) (world : World) :
    (Mettapedia.GSLT.LanguageDef.NativeControlBoundedCursor.collectBounded
      (FairObservation.streamPull expected) demand demand index world).2.stop = .limit ∧
    ∀ fuel,
      (Mettapedia.GSLT.LanguageDef.NativeControlEffectCursor.collectCounted
        (FairObservation.streamPull expected) fuel index world).2.2 = none := by
  constructor
  · rw [FairObservation.stream_collect_exact]
  · intro fuel
    exact full_collection_of_stream_never_completes expected fuel index world


namespace Composition

variable {Error : Type}

/-- The HE reference first completes an atomic answer collection, then folds
its ordered occurrences. No provisional scalar result is published. -/
def heMaterializedFold (consume : Accumulator → Item → Accumulator)
    (initial : Accumulator) (events : List (Event Item Error)) : Except Error Accumulator :=
  (atomicResult events).map (fun items => items.foldl consume initial)

/-- PeTTa's collecting worker retains a reverse list while answers arrive.
The public list is restored to occurrence order only at completion. -/
def pettaCollect : List Item → List (Event Item Error) → Except Error (List Item)
  | collected, [] => .ok collected.reverse
  | _, .raise error :: _ => .error error
  | collected, .answer item :: rest => pettaCollect (item :: collected) rest

theorem pettaCollect_eq (events : List (Event Item Error)) (collected : List Item) :
    pettaCollect collected events =
      (atomicResult events).map (fun items => collected.reverse ++ items) := by
  induction events generalizing collected with
  | nil => simp [pettaCollect, atomicResult, Except.map]
  | cons event rest ih =>
      cases event with
      | raise error => rfl
      | answer item =>
          rw [pettaCollect, ih]
          cases found : atomicResult rest with
          | error error => simp [atomicResult, found, Except.map]
          | ok items => simp [atomicResult, found, Except.map, List.append_assoc]

def pettaMaterializedFold (consume : Accumulator → Item → Accumulator)
    (initial : Accumulator) (events : List (Event Item Error)) : Except Error Accumulator :=
  (pettaCollect [] events).map (fun items => items.foldl consume initial)

/-- The native fused route updates a private accumulator, consumes the whole
producer, and publishes only after an exhaustion boundary. The supplied step
is a total pure operation in the admitted fragment. -/
def privateFold (consume : Accumulator → Item → Accumulator) :
    Accumulator → List (Event Item Error) → Except Error Accumulator
  | initial, [] => .ok initial
  | _, .raise error :: _ => .error error
  | initial, .answer item :: rest => privateFold consume (consume initial item) rest

theorem privateFold_agrees_he (consume : Accumulator → Item → Accumulator)
    (events : List (Event Item Error)) (initial : Accumulator) :
    privateFold consume initial events = heMaterializedFold consume initial events := by
  induction events generalizing initial with
  | nil => rfl
  | cons event rest ih =>
      cases event with
      | raise error => rfl
      | answer item =>
          rw [privateFold, ih]
          cases found : atomicResult rest with
          | error error => simp [heMaterializedFold, atomicResult, found, Except.map]
          | ok items => simp [heMaterializedFold, atomicResult, found, Except.map]

theorem privateFold_agrees_petta (consume : Accumulator → Item → Accumulator)
    (events : List (Event Item Error)) (initial : Accumulator) :
    privateFold consume initial events = pettaMaterializedFold consume initial events := by
  rw [privateFold_agrees_he, pettaMaterializedFold, pettaCollect_eq]
  cases found : atomicResult events <;> simp [heMaterializedFold, Except.map, found]

/-- Updating privately is not short-circuiting. A fault after any successful
prefix remains a fault of the whole atomic operation. -/
theorem late_fault_is_retained (consume : Accumulator → Item → Accumulator)
    (items : List Item) (initial : Accumulator) (error : Error) :
    privateFold consume initial (items.map Event.answer ++ [.raise error]) = .error error := by
  induction items generalizing initial with
  | nil => rfl
  | cons item rest ih => simpa [privateFold] using ih (consume initial item)

/-- The completed common boundary and both independent materializing routes
agree for every finite pure occurrence list, with an explicit administrative
request count. This is separate from authored firing/fuel accounting. -/
theorem boundary_dialect_agreement (consume : Accumulator → Item → Accumulator)
    (items : List Item) (initial : Accumulator) :
    Fold.OwnedSequence.sequence (fun acc item => some (consume acc item)) (items.length + 1)
      ⟨items, none, initial, 0, 0⟩ =
        (.complete, ⟨[], none, items.foldl consume initial, items.length, items.length + 1⟩) ∧
    heMaterializedFold consume initial (items.map (Event.answer (Error := Error))) =
      .ok (items.foldl consume initial) ∧
    pettaMaterializedFold consume initial (items.map (Event.answer (Error := Error))) =
      .ok (items.foldl consume initial) := by
  constructor
  · simpa using Fold.OwnedSequence.complete_exact consume items initial 0 0
  · have run : privateFold consume initial (items.map (Event.answer (Error := Error))) =
        .ok (items.foldl consume initial) := by
      induction items generalizing initial with
      | nil => rfl
      | cons item rest ih => simpa [privateFold] using ih (consume initial item)
    exact ⟨(privateFold_agrees_he consume _ initial).symm.trans run,
      (privateFold_agrees_petta consume _ initial).symm.trans run⟩

/-- Direct composition retains the current payload and accumulator instead
of copying every occurrence into an intermediate result container. The producer
frontier and owner metadata must be added separately to this account. -/
def directWorkingPeak (itemBytes : Item → Nat) (accumulatorBytes : Nat)
    (items : List Item) : Nat :=
  transientPeak itemBytes items + accumulatorBytes

theorem direct_working_bound (itemBytes : Item → Nat) (items : List Item)
    (itemLimit accumulatorBytes accumulatorLimit : Nat)
    (itemBound : ∀ item ∈ items, itemBytes item ≤ itemLimit)
    (accumulatorBound : accumulatorBytes ≤ accumulatorLimit) :
    directWorkingPeak itemBytes accumulatorBytes items ≤ itemLimit + accumulatorLimit := by
  exact Nat.add_le_add (transientPeak_le itemBytes items itemLimit itemBound) accumulatorBound

/-- At fixed item size, the materialization receipt grows with occurrences;
the direct working bound does not. Both quantities count bytes, not time. -/
theorem avoided_materialization (count itemSize accumulatorSize : Nat) :
    publicationBytes (fun _ : Unit => itemSize) (List.replicate count ()) = count * itemSize ∧
    directWorkingPeak (fun _ : Unit => itemSize) accumulatorSize (List.replicate count ()) ≤
      itemSize + accumulatorSize := by
  constructor
  · simp [publicationBytes]
  · exact direct_working_bound _ _ _ _ _ (by intros; exact Nat.le_refl _) (Nat.le_refl _)

namespace Controls

theorem duplicate_and_late_fault :
    privateFold (fun n item : Nat => n + item) 0
      ([.answer 3, .answer 3] : List (Event Nat String)) = .ok 6 ∧
    privateFold (fun n item : Nat => n + item) 0
      ([.answer 3, .answer 3, .raise "late"] : List (Event Nat String)) = .error "late" :=
  by decide

end Controls

end Composition

namespace Controls

theorem duplicate_publication_is_charged_twice :
    (advance (Sequence.tails Nat) (Fold.client (· + ·))
      (publicationCharge (fun _ => 8)) 2
      (Fold.start _ (· + ·) [7, 7, 9] 0)).1 = 16 := rfl

theorem once_does_not_charge_unrequested_output :
    (advance (Sequence.tails Nat) (Fold.client (· + ·))
      (publicationCharge id) 1
      (Fold.start _ (· + ·) [1, 1000000] 0)).1 = 1 := rfl

theorem result_retention_exceeds_transient_payload :
    transientPeak (fun _ : Unit => 1) [(), (), ()] = 1 ∧
      publicationBytes (fun _ : Unit => 1) [(), (), ()] = 3 := by
  constructor <;> rfl

end Controls

end Mettapedia.Machines.Cursor.PublicationCost
