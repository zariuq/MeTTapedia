import Mettapedia.Machines.Cursor.StampedSnapshots
import Mettapedia.Languages.MeTTa.PeTTa.LibTransform

/-!
# Historical query reads and current firing dependencies

A retained query enumerates its entry view even when a caller removes a
later row between answers. A current catalyst instead requires that row to
remain present at admission. These are different promises, not two
implementations of one unconditional read law. Negative queries and current
absence guards have the analogous distinction.

Both profiles use the same stable occurrence store. Historical offers can
feed checked linear consumption, but an offer alone is not permission to
consume it. The direct publication function below takes already established
readiness; its checked wrapper does not mandate a second matching pass.

This sequential logical model does not select a surface-language profile or
prove a native synchronization, memory-lifetime or compiler correspondence.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor.ReadAdmissionProfiles

open Mettapedia.Languages.MeTTa.PeTTa.LibTransform (Trace Search)
open StampedSnapshots (Store Row Reader)

variable {Value Answer : Type}

abbrev Offer (Value : Type) := Nat × Value

def offers (store : Store Value) (reader : Reader) : List (Offer Value) :=
  (StampedSnapshots.snapshot store reader).filterMap id

def current (store : Store Value) (occurrence : Nat) : Option (Offer Value) :=
  StampedSnapshots.atTime store store.clock occurrence

def captured (entry : List (Offer Value)) : Search (Store Value) (Offer Value) :=
  Search.superpose entry

variable [DecidableEq Value]

/-- Current admission uses the retained occurrence and value, without
rerunning the source matcher or the code that supplied its bindings. -/
def kept : List (Offer Value) → Search (Store Value) (Offer Value)
  | [], store => .done store
  | offered :: rest, store =>
      if current store offered.1 = some offered then
        .answer offered store (kept rest)
      else kept rest store

/-- Publication itself accepts earned readiness. The proof argument is
erased; the operation is the actual stable-slot retirement. -/
def publishTake (store : Store Value) (offered : Offer Value)
    (_ready : current store offered.1 = some offered) : Store Value :=
  StampedSnapshots.remove store offered.1

def taken : List (Offer Value) → Search (Store Value) (Offer Value)
  | [], store => .done store
  | offered :: rest, store =>
      if ready : current store offered.1 = some offered then
        .answer offered (publishTake store offered ready) (taken rest)
      else taken rest store

theorem take_under_ready (offered : Offer Value) (rest : List (Offer Value))
    (store : Store Value) (ready : current store offered.1 = some offered) :
    taken (offered :: rest) store =
      .answer offered (StampedSnapshots.remove store offered.1) (taken rest) := by
  simp [taken, ready, publishTake]

/-- Every first admitted take was enabled in its actual pre-state. Skipping
invalid historical offers has no intervening mutation. -/
theorem take_first_sound (entry : List (Offer Value)) (store : Store Value)
    (offered : Offer Value) (after : Store Value)
    (first : (taken entry store).first? = some (offered, after)) :
    current store offered.1 = some offered ∧
      after = StampedSnapshots.remove store offered.1 := by
  induction entry with
  | nil => simp [taken, Trace.first?] at first
  | cons candidate rest ih =>
      by_cases ready : current store candidate.1 = some candidate
      · simp only [taken, dif_pos ready, Trace.first?, Option.some.injEq, Prod.mk.injEq] at first
        rcases first with ⟨rfl, rfl⟩
        exact ⟨ready, rfl⟩
      · simp only [taken, dif_neg ready] at first
        exact ih first

omit [DecidableEq Value] in
theorem offers_remove (store : Store Value) (reader : Reader) (occurrence : Nat)
    (admissible : StampedSnapshots.Admissible store reader) :
    offers (StampedSnapshots.remove store occurrence) reader = offers store reader := by
  simp only [offers, StampedSnapshots.snapshot_remove store occurrence reader admissible]

omit [DecidableEq Value] in
theorem offers_add (store : Store Value) (reader : Reader) (value : Value)
    (admissible : StampedSnapshots.Admissible store reader) :
    offers (StampedSnapshots.add store value) reader = offers store reader := by
  simp only [offers, StampedSnapshots.snapshot_add store value reader admissible]

omit [DecidableEq Value] in
/-- A local stable-slot frame condition is enough. An unrelated removal
may advance the store clock without invalidating this live catalyst. -/
theorem current_remove_other (store : Store Value) (occurrence retired : Nat)
    (row : Row Value) (found : store.row occurrence = some row)
    (born : row.born ≤ store.clock) (alive : row.death = none)
    (distinct : occurrence ≠ retired) :
    current (StampedSnapshots.remove store retired) occurrence = some (occurrence, row.value) := by
  have slot : (StampedSnapshots.remove store retired).row occurrence = store.row occurrence := by
    unfold StampedSnapshots.remove
    split
    · rfl
    · split
      · rfl
      · exact Function.update_of_ne distinct _ _
  have age : row.born ≤ (StampedSnapshots.remove store retired).clock :=
    born.trans (StampedSnapshots.remove_clock store retired)
  simp [current, StampedSnapshots.atTime, slot, found, StampedSnapshots.visible, alive, age]

def absent (predicate : Value → Bool) (rows : List (Offer Value)) : Bool :=
  !(rows.any fun row => predicate row.2)

def currentAbsent (predicate : Value → Bool) (store : Store Value) : Bool :=
  absent predicate (offers store (StampedSnapshots.start store))

def testAbsence (entry : List (Offer Value)) (predicate : Value → Bool)
    (useEntry : Bool) (value : Answer) : Search (Store Value) Answer := fun store =>
  if (if useEntry then absent predicate entry else currentAbsent predicate store) then
    .answer value store .done
  else .done store

namespace Controls

def entry : Store Nat := StampedSnapshots.add (StampedSnapshots.add StampedSnapshots.empty 10) 20

def entryRows : List (Offer Nat) := offers entry (StampedSnapshots.start entry)

/-- The caller changes the store only after observing the first answer. -/
def removeFuture (offered : Offer Nat) : Search (Store Nat) Nat := fun store =>
  .answer offered.2 (if offered.1 = 0 then StampedSnapshots.remove store 1 else store) .done

theorem historical_query_keeps_removed_future_row :
    ((captured entryRows).bind removeFuture entry).drain.1 = [10, 20] := by decide

theorem current_catalyst_refuses_removed_future_row :
    ((kept entryRows).bind removeFuture entry).drain.1 = [10] := by decide

/-- Even with identical candidate discovery, one adaptive observation
separates the two contracts. An implementation cannot preserve both traces
under one unqualified read rule. -/
theorem no_single_observation_preserves_both (observed : List Nat) :
    ¬ (observed = ((captured entryRows).bind removeFuture entry).drain.1 ∧
      observed = ((kept entryRows).bind removeFuture entry).drain.1) := by
  rw [historical_query_keeps_removed_future_row, current_catalyst_refuses_removed_future_row]
  intro incompatible
  exact (by decide : ([10, 20] : List Nat) ≠ [10])
    (incompatible.1.symm.trans incompatible.2)

def uncheckedTake : List (Offer Nat) → Search (Store Nat) (Offer Nat)
  | [], store => .done store
  | offered :: rest, store =>
      .answer offered (StampedSnapshots.remove store offered.1) (uncheckedTake rest)

theorem historical_offer_is_not_take_readiness :
    (taken [(0, 10), (0, 10)] entry).drain.1 = [(0, 10)] ∧
      (uncheckedTake [(0, 10), (0, 10)] entry).drain.1 = [(0, 10), (0, 10)] := by decide

theorem equal_payloads_at_distinct_occurrences_both_consume :
    (taken [(0, 10), (1, 10)]
      (StampedSnapshots.add (StampedSnapshots.add StampedSnapshots.empty 10) 10)).drain.1 =
      [(0, 10), (1, 10)] := by decide

def negativeSource (useEntry : Bool) : Search (Store Nat) Nat :=
  (Search.superpose [0, 1]).bind (testAbsence [] (fun value => value == 99) useEntry)

def addAfterFirst (value : Nat) : Search (Store Nat) Nat := fun store =>
  .answer value (if value = 0 then StampedSnapshots.add store 99 else store) .done

theorem historical_absence_is_not_current_absence :
    ((negativeSource true).bind addAfterFirst StampedSnapshots.empty).drain.1 = [0, 1] ∧
      ((negativeSource false).bind addAfterFirst StampedSnapshots.empty).drain.1 = [0] := by decide

theorem unrelated_removal_does_not_invalidate_catalyst :
    current (StampedSnapshots.remove entry 0) 1 = some (1, 20) := by decide

theorem catalyst_read_alone_does_not_consume :
    (kept [(0, 10), (0, 10)] entry).drain.1 = [(0, 10), (0, 10)] ∧
      current (kept [(0, 10), (0, 10)] entry).drain.2 0 = some (0, 10) := by decide

end Controls

namespace LibraryControls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa.LibTransform

def pattern : Atom := .expression [.symbol "p", .var "x"]
def fact (value : String) : Atom := .expression [.symbol "p", .symbol value]
def original : List Atom := [fact "a", fact "b"]

def libraryQuery : Search (List Atom) Atom :=
  transform (readSources [pattern] none) (.var "x")

/-- A single match opens its logical read view once. Its returned bindings
are retained while the caller processes each result. -/
def entryMatch : Search (List Atom) Atom := fun store =>
  Search.superpose (matchAnswers store [pattern] (.var "x")) store

def removeNext (value : Atom) : Search (List Atom) Atom := fun store =>
  .answer value (store.filter fun row => row != fact "b") .done

theorem stable_readonly_library_law_holds :
    (libraryQuery original).drain = ([.symbol "a", .symbol "b"], original) ∧
      (entryMatch original).drain = ([.symbol "a", .symbol "b"], original) := by decide

/-- The existing library theorem concerns a stable drain. Its actual
guided firing rechecks the later read after the caller changes the store. -/
theorem library_stable_law_is_not_adaptive_equivalence :
    (libraryQuery.bind removeNext original).drain.1 = [.symbol "a"] ∧
      (entryMatch.bind removeNext original).drain.1 = [.symbol "a", .symbol "b"] := by decide

def negativeQuery : Search (List Atom) Atom :=
  transform ⟨[.pat .read pattern, .absent (.one (.symbol "blocked"))], [], none⟩ (.var "x")

def blockNext (value : Atom) : Search (List Atom) Atom := fun store =>
  .answer value (store ++ [.symbol "blocked"]) .done

theorem library_absence_is_rechecked_after_caller_effect :
    (negativeQuery.bind blockNext original).drain.1 = [.symbol "a"] := by decide

end LibraryControls

end Mettapedia.Machines.Cursor.ReadAdmissionProfiles
