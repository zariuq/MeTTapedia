import Mettapedia.Machines.Cursor.Protocol
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Range

/-!
# An adversary lower bound for observing an arbitrary input prefix

The provider answers random-access Boolean queries and records which locations
were read. Clients are the existing coalgebraic cursor clients: they may choose
later queries from earlier replies and need not terminate. On a completed run,
a client correct for every input must have read every requested output position.
The proof changes one unread input bit and derives an indistinguishable run
with a different required answer.

This is a query-complexity result for fresh, opaque input with no auxiliary
summary. It does not lower-bound all computation, encoded/compressed inputs,
effectful search, or executions carrying previously acquired information.
The prefix-reading client attains the bound. Its implementation is independent
of the correctness specification, and both use the shared cursor evaluator.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor.QueryLowerBound

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.IndexedPolynomial

abbrev protocol : IndexedPolynomial Unit (fun _ => Unit) where
  Shape _ _ := Nat
  Position _ := Bool
  next _ _ := ()

structure State where
  memory : Nat → Bool
  reads : Finset Nat

def provider : Provider protocol where
  State _ _ := State
  step state address := ⟨state.memory address, { state with reads := insert address state.reads }⟩

def work : Charge provider := fun _ _ => 1

abbrev Result := fun (_ : Unit) (_ : Unit) => List Bool
abbrev Program := Client (P := protocol) (Return := Result)

def initial (memory : Nat → Bool) : State := ⟨memory, ∅⟩

/-- An observation keeps suspension distinct from return and retains the
read footprint. Only the unqueried contents of the oracle are hidden. -/
def observe (C : Program) : Outcome provider C () →
    Finset Nat × (C.V () () ⊕ List Bool)
  | .paused ⟨(), control, state⟩ => (state.reads, .inl control)
  | .done ⟨(), value, state⟩ => (state.reads, .inr value)

def execute (C : Program) (fuel : Nat) (control : C.V () ()) (state : State) :
    Nat × (Finset Nat × (C.V () () ⊕ List Bool)) :=
  let result := advance provider C work fuel ⟨(), control, state⟩
  (result.1, observe C result.2)

theorem execute_query (C : Program) (fuel : Nat) (control : C.V () ()) (state : State)
    (address : Nat) (children : Bool → C.V () ())
    (query : C.str () () control = ⟨.inr address, children⟩) :
    execute C (fuel + 1) control state =
      let next := execute C fuel (children (state.memory address))
        { state with reads := insert address state.reads }
      (1 + next.1, next.2) := by
  simp only [execute, advance, query]
  rfl

theorem reads_mono (C : Program) (fuel : Nat) (control : C.V () ()) (state : State) :
    state.reads ⊆ (execute C fuel control state).2.1 := by
  induction fuel generalizing control state with
  | zero => exact Finset.Subset.refl _
  | succ fuel ih =>
      cases eq : C.str () () control with
      | mk shape children =>
          cases shape with
          | inl value => simp [execute, advance, eq, observe]
          | inr address =>
              dsimp only [withHoles] at children
              rw [execute_query C fuel control state address children eq]
              have next := ih (children (state.memory address))
                { state with reads := insert address state.reads }
              exact (Finset.subset_insert _ _).trans next

theorem distinct_reads_le_work (C : Program) (fuel : Nat) (control : C.V () ())
    (state : State) :
    (execute C fuel control state).2.1.card ≤
      state.reads.card + (execute C fuel control state).1 := by
  induction fuel generalizing control state with
  | zero => simp [execute, advance, observe]
  | succ fuel ih =>
      cases eq : C.str () () control with
      | mk shape children =>
          cases shape with
          | inl value => simp [execute, advance, eq, observe]
          | inr address =>
              dsimp only [withHoles] at children
              have next := ih (children (state.memory address))
                { state with reads := insert address state.reads }
              have one := Finset.card_insert_le (α := Nat) address state.reads
              rw [execute_query C fuel control state address children eq]
              change (execute C fuel (children (state.memory address))
                  { state with reads := insert address state.reads }).2.1.card ≤
                state.reads.card + (1 + (execute C fuel (children (state.memory address))
                  { state with reads := insert address state.reads }).1)
              change (execute C fuel (children (state.memory address))
                  { state with reads := insert address state.reads }).2.1.card ≤
                (insert address state.reads).card +
                  (execute C fuel (children (state.memory address))
                    { state with reads := insert address state.reads }).1 at next
              omega

/-- Altering one location outside the actual read footprint preserves the
whole observed execution, including work, control and the read footprint. -/
theorem unread_congruence (C : Program) (fuel : Nat) (control : C.V () ())
    (before after : Nat → Bool) (reads : Finset Nat) (hidden : Nat)
    (agree : ∀ address, address ≠ hidden → after address = before address)
    (unread : hidden ∉ (execute C fuel control ⟨before, reads⟩).2.1) :
    execute C fuel control ⟨after, reads⟩ =
      execute C fuel control ⟨before, reads⟩ := by
  induction fuel generalizing control reads with
  | zero => rfl
  | succ fuel ih =>
      cases eq : C.str () () control with
      | mk shape children =>
          cases shape with
          | inl value => simp [execute, advance, eq, observe]
          | inr address =>
              dsimp only [withHoles] at children
              have nextUnread : hidden ∉
                  (execute C fuel (children (before address))
                    ⟨before, insert address reads⟩).2.1 := by
                simpa only [execute_query C fuel control _ address children eq] using unread
              have inserted := reads_mono C fuel (children (before address))
                ⟨before, insert address reads⟩
              have different : address ≠ hidden := by
                intro same
                exact nextUnread (inserted (Finset.mem_insert.mpr (Or.inl same.symm)))
              have reply := agree address different
              have next := ih (children (before address)) (insert address reads) nextUnread
              rw [execute_query C fuel control _ address children eq,
                execute_query C fuel control _ address children eq]
              dsimp only
              rw [reply]
              exact congrArg (fun result => (1 + result.1, result.2)) next

def inputPrefix (memory : Nat → Bool) (count : Nat) : List Bool :=
  (List.range count).map memory

/-- Partial correctness is enough. Diverging clients are allowed; the lower
bound concerns only runs which actually return a prefix. -/
def Correct (C : Program) (control : C.V () ()) (count : Nat) : Prop :=
  ∀ memory fuel value,
    (execute C fuel control (initial memory)).2.2 = .inr value →
      value = inputPrefix memory count

theorem flip_changes_prefix (memory : Nat → Bool) {count hidden : Nat}
    (within : hidden < count) :
    inputPrefix (Function.update memory hidden (!(memory hidden))) count ≠
      inputPrefix memory count := by
  intro same
  have atPosition := congrArg (fun xs : List Bool => xs[hidden]?) same
  simp [inputPrefix, within] at atPosition

theorem output_position_was_read (C : Program) (control : C.V () ()) (count : Nat)
    (correct : Correct C control count) (memory : Nat → Bool) (fuel : Nat)
    (value : List Bool)
    (finished : (execute C fuel control (initial memory)).2.2 = .inr value)
    {hidden : Nat} (within : hidden < count) :
    hidden ∈ (execute C fuel control (initial memory)).2.1 := by
  by_contra unread
  let alternative := Function.update memory hidden (!(memory hidden))
  have same := unread_congruence C fuel control memory alternative ∅ hidden
    (by intro address different; simp [alternative, different]) unread
  have otherFinished :
      (execute C fuel control (initial alternative)).2.2 = .inr value := by
    change (execute C fuel control ⟨alternative, ∅⟩).2.2 = _
    rw [same]
    exact finished
  have first := correct memory fuel value finished
  have other := correct alternative fuel value otherFinished
  exact flip_changes_prefix memory within (other.symm.trans first)

/-- Every completed correct adaptive algorithm pays at least one query per
requested position, even if the observed Boolean values contain duplicates. -/
theorem prefix_query_lower_bound (C : Program) (control : C.V () ()) (count : Nat)
    (correct : Correct C control count) (memory : Nat → Bool) (fuel : Nat)
    (value : List Bool)
    (finished : (execute C fuel control (initial memory)).2.2 = .inr value) :
    count ≤ (execute C fuel control (initial memory)).1 := by
  have subset : Finset.range count ⊆ (execute C fuel control (initial memory)).2.1 := by
    intro address member
    exact output_position_was_read C control count correct memory fuel value finished
      (Finset.mem_range.mp member)
  have countBound := Finset.card_le_card subset
  have workBound := distinct_reads_le_work C fuel control (initial memory)
  simp only [Finset.card_range] at countBound
  exact countBound.trans (by simpa only [initial, Finset.card_empty, Nat.zero_add] using workBound)

open CategoryTheory

/-- This client reads a supplied list of locations, accumulating replies in
reverse order. It does not perform a query to discover the end of that list. -/
def reader : Program where
  V _ _ := List Nat × List Bool
  str := fun _ _ => ↾(fun (locations, reverseAnswers) => match locations with
    | [] => ⟨.inl reverseAnswers.reverse, fun impossible => nomatch impossible⟩
    | address :: rest => ⟨.inr address, fun reply => (rest, reply :: reverseAnswers)⟩)

theorem reader_complete (locations : List Nat) (reverseAnswers : List Bool)
    (memory : Nat → Bool) (reads : Finset Nat) :
    execute reader (locations.length + 1) (locations, reverseAnswers) ⟨memory, reads⟩ =
      (locations.length,
        (reads ∪ locations.toFinset, .inr (reverseAnswers.reverse ++ locations.map memory))) := by
  induction locations generalizing reverseAnswers reads with
  | nil =>
      change (0, (reads, Sum.inr reverseAnswers.reverse)) =
        (0, (reads ∪ ∅, Sum.inr (reverseAnswers.reverse ++ [])))
      simp
  | cons address rest ih =>
      change (1 + (execute reader (rest.length + 1) (rest, memory address :: reverseAnswers)
          ⟨memory, insert address reads⟩).1,
        (execute reader (rest.length + 1) (rest, memory address :: reverseAnswers)
          ⟨memory, insert address reads⟩).2) = _
      rw [ih]
      simp [List.reverse_cons, List.append_assoc, Nat.add_comm, Finset.insert_union,
        Finset.union_insert]

theorem reader_partial (fuel : Nat) (locations : List Nat) (reverseAnswers : List Bool)
    (memory : Nat → Bool) (reads : Finset Nat) (value : List Bool)
    (finished : (execute reader fuel (locations, reverseAnswers) ⟨memory, reads⟩).2.2 =
      .inr value) :
    value = reverseAnswers.reverse ++ locations.map memory := by
  induction fuel generalizing locations reverseAnswers reads with
  | zero => simp [execute, advance, observe] at finished
  | succ fuel ih =>
      cases locations with
      | nil =>
          change Sum.inr reverseAnswers.reverse = Sum.inr value at finished
          simpa using (Sum.inr.inj finished).symm
      | cons address rest =>
          have next : (execute reader fuel (rest, memory address :: reverseAnswers)
              ⟨memory, insert address reads⟩).2.2 = .inr value := finished
          have result := ih rest (memory address :: reverseAnswers) (insert address reads) next
          simpa [List.reverse_cons, List.append_assoc] using result

def startReader (count : Nat) : reader.V () () := (List.range count, [])

theorem reader_correct (count : Nat) : Correct reader (startReader count) count := by
  intro memory fuel value finished
  have result := reader_partial fuel (List.range count) [] memory ∅ value finished
  simpa [inputPrefix] using result

/-- The concrete reader attains the adversary bound: exactly k oracle reads
produce the first k values, preserving their order and duplicates. -/
theorem reader_exact (memory : Nat → Bool) (count : Nat) :
    execute reader (count + 1) (startReader count) (initial memory) =
      (count, (Finset.range count, .inr (inputPrefix memory count))) := by
  have locations : (List.range count).toFinset = Finset.range count := by
    ext address
    simp
  simpa [startReader, initial, inputPrefix, locations] using
    reader_complete (List.range count) [] memory ∅

theorem reader_is_query_optimal (C : Program) (control : C.V () ()) (count : Nat)
    (correct : Correct C control count) (memory : Nat → Bool) (fuel : Nat)
    (value : List Bool)
    (finished : (execute C fuel control (initial memory)).2.2 = .inr value) :
    (execute reader (count + 1) (startReader count) (initial memory)).1 ≤
      (execute C fuel control (initial memory)).1 := by
  rw [reader_exact]
  exact prefix_query_lower_bound C control count correct memory fuel value finished

namespace Controls

theorem once_reads_no_next_location (memory : Nat → Bool) :
    execute reader 2 (startReader 1) (initial memory) =
      (1, ({0}, .inr [memory 0])) := reader_exact memory 1

theorem zero_demand_reads_nothing (memory : Nat → Bool) :
    execute reader 1 (startReader 0) (initial memory) = (0, (∅, .inr [])) :=
  reader_exact memory 0

/-- Repeated values in the actual input do not help a universally correct
opaque-input reader: an unread position might have been different. -/
theorem duplicates_still_require_queries (C : Program) (control : C.V () ())
    (count : Nat) (correct : Correct C control count) (fuel : Nat) (value : List Bool)
    (finished : (execute C fuel control (initial (fun _ => false))).2.2 = .inr value) :
    count ≤ (execute C fuel control (initial (fun _ => false))).1 :=
  prefix_query_lower_bound C control count correct (fun _ => false) fuel value finished

/-- Prior knowledge changes the comparison class. The independent constant
client answers a known all-false input without querying it. -/
def constantClient (count : Nat) : Program where
  V _ _ := Unit
  str := fun _ _ => ↾(fun _ =>
    ⟨.inl (List.replicate count false), fun impossible => nomatch impossible⟩)

theorem prior_knowledge_avoids_queries (count : Nat) :
    execute (constantClient count) 1 () (initial (fun _ => false)) =
      (0, (∅, .inr (inputPrefix (fun _ => false) count))) := by
  change (0, (∅, Sum.inr (List.replicate count false))) =
    (0, (∅, Sum.inr (inputPrefix (fun _ => false) count)))
  simp [inputPrefix]

theorem constant_client_is_not_universally_correct :
    ¬ Correct (constantClient 1) () 1 := by
  intro correct
  have wrong := correct (fun _ => true) 1 [false] rfl
  simp [inputPrefix] at wrong

end Controls

end Mettapedia.Machines.Cursor.QueryLowerBound
