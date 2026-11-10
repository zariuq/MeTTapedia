import Mettapedia.Machines.Cursor.QueryLowerBound

/-!
# Query lower bounds relative to precomputed encodings

A program may start with auxiliary information about the input. The encoding
class studied here consists of functions depending only on a declared finite
set of input locations. The program can then query the opaque input adaptively
using the existing cursor protocol. Correctness is quantified over all inputs;
the claim concerns completed runs and allows other runs to suspend or diverge.

Every requested output location outside the encoding footprint must actually
be queried. Hence requested length is bounded by footprint cardinality plus
new query count. This is a lower bound for this encoding/interface class, not
for all ways of representing a sequence. A prepared-prefix client and an
explicit preprocessing read show why a zero-query online phase is compatible
with the fresh-input lower bound. Footprint cardinality is not a claim about
the encoding's size, preprocessing time, CPU instructions, or wall time.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.OperatorChoice.EncodedQueryBounds

open Mettapedia.Machines.Cursor
open Mettapedia.Machines.Cursor.QueryLowerBound

variable {Encoding : Type}

/-- The comparison class excludes information about locations outside the
declared footprint. Encodings may otherwise compress or reorganize it freely. -/
def LocalEncoding (known : Finset Nat) (encode : (Nat → Bool) → Encoding) : Prop :=
  ∀ before after, (∀ address ∈ known, before address = after address) →
    encode before = encode after

/-- The initial control can depend on the encoding, but cannot inspect the
opaque input by any other channel before the cursor starts. -/
def CorrectEncoded (program : Program) (start : Encoding → program.V () ())
    (encode : (Nat → Bool) → Encoding) (count : Nat) : Prop :=
  ∀ memory fuel value,
    (execute program fuel (start (encode memory)) (initial memory)).2.2 = .inr value →
      value = inputPrefix memory count

/-- The adversary can flip any unread, unencoded bit without changing either
the initial control or the ensuing adaptive execution. -/
theorem unencoded_output_position_was_read
    (program : Program) (start : Encoding → program.V () ())
    (encode : (Nat → Bool) → Encoding) (known : Finset Nat)
    (locality : LocalEncoding known encode) (count : Nat)
    (correct : CorrectEncoded program start encode count)
    (memory : Nat → Bool) (fuel : Nat) (value : List Bool)
    (finished : (execute program fuel (start (encode memory)) (initial memory)).2.2 =
      .inr value) {hidden : Nat} (within : hidden < count) (unknown : hidden ∉ known) :
    hidden ∈ (execute program fuel (start (encode memory)) (initial memory)).2.1 := by
  by_contra unread
  let alternative := Function.update memory hidden (!(memory hidden))
  have sameEncoding : encode alternative = encode memory := by
    apply locality
    intro address member
    have different : address ≠ hidden := by
      intro same
      exact unknown (same ▸ member)
    simp [alternative, different]
  have same := unread_congruence program fuel (start (encode memory))
    memory alternative ∅ hidden
    (by intro address different; simp [alternative, different]) unread
  have otherFinished :
      (execute program fuel (start (encode alternative)) (initial alternative)).2.2 =
        .inr value := by
    rw [sameEncoding]
    change (execute program fuel (start (encode memory)) ⟨alternative, ∅⟩).2.2 = _
    rw [same]
    exact finished
  have first := correct memory fuel value finished
  have other := correct alternative fuel value otherFinished
  exact flip_changes_prefix memory within (other.symm.trans first)

/-- The sharper form counts only requested positions outside the encoding's
footprint, ignoring unrelated positions that the encoding may also contain. -/
theorem unencoded_positions_query_lower_bound
    (program : Program) (start : Encoding → program.V () ())
    (encode : (Nat → Bool) → Encoding) (known : Finset Nat)
    (locality : LocalEncoding known encode) (count : Nat)
    (correct : CorrectEncoded program start encode count)
    (memory : Nat → Bool) (fuel : Nat) (value : List Bool)
    (finished : (execute program fuel (start (encode memory)) (initial memory)).2.2 =
      .inr value) :
    (Finset.range count \ known).card ≤
      (execute program fuel (start (encode memory)) (initial memory)).1 := by
  have covered : Finset.range count \ known ⊆
      (execute program fuel (start (encode memory)) (initial memory)).2.1 := by
    intro address member
    obtain ⟨within, unknown⟩ := Finset.mem_sdiff.mp member
    exact unencoded_output_position_was_read program start encode known locality count correct
      memory fuel value finished (Finset.mem_range.mp within) unknown
  have locations := Finset.card_le_card covered
  have queries := distinct_reads_le_work program fuel (start (encode memory)) (initial memory)
  simp only [initial, Finset.card_empty, Nat.zero_add] at locations queries ⊢
  exact locations.trans queries

/-- Every correct completed implementation in the stated class obeys the
footprint-plus-query bound. The program, encoding and actual input are arbitrary. -/
theorem encoded_prefix_query_lower_bound
    (program : Program) (start : Encoding → program.V () ())
    (encode : (Nat → Bool) → Encoding) (known : Finset Nat)
    (locality : LocalEncoding known encode) (count : Nat)
    (correct : CorrectEncoded program start encode count)
    (memory : Nat → Bool) (fuel : Nat) (value : List Bool)
    (finished : (execute program fuel (start (encode memory)) (initial memory)).2.2 =
      .inr value) :
    count ≤ known.card +
      (execute program fuel (start (encode memory)) (initial memory)).1 := by
  have covered : Finset.range count ⊆ known ∪
      (execute program fuel (start (encode memory)) (initial memory)).2.1 := by
    intro address member
    by_cases recorded : address ∈ known
    · exact Finset.mem_union.mpr (Or.inl recorded)
    · exact Finset.mem_union.mpr (Or.inr
        (unencoded_output_position_was_read program start encode known locality count correct
          memory fuel value finished (Finset.mem_range.mp member) recorded))
  have locations := Finset.card_le_card covered
  have unionBound := Finset.card_union_le known
    (execute program fuel (start (encode memory)) (initial memory)).2.1
  have queryBound := distinct_reads_le_work program fuel (start (encode memory)) (initial memory)
  simp only [Finset.card_range] at locations
  simp only [initial, Finset.card_empty, Nat.zero_add] at queryBound locations unionBound ⊢
  omega

theorem prefix_encoding_local (count : Nat) :
    LocalEncoding (Finset.range count) (fun memory => inputPrefix memory count) := by
  intro before after agree
  apply List.map_congr_left
  intro address member
  exact agree address (Finset.mem_range.mpr (List.mem_range.mp member))

/-- Retain a previously read prefix and query just the remaining locations.
The implementation is the existing independently implemented cursor reader. -/
def cachedStart (count : Nat) (cached : List Bool) : reader.V () () :=
  ((List.range count).drop cached.length, cached.reverse)

private theorem prefix_append_remaining (memory : Nat → Bool) (known count : Nat)
    (within : known ≤ count) :
    inputPrefix memory known ++ ((List.range count).drop known).map memory =
      inputPrefix memory count := by
  have split := congrArg (List.map memory) (List.take_append_drop known (List.range count))
  simpa [inputPrefix, List.map_append, List.take_range, Nat.min_eq_left within] using split

theorem cached_reader_correct (known count : Nat) (within : known ≤ count) :
    CorrectEncoded reader (cachedStart count) (fun memory => inputPrefix memory known) count := by
  intro memory fuel value finished
  have result := reader_partial fuel
    ((List.range count).drop (inputPrefix memory known).length)
    (inputPrefix memory known).reverse memory ∅ value finished
  simp only [List.reverse_reverse, inputPrefix, List.length_map, List.length_range] at result
  exact result.trans (prefix_append_remaining memory known count within)

/-- The bound is attained for every intermediate prefix size, not only for
empty input knowledge or a fully prepared result. -/
theorem cached_reader_exact (memory : Nat → Bool) (known count : Nat) (within : known ≤ count) :
    execute reader (count - known + 1) (cachedStart count (inputPrefix memory known))
      (initial memory) =
      (count - known, (((List.range count).drop known).toFinset,
        .inr (inputPrefix memory count))) := by
  have completed := reader_complete ((List.range count).drop known)
    (inputPrefix memory known).reverse memory ∅
  rw [List.reverse_reverse, prefix_append_remaining memory known count within] at completed
  simpa [cachedStart, inputPrefix, initial, List.length_drop] using completed

/-- Retaining the first `known` values attains the least possible number of
new queries among all encodings local to those locations. A richer interface
or an encoding carrying information about other locations is outside this class. -/
theorem cached_reader_is_query_optimal
    (program : Program) (start : Encoding → program.V () ())
    (encode : (Nat → Bool) → Encoding) (known count : Nat) (within : known ≤ count)
    (locality : LocalEncoding (Finset.range known) encode)
    (correct : CorrectEncoded program start encode count)
    (memory : Nat → Bool) (fuel : Nat) (value : List Bool)
    (finished : (execute program fuel (start (encode memory)) (initial memory)).2.2 =
      .inr value) :
    (execute reader (count - known + 1) (cachedStart count (inputPrefix memory known))
      (initial memory)).1 ≤
        (execute program fuel (start (encode memory)) (initial memory)).1 := by
  rw [cached_reader_exact memory known count within]
  have lower := encoded_prefix_query_lower_bound program start encode (Finset.range known)
    locality count correct memory fuel value finished
  simp only [Finset.card_range] at lower
  omega

open CategoryTheory

/-- A prepared-prefix consumer returns the retained list; its evaluator still
uses the same cursor semantics and charges every query it actually performs. -/
def prepared : Program where
  V _ _ := List Bool
  str := fun _ _ => ↾(fun values =>
    ⟨.inl values, fun impossible => nomatch impossible⟩)

theorem prepared_exact (values : List Bool) (memory : Nat → Bool) :
    execute prepared 1 values (initial memory) = (0, (∅, .inr values)) := rfl

theorem prepared_correct (count : Nat) :
    CorrectEncoded prepared id (fun memory => inputPrefix memory count) count := by
  intro memory fuel value finished
  cases fuel with
  | zero => simp [execute, advance, observe] at finished
  | succ fuel =>
      change Sum.inr (inputPrefix memory count) = Sum.inr value at finished
      exact (Sum.inr.inj finished).symm

/-- A nonempty full prefix can take zero new queries after preparation. This
does not refute the fresh-input theorem: the encoding footprint is nonempty. -/
theorem prepared_avoids_new_queries (memory : Nat → Bool) (count : Nat) :
    LocalEncoding (Finset.range count) (fun input => inputPrefix input count) ∧
      CorrectEncoded prepared id (fun input => inputPrefix input count) count ∧
      execute prepared 1 (inputPrefix memory count) (initial memory) =
        (0, (∅, .inr (inputPrefix memory count))) :=
  ⟨prefix_encoding_local count, prepared_correct count, prepared_exact _ _⟩

/-- The footprint cannot be erased from the theorem merely because the online
phase is cheap. Even the one-bit prefix is not an empty-footprint encoding. -/
theorem nonempty_prefix_not_empty_local {count : Nat} (positive : 0 < count) :
    ¬ LocalEncoding ∅ (fun memory => inputPrefix memory count) := by
  intro locality
  have same := locality (Function.update (fun _ => false) 0 true) (fun _ => false)
    (by intro address member; simp at member)
  exact flip_changes_prefix (fun _ => false) positive same

/-- Preparation is an actual execution of the independent reader. Combining
it with the prepared consumer costs `count` queries once and zero new queries
for a later read of this unchanged prepared prefix. -/
theorem prepare_then_consume (memory : Nat → Bool) (count : Nat) :
    execute reader (count + 1) (startReader count) (initial memory) =
      (count, (Finset.range count, .inr (inputPrefix memory count))) ∧
    execute prepared 1 (inputPrefix memory count) (initial memory) =
      (0, (∅, .inr (inputPrefix memory count))) :=
  ⟨reader_exact memory count, prepared_exact _ _⟩

/-- Relevant-location agreement is sufficient for reusing a prepared prefix;
unrelated input changes need not invalidate it. -/
theorem prepared_reuse_of_agreement (before after : Nat → Bool) (count : Nat)
    (stable : ∀ address < count, before address = after address) :
    execute prepared 1 (inputPrefix before count) (initial after) =
      (0, (∅, .inr (inputPrefix after count))) := by
  have same := prefix_encoding_local count before after
    (fun address member => stable address (Finset.mem_range.mp member))
  dsimp only at same
  rw [prepared_exact]
  rw [same]

/-- Reusing a prepared prefix after an untracked relevant mutation changes
the required answer. Correct preprocessing is not a stability proof. -/
theorem stale_preparation_is_wrong :
    (execute prepared 1 (inputPrefix (fun _ => false) 1)
      (initial (Function.update (fun _ => false) 0 true))).2.2 ≠
        .inr (inputPrefix (Function.update (fun _ => false) 0 true) 1) := by
  change (Sum.inr [false] : List Bool ⊕ List Bool) ≠ .inr [true]
  decide

end Mettapedia.Machines.OperatorChoice.EncodedQueryBounds
