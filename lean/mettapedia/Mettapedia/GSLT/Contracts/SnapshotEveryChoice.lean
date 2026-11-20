import Mettapedia.GSLT.Contracts.GreedyMaximalSelection
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Waves

/-!
# Direct maximal selection in the same-cut every profile

EveryEnabled is hereditary on the original candidate occurrences,
even with predicate queries: each query and compatibility check is
about one fixed pre-state. This connects the generic greedy licence
to the actual occurrence-wave semantics. It does not apply to a
semantics that reruns admission after each chosen edit.

Candidate identities are separate from the commits they describe.
The input word declares the order on decisions. It says nothing
about how a different explorer orders the resulting states.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Contracts.SnapshotEveryChoice

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open Mettapedia.GSLT.Contracts.GreedyMaximalSelection

variable {Occurrence Row Id : Type*} [DecidableEq Occurrence] [DecidableEq Id]

omit [DecidableEq Id] in
theorem every_of_sublist {label : Occurrence → Row} {store : Finset Occurrence}
    {small large : List (Commit Occurrence Row)} (sub : small.Sublist large)
    (allowed : EveryEnabled label store large) : EveryEnabled label store small := by
  obtain ⟨enabled, clashes, kept⟩ := everyEnabled_iff.mp allowed
  exact everyEnabled_iff.mpr ⟨fun c member => enabled c (sub.subset member),
    clashes.sublist sub, fun a ma b mb => kept a (sub.subset ma) b (sub.subset mb)⟩

def batch (describe : Id → Commit Occurrence Row) (word : List Id) (selection : Finset Id) :
    List (Commit Occurrence Row) :=
  (word.filter fun id => decide (id ∈ selection)).map describe

def legal (label : Occurrence → Row) (store : Finset Occurrence)
    (describe : Id → Commit Occurrence Row) (word : List Id) (selection : Finset Id) : Prop :=
  EveryEnabled label store (batch describe word selection)

private theorem sublist_of_subset (word : List Id) {small large : Finset Id} (inc : small ⊆ large) :
    (word.filter fun id => decide (id ∈ small)).Sublist (word.filter fun id => decide (id ∈ large)) := by
  induction word with
  | nil => exact .slnil
  | cons id rest ih =>
      by_cases kept : id ∈ small
      · have also := inc kept
        simp only [List.filter_cons, kept, also, decide_true]
        exact .cons_cons _ ih
      · by_cases also : id ∈ large
        · simp only [List.filter_cons, kept, also, decide_true, decide_false]
          exact .cons _ ih
        · simpa [List.filter_cons, kept, also] using ih

theorem legal_hereditary (label : Occurrence → Row) (store : Finset Occurrence)
    (describe : Id → Commit Occurrence Row) (word : List Id) :
    Hereditary (legal label store describe word) :=
  fun {_ _} inc allowed => every_of_sublist ((sublist_of_subset word inc).map describe) allowed

private instance decideClash (c d : Commit Occurrence Row) : Decidable (Clash c d) :=
  inferInstanceAs (Decidable (¬ Disjoint c.taken d.taken ∨ ¬ Disjoint c.made d.made))

instance decideLegal (label : Occurrence → Row) (store : Finset Occurrence)
    (describe : Id → Commit Occurrence Row) (word : List Id) (selection : Finset Id) :
    Decidable (legal label store describe word selection) := by
  unfold legal EveryEnabled
  infer_instance

theorem empty_legal (label : Occurrence → Row) (store : Finset Occurrence)
    (describe : Id → Commit Occurrence Row) (word : List Id) :
    legal label store describe word ∅ := by
  simp [legal, batch, everyEnabled_iff]

def select (label : Occurrence → Row) (store : Finset Occurrence)
    (describe : Id → Commit Occurrence Row) (word : List Id) : Finset Id :=
  choose (legal label store describe word) ∅ word

theorem select_every (label : Occurrence → Row) (store : Finset Occurrence)
    (describe : Id → Commit Occurrence Row) (word : List Id) :
    EveryEnabled label store (batch describe word (select label store describe word)) :=
  choose_legal _ (empty_legal label store describe word) word

theorem select_maximal (label : Occurrence → Row) (store : Finset Occurrence)
    (describe : Id → Commit Occurrence Row) (word : List Id) {other : Finset Id}
    (offered : other ⊆ word.toFinset) (admitted : EveryEnabled label store (batch describe word other))
    (includes : select label store describe word ⊆ other) :
    other = select label store describe word :=
  choose_maximal _ (legal_hereditary label store describe word) ∅ word
    (offered.trans Finset.subset_union_right) admitted includes

theorem select_preferred (label : Occurrence → Row) (store : Finset Occurrence)
    (describe : Id → Commit Occurrence Row) (word : List Id) {other : Finset Id}
    (admitted : EveryEnabled label store (batch describe word other)) :
    decisions (select label store describe word) word = decisions other word ∨
      List.Lex FirstPreference (decisions (select label store describe word) word) (decisions other word) :=
  choose_preferred _ (legal_hereditary label store describe word) word ∅
    (empty_legal label store describe word) other (Finset.empty_subset _) admitted

namespace Controls

private def competingClaims (id : Bool) : Commit Nat Unit :=
  ⟨{0}, ∅, if id then {1} else {9}, []⟩

/-- The direct choice can select the larger output if its producer
has declared priority. The reverse priority preserves admissibility
but changes the result. -/
theorem priority_is_observable :
    fire {0} (amalgamate (batch competingClaims [false, true]
      (select (fun _ => ()) {0} competingClaims [false, true]))) = {9} ∧
    fire {0} (amalgamate (batch competingClaims [true, false]
      (select (fun _ => ()) {0} competingClaims [true, false]))) = {1} := by
  decide

end Controls

#print axioms every_of_sublist
#print axioms select_maximal
#print axioms select_preferred
#print axioms Controls.priority_is_observable

end Mettapedia.GSLT.Contracts.SnapshotEveryChoice
