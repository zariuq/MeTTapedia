import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.ConditionTransport

/-!
# Finite preconditions for sequential occurrence commits

Exact queries, required occurrences and excluded occurrences are closed under
backward transport through an enabled commit. The result is finite inspectable
data, with the fixed impossible cases recorded by a Boolean. It does not retain
a callback that simply runs the original sequence.

Occurrence exclusion is needed even when all final writes cancel: creating and
then consuming an occurrence still requires its initial absence. Labels alone
cannot in general express that exclusion.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

universe u v

variable {O : Type u} [DecidableEq O] {R : Type v}

/-- A finite conjunction of the existing commit checks. `possible` records
checks independent of the initial store, including incompatible overlaps. -/
structure CommitPrecondition (O : Type u) (R : Type v) where
  present : Finset O
  absent : Finset O
  queries : List (PredicateQuery O R)
  possible : Bool

namespace CommitPrecondition

def Holds (p : CommitPrecondition O R) (label : O → R) (store : Finset O) : Prop :=
  p.possible = true ∧ p.present ⊆ store ∧ Disjoint p.absent store ∧
    ∀ q ∈ p.queries, q.Holds label store

instance (p : CommitPrecondition O R) (label : O → R) (store : Finset O) :
    Decidable (p.Holds label store) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-- The actual finite enabling tests of one existing commit. -/
def ofCommit (c : Commit O R) : CommitPrecondition O R where
  present := c.taken ∪ c.kept
  absent := c.made
  queries := c.queries
  possible := decide (Disjoint c.taken c.kept)

theorem ofCommit_holds_iff (c : Commit O R) (label : O → R) (store : Finset O) :
    (ofCommit c).Holds label store ↔ Enabled label store c := by
  simp only [Holds, ofCommit, decide_eq_true_eq, Finset.union_subset_iff]
  exact ⟨fun ⟨apart, ⟨taken, kept⟩, fresh, queries⟩ => ⟨taken, kept, apart, fresh, queries⟩,
    fun h => ⟨h.apart, ⟨h.taken_subset, h.kept_subset⟩, h.fresh, h.queries_hold⟩⟩

/-- Conjunction retains query positions, even for repeated identical queries. -/
def and (p q : CommitPrecondition O R) : CommitPrecondition O R where
  present := p.present ∪ q.present
  absent := p.absent ∪ q.absent
  queries := p.queries ++ q.queries
  possible := p.possible && q.possible

theorem and_holds_iff (p q : CommitPrecondition O R) (label : O → R) (store : Finset O) :
    (p.and q).Holds label store ↔ p.Holds label store ∧ q.Holds label store := by
  simp only [Holds, and, Bool.and_eq_true, Finset.union_subset_iff,
    Finset.disjoint_union_left, List.mem_append, or_imp, forall_and]
  tauto

/-- Compile a postcondition into initial occurrence tests and transported queries. -/
def before (p : CommitPrecondition O R) (label : O → R) (c : Commit O R) :
    CommitPrecondition O R where
  present := p.present \ c.made
  absent := p.absent \ c.taken
  queries := p.queries.map fun q => q.pullback label c
  possible := p.possible && decide (Disjoint (p.present \ c.made) c.taken) &&
    decide (Disjoint p.absent c.made) && decide (∀ q ∈ p.queries, q.Compatible label c)

/-- The finite construction is exactly the preimage of the postcondition. -/
theorem before_holds_iff (p : CommitPrecondition O R) {label : O → R}
    {store : Finset O} {c : Commit O R} (enabled : Enabled label store c) :
    (p.before label c).Holds label store ↔ p.Holds label (fire store c) := by
  simp only [Holds, before, Bool.and_eq_true, decide_eq_true_eq,
    subset_fire_iff, disjoint_fire_iff, queries_hold_fire_iff _ enabled]
  tauto

/-- Initial tests for two ordered applications, without storing or replaying
their execution history. Overlap identities remain in the component sets. -/
def sequential (label : O → R) (first second : Commit O R) : CommitPrecondition O R :=
  (ofCommit first).and ((ofCommit second).before label first)

theorem sequential_holds_iff (label : O → R) (first second : Commit O R) (store : Finset O) :
    (sequential label first second).Holds label store ↔
      Enabled label store first ∧ Enabled label (fire store first) second := by
  rw [sequential, and_holds_iff, ofCommit_holds_iff]
  constructor
  · rintro ⟨enabled, later⟩
    exact ⟨enabled, (ofCommit_holds_iff second label _).mp
      ((before_holds_iff (ofCommit second) enabled).mp later)⟩
  · rintro ⟨enabled, later⟩
    exact ⟨enabled, (before_holds_iff (ofCommit second) enabled).mpr
      ((ofCommit_holds_iff second label _).mpr later)⟩

/-- Transport distributes over conjunction at every admitted initial store. -/
theorem before_and_holds_iff (p q : CommitPrecondition O R) {label : O → R}
    {store : Finset O} {c : Commit O R} (enabled : Enabled label store c) :
    ((p.and q).before label c).Holds label store ↔
      ((p.before label c).and (q.before label c)).Holds label store := by
  rw [before_holds_iff _ enabled, and_holds_iff, and_holds_iff,
    before_holds_iff _ enabled, before_holds_iff _ enabled]

/-- Iterated transport retains the exact postcondition of two updates. -/
theorem before_before_holds_iff (p : CommitPrecondition O R) {label : O → R}
    {store : Finset O} {first second : Commit O R}
    (one : Enabled label store first) (two : Enabled label (fire store first) second) :
    ((p.before label second).before label first).Holds label store ↔
      p.Holds label (fire (fire store first) second) := by
  rw [before_holds_iff _ one, before_holds_iff _ two]

end CommitPrecondition

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
