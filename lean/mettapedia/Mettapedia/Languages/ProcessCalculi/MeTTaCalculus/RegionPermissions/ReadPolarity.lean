import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.InteractionTypes.Facets

/-!
# Which runs can falsify a read: the read's polarity decides

A read at a set of names `A` is a predicate of the occurrences there: `P (restrict A S)` at the
store `S`. Three shapes matter.

* **Universal reads** (`∀`, `¬∃`: absence, "every row here is like this") are downward closed
  (`OccurrenceCommits.DownwardClosed`; absence is `absence_downward_closed`): they survive removals
  and can fail by one arrival.
* **Existential reads** (a matched witness, "some row here is like this") are upward closed
  (`OccurrenceCommits.UpwardClosed`): they survive arrivals and can fail by one removal.
* **Exact reads** (counts, uniqueness, a snapshot of the region) are neither; any write can change
  them.

## What a run must not do, for each shape

* A universal read survives every run that makes nothing at `A` (`antitone_stable_of_noMake`);
  takes are harmless to it.
* An existential read survives every run that takes nothing at `A` (`monotone_stable_of_noTake`);
  makes are harmless to it.
* Any read survives a run that writes nothing at `A` (`stable_of_noWrite`). For a predicate query
  this is `OccurrenceCommits.holds_fireList_of_no_write`, and inside a scope
  `OccurrenceCommits.scope_read_stable`; the first two conditions refine it by polarity.

Each condition is necessary for some read of its shape: one make falsifies absence
(`Controls.absence_falsified_by_make`), one take falsifies the existence of a witness
(`Controls.exists_falsified_by_take`).

## What validation at commit time can check, for each shape

* **An existential read is validated by its witnesses.** If the occurrences that made it true are
  still present, it still holds (`monotone_of_witnesses_present`), whatever else arrived. A commit
  that keeps or takes its witnesses checks exactly that (`Enabled.kept_subset`,
  `Enabled.taken_subset`), so the read needs no epoch of its region and no fact about who else
  holds which right.
* **A universal read is not validated by occurrences.** Every occurrence present when it was read
  can still be present while it fails (`Controls.universal_not_validated_by_occurrences`). It needs
  the region itself: a full re-read or an epoch of the region, or a fact that guarantees no
  arrival, which is a fact about rights (`OwnedReads`, `DelegatedReads`).

So a read's quantifier polarity says what keeps it true: an existential read asks only that its
own witnesses stay, and a universal read asks that nobody else can make at its names.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.RegionPermissions

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

universe u v w

variable {O : Type u} [DecidableEq O] {R : Type v} {N : Type w}

/-! ## Stability by polarity

The writes at a set of names (`MakesOutside`, `TakesOutside`) and their frame laws
(`restrict_fireList_subset_of_makesOutside`, `restrict_subset_fireList_of_takesOutside`) are those
of `OccurrenceCommits.ChannelAddressing`, the frame law of regions read through addresses. -/

section Stability

variable {label : O → R} {loc : R → N} {A : N → Bool} {P : Finset O → Prop}

/-- **A universal read survives every run that makes nothing at its names.** -/
theorem antitone_stable_of_noMake (antitone : DownwardClosed P) {run : List (Commit O R)}
    (outside : ∀ e ∈ run, MakesOutside label loc A e) {S : Finset O}
    (holds : P (restrict label loc A S)) : P (restrict label loc A (fireList S run)) :=
  antitone (restrict_fireList_subset_of_makesOutside outside S) holds

/-- **An existential read survives every run that takes nothing at its names.** -/
theorem monotone_stable_of_noTake (monotone : UpwardClosed P) {run : List (Commit O R)}
    (outside : ∀ e ∈ run, TakesOutside label loc A e) {S : Finset O}
    (holds : P (restrict label loc A S)) : P (restrict label loc A (fireList S run)) :=
  monotone (restrict_subset_fireList_of_takesOutside outside S) holds

/-- **Any read survives a run that writes nothing at its names.** -/
theorem stable_of_noWrite {run : List (Commit O R)}
    (noMake : ∀ e ∈ run, MakesOutside label loc A e)
    (noTake : ∀ e ∈ run, TakesOutside label loc A e) (S : Finset O) :
    restrict label loc A (fireList S run) = restrict label loc A S :=
  Finset.Subset.antisymm (restrict_fireList_subset_of_makesOutside noMake S)
    (restrict_subset_fireList_of_takesOutside noTake S)

omit [DecidableEq O] in
/-- **An existential read is validated by its witnesses**: if the occurrences that made it true
are still at its names, it still holds, whatever arrived. -/
theorem monotone_of_witnesses_present (monotone : UpwardClosed P) {witnesses S : Finset O}
    (holds : P witnesses) (present : witnesses ⊆ restrict label loc A S) :
    P (restrict label loc A S) :=
  monotone present holds

omit [DecidableEq O] in
/-- A commit that keeps the witnesses of an existential read, and is enabled, sees the read
hold: keeping is the validation. -/
theorem monotone_of_kept (monotone : UpwardClosed P) {c : Commit O R} {S : Finset O}
    (enabled : Enabled label S c) (atA : ∀ o ∈ c.kept, A (loc (label o)) = true)
    (holds : P c.kept) : P (restrict label loc A S) :=
  monotone_of_witnesses_present monotone holds fun o kept =>
    mem_restrict.mpr ⟨enabled.kept_subset kept, atA o kept⟩

end Stability

/-! ## Controls -/

namespace Controls

/-- Occurrences are numbers; occurrence `n` carries label `n`, and lives at name `n % 2`. -/
def lab : ℕ → ℕ := id

/-- Even labels live at name `0`, odd ones at name `1`. -/
def place : ℕ → Bool := fun n => n % 2 == 1

/-- The read looks at name `false` (even labels). -/
def atEven : Bool → Bool := fun b => !b

/-- Absence of every occurrence at the read's names: a universal read. Of the held part, it is the
absence read of the names' region (`OccurrenceCommits.restrict_eq_empty_iff`). -/
abbrev Absent : Finset ℕ → Prop := fun B => B = ∅

/-- Some occurrence at the read's names: an existential read. -/
abbrev Witnessed : Finset ℕ → Prop := fun B => B.Nonempty

theorem absent_downward : DownwardClosed Absent := by
  intro small large sub holds
  unfold Absent at holds ⊢
  subst holds
  exact Finset.subset_empty.mp sub

theorem witnessed_upward : UpwardClosed Witnessed := by
  intro small large sub holds
  exact holds.mono sub

/-- Make occurrence `2`, at the read's names. -/
def makeTwo : Commit ℕ ℕ := ⟨∅, ∅, {2}, []⟩

/-- Take occurrence `4`. -/
def takeFour : Commit ℕ ℕ := ⟨{4}, ∅, ∅, []⟩

/-- Make occurrence `3`, outside the read's names. -/
def makeThree : Commit ℕ ℕ := ⟨∅, ∅, {3}, []⟩

/-- **One make falsifies a universal read.** The store `{1}` has nothing at the even name; after
making `2` it does. -/
theorem absence_falsified_by_make :
    Absent (restrict lab place atEven {1}) ∧
      ¬ Absent (restrict lab place atEven (fireList {1} [makeTwo])) := by
  refine ⟨by decide, ?_⟩
  unfold Absent
  decide

/-- **One take falsifies an existential read.** The store `{4}` has a witness at the even name;
taking it leaves none. -/
theorem exists_falsified_by_take :
    Witnessed (restrict lab place atEven {4}) ∧
      ¬ Witnessed (restrict lab place atEven (fireList {4} [takeFour])) := by
  refine ⟨⟨4, by decide⟩, ?_⟩
  unfold Witnessed
  decide

/-- Makes elsewhere and takes are harmless to the universal read; makes are harmless to the
existential read. -/
theorem harmless_writes :
    Absent (restrict lab place atEven (fireList {1} [makeThree])) ∧
      Witnessed (restrict lab place atEven (fireList {4} [makeTwo])) := by
  refine ⟨?_, ⟨4, by decide⟩⟩
  unfold Absent
  decide

/-- **A universal read is not validated by occurrences.** Every occurrence of the store at the
time of the read (`{1}`) is still present after the make of `2`, the read's witness set (empty)
is still present, and the read fails. -/
theorem universal_not_validated_by_occurrences :
    ({1} : Finset ℕ) ⊆ fireList {1} [makeTwo] ∧
      restrict lab place atEven ({1} : Finset ℕ) ⊆ restrict lab place atEven (fireList {1} [makeTwo]) ∧
      Absent (restrict lab place atEven {1}) ∧
      ¬ Absent (restrict lab place atEven (fireList {1} [makeTwo])) := by
  refine ⟨by decide, by decide, absence_falsified_by_make⟩

/-- **An existential read is validated by its witness**, an instance of
`monotone_of_witnesses_present`: the witness `4` is still present after the make of `2`. -/
theorem existential_validated_by_witness :
    Witnessed (restrict lab place atEven (fireList {4} [makeTwo])) :=
  monotone_of_witnesses_present witnessed_upward (witnesses := {4}) ⟨4, by decide⟩ (by decide)

end Controls

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.RegionPermissions
