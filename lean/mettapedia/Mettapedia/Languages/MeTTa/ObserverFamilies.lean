import Mettapedia.Languages.MeTTa.ObserverLattice

/-!
# A family of plain observers versus one aggregate observer

An observer that returns a tagged aggregate — values, coverage and faults
bundled into one record — is not the only way to expose more than values.
The alternative is a *family* of ordinary observers, each returning plain
data, each asked separately.

This module settles what separates the two, and the answer is not what the
earlier laundering result suggested.

**Information: nothing separates them.**  The family jointly determines the
aggregate and the aggregate determines each member
(`family_and_aggregate_equivalent`).  An aggregate buys no information that
asking three questions does not.

**Soundness: nothing separates them either, and the earlier framing was
imprecise.**  Two different failures were being run together:

* `values_cannot_report_coverage` — the values view does not *determine*
  coverage.  That is a loss of information: honest ignorance.
* `roundTrip_launders_incompleteness` (in `CollapseSuperposeRoundTrip`) — a
  *reconstruction* manufactures a coverage claim that was never observed.
  That is an invention of information: a false report.

Only the second is unsound, and it requires a reconstruction map.  A language
with no operation building an outcome from data cannot launder, however
values-only its observers are (`laundering_needs_a_reconstruction`).  So
values-only observation is not itself the hazard; round-tripping through data
is.

**What does separate them: atomicity.**  A family is equivalent to an
aggregate only when its members observe *the same run*.  Applied to separate
runs of a computation that can differ, a family reports combinations no
single run ever produced (`separate_runs_admit_impossible_combinations`).
That is a genuine constraint, and it is about sharing a run rather than about
how the answer is packaged.
-/

namespace Mettapedia.Languages.MeTTa.ObserverFamilies

open Mettapedia.Languages.MeTTa.Emptiness
open Mettapedia.Languages.MeTTa.RoundTrip
open Mettapedia.Languages.MeTTa.ObserverLattice
open Mettapedia.GSLT.Core.NonFactorization

/-! ## The two arrangements -/

/-- Asking three separate questions of one run. -/
def familyView (outcome : Outcome) : List Datum × Coverage × List String :=
  (outcome.values, outcome.coverage, outcome.faults)

/-- The aggregate: the whole outcome at once. -/
def aggregateView : Outcome → Outcome := id

/-! ## Information: the arrangements are equivalent -/

theorem family_determines_aggregate : Factors familyView aggregateView :=
  ⟨fun observed => ⟨observed.1, observed.2.1, observed.2.2⟩, fun _ => rfl⟩

theorem aggregate_determines_family : Factors aggregateView familyView :=
  ⟨familyView, fun _ => rfl⟩

/-- **An aggregate observer carries no information a family lacks.**  Each
determines the other, so packaging is not an information question. -/
theorem family_and_aggregate_equivalent :
    Factors familyView aggregateView ∧ Factors aggregateView familyView :=
  ⟨family_determines_aggregate, aggregate_determines_family⟩

/-- Each member of the family is recoverable from the family, and none of them
alone suffices — the earlier lattice results, restated for the members. -/
theorem family_members_are_needed :
    ¬ Determines valuesView coverageView ∧ ¬ Determines valuesView faultsView ∧
      ¬ Determines coverageView valuesView :=
  ⟨values_not_determines_coverage, values_not_determines_faults,
    coverage_not_determines_values⟩

/-! ## Two different failures, only one of them unsound

Losing information and inventing it are not the same defect, and only the
second threatens soundness. -/

/-- **The values view is silent about coverage, not wrong about it.**  It
fails to determine coverage, which is a limit on what may be concluded from
it — not a false claim. -/
theorem values_cannot_report_coverage : ¬ Determines valuesView coverageView :=
  values_not_determines_coverage

/-- **Laundering needs a reconstruction.**  A coverage claim can only be
manufactured by a function that builds an outcome from data.  Where the
language has no such function, no claim is manufactured, whatever its
observers return.

Stated as the exact dependency: any laundering witness is an application of
some reconstruction, so a fragment without one has no witness to exhibit. -/
theorem laundering_needs_a_reconstruction
    (reconstruct : List Datum → Outcome)
    (launders : ∃ outcome : Outcome,
      (reconstruct outcome.values).coverage ≠ outcome.coverage) :
    ∃ observed : List Datum, ∃ outcome : Outcome,
      outcome.values = observed ∧ (reconstruct observed).coverage ≠ outcome.coverage := by
  obtain ⟨outcome, differs⟩ := launders
  exact ⟨outcome.values, outcome, rfl, differs⟩

/-- The values view of a run, used *without* reconstruction, never contradicts
that run: it is a projection of it. -/
theorem values_projection_is_faithful (outcome : Outcome) :
    valuesView outcome = outcome.values := rfl

/-! ## What genuinely separates them: one run or two

A family is equivalent to an aggregate only when its members see the same
run.  Across runs the equivalence fails, and it fails by admitting reports
that no single run produced. -/

/-- Runs of one expression, indexed. -/
def RunFamily := Nat → Outcome

/-- Reading values from one run and coverage from another. -/
def acrossRuns (runs : RunFamily) (valueRun coverageRun : Nat) :
    List Datum × Coverage :=
  ((runs valueRun).values, (runs coverageRun).coverage)

/-- Two runs that disagree in both coordinates. -/
def divergentRuns : RunFamily := fun index =>
  if index = 0 then ⟨[.unit], .complete, []⟩ else ⟨[], .incomplete "budget", []⟩

/-- **Observing across runs admits combinations no run produced.**  Taking
values from the first run and coverage from the second yields a pair that is
not the values-and-coverage of either run, so a family observing separate
runs is strictly weaker than an aggregate observing one.

This is the real constraint on families, and it concerns sharing a run — not
how the result is packaged. -/
theorem separate_runs_admit_impossible_combinations :
    acrossRuns divergentRuns 0 1 ≠ ((divergentRuns 0).values, (divergentRuns 0).coverage) ∧
      acrossRuns divergentRuns 0 1 ≠
        ((divergentRuns 1).values, (divergentRuns 1).coverage) := by
  constructor <;> decide

/-- On a single run the family and the aggregate agree exactly, so the
constraint above is the only one. -/
theorem one_run_makes_family_faithful (outcome : Outcome) :
    familyView outcome = (outcome.values, outcome.coverage, outcome.faults) := rfl

end Mettapedia.Languages.MeTTa.ObserverFamilies
