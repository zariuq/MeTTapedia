import Mettapedia.Languages.MeTTa.CollapseSuperposeRoundTrip

/-!
# Ordering observations by what they determine

An engine offers several views of a computation: the exact report, its
values, its coverage, its faults, a bare "were there any?" test, a compact
display.  Which of these can stand in for which is not a matter of
convenience — it is the factorization question again, and it has answers.

Write `Determines fine coarse` for "the coarse view is recoverable from the
fine one".  That is literally `Factors fine coarse`, so the whole ordering is
inherited from `Core.NonFactorization`, including its criterion: a view fails
to determine another exactly when two outcomes agree on the first and differ
on the second.

The results are a small lattice of positives and negatives, and one theorem
with operational consequences:

* `notFound_justified_of_complete` — over a complete report, "no values"
  really does mean "there is nothing".
* `notFound_not_determined_by_incomplete_report` — over an incomplete report
  it means nothing at all, and not because the reasoning is hard.  Two
  realities, one containing an answer and one not, produce the *same*
  incomplete report, so no function of that report can decide between them.

That is the precise content of "exhaustion is never absence": it is not a
discipline to remember but a fact about what an incomplete observation
contains.
-/

namespace Mettapedia.Languages.MeTTa.ObserverLattice

open Mettapedia.Languages.MeTTa.Emptiness
open Mettapedia.Languages.MeTTa.RoundTrip
open Mettapedia.GSLT.Core.NonFactorization

/-! ## The ordering -/

/-- The coarse view is recoverable from the fine one. -/
def Determines {Fine Coarse : Type} (fine : Outcome → Fine)
    (coarse : Outcome → Coarse) : Prop :=
  Factors fine coarse

theorem Determines.refl {View : Type} (view : Outcome → View) :
    Determines view view := ⟨id, fun _ => rfl⟩

theorem Determines.trans {A B C : Type} {first : Outcome → A}
    {second : Outcome → B} {third : Outcome → C}
    (firstDeterminesSecond : Determines first second)
    (secondDeterminesThird : Determines second third) :
    Determines first third := by
  obtain ⟨recoverSecond, recoversSecond⟩ := firstDeterminesSecond
  obtain ⟨recoverThird, recoversThird⟩ := secondDeterminesThird
  refine ⟨fun observed => recoverThird (recoverSecond observed), fun outcome => ?_⟩
  show recoverThird (recoverSecond (first outcome)) = third outcome
  rw [recoversSecond outcome, recoversThird outcome]

/-! ## The views -/

/-- Everything the engine knows. -/
def exactReport : Outcome → Outcome := id
/-- The answers only. -/
def valuesView : Outcome → List Datum := Outcome.values
/-- Whether the search finished. -/
def coverageView : Outcome → Coverage := Outcome.coverage
/-- What went wrong. -/
def faultsView : Outcome → List String := Outcome.faults
/-- Were there any answers at all. -/
def zeroTest : Outcome → Bool := fun outcome => outcome.values.isEmpty

/-- The exact report is the top of the ordering: every view factors through
it, by definition of being a view. -/
theorem exactReport_determines {View : Type} (view : Outcome → View) :
    Determines exactReport view := ⟨view, fun _ => rfl⟩

/-- Values determine the zero test. -/
theorem values_determines_zeroTest : Determines valuesView zeroTest :=
  ⟨fun answers => answers.isEmpty, fun _ => rfl⟩

/-! ## What the value view loses

Each negative is a fibre: two outcomes agreeing on values and differing
elsewhere. -/

/-- Same answers, different coverage. -/
def coverageFiber : NonTrivialFiber valuesView coverageView where
  left := ⟨[.unit], .complete, []⟩
  right := ⟨[.unit], .incomplete "budget", []⟩
  sameShadow := rfl
  differentValue := by decide

/-- **Values do not determine coverage.**  So a values-only observer cannot
report whether the search finished, and any coverage it displays is
manufactured. -/
theorem values_not_determines_coverage : ¬ Determines valuesView coverageView :=
  coverageFiber.not_factors

/-- Same answers, different faults. -/
def faultFiber : NonTrivialFiber valuesView faultsView where
  left := ⟨[.unit], .complete, []⟩
  right := ⟨[.unit], .complete, ["divide by zero"]⟩
  sameShadow := rfl
  differentValue := by decide

/-- **Values do not determine faults.** -/
theorem values_not_determines_faults : ¬ Determines valuesView faultsView :=
  faultFiber.not_factors

/-- Same verdict on emptiness, different answers. -/
def zeroTestFiber : NonTrivialFiber zeroTest valuesView where
  left := ⟨[.unit], .complete, []⟩
  right := ⟨[.nil], .complete, []⟩
  sameShadow := rfl
  differentValue := by decide

/-- **A zero test does not determine the answers.**  Knowing that something
was found says nothing about what. -/
theorem zeroTest_not_determines_values : ¬ Determines zeroTest valuesView :=
  zeroTestFiber.not_factors

/-- Same coverage, different answers: the coverage view is not a substitute
for the value view either. -/
def coverageOnlyFiber : NonTrivialFiber coverageView valuesView where
  left := ⟨[], .complete, []⟩
  right := ⟨[.unit], .complete, []⟩
  sameShadow := rfl
  differentValue := by decide

theorem coverage_not_determines_values : ¬ Determines coverageView valuesView :=
  coverageOnlyFiber.not_factors

/-! ## Exhaustion is never absence

The theorem with teeth.  An observation is *sound* when the answers it
reports really occur, and when a report claiming completeness really did
return everything.  Those are the only assumptions used. -/

/-- A report together with the reality it was taken of. -/
structure SoundObservation where
  /-- What is actually there. -/
  underlying : List Datum
  /-- What the observer said. -/
  reported : Outcome
  /-- Reported answers really occur. -/
  reportedOccurs : reported.values ⊆ underlying
  /-- A report claiming completeness returned everything. -/
  completeIsExhaustive : reported.coverage = .complete → reported.values = underlying

/-- **Over a complete report, absence of answers is a negative result.** -/
theorem notFound_justified_of_complete (observation : SoundObservation)
    (complete : observation.reported.coverage = .complete)
    (noAnswers : observation.reported.values = []) :
    observation.underlying = [] := by
  rw [← observation.completeIsExhaustive complete, noAnswers]

/-- Two realities — one holding an answer, one not — that produce exactly the
same incomplete report. -/
def incompleteFiber :
    NonTrivialFiber SoundObservation.reported SoundObservation.underlying where
  left :=
    { underlying := []
      reported := ⟨[], .incomplete "budget", []⟩
      reportedOccurs := by simp
      completeIsExhaustive := by intro complete; simp at complete }
  right :=
    { underlying := [.unit]
      reported := ⟨[], .incomplete "budget", []⟩
      reportedOccurs := by simp
      completeIsExhaustive := by intro complete; simp at complete }
  sameShadow := rfl
  differentValue := by decide

/-- **Over an incomplete report, absence of answers means nothing.**  No
function of the report decides whether an answer exists, because the same
report arises from both realities.  So "not found" is not a conclusion an
incomplete search may draw — and this is a fact about the information the
report carries, not a caution about reasoning carelessly. -/
theorem notFound_not_determined_by_incomplete_report :
    ¬ Factors SoundObservation.reported SoundObservation.underlying :=
  incompleteFiber.not_factors

/-- The two together: completeness is exactly what upgrades an empty report
from ignorance to a negative result. -/
theorem completeness_is_what_licenses_notFound :
    (∀ observation : SoundObservation,
        observation.reported.coverage = .complete →
        observation.reported.values = [] → observation.underlying = []) ∧
      ¬ Factors SoundObservation.reported SoundObservation.underlying :=
  ⟨notFound_justified_of_complete, notFound_not_determined_by_incomplete_report⟩

end Mettapedia.Languages.MeTTa.ObserverLattice
