import Mettapedia.Languages.GF.English.RoundTripCorpus
import Mettapedia.Languages.GF.Czech.RoundTripCorpus

/-!
# GF Roundtrip Regression Harness (EN + CZ)

Executable + theorem-backed regression harness over the current full curated
English and Czech roundtrip corpora.

- `*_Failures` compute counterexample sets.
- `*_Failures_empty` prove there are no current corpus regressions.
- `totalFailureCount_zero` gives a single aggregate status theorem.
-/

namespace Mettapedia.Languages.GF.RoundTripRegression

/-- English roundtrip counterexamples in the curated corpus. -/
def englishFailures : List Mettapedia.Languages.GF.English.RoundTripCorpus.ExampleSurface :=
  Mettapedia.Languages.GF.English.RoundTripCorpus.allExamples.filter
    (fun e => decide
      (e ∉ Mettapedia.Languages.GF.English.RoundTripCorpus.parseSurface
        (Mettapedia.Languages.GF.English.RoundTripCorpus.linearizeSurface e)))

/-- Czech roundtrip counterexamples in the curated corpus. -/
def czechFailures : List Mettapedia.Languages.GF.Czech.RoundTripCorpus.ExampleSurface :=
  Mettapedia.Languages.GF.Czech.RoundTripCorpus.allExamples.filter
    (fun e => decide
      (e ∉ Mettapedia.Languages.GF.Czech.RoundTripCorpus.parseSurface
        (Mettapedia.Languages.GF.Czech.RoundTripCorpus.linearizeSurface e)))

/-- English harness soundness: no failures in the current corpus. -/
theorem englishFailures_empty : englishFailures = [] := by
  apply (List.filter_eq_nil_iff).2
  intro e he
  have hOk :
      e ∈ Mettapedia.Languages.GF.English.RoundTripCorpus.parseSurface
        (Mettapedia.Languages.GF.English.RoundTripCorpus.linearizeSurface e) :=
    Mettapedia.Languages.GF.English.RoundTripCorpus.parse_linearize_complete e
  simp [hOk]

/-- Czech harness soundness: no failures in the current corpus. -/
theorem czechFailures_empty : czechFailures = [] := by
  apply (List.filter_eq_nil_iff).2
  intro e he
  have hOk :
      e ∈ Mettapedia.Languages.GF.Czech.RoundTripCorpus.parseSurface
        (Mettapedia.Languages.GF.Czech.RoundTripCorpus.linearizeSurface e) :=
    Mettapedia.Languages.GF.Czech.RoundTripCorpus.parse_linearize_complete e
  simp [hOk]

/-- Aggregate regression count across English and Czech corpora. -/
def totalFailureCount : Nat :=
  englishFailures.length + czechFailures.length

/-- Current aggregate roundtrip regression count is zero. -/
theorem totalFailureCount_zero : totalFailureCount = 0 := by
  simp [totalFailureCount, englishFailures_empty, czechFailures_empty]

-- Executable regression summary.
#eval englishFailures.length
#eval czechFailures.length
#eval totalFailureCount

end Mettapedia.Languages.GF.RoundTripRegression
