import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunsAmplitude
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunsWorldModelRules
import Mettapedia.PLN.TruthValues.PLNAmplitudePhase
import Mettapedia.QuantumTheory.AmplitudeSemantics

/-!
# Measurement, publication and waveform guards over runs

## The two-path law

The exact law `born_add` of `AnnotatedRunsAmplitude`, read in `ℂ` through the injective algebra map
`intoComplex`, is the squared norm of the complex sum (`born_add_complex`). In polar form it is
`PLNAmplitudePhase.complexTwoPathBornWeight_interference`: magnitudes `r`, `s` and phases `θ`, `φ`
give `r² + s² + 2rs cos(θ - φ)` (`born_add_polar`), and the interference term is
`2rs cos(θ - φ)` (`interference_polar`).

## Runs as executions

A run's amplitude is the execution of its scale actions in `AmplitudeSemantics`' ordered action
language (`runAmplitude_eq_execute`), so its Born weight agrees with the complex readout of that
execution (`born_runAmplitude_complex`, from `rational_execution_readout`).

## Measurement at a cut

* A binary measurement reads two regions of the space, the rows of `yes` and of `no`. Its Born
  probability is `born Z_yes / (born Z_yes + born Z_no)` (`bornProbability`), and its truth value
  pairs it with the PLN confidence `n/(n+k)` of a declared concentration `n` (`measuredTruth`).
* This reads `born Z_Q` as a Born probability, which is exact when the histories of each region
  have one end (`AmplitudeRuns.endReadout_of_one_end`). With the nominal end, histories that differ
  only in the identities they make share an end (`AmplitudeRuns.nominalEnd`); with the
  identity-observing end every made row is a record, and the Born weights of different ends add
  (`AmplitudeRuns.branchReadout`).
* **Through `PLNAmplitudePhase`**: the measurement is the phased state with the Hellinger
  magnitudes of that probability, the relative phase of the two amplitudes, and the concentration
  (`phasedState`). Its typed STV is the measured truth value, for any confidence chart, and the
  confidence is `n/(n+k)` in PLN's odds chart (`phasedState_toTypedSTV`,
  `phasedState_confidence`).
* **Phase invisibility**: equal Born weights give one truth value and one typed STV, whatever the
  phases (`measuredTruth_eq_of_born`, `toTypedSTV_eq_of_born`). The measurements `(1, 1)` and
  `(1, -1)` are different phased states with relative phases `0` and `-π`, and one truth value
  (`phase_invisible_control`).
* **A total cancellation has no Born readout**: the Born probability is `RationalComplexAmplitude`'s
  normalized readout when the Born total is not zero (`normalizeBorn_measurement`), and there is no
  readout when both amplitudes vanish (`normalizeBorn_measurement_none`).

## Publication into R30's ledger

* `measurementFiring` has predicate queries of the two regions, the guard that what they saw has a
  nonzero Born total, and makes the row of the measured truth value at a fresh identity. It is
  admitted exactly when both queries saw their regions whole, the Born total is not zero, the row
  is fresh and carries that truth value, and the store has a solution
  (`measurementFiring_valid_iff`). So an admitted measurement publishes the truth value of the
  regional amplitudes at its cut (`measurement_adequate`), and where both regions cancel no
  measurement is admitted (`measurement_refused_of_cancelled`).
* With its rows in R30's evidence space, recording their truth values, the measurement adds one
  identified observation to the ledger (`measurement_publishes`), and the readout gains one sample
  of the measured truth value (`measurement_readout`).
* **The ledger does not see phase**: measurements at cuts whose regional amplitudes have equal Born
  weights publish one row and add the same evidence to R30's ledger, for every query of truth
  values (`ledger_phase_invisible`). Before publication the phase is visible: one more path
  separates amplitudes of equal weight (`phase_visible_before_publication`).

## Interference must be computed before publication

* Publishing each path's Born weight separately and revising by union gives the incoherent
  weight, never the coherent one (`separate_publication_incoherent`).
* **Separating example**: the paths `1, -1` and `1, 1` publish the same Born weights, so R30's
  ledger evidence agrees for every query, while their coherent Born weights are `0` and `4`
  (`separate_publication_loses_interference`, `separate_ledger_evidence_eq`). No function of the
  separately published weights computes the coherent weight
  (`no_readout_after_separate_publication`). Measured before publication, with one path `1` for
  `no`, they give the truth values `(0, 1/2)` and `(4/5, 1/2)`
  (`interference_then_publication_control`).

## A waveform guard as a transform rule

* `waveformFiring verdict` has a predicate query of the region, the guard that `verdict` holds of
  the paths it saw (R30's `GuardBits`), and produces the row of their coherent amplitude.
* **Adequacy** (`waveform_adequate`): an admitted waveform firing saw the whole region, the verdict
  holds of the region's paths at the cut, and its row is the regional amplitude at the cut.
  Conversely it fires wherever the verdict holds, with a fresh row of that amplitude and a
  consistent store (`waveform_fires`), and it is refused where the verdict fails
  (`waveform_refused`) or a path has arrived since its query saw the region
  (`waveform_refuses_arrival`).
* The cancellation guard (`cancellationFiring`) produces the row of amplitude zero
  (`cancellation_adequate`); the reinforcement guard is `reinforcementFiring`.
-/

set_option autoImplicit false

open scoped QuadraticAlgebra

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns

namespace AmplitudeRuns

open Mettapedia.Algebra.RationalComplexAmplitude (Amplitude born born_formula born_nonnegative
  born_zero_iff intoComplex born_agrees_complex normalizeBorn bornTotal normalizeBorn_eq_some_iff
  normalizeBorn_none_iff bornTotal_zero_iff)
open Mettapedia.PLN.TruthValues.PLNAmplitudePhase (BinaryAmplitudePhaseState complexAmplitude
  complexTwoPathBornWeight_interference complexAmplitude_normSq)
open Mettapedia.PLN.TruthValues.PLNTruthTower (TypedSTV)
open Mettapedia.PLN.TruthValues.PLNConfidenceWeight (EvidenceWeightCoordinate)
open Mettapedia.PLN.TruthValues.PLNConfidenceWeight.EvidenceWeightCoordinate (TypedConfidence
  plnOddsCoordinate)
open Mettapedia.PLN.WorldModel.EvidenceSpaces (Evidence sampleEvidence)
open Mettapedia.PLN.WorldModel.EvidenceContracts (ledgerEvidence)
open MeTTaCalculus.OccurrenceCommits (regionOf PredicateQuery mem_regionOf)
open WorldModelRuns (ledger readout recorded madeObservations KeepsEvidence ledger_result_of_keeps
  readout_result_of_keeps GuardBits)

universe uT uS uO

/-! ## The two-path law, in `ℂ` and in polar form -/

section TwoPath

/-- **The exact two-path law read in `ℂ`**: the Born weight of a sum of rational amplitudes is the
squared norm of the sum of their complex images. -/
theorem born_add_complex (z w : Amplitude) :
    (born (z + w) : ℝ) = Complex.normSq (intoComplex z + intoComplex w) := by
  rw [born_agrees_complex, map_add]

/-- **In polar form it is `PLNAmplitudePhase`'s two-path law.** -/
theorem born_add_polar {z w : Amplitude} {r s θ φ : ℝ} (hz : intoComplex z = complexAmplitude r θ)
    (hw : intoComplex w = complexAmplitude s φ) :
    (born (z + w) : ℝ) = r ^ 2 + s ^ 2 + 2 * r * s * Real.cos (θ - φ) := by
  rw [born_add_complex, hz, hw]
  exact complexTwoPathBornWeight_interference r s θ φ

/-- **The interference term in polar form** is `2rs cos(θ - φ)`. -/
theorem interference_polar {z w : Amplitude} {r s θ φ : ℝ}
    (hz : intoComplex z = complexAmplitude r θ) (hw : intoComplex w = complexAmplitude s φ) :
    (interference z w : ℝ) = 2 * r * s * Real.cos (θ - φ) := by
  have total := born_add_polar hz hw
  have left : (born z : ℝ) = r ^ 2 := by
    rw [born_agrees_complex, hz, complexAmplitude_normSq]
  have right : (born w : ℝ) = s ^ 2 := by
    rw [born_agrees_complex, hw, complexAmplitude_normSq]
  rw [born_add] at total
  push_cast at total
  linarith

end TwoPath

/-! ## A run's amplitude is the execution of its scale actions -/

section Execution

open Mettapedia.QuantumTheory (AmplitudeAction execute rational_execution_readout)

variable {T : Type uT} {S : Type uS} {O : Type uO} (amp : Firing T S O → Amplitude)

/-- The scale actions of a run: one per firing, by its amplitude. -/
def scaleActions (w : List (Firing T S O)) : List (AmplitudeAction Amplitude) :=
  w.map fun f => AmplitudeAction.scale (amp f)

/-- Executing a run's scale actions multiplies by the run's amplitude. -/
theorem execute_scaleActions : ∀ (w : List (Firing T S O)) (z : Amplitude),
    execute (scaleActions amp w) z = z * runAmplitude amp w
  | [], z => (mul_one z).symm
  | f :: rest, z => by
      change execute (scaleActions amp rest) (z * amp f) = z * (amp f * runAmplitude amp rest)
      rw [execute_scaleActions rest, mul_assoc]

/-- **A run's amplitude is the execution of its scale actions** in `AmplitudeSemantics`' ordered
action language. -/
theorem runAmplitude_eq_execute (w : List (Firing T S O)) :
    runAmplitude amp w = execute (scaleActions amp w) 1 := by
  rw [execute_scaleActions, one_mul]

/-- **Its Born weight is the complex readout of the same execution** (`rational_execution_readout`):
the exact amplitude of a run and its complex interpretation give one Born weight. -/
theorem born_runAmplitude_complex (w : List (Firing T S O)) :
    (born (runAmplitude amp w) : ℝ) =
      Complex.normSq (execute ((scaleActions amp w).map (AmplitudeAction.map intoComplex))
        (intoComplex 1)) := by
  rw [runAmplitude_eq_execute]
  exact rational_execution_readout (scaleActions amp w) 1

end Execution

/-! ## Measurement: the Born readout as a PLN truth value -/

section Measurement

/-- **The Born probability of `yes`** from the regional amplitudes of `yes` and `no`: a probability when
the histories of each region have one end. -/
def bornProbability (yes no : Amplitude) : ℚ := born yes / (born yes + born no)

theorem bornProbability_nonneg (yes no : Amplitude) : 0 ≤ bornProbability yes no :=
  div_nonneg (born_nonnegative yes) (add_nonneg (born_nonnegative yes) (born_nonnegative no))

theorem bornProbability_le_one (yes no : Amplitude) : bornProbability yes no ≤ 1 := by
  unfold bornProbability
  rcases (add_nonneg (born_nonnegative yes) (born_nonnegative no)).eq_or_lt with zero | positive
  · rw [← zero, div_zero]
    exact zero_le_one
  · rw [div_le_one positive]
    linarith [born_nonnegative no]

/-- **The measured truth value**: the Born probability of `yes`, and the PLN confidence `n/(n+k)`
of the declared concentration `n` at prior weight `k`. -/
def measuredTruth (k n : ℚ) (yes no : Amplitude) : ℚ × ℚ := (bornProbability yes no, n / (n + k))

/-- **The phased PLN state of a measurement**: the Hellinger magnitudes of its Born probability,
the relative phase of its two amplitudes, and its concentration. -/
noncomputable def phasedState (n : ℚ) (yes no : Amplitude) : BinaryAmplitudePhaseState :=
  BinaryAmplitudePhaseState.fromStrengthConcentration (bornProbability yes no) n
    (Complex.arg (intoComplex yes) - Complex.arg (intoComplex no))

/-- **The typed STV of a measurement**: its strength is the Born probability, its confidence the
declared concentration in the chosen chart. -/
theorem phasedState_toTypedSTV (χ : EvidenceWeightCoordinate) (n : ℚ) (yes no : Amplitude) :
    (phasedState n yes no).toTypedSTV χ =
      ⟨(bornProbability yes no : ℝ), TypedConfidence.ofWeight χ (n : ℝ)⟩ := by
  have strength : (phasedState n yes no).bornStrength = (bornProbability yes no : ℝ) :=
    BinaryAmplitudePhaseState.fromStrengthConcentration_bornStrength
      (by exact_mod_cast bornProbability_nonneg yes no)
  change (⟨(phasedState n yes no).bornStrength, TypedConfidence.ofWeight χ (n : ℝ)⟩ : TypedSTV χ) =
    _
  rw [strength]

/-- **In PLN's odds chart, the confidence is `n/(n+k)`**: the measured truth value is the typed
STV of the phased state. -/
theorem phasedState_confidence {k : ℚ} (hk : 0 < (k : ℝ)) (n : ℚ) (yes no : Amplitude) :
    ((phasedState n yes no).toTypedSTV (plnOddsCoordinate (k : ℝ) hk)).strength =
        ((measuredTruth k n yes no).1 : ℝ) ∧
      ((phasedState n yes no).toTypedSTV (plnOddsCoordinate (k : ℝ) hk)).confidence.display =
        ((measuredTruth k n yes no).2 : ℝ) := by
  rw [phasedState_toTypedSTV]
  refine ⟨rfl, ?_⟩
  change (n : ℝ) / ((n : ℝ) + (k : ℝ)) = ((n / (n + k) : ℚ) : ℝ)
  push_cast
  rfl

/-- **Phase is invisible to the truth value**: equal Born weights give one truth value. -/
theorem measuredTruth_eq_of_born {k n : ℚ} {yes no yes' no' : Amplitude}
    (sameYes : born yes = born yes') (sameNo : born no = born no') :
    measuredTruth k n yes no = measuredTruth k n yes' no' := by
  simp only [measuredTruth, bornProbability, sameYes, sameNo]

/-- **Phase is invisible to the typed STV**: equal Born weights give one typed STV. -/
theorem toTypedSTV_eq_of_born (χ : EvidenceWeightCoordinate) {n : ℚ} {yes no yes' no' : Amplitude}
    (sameYes : born yes = born yes') (sameNo : born no = born no') :
    (phasedState n yes no).toTypedSTV χ = (phasedState n yes' no').toTypedSTV χ := by
  rw [phasedState_toTypedSTV, phasedState_toTypedSTV]
  simp only [bornProbability, sameYes, sameNo]

/-- **Canary**: the measurements `(1, 1)` and `(1, -1)` have relative phases `0` and `-π`, so they
are different phased states, with one typed STV and one truth value. -/
theorem phase_invisible_control (χ : EvidenceWeightCoordinate) :
    (phasedState 1 1 1).relativePhase = 0 ∧ (phasedState 1 1 (-1)).relativePhase = -Real.pi ∧
      phasedState 1 1 1 ≠ phasedState 1 1 (-1) ∧
      (phasedState 1 1 1).toTypedSTV χ = (phasedState 1 1 (-1)).toTypedSTV χ ∧
      measuredTruth 1 1 1 1 = measuredTruth 1 1 1 (-1) := by
  have phase₁ : (phasedState 1 1 1).relativePhase = 0 := by
    change Complex.arg (intoComplex 1) - Complex.arg (intoComplex 1) = 0
    rw [sub_self]
  have phase₂ : (phasedState 1 1 (-1)).relativePhase = -Real.pi := by
    change Complex.arg (intoComplex 1) - Complex.arg (intoComplex (-1)) = -Real.pi
    rw [map_neg, map_one, Complex.arg_one, Complex.arg_neg_one, zero_sub]
  refine ⟨phase₁, phase₂, fun same => ?_, toTypedSTV_eq_of_born χ rfl (born_neg 1).symm,
    measuredTruth_eq_of_born rfl (born_neg 1).symm⟩
  have phases := congrArg BinaryAmplitudePhaseState.relativePhase same
  rw [phase₁, phase₂] at phases
  linarith [Real.pi_pos]

/-- **The Born probability is the normalized Born readout** of `RationalComplexAmplitude`, when the
Born total is not zero. -/
theorem normalizeBorn_measurement {yes no : Amplitude} (measured : born yes + born no ≠ 0) :
    normalizeBorn [(true, yes), (false, no)] =
      some [(true, bornProbability yes no), (false, born no / (born yes + born no))] := by
  have total : bornTotal [(true, yes), (false, no)] = born yes + born no := by
    simp [bornTotal]
  rw [normalizeBorn_eq_some_iff, total]
  exact ⟨measured, by simp [bornProbability]⟩

/-- **A total cancellation has no Born readout.** -/
theorem normalizeBorn_measurement_none {yes no : Amplitude} :
    normalizeBorn [(true, yes), (false, no)] = none ↔ yes = 0 ∧ no = 0 := by
  rw [normalizeBorn_none_iff, bornTotal_zero_iff]
  simp

end Measurement

/-! ## Row firings -/

section RowFirings

variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]
variable (A : SubstitutionAction T S) (label : O → T)

omit [DecidableEq O] in
/-- **A row firing**: fixed predicate queries and guards; it takes and reads nothing and makes the
row `t` at `r`. -/
def rowFiring (queries : List (PredicateQuery O T)) (checks : List (Check T)) (t : T) (r : O) :
    Firing T S O :=
  ⟨⟨[], [], [], checks, [t]⟩, queries.map PredicateQueryAdmission.Query.fixed, ⟨[], [], [r]⟩⟩

/-- **Admission of a row firing**: every query saw its region whole, the row is fresh and carries
`t`, the store has a solution, and every guard holds at every solution of the store. -/
theorem rowFiring_valid_iff (queries : List (PredicateQuery O T)) (checks : List (Check T)) (t : T)
    (r : O) (C : Configuration T O) :
    (rowFiring queries checks t r : Firing T S O).Valid A label C ↔
      (∀ query ∈ queries, query.Holds label C.present) ∧ r ∉ C.present ∧ label r = t ∧
        A.Consistent C.equations ∧
        ∀ check ∈ checks, A.Entails C.equations fun σ => check.Holds A σ label C.present := by
  have problem : (⟨[], [], [r]⟩ : Selection O).problem label
      (⟨[], [], [], checks, [t]⟩ : RuleInstance T) C = C.equations := by
    simp [Selection.problem, Selection.equations]
  change PredicateQueryAdmission.Valid A label (⟨[], [], [], checks, [t]⟩ : RuleInstance T)
      (queries.map PredicateQueryAdmission.Query.fixed) C (⟨[], [], [r]⟩ : Selection O) ↔ _
  rw [PredicateQueryAdmission.valid_fixed_iff]
  constructor
  · rintro ⟨firing, holds⟩
    have consistent := firing.consistent
    have checksHold := firing.checks
    rw [problem] at consistent checksHold
    refine ⟨holds, fun present => ?_, by simpa using firing.outputs, consistent, checksHold⟩
    exact Finset.disjoint_left.mp firing.occurrences.fresh (by simp [Selection.commit]) present
  · rintro ⟨holds, fresh, rowEq, consistent, checksHold⟩
    refine ⟨⟨by simp, by simp, rfl, rfl, by simp [rowEq],
      ⟨by simp [Selection.commit], by simp [Selection.commit], by simp [Selection.commit],
        by simpa [Selection.commit] using fresh, by simp [Selection.commit]⟩,
      by rw [problem]; exact consistent, by rw [problem]; exact checksHold⟩, holds⟩

omit [DecidableEq O] in
theorem rowFiring_taken (queries : List (PredicateQuery O T)) (checks : List (Check T)) (t : T)
    (r : O) : (rowFiring queries checks t r : Firing T S O).selection.taken = [] := rfl

end RowFirings

/-! ## Publication into R30's ledger -/

section Publication

variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]
variable (A : SubstitutionAction T S) (label : O → T) (wave : T → Amplitude)

omit [DecidableEq O] in
/-- **The measured truth value at a cut**, from the regional amplitudes of `yes` and `no`. -/
def cutTruth (yes no : T → Bool) (k n : ℚ) (C : Configuration T O) : ℚ × ℚ :=
  measuredTruth k n (coherent (regionPaths label wave yes C))
    (coherent (regionPaths label wave no C))

omit [DecidableEq O] in
/-- **The measurement firing**: predicate queries of the regions `yes` and `no` that saw `yesSeen`
and `noSeen`, the guard that what they saw has a nonzero Born total, and the row of its measured
truth value made at `r`. -/
def measurementFiring (bits : GuardBits A) (yes no : T → Bool) (k n : ℚ) (row : ℚ × ℚ → T)
    (yesSeen noSeen : Finset O) (r : O) : Firing T S O :=
  rowFiring [⟨yes, yesSeen⟩, ⟨no, noSeen⟩]
    [bits.check (decide (born (coherent (pathsOf label wave yesSeen)) +
      born (coherent (pathsOf label wave noSeen)) ≠ 0))]
    (row (measuredTruth k n (coherent (pathsOf label wave yesSeen))
      (coherent (pathsOf label wave noSeen)))) r

variable {bits : GuardBits A} {yes no : T → Bool} {k n : ℚ} {row : ℚ × ℚ → T}

/-- **Admission of a measurement**: both queries saw their regions whole, what they saw has a
nonzero Born total, the row is fresh and carries the measured truth value, and the store has a
solution. -/
theorem measurementFiring_valid_iff (yesSeen noSeen : Finset O) (r : O) (C : Configuration T O) :
    (measurementFiring A label wave bits yes no k n row yesSeen noSeen r).Valid A label C ↔
      regionOf label C.present yes = yesSeen ∧ regionOf label C.present no = noSeen ∧
        born (coherent (pathsOf label wave yesSeen)) +
            born (coherent (pathsOf label wave noSeen)) ≠ 0 ∧
        r ∉ C.present ∧
        label r = row (measuredTruth k n (coherent (pathsOf label wave yesSeen))
          (coherent (pathsOf label wave noSeen))) ∧
        A.Consistent C.equations := by
  unfold measurementFiring
  rw [rowFiring_valid_iff]
  constructor
  · rintro ⟨holds, fresh, rowEq, ⟨σ, solved⟩, guard⟩
    have decided := (GuardBits.holds_iff label bits σ C.present _).mp
      (guard _ (List.mem_singleton_self _) σ solved)
    exact ⟨holds ⟨yes, yesSeen⟩ (by simp), holds ⟨no, noSeen⟩ (by simp),
      of_decide_eq_true decided, fresh, rowEq, ⟨σ, solved⟩⟩
  · rintro ⟨yesEq, noEq, measured, fresh, rowEq, consistent⟩
    refine ⟨fun query member => ?_, fresh, rowEq, consistent, fun check member σ _ => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact yesEq
      · exact noEq
    · rw [List.mem_singleton.mp member]
      exact (GuardBits.holds_iff label bits σ C.present _).mpr (decide_eq_true measured)

/-- **Adequacy of measurement**: an admitted measurement saw both regions whole, the Born total of
the regional amplitudes at its cut is not zero, and its row is their measured truth value. -/
theorem measurement_adequate {yesSeen noSeen : Finset O} {r : O} {C : Configuration T O}
    (valid : (measurementFiring A label wave bits yes no k n row yesSeen noSeen r).Valid
      A label C) :
    yesSeen = regionOf label C.present yes ∧ noSeen = regionOf label C.present no ∧
      born (coherent (regionPaths label wave yes C)) +
          born (coherent (regionPaths label wave no C)) ≠ 0 ∧
      label r = row (cutTruth label wave yes no k n C) := by
  obtain ⟨yesEq, noEq, measured, -, rowEq, -⟩ :=
    (measurementFiring_valid_iff A label wave yesSeen noSeen r C).mp valid
  subst yesEq
  subst noEq
  exact ⟨rfl, rfl, measured, rowEq⟩

/-- **A total cancellation is not measured**: where both regions cancel to zero, no measurement is
admitted, whatever its queries saw. -/
theorem measurement_refused_of_cancelled {yesSeen noSeen : Finset O} {r : O}
    {C : Configuration T O} (yesZero : coherent (regionPaths label wave yes C) = 0)
    (noZero : coherent (regionPaths label wave no C) = 0) :
    ¬ (measurementFiring A label wave bits yes no k n row yesSeen noSeen r).Valid A label C :=
  fun valid => by
    have measured := (measurement_adequate A label wave valid).2.2.1
    rw [yesZero, noZero, born_zero, add_zero] at measured
    exact measured rfl

variable (space : T → Bool) (outcome : T → ℚ × ℚ)

omit [DecidableEq O] in
theorem measurement_keeps (yesSeen noSeen : Finset O) (r : O) :
    KeepsEvidence label space
      (measurementFiring A label wave bits yes no k n row yesSeen noSeen r) := by
  intro o taken
  cases taken

theorem measurement_madeObservations {yesSeen noSeen : Finset O} {r : O} {C : Configuration T O}
    (valid : (measurementFiring A label wave bits yes no k n row yesSeen noSeen r).Valid A label C)
    (observed : ∀ tv, space (row tv) = true) :
    madeObservations label space
      (measurementFiring A label wave bits yes no k n row yesSeen noSeen r) = {r} := by
  have rowEq := (measurement_adequate A label wave valid).2.2.2
  ext o
  simp only [madeObservations, measurementFiring, rowFiring, List.toFinset_cons, List.toFinset_nil,
    Finset.mem_filter, Finset.mem_insert, Finset.notMem_empty, or_false, Finset.mem_singleton]
  constructor
  · exact fun inside => inside.1
  · rintro rfl
    exact ⟨rfl, by rw [rowEq]; exact observed _⟩

/-- **Publication**: an admitted measurement adds one identified observation, its row, to R30's
ledger. -/
theorem measurement_publishes {yesSeen noSeen : Finset O} {r : O} {C : Configuration T O}
    (valid : (measurementFiring A label wave bits yes no k n row yesSeen noSeen r).Valid A label C)
    (observed : ∀ tv, space (row tv) = true) :
    ledger label space
        ((measurementFiring A label wave bits yes no k n row yesSeen noSeen r).result label C) =
      ledger label space C ∪ {r} := by
  rw [ledger_result_of_keeps label space (measurement_keeps A label wave space yesSeen noSeen r) C,
    measurement_madeObservations A label wave space valid observed]

/-- **The published evidence**: for every query `φ` of truth values, the readout of R30's ledger
gains one sample of the measured truth value of the regional amplitudes at the cut. -/
theorem measurement_readout {yesSeen noSeen : Finset O} {r : O} {C : Configuration T O}
    (valid : (measurementFiring A label wave bits yes no k n row yesSeen noSeen r).Valid A label C)
    (observed : ∀ tv, space (row tv) = true) (records : ∀ tv, outcome (row tv) = tv)
    (φ : ℚ × ℚ → Bool) :
    readout label space outcome φ
        ((measurementFiring A label wave bits yes no k n row yesSeen noSeen r).result label C) =
      readout label space outcome φ C + sampleEvidence φ (cutTruth label wave yes no k n C) := by
  rw [readout_result_of_keeps label space outcome φ
      (measurement_keeps A label wave space yesSeen noSeen r) valid,
    measurement_madeObservations A label wave space valid observed]
  congr 1
  rw [ledgerEvidence, Finset.sum_singleton]
  change sampleEvidence φ (outcome (label r)) = _
  rw [(measurement_adequate A label wave valid).2.2.2, records]

/-- **The ledger does not see phase.** Admitted measurements at two cuts whose regional amplitudes
have equal Born weights publish one row, and each adds the same evidence to R30's ledger for every
query of truth values, whatever the phases of the amplitudes. -/
theorem ledger_phase_invisible (observed : ∀ tv, space (row tv) = true)
    (records : ∀ tv, outcome (row tv) = tv) {C D : Configuration T O}
    {yesSeen noSeen yesSeen' noSeen' : Finset O} {r r' : O}
    (validC : (measurementFiring A label wave bits yes no k n row yesSeen noSeen r).Valid A label C)
    (validD : (measurementFiring A label wave bits yes no k n row yesSeen' noSeen' r').Valid
      A label D)
    (sameYes : born (coherent (regionPaths label wave yes C)) =
      born (coherent (regionPaths label wave yes D)))
    (sameNo : born (coherent (regionPaths label wave no C)) =
      born (coherent (regionPaths label wave no D))) :
    label r = label r' ∧ ∀ φ : ℚ × ℚ → Bool,
      readout label space outcome φ
          ((measurementFiring A label wave bits yes no k n row yesSeen noSeen r).result label C) =
        readout label space outcome φ C + sampleEvidence φ (cutTruth label wave yes no k n C) ∧
      readout label space outcome φ
          ((measurementFiring A label wave bits yes no k n row yesSeen' noSeen' r').result
            label D) =
        readout label space outcome φ D + sampleEvidence φ (cutTruth label wave yes no k n C) := by
  have same : cutTruth label wave yes no k n C = cutTruth label wave yes no k n D :=
    measuredTruth_eq_of_born sameYes sameNo
  refine ⟨?_, fun φ =>
    ⟨measurement_readout A label wave space outcome validC observed records φ, ?_⟩⟩
  · rw [(measurement_adequate A label wave validC).2.2.2,
      (measurement_adequate A label wave validD).2.2.2, same]
  · rw [measurement_readout A label wave space outcome validD observed records φ, same]

/-- **Before publication the phase is visible**: the amplitudes `1` and `-1` have one Born weight,
and one more path `1` separates them, `4` against `0`. -/
theorem phase_visible_before_publication :
    born (1 : Amplitude) = born (-1) ∧ born ((1 : Amplitude) + 1) = 4 ∧
      born ((-1 : Amplitude) + 1) = 0 := by
  refine ⟨(born_neg 1).symm, ?_, ?_⟩
  · rw [born_double, born_one]
    norm_num
  · rw [neg_add_cancel, born_zero]

end Publication


/-! ## Interference must be computed before publication -/

section Order

/-- **The weight readout** of a ledger whose observations record Born weights: their sum. -/
def weightReadout {Id : Type*} (weight : Id → ℚ) (ledger : Finset Id) : ℚ := ∑ i ∈ ledger, weight i

/-- Revision of disjoint ledgers adds their weights. -/
theorem weightReadout_union_of_disjoint {Id : Type*} [DecidableEq Id] (weight : Id → ℚ)
    {first second : Finset Id} (apart : Disjoint first second) :
    weightReadout weight (first ∪ second) =
      weightReadout weight first + weightReadout weight second :=
  Finset.sum_union apart

/-- **Publishing each path's Born weight and revising gives the incoherent weight.** -/
theorem separate_publication_incoherent {Id : Type*} (path : Id → Amplitude) (ledger : Finset Id) :
    weightReadout (fun i => born (path i)) ledger = incoherent (ledger.val.map path) := by
  unfold weightReadout incoherent
  rw [Multiset.map_map]
  rfl

/-- **Separately published weights do not see phase**: families of paths with equal Born weights
give R30's ledger the same evidence, for every query of weights and every ledger. -/
theorem separate_ledger_evidence_eq {Id : Type*} [DecidableEq Id] {path path' : Id → Amplitude}
    (same : ∀ i, born (path i) = born (path' i)) (φ : ℚ → Bool) (ledger : Finset Id) :
    ledgerEvidence (fun i => born (path i)) φ ledger =
      ledgerEvidence (fun i => born (path' i)) φ ledger := by
  rw [show (fun i => born (path i)) = fun i => born (path' i) from funext same]

/-- The paths `1` and `-1`, indexed by the two observation identities. -/
def opposedPaths : Bool → Amplitude
  | true => 1
  | false => -1

/-- The paths `1` and `1`. -/
def alignedPaths : Bool → Amplitude := fun _ => 1

/-- **Separating example: publication before interference loses it.** The paths `1, -1` and
`1, 1` publish the same Born weights, so R30's ledger gets the same evidence for every query and
the same weight `2`, while their coherent Born weights are `0` and `4`. -/
theorem separate_publication_loses_interference :
    (∀ φ : ℚ → Bool, ledgerEvidence (fun i => born (opposedPaths i)) φ Finset.univ =
        ledgerEvidence (fun i => born (alignedPaths i)) φ Finset.univ) ∧
      weightReadout (fun i => born (opposedPaths i)) Finset.univ = 2 ∧
      weightReadout (fun i => born (alignedPaths i)) Finset.univ = 2 ∧
      born (∑ i, opposedPaths i) = 0 ∧ born (∑ i, alignedPaths i) = 4 := by
  have weights : ∀ i, born (opposedPaths i) = born (alignedPaths i) := by
    intro i
    cases i
    · simp [opposedPaths, alignedPaths, born_neg]
    · rfl
  refine ⟨fun φ => separate_ledger_evidence_eq weights φ Finset.univ, ?_, ?_, ?_, ?_⟩
  · norm_num [weightReadout, Fintype.sum_bool, opposedPaths, born_neg, born_one]
  · norm_num [weightReadout, Fintype.sum_bool, alignedPaths, born_one]
  · simp [opposedPaths]
  · simp only [Fintype.sum_bool, alignedPaths]
    rw [born_double, born_one]
    norm_num

/-- **No readout of separately published Born weights computes the coherent Born weight.** -/
theorem no_readout_after_separate_publication :
    ¬ ∃ readout : Multiset ℚ → ℚ, ∀ paths : Multiset Amplitude,
      readout (paths.map born) = born (coherent paths) := by
  rintro ⟨readout, computes⟩
  have opposed := computes {1, -1}
  have aligned := computes {1, 1}
  have sameWeights :
      ({1, -1} : Multiset Amplitude).map born = ({1, 1} : Multiset Amplitude).map born := by
    simp [born_neg]
  rw [sameWeights, opposite_phase_control.1] at opposed
  rw [in_phase_control.1] at aligned
  rw [opposed] at aligned
  norm_num at aligned

/-- **Interference then publication keeps it**: measured before publication, with one path `1` for
`no`, the paths `1, -1` and `1, 1` give the truth values `(0, 1/2)` and `(4/5, 1/2)`. -/
theorem interference_then_publication_control :
    measuredTruth 1 1 (coherent {1, -1}) 1 = (0, 1 / 2) ∧
      measuredTruth 1 1 (coherent {1, 1}) 1 = (4 / 5, 1 / 2) := by
  refine ⟨?_, ?_⟩
  · rw [coherent_pair, add_neg_cancel]
    simp [measuredTruth, bornProbability]
    norm_num
  · rw [coherent_pair]
    simp only [measuredTruth, bornProbability, born_double, born_one]
    norm_num

end Order

/-! ## A waveform guard as a transform rule -/

section Waveform

variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]
variable (A : SubstitutionAction T S) (label : O → T) (wave : T → Amplitude)

omit [DecidableEq O] in
/-- **The waveform guard firing** for a verdict on paths: a predicate query of the region that saw
`seen`, the guard that the verdict holds of the paths it saw, and the row of their coherent
amplitude made at `r`. -/
def waveformFiring (verdict : Multiset Amplitude → Prop) [DecidablePred verdict]
    (bits : GuardBits A) (row : Amplitude → T) (region : T → Bool) (seen : Finset O) (r : O) :
    Firing T S O :=
  rowFiring [⟨region, seen⟩] [bits.check (decide (verdict (pathsOf label wave seen)))]
    (row (coherent (pathsOf label wave seen))) r

variable {verdict : Multiset Amplitude → Prop} [DecidablePred verdict] {bits : GuardBits A}
  {row : Amplitude → T} {region : T → Bool}

/-- **Adequacy of the waveform guard**: an admitted waveform firing saw the whole region, the
verdict holds of the region's paths at the cut, and its row is the regional amplitude at the
cut. -/
theorem waveform_adequate {seen : Finset O} {r : O} {C : Configuration T O}
    (valid : (waveformFiring A label wave verdict bits row region seen r).Valid A label C) :
    seen = regionOf label C.present region ∧ verdict (regionPaths label wave region C) ∧
      label r = row (coherent (regionPaths label wave region C)) := by
  obtain ⟨holds, -, rowEq, ⟨σ, solved⟩, guard⟩ :=
    (rowFiring_valid_iff A label _ _ _ r C).mp valid
  have saw : regionOf label C.present region = seen := holds _ (List.mem_singleton_self _)
  have decided := (GuardBits.holds_iff label bits σ C.present _).mp
    (guard _ (List.mem_singleton_self _) σ solved)
  subst saw
  exact ⟨rfl, of_decide_eq_true decided, rowEq⟩

/-- **The waveform guard fires wherever its verdict holds**, with its query of the region, a fresh
row of the regional amplitude and a consistent store. -/
theorem waveform_fires {r : O} {C : Configuration T O}
    (holds : verdict (regionPaths label wave region C)) (fresh : r ∉ C.present)
    (rowEq : label r = row (coherent (regionPaths label wave region C)))
    (consistent : A.Consistent C.equations) :
    (waveformFiring A label wave verdict bits row region (regionOf label C.present region) r).Valid
      A label C := by
  refine (rowFiring_valid_iff A label _ _ _ r C).mpr ⟨?_, fresh, rowEq, consistent, ?_⟩
  · intro query member
    rw [List.mem_singleton.mp member]
    rfl
  · intro check member σ _
    rw [List.mem_singleton.mp member]
    exact (GuardBits.holds_iff label bits σ C.present _).mpr (decide_eq_true holds)

/-- **The waveform guard is refused where its verdict fails.** -/
theorem waveform_refused {seen : Finset O} {r : O} {C : Configuration T O}
    (fails : ¬ verdict (regionPaths label wave region C)) :
    ¬ (waveformFiring A label wave verdict bits row region seen r).Valid A label C := fun valid =>
  fails (waveform_adequate A label wave valid).2.1

/-- **A path arriving in the region after its query saw it refuses the waveform guard.** -/
theorem waveform_refuses_arrival {seen : Finset O} {r : O} {C : Configuration T O}
    (valid : (waveformFiring A label wave verdict bits row region seen r).Valid A label C) {o : O}
    (absent : o ∉ C.present) (inRegion : region (label o) = true) :
    ¬ (waveformFiring A label wave verdict bits row region seen r).Valid A label
      ⟨C.equations, C.present ∪ {o}⟩ :=
  query_refuses_arrival A label valid (query := ⟨region, seen⟩) (List.mem_singleton_self _) absent
    inRegion

omit [DecidableEq O] in
/-- **The cancellation guard**: fires on a cancelling region and produces the row of its
amplitude. -/
def cancellationFiring (bits : GuardBits A) (row : Amplitude → T) (region : T → Bool)
    (seen : Finset O) (r : O) : Firing T S O :=
  waveformFiring A label wave Destructive bits row region seen r

omit [DecidableEq O] in
/-- **The reinforcement guard**: fires on a reinforcing region and produces the row of its
amplitude. -/
def reinforcementFiring (bits : GuardBits A) (row : Amplitude → T) (region : T → Bool)
    (seen : Finset O) (r : O) : Firing T S O :=
  waveformFiring A label wave Constructive bits row region seen r

/-- **Adequacy of the cancellation guard**: an admitted cancellation firing saw the whole region,
the region cancels at the cut, and the row it produces is the row of amplitude zero. -/
theorem cancellation_adequate {bits : GuardBits A} {row : Amplitude → T} {seen : Finset O} {r : O}
    {C : Configuration T O}
    (valid : (cancellationFiring A label wave bits row region seen r).Valid A label C) :
    seen = regionOf label C.present region ∧ Destructive (regionPaths label wave region C) ∧
      label r = row 0 := by
  obtain ⟨seenEq, cancels, rowEq⟩ := waveform_adequate A label wave valid
  exact ⟨seenEq, cancels, rowEq.trans (congrArg row cancels.1)⟩

/-- **Adequacy of the reinforcement guard.** -/
theorem reinforcement_adequate {bits : GuardBits A} {row : Amplitude → T} {seen : Finset O} {r : O}
    {C : Configuration T O}
    (valid : (reinforcementFiring A label wave bits row region seen r).Valid A label C) :
    seen = regionOf label C.present region ∧ Constructive (regionPaths label wave region C) ∧
      label r = row (coherent (regionPaths label wave region C)) :=
  waveform_adequate A label wave valid

end Waveform

end AmplitudeRuns

open AmplitudeRuns

#print axioms born_add_complex
#print axioms born_add_polar
#print axioms interference_polar
#print axioms execute_scaleActions
#print axioms runAmplitude_eq_execute
#print axioms born_runAmplitude_complex
#print axioms bornProbability_le_one
#print axioms phasedState_toTypedSTV
#print axioms phasedState_confidence
#print axioms measuredTruth_eq_of_born
#print axioms toTypedSTV_eq_of_born
#print axioms phase_invisible_control
#print axioms normalizeBorn_measurement
#print axioms normalizeBorn_measurement_none
#print axioms measurement_refused_of_cancelled
#print axioms rowFiring_valid_iff
#print axioms measurementFiring_valid_iff
#print axioms measurement_adequate
#print axioms measurement_publishes
#print axioms measurement_readout
#print axioms ledger_phase_invisible
#print axioms phase_visible_before_publication
#print axioms weightReadout_union_of_disjoint
#print axioms separate_publication_incoherent
#print axioms separate_ledger_evidence_eq
#print axioms separate_publication_loses_interference
#print axioms no_readout_after_separate_publication
#print axioms interference_then_publication_control
#print axioms waveform_adequate
#print axioms waveform_fires
#print axioms waveform_refused
#print axioms waveform_refuses_arrival
#print axioms cancellation_adequate
#print axioms reinforcement_adequate

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns
