import Mettapedia.Logic.EvidenceQuantale
import Mettapedia.Logic.PLNRevision
import Mathlib.Data.List.Count

/-!
# RavenAsymmetricInduction — learning "ravens are black", *not* "black things are ravens"

A WM-PLN-solid worked example of the directional asymmetry of inductive
inheritance (Hempel's raven paradox dissolved *dynamically*).

Induction is modeled as iterated **revision** (`revision = (+)` on
`BinaryEvidence`, the WM-calculus evidence-addition operation). Each observation
contributes one unit of evidence:

* **`raven → black`** — every observed raven is black, so each raven contributes
  `pos = 1`, `neg = 0`. After `R` ravens the evidence is `⟨R, 0⟩` and the strength
  is `R / R = 1`.
* **`black → raven`** — among black things, ravens are positive and black
  non-ravens are negative. After `R` black ravens and `M` black non-ravens the
  evidence is `⟨R, M⟩` and the strength is `R / (R + M)`, which **decays toward
  the base rate** as the number `M` of *other black items* grows.

The *same* observations feed both links; the asymmetry is purely a matter of
which count each observation lands in — exactly the base-rate dilution of the
inverse conditional. Crucially, `black → raven` is *well-evidenced* (total
`R + M` grows with `M`): we become *confident* that black things are mostly
*not* ravens.

This file gives both:

* a **dataset-level** presentation using finite lists of observations and
  iterated revision, showing the result depends only on the two sufficient
  counts;
* the familiar **closed-form** `R/M` presentation as a corollary.

`sorry`-free, `axiom`-free.
-/

namespace Mettapedia.Logic.RavenAsymmetricInduction

open scoped ENNReal
open scoped Topology
open Filter
open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.Logic.EvidenceQuantale.BinaryEvidence
open Mettapedia.Logic.PLNRevision

/-- Coordinatewise `pos` of a revision step (`+` is coordinatewise). -/
private theorem add_pos' (x y : BinaryEvidence) : (x + y).pos = x.pos + y.pos := rfl
/-- Coordinatewise `neg` of a revision step. -/
private theorem add_neg' (x y : BinaryEvidence) : (x + y).neg = x.neg + y.neg := rfl

/-! ## Per-observation evidence -/

/-- The two relevant observation kinds in the raven example. -/
inductive Observation where
  | blackRaven
  | blackNonRaven
  deriving DecidableEq, Repr

/-- One observed raven, which is black: positive evidence for *both*
`raven → black` and `black → raven`. -/
def blackRavenObs : BinaryEvidence := ⟨1, 0⟩

/-- One observed black thing that is *not* a raven: negative evidence for
`black → raven` (irrelevant to `raven → black`). -/
def blackNonRavenObs : BinaryEvidence := ⟨0, 1⟩

/-- `raven → black` evidence after `R` black ravens: `⟨R, 0⟩`. -/
def ravenBlackEvidence (R : ℕ) : BinaryEvidence := ⟨(R : ℝ≥0∞), 0⟩

/-- `black → raven` evidence after `R` black ravens and `M` black non-ravens: `⟨R, M⟩`. -/
def blackRavenEvidence (R M : ℕ) : BinaryEvidence := ⟨(R : ℝ≥0∞), (M : ℝ≥0∞)⟩

/-! ## Dataset-level observation semantics -/

/-- How many black ravens occur in the dataset. -/
def ravenCount (obs : List Observation) : ℕ := obs.count .blackRaven

/-- How many black non-ravens occur in the dataset. -/
def blackNonRavenCount (obs : List Observation) : ℕ := obs.count .blackNonRaven

/-- Total number of black observations in the dataset. -/
def blackObservationCount (obs : List Observation) : ℕ :=
  ravenCount obs + blackNonRavenCount obs

/-- Contribution of one observation to the forward link `raven → black`. -/
def ravenBlackContribution : Observation → BinaryEvidence
  | .blackRaven => blackRavenObs
  | .blackNonRaven => 0

/-- Contribution of one observation to the inverse link `black → raven`. -/
def blackRavenContribution : Observation → BinaryEvidence
  | .blackRaven => blackRavenObs
  | .blackNonRaven => blackNonRavenObs

/-- Aggregate evidence by iterated revision over a finite observation list. -/
noncomputable def aggregateStep (contribution : Observation → BinaryEvidence)
    (acc : BinaryEvidence) (obs : Observation) : BinaryEvidence :=
  revision acc (contribution obs)

/-- Aggregate evidence by iterated revision over a finite observation list. -/
noncomputable def aggregateEvidence (contribution : Observation → BinaryEvidence)
    (obs : List Observation) : BinaryEvidence :=
  obs.foldl (aggregateStep contribution) Mettapedia.Logic.EvidenceQuantale.BinaryEvidence.zero

/-- Canonical dataset with `R` black ravens and `M` black non-ravens. -/
def ravenObservationDataset (R M : ℕ) : List Observation :=
  List.replicate R .blackRaven ++ List.replicate M .blackNonRaven

/-! ## Induction = iterated revision (one observation per step)

These show the closed forms above really are produced by revising in one
observation at a time. -/

theorem ravenBlackEvidence_succ (R : ℕ) :
    ravenBlackEvidence (R + 1) = revision (ravenBlackEvidence R) blackRavenObs := by
  apply ext'
  · simp only [revision, add_pos', ravenBlackEvidence, blackRavenObs, Nat.cast_succ]
  · simp only [revision, add_neg', ravenBlackEvidence, blackRavenObs, add_zero]

theorem blackRavenEvidence_succ_raven (R M : ℕ) :
    blackRavenEvidence (R + 1) M = revision (blackRavenEvidence R M) blackRavenObs := by
  apply ext'
  · simp only [revision, add_pos', blackRavenEvidence, blackRavenObs, Nat.cast_succ]
  · simp only [revision, add_neg', blackRavenEvidence, blackRavenObs, add_zero]

theorem blackRavenEvidence_succ_nonraven (R M : ℕ) :
    blackRavenEvidence R (M + 1) = revision (blackRavenEvidence R M) blackNonRavenObs := by
  apply ext'
  · simp only [revision, add_pos', blackRavenEvidence, blackNonRavenObs, add_zero]
  · simp only [revision, add_neg', blackRavenEvidence, blackNonRavenObs, Nat.cast_succ]

private theorem aggregate_ravenBlack_aux (obs : List Observation) (R : ℕ) :
    obs.foldl (aggregateStep ravenBlackContribution) (ravenBlackEvidence R) =
      ravenBlackEvidence (R + ravenCount obs) := by
  induction obs generalizing R with
  | nil =>
      simp [ravenCount, ravenBlackEvidence]
  | cons o os ih =>
      cases o with
      | blackRaven =>
          simp [aggregateStep, ravenCount, ravenBlackContribution]
          rw [← ravenBlackEvidence_succ R]
          simpa [ravenCount, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using ih (R + 1)
      | blackNonRaven =>
          simpa [aggregateStep, ravenCount, ravenBlackContribution] using ih R

/-- The forward-link aggregate depends only on the number of ravens observed. -/
theorem aggregate_ravenBlack_eq_count (obs : List Observation) :
    aggregateEvidence ravenBlackContribution obs = ravenBlackEvidence (ravenCount obs) := by
  unfold aggregateEvidence
  simpa [ravenBlackEvidence, Mettapedia.Logic.EvidenceQuantale.BinaryEvidence.zero]
    using aggregate_ravenBlack_aux obs 0

private theorem aggregate_blackRaven_aux (obs : List Observation) (R M : ℕ) :
    obs.foldl (aggregateStep blackRavenContribution) (blackRavenEvidence R M) =
      blackRavenEvidence (R + ravenCount obs) (M + blackNonRavenCount obs) := by
  induction obs generalizing R M with
  | nil =>
      simp [ravenCount, blackNonRavenCount, blackRavenEvidence]
  | cons o os ih =>
      cases o with
      | blackRaven =>
          simp [aggregateStep, ravenCount, blackNonRavenCount, blackRavenContribution]
          rw [← blackRavenEvidence_succ_raven R M]
          simpa [ravenCount, blackNonRavenCount, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
            using ih (R + 1) M
      | blackNonRaven =>
          simp [aggregateStep, ravenCount, blackNonRavenCount, blackRavenContribution]
          rw [← blackRavenEvidence_succ_nonraven R M]
          simpa [ravenCount, blackNonRavenCount, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
            using ih R (M + 1)

/-- The inverse-link aggregate depends only on raven count and other-black count. -/
theorem aggregate_blackRaven_eq_counts (obs : List Observation) :
    aggregateEvidence blackRavenContribution obs =
      blackRavenEvidence (ravenCount obs) (blackNonRavenCount obs) := by
  unfold aggregateEvidence
  simpa [blackRavenEvidence, Mettapedia.Logic.EvidenceQuantale.BinaryEvidence.zero]
    using aggregate_blackRaven_aux obs 0 0

/-- The total number of black observations is exactly the dataset length. -/
theorem blackObservationCount_eq_length (obs : List Observation) :
    blackObservationCount obs = obs.length := by
  induction obs with
  | nil =>
      simp [blackObservationCount, ravenCount, blackNonRavenCount]
  | cons o os ih =>
      cases o with
      | blackRaven =>
          simp [blackObservationCount, ravenCount, blackNonRavenCount]
          calc
            List.count Observation.blackRaven os + 1 + List.count Observation.blackNonRaven os
                = (List.count Observation.blackRaven os + List.count Observation.blackNonRaven os) + 1 := by omega
            _ = os.length + 1 := by
              simpa [blackObservationCount, ravenCount, blackNonRavenCount,
                Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using congrArg Nat.succ ih
      | blackNonRaven =>
          simp [blackObservationCount, ravenCount, blackNonRavenCount]
          calc
            List.count Observation.blackRaven os + (List.count Observation.blackNonRaven os + 1)
                = (List.count Observation.blackRaven os + List.count Observation.blackNonRaven os) + 1 := by omega
            _ = os.length + 1 := by
              simpa [blackObservationCount, ravenCount, blackNonRavenCount,
                Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using congrArg Nat.succ ih

/-- Reordering the observations does not change the forward aggregate. -/
theorem aggregate_ravenBlack_perm (obs₁ obs₂ : List Observation) (hperm : obs₁.Perm obs₂) :
    aggregateEvidence ravenBlackContribution obs₁ =
      aggregateEvidence ravenBlackContribution obs₂ := by
  rw [aggregate_ravenBlack_eq_count, aggregate_ravenBlack_eq_count]
  exact congrArg ravenBlackEvidence (by simpa [ravenCount] using hperm.count_eq Observation.blackRaven)

/-- Reordering the observations does not change the inverse aggregate. -/
theorem aggregate_blackRaven_perm (obs₁ obs₂ : List Observation) (hperm : obs₁.Perm obs₂) :
    aggregateEvidence blackRavenContribution obs₁ =
      aggregateEvidence blackRavenContribution obs₂ := by
  rw [aggregate_blackRaven_eq_counts, aggregate_blackRaven_eq_counts]
  exact congrArg₂ blackRavenEvidence
    (by simpa [ravenCount] using hperm.count_eq Observation.blackRaven)
    (by simpa [blackNonRavenCount] using hperm.count_eq Observation.blackNonRaven)

private theorem ravenCount_replicate_blackNonRaven (M : ℕ) :
    ravenCount (List.replicate M Observation.blackNonRaven) = 0 := by
  unfold ravenCount
  rw [List.count_replicate]
  simp

private theorem blackNonRavenCount_replicate_blackRaven (R : ℕ) :
    blackNonRavenCount (List.replicate R Observation.blackRaven) = 0 := by
  unfold blackNonRavenCount
  rw [List.count_replicate]
  simp

theorem ravenCount_ravenObservationDataset (R M : ℕ) :
    ravenCount (ravenObservationDataset R M) = R := by
  unfold ravenObservationDataset ravenCount
  rw [List.count_append]
  rw [List.count_replicate]
  rw [List.count_replicate]
  simp

theorem blackNonRavenCount_ravenObservationDataset (R M : ℕ) :
    blackNonRavenCount (ravenObservationDataset R M) = M := by
  unfold ravenObservationDataset blackNonRavenCount
  rw [List.count_append]
  rw [List.count_replicate]
  rw [List.count_replicate]
  simp

/-- The canonical `R/M` dataset yields the forward closed form. -/
theorem aggregate_ravenBlack_ravenObservationDataset (R M : ℕ) :
    aggregateEvidence ravenBlackContribution (ravenObservationDataset R M) =
      ravenBlackEvidence R := by
  rw [aggregate_ravenBlack_eq_count]
  rw [ravenCount_ravenObservationDataset]

/-- The canonical `R/M` dataset yields the inverse closed form. -/
theorem aggregate_blackRaven_ravenObservationDataset (R M : ℕ) :
    aggregateEvidence blackRavenContribution (ravenObservationDataset R M) =
      blackRavenEvidence R M := by
  rw [aggregate_blackRaven_eq_counts]
  rw [ravenCount_ravenObservationDataset, blackNonRavenCount_ravenObservationDataset]

/-! ## Totals (confidence): `black → raven` is well-evidenced -/

theorem total_ravenBlack (R : ℕ) : (ravenBlackEvidence R).total = (R : ℝ≥0∞) := by
  simp [ravenBlackEvidence, total]

theorem total_blackRaven (R M : ℕ) :
    (blackRavenEvidence R M).total = (R : ℝ≥0∞) + (M : ℝ≥0∞) := by
  simp [blackRavenEvidence, total]

/-- With fixed ravens, more black non-ravens means more total evidence and hence
more confidence in the inverse estimate. -/
theorem confidence_blackRaven_monotone (κ : ℝ≥0∞)
    (hκ_pos : κ ≠ 0) (hκ_top : κ ≠ ⊤)
    (R M M' : ℕ) (hMM : M ≤ M') :
    BinaryEvidence.toConfidence κ (blackRavenEvidence R M) ≤
      BinaryEvidence.toConfidence κ (blackRavenEvidence R M') := by
  apply BinaryEvidence.confidence_monotone_in_total
  · exact hκ_pos
  · exact hκ_top
  · rw [total_blackRaven]
    simp
  · rw [total_blackRaven, total_blackRaven]
    gcongr

/-! ## The strengths -/

/-- "ravens are black" converges to strength `1`. -/
theorem strength_ravenBlack (R : ℕ) (hR : 0 < R) :
    toStrength (ravenBlackEvidence R) = 1 := by
  have hR0 : (R : ℝ≥0∞) ≠ 0 := by exact_mod_cast hR.ne'
  unfold toStrength
  rw [total_ravenBlack, if_neg hR0]
  show (ravenBlackEvidence R).pos / (R : ℝ≥0∞) = 1
  simp only [ravenBlackEvidence]
  exact ENNReal.div_self hR0 (ENNReal.natCast_ne_top R)

/-- "black things are ravens" has strength `R / (R + M)` — the inverse
conditional, diluted by every black non-raven. -/
theorem strength_blackRaven (R M : ℕ) (h : 0 < R + M) :
    toStrength (blackRavenEvidence R M) = (R : ℝ≥0∞) / ((R : ℝ≥0∞) + (M : ℝ≥0∞)) := by
  have hne : ((R : ℝ≥0∞) + (M : ℝ≥0∞)) ≠ 0 := by
    have : (0 : ℝ≥0∞) < (R : ℝ≥0∞) + (M : ℝ≥0∞) := by exact_mod_cast h
    exact this.ne'
  unfold toStrength
  rw [total_blackRaven, if_neg hne]
  simp only [blackRavenEvidence]

/-- Dataset-level forward strength: every observed raven supports `raven → black`. -/
theorem strength_ravenBlack_of_observations (obs : List Observation)
    (hR : 0 < ravenCount obs) :
    toStrength (aggregateEvidence ravenBlackContribution obs) = 1 := by
  rw [aggregate_ravenBlack_eq_count]
  exact strength_ravenBlack (ravenCount obs) hR

/-- Dataset-level inverse strength: black non-ravens dilute `black → raven`. -/
theorem strength_blackRaven_of_observations (obs : List Observation)
    (h : 0 < blackObservationCount obs) :
    toStrength (aggregateEvidence blackRavenContribution obs) =
      (ravenCount obs : ℝ≥0∞) /
        ((ravenCount obs : ℝ≥0∞) + (blackNonRavenCount obs : ℝ≥0∞)) := by
  rw [aggregate_blackRaven_eq_counts]
  exact strength_blackRaven (ravenCount obs) (blackNonRavenCount obs) (by simpa [blackObservationCount] using h)

/-! ## The asymmetry -/

/-- More *other black items* ⇒ lower `black → raven` strength (base-rate dilution). -/
theorem strength_blackRaven_antitone (R M M' : ℕ) (hR : 0 < R) (hMM : M ≤ M') :
    toStrength (blackRavenEvidence R M') ≤ toStrength (blackRavenEvidence R M) := by
  rw [strength_blackRaven R M' (by omega), strength_blackRaven R M (by omega)]
  gcongr

/-- With at least one other black item, `black → raven` is strictly below `1`. -/
theorem strength_blackRaven_lt_one (R M : ℕ) (hR : 0 < R) (hM : 0 < M) :
    toStrength (blackRavenEvidence R M) < 1 := by
  rw [strength_blackRaven R M (by omega)]
  rw [ENNReal.div_lt_iff (Or.inr (by exact_mod_cast hR.ne')) (Or.inr (ENNReal.natCast_ne_top R)),
    one_mul]
  exact_mod_cast (by omega : R < R + M)

/-- **The asymmetry**: after seeing `R` black ravens and `M ≥ 1` other black
items, induction holds `raven → black` at strength `1` while `black → raven`
sits strictly below it. -/
theorem raven_black_strictly_stronger (R M : ℕ) (hR : 0 < R) (hM : 0 < M) :
    toStrength (blackRavenEvidence R M) < toStrength (ravenBlackEvidence R) := by
  rw [strength_ravenBlack R hR]
  exact strength_blackRaven_lt_one R M hR hM

/-- Dataset-level asymmetry: enough ravens and at least one other black item
force the inverse link strictly below the forward link. -/
theorem raven_black_strictly_stronger_of_observations (obs : List Observation)
    (hR : 0 < ravenCount obs) (hM : 0 < blackNonRavenCount obs) :
    toStrength (aggregateEvidence blackRavenContribution obs) <
      toStrength (aggregateEvidence ravenBlackContribution obs) := by
  rw [aggregate_blackRaven_eq_counts, aggregate_ravenBlack_eq_count]
  exact raven_black_strictly_stronger (ravenCount obs) (blackNonRavenCount obs) hR hM

/-! ## Convergence: the inverse conditional vanishes -/

/-- As the number `M` of *other black items* grows without bound, the
`black → raven` strength `R / (R + M)` tends to `0`. So the asymmetry gap
`1 - R/(R+M)` tends to `1`: in the limit "ravens are black" is certain while
"black things are ravens" is fully diluted to the base rate. -/
theorem strength_blackRaven_tendsto_zero (R : ℕ) (hR : 0 < R) :
    Tendsto (fun M : ℕ => toStrength (blackRavenEvidence R M)) atTop (𝓝 0) := by
  have hf : ∀ M : ℕ, toStrength (blackRavenEvidence R M) ≠ ⊤ := by
    intro M
    rw [strength_blackRaven R M (by omega)]
    refine ENNReal.div_ne_top (ENNReal.natCast_ne_top R) ?_
    have : (0 : ℝ≥0∞) < (R : ℝ≥0∞) + (M : ℝ≥0∞) := by exact_mod_cast (by omega : 0 < R + M)
    exact this.ne'
  rw [← ENNReal.tendsto_toReal_iff hf (by simp)]
  have hcoe : (fun M : ℕ => (toStrength (blackRavenEvidence R M)).toReal)
      = fun M : ℕ => (R : ℝ) / ((R : ℝ) + (M : ℝ)) := by
    funext M
    rw [strength_blackRaven R M (by omega), ENNReal.toReal_div,
      ENNReal.toReal_add (ENNReal.natCast_ne_top R) (ENNReal.natCast_ne_top M),
      ENNReal.toReal_natCast, ENNReal.toReal_natCast]
  simp only [ENNReal.toReal_zero, hcoe]
  have hg : Tendsto (fun M : ℕ => (R : ℝ) + (M : ℝ)) atTop atTop :=
    tendsto_atTop_add_const_left atTop (R : ℝ) tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun M : ℕ => ((R : ℝ) + (M : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hg
  have hmul := hinv.const_mul (R : ℝ)
  simpa [div_eq_mul_inv, mul_zero] using hmul

/-! ## Concrete worked example: 5 black ravens vs. 95 other black items -/

/-- The concrete worked dataset that drives the standard `5/95` raven example. -/
def positiveExampleDataset : List Observation := ravenObservationDataset 5 95

/-- The dataset-level aggregation reproduces the `5/95` forward closed form. -/
example :
    aggregateEvidence ravenBlackContribution positiveExampleDataset = ravenBlackEvidence 5 := by
  simpa [positiveExampleDataset] using aggregate_ravenBlack_ravenObservationDataset 5 95

/-- The dataset-level aggregation reproduces the `5/95` inverse closed form. -/
example :
    aggregateEvidence blackRavenContribution positiveExampleDataset =
      blackRavenEvidence 5 95 := by
  simpa [positiveExampleDataset] using aggregate_blackRaven_ravenObservationDataset 5 95

/-- `raven → black` is fully confirmed. -/
example : toStrength (ravenBlackEvidence 5) = 1 := strength_ravenBlack 5 (by norm_num)

/-- `black → raven` has decayed to `5 / 100` — and keeps dropping with more black
non-ravens (`5 / 1000` at `M = 995`). -/
example :
    toStrength (blackRavenEvidence 5 995) ≤ toStrength (blackRavenEvidence 5 95) :=
  strength_blackRaven_antitone 5 95 995 (by norm_num) (by norm_num)

/-- The headline asymmetry, concretely. -/
example : toStrength (blackRavenEvidence 5 95) < toStrength (ravenBlackEvidence 5) :=
  raven_black_strictly_stronger 5 95 (by norm_num) (by norm_num)

/-- The same headline asymmetry, phrased at the dataset level. -/
example :
    toStrength (aggregateEvidence blackRavenContribution positiveExampleDataset) <
      toStrength (aggregateEvidence ravenBlackContribution positiveExampleDataset) := by
  simpa [positiveExampleDataset] using
    raven_black_strictly_stronger_of_observations
      (ravenObservationDataset 5 95)
      (by
        rw [ravenCount_ravenObservationDataset]
        norm_num)
      (by
        rw [blackNonRavenCount_ravenObservationDataset]
        norm_num)

end Mettapedia.Logic.RavenAsymmetricInduction
