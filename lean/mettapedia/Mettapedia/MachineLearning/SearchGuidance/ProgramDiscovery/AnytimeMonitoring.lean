import Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery.PairedDesignEstimands
import Mettapedia.PLN.Evidence.BinEvNat
import Mathlib.Probability.Martingale.OptionalStopping

/-!
# Anytime-valid monitoring of sequential discovery campaigns

Campaign results become visible in their registered artifact order.  The
corresponding information state is therefore the natural filtration of that
declared stream, rather than a filtration selected after seeing the results.

An e-process is represented by its standard mathematical contract: a
nonnegative supermartingale starting at one.  The bounded optional-stopping
theorem below is inherited from Mathlib's optional-stopping theorem, not added
as a field.  Consequently, an adapted decision to stop after an encouraging
generation cannot increase its expected e-value above one under the null.

The final section records a counts-primal likelihood-ratio chart.  Its state is
the existing PLN `(n⁺, n⁻)` register; the real-valued e-value is derived from
those counts.
-/

namespace Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery

open MeasureTheory ProbabilityTheory
open Mettapedia.PLN.Evidence
open scoped ENNReal NNReal MeasureTheory ProbabilityTheory

universe uOmega uIncrement uWorld uArm

/-! ## The declared observation order -/

/-- The key whose artifact becomes visible at one monitoring step.  `ordinal`
is the registered total order within a generation (for example the fixed arm
order), so the filtration cannot be rearranged after observing outcomes. -/
structure CampaignArtifactKey (World : Type uWorld) (Arm : Type uArm) where
  world : World
  generation : ℕ
  ordinal : ℕ
  arm : Arm

/-- A campaign stream and the exact registered key revealed at every step.
The measurability proof is operational input: it says each increment is an
observable artifact, not hidden future state. -/
structure DeclaredCampaignStream
    (Ω : Type uOmega) [MeasurableSpace Ω]
    (Increment : Type uIncrement) [TopologicalSpace Increment]
    [TopologicalSpace.MetrizableSpace Increment]
    [MeasurableSpace Increment] [BorelSpace Increment]
    (World : Type uWorld) (Arm : Type uArm) where
  key : ℕ → CampaignArtifactKey World Arm
  reveal : ℕ → Ω → Increment
  reveal_stronglyMeasurable : ∀ n, StronglyMeasurable (reveal n)

namespace DeclaredCampaignStream

variable {Ω : Type uOmega} [MeasurableSpace Ω]
variable {Increment : Type uIncrement} [TopologicalSpace Increment]
variable [TopologicalSpace.MetrizableSpace Increment]
variable [MeasurableSpace Increment] [BorelSpace Increment]
variable {World : Type uWorld} {Arm : Type uArm}

/-- The smallest filtration revealing the registered campaign artifacts in
their declared order. -/
def filtration
    (stream : DeclaredCampaignStream Ω Increment World Arm) :
    Filtration ℕ ‹MeasurableSpace Ω› :=
  Filtration.natural stream.reveal stream.reveal_stronglyMeasurable

/-- Every registered artifact is measurable when its own monitoring step is
reached. -/
theorem reveal_stronglyAdapted
    (stream : DeclaredCampaignStream Ω Increment World Arm) :
    StronglyAdapted stream.filtration stream.reveal := by
  exact Filtration.stronglyAdapted_natural stream.reveal_stronglyMeasurable

end DeclaredCampaignStream

/-! ## E-process and optional stopping -/

/-- A nonnegative supermartingale initialized at one.  Optional-stopping
validity is intentionally not a field of this structure. -/
structure EProcess
    {Ω : Type uOmega} [MeasurableSpace Ω]
    (μ : Measure Ω) (𝓕 : Filtration ℕ ‹MeasurableSpace Ω›)
    (value : ℕ → Ω → ℝ) : Prop where
  supermartingale : Supermartingale value 𝓕 μ
  nonnegative : ∀ n, 0 ≤ᵐ[μ] value n
  initial : value 0 =ᵐ[μ] fun _ ↦ 1

namespace EProcess

variable {Ω : Type uOmega} [MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {𝓕 : Filtration ℕ ‹MeasurableSpace Ω›}
variable {value : ℕ → Ω → ℝ}

/-- Bounded optional stopping for an e-process.  The stopping rule may depend
on everything revealed so far, but not on future artifacts. -/
theorem expected_stoppedValue_le_one
    (hE : EProcess μ 𝓕 value)
    (τ : Ω → WithTop ℕ) (hτ : IsStoppingTime 𝓕 τ)
    {horizon : ℕ} (hbounded : ∀ ω, τ ω ≤ horizon) :
    (∫ ω, stoppedValue value τ ω ∂μ) ≤ 1 := by
  have hmono := hE.supermartingale.neg.expected_stoppedValue_mono
    (isStoppingTime_const 𝓕 0) hτ (fun _ ↦ by exact bot_le) hbounded
  have hinitial : (∫ ω, value 0 ω ∂μ) = 1 := by
    calc
      (∫ ω, value 0 ω ∂μ) = ∫ _ : Ω, (1 : ℝ) ∂μ := integral_congr_ae hE.initial
      _ = 1 := by simp
  have hnegInitial : (∫ ω, -value 0 ω ∂μ) = -1 := by
    rw [integral_neg, hinitial]
  have hnegStopped :
      (∫ ω, stoppedValue (-value) τ ω ∂μ) =
        -(∫ ω, stoppedValue value τ ω ∂μ) := by
    change (∫ ω, -stoppedValue value τ ω ∂μ) =
      -(∫ ω, stoppedValue value τ ω ∂μ)
    exact integral_neg _
  have hnegInitial' : (∫ ω, (-value) 0 ω ∂μ) = -1 := by
    simpa only [Pi.neg_apply] using hnegInitial
  rw [stoppedValue_const, hnegInitial', hnegStopped] at hmono
  linarith

/-- Fixed-horizon monitoring is the constant-stopping-time special case. -/
theorem expected_value_le_one
    (hE : EProcess μ 𝓕 value) (n : ℕ) :
    (∫ ω, value n ω ∂μ) ≤ 1 := by
  have hUntop : (n : WithTop ℕ).untopA = n := by
    change (WithTop.some n).untopA = n
    rfl
  simpa [stoppedValue, hUntop] using
    hE.expected_stoppedValue_le_one (fun _ ↦ (n : WithTop ℕ))
    (isStoppingTime_const 𝓕 n) (horizon := n) (fun _ ↦ by simp)

end EProcess

section DeclaredCampaignValidity

variable {Ω : Type uOmega} [MeasurableSpace Ω]
variable {Increment : Type uIncrement} [TopologicalSpace Increment]
variable [TopologicalSpace.MetrizableSpace Increment]
variable [MeasurableSpace Increment] [BorelSpace Increment]
variable {World : Type uWorld} {Arm : Type uArm}
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Optional-stopping validity specialized to the natural filtration of the
registered campaign stream.  This theorem is the explicit join between the
artifact order and the e-process result. -/
theorem DeclaredCampaignStream.expected_stoppedValue_le_one
    (stream : DeclaredCampaignStream Ω Increment World Arm)
    {value : ℕ → Ω → ℝ}
    (hE : EProcess μ stream.filtration value)
    (τ : Ω → WithTop ℕ) (hτ : IsStoppingTime stream.filtration τ)
    {horizon : ℕ} (hbounded : ∀ ω, τ ω ≤ horizon) :
    (∫ ω, stoppedValue value τ ω ∂μ) ≤ 1 :=
  hE.expected_stoppedValue_le_one τ hτ hbounded

end DeclaredCampaignValidity

/-! ## Counts-primal likelihood-ratio chart -/

/-- The e-value chart derived from a PLN count register for a Bernoulli null
rate `p` and alternative rate `q`. -/
noncomputable def countLikelihoodEValue
    (p q : ℝ) (counts : BinEvNat) : ℝ :=
  (q / p) ^ counts.pos * ((1 - q) / (1 - p)) ^ counts.neg

@[simp]
theorem countLikelihoodEValue_zero (p q : ℝ) :
    countLikelihoodEValue p q 0 = 1 := by
  change (q / p) ^ 0 * ((1 - q) / (1 - p)) ^ 0 = 1
  simp

/-- Counts addition is multiplication in the derived e-value chart. -/
theorem countLikelihoodEValue_add (p q : ℝ) (left right : BinEvNat) :
    countLikelihoodEValue p q (left + right) =
      countLikelihoodEValue p q left * countLikelihoodEValue p q right := by
  cases left with
  | mk leftPos leftNeg =>
    cases right with
    | mk rightPos rightNeg =>
      change
        (q / p) ^ (leftPos + rightPos) *
            ((1 - q) / (1 - p)) ^ (leftNeg + rightNeg) =
          ((q / p) ^ leftPos * ((1 - q) / (1 - p)) ^ leftNeg) *
            ((q / p) ^ rightPos * ((1 - q) / (1 - p)) ^ rightNeg)
      rw [pow_add, pow_add]
      ring

/-- One Bernoulli likelihood-ratio factor has conditional mean one under the
declared null.  This is the local fairness equation that turns sequential
count accumulation into an e-process when the conditional null rate is `p`. -/
theorem bernoulliLikelihoodFactor_nullMean
    (p q : ℝ) (hp : p ≠ 0) (hp1 : 1 - p ≠ 0) :
    p * (q / p) + (1 - p) * ((1 - q) / (1 - p)) = 1 := by
  field_simp
  ring

/-- A counts-primal monitor retains its WM-PLN register as primary state and
exposes the e-value only as a derived chart. -/
structure CountsPrimalMonitor
    {Ω : Type uOmega} [MeasurableSpace Ω]
    (μ : Measure Ω) (𝓕 : Filtration ℕ ‹MeasurableSpace Ω›) where
  nullRate : ℝ
  alternativeRate : ℝ
  counts : ℕ → Ω → BinEvNat
  eProcess : EProcess μ 𝓕
    (fun n ω ↦ countLikelihoodEValue nullRate alternativeRate (counts n ω))

namespace CountsPrimalMonitor

variable {Ω : Type uOmega} [MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {𝓕 : Filtration ℕ ‹MeasurableSpace Ω›}

/-- Anytime validity transported directly from the e-process theorem while
the operational monitor state remains `(n⁺, n⁻)`. -/
theorem expected_stoppedChart_le_one
    (monitor : CountsPrimalMonitor μ 𝓕)
    (τ : Ω → WithTop ℕ) (hτ : IsStoppingTime 𝓕 τ)
    {horizon : ℕ} (hbounded : ∀ ω, τ ω ≤ horizon) :
    (∫ ω, stoppedValue
      (fun n ω ↦ countLikelihoodEValue monitor.nullRate monitor.alternativeRate
        (monitor.counts n ω)) τ ω ∂μ) ≤ 1 :=
  monitor.eProcess.expected_stoppedValue_le_one τ hτ hbounded

end CountsPrimalMonitor

end Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery
