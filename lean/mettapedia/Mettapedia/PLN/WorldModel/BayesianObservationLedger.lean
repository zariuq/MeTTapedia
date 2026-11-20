import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Probability.Kernel.WithDensity
import Mathlib.Probability.Kernel.Posterior
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mettapedia.ProbabilityTheory.BayesianInference.Basic

/-!
# Bayesian observation ledgers over measurable worlds

Event identity controls replay; likelihood meanings and observed payloads are
fixed by the supplied observation model. A new event carries a likelihood conditional
on the entire recorded history; no independence follows from distinct names.
The operational ledger denotes an unnormalized measure. Its observation step
commutes with density updating, and normalization is permitted only at positive
finite mass. Kernel scoring gives the same interpretation for an input-indexed
program. Regular conditional distributions handle observations with zero
singleton mass without conditioning on a null event by division.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.PLN.WorldModel.BayesianObservationLedger

open MeasureTheory
open scoped ENNReal _root_.ProbabilityTheory

variable {Ω Event : Type*} [MeasurableSpace Ω]

/-- History is newest first. The likelihood of a fresh event may depend on
all older event identities. Observed payloads are fixed by the supplied
likelihood interpretation; changing that interpretation requires a new model. -/
structure ObservationModel (Ω Event : Type*) [MeasurableSpace Ω] where
  likelihood : List Event → Event → Ω → ℝ≥0∞
  measurable : ∀ history event, Measurable (likelihood history event)

namespace ObservationModel

variable (model : ObservationModel Ω Event)

def density (model : ObservationModel Ω Event) : List Event → Ω → ℝ≥0∞
  | [] => fun _ => 1
  | event :: history => fun world =>
      density model history world * model.likelihood history event world

theorem density_measurable (history : List Event) : Measurable (model.density history) := by
  induction history with
  | nil => exact measurable_const
  | cons event history ih => exact ih.mul (model.measurable history event)

/-- Incorporating an already recorded event is an explicit no-op. -/
def record [DecidableEq Event] (history : List Event) (event : Event) : List Event :=
  if event ∈ history then history else event :: history

theorem record_replay [DecidableEq Event] (history : List Event) (event : Event)
    (seen : event ∈ history) : record history event = history := if_pos seen

theorem record_nodup [DecidableEq Event] (history : List Event) (event : Event)
    (unique : history.Nodup) : (record history event).Nodup := by
  unfold record
  split
  · exact unique
  · exact List.nodup_cons.mpr ⟨by assumption, unique⟩

def denote (prior : Measure Ω) (history : List Event) : Measure Ω :=
  prior.withDensity (model.density history)

/-- The semantic square for a fresh observation, with its conditional
likelihood evaluated at the actual preceding history. -/
theorem denote_record_new [DecidableEq Event] (prior : Measure Ω)
    (history : List Event) (event : Event) (fresh : event ∉ history) :
    model.denote prior (record history event) =
      (model.denote prior history).withDensity (model.likelihood history event) := by
  rw [record, if_neg fresh]
  exact withDensity_mul prior (model.density_measurable history)
    (model.measurable history event)

theorem denote_record_replay [DecidableEq Event] (prior : Measure Ω)
    (history : List Event) (event : Event) (seen : event ∈ history) :
    model.denote prior (record history event) = model.denote prior history := by
  rw [record_replay history event seen]

/-- Independence is a factorization obligation on the conditional likelihood,
not a consequence of `first ≠ second`. -/
theorem independent_pair (first second : Event)
    (factor : model.likelihood [first] second = model.likelihood [] second) :
    model.density [second, first] = fun world =>
      model.likelihood [] first world * model.likelihood [] second world := by
  funext world
  simp only [density, one_mul, factor]

end ObservationModel

def normalize (measure : Measure Ω) : Measure Ω := (measure Set.univ)⁻¹ • measure

def posterior? (measure : Measure Ω) : Option (Measure Ω) :=
  if measure Set.univ = 0 ∨ measure Set.univ = ∞ then none else some (normalize measure)

theorem normalize_probability (measure : Measure Ω)
    (positive : measure Set.univ ≠ 0) (finite : measure Set.univ ≠ ∞) :
    IsProbabilityMeasure (normalize measure) := by
  constructor
  simp only [normalize, Measure.smul_apply, smul_eq_mul]
  exact ENNReal.inv_mul_cancel positive finite

theorem normalize_scale (measure : Measure Ω) (weight : ℝ≥0∞)
    (positive : weight ≠ 0) (finite : weight ≠ ∞) :
    normalize (weight • measure) = normalize measure := by
  simp only [normalize, Measure.smul_apply, smul_eq_mul, smul_smul]
  rw [ENNReal.mul_inv (Or.inl positive) (Or.inl finite)]
  congr 1
  calc
    (weight⁻¹ * (measure Set.univ)⁻¹) * weight =
        (weight⁻¹ * weight) * (measure Set.univ)⁻¹ := by ac_rfl
    _ = (measure Set.univ)⁻¹ := by rw [ENNReal.inv_mul_cancel positive finite, one_mul]

/-- Normalizing between observations does not change the final posterior.
The side conditions concern the preceding mass; the final posterior is still
admitted separately by `posterior?`. -/
theorem normalized_update (measure : Measure Ω) (likelihood : Ω → ℝ≥0∞)
    (positive : measure Set.univ ≠ 0) (finite : measure Set.univ ≠ ∞) :
    normalize ((normalize measure).withDensity likelihood) =
      normalize (measure.withDensity likelihood) := by
  change normalize (((measure Set.univ)⁻¹ • measure).withDensity likelihood) = _
  rw [withDensity_smul_measure]
  exact normalize_scale _ _ (ENNReal.inv_ne_zero.mpr finite) (ENNReal.inv_ne_top.mpr positive)

theorem posterior_record_new [DecidableEq Event] (model : ObservationModel Ω Event)
    (prior : Measure Ω) (history : List Event) (event : Event) (fresh : event ∉ history) :
    posterior? (model.denote prior (ObservationModel.record history event)) =
      posterior? ((model.denote prior history).withDensity (model.likelihood history event)) := by
  rw [model.denote_record_new prior history event fresh]

theorem posterior_record_replay [DecidableEq Event] (model : ObservationModel Ω Event)
    (prior : Measure Ω) (history : List Event) (event : Event) (seen : event ∈ history) :
    posterior? (model.denote prior (ObservationModel.record history event)) =
      posterior? (model.denote prior history) := by
  rw [model.denote_record_replay prior history event seen]

/-- An input-indexed generative program is a kernel. Scoring its output
agrees pointwise with scoring its measure denotation. -/
theorem kernel_score {Input : Type*} [MeasurableSpace Input]
    (program : ProbabilityTheory.Kernel Input Ω) [ProbabilityTheory.IsSFiniteKernel program]
    (likelihood : Input → Ω → ℝ≥0∞) (measurable : Measurable (Function.uncurry likelihood))
    (input : Input) :
    ProbabilityTheory.Kernel.withDensity program likelihood input =
      (program input).withDensity (likelihood input) :=
  ProbabilityTheory.Kernel.withDensity_apply program measurable input

/-- Likelihood ratios relative to the observation marginal give a ledger
interpretation of regular conditioning. Unlike a fixed base density, this
ratio already includes the Bayes normalizing factor almost everywhere. -/
def kernelModel {Y : Type*} [MeasurableSpace Y]
    [MeasurableSpace.CountableOrCountablyGenerated Ω Y]
    (program : ProbabilityTheory.Kernel Ω Y) [ProbabilityTheory.IsFiniteKernel program]
    (prior : Measure Ω) [IsFiniteMeasure prior] : ObservationModel Ω Y where
  likelihood _ observation world := program.rnDeriv
    (ProbabilityTheory.Kernel.const Ω (program ∘ₘ prior)) world observation
  measurable _ _observation :=
    (ProbabilityTheory.Kernel.measurable_rnDeriv program _).comp
      (measurable_id.prodMk measurable_const)

/-- The ledger posterior is the independently constructed regular conditional
kernel, almost everywhere under the observation marginal. No uniqueness at
an individual null observation is asserted. -/
theorem ledger_regular_conditional {Y : Type*} [MeasurableSpace Y]
    [StandardBorelSpace Ω] [Nonempty Ω]
    [MeasurableSpace.CountableOrCountablyGenerated Ω Y]
    (program : ProbabilityTheory.Kernel Ω Y) [ProbabilityTheory.IsFiniteKernel program]
    (prior : Measure Ω) [IsFiniteMeasure prior]
    (dominated : ∀ᵐ world ∂prior, program world ≪ program ∘ₘ prior) :
    ∀ᵐ observation ∂(program ∘ₘ prior),
      posterior? ((kernelModel program prior).denote prior [observation]) =
        some (ProbabilityTheory.posterior program prior observation) := by
  filter_upwards [ProbabilityTheory.posterior_eq_withDensity dominated] with observation bayes
  have denote : (kernelModel program prior).denote prior [observation] =
      ProbabilityTheory.posterior program prior observation := by
    simpa [ObservationModel.denote, ObservationModel.density, kernelModel] using bayes.symm
  rw [denote]
  simp [posterior?, normalize, measure_univ]

end Mettapedia.PLN.WorldModel.BayesianObservationLedger
