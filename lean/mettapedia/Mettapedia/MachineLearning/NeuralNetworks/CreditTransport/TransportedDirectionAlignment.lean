import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.DirectionalTaskDescent

/-!
# Credit-mechanism telemetry

This module gives BP-relation measurements a precise but deliberately limited
role.  A sample carries the raw local credit, the matched BP task gradient, the
direction that parameter transport actually subtracts, and two distinct time
coordinates.  Cosine and norm ratio refuse zero denominators.

Raw-credit alignment is mechanism telemetry.  Finite task descent belongs to
the transported direction together with a directional task model and a step
budget; a counterexample below shows why these claims must not be conflated.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace TransportedDirectionAlignment

open scoped InnerProductSpace
open DirectionalTaskDescent

variable {Parameter : Type*}
  [NormedAddCommGroup Parameter] [InnerProductSpace ℝ Parameter]

/-- One authenticated mechanism observation at a declared relaxation time. -/
structure Sample (Parameter : Type*) where
  nominalRelaxationTime : ℝ
  acceptedRelaxationTime : ℝ
  bpTaskGradient : Parameter
  rawCredit : Parameter
  transportedDirection : Parameter

/-- The first-order relation reported before clipping or optimizer transport. -/
def rawAlignment (sample : Sample Parameter) : ℝ :=
  ⟪sample.bpTaskGradient, sample.rawCredit⟫_ℝ

/-- The first-order relation of the direction actually subtracted from the
parameter.  This is the direction relevant to a task-descent theorem. -/
def transportedAlignment (sample : Sample Parameter) : ℝ :=
  ⟪sample.bpTaskGradient, sample.transportedDirection⟫_ℝ

/-- Mathematical cosine refuses either zero vector rather than silently
choosing a denominator convention. -/
noncomputable def cosine? (sample : Sample Parameter) : Option ℝ :=
  if ‖sample.rawCredit‖ = 0 ∨ ‖sample.bpTaskGradient‖ = 0 then
    none
  else
    some
      (rawAlignment sample /
        (‖sample.rawCredit‖ * ‖sample.bpTaskGradient‖))

/-- Mathematical norm ratio refuses a zero BP-gradient norm. -/
noncomputable def normRatio? (sample : Sample Parameter) : Option ℝ :=
  if ‖sample.bpTaskGradient‖ = 0 then
    none
  else
    some (‖sample.rawCredit‖ / ‖sample.bpTaskGradient‖)

/-- Cosine of the direction actually transported to the optimizer against the
matched BP task gradient.  This remains distinct from `cosine?`, which measures
the raw local credit before optimizer transport. -/
noncomputable def transportedCosine? (sample : Sample Parameter) : Option ℝ :=
  if ‖sample.transportedDirection‖ = 0 ∨ ‖sample.bpTaskGradient‖ = 0 then
    none
  else
    some
      (transportedAlignment sample /
        (‖sample.transportedDirection‖ * ‖sample.bpTaskGradient‖))

/-- Norm ratio of the transported direction against the matched BP task
gradient.  Directional agreement alone does not control this magnitude. -/
noncomputable def transportedNormRatio? (sample : Sample Parameter) : Option ℝ :=
  if ‖sample.bpTaskGradient‖ = 0 then
    none
  else
    some (‖sample.transportedDirection‖ / ‖sample.bpTaskGradient‖)

theorem cosine?_eq_none_of_rawCredit_eq_zero
    (sample : Sample Parameter) (hzero : sample.rawCredit = 0) :
    cosine? sample = none := by
  simp [cosine?, hzero]

theorem cosine?_eq_none_of_bpTaskGradient_eq_zero
    (sample : Sample Parameter) (hzero : sample.bpTaskGradient = 0) :
    cosine? sample = none := by
  simp [cosine?, hzero]

omit [InnerProductSpace ℝ Parameter] in
theorem normRatio?_eq_none_of_bpTaskGradient_eq_zero
    (sample : Sample Parameter) (hzero : sample.bpTaskGradient = 0) :
    normRatio? sample = none := by
  simp [normRatio?, hzero]

theorem transportedCosine?_eq_none_of_transportedDirection_eq_zero
    (sample : Sample Parameter) (hzero : sample.transportedDirection = 0) :
    transportedCosine? sample = none := by
  simp [transportedCosine?, hzero]

theorem transportedCosine?_eq_none_of_bpTaskGradient_eq_zero
    (sample : Sample Parameter) (hzero : sample.bpTaskGradient = 0) :
    transportedCosine? sample = none := by
  simp [transportedCosine?, hzero]

omit [InnerProductSpace ℝ Parameter] in
theorem transportedNormRatio?_eq_none_of_bpTaskGradient_eq_zero
    (sample : Sample Parameter) (hzero : sample.bpTaskGradient = 0) :
    transportedNormRatio? sample = none := by
  simp [transportedNormRatio?, hzero]

/-- A trace is ordered by accepted relaxation time.  Nominal and accepted
time remain separate because backtracking can make them unequal. -/
def RelaxationOrdered (samples : List (Sample Parameter)) : Prop :=
  samples.Pairwise fun earlier later =>
    earlier.acceptedRelaxationTime ≤ later.acceptedRelaxationTime

/-- Positive fixture: an increasing accepted-time trace. -/
def orderedScalarTrace : List (Sample ℝ) :=
  [ { nominalRelaxationTime := 2
      acceptedRelaxationTime := 1
      bpTaskGradient := 1
      rawCredit := 1
      transportedDirection := 1 }
  , { nominalRelaxationTime := 3
      acceptedRelaxationTime := 2
      bpTaskGradient := 1
      rawCredit := 1
      transportedDirection := 1 } ]

theorem orderedScalarTrace_is_ordered :
    RelaxationOrdered orderedScalarTrace := by
  norm_num [RelaxationOrdered, orderedScalarTrace]

/-- Negative fixture: the same samples in reverse order do not form an
accepted-relaxation-time trace. -/
theorem reversedScalarTrace_is_not_ordered :
    ¬ RelaxationOrdered orderedScalarTrace.reverse := by
  norm_num [RelaxationOrdered, orderedScalarTrace]

/-- Raw PC credit can be perfectly BP-aligned while the direction produced by
parameter transport is exactly reversed.  Consequently raw cosine is not by
itself a finite-update safety certificate. -/
theorem raw_alignment_does_not_imply_transported_alignment :
    ∃ sample : Sample ℝ,
      0 < rawAlignment sample ∧ transportedAlignment sample < 0 := by
  refine ⟨
    { nominalRelaxationTime := 1
      acceptedRelaxationTime := 1
      bpTaskGradient := 1
      rawCredit := 1
      transportedDirection := -1 },
    ?_, ?_⟩
  · norm_num [rawAlignment, real_inner_comm]
  · norm_num [transportedAlignment, real_inner_comm]

/-- A scalar family in which raw credit and transported motion have the same
perfect BP direction, while optimizer transport may choose any positive norm
ratio. -/
def positiveScaledTransportSample (scale : ℝ) : Sample ℝ :=
  { nominalRelaxationTime := 1
    acceptedRelaxationTime := 1
    bpTaskGradient := 1
    rawCredit := 1
    transportedDirection := scale }

theorem positiveScaledTransportSample_telemetry
    {scale : ℝ} (hscale : 0 < scale) :
    cosine? (positiveScaledTransportSample scale) = some 1 ∧
    transportedCosine? (positiveScaledTransportSample scale) = some 1 ∧
    transportedNormRatio? (positiveScaledTransportSample scale) = some scale := by
  have hscale_ne : scale ≠ 0 := ne_of_gt hscale
  simp [cosine?, transportedCosine?, transportedNormRatio?, rawAlignment,
    transportedAlignment, positiveScaledTransportSample, Real.norm_eq_abs,
    abs_of_pos hscale, hscale_ne]

/-- Negative boundary for cosine-only reporting: both raw and transported
cosines are exactly one, although the transported update has less than one
percent of the matched BP norm. -/
theorem cosine_eq_one_not_normRatio_le :
    cosine? (positiveScaledTransportSample (1 / 1000 : ℝ)) = some 1 ∧
    transportedCosine? (positiveScaledTransportSample (1 / 1000 : ℝ)) = some 1 ∧
    transportedNormRatio? (positiveScaledTransportSample (1 / 1000 : ℝ)) =
      some (1 / 1000 : ℝ) ∧
    (1 / 1000 : ℝ) < 1 / 100 := by
  have telemetry :=
    positiveScaledTransportSample_telemetry (scale := (1 / 1000 : ℝ)) (by norm_num)
  exact ⟨telemetry.1, telemetry.2.1, telemetry.2.2, by norm_num⟩

/-- The actual finite-step safety route: a directional task upper model for
the transported direction plus a positive step and curvature budget. -/
theorem transportedDirection_strictTaskDescent
    {loss : Parameter → ℝ} {parameter : Parameter}
    {sample : Sample Parameter} {curvature step : ℝ}
    (certificate :
      HasDirectionalTaskUpperModelAt loss parameter sample.bpTaskGradient
        sample.transportedDirection curvature)
    (hstep : 0 < step)
    (htrust :
      step * curvature / 2 < transportedAlignment sample) :
    loss (parameter - step • sample.transportedDirection) < loss parameter := by
  exact directionalTask_strict_descent certificate hstep htrust

#print axioms cosine?_eq_none_of_rawCredit_eq_zero
#print axioms orderedScalarTrace_is_ordered
#print axioms reversedScalarTrace_is_not_ordered
#print axioms raw_alignment_does_not_imply_transported_alignment
#print axioms positiveScaledTransportSample_telemetry
#print axioms cosine_eq_one_not_normRatio_le
#print axioms transportedDirection_strictTaskDescent

end TransportedDirectionAlignment

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
