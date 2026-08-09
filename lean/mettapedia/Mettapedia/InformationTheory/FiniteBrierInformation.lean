import Mathlib.Tactic

/-!
# Finite multiclass Brier value of information

For a finite context `X`, a finite schema signal `Z`, and a finite label space
`Y`, this module compares two calibrated forecasts:

* the unresolved forecast averages `P(Y | X, Z)` over `Z`;
* the resolved forecast observes `Z` and uses `P(Y | X, Z)` itself.

Their Brier-risk difference is exactly the weighted squared distance between
the resolved and unresolved posteriors.  Thus information has nonnegative
value, zero value exactly when it changes no positive-mass posterior, and
strict value as soon as one positive-mass coordinate changes.
-/

namespace Mettapedia.InformationTheory.FiniteBrierInformation

open scoped BigOperators

noncomputable section

universe u v w

variable {Y : Type u} [Fintype Y] [DecidableEq Y]

/-- One-hot coordinate of a realized finite outcome. -/
def outcomeCoordinate (outcome coordinate : Y) : ℝ :=
  if coordinate = outcome then 1 else 0

/-- Multiclass Brier loss of a forecast at one realized outcome. -/
def brierLoss (forecast : Y → ℝ) (outcome : Y) : ℝ :=
  ∑ coordinate, (forecast coordinate - outcomeCoordinate outcome coordinate) ^ 2

/-- Expected Brier loss under a declared finite label distribution. -/
def expectedBrier (truth forecast : Y → ℝ) : ℝ :=
  ∑ outcome, truth outcome * brierLoss forecast outcome

/-- Squared Euclidean distance between two finite forecasts. -/
def forecastSquaredDistance (left right : Y → ℝ) : ℝ :=
  ∑ coordinate, (left coordinate - right coordinate) ^ 2

/-- Expansion of one realized multiclass Brier loss. -/
theorem brierLoss_eq_sum_sq_sub
    (forecast : Y → ℝ) (outcome : Y) :
    brierLoss forecast outcome =
      (∑ coordinate, (forecast coordinate) ^ 2) -
        2 * forecast outcome + 1 := by
  unfold brierLoss outcomeCoordinate
  calc
    (∑ coordinate,
        (forecast coordinate - if coordinate = outcome then 1 else 0) ^ 2) =
        ∑ coordinate,
          ((forecast coordinate) ^ 2 -
            2 * forecast coordinate *
              (if coordinate = outcome then 1 else 0) +
            (if coordinate = outcome then 1 else 0) ^ 2) := by
      apply Finset.sum_congr rfl
      intro coordinate _
      ring
    _ = (∑ coordinate, (forecast coordinate) ^ 2) -
          ∑ coordinate,
            (2 * forecast coordinate *
              (if coordinate = outcome then 1 else 0)) +
          ∑ coordinate,
            (if coordinate = outcome then 1 else 0) ^ 2 := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    _ = (∑ coordinate, (forecast coordinate) ^ 2) -
          2 * forecast outcome + 1 := by
      simp

/-- Expansion of expected Brier loss for a normalized truth distribution. -/
theorem expectedBrier_eq_sum_sq_sub_inner_add_one
    (truth forecast : Y → ℝ)
    (truth_sum : ∑ outcome, truth outcome = 1) :
    expectedBrier truth forecast =
      (∑ coordinate, (forecast coordinate) ^ 2) -
        2 * (∑ coordinate, truth coordinate * forecast coordinate) + 1 := by
  unfold expectedBrier
  rw [show (fun outcome => truth outcome * brierLoss forecast outcome) =
      (fun outcome => truth outcome *
        ((∑ coordinate, (forecast coordinate) ^ 2) -
          2 * forecast outcome + 1)) by
    funext outcome
    rw [brierLoss_eq_sum_sq_sub]]
  calc
    (∑ outcome,
        truth outcome *
          ((∑ coordinate, (forecast coordinate) ^ 2) -
            2 * forecast outcome + 1)) =
        ∑ outcome,
          (truth outcome * (∑ coordinate, (forecast coordinate) ^ 2) -
            2 * (truth outcome * forecast outcome) + truth outcome) := by
      apply Finset.sum_congr rfl
      intro outcome _
      ring
    _ = (∑ outcome,
          truth outcome * (∑ coordinate, (forecast coordinate) ^ 2)) -
        (∑ outcome, 2 * (truth outcome * forecast outcome)) +
        ∑ outcome, truth outcome := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    _ = (∑ outcome, truth outcome) *
          (∑ coordinate, (forecast coordinate) ^ 2) -
        2 * (∑ outcome, truth outcome * forecast outcome) +
        ∑ outcome, truth outcome := by
      rw [Finset.sum_mul, Finset.mul_sum]
    _ = (∑ coordinate, (forecast coordinate) ^ 2) -
        2 * (∑ coordinate, truth coordinate * forecast coordinate) + 1 := by
      rw [truth_sum]
      ring

omit [DecidableEq Y] in
/-- Expansion of finite squared forecast distance. -/
theorem forecastSquaredDistance_eq
    (left right : Y → ℝ) :
    forecastSquaredDistance left right =
      (∑ coordinate, (left coordinate) ^ 2) -
        2 * (∑ coordinate, right coordinate * left coordinate) +
        ∑ coordinate, (right coordinate) ^ 2 := by
  unfold forecastSquaredDistance
  calc
    (∑ coordinate, (left coordinate - right coordinate) ^ 2) =
        ∑ coordinate,
          ((left coordinate) ^ 2 -
            2 * (right coordinate * left coordinate) +
            (right coordinate) ^ 2) := by
      apply Finset.sum_congr rfl
      intro coordinate _
      ring
    _ = (∑ coordinate, (left coordinate) ^ 2) -
        2 * (∑ coordinate, right coordinate * left coordinate) +
        ∑ coordinate, (right coordinate) ^ 2 := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]

/-- **Strict propriety of finite multiclass Brier score.**  Excess expected
risk over the calibrated forecast is exactly squared forecast distance. -/
theorem expectedBrier_decomposition
    (truth forecast : Y → ℝ)
    (truth_sum : ∑ outcome, truth outcome = 1) :
    expectedBrier truth forecast =
      expectedBrier truth truth + forecastSquaredDistance forecast truth := by
  rw [expectedBrier_eq_sum_sq_sub_inner_add_one truth forecast truth_sum,
    expectedBrier_eq_sum_sq_sub_inner_add_one truth truth truth_sum,
    forecastSquaredDistance_eq]
  ring_nf

/-- Brier excess risk is nonnegative. -/
theorem expectedBrier_truth_le
    (truth forecast : Y → ℝ)
    (truth_sum : ∑ outcome, truth outcome = 1) :
    expectedBrier truth truth ≤ expectedBrier truth forecast := by
  rw [expectedBrier_decomposition truth forecast truth_sum]
  exact le_add_of_nonneg_right
    (Finset.sum_nonneg fun coordinate _ => sq_nonneg _)

/-- Exact equality in the proper-score theorem means coordinatewise equality. -/
theorem expectedBrier_eq_truth_iff
    (truth forecast : Y → ℝ)
    (truth_sum : ∑ outcome, truth outcome = 1) :
    expectedBrier truth forecast = expectedBrier truth truth ↔
      forecast = truth := by
  rw [expectedBrier_decomposition truth forecast truth_sum]
  constructor
  · intro equal
    have distance_zero : forecastSquaredDistance forecast truth = 0 := by
      linarith
    funext coordinate
    unfold forecastSquaredDistance at distance_zero
    have coordinate_zero :
        (forecast coordinate - truth coordinate) ^ 2 = 0 := by
      exact (Finset.sum_eq_zero_iff_of_nonneg
        (fun index _ => sq_nonneg (forecast index - truth index))).mp
          distance_zero coordinate (Finset.mem_univ coordinate)
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp coordinate_zero)
  · rintro rfl
    simp [forecastSquaredDistance]

/-! ## A finite conditional-information model -/

/-- Calibrated finite conditional distributions over contexts, schema signals,
and labels. -/
structure ConditionalLabelModel (X : Type v) (Z : Type w) (Y : Type u)
    [Fintype X] [Fintype Z] [Fintype Y] where
  contextWeight : X → ℝ
  schemaWeight : X → Z → ℝ
  labelPosterior : X → Z → Y → ℝ
  contextWeight_nonneg : ∀ context, 0 ≤ contextWeight context
  contextWeight_sum : ∑ context, contextWeight context = 1
  schemaWeight_nonneg : ∀ context schema, 0 ≤ schemaWeight context schema
  schemaWeight_sum : ∀ context, ∑ schema, schemaWeight context schema = 1
  labelPosterior_nonneg : ∀ context schema label,
    0 ≤ labelPosterior context schema label
  labelPosterior_sum : ∀ context schema,
    ∑ label, labelPosterior context schema label = 1

variable {X : Type v} {Z : Type w}
variable [Fintype X] [Fintype Z]

/-- Label posterior before the schema signal is resolved. -/
def ConditionalLabelModel.coarsePosterior
    (model : ConditionalLabelModel X Z Y) (context : X) (label : Y) : ℝ :=
  ∑ schema, model.schemaWeight context schema *
    model.labelPosterior context schema label

omit [DecidableEq Y] in
/-- The unresolved posterior is normalized. -/
theorem ConditionalLabelModel.coarsePosterior_sum
    (model : ConditionalLabelModel X Z Y) (context : X) :
    ∑ label, model.coarsePosterior context label = 1 := by
  unfold ConditionalLabelModel.coarsePosterior
  calc
    (∑ label, ∑ schema,
        model.schemaWeight context schema *
          model.labelPosterior context schema label) =
        ∑ schema, ∑ label,
          model.schemaWeight context schema *
            model.labelPosterior context schema label := by
      exact Finset.sum_comm
    _ = ∑ schema,
          model.schemaWeight context schema *
            (∑ label, model.labelPosterior context schema label) := by
      apply Finset.sum_congr rfl
      intro schema _
      rw [Finset.mul_sum]
    _ = ∑ schema, model.schemaWeight context schema := by
      apply Finset.sum_congr rfl
      intro schema _
      rw [model.labelPosterior_sum]
      ring
    _ = 1 := model.schemaWeight_sum context

/-- Risk of an arbitrary forecast allowed to observe both context and schema. -/
def conditionalBrierRisk (model : ConditionalLabelModel X Z Y)
    (forecast : X → Z → Y → ℝ) : ℝ :=
  ∑ context, model.contextWeight context *
    ∑ schema, model.schemaWeight context schema *
      expectedBrier (model.labelPosterior context schema)
        (forecast context schema)

/-- Risk of the calibrated schema-resolved posterior. -/
def resolvedBrierRisk (model : ConditionalLabelModel X Z Y) : ℝ :=
  conditionalBrierRisk model model.labelPosterior

/-- Risk of using only the context-level mixture, without resolved schema. -/
def unresolvedBrierRisk (model : ConditionalLabelModel X Z Y) : ℝ :=
  conditionalBrierRisk model
    (fun context _schema => model.coarsePosterior context)

/-- Weighted squared posterior movement supplied by resolving the schema. -/
def brierInformationValue (model : ConditionalLabelModel X Z Y) : ℝ :=
  ∑ context, model.contextWeight context *
    ∑ schema, model.schemaWeight context schema *
      forecastSquaredDistance (model.coarsePosterior context)
        (model.labelPosterior context schema)

/-- Risk decomposition for any schema-aware forecast. -/
theorem conditionalBrierRisk_decomposition
    (model : ConditionalLabelModel X Z Y)
    (forecast : X → Z → Y → ℝ) :
    conditionalBrierRisk model forecast =
      resolvedBrierRisk model +
        ∑ context, model.contextWeight context *
          ∑ schema, model.schemaWeight context schema *
            forecastSquaredDistance (forecast context schema)
              (model.labelPosterior context schema) := by
  unfold conditionalBrierRisk resolvedBrierRisk
  calc
    (∑ context, model.contextWeight context *
      ∑ schema, model.schemaWeight context schema *
        expectedBrier (model.labelPosterior context schema)
          (forecast context schema)) =
      ∑ context, model.contextWeight context *
        ∑ schema, model.schemaWeight context schema *
          (expectedBrier (model.labelPosterior context schema)
              (model.labelPosterior context schema) +
            forecastSquaredDistance (forecast context schema)
              (model.labelPosterior context schema)) := by
        apply Finset.sum_congr rfl
        intro context _
        congr 1
        apply Finset.sum_congr rfl
        intro schema _
        rw [expectedBrier_decomposition]
        exact model.labelPosterior_sum context schema
    _ = (∑ context, model.contextWeight context *
        ∑ schema, model.schemaWeight context schema *
          expectedBrier (model.labelPosterior context schema)
            (model.labelPosterior context schema)) +
      ∑ context, model.contextWeight context *
        ∑ schema, model.schemaWeight context schema *
          forecastSquaredDistance (forecast context schema)
            (model.labelPosterior context schema) := by
      simp only [mul_add, Finset.sum_add_distrib]

/-- **Finite multiclass value of schema information.**  The reduction in
Brier risk from resolving the schema is exactly the expected squared movement
of the calibrated posterior. -/
theorem unresolved_sub_resolved_eq_brierInformationValue
    (model : ConditionalLabelModel X Z Y) :
    unresolvedBrierRisk model - resolvedBrierRisk model =
      brierInformationValue model := by
  rw [show unresolvedBrierRisk model =
      resolvedBrierRisk model + brierInformationValue model by
    simpa [unresolvedBrierRisk, brierInformationValue] using
      conditionalBrierRisk_decomposition model
        (fun context _schema => model.coarsePosterior context)]
  ring

omit [DecidableEq Y] in
/-- Calibrated schema information cannot increase Brier risk. -/
theorem brierInformationValue_nonneg
    (model : ConditionalLabelModel X Z Y) :
    0 ≤ brierInformationValue model := by
  unfold brierInformationValue
  exact Finset.sum_nonneg fun context _ =>
    mul_nonneg (model.contextWeight_nonneg context)
      (Finset.sum_nonneg fun schema _ =>
        mul_nonneg (model.schemaWeight_nonneg context schema)
          (Finset.sum_nonneg fun label _ => sq_nonneg _))

omit [DecidableEq Y] in
/-- Exact zero-information boundary: every posterior coordinate agrees on
every context/schema cell carrying positive joint mass. -/
theorem brierInformationValue_eq_zero_iff
    (model : ConditionalLabelModel X Z Y) :
    brierInformationValue model = 0 ↔
      ∀ context schema label,
        0 < model.contextWeight context * model.schemaWeight context schema →
        model.labelPosterior context schema label =
          model.coarsePosterior context label := by
  constructor
  · intro value_zero context schema label positive
    have context_terms_zero :
        ∀ context ∈ (Finset.univ : Finset X),
          model.contextWeight context *
            ∑ schema, model.schemaWeight context schema *
              forecastSquaredDistance (model.coarsePosterior context)
                (model.labelPosterior context schema) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun index _ =>
        mul_nonneg (model.contextWeight_nonneg index)
          (Finset.sum_nonneg fun signal _ =>
            mul_nonneg (model.schemaWeight_nonneg index signal)
              (Finset.sum_nonneg fun coordinate _ => sq_nonneg _)))).mp
        value_zero
    have context_zero := context_terms_zero context (Finset.mem_univ context)
    have joint_context_pos : 0 < model.contextWeight context := by
      nlinarith [model.schemaWeight_nonneg context schema]
    have schema_sum_zero :
        ∑ signal, model.schemaWeight context signal *
          forecastSquaredDistance (model.coarsePosterior context)
            (model.labelPosterior context signal) = 0 := by
      exact (mul_eq_zero.mp context_zero).resolve_left joint_context_pos.ne'
    have schema_terms_zero :
        ∀ signal ∈ (Finset.univ : Finset Z),
          model.schemaWeight context signal *
            forecastSquaredDistance (model.coarsePosterior context)
              (model.labelPosterior context signal) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun signal _ =>
        mul_nonneg (model.schemaWeight_nonneg context signal)
          (Finset.sum_nonneg fun coordinate _ => sq_nonneg _))).mp
        schema_sum_zero
    have schema_zero := schema_terms_zero schema (Finset.mem_univ schema)
    have schema_pos : 0 < model.schemaWeight context schema := by
      nlinarith [model.contextWeight_nonneg context]
    have distance_zero :
        forecastSquaredDistance (model.coarsePosterior context)
          (model.labelPosterior context schema) = 0 :=
      (mul_eq_zero.mp schema_zero).resolve_left schema_pos.ne'
    unfold forecastSquaredDistance at distance_zero
    have coordinate_zero :
        (model.coarsePosterior context label -
          model.labelPosterior context schema label) ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun coordinate _ => sq_nonneg
          (model.coarsePosterior context coordinate -
            model.labelPosterior context schema coordinate))).mp
        distance_zero label (Finset.mem_univ label)
    nlinarith [coordinate_zero]
  · intro equal
    unfold brierInformationValue
    apply Finset.sum_eq_zero
    intro context _
    by_cases contextZero : model.contextWeight context = 0
    · simp [contextZero]
    · have contextPos : 0 < model.contextWeight context :=
        lt_of_le_of_ne (model.contextWeight_nonneg context)
          (Ne.symm contextZero)
      apply mul_eq_zero_of_right
      apply Finset.sum_eq_zero
      intro schema _
      by_cases schemaZero : model.schemaWeight context schema = 0
      · simp [schemaZero]
      · have schemaPos : 0 < model.schemaWeight context schema :=
          lt_of_le_of_ne (model.schemaWeight_nonneg context schema)
            (Ne.symm schemaZero)
        apply mul_eq_zero_of_right
        unfold forecastSquaredDistance
        apply Finset.sum_eq_zero
        intro label _
        rw [equal context schema label (mul_pos contextPos schemaPos)]
        ring

omit [DecidableEq Y] in
/-- Any positive-mass posterior-coordinate change gives strictly positive
schema information value. -/
theorem brierInformationValue_pos_of_exists
    (model : ConditionalLabelModel X Z Y)
    (context : X) (schema : Z) (label : Y)
    (joint_pos : 0 <
      model.contextWeight context * model.schemaWeight context schema)
    (different : model.labelPosterior context schema label ≠
      model.coarsePosterior context label) :
    0 < brierInformationValue model := by
  have nonneg := brierInformationValue_nonneg model
  exact lt_of_le_of_ne nonneg (fun zero =>
    different ((brierInformationValue_eq_zero_iff model).1 zero.symm
      context schema label joint_pos))

/-- Giving a static learner the resolved binding restores risk parity with the
calibrated resolved predictor. -/
theorem resolved_binding_restores_brier_parity
    (model : ConditionalLabelModel X Z Y) :
    conditionalBrierRisk model model.labelPosterior =
      resolvedBrierRisk model := by
  rw [conditionalBrierRisk_decomposition]
  unfold forecastSquaredDistance
  simp

/-! ## Informative, irrelevant, and misleading controls -/

def twoModeModel : ConditionalLabelModel Unit Bool Bool where
  contextWeight _ := 1
  schemaWeight _ _ := 1 / 2
  labelPosterior _ schema label := if label = schema then 1 else 0
  contextWeight_nonneg := by intro; norm_num
  contextWeight_sum := by simp
  schemaWeight_nonneg := by intros; norm_num
  schemaWeight_sum := by intro; norm_num
  labelPosterior_nonneg := by intros; split <;> norm_num
  labelPosterior_sum := by intro context schema; cases schema <;> norm_num

/-- Resolving two equally likely deterministic modes reduces Brier risk by
exactly one half. -/
theorem twoMode_brierInformationValue_eq_half :
    brierInformationValue twoModeModel = 1 / 2 := by
  norm_num [brierInformationValue, forecastSquaredDistance,
    ConditionalLabelModel.coarsePosterior, twoModeModel]

def irrelevantSchemaModel : ConditionalLabelModel Unit Bool Bool where
  contextWeight _ := 1
  schemaWeight _ _ := 1 / 2
  labelPosterior _ _ label := if label then 3 / 4 else 1 / 4
  contextWeight_nonneg := by intro; norm_num
  contextWeight_sum := by simp
  schemaWeight_nonneg := by intros; norm_num
  schemaWeight_sum := by intro; norm_num
  labelPosterior_nonneg := by intros; split <;> norm_num
  labelPosterior_sum := by intros; norm_num

/-- A schema that leaves the calibrated label posterior unchanged has exactly
zero value. -/
theorem irrelevantSchema_has_zero_brierInformationValue :
    brierInformationValue irrelevantSchemaModel = 0 := by
  norm_num [brierInformationValue, forecastSquaredDistance,
    ConditionalLabelModel.coarsePosterior, irrelevantSchemaModel]

def fairTruth : Bool → ℝ
  | false => 1 / 2
  | true => 1 / 2

def misleadingForecast : Bool → ℝ
  | false => 0
  | true => 1

/-- Uncalibrated schema advice can be harmful: on a fair binary outcome, a
confident one-sided forecast doubles Bayes Brier risk from `1/2` to `1`. -/
theorem misleading_uncalibrated_schema_increases_brierRisk :
    expectedBrier fairTruth fairTruth = 1 / 2 ∧
      expectedBrier fairTruth misleadingForecast = 1 ∧
      expectedBrier fairTruth fairTruth <
        expectedBrier fairTruth misleadingForecast := by
  norm_num [expectedBrier, brierLoss, outcomeCoordinate,
    fairTruth, misleadingForecast]

#print axioms expectedBrier_decomposition
#print axioms expectedBrier_truth_le
#print axioms expectedBrier_eq_truth_iff
#print axioms ConditionalLabelModel.coarsePosterior_sum
#print axioms conditionalBrierRisk_decomposition
#print axioms unresolved_sub_resolved_eq_brierInformationValue
#print axioms brierInformationValue_nonneg
#print axioms brierInformationValue_eq_zero_iff
#print axioms brierInformationValue_pos_of_exists
#print axioms resolved_binding_restores_brier_parity
#print axioms twoMode_brierInformationValue_eq_half
#print axioms irrelevantSchema_has_zero_brierInformationValue
#print axioms misleading_uncalibrated_schema_increases_brierRisk

end

end Mettapedia.InformationTheory.FiniteBrierInformation
