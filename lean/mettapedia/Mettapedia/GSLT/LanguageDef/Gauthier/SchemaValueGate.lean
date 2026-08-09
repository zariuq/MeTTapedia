import Mettapedia.GSLT.LanguageDef.Gauthier.SchemaActionEvidence
import Mettapedia.InformationTheory.FiniteBrierInformation
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.ConditionalCreditAdvantage
import Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery.PairedDesignEstimands

/-!
# Work-normalized value gates for schema information

The gross value of a schema has two separately auditable terms: calibrated
label information and any certified progress advantage of the realized PC
direction over BP.  The net value subtracts priced extra work.  Dividing by a
positive matched-work denominator changes scale but not the admission sign.

The accompanying two-by-two estimand compares the schema-on minus schema-off
effect under PC with the same effect under BP.  Shared static evidence is an
additive main effect and therefore has zero interaction; only an additional
PC-specific use of the schema appears in the interaction term.
-/

namespace Mettapedia.GSLT.LanguageDef.GauthierSchemaValueGate

open Mettapedia.InformationTheory.FiniteBrierInformation
open Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
open Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.ConditionalCreditAdvantage
open Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery

/-! ## Exact net-value gate -/

/-- Net schema value in common utility units.  `informationValue` is the
proper-score risk reduction, the two guarantees price learning progress, and
`workPrice * extraWork` charges the additional computation. -/
def netSchemaValue
    (informationValue pcGuarantee bpGuarantee extraWork workPrice : ℝ) : ℝ :=
  informationValue + (pcGuarantee - bpGuarantee) - workPrice * extraWork

/-- Net schema value per unit of declared matched work. -/
noncomputable def workNormalizedNetSchemaValue
    (informationValue pcGuarantee bpGuarantee extraWork workPrice
      totalWork : ℝ) : ℝ :=
  netSchemaValue informationValue pcGuarantee bpGuarantee extraWork workPrice /
    totalWork

/-- **Exact work-normalized schema gate.**  For positive declared work, the
schema is admitted exactly when information plus certified PC progress pays
for the priced extra work. -/
theorem workNormalizedNetSchemaValue_pos_iff
    (informationValue pcGuarantee bpGuarantee extraWork workPrice
      totalWork : ℝ)
    (totalWork_pos : 0 < totalWork) :
    0 < workNormalizedNetSchemaValue informationValue pcGuarantee bpGuarantee
        extraWork workPrice totalWork ↔
      workPrice * extraWork <
        informationValue + (pcGuarantee - bpGuarantee) := by
  rw [workNormalizedNetSchemaValue,
    div_pos_iff_of_pos_right totalWork_pos]
  unfold netSchemaValue
  constructor <;> intro gate <;> linarith

/-- Instantiate the gate with the calibrated finite Brier information value. -/
def calibratedSchemaNetValue
    {X Z Y : Type*} [Fintype X] [Fintype Z] [Fintype Y] [DecidableEq Y]
    (model : ConditionalLabelModel X Z Y)
    (pcGuarantee bpGuarantee extraWork workPrice : ℝ) : ℝ :=
  netSchemaValue (brierInformationValue model) pcGuarantee bpGuarantee
    extraWork workPrice

/-- The calibrated gate can be read entirely as observable risk reduction
plus the certified progress contrast. -/
theorem workNormalized_calibrated_gate_iff
    {X Z Y : Type*} [Fintype X] [Fintype Z] [Fintype Y] [DecidableEq Y]
    (model : ConditionalLabelModel X Z Y)
    (pcGuarantee bpGuarantee extraWork workPrice totalWork : ℝ)
    (totalWork_pos : 0 < totalWork) :
    0 < workNormalizedNetSchemaValue (brierInformationValue model)
        pcGuarantee bpGuarantee extraWork workPrice totalWork ↔
      workPrice * extraWork <
        (unresolvedBrierRisk model - resolvedBrierRisk model) +
          (pcGuarantee - bpGuarantee) := by
  rw [workNormalizedNetSchemaValue_pos_iff _ _ _ _ _ _ totalWork_pos,
    unresolved_sub_resolved_eq_brierInformationValue]

/-- Direct bridge to the already-certified work-normalized credit guarantees. -/
noncomputable def calibratedNetValueFromCreditGuarantees
    {X Z Y : Type*} [Fintype X] [Fintype Z] [Fintype Y] [DecidableEq Y]
    (model : ConditionalLabelModel X Z Y)
    (workBudget pcFixed pcSweep pcDepth bpFixed bpSweep bpDepth : ℕ)
    (step pcAlignment pcCurvature bpAlignment bpCurvature
      extraWork workPrice : ℝ) : ℝ :=
  calibratedSchemaNetValue model
    (workNormalizedGuarantee workBudget pcFixed pcSweep pcDepth
      step pcAlignment pcCurvature)
    (workNormalizedGuarantee workBudget bpFixed bpSweep bpDepth
      step bpAlignment bpCurvature)
    extraWork workPrice

/-- If the schema carries no label information, PC has no certified progress
advantage, and extra work has nonnegative price, its net value is nonpositive. -/
theorem netSchemaValue_nonpos_of_closed_channels
    (pcGuarantee bpGuarantee extraWork workPrice : ℝ)
    (pc_le_bp : pcGuarantee ≤ bpGuarantee)
    (extraWork_nonneg : 0 ≤ extraWork)
    (workPrice_nonneg : 0 ≤ workPrice) :
    netSchemaValue 0 pcGuarantee bpGuarantee extraWork workPrice ≤ 0 := by
  unfold netSchemaValue
  nlinarith [mul_nonneg workPrice_nonneg extraWork_nonneg]

/-- A positive information/progress margin can pay for work. -/
theorem positive_margin_pays_for_work :
    0 < workNormalizedNetSchemaValue 2 3 2 2 1 5 := by
  norm_num [workNormalizedNetSchemaValue, netSchemaValue]

/-- Excess work can erase the same gross advantage. -/
theorem excess_work_rejects_schema :
    workNormalizedNetSchemaValue 2 3 2 4 1 5 < 0 := by
  norm_num [workNormalizedNetSchemaValue, netSchemaValue]

/-! ## Schema-by-rule interaction -/

/-- Difference in schema effects: `(PC,on - PC,off) - (BP,on - BP,off)`. -/
def schemaRuleInteraction
    (bpOff bpOn pcOff pcOn : ℝ) : ℝ :=
  (pcOn - pcOff) - (bpOn - bpOff)

/-- The real-valued schema/rule interaction agrees with the existing
count-valued paired-design interaction after casting. -/
theorem schemaRuleInteraction_natCast_eq_architectureUpdateInteraction
    (bpOff bpOn pcOff pcOn : ℕ) :
    schemaRuleInteraction (bpOff : ℝ) (bpOn : ℝ) (pcOff : ℝ) (pcOn : ℝ) =
      (architectureUpdateInteraction bpOff bpOn pcOff pcOn : ℝ) := by
  unfold schemaRuleInteraction architectureUpdateInteraction
  push_cast
  ring

/-- Interaction is zero exactly when the schema contrast is the same under
both learning rules. -/
theorem schemaRuleInteraction_eq_zero_iff
    (bpOff bpOn pcOff pcOn : ℝ) :
    schemaRuleInteraction bpOff bpOn pcOff pcOn = 0 ↔
      pcOn - pcOff = bpOn - bpOff := by
  unfold schemaRuleInteraction
  constructor <;> intro equality <;> linarith

/-- Shared static schema evidence is an additive main effect and has zero
schema-by-rule interaction. -/
theorem additive_static_schema_effect_has_zero_interaction
    (baseline ruleEffect staticSchemaEffect : ℝ) :
    schemaRuleInteraction
      baseline (baseline + staticSchemaEffect)
      (baseline + ruleEffect)
      (baseline + ruleEffect + staticSchemaEffect) = 0 := by
  unfold schemaRuleInteraction
  ring

/-- If PC extracts an additional dynamic benefit from the same schema, the
four-cell interaction identifies exactly that surplus. -/
theorem schemaRuleInteraction_eq_dynamic_surplus
    (baseline ruleEffect staticSchemaEffect dynamicSurplus : ℝ) :
    schemaRuleInteraction
      baseline (baseline + staticSchemaEffect)
      (baseline + ruleEffect)
      (baseline + ruleEffect + staticSchemaEffect + dynamicSurplus) =
        dynamicSurplus := by
  unfold schemaRuleInteraction
  ring

/-- Three cells never identify the schema-by-rule interaction: two possible
values of the missing PC/schema-on cell preserve every observation but give
different contrasts. -/
theorem three_cells_do_not_identify_schemaRuleInteraction
    (bpOff bpOn pcOff : ℝ) :
    ∃ firstCompletion secondCompletion : ℝ,
      schemaRuleInteraction bpOff bpOn pcOff firstCompletion ≠
        schemaRuleInteraction bpOff bpOn pcOff secondCompletion := by
  refine ⟨0, 1, ?_⟩
  unfold schemaRuleInteraction
  linarith

/-- Concrete positive interaction: static evidence helps both rules by one,
and PC obtains two further units dynamically. -/
theorem schemaRuleInteraction_positive_example :
    schemaRuleInteraction 10 11 10 13 = 2 := by
  norm_num [schemaRuleInteraction]

/-- Concrete no-interaction control. -/
theorem schemaRuleInteraction_zero_example :
    schemaRuleInteraction 10 11 12 13 = 0 := by
  norm_num [schemaRuleInteraction]

#print axioms workNormalizedNetSchemaValue_pos_iff
#print axioms workNormalized_calibrated_gate_iff
#print axioms netSchemaValue_nonpos_of_closed_channels
#print axioms positive_margin_pays_for_work
#print axioms excess_work_rejects_schema
#print axioms schemaRuleInteraction_natCast_eq_architectureUpdateInteraction
#print axioms schemaRuleInteraction_eq_zero_iff
#print axioms additive_static_schema_effect_has_zero_interaction
#print axioms schemaRuleInteraction_eq_dynamic_surplus
#print axioms three_cells_do_not_identify_schemaRuleInteraction
#print axioms schemaRuleInteraction_positive_example
#print axioms schemaRuleInteraction_zero_example

end Mettapedia.GSLT.LanguageDef.GauthierSchemaValueGate
