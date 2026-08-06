/-
# Gauthier action evidence in the categorical WM-PC register

This module instantiates the generic categorical evidence-register bridge on
the actual sixteen-action `orgMemoSignature`.  Positive discoveries support
their action.  A refutation supplies maximum-entropy opposition evidence: one
unit of total mass distributed uniformly over the alternative actions and
none for the refuted action.  A
budget-undetermined observation remains outside the decided action register.

The exact checker mask is applied after the common posterior.  Consequently
the static and settled readouts consume the same information and have exactly
the same legal support; this is an information-parity result, not an efficacy
claim.
-/

import Mettapedia.GSLT.LanguageDef.Gauthier.AlignmentEvidence
import Mettapedia.PLN.Bridges.PredictiveCoding.CategoricalEvidenceRegisterBridge

namespace Mettapedia.GSLT.LanguageDef.GauthierActionEvidencePCBridge

open Mettapedia.GSLT.LanguageDef.GauthierSkeleton
open Mettapedia.GSLT.LanguageDef.GauthierSkeletonMask
open Mettapedia.GSLT.LanguageDef.GauthierAlignmentEvidence
open Mettapedia.PLN.Bridges.PredictiveCoding
open Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceDirichlet
open Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier.EvidentialOpinion

instance : Nonempty OperatorAction :=
  ⟨⟨0, by rw [operatorCount_eq]; omega⟩⟩

@[simp] theorem oneHot_total (action : OperatorAction) :
    (GradedActionEvidence.oneHot action).total = 1 := by
  simp [MultiEvidence.total, GradedActionEvidence.oneHot]

/-- Raw alternative support induced by graded observations.  A negative
observation for action `i` supports every action except `i`; undetermined
observations are deliberately absent.  Normalization by the number of
alternatives occurs in `actionEvidenceRegister`, so one refutation has total
evidence mass one rather than `operatorCount - 1`. -/
def oppositionSupportCounts
    (evidence : GradedActionEvidence operatorCount) :
    MultiEvidence operatorCount :=
  ⟨fun action => evidence.positive.counts action +
    (evidence.negative.total - evidence.negative.counts action)⟩

/-- Number of alternatives to one refuted action. -/
def oppositionScale : Nat := operatorCount - 1

theorem oppositionScale_eq : oppositionScale = 15 := by
  norm_num [oppositionScale, operatorCount, orgMemoSignature,
    Mettapedia.GSLT.LanguageDef.GauthierE2.intlSignature,
    Mettapedia.GSLT.LanguageDef.GauthierE2.orgSignature,
    Mettapedia.GSLT.LanguageDef.GauthierE2.listOps]

/-- The actual categorical evidence register consumed by both readouts. -/
noncomputable def actionEvidenceRegister
    (evidence : GradedActionEvidence operatorCount) : Opinion OperatorAction :=
  { evidence := fun action =>
      evidence.positive.counts action +
        ((evidence.negative.total - evidence.negative.counts action : Nat) : ℝ) /
          oppositionScale
    evidence_nonneg := by
      intro action
      exact add_nonneg (Nat.cast_nonneg _)
        (div_nonneg (Nat.cast_nonneg _) (by norm_num [oppositionScale_eq])) }

/-- Exact operator-only view of the established checker mask.  EOS remains a
separate decoder action and is intentionally not embedded in `OperatorAction`. -/
def checkerOperatorLegal (state : MaskState) (action : OperatorAction) : Bool :=
  decide (Int.ofNat action.val ∈ legalTokens orgMemoSignature state)

/-- Static, checker-masked action distribution. -/
noncomputable def staticActionReadout
    (evidence : GradedActionEvidence operatorCount) (state : MaskState)
    (action : OperatorAction) : ℝ :=
  maskedCategoricalDistribution (actionEvidenceRegister evidence)
    (checkerOperatorLegal state) action

/-- Exact scaled concentration.  Multiplication by `oppositionScale` clears
the common denominator introduced by normalized negative evidence; it leaves
the final categorical distribution unchanged. -/
def scaledActionConcentration
    (evidence : GradedActionEvidence operatorCount)
    (action : OperatorAction) : Nat :=
  oppositionScale * (evidence.positive.counts action + 1) +
    (evidence.negative.total - evidence.negative.counts action)

/-- Exact denominator of the masked categorical action distribution. -/
def maskedScaledConcentrationTotal
    (evidence : GradedActionEvidence operatorCount) (state : MaskState) : Nat :=
  ∑ action, if checkerOperatorLegal state action then
    scaledActionConcentration evidence action else 0

/-- Executable rational representation used by the cross-runtime fixture. -/
structure ExactActionProbability where
  action : Nat
  legal : Bool
  numerator : Nat
  denominator : Nat
  deriving DecidableEq, Repr

def exactActionProbability
    (evidence : GradedActionEvidence operatorCount) (state : MaskState)
    (action : OperatorAction) : ExactActionProbability :=
  let legal := checkerOperatorLegal state action
  { action := action.val
    legal
    numerator := if legal then scaledActionConcentration evidence action else 0
    denominator := maskedScaledConcentrationTotal evidence state }

def exactMaskedActionDistribution
    (evidence : GradedActionEvidence operatorCount) (state : MaskState) :
    List ExactActionProbability :=
  (List.finRange operatorCount).map
    (exactActionProbability evidence state)

/-- The executable natural-number ratio is exactly the real-valued static/PC
distribution proved above. -/
theorem staticActionReadout_eq_exactRatio
    (evidence : GradedActionEvidence operatorCount) (state : MaskState)
    (hlegal : ∃ action, checkerOperatorLegal state action = true)
    (action : OperatorAction) :
    staticActionReadout evidence state action =
      (if checkerOperatorLegal state action then
          (scaledActionConcentration evidence action : ℝ) else 0) /
        (maskedScaledConcentrationTotal evidence state : ℝ) := by
  rw [staticActionReadout,
    maskedCategoricalDistribution_eq_concentrationRatio
      (actionEvidenceRegister evidence) (checkerOperatorLegal state) hlegal action]
  have hcoordinate : ∀ index : OperatorAction,
      concentration (actionEvidenceRegister evidence) index =
        (scaledActionConcentration evidence index : ℝ) / oppositionScale := by
    intro index
    simp only [actionEvidenceRegister, concentration, scaledActionConcentration,
      Nat.cast_add, Nat.cast_mul]
    rw [oppositionScale_eq]
    norm_num
    ring
  have htotal :
      maskedConcentrationTotal (actionEvidenceRegister evidence)
          (checkerOperatorLegal state) =
        (maskedScaledConcentrationTotal evidence state : ℝ) /
          oppositionScale := by
    unfold maskedConcentrationTotal maskedScaledConcentrationTotal
    rw [Nat.cast_sum]
    simp only [Nat.cast_ite, Nat.cast_zero]
    calc
      (∑ index,
          if checkerOperatorLegal state index = true then
            concentration (actionEvidenceRegister evidence) index else 0) =
        ∑ index,
          (if checkerOperatorLegal state index = true then
              (scaledActionConcentration evidence index : ℝ) else 0) /
            oppositionScale := by
          apply Finset.sum_congr rfl
          intro index _
          by_cases h : checkerOperatorLegal state index = true
          · rw [if_pos h, if_pos h, hcoordinate]
          · rw [if_neg h, if_neg h]
            norm_num
      _ = (∑ index,
          if checkerOperatorLegal state index = true then
            (scaledActionConcentration evidence index : ℝ) else 0) /
          oppositionScale := by rw [Finset.sum_div]
  rw [htotal]
  by_cases h : checkerOperatorLegal state action = true
  · rw [if_pos h, if_pos h, hcoordinate]
    exact div_div_div_cancel_right₀
      (by norm_num [oppositionScale_eq] : (oppositionScale : ℝ) ≠ 0) _ _
  · rw [if_neg h, if_neg h]
    rw [zero_div, zero_div]

/-- The PC evidence-energy equilibrium over the same register. -/
noncomputable def ActionPCEnergyEquilibrium
    (evidence : GradedActionEvidence operatorCount)
    (settled : OperatorAction → ℝ) : Prop :=
  CategoricalPCEquilibrium (actionEvidenceRegister evidence) settled

/-- Undetermined evidence has no hidden path into decided action support. -/
theorem oppositionSupportCounts_ignores_undetermined
    (positive negative firstUndetermined secondUndetermined :
      MultiEvidence operatorCount) :
    oppositionSupportCounts
        ⟨positive, negative, firstUndetermined⟩ =
      oppositionSupportCounts
        ⟨positive, negative, secondUndetermined⟩ := by
  rfl

/-- **Actual Gauthier information parity.**  A settled PC readout equals the
WM-PLN categorical posterior, and both have support exactly on the operator
actions currently admitted by the established checker mask. -/
theorem settledActionReadout_eq_static_and_same_checker_support
    (evidence : GradedActionEvidence operatorCount)
    (settled : OperatorAction → ℝ)
    (hsettled : ActionPCEnergyEquilibrium evidence settled)
    (state : MaskState)
    (hlegal : ∃ action, checkerOperatorLegal state action = true) :
    settled = categoricalPosterior (actionEvidenceRegister evidence) ∧
      (∀ action,
        staticActionReadout evidence state action ≠ 0 ↔
          checkerOperatorLegal state action = true) := by
  exact staticReadout_eq_settledReadout_and_sameSupport
    (actionEvidenceRegister evidence) settled hsettled
    (checkerOperatorLegal state) hlegal

/-- The exact checker still owns support: an illegal operator receives zero
regardless of its categorical evidence count. -/
theorem illegal_operator_has_zero_static_support
    (evidence : GradedActionEvidence operatorCount)
    (state : MaskState) (action : OperatorAction)
    (hillegal : checkerOperatorLegal state action = false) :
    staticActionReadout evidence state action = 0 := by
  simp [staticActionReadout, maskedCategoricalDistribution,
    maskedCategoricalScore, hillegal]

/-! ## Concrete sixteen-action boundaries -/

def actionZero : OperatorAction :=
  ⟨0, by rw [operatorCount_eq]; omega⟩

def actionOne : OperatorAction :=
  ⟨1, by rw [operatorCount_eq]; omega⟩

/-- One refutation does not positively support the refuted action. -/
theorem one_refutation_zero_self_support :
    (oppositionSupportCounts
      (GradedActionEvidence.ofVerdict actionZero .provablyPartial)).counts
        actionZero = 0 := by
  change 0 + ((GradedActionEvidence.oneHot actionZero).total -
    (GradedActionEvidence.oneHot actionZero).counts actionZero) = 0
  rw [oneHot_total]
  simp [GradedActionEvidence.oneHot]

/-- Before normalization, the same refutation supplies one integer opposition
count to another action.  `actionEvidenceRegister` divides each such count by
fifteen, so the alternatives jointly receive one unit of evidence mass. -/
theorem one_refutation_supports_alternative :
    (oppositionSupportCounts
      (GradedActionEvidence.ofVerdict actionZero .provablyPartial)).counts
        actionOne = 1 := by
  have hne : actionOne ≠ actionZero := by
    intro heq
    have := congrArg Fin.val heq
    norm_num [actionZero, actionOne] at this
  change 0 + ((GradedActionEvidence.oneHot actionZero).total -
    (GradedActionEvidence.oneHot actionZero).counts actionOne) = 1
  rw [oneHot_total]
  simp [GradedActionEvidence.oneHot, hne]

/-- Normalization is evidence-conservative: one refutation raises the total
Dirichlet precision from the sixteen-unit neutral prior to exactly seventeen,
not to thirty-one. -/
theorem one_refutation_precision_eq_prior_plus_one :
    categoricalPrecision
      (actionEvidenceRegister
        (GradedActionEvidence.ofVerdict actionZero .provablyPartial)) = 17 := by
  unfold categoricalPrecision strength concentration actionEvidenceRegister
  simp only [GradedActionEvidence.ofVerdict, MultiEvidence.zero, Nat.cast_zero,
    zero_add]
  rw [oneHot_total, oppositionScale_eq]
  simp only [GradedActionEvidence.oneHot]
  rw [Finset.sum_add_distrib]
  have hsum :
      (∑ action : OperatorAction,
        (↑((1 : Nat) - if action = actionZero then (1 : Nat) else 0) : ℝ) /
          (15 : ℝ)) = 1 := by
    calc
      (∑ action : OperatorAction,
          (↑((1 : Nat) - if action = actionZero then (1 : Nat) else 0) : ℝ) /
            (15 : ℝ)) =
        ∑ action : OperatorAction,
          (((1 : ℝ) - if action = actionZero then 1 else 0) / 15) := by
            apply Finset.sum_congr rfl
            intro action _
            by_cases h : action = actionZero <;> simp [h]
      _ = (∑ action : OperatorAction,
          ((1 : ℝ) - if action = actionZero then 1 else 0)) / 15 := by
            rw [Finset.sum_div]
      _ = ((∑ _action : OperatorAction, (1 : ℝ)) -
          ∑ action : OperatorAction,
            (if action = actionZero then (1 : ℝ) else 0)) / 15 := by
            rw [Finset.sum_sub_distrib]
      _ = 1 := by norm_num [operatorCount_eq]
  calc
    (∑ action : OperatorAction,
        (↑((1 : Nat) - if action = actionZero then (1 : Nat) else 0) : ℝ) /
          (15 : ℝ)) +
        ∑ _action : OperatorAction, (1 : ℝ) =
      1 + ∑ _action : OperatorAction, (1 : ℝ) := by rw [hsum]
    _ = 17 := by norm_num [operatorCount_eq]

/-- At the initial three-token decoder state the zero operator is genuinely
checker-legal in the authenticated signature. -/
theorem initial_actionZero_legal :
    checkerOperatorLegal (initial 3) actionZero = true := by
  decide

/-- An arity-five action cannot be emitted from an empty stack and therefore
has no support at the same decoder state. -/
def actionArityFive : OperatorAction :=
  ⟨13, by rw [operatorCount_eq]; omega⟩

theorem initial_actionArityFive_illegal :
    checkerOperatorLegal (initial 3) actionArityFive = false := by
  decide

theorem initial_actionArityFive_zero_distribution
    (evidence : GradedActionEvidence operatorCount) :
    staticActionReadout evidence (initial 3) actionArityFive = 0 :=
  illegal_operator_has_zero_static_support evidence (initial 3) actionArityFive
    initial_actionArityFive_illegal

#print axioms oppositionSupportCounts_ignores_undetermined
#print axioms settledActionReadout_eq_static_and_same_checker_support
#print axioms staticActionReadout_eq_exactRatio
#print axioms illegal_operator_has_zero_static_support
#print axioms one_refutation_zero_self_support
#print axioms one_refutation_supports_alternative
#print axioms one_refutation_precision_eq_prior_plus_one
#print axioms initial_actionZero_legal
#print axioms initial_actionArityFive_zero_distribution

end Mettapedia.GSLT.LanguageDef.GauthierActionEvidencePCBridge
