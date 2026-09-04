import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# Probability alignment for constrained semantic decoding

Hard support correctness and probabilistic faithfulness are different
properties.  Renormalizing the next-action distribution on currently legal
actions is generally not the original trace distribution conditioned on
eventual acceptance.  The latter is the finite-state Doob transform and
weights a legal child by its future survival probability.

This module keeps the algebra explicit, proves normalization and the equality
condition, supplies a finite distortion witness, and decomposes legal-target
negative log likelihood into within-support ranking and legal-mass terms.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.TypedGraphDecoding.ProbabilityAlignment

noncomputable section

universe uAction

variable {Action : Type uAction} [DecidableEq Action]

/-- Probability mass currently assigned to checker-legal actions. -/
def legalMass (legal : Finset Action) (probability : Action → ℝ) : ℝ :=
  ∑ action ∈ legal, probability action

/-- Mass that both takes a legal action and later reaches acceptance. -/
def acceptedMass (legal : Finset Action) (probability survival : Action → ℝ) : ℝ :=
  ∑ action ∈ legal, probability action * survival action

/-- Ordinary local hard-mask renormalization. -/
def locallyMasked (legal : Finset Action) (probability : Action → ℝ)
    (action : Action) : ℝ :=
  if action ∈ legal then probability action / legalMass legal probability else 0

/-- One-step globally conditioned distribution.  `survival action` is the
conditional probability of eventual acceptance after taking that child. -/
def globallyConditioned (legal : Finset Action)
    (probability survival : Action → ℝ) (action : Action) : ℝ :=
  if action ∈ legal then
    probability action * survival action /
      acceptedMass legal probability survival
  else 0

/-- Local masking is normalized whenever legal mass is nonzero. -/
theorem sum_locallyMasked_eq_one
    (legal : Finset Action) (probability : Action → ℝ)
    (nonzero : legalMass legal probability ≠ 0) :
    ∑ action ∈ legal, locallyMasked legal probability action = 1 := by
  calc
    (∑ action ∈ legal, locallyMasked legal probability action) =
        ∑ action ∈ legal,
          probability action / legalMass legal probability := by
            apply Finset.sum_congr rfl
            intro action member
            simp [locallyMasked, member]
    _ = (∑ action ∈ legal, probability action) /
        legalMass legal probability := by rw [Finset.sum_div]
    _ = 1 := by
      change legalMass legal probability / legalMass legal probability = 1
      exact div_self nonzero

/-- The Doob step is normalized whenever accepted mass is nonzero. -/
theorem sum_globallyConditioned_eq_one
    (legal : Finset Action) (probability survival : Action → ℝ)
    (nonzero : acceptedMass legal probability survival ≠ 0) :
    ∑ action ∈ legal,
      globallyConditioned legal probability survival action = 1 := by
  calc
    (∑ action ∈ legal,
        globallyConditioned legal probability survival action) =
        ∑ action ∈ legal,
          (probability action * survival action) /
            acceptedMass legal probability survival := by
              apply Finset.sum_congr rfl
              intro action member
              simp [globallyConditioned, member]
    _ = (∑ action ∈ legal, probability action * survival action) /
        acceptedMass legal probability survival := by rw [Finset.sum_div]
    _ = 1 := by
      change acceptedMass legal probability survival /
        acceptedMass legal probability survival = 1
      exact div_self nonzero

/-- Pointwise equality is controlled by future survival weight.  For a
positive-mass action, local and global normalization agree exactly when the
child's survival times total legal mass equals total accepted mass. -/
theorem locallyMasked_eq_globallyConditioned_iff
    (legal : Finset Action) (probability survival : Action → ℝ)
    (action : Action) (member : action ∈ legal)
    (actionNonzero : probability action ≠ 0)
    (legalNonzero : legalMass legal probability ≠ 0)
    (acceptedNonzero : acceptedMass legal probability survival ≠ 0) :
    locallyMasked legal probability action =
        globallyConditioned legal probability survival action ↔
      survival action * legalMass legal probability =
        acceptedMass legal probability survival := by
  simp only [locallyMasked, globallyConditioned, member, if_true]
  field_simp [actionNonzero, legalNonzero, acceptedNonzero]
  constructor <;> intro equality
  · nlinarith
  · nlinarith

/-- Constant future survival on the legal support is sufficient for local
masking to equal global conditioning. -/
theorem locallyMasked_eq_globallyConditioned_of_constant_survival
    (legal : Finset Action) (probability survival : Action → ℝ)
    (constant : ℝ)
    (survivalConstant : ∀ action ∈ legal, survival action = constant)
    (legalNonzero : legalMass legal probability ≠ 0)
    (constantNonzero : constant ≠ 0)
    (action : Action) :
    locallyMasked legal probability action =
      globallyConditioned legal probability survival action := by
  classical
  have acceptedMassEq :
      acceptedMass legal probability survival =
        constant * legalMass legal probability := by
    unfold acceptedMass legalMass
    calc
      (∑ candidate ∈ legal, probability candidate * survival candidate) =
          ∑ candidate ∈ legal, probability candidate * constant := by
            apply Finset.sum_congr rfl
            intro candidate candidateMember
            rw [survivalConstant candidate candidateMember]
      _ = constant * ∑ candidate ∈ legal, probability candidate := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro candidate _candidateMember
            ring
  by_cases member : action ∈ legal
  · simp only [locallyMasked, globallyConditioned, member, if_true]
    rw [survivalConstant action member, acceptedMassEq]
    field_simp [legalNonzero, constantNonzero]
  · simp [locallyMasked, globallyConditioned, member]

/-- Hard masking preserves within-state score order when the normalizer is
positive.  This is a beam-order statement, not a sampling-distribution
statement across different states. -/
theorem locallyMasked_order_iff
    (legal : Finset Action) (probability : Action → ℝ)
    (first second : Action)
    (firstMember : first ∈ legal) (secondMember : second ∈ legal)
    (positive : 0 < legalMass legal probability) :
    locallyMasked legal probability first ≤
        locallyMasked legal probability second ↔
      probability first ≤ probability second := by
  simp only [locallyMasked, firstMember, secondMember, if_true]
  exact div_le_div_iff_of_pos_right positive

/-! ## Negative-log-likelihood decomposition -/

def negativeLogLikelihood (probability : ℝ) : ℝ :=
  -Real.log probability

/-- For a legal target, ordinary NLL is exactly masked NLL plus the penalty
for assigning insufficient total mass to the legal support. -/
theorem legal_target_nll_decomposition
    (targetProbability normalization : ℝ)
    (targetNonzero : targetProbability ≠ 0)
    (normalizationNonzero : normalization ≠ 0) :
    negativeLogLikelihood targetProbability =
      negativeLogLikelihood (targetProbability / normalization) +
        negativeLogLikelihood normalization := by
  unfold negativeLogLikelihood
  rw [Real.log_div targetNonzero normalizationNonzero]
  ring

/-! ## Finite distortion witness -/

private def fairProbability : Fin 2 → ℝ := fun _ => 1 / 2

private def unequalSurvival : Fin 2 → ℝ
  | 0 => 1
  | 1 => 1 / 2

private def bothActions : Finset (Fin 2) := Finset.univ

theorem fair_legalMass :
    legalMass bothActions fairProbability = 1 := by
  norm_num [legalMass, bothActions, fairProbability, Fin.sum_univ_two]

theorem fair_acceptedMass :
    acceptedMass bothActions fairProbability unequalSurvival = 3 / 4 := by
  norm_num [acceptedMass, bothActions, fairProbability, unequalSurvival,
    Fin.sum_univ_two]

/-- Both children are currently legal, so local masking leaves them at one
half each; conditioning on eventual acceptance changes them to two thirds and
one third. -/
theorem local_mask_is_not_global_conditioning :
    locallyMasked bothActions fairProbability 0 = 1 / 2 ∧
      locallyMasked bothActions fairProbability 1 = 1 / 2 ∧
      globallyConditioned bothActions fairProbability unequalSurvival 0 = 2 / 3 ∧
      globallyConditioned bothActions fairProbability unequalSurvival 1 = 1 / 3 := by
  have zeroMember : (0 : Fin 2) ∈ bothActions := by simp [bothActions]
  have oneMember : (1 : Fin 2) ∈ bothActions := by simp [bothActions]
  simp only [locallyMasked, globallyConditioned, zeroMember, oneMember,
    if_true]
  rw [fair_legalMass, fair_acceptedMass]
  norm_num [fairProbability, unequalSurvival]

theorem local_mask_distorts_conditioned_trace_distribution :
    locallyMasked bothActions fairProbability 0 ≠
      globallyConditioned bothActions fairProbability unequalSurvival 0 := by
  rw [local_mask_is_not_global_conditioning.1,
    local_mask_is_not_global_conditioning.2.2.1]
  norm_num

#print axioms sum_locallyMasked_eq_one
#print axioms sum_globallyConditioned_eq_one
#print axioms locallyMasked_eq_globallyConditioned_iff
#print axioms locallyMasked_eq_globallyConditioned_of_constant_survival
#print axioms locallyMasked_order_iff
#print axioms legal_target_nll_decomposition
#print axioms local_mask_is_not_global_conditioning
#print axioms local_mask_distorts_conditioned_trace_distribution

end

end Mettapedia.GSLT.LanguageDef.TypedGraphDecoding.ProbabilityAlignment
