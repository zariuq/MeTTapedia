import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic
import Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceDirichlet

/-!
# Continuous evidential opinions for the unified carrier

Sensoy, Kaplan, and Kandemir, *Evidential Deep Learning to Quantify
Classification Uncertainty* (2018, arXiv:1806.01768), Section 3,
Equations (1)--(2), map nonnegative neural evidence `eᵢ` to Dirichlet
concentrations `αᵢ = eᵢ + 1`.  With strength `S = ∑ᵢ αᵢ`, singleton belief is
`bᵢ = eᵢ / S`, uncertainty is `u = K / S`, and the categorical posterior mean
is `αᵢ / S`.

This file formalizes that finite evidence chart and the boundaries needed by
an evidence-carrying recurrent state.

* Belief and uncertainty conserve unit mass.
* The posterior mean is belief plus the uniform base-rate share of
  uncertainty.
* Fresh evidence adds to strength once and strictly lowers uncertainty when
  its total mass is positive.
* Adding posterior concentrations instead of evidence double-counts one unit
  of prior concentration per class.
* Uniformly rescaling every concentration preserves all posterior means while
  changing uncertainty.  Thus a point prediction does not determine
  epistemic uncertainty.
* A binary high-conflict opinion and the zero-evidence opinion both predict
  `(1/2, 1/2)`, yet their uncertainties are `1/10` and `1`.

The formulas do not certify calibration, out-of-distribution detection,
adversarial robustness, or the behavior of a neural evidence map.  Those are
empirical and executable obligations.

Source artifact SHA-256:
`5b7034752f90d4ca12e30cbf943f7fc06c8eec0a2afb3393d908f164f65098a4`.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier

namespace EvidentialOpinion

open scoped BigOperators

noncomputable section

/-- A finite vector of nonnegative continuous evidence.  This is the neural
analogue of the natural-number counts in `MultiEvidence`. -/
@[ext]
structure Opinion (Class : Type*) where
  evidence : Class → ℝ
  evidence_nonneg : ∀ classIndex, 0 ≤ evidence classIndex

variable {Class : Type*} [Fintype Class] [Nonempty Class]

/-- Number of classes, represented in the scalar evidence field. -/
def classCount : ℝ :=
  Fintype.card Class

/-- Total continuous evidence before adding the unit Dirichlet base rate. -/
def totalEvidence (opinion : Opinion Class) : ℝ :=
  ∑ classIndex, opinion.evidence classIndex

/-- Dirichlet concentration `αᵢ = eᵢ + 1`. -/
def concentration
    (opinion : Opinion Class) (classIndex : Class) : ℝ :=
  opinion.evidence classIndex + 1

/-- Dirichlet strength `S = ∑ᵢ αᵢ`. -/
def strength (opinion : Opinion Class) : ℝ :=
  ∑ classIndex, concentration opinion classIndex

/-- Singleton belief mass `bᵢ = eᵢ / S`. -/
def belief (opinion : Opinion Class) (classIndex : Class) : ℝ :=
  opinion.evidence classIndex / strength opinion

/-- Epistemic uncertainty mass `u = K / S`. -/
def uncertainty (opinion : Opinion Class) : ℝ :=
  classCount (Class := Class) / strength opinion

/-- Dirichlet posterior mean `αᵢ / S`. -/
def posteriorMean
    (opinion : Opinion Class) (classIndex : Class) : ℝ :=
  concentration opinion classIndex / strength opinion

theorem classCount_pos :
    0 < classCount (Class := Class) := by
  simpa only [classCount] using
    (Nat.cast_pos.mpr (Fintype.card_pos (α := Class)) :
      0 < (Fintype.card Class : ℝ))

omit [Nonempty Class] in
theorem totalEvidence_nonneg (opinion : Opinion Class) :
    0 ≤ totalEvidence opinion :=
  Finset.sum_nonneg fun classIndex _ => opinion.evidence_nonneg classIndex

omit [Nonempty Class] in
/-- Strength is total evidence plus one unit base concentration per class. -/
theorem strength_eq_totalEvidence_add_classCount
    (opinion : Opinion Class) :
    strength opinion =
      totalEvidence opinion + classCount (Class := Class) := by
  simp [strength, concentration, totalEvidence, classCount,
    Finset.sum_add_distrib]

theorem strength_pos (opinion : Opinion Class) :
    0 < strength opinion := by
  rw [strength_eq_totalEvidence_add_classCount]
  exact add_pos_of_nonneg_of_pos
    (totalEvidence_nonneg opinion) classCount_pos

omit [Fintype Class] [Nonempty Class] in
theorem concentration_pos
    (opinion : Opinion Class) (classIndex : Class) :
    0 < concentration opinion classIndex := by
  exact lt_add_of_le_of_pos
    (opinion.evidence_nonneg classIndex) zero_lt_one

theorem belief_nonneg
    (opinion : Opinion Class) (classIndex : Class) :
    0 ≤ belief opinion classIndex :=
  div_nonneg (opinion.evidence_nonneg classIndex)
    (strength_pos opinion).le

theorem uncertainty_pos (opinion : Opinion Class) :
    0 < uncertainty opinion :=
  div_pos classCount_pos (strength_pos opinion)

theorem posteriorMean_pos
    (opinion : Opinion Class) (classIndex : Class) :
    0 < posteriorMean opinion classIndex :=
  div_pos (concentration_pos opinion classIndex) (strength_pos opinion)

/-- Subjective-logic mass conservation: singleton beliefs plus uncertainty
sum to one. -/
theorem uncertainty_add_sum_belief (opinion : Opinion Class) :
    uncertainty opinion + ∑ classIndex, belief opinion classIndex = 1 := by
  simp only [uncertainty, belief, ← Finset.sum_div]
  rw [← add_div]
  rw [add_comm, ← totalEvidence]
  rw [← strength_eq_totalEvidence_add_classCount]
  exact div_self (ne_of_gt (strength_pos opinion))

/-- The Dirichlet categorical means form a probability vector. -/
theorem sum_posteriorMean (opinion : Opinion Class) :
    ∑ classIndex, posteriorMean opinion classIndex = 1 := by
  simp only [posteriorMean, ← Finset.sum_div]
  change strength opinion / strength opinion = 1
  exact div_self (ne_of_gt (strength_pos opinion))

/-- The posterior mean is belief plus the uniform base-rate allocation of
uncertainty. -/
theorem posteriorMean_eq_belief_add_uniform_uncertainty
    (opinion : Opinion Class) (classIndex : Class) :
    posteriorMean opinion classIndex =
      belief opinion classIndex +
        (1 / classCount (Class := Class)) * uncertainty opinion := by
  have hcount : classCount (Class := Class) ≠ 0 :=
    ne_of_gt classCount_pos
  have hstrength : strength opinion ≠ 0 :=
    ne_of_gt (strength_pos opinion)
  simp only [posteriorMean, belief, uncertainty, concentration]
  field_simp

/-! ## Evidence fusion and the exactly-once prior boundary -/

/-- Fuse two independent continuous evidence packets by adding evidence, not
posterior concentrations. -/
def fuse (first second : Opinion Class) : Opinion Class where
  evidence := fun classIndex =>
    first.evidence classIndex + second.evidence classIndex
  evidence_nonneg := fun classIndex =>
    add_nonneg
      (first.evidence_nonneg classIndex)
      (second.evidence_nonneg classIndex)

omit [Fintype Class] [Nonempty Class] in
@[simp]
theorem fuse_evidence
    (first second : Opinion Class) (classIndex : Class) :
    (fuse first second).evidence classIndex =
      first.evidence classIndex + second.evidence classIndex :=
  rfl

omit [Nonempty Class] in
theorem totalEvidence_fuse (first second : Opinion Class) :
    totalEvidence (fuse first second) =
      totalEvidence first + totalEvidence second := by
  simp [totalEvidence, fuse, Finset.sum_add_distrib]

omit [Nonempty Class] in
/-- A fresh packet adds exactly its evidence mass to existing strength; the
unit Dirichlet base rate is not imported again. -/
theorem strength_fuse_eq_strength_add_totalEvidence
    (first second : Opinion Class) :
    strength (fuse first second) =
      strength first + totalEvidence second := by
  rw [strength_eq_totalEvidence_add_classCount,
    totalEvidence_fuse, strength_eq_totalEvidence_add_classCount]
  ring

omit [Fintype Class] [Nonempty Class] in
/-- Adding posterior concentrations directly counts the unit base rate twice.
The excess is exactly one concentration unit in every class. -/
theorem concentration_add_doubleCounts_prior
    (first second : Opinion Class) (classIndex : Class) :
    concentration first classIndex +
        concentration second classIndex =
      concentration (fuse first second) classIndex + 1 := by
  simp [concentration, fuse]
  ring

omit [Nonempty Class] in
/-- At the strength level, naive concentration addition overcounts the fused
opinion by exactly the number of classes. -/
theorem sum_concentration_add_eq_strength_fuse_add_classCount
    (first second : Opinion Class) :
    (∑ classIndex,
        (concentration first classIndex +
          concentration second classIndex)) =
      strength (fuse first second) + classCount (Class := Class) := by
  calc
    (∑ classIndex,
        (concentration first classIndex +
          concentration second classIndex)) =
        ∑ classIndex,
          (concentration (fuse first second) classIndex + 1) := by
            apply Finset.sum_congr rfl
            intro classIndex _
            exact concentration_add_doubleCounts_prior
              first second classIndex
    _ = strength (fuse first second) +
          classCount (Class := Class) := by
      simp [strength, classCount, Finset.sum_add_distrib]

/-- Adding any nonnegative evidence packet cannot increase uncertainty. -/
theorem uncertainty_fuse_le
    (first second : Opinion Class) :
    uncertainty (fuse first second) ≤ uncertainty first := by
  have hfirst := strength_pos first
  have htotal := totalEvidence_nonneg second
  rw [uncertainty, uncertainty,
    strength_fuse_eq_strength_add_totalEvidence]
  have hfusedDenominator :
      0 < strength first + totalEvidence second :=
    add_pos_of_pos_of_nonneg hfirst htotal
  rw [div_le_div_iff₀ hfusedDenominator hfirst]
  nlinarith [classCount_pos (Class := Class)]

/-- A packet with strictly positive total evidence strictly lowers
uncertainty. -/
theorem uncertainty_fuse_lt
    (first second : Opinion Class)
    (hpositive : 0 < totalEvidence second) :
    uncertainty (fuse first second) < uncertainty first := by
  have hfirst := strength_pos first
  rw [uncertainty, uncertainty,
    strength_fuse_eq_strength_add_totalEvidence]
  have hfusedDenominator :
      0 < strength first + totalEvidence second :=
    add_pos hfirst hpositive
  rw [div_lt_div_iff₀ hfusedDenominator hfirst]
  nlinarith [classCount_pos (Class := Class)]

/-! ## Concentration rescaling separates prediction from uncertainty -/

/-- Rescale every Dirichlet concentration by a factor at least one, then
return to evidence coordinates. -/
def rescaleConcentration
    (scale : ℝ) (hscale : 1 ≤ scale)
    (opinion : Opinion Class) : Opinion Class where
  evidence := fun classIndex =>
    scale * (opinion.evidence classIndex + 1) - 1
  evidence_nonneg := by
    intro classIndex
    have hfactor : 1 ≤ opinion.evidence classIndex + 1 := by
      linarith [opinion.evidence_nonneg classIndex]
    have hscaleNonneg : 0 ≤ scale := zero_le_one.trans hscale
    have hproduct :
        1 * 1 ≤ scale * (opinion.evidence classIndex + 1) :=
      mul_le_mul hscale hfactor zero_le_one hscaleNonneg
    linarith

omit [Fintype Class] [Nonempty Class] in
@[simp]
theorem concentration_rescaleConcentration
    (scale : ℝ) (hscale : 1 ≤ scale)
    (opinion : Opinion Class) (classIndex : Class) :
    concentration (rescaleConcentration scale hscale opinion) classIndex =
      scale * concentration opinion classIndex := by
  simp [concentration, rescaleConcentration]

omit [Nonempty Class] in
theorem strength_rescaleConcentration
    (scale : ℝ) (hscale : 1 ≤ scale)
    (opinion : Opinion Class) :
    strength (rescaleConcentration scale hscale opinion) =
      scale * strength opinion := by
  simp [strength, concentration_rescaleConcentration,
    Finset.mul_sum]

/-- Uniform concentration rescaling preserves every categorical posterior
mean exactly. -/
theorem posteriorMean_rescaleConcentration
    (scale : ℝ) (hscale : 1 ≤ scale)
    (opinion : Opinion Class) (classIndex : Class) :
    posteriorMean (rescaleConcentration scale hscale opinion) classIndex =
      posteriorMean opinion classIndex := by
  have hscalePos : 0 < scale := zero_lt_one.trans_le hscale
  rw [posteriorMean, concentration_rescaleConcentration,
    strength_rescaleConcentration, posteriorMean]
  field_simp [ne_of_gt hscalePos, ne_of_gt (strength_pos opinion)]

/-- The same rescaling divides epistemic uncertainty by its scale. -/
theorem uncertainty_rescaleConcentration
    (scale : ℝ) (hscale : 1 ≤ scale)
    (opinion : Opinion Class) :
    uncertainty (rescaleConcentration scale hscale opinion) =
      uncertainty opinion / scale := by
  have hscalePos : 0 < scale := zero_lt_one.trans_le hscale
  rw [uncertainty, strength_rescaleConcentration, uncertainty]
  field_simp [ne_of_gt hscalePos, ne_of_gt (strength_pos opinion)]

/-- Rescaling by a factor above one keeps the complete point prediction but
strictly lowers uncertainty. -/
theorem samePosteriorMean_strictlyLowerUncertainty_of_one_lt_scale
    (scale : ℝ) (hscale : 1 < scale)
    (opinion : Opinion Class) :
    (∀ classIndex,
      posteriorMean
          (rescaleConcentration scale hscale.le opinion) classIndex =
        posteriorMean opinion classIndex) ∧
      uncertainty
          (rescaleConcentration scale hscale.le opinion) <
        uncertainty opinion := by
  constructor
  · intro classIndex
    exact posteriorMean_rescaleConcentration
      scale hscale.le opinion classIndex
  · rw [uncertainty_rescaleConcentration scale hscale.le opinion]
    have hu : 0 < uncertainty opinion := uncertainty_pos opinion
    rw [div_lt_iff₀ (zero_lt_one.trans hscale)]
    nlinarith

/-! ## Executable positive and negative boundaries -/

/-- Complete ignorance: no class has evidence. -/
def zeroOpinion : Opinion Class where
  evidence := fun _ => 0
  evidence_nonneg := fun _ => le_rfl

omit [Nonempty Class] in
theorem zeroOpinion_belief (classIndex : Class) :
    belief (zeroOpinion : Opinion Class) classIndex = 0 := by
  simp [belief, zeroOpinion]

theorem zeroOpinion_uncertainty :
    uncertainty (zeroOpinion : Opinion Class) = 1 := by
  simp [uncertainty, strength, concentration, zeroOpinion, classCount]

omit [Nonempty Class] in
theorem zeroOpinion_posteriorMean (classIndex : Class) :
    posteriorMean (zeroOpinion : Opinion Class) classIndex =
      1 / classCount (Class := Class) := by
  simp [posteriorMean, strength, concentration, zeroOpinion, classCount]

/-- High but perfectly conflicting binary evidence. -/
def binaryHighConflict : Opinion Bool where
  evidence := fun _ => 9
  evidence_nonneg := fun _ => by norm_num

/-- Zero evidence and high balanced conflict have the same point prediction
but radically different uncertainty. -/
theorem binary_sameMean_differentUncertainty :
    (∀ classIndex : Bool,
      posteriorMean (zeroOpinion : Opinion Bool) classIndex =
        posteriorMean binaryHighConflict classIndex) ∧
      uncertainty (zeroOpinion : Opinion Bool) = 1 ∧
      uncertainty binaryHighConflict = 1 / 10 := by
  constructor
  · intro classIndex
    cases classIndex <;>
      norm_num [posteriorMean, strength, concentration,
        zeroOpinion, binaryHighConflict]
  · constructor
    · exact zeroOpinion_uncertainty (Class := Bool)
    · norm_num [uncertainty, strength, concentration,
        binaryHighConflict, classCount]

end

end EvidentialOpinion

end Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier
