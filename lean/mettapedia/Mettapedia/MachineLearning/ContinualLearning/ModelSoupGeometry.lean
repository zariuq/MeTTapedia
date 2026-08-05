import Mettapedia.MachineLearning.ContinualLearning.RandomFourierOnlineClassifier

/-!
# Model-soup geometry and greedy admission

Wortsman et al., *Model soups: averaging weights of multiple fine-tuned models
improves accuracy without increasing inference time* (ICML 2022,
arXiv:2203.05482), average independently fine-tuned parameter vectors and
accept a candidate into the greedy soup only when validation accuracy does not
decrease.

This file isolates two exact boundaries behind that construction:

* for an affine predictor, prediction at a two-model parameter soup is exactly
  the corresponding output ensemble;
* greedy admission makes the validation score of the current soup
  monotonically nondecreasing, independently of the proposal order.

Neither statement extends to an arbitrary nonlinear predictor.  A scalar
square predictor gives two individually perfect endpoints whose uniform soup
is strictly worse and whose soup prediction differs from their output
ensemble.

The results do not prove that independently trained neural networks share a
low-loss basin, that validation improvement transfers to test accuracy, or
that a soup outperforms either an ensemble or every endpoint.
-/

namespace Mettapedia.MachineLearning.ContinualLearning

namespace ModelSoupGeometry

noncomputable section

section TwoModelSoup

variable {Parameter Output : Type*}
  [AddCommGroup Parameter] [Module ℝ Parameter]
  [AddCommGroup Output] [Module ℝ Output]

/-- Parameter interpolation for a two-model soup. -/
def twoSoup
    (weight : ℝ) (left right : Parameter) : Parameter :=
  (1 - weight) • left + weight • right

/-- Output interpolation for the corresponding two-model ensemble. -/
def twoEnsemble
    (predict : Parameter → Output)
    (weight : ℝ) (left right : Parameter) : Output :=
  (1 - weight) • predict left + weight • predict right

/-- A linear predictor commutes exactly with two-model souping. -/
theorem linearPredict_twoSoup
    (predict : Parameter →ₗ[ℝ] Output)
    (weight : ℝ) (left right : Parameter) :
    predict (twoSoup weight left right) =
      twoEnsemble predict weight left right := by
  simp [twoSoup, twoEnsemble]

/-- An affine predictor also commutes with two-model souping because the
interpolation coefficients sum to one. -/
theorem affinePredict_twoSoup
    (linear : Parameter →ₗ[ℝ] Output)
    (bias : Output)
    (weight : ℝ) (left right : Parameter) :
    linear (twoSoup weight left right) + bias =
      twoEnsemble (fun parameter => linear parameter + bias)
        weight left right := by
  simp only [twoSoup, twoEnsemble, map_add, map_smul]
  module

/-- The identity predictor is a concrete positive fixture for exact
soup--ensemble coincidence. -/
theorem identity_uniformSoup_eq_ensemble :
    twoSoup (1 / 2 : ℝ) 2 4 =
      twoEnsemble (fun value : ℝ => value) (1 / 2 : ℝ) 2 4 := by
  norm_num [twoSoup, twoEnsemble]

end TwoModelSoup

section GreedyAdmission

variable {Parameter : Type*}
  [NormedAddCommGroup Parameter] [NormedSpace ℝ Parameter]

open RandomFourierOnlineClassifier

/-- Validation score of the exactly weighted mean of the current
ingredients. -/
def soupScore
    (validation : Parameter → ℝ)
    (ingredients : List Parameter) : ℝ :=
  validation (onlineMean ingredients)

/-- The source's greedy admission step: retain a candidate exactly when the
score of the enlarged soup does not fall. -/
def greedyStep
    (validation : Parameter → ℝ)
    (ingredients : List Parameter)
    (candidate : Parameter) : List Parameter :=
  if soupScore validation ingredients ≤
      soupScore validation (candidate :: ingredients) then
    candidate :: ingredients
  else
    ingredients

/-- One greedy admission step cannot reduce the current validation score. -/
theorem soupScore_greedyStep_ge
    (validation : Parameter → ℝ)
    (ingredients : List Parameter)
    (candidate : Parameter) :
    soupScore validation ingredients ≤
      soupScore validation (greedyStep validation ingredients candidate) := by
  unfold greedyStep
  split_ifs with accepted
  · exact accepted
  · exact le_rfl

/-- Sequential greedy construction from an initial ingredient list. -/
def greedySoup
    (validation : Parameter → ℝ)
    (initial candidates : List Parameter) : List Parameter :=
  candidates.foldl (greedyStep validation) initial

/-- Greedy admission is validation-monotone over every finite proposal
sequence. -/
theorem soupScore_greedySoup_ge
    (validation : Parameter → ℝ)
    (initial candidates : List Parameter) :
    soupScore validation initial ≤
      soupScore validation (greedySoup validation initial candidates) := by
  induction candidates generalizing initial with
  | nil =>
      simp [greedySoup]
  | cons candidate candidates induction =>
      rw [greedySoup, List.foldl_cons]
      exact le_trans
        (soupScore_greedyStep_ge validation initial candidate)
        (induction (greedyStep validation initial candidate))

/-- Starting from the validation-best candidate therefore makes the final
greedy soup no worse than that candidate on the same validation score. -/
theorem greedySoup_no_worse_than_first
    (validation : Parameter → ℝ)
    (first : Parameter)
    (candidates : List Parameter) :
    validation first ≤
      soupScore validation (greedySoup validation [first] candidates) := by
  simpa [soupScore, onlineMean, onlineMeanUpdate] using
    soupScore_greedySoup_ge validation [first] candidates

end GreedyAdmission

section NonlinearBoundary

/-- Scalar nonlinear predictor used to expose the soup/ensemble boundary. -/
def squarePredict (parameter : ℝ) : ℝ :=
  parameter ^ 2

/-- Both endpoint parameters are perfect for the target output one. -/
theorem squarePredict_endpoints :
    squarePredict (-1) = 1 ∧ squarePredict 1 = 1 := by
  norm_num [squarePredict]

/-- The uniform parameter soup of the two perfect endpoints predicts zero. -/
theorem squarePredict_uniformSoup :
    squarePredict (twoSoup (1 / 2 : ℝ) (-1) 1) = 0 := by
  norm_num [squarePredict, twoSoup]

/-- The output ensemble of those same endpoints predicts one. -/
theorem squarePredict_uniformEnsemble :
    twoEnsemble squarePredict (1 / 2 : ℝ) (-1) 1 = 1 := by
  norm_num [squarePredict, twoEnsemble]

/-- Negative boundary: parameter souping and output ensembling differ for a
nonlinear predictor, even when both endpoints agree perfectly. -/
theorem nonlinearSoup_ne_ensemble :
    squarePredict (twoSoup (1 / 2 : ℝ) (-1) 1) ≠
      twoEnsemble squarePredict (1 / 2 : ℝ) (-1) 1 := by
  rw [squarePredict_uniformSoup, squarePredict_uniformEnsemble]
  norm_num

/-- Negative squared error against target one. -/
def validationScore (parameter : ℝ) : ℝ :=
  -((squarePredict parameter - 1) ^ 2)

/-- A uniform soup can be strictly worse than each of its ingredients. -/
theorem uniformSoup_can_be_worse_than_both_endpoints :
    validationScore (twoSoup (1 / 2 : ℝ) (-1) 1) <
        validationScore (-1) ∧
      validationScore (twoSoup (1 / 2 : ℝ) (-1) 1) <
        validationScore 1 := by
  norm_num [validationScore, squarePredict, twoSoup]

end NonlinearBoundary

#print axioms linearPredict_twoSoup
#print axioms affinePredict_twoSoup
#print axioms soupScore_greedySoup_ge
#print axioms greedySoup_no_worse_than_first
#print axioms nonlinearSoup_ne_ensemble
#print axioms uniformSoup_can_be_worse_than_both_endpoints

end

end ModelSoupGeometry

end Mettapedia.MachineLearning.ContinualLearning
