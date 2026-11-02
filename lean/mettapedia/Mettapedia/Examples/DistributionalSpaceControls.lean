import Mettapedia.MachineLearning.NeuralNetworks.DistributionalInterface
import Mettapedia.GSLT.Logic.TaskRelativeMemory
import Mettapedia.Machines.BranchLocalNeed.Weighted.StressAndCommitments

/-!
# Distributional space controls

These examples separate event identity, stochastic independence, predictive
readouts, learning derivatives and stationary process observations. The finite
examples query the same public space interface used by the general theorems.
-/
set_option autoImplicit false

namespace Mettapedia.Examples.DistributionalSpaceControls
set_option backward.isDefEq.respectTransparency false
open Finset Mettapedia.InformationTheory Mettapedia.ProbabilityTheory.BayesianInference
open Mettapedia.Logic.DistributionalSpace
open Mettapedia.MachineLearning.NeuralNetworks.DistributionalInterface
open Mettapedia.GSLT.TaskRelativeMemory

noncomputable def fair : Prob Bool :=
  ⟨fun _ => 1 / 2, fun _ => by norm_num, by norm_num [Fintype.sum_bool]⟩

/-- A report is certain in a true world and fair in a false world. -/
noncomputable def report (w : Bool) : Prob Bool :=
  ⟨fun b => if b then if w then 1 else 1/2 else if w then 0 else 1/2,
    fun b => by cases w <;> cases b <;> norm_num, by cases w <;> norm_num⟩

noncomputable def reports : Model Unit Bool (Bool → Bool) Bool :=
  independentModel (fun _ => fair) (fun _ w _ => report w) (fun _ => true)

@[simp] theorem reports_likelihood (E : Finset Bool) (w : Bool) :
    reports.likelihood () E w = ∏ _i ∈ E, (if w then (1 : ℝ) else 1/2) := by
  exact independent_likelihood _ _ _ _ _ _

theorem one_report : reports.probability? () {false} id = some (2/3) := by
  rw [Model.probability?_formula]
  simp only [Model.normalizer, evidence, reports_likelihood]
  norm_num [reports, independentModel, fair]

theorem replay_report : reports.probability? () (observe {false} false) id = some (2/3) := by
  simpa [observe] using one_report

theorem two_reports : reports.probability? () {false, true} id = some (4/5) := by
  rw [Model.probability?_formula]
  simp only [Model.normalizer, evidence, reports_likelihood]
  norm_num [reports, independentModel, fair]

theorem erase_restores_prior : reports.probability? () (retract {false} false) id = some (1/2) := by
  simp [retract, Model.probability?, Model.expectation?, reports, independentModel, fair]

theorem same_posterior : reports.posterior? () {false} = reports.posterior? () {true} := by
  apply Model.posterior?_congr
  funext w
  simp

theorem other_report : reports.probability? () {true} id = some (2/3) := by
  change (reports.posterior? () {true}).map _ = _
  rw [← same_posterior]
  exact one_report

/-- The existing future-observation criterion rejects posterior-only memory:
retracting an identified report separates otherwise identical posteriors. -/
theorem posterior_not_revision_memory :
    ¬ (futureFamily (retract (Id := Bool))
      (fun _ : Unit => fun E => reports.probability? () E id)).SupportsReadout
        (reports.posterior? ()) := by
  intro h
  have same := congrArg (h.some.run ([false], ())) same_posterior
  have a := h.some.agrees ([false], ()) {false}
  have b := h.some.agrees ([false], ()) {true}
  have eqv := a.symm.trans (same.trans b)
  clear same
  have same := eqv
  change reports.probability? () (retract {false} false) id =
    reports.probability? () (retract {true} false) id at same
  rw [erase_restores_prior] at same
  have ht : retract ({true} : Finset Bool) false = {true} := by simp [retract]
  rw [ht, other_report] at same
  norm_num at same

/-- Distinct labels can still describe one shared observation. -/
noncomputable def correlatedReports : Model Unit Bool Bool Bool where
  prior _ := fair
  observations _ w := report w
  catalogue _ o := o

theorem distinct_labels_not_independent :
    correlatedReports.probability? () {false, true} id = some (2/3) ∧
    reports.probability? () {false, true} id = some (4/5) := by
  constructor
  · rw [Model.probability?_formula]
    norm_num [Model.normalizer, evidence, Model.likelihood, Model.accepts,
      correlatedReports, report, fair]
  · exact two_reports

/-- Two named observations assert opposite outcomes of the same joint variable. -/
noncomputable def contradictory : Model Unit Bool Bool Bool where
  prior _ := fair
  observations _ w := Prob.dirac w
  catalogue i o := decide (o = i)

theorem impossible_evidence : contradictory.posterior? () {false, true} = none := by
  rw [Model.posterior?_none_iff]
  norm_num [Model.normalizer, evidence, Model.likelihood, Model.accepts, contradictory, fair]

theorem retract_contradiction :
    contradictory.probability? () (retract {false, true} false) id = some 1 := by
  rw [Model.probability?_formula]
  norm_num [retract, Model.normalizer, evidence, Model.likelihood, Model.accepts,
    contradictory, fair, Prob.dirac]

theorem zero_is_answer : contradictory.probability? () {false} id = some 0 := by
  rw [Model.probability?_formula]
  norm_num [Model.normalizer, evidence, Model.likelihood, Model.accepts,
    contradictory, fair, Prob.dirac]

/-- Shared choice and fresh independent choices, using existing bind/coarsen. -/
noncomputable def shared : Prob (Bool × Bool) := Prob.coarsen fair fun b => (b,b)
noncomputable def fresh : Prob (Bool × Bool) := joint fair fun _ => fair

theorem shared_fresh_marginals :
    Prob.coarsen shared Prod.fst = fair ∧ Prob.coarsen fresh Prod.fst = fair ∧
    Prob.coarsen shared Prod.snd = fair ∧ Prob.coarsen fresh Prod.snd = fair := by
  constructor
  · rw [shared, Prob.coarsen_comp]
    change Prob.coarsen fair id = fair
    exact Prob.coarsen_id fair
  constructor
  · apply Subtype.ext
    funext b
    rw [Prob.coarsen_apply]
    rw [Mettapedia.InformationTheory.FiniteRV.pushforward_fst]
    exact joint_latent_marginal fair (fun _ => fair) b
  constructor
  · rw [shared, Prob.coarsen_comp]
    change Prob.coarsen fair id = fair
    exact Prob.coarsen_id fair
  · apply Subtype.ext
    funext b
    rw [Prob.coarsen_apply]
    rw [Mettapedia.InformationTheory.FiniteRV.pushforward_snd]
    norm_num [fresh, joint_apply, fair]

theorem shared_fresh_joint : shared.1 (true,true) = 1/2 ∧ fresh.1 (true,true) = 1/4 := by
  norm_num [shared, fresh, Prob.coarsen, Mettapedia.InformationTheory.FiniteRV.pushforward_eq_sum_ite,
    joint, fair]

open Mettapedia.Machines.BranchLocalNeed.Weighted in
/-- These finite laws are the readouts of the already certified shared and
resampled programs, once their executions have completed. -/
theorem retained_machine_laws (fuel : Nat) (enough : 50 ≤ fuel) (a b : Bool) :
    (ProbabilityControls.pairLaw fuel capturedCellInCode (some (a,b))).toReal = shared.1 (a,b) ∧
    (ProbabilityControls.pairLaw fuel resampledCellInCode (some (a,b))).toReal = fresh.1 (a,b) := by
  rw [ProbabilityControls.captured_probability fuel enough,
    ProbabilityControls.resampled_probability fuel enough]
  cases a <;> cases b <;>
    norm_num [shared, fresh, Prob.coarsen,
      Mettapedia.InformationTheory.FiniteRV.pushforward_eq_sum_ite, joint, fair]

/-- Equal current neural predictions do not determine a learning derivative. -/
theorem same_prediction_different_gradient :
    bernoulli (0 : ℝ) = bernoulli (2 * 0) ∧
    HasDerivAt (fun θ => -Real.log ((bernoulli θ).1 true)) (-(1/2)) 0 ∧
    HasDerivAt (fun θ => -Real.log ((bernoulli (2*θ)).1 true)) (-1) 0 := by
  constructor
  · norm_num
  constructor
  · convert bernoulli_nll_derivative (hasDerivAt_id (0 : ℝ)) true using 1 <;> norm_num
  · convert bernoulli_nll_derivative ((hasDerivAt_id (0 : ℝ)).const_mul 2) true using 1 <;> norm_num

noncomputable def neuralReports : Model ℝ Bool (Bool → Bool) Bool :=
  independentModel (fun _ => fair)
    (affineChannel (fun _ w => if w then 1 else 0) (fun _ => 0)) (fun _ => true)

@[simp] theorem neural_report_likelihood (θ : ℝ) (w : Bool) :
    neuralReports.likelihood θ {false} w = Real.sigmoid (θ * if w then 1 else 0) := by
  simp [neuralReports, independent_likelihood, affineChannel, bernoulli]

/-- Retaining evidence and changing parameters changes the same Space's answer. -/
theorem neural_parameter_revision :
    neuralReports.probability? 0 {false} id = some (1/2) ∧
    neuralReports.probability? (Real.log 3) {false} id = some (3/5) := by
  constructor <;> rw [Model.probability?_formula] <;>
    simp only [Model.normalizer, evidence, neural_report_likelihood] <;>
    norm_num [neuralReports, independentModel, fair, Real.sigmoid_def, Real.exp_neg,
      Real.exp_log (by norm_num : (0 : ℝ) < 3)]

/-- A complete model-to-training-objective instance of the score identity. -/
theorem neural_evidence_gradient :
    HasDerivAt (fun θ => -Real.log (neuralReports.normalizer θ {false})) (-(1/4)) 0 := by
  have h := space_score_along neuralReports id fair (fun _ => rfl) {false} 0
    (fun w => if w then (1/4 : ℝ) else 0)
    (by
      intro w
      simp only [id_eq, neural_report_likelihood]
      cases w
      · simpa using hasDerivAt_const (0 : ℝ) (Real.sigmoid 0)
      · convert Real.hasDerivAt_sigmoid 0 using 1 <;> norm_num)
    (by intro w; simp only [id_eq, neural_report_likelihood]; exact Real.sigmoid_pos _)
    (by norm_num [evidence, neural_report_likelihood, fair])
  convert h using 1 <;>
    norm_num [posterior_apply, evidence, neural_report_likelihood, fair]

open Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding in
/-- An inhabited analytic example: a one-dimensional standard Gaussian model. -/
noncomputable def unitGaussian : LinearGaussianOperatorModel Unit Unit where
  residualMatrix := 1
  residualPrecision := 1
  residualOffset := 0
  residualMatrix_injective := by
    intro x y h
    simpa using h
  residualPrecision_posDef := Matrix.PosDef.one

theorem unitGaussian_has_uncertainty :
    0 < _root_.ProbabilityTheory.variance (fun v => v ()) unitGaussian.posterior ∧
    unitGaussian.posterior ≠ MeasureTheory.Measure.dirac unitGaussian.posteriorMean :=
  ⟨gaussian_variance_positive unitGaussian (), gaussian_not_mean_dirac unitGaussian ()⟩

/-- Clockwise and counterclockwise probabilities on a three-state ring. -/
noncomputable def cycleKernel (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (i : Fin 3) : Prob (Fin 3) :=
  ⟨fun j => if j.val = (i.val + 1) % 3 then p else if j.val = (i.val + 2) % 3 then 1-p else 0,
   fun j => by dsimp only; split_ifs <;> linarith, by
    fin_cases i <;> norm_num [Fin.sum_univ_succ]⟩

noncomputable def uniform3 : Prob (Fin 3) :=
  ⟨fun _ => 1/3, fun _ => by norm_num, by norm_num [Fin.sum_univ_succ]⟩

theorem cycle_stationary (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    Prob.bind uniform3 (cycleKernel p hp hp1) = uniform3 := by
  apply Subtype.ext
  funext j
  fin_cases j <;> simp [Prob.bind, uniform3, cycleKernel, Fin.sum_univ_succ] <;> ring

/-- Stationarity does not imply detailed balance or determine path queries. -/
theorem stationary_different_current :
    (joint uniform3 (cycleKernel (2/3) (by norm_num) (by norm_num))).1 (0,1) -
      (joint uniform3 (cycleKernel (2/3) (by norm_num) (by norm_num))).1 (1,0) = 1/9 ∧
    (joint uniform3 (cycleKernel (1/2) (by norm_num) (by norm_num))).1 (0,1) -
      (joint uniform3 (cycleKernel (1/2) (by norm_num) (by norm_num))).1 (1,0) = 0 := by
  norm_num [joint, uniform3, cycleKernel]

end Mettapedia.Examples.DistributionalSpaceControls
