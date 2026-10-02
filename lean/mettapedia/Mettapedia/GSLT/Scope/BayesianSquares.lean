import Mettapedia.Algorithms.FiniteBayesReduction
import Mettapedia.GSLT.Scope.BayesianDependencyReuse
import Mettapedia.GSLT.Scope.ConsumerDescent
import Mettapedia.GSLT.Scope.UpdateSquares
import Mettapedia.KR.ConceptOntology.AdmissibleRepresentation
import Mettapedia.Logic.WorldModel.Bayesian
import Mettapedia.ProbabilityTheory.BayesianInference.ModelRefinement
import Mettapedia.ProbabilityTheory.BayesianInference.SensoryActiveInterface

/-!
# Bayesian instances of scope squares and dependency receipts

The visible bit descends along the coarse concept reading. The update that
copies the hidden bit does not. An active write of the external coordinate
closes a sensory square and preserves the sensory prediction. A changed
point-mass goal keeps a nonzero coupling cost.

A likelihood and a consumer that both factor through the state map give the
same world-model query on the expanded carrier and on its pushforward,
including the refusal when the evidence is zero. The posterior predictive
emission and the subsequent factored policy value survive under that same
factorization. A hidden-bit likelihood can determine the diagnostic while
leaving today's visible answer unchanged, and that diagnostic does not factor
through the coarse reading. Replacing the compatible transition by the
identity breaks the predictive certificate.

Posterior reuse and rational prior reduction are the existing receipt and
reduction operations: current dependencies transfer, and a changed likelihood
or an expanded support refuses the stored result.
-/

namespace Mettapedia.GSLT.Scope.BayesianSquares

open Mettapedia.Algorithms.FiniteBayes
open Mettapedia.Algorithms.FiniteBayesReduction
open Mettapedia.Cybernetics.ApproximateAdequacy hiding dirac
open Mettapedia.GSLT.Core.NonFactorization
open Mettapedia.GSLT.Dynamics.AdaptiveContinuationPlanning
open Mettapedia.GSLT.Scope
open Mettapedia.GSLT.Scope.BayesianDependencyReuse
open Mettapedia.InformationTheory
open Mettapedia.InformationTheory.Prob
open Mettapedia.KR.ConceptOntology.AdmissibleRepresentation
open Mettapedia.KR.ConceptOntology.StochasticSufficiency.CompressionControl
open Mettapedia.Logic.WorldModel.Bayesian
open Mettapedia.ProbabilityTheory.BayesianInference
open Mettapedia.ProbabilityTheory.BayesianInference.ModelRefinement
open Mettapedia.ProbabilityTheory.BayesianInference.SensoryActive

open scoped NNReal

def visibleSetoid : Setoid State where
  r source target := source.1 = target.1
  iseqv := ⟨fun _ => rfl, Eq.symm, Eq.trans⟩

def flipVisible (state : State) : State :=
  (!state.1, state.2)

def bitDist (left right : Bool) : ℕ :=
  if left = right then 0 else 1

theorem visible_answer_descends : Factors (Quotient.mk visibleSetoid) Prod.fst :=
  (function_descends_iff visibleSetoid Prod.fst).mpr fun _ _ same => same

theorem diagnostic_does_not_descend : ¬ Factors (Quotient.mk visibleSetoid) diagnostic := by
  intro factors
  have same :=
    factors.constantOnFibers (false, false) (false, true) (Quotient.sound rfl)
  simp [diagnostic] at same

theorem hidden_bit_transport_boundary :
    Nonempty (∀ P : Quotient visibleSetoid → Type,
        P (Quotient.mk visibleSetoid (false, false)) →
          P (Quotient.mk visibleSetoid (false, true))) ∧
      ¬ Nonempty (∀ P : State → Type, P (false, false) → P (false, true)) :=
  transport_boundary (Quotient.mk visibleSetoid) (by decide) (Quotient.sound rfl)

theorem today_without_tomorrow :
    Factors (readout .coarse) Prod.fst ∧ ¬ Supports (readout .coarse) expose :=
  ⟨⟨Prod.fst, fun _ => rfl⟩, coarse_splits_expose⟩

theorem clear_preserves_visible : PreservesExactly Prod.fst clearHidden :=
  fun _ => rfl

theorem clear_approximates : Approximates bitDist Prod.fst 0 clearHidden :=
  PreservesExactly.approximates (fun bit => by simp [bitDist]) clear_preserves_visible

theorem expose_changes_visible : ¬ PreservesExactly Prod.fst expose := by
  intro preserves
  have same := preserves (false, true)
  simp [expose] at same

theorem expose_not_within_zero : ¬ Approximates bitDist Prod.fst 0 expose := by
  intro approximates
  have bound := approximates (false, true)
  simp [bitDist, expose] at bound

theorem flip_square : SquareCloses Prod.fst Prod.fst flipVisible :=
  ⟨fun bit => !bit, fun _ => rfl⟩

theorem intervention_square (action : Bool) :
    SquareCloses sensory sensory (fun world => writeExternal action world) :=
  ⟨fun reading => (action, reading.2), fun _ => rfl⟩

theorem copy_square_fails :
    ¬ Supports sensory (fun world : World => (world.2.2, world.2.1, world.2.2)) :=
  not_supports_of_split
    (x := (false, true, false)) (y := (false, true, true)) rfl
    (by
      show sensory (false, true, false) ≠ sensory (true, true, true)
      decide)

theorem active_prediction_follows_square (prior : Prob World) (action : Bool) :
    SquareCloses sensory sensory (fun world => writeExternal action world) ∧
      coarsen (Prob.bind prior (applyAction action)) sensory =
        Prob.bind (coarsen prior sensory) (fun reading => dirac (action, reading.2)) :=
  ⟨intervention_square action, apply_prediction prior action⟩

theorem visible_query_survives (prior : Prob State) :
    query prior (fun _ => 1) (fun state => if state.1 then (1 : ℝ) else 0) =
      query (coarsen prior Prod.fst) (fun _ => 1) (fun bit => if bit then 1 else 0) := by
  rw [query_one, query_one]
  exact congrArg some
    (coarsen_expectation prior Prod.fst (fun bit => if bit then (1 : ℝ) else 0)).symm

/-- A factored likelihood and consumer have one world-model query on either carrier. -/
theorem query_factors {S C : Type*} [Fintype S] [Fintype C] [DecidableEq C]
    (prior : Prob S) (view : S → C) (likelihood : C → ℝ≥0) (consumer : C → ℝ) :
    query prior (fun state => likelihood (view state)) (fun state => consumer (view state)) =
      query (coarsen prior view) likelihood consumer := by
  unfold query
  have like_fn :
      (fun state => (likelihood (view state) : ℝ)) =
        (fun image => (likelihood image : ℝ)) ∘ view := by
    funext state
    rfl
  simp only [like_fn]
  by_cases possible : 0 < evidence prior ((fun image => (likelihood image : ℝ)) ∘ view)
  · have coarse_possible :
        0 < evidence (coarsen prior view) (fun image => (likelihood image : ℝ)) := by
      rw [evidence_coarsen]
      exact possible
    simp only [dif_pos possible, dif_pos coarse_possible]
    apply congrArg some
    have sameValue :
        (posterior (coarsen prior view) (fun image => (likelihood image : ℝ))
          (fun image => (likelihood image).coe_nonneg) coarse_possible).1 =
        (posterior (coarsen prior view) (fun image => (likelihood image : ℝ))
          (fun image => (likelihood image).coe_nonneg)
          (by rw [evidence_coarsen]; exact possible)).1 := rfl
    rw [sameValue]
    have pushed :=
      coarsen_posterior prior view (fun image => (likelihood image : ℝ))
        (fun image => (likelihood image).coe_nonneg) possible
    have summed :=
      coarsen_expectation
        (posterior prior ((fun image => (likelihood image : ℝ)) ∘ view)
          (fun state => (likelihood (view state)).coe_nonneg) possible)
        view consumer
    rw [pushed] at summed
    exact summed.symm
  · have coarse_impossible :
        ¬ 0 < evidence (coarsen prior view) (fun image => (likelihood image : ℝ)) := by
      rw [evidence_coarsen]
      exact possible
    simp only [dif_neg possible, dif_neg coarse_impossible]

/-- An impossible factored likelihood is refused on both carriers. -/
theorem impossible_factored_query_refuses {S C : Type*} [Fintype S] [Fintype C] [DecidableEq C]
    (prior : Prob S) (view : S → C) (consumer : C → ℝ) :
    query prior (fun _ => (0 : ℝ≥0)) (fun state => consumer (view state)) = none ∧
      query (coarsen prior view) (fun _ => 0) consumer = none := by
  constructor
  · have zeroLike : (fun _ : S => (0 : ℝ≥0)) = fun state => (fun _ : C => (0 : ℝ≥0)) (view state) := rfl
    rw [zeroLike, query_factors prior view (fun _ => 0) consumer, query_zero]
  · exact query_zero (coarsen prior view) consumer

/-- The posterior's factored emission agrees with the emission from the coarse posterior. -/
theorem posterior_predictive_survives {S C O : Type*} [Fintype S] [Fintype C] [Fintype O]
    [DecidableEq C] [DecidableEq O] (prior : Prob S) (view : S → C) (likelihood : C → ℝ)
    (nonneg : ∀ image, 0 ≤ likelihood image)
    (possible : 0 < evidence prior (likelihood ∘ view)) (emission : C → Prob O) :
    observationLaw
        (posterior prior (likelihood ∘ view) (fun state => nonneg (view state)) possible)
        (emission ∘ view) =
      observationLaw
        (posterior (coarsen prior view) likelihood nonneg
          (by rw [evidence_coarsen]; exact possible))
        emission := by
  rw [observationLaw, observationLaw, bind_of_coarsen, coarsen_posterior]

/-- A factored policy value survives when it is averaged over that posterior. -/
theorem posterior_decision_survives {Fine Coarse Action : Type*}
    [Fintype Fine] [Fintype Coarse] [DecidableEq Coarse]
    (view : Fine → Coarse)
    (fineKernel : Action → Fine → Prob Fine) (coarseKernel : Action → Coarse → Prob Coarse)
    (transition : ∀ action state,
      coarsen (fineKernel action state) view = coarseKernel action (view state))
    {Obs : Type*} [Fintype Obs] [DecidableEq Obs]
    (fineEmit : Action → Fine → Prob Obs) (coarseEmit : Action → Coarse → Prob Obs)
    (emissionCompat : ∀ action state, fineEmit action state = coarseEmit action (view state))
    (prior : Prob Fine) (likelihood : Coarse → ℝ) (nonneg : ∀ image, 0 ≤ likelihood image)
    (possible : 0 < evidence prior (likelihood ∘ view))
    (reward : Coarse → ℝ) {n : ℕ} (policy : ObservationPolicy Obs Action n) :
    expect
        (posterior prior (likelihood ∘ view) (fun state => nonneg (view state)) possible).1
        (adaptiveValue (fun action state => joint (fineKernel action state) (fineEmit action))
          (reward ∘ view) policy) =
      expect
        (posterior (coarsen prior view) likelihood nonneg
          (by rw [evidence_coarsen]; exact possible)).1
        (adaptiveValue
          (fun action state => joint (coarseKernel action state) (coarseEmit action))
          reward policy) :=
  expected_policy_preserved view fineKernel coarseKernel transition fineEmit coarseEmit
    emissionCompat
    (posterior prior (likelihood ∘ view) (fun state => nonneg (view state)) possible)
    (posterior (coarsen prior view) likelihood nonneg (by rw [evidence_coarsen]; exact possible))
    (coarsen_posterior prior view likelihood nonneg possible) reward policy

/-- Likelihood of the hidden bit, as a nonnegative world-model revision. -/
def hiddenLike (state : State) : ℝ≥0 :=
  if state.2 then 1 else 0

theorem hiddenLike_apply (state : State) :
    (hiddenLike state : ℝ) = if state.2 then (1 : ℝ) else 0 := by
  by_cases hidden : state.2 <;> simp [hiddenLike, hidden]

theorem hidden_evidence :
    evidence uniformPrior (fun state => (hiddenLike state : ℝ)) = 1 / 2 := by
  have coeLike :
      (fun state => (hiddenLike state : ℝ)) = fun state => if state.2 then (1 : ℝ) else 0 := by
    funext state
    exact hiddenLike_apply state
  rw [coeLike]
  unfold evidence uniformPrior
  norm_num [Fintype.sum_prod_type, Fintype.sum_bool]

theorem hidden_update_learns_diagnostic :
    query uniformPrior hiddenLike (fun state => if state.2 then (1 : ℝ) else 0) = some 1 := by
  have possible : 0 < evidence uniformPrior (fun state => (hiddenLike state : ℝ)) := by
    rw [hidden_evidence]
    norm_num
  unfold query
  simp only [dif_pos possible]
  apply congrArg some
  simp only [posterior_apply]
  simp only [hidden_evidence]
  simp only [uniformPrior, hiddenLike_apply]
  norm_num [Fintype.sum_prod_type, Fintype.sum_bool]

theorem hidden_update_keeps_visible_answer :
    query uniformPrior hiddenLike (fun state => if state.1 then (1 : ℝ) else 0) =
      query uniformPrior (fun _ => 1) (fun state => if state.1 then (1 : ℝ) else 0) := by
  have possible : 0 < evidence uniformPrior (fun state => (hiddenLike state : ℝ)) := by
    rw [hidden_evidence]
    norm_num
  have updated :
      query uniformPrior hiddenLike (fun state => if state.1 then (1 : ℝ) else 0) = some (1 / 2) := by
    unfold query
    simp only [dif_pos possible]
    apply congrArg some
    simp only [posterior_apply]
    simp only [hidden_evidence]
    simp only [uniformPrior, hiddenLike_apply]
    norm_num [Fintype.sum_prod_type, Fintype.sum_bool]
  have original :
      query uniformPrior (fun _ => 1) (fun state => if state.1 then (1 : ℝ) else 0) =
        some (1 / 2) := by
    rw [query_one]
    apply congrArg some
    simp only [uniformPrior]
    norm_num [Fintype.sum_prod_type, Fintype.sum_bool]
  rw [updated, original]

/-- Today's visible answer survives coarsening, while the hidden update does not factor. -/
theorem today_survives_hidden_update_fails :
    query uniformPrior (fun _ => 1) (fun state => if state.1 then (1 : ℝ) else 0) =
      query (coarsen uniformPrior Prod.fst) (fun _ => 1) (fun bit => if bit then 1 else 0) ∧
      query uniformPrior hiddenLike (fun state => if state.2 then (1 : ℝ) else 0) = some 1 ∧
      query uniformPrior hiddenLike (fun state => if state.1 then (1 : ℝ) else 0) =
        query uniformPrior (fun _ => 1) (fun state => if state.1 then (1 : ℝ) else 0) ∧
      ¬ Factors (readout .coarse) diagnostic :=
  ⟨visible_query_survives uniformPrior, hidden_update_learns_diagnostic,
    hidden_update_keeps_visible_answer, coarse_hides_diagnostic⟩

/-- The identity transition is not the compatible flip. -/
def stayFine (_ : Unit) (state : Bool × Bool) : Prob (Bool × Bool) :=
  dirac state

theorem changed_dynamics_refuses_prediction :
    coarsen (Prob.bind (dirac (true, false)) (stayFine ())) redundantView ≠
      Prob.bind (dirac true) (redundantCoarse ()) := by
  intro same
  have leftLaw :
      coarsen (Prob.bind (dirac (true, false)) (stayFine ())) redundantView = dirac true := by
    rw [Mettapedia.ProbabilityTheory.BayesianInference.ModelRefinement.bind_dirac, stayFine,
      coarsen_dirac, redundantView]
  have rightLaw : Prob.bind (dirac true) (redundantCoarse ()) = dirac false := by
    rw [Mettapedia.ProbabilityTheory.BayesianInference.ModelRefinement.bind_dirac, redundantCoarse,
      Bool.not_true]
  rw [leftLaw, rightLaw] at same
  have mass := congrArg (fun law : Prob Bool => law.1 true) same
  simp [dirac_apply] at mass

theorem compatible_dynamics_transfers (flag : Bool) :
    coarsen (Prob.bind (dirac (true, flag)) (redundantFine ())) redundantView =
      Prob.bind (dirac true) (redundantCoarse ()) :=
  redundant_prediction flag

theorem hidden_score_does_not_survive :
    expect uniformPrior.1 richerUtility ≠
      expect (coarsen uniformPrior Prod.fst).1 retainedUtility := by
  intro same
  have gap := coarse_loss_is_declared_estimate.2
  rw [same, sub_self, abs_zero] at gap
  norm_num at gap

theorem supported_policy_keeps_visible_score {n : ℕ}
    (policy : ObservationPolicy Unit Unit n) (flag : Bool) :
    adaptiveValue
        (fun action state =>
          joint (redundantFine action state) (fun _ => dirac ()))
        (bitReward ∘ redundantView) policy (true, flag) =
      adaptiveValue
        (fun action bit => joint (redundantCoarse action bit) (fun _ => dirac ()))
        bitReward policy true ∧
      ((∑ s, (Prob.bind (dirac (true, false)) (redundantFine ())).1 s * hiddenFlag s) = 0 ∧
        (∑ s, (Prob.bind (dirac (true, true)) (redundantFine ())).1 s * hiddenFlag s) = 1) :=
  ⟨redundant_policy policy flag, redundant_hidden_splits⟩

theorem refinement_task_transfers (flag : Bool) :
    (∑ s, (Prob.bind (dirac (true, flag)) (redundantFine ())).1 s *
        bitReward (redundantView s)) =
      ∑ bit, (Prob.bind (dirac true) (redundantCoarse ())).1 bit * bitReward bit :=
  redundant_task_preserved flag

theorem expansion_refuses_prediction :
    coarsen (Prob.bind (dirac (true, false)) (redundantFine ())) redundantView ≠
      Prob.bind (dirac false) (redundantCoarse ()) :=
  unsupported_prior_expansion

theorem same_goal_has_zero_diagonal_cost (reward : Bool → ℝ) :
    (diagonalCoupling (dirac true)).cost (fun x y => |reward x - reward y|) = 0 :=
  diagonalCoupling_abs_cost (dirac true) reward

theorem changed_goal_matches_coupling_cost :
    |(∑ b, (dirac true).1 b * (fun bit : Bool => if bit then (1 : ℝ) else 0) b) -
        ∑ b, (dirac false).1 b * (fun bit : Bool => if bit then (1 : ℝ) else 0) b| =
      (Coupling.ofDirac (𝕜 := ℝ) true false).cost
        (fun x y => |(fun bit : Bool => if bit then (1 : ℝ) else 0) x -
          (fun bit : Bool => if bit then (1 : ℝ) else 0) y|) :=
  discrepant_point_mass_gap

theorem selected_representation :
    benefitCriterion.IsOptimal .refined ∧ ¬ selection.IsOptimal .redundant ∧
      ¬ admits .coarse :=
  ⟨refined_benefit_optimal, redundant_admissible_not_optimal.2, coarse_not_admitted⟩

theorem prior_reduction_transfers :
    reduce (twoMass (1 / 2) (1 / 2)) (twoMass (3 / 4) (1 / 4)) (twoMass (1 / 4) (3 / 4)) =
      update (twoMass (3 / 4) (1 / 4)) (twoMass 1 3) :=
  same_likelihood_agrees

theorem prior_reduction_refuses_expansion :
    update (twoMass 1 0) (twoMass 1 1) = some (twoMass 1 0) ∧
      0 < normalizer (twoMass (1 / 2) (1 / 2)) (twoMass 1 1) ∧
      update (twoMass (1 / 2) (1 / 2)) (twoMass 1 1) = some (twoMass (1 / 2) (1 / 2)) ∧
      reduce (twoMass 1 0) (twoMass (1 / 2) (1 / 2)) (twoMass 1 0) = none :=
  support_expansion_refused

theorem posterior_receipt_reuses {S : Type*} [Fintype S]
    (saved : PreparedArtifact (posteriorPlan (S := S))) (current : Bool → S → ℚ)
    (output : S → ℚ) (accepted : reuse saved current = some (some output)) :
    ∃ valid : IsDistribution (current true),
      ∃ nonneg : ∀ s, 0 ≤ (current false s : ℝ),
      ∃ possible : 0 < evidence (realDistribution (current true) valid)
        (fun s => (current false s : ℝ)),
      ∃ outputValid : IsDistribution output,
        realDistribution output outputValid =
          posterior (realDistribution (current true) valid)
            (fun s => (current false s : ℝ)) nonneg possible :=
  reuse_refines saved current output accepted

theorem posterior_receipt_refuses_changed_likelihood {S : Type*} [Fintype S]
    (saved : PreparedArtifact (posteriorPlan (S := S))) (current : Bool → S → ℚ)
    (old : S → ℚ) (recorded : (false, old) ∈ saved.dependencies)
    (changed : old ≠ current false) :
    reuse saved current = none :=
  changed_likelihood_refuses saved current old recorded changed

end Mettapedia.GSLT.Scope.BayesianSquares
