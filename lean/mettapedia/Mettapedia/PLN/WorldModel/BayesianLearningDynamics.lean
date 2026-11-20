import Mettapedia.ProbabilityTheory.BayesianInference.SufficientFiltering
import Mettapedia.MachineLearning.ContinualLearning.RealTimeContinualSchedule
import Mettapedia.GSLT.Core.InferenceControl
import Mathlib.Tactic

/-!
# Bayesian learning, observation cadence, and retained computation

Exact finite conditioning is invariant under batching a fixed likelihood
sequence. A retained sufficient view can resume prediction and conditioning;
the transition and emission hypotheses are separate. Approximation and
misspecified drift have a quantitative, evidence-sensitive error bound.

The coupled machine keeps observations, reference posterior, numerical
approximation, deployed parameters, environment and retained proof search.
Observation arrival, assimilation, retraining and search resumption have
different effects. Strictly positive likelihoods make the batching interface
total; zero-support observations require the partial update interface.
-/

set_option autoImplicit false

namespace Mettapedia.PLN.WorldModel.BayesianLearningDynamics

open scoped BigOperators
open Mettapedia.InformationTheory
open Mettapedia.InformationTheory.Prob
open Mettapedia.ProbabilityTheory.BayesianInference
open Mettapedia.ProbabilityTheory.FiniteLumpability

variable {S : Type*} [Fintype S]

/-- A likelihood valid at every state. Positivity is the declared support
condition for this total, static-model batch interface. -/
structure PositiveLikelihood (S : Type*) where
  value : S → ℝ
  positive : ∀ state, 0 < value state

namespace PositiveLikelihood

def unit : PositiveLikelihood S := ⟨fun _ => 1, fun _ => zero_lt_one⟩

def mul (first second : PositiveLikelihood S) : PositiveLikelihood S :=
  ⟨fun state => first.value state * second.value state,
    fun state => mul_pos (first.positive state) (second.positive state)⟩

theorem possible (likelihood : PositiveLikelihood S) (prior : Prob S) :
    0 < evidence prior likelihood.value := by
  have somePositive : ∃ state, 0 < prior.1 state := by
    by_contra noPositive
    push Not at noPositive
    have zero : ∀ state, prior.1 state = 0 :=
      fun state => le_antisymm (noPositive state) (prior.2.1 state)
    have normalized := prior.2.2
    simp only [zero, Finset.sum_const_zero] at normalized
    norm_num at normalized
  obtain ⟨state, positive⟩ := somePositive
  exact Finset.sum_pos' (fun s _ => mul_nonneg (prior.2.1 s) (likelihood.positive s).le)
    ⟨state, Finset.mem_univ state, mul_pos positive (likelihood.positive state)⟩

noncomputable def update (likelihood : PositiveLikelihood S) (prior : Prob S) : Prob S :=
  posterior prior likelihood.value (fun state => (likelihood.positive state).le)
    (likelihood.possible prior)

@[simp] theorem update_unit (prior : Prob S) : (unit (S := S)).update prior = prior :=
  posterior_one prior

/-- Exact sequential updating equals one batch, under the same fixed model. -/
theorem update_mul (first second : PositiveLikelihood S) (prior : Prob S) :
    second.update (first.update prior) = (first.mul second).update prior :=
  posterior_posterior prior first.value second.value
    (fun state => (first.positive state).le) (fun state => (second.positive state).le)
    (first.possible prior) (second.possible (first.update prior))

def batch : List (PositiveLikelihood S) → PositiveLikelihood S
  | [] => unit
  | first :: rest => first.mul (batch rest)

noncomputable def online (prior : Prob S) : List (PositiveLikelihood S) → Prob S
  | [] => prior
  | first :: rest => online (first.update prior) rest

/-- The reference posterior is independent of how many update calls partition
the same likelihood sequence. No approximation or parameter change occurs. -/
theorem online_eq_batch (prior : Prob S) (observations : List (PositiveLikelihood S)) :
    online prior observations = (batch observations).update prior := by
  induction observations generalizing prior with
  | nil => exact (update_unit prior).symm
  | cons first rest ih =>
      rw [online, ih, update_mul]
      rfl

theorem online_append (prior : Prob S) (first second : List (PositiveLikelihood S)) :
    online prior (first ++ second) = online (online prior first) second := by
  induction first generalizing prior with
  | nil => rfl
  | cons likelihood rest ih => exact ih (likelihood.update prior)

theorem scheduled_batches_exact (prior : Prob S) (batches : List (List (PositiveLikelihood S))) :
    batches.foldl (fun law observations => online law observations) prior =
      (batch batches.flatten).update prior := by
  have flatten : ∀ prior : Prob S,
      batches.foldl (fun law observations => online law observations) prior =
        online prior batches.flatten := by
    induction batches with
    | nil => intro prior; rfl
    | cons first rest ih =>
        intro prior
        simp only [List.foldl_cons, List.flatten_cons, online_append]
        exact ih (online prior first)
  rw [flatten, online_eq_batch]

end PositiveLikelihood

/-- Bayesian updating amplifies prior error when the conditioning event has
small mass. Both posterior distributions are independently specified. -/
theorem posterior_l1_bound (first second : Prob S) (likelihood : S → ℝ)
    (nonneg : ∀ state, 0 ≤ likelihood state)
    (firstPossible : 0 < evidence first likelihood)
    (secondPossible : 0 < evidence second likelihood)
    (M δ : ℝ) (bounded : ∀ state, likelihood state ≤ M)
    (positive : 0 < δ) (margin : δ ≤ evidence first likelihood) :
    l1Distance (posterior first likelihood nonneg firstPossible)
      (posterior second likelihood nonneg secondPossible) ≤
      (2 * M / δ) * l1Distance first second := by
  let z := evidence first likelihood
  let w := evidence second likelihood
  have hz : 0 < z := firstPossible
  have hw : 0 < w := secondPossible
  have likelihoodAbs : ∀ state, |likelihood state| ≤ M := by
    intro state
    rw [abs_of_nonneg (nonneg state)]
    exact bounded state
  have massError : |z - w| ≤ M * l1Distance first second :=
    abs_expectation_sub_le_l1 first second likelihood M likelihoodAbs
  have weightError : (∑ state, |first.1 state * likelihood state -
      second.1 state * likelihood state|) ≤ M * l1Distance first second := by
    calc
      _ = ∑ state, |first.1 state - second.1 state| * likelihood state := by
        apply Finset.sum_congr rfl
        intro state _
        rw [← sub_mul, abs_mul, abs_of_nonneg (nonneg state)]
      _ ≤ ∑ state, |first.1 state - second.1 state| * M :=
        Finset.sum_le_sum fun state _ =>
          mul_le_mul_of_nonneg_left (bounded state) (abs_nonneg _)
      _ = M * l1Distance first second := by
        rw [← Finset.sum_mul, mul_comm]
        rfl
  have inverse : w * |1 / z - 1 / w| = |z - w| / z := by
    rw [div_sub_div _ _ hz.ne' hw.ne', abs_div, abs_mul,
      abs_of_pos hz, abs_of_pos hw]
    simp only [one_mul, mul_one]
    rw [abs_sub_comm w z]
    field_simp
  have totalBound :
      l1Distance (posterior first likelihood nonneg firstPossible)
        (posterior second likelihood nonneg secondPossible) ≤
      ((∑ state, |first.1 state * likelihood state - second.1 state * likelihood state|) +
        |z - w|) / z := by
    unfold l1Distance
    simp only [posterior_apply]
    change (∑ state, |first.1 state * likelihood state / z -
      second.1 state * likelihood state / w|) ≤ _
    calc
      _ ≤ ∑ state, (|first.1 state * likelihood state - second.1 state * likelihood state| / z +
          second.1 state * likelihood state * |1 / z - 1 / w|) := by
        apply Finset.sum_le_sum
        intro state _
        have decomposition : first.1 state * likelihood state / z -
            second.1 state * likelihood state / w =
          (first.1 state * likelihood state - second.1 state * likelihood state) / z +
            second.1 state * likelihood state * (1 / z - 1 / w) := by ring
        rw [decomposition]
        calc
          _ ≤ |(first.1 state * likelihood state - second.1 state * likelihood state) / z| +
              |second.1 state * likelihood state * (1 / z - 1 / w)| := abs_add_le _ _
          _ = _ := by
            rw [abs_div, abs_of_pos hz, abs_mul,
              abs_of_nonneg (mul_nonneg (second.2.1 state) (nonneg state))]
      _ = _ := by
        rw [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_mul]
        change _ + w * |1 / z - 1 / w| = _
        rw [inverse, ← add_div]
  have numeratorNonneg : 0 ≤ 2 * M * l1Distance first second := by
    have productNonneg : 0 ≤ M * l1Distance first second :=
      (Finset.sum_nonneg (fun state _ => abs_nonneg
        (first.1 state * likelihood state - second.1 state * likelihood state))).trans weightError
    nlinarith
  calc
    _ ≤ ((∑ state, |first.1 state * likelihood state - second.1 state * likelihood state|) +
        |z - w|) / z := totalBound
    _ ≤ (M * l1Distance first second + M * l1Distance first second) / z :=
      div_le_div_of_nonneg_right (add_le_add weightError massError) hz.le
    _ = (2 * M * l1Distance first second) / z := by ring
    _ ≤ (2 * M * l1Distance first second) / δ :=
      div_le_div_of_nonneg_left numeratorNonneg positive margin
    _ = _ := by ring

/-- Prediction discrepancy splits into retained-posterior error and rowwise
environment/model drift. -/
theorem prediction_l1_bound (first second : Prob S) (actual modeled : S → Prob S)
    (ε : ℝ) (rows : ∀ state, l1Distance (actual state) (modeled state) ≤ ε) :
    l1Distance (bind first actual) (bind second modeled) ≤ l1Distance first second + ε := by
  exact (l1Distance_triangle _ (bind second actual) _).trans
    (add_le_add (l1Distance_bind_le first second actual)
      (l1Distance_bind_rows_le second actual modeled ε rows))

/-- Evolution while a deployed snapshot remains stale accumulates at most
one declared drift budget per elapsed transition. -/
theorem stale_prediction_bound [DecidableEq S] (kernel : S → Prob S)
    (δ : ℝ) (drift : ∀ state, l1Distance (kernel state) (Prob.dirac state) ≤ δ)
    (prior : Prob S) (steps : ℕ) :
    l1Distance ((fun law => bind law kernel)^[steps] prior) prior ≤ steps * δ := by
  induction steps with
  | zero => simp
  | succ steps ih =>
      rw [Function.iterate_succ_apply']
      have stepBound := prediction_l1_bound
        ((fun law => bind law kernel)^[steps] prior) prior kernel Prob.dirac δ drift
      rw [bind_dirac_right] at stepBound
      calc
        _ ≤ l1Distance ((fun law => bind law kernel)^[steps] prior) prior + δ := stepBound
        _ ≤ (steps : ℝ) * δ + δ := add_le_add ih (le_refl δ)
        _ = _ := by push_cast; ring

/-- A real-time update schedule gives a bound at its unpaired stream steps.
This bound assumes each unpaired step is one transition of the same kernel. -/
theorem scheduled_staleness_bound [DecidableEq S] (kernel : S → Prob S)
    (δ : ℝ) (drift : ∀ state, l1Distance (kernel state) (Prob.dirac state) ≤ δ)
    (prior : Prob S)
    (ratio : Mettapedia.MachineLearning.ContinualLearning.RealTimeContinualSchedule.StreamWorkRatio)
    (arrivals : ℕ) :
    l1Distance ((fun law => bind law kernel)^[
      Mettapedia.MachineLearning.ContinualLearning.RealTimeContinualSchedule.skippedStreamSteps ratio arrivals]
      prior) prior ≤
      Mettapedia.MachineLearning.ContinualLearning.RealTimeContinualSchedule.skippedStreamSteps ratio arrivals * δ :=
  stale_prediction_bound kernel δ drift prior _

/-- One filtering step, then a certified numerical projection. The likelihood
margin controls error amplification; no zero-evidence normalization occurs. -/
theorem filtering_l1_bound (first second approximateNext : Prob S)
    (actual modeled : S → Prob S) (likelihood : PositiveLikelihood S)
    (M δ ε η : ℝ) (mNonneg : 0 ≤ M)
    (bounded : ∀ state, likelihood.value state ≤ M) (positive : 0 < δ)
    (margin : δ ≤ evidence (bind first actual) likelihood.value)
    (rows : ∀ state, l1Distance (actual state) (modeled state) ≤ ε)
    (projection : l1Distance (likelihood.update (bind second modeled)) approximateNext ≤ η) :
    l1Distance (likelihood.update (bind first actual)) approximateNext ≤
      (2 * M / δ) * (l1Distance first second + ε) + η := by
  have posteriorError := posterior_l1_bound (bind first actual) (bind second modeled)
    likelihood.value (fun state => (likelihood.positive state).le)
    (likelihood.possible _) (likelihood.possible _) M δ bounded positive margin
  have factorNonneg : 0 ≤ 2 * M / δ :=
    div_nonneg (mul_nonneg (by norm_num) mNonneg) positive.le
  exact (l1Distance_triangle _ (likelihood.update (bind second modeled)) _).trans
    (add_le_add (posteriorError.trans
      (mul_le_mul_of_nonneg_left (prediction_l1_bound first second actual modeled ε rows)
        factorNonneg)) projection)

/-- A controlled finite filtering model whose emissions have full support. -/
structure FilteringModel (State Input : Type*) [Fintype State] where
  transition : Input → State → Prob State
  emission : Input → PositiveLikelihood State

namespace FilteringModel

variable {Input C : Type*} [Fintype C] [DecidableEq C]

noncomputable def step (model : FilteringModel S Input) (input : Input) (prior : Prob S) : Prob S :=
  (model.emission input).update (bind prior (model.transition input))

noncomputable def run (model : FilteringModel S Input) (inputs : List Input) (prior : Prob S) : Prob S :=
  inputs.foldl (fun law input => model.step input law) prior

theorem run_append (model : FilteringModel S Input) (first second : List Input) (prior : Prob S) :
    model.run (first ++ second) prior = model.run second (model.run first prior) :=
  List.foldl_append

/-- Finite filtering commutes with a supplied sufficient view. Local transition
and emission conditions prove the whole future execution square. -/
theorem coarsen_run (view : S → C)
    (fine : FilteringModel S Input) (coarse : FilteringModel C Input)
    (transition : ∀ input state,
      coarsen (fine.transition input state) view = coarse.transition input (view state))
    (emission : ∀ input state,
      (fine.emission input).value state = (coarse.emission input).value (view state))
    (inputs : List Input) (prior : Prob S) :
    coarsen (fine.run inputs prior) view = coarse.run inputs (coarsen prior view) := by
  have oneStep : ∀ input prior, coarsen (fine.step input prior) view =
      coarse.step input (coarsen prior view) := by
    intro input prior
    have likelihoodEq : (fine.emission input).value = (coarse.emission input).value ∘ view :=
      funext (emission input)
    have possible : 0 < evidence (bind prior (fine.transition input))
        ((coarse.emission input).value ∘ view) := by
      simpa only [← likelihoodEq] using (fine.emission input).possible
        (bind prior (fine.transition input))
    have commutes := coarsen_posterior (bind prior (fine.transition input)) view
      (coarse.emission input).value (fun state => ((coarse.emission input).positive state).le) possible
    have predict := coarsen_bind_of_rows view view (fine.transition input)
      (coarse.transition input) (transition input) prior
    simpa only [step, PositiveLikelihood.update, likelihoodEq, predict] using commutes
  induction inputs generalizing prior with
  | nil => rfl
  | cons input rest ih =>
      change coarsen (fine.run rest (fine.step input prior)) view =
        coarse.run rest (coarse.step input (coarsen prior view))
      rw [ih, oneStep]

/-- A retained sufficient distribution is enough to resume every allowed
future observation/action sequence, even when the fine posteriors differ. -/
theorem resume_from_sufficient (view : S → C)
    (fine : FilteringModel S Input) (coarse : FilteringModel C Input)
    (transition : ∀ input state,
      coarsen (fine.transition input state) view = coarse.transition input (view state))
    (emission : ∀ input state,
      (fine.emission input).value state = (coarse.emission input).value (view state))
    (first second : Prob S) (sameView : coarsen first view = coarsen second view)
    (future : List Input) :
    coarsen (fine.run future first) view = coarsen (fine.run future second) view := by
  rw [coarsen_run view fine coarse transition emission,
    coarsen_run view fine coarse transition emission, sameView]

end FilteringModel

open Mettapedia.GSLT.Core.BranchingTemporal (BranchingSystem)
open Mettapedia.GSLT.Core.InferenceControl (Controller Snapshot)

/-- Environment state, observation history, exact reference semantics,
approximation, deployed parameters, and retained search are independent
coordinates. Search includes its controller's memory and live frontier. -/
structure CoupledState (S Environment Parameter Observation Node Answer Memory : Type*) [Fintype S] where
  environment : Environment
  arrived : List Observation
  assimilated : List Observation
  waiting : List Observation
  posterior : Prob S
  approximation : Prob S
  deployed : Parameter
  inference : Snapshot Node Answer Memory
  deploymentVersion : ℕ

namespace CoupledState

variable {Environment Parameter Observation Node Answer Memory : Type*}

def LedgerValid (state : CoupledState S Environment Parameter Observation Node Answer Memory) : Prop :=
  state.arrived = state.assimilated ++ state.waiting

def arrive (nextEnvironment : Environment) (observation : Observation)
    (state : CoupledState S Environment Parameter Observation Node Answer Memory) :=
  {state with environment := nextEnvironment
              arrived := state.arrived ++ [observation]
              waiting := state.waiting ++ [observation]}

noncomputable def predict (nextEnvironment : Environment) (actual modeled : S → Prob S)
    (state : CoupledState S Environment Parameter Observation Node Answer Memory) :=
  {state with environment := nextEnvironment
              posterior := bind state.posterior actual
              approximation := bind state.approximation modeled}

noncomputable def assimilate (observation : Observation) (remaining : List Observation)
    (likelihood : PositiveLikelihood S) (approximate : Prob S → Prob S)
    (state : CoupledState S Environment Parameter Observation Node Answer Memory) :=
  {state with assimilated := state.assimilated ++ [observation]
              waiting := remaining
              posterior := likelihood.update state.posterior
              approximation := approximate (likelihood.update state.approximation)}

def deploy (train : Prob S → Parameter → Parameter)
    (state : CoupledState S Environment Parameter Observation Node Answer Memory) :=
  {state with deployed := train state.approximation state.deployed
              deploymentVersion := state.deploymentVersion + 1}

def resume (system : BranchingSystem Node Answer) (controller : Controller Node Answer Memory)
    (work : ℕ) (state : CoupledState S Environment Parameter Observation Node Answer Memory) :=
  {state with inference :=
    Mettapedia.GSLT.Core.InferenceControl.Snapshot.run system controller work state.inference}

theorem arrive_ledger (next : Environment) (observation : Observation)
    (state : CoupledState S Environment Parameter Observation Node Answer Memory)
    (valid : state.LedgerValid) : (state.arrive next observation).LedgerValid := by
  simp only [LedgerValid, arrive] at *
  rw [valid, List.append_assoc]

theorem assimilate_ledger (observation : Observation) (remaining : List Observation)
    (likelihood : PositiveLikelihood S) (approximate : Prob S → Prob S)
    (state : CoupledState S Environment Parameter Observation Node Answer Memory)
    (valid : state.LedgerValid) (pending : state.waiting = observation :: remaining) :
    (state.assimilate observation remaining likelihood approximate).LedgerValid := by
  simp only [LedgerValid, assimilate] at *
  rw [valid, pending, List.append_assoc]
  rfl

/-- Training from the approximation never consumes a second copy of a raw
observation in the reference Bayesian state. -/
theorem deploy_preserves_reference (train : Prob S → Parameter → Parameter)
    (state : CoupledState S Environment Parameter Observation Node Answer Memory) :
    (state.deploy train).posterior = state.posterior ∧
      (state.deploy train).assimilated = state.assimilated ∧
      (state.deploy train).waiting = state.waiting := ⟨rfl, rfl, rfl⟩

/-- Retained proof computation can advance between observation arrivals and
deployments without changing the statistical ledger or deployed model. -/
theorem resume_preserves_learning (system : BranchingSystem Node Answer)
    (controller : Controller Node Answer Memory) (work : ℕ)
    (state : CoupledState S Environment Parameter Observation Node Answer Memory) :
    (state.resume system controller work).posterior = state.posterior ∧
      (state.resume system controller work).arrived = state.arrived ∧
      (state.resume system controller work).deployed = state.deployed := ⟨rfl, rfl, rfl⟩

/-- Any lawful resumed proof search preserves the existing proof authority's
soundness; a posterior or parameter change is not a proof certificate. -/
theorem resume_sound (system : BranchingSystem Node Answer)
    (controller : Controller Node Answer Memory) (work : ℕ) (roots : List Node)
    (state : CoupledState S Environment Parameter Observation Node Answer Memory)
    (sound : state.inference.search.Sound system roots) :
    (state.resume system controller work).inference.search.Sound system roots :=
  Mettapedia.GSLT.Core.InferenceControl.Snapshot.sound_run system controller sound work

/-- Legal transitions consume observations in their recorded order. A raw
state update is not itself evidence that an observation was pending. -/
inductive Transition : CoupledState S Environment Parameter Observation Node Answer Memory →
    CoupledState S Environment Parameter Observation Node Answer Memory → Prop where
  | arrive (next : Environment) (observation : Observation) (state) :
      Transition state (state.arrive next observation)
  | predict (next : Environment) (actual modeled : S → Prob S) (state) :
      Transition state (state.predict next actual modeled)
  | assimilate (observation : Observation) (remaining : List Observation)
      (likelihood : PositiveLikelihood S) (approximate : Prob S → Prob S) (state)
      (pending : state.waiting = observation :: remaining) :
      Transition state (state.assimilate observation remaining likelihood approximate)
  | deploy (train : Prob S → Parameter → Parameter) (state) :
      Transition state (state.deploy train)
  | resume (system : BranchingSystem Node Answer) (controller : Controller Node Answer Memory)
      (work : ℕ) (state) : Transition state (state.resume system controller work)

theorem Transition.preserves_ledger
    {first second : CoupledState S Environment Parameter Observation Node Answer Memory}
    (transition : Transition first second) (valid : first.LedgerValid) : second.LedgerValid := by
  cases transition with
  | arrive next observation => exact arrive_ledger next observation _ valid
  | predict => exact valid
  | assimilate => exact assimilate_ledger _ _ _ _ _ valid (by assumption)
  | deploy => exact valid
  | resume => exact valid

/-- A coupled prediction step inherits the same independently proved drift
and retained-posterior error bound as its reference semantics. -/
theorem predict_error (next : Environment) (actual modeled : S → Prob S)
    (state : CoupledState S Environment Parameter Observation Node Answer Memory)
    (ε : ℝ) (rows : ∀ latent, l1Distance (actual latent) (modeled latent) ≤ ε) :
    l1Distance (state.predict next actual modeled).posterior
      (state.predict next actual modeled).approximation ≤
        l1Distance state.posterior state.approximation + ε :=
  prediction_l1_bound state.posterior state.approximation actual modeled ε rows

/-- Each legal assimilation has a bound connecting its reference posterior
to its numerical approximation, rather than merely preserving field names. -/
theorem assimilate_error (observation : Observation) (remaining : List Observation)
    (likelihood : PositiveLikelihood S) (approximate : Prob S → Prob S)
    (state : CoupledState S Environment Parameter Observation Node Answer Memory)
    (M δ η : ℝ) (bounded : ∀ latent, likelihood.value latent ≤ M)
    (positive : 0 < δ) (margin : δ ≤ evidence state.posterior likelihood.value)
    (projection : l1Distance (likelihood.update state.approximation)
      (approximate (likelihood.update state.approximation)) ≤ η) :
    l1Distance (state.assimilate observation remaining likelihood approximate).posterior
      (state.assimilate observation remaining likelihood approximate).approximation ≤
        (2 * M / δ) * l1Distance state.posterior state.approximation + η :=
  (l1Distance_triangle _ (likelihood.update state.approximation) _).trans
    (add_le_add (posterior_l1_bound state.posterior state.approximation likelihood.value
      (fun latent => (likelihood.positive latent).le)
      (likelihood.possible _) (likelihood.possible _) M δ bounded positive margin) projection)

end CoupledState

end Mettapedia.PLN.WorldModel.BayesianLearningDynamics
