import Mathlib.Data.List.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Logic.Equiv.Fin.Basic
import Mettapedia.UniversalAI.BayesianAgents

/-!
# Important Problem Classes (Hutter 2005, Chapter 6)

This file formalizes the reduction of various AI problem classes to the AIXI framework,
following Chapter 6 of Hutter's "Universal Artificial Intelligence" (2005).

## Main Definitions

### Problem Classes
* `SequencePredictionProblem` - Binary sequence prediction (SP)
* `StrategicGameProblem` - Strategic games like chess (SG)
* `FunctionMinimizationProblem` - Function minimization (FM)
* `SupervisedLearningProblem` - Learning from examples (EX)

### Key Results
* Each problem class can be embedded in the AIXI framework
* AIXI is optimal for each problem class (when specialized)
* Reduction theorems showing equivalence of optimal strategies

## References

- Hutter, M. (2005). "Universal Artificial Intelligence", Chapter 6
- Section 6.2: Sequence Prediction
- Section 6.3: Strategic Games
- Section 6.4: Function Minimization
- Section 6.5: Supervised Learning from Examples

## Mathematical Content

### Sequence Prediction (Section 6.2)
Given a probability distribution μ over binary sequences, the SP_μ agent predicts:
  x̂_k = argmax_{x_k} μ(x_<k x_k)

Key theorem: Using AIμ for SP yields the same prediction as SP_μ.

### Strategic Games (Section 6.3)
For two-player zero-sum games with perfect information:
  - Minimax strategy: y_k = argmax min ... max min V(y₁o₁...y_no_n)
  - AIμ implements minimax when μ models rational opponent

### Function Minimization (Section 6.4)
Given function f: Y → ℝ, minimize weighted sum α₁z₁ + ... + α_m z_m
  - FMF: Final model (only final output matters)
  - FMS: Sum model (all outputs matter equally)
  - FME: Exponential weighting

### Supervised Learning (Section 6.5)
Learn relations R ⊆ Z × V from examples:
  - Environment presents (z_k, v_k) ∈ R or (z_k, ?) for queries
  - Agent outputs prediction y_k, receives reward r_k = δ(z_k, y_k) ∈ R
-/

namespace Mettapedia.UniversalAI.ProblemClasses

open BayesianAgents
open scoped Classical

/-! ### Shared Discount Factor

For the strategic-game reductions (Section 6.3), we use the undiscounted case `γ = 1`. -/

noncomputable def gameDiscount : BayesianAgents.Core.DiscountFactor := ⟨1, by simp, by simp⟩

/-! ## Section 6.1: Repetition of the AIμ/ξ Models

This section recalls the key definitions from Chapter 4/5. We import them
from BayesianAgents.lean.
-/

/-! ## Section 6.2: Sequence Prediction (SP)

Sequence prediction is the simplest and most well-studied problem class.
Given observations z₁z₂z₃..., predict the next element.
-/

/-- A sequence prediction problem with known prior μ.
    The environment generates a binary sequence according to μ.

    A semimeasure satisfies: μ(xs ++ [0]) + μ(xs ++ [1]) ≤ μ(xs)
    This is the standard definition from Solomonoff/Li-Vitányi.
    For probability measures, equality holds; for semimeasures, we allow ≤. -/
structure SequencePredictionProblem where
  /-- Prior probability distribution over binary sequences -/
  μ : List Bool → ENNReal
  /-- Base case: μ([]) ≤ 1 (probability of the empty sequence) -/
  μ_base_le_one : μ [] ≤ 1
  /-- Semimeasure property: sum of extensions ≤ prefix probability.
      This is the standard definition: μ(xs0) + μ(xs1) ≤ μ(xs) -/
  semimeasure : ∀ xs, μ (xs ++ [false]) + μ (xs ++ [true]) ≤ μ xs

/-- Any prefix probability is ≤ 1 (follows from semimeasure + base case).

    Uses reverse induction since the semimeasure property extends to the right. -/
theorem SequencePredictionProblem.μ_le_one (sp : SequencePredictionProblem)
    (xs : List Bool) : sp.μ xs ≤ 1 := by
  induction xs using List.reverseRecOn with
  | nil => exact sp.μ_base_le_one
  | append_singleton init b ih =>
    -- μ(init ++ [b]) ≤ μ(init ++ [false]) + μ(init ++ [true]) ≤ μ(init) ≤ 1
    have h := sp.semimeasure init
    cases b with
    | false =>
      calc sp.μ (init ++ [false])
          ≤ sp.μ (init ++ [false]) + sp.μ (init ++ [true]) := le_add_of_nonneg_right (zero_le _)
        _ ≤ sp.μ init := h
        _ ≤ 1 := ih
    | true =>
      calc sp.μ (init ++ [true])
          ≤ sp.μ (init ++ [false]) + sp.μ (init ++ [true]) := le_add_of_nonneg_left (zero_le _)
        _ ≤ sp.μ init := h
        _ ≤ 1 := ih

/-- The optimal sequence predictor for known μ.
    Predicts the bit with higher conditional probability.

    SPμ: x̂_k = argmax_{x_k} μ(x_<k x_k)  (Equation 6.10) -/
noncomputable def optimalSequencePredictor (sp : SequencePredictionProblem)
    (history : List Bool) : Bool :=
  if sp.μ (history ++ [true]) > sp.μ (history ++ [false]) then true else false

/-- The probability mass of making a prediction error after observing prefix `xs`.

For a given prefix, the Bayes-optimal one-step predictor chooses the more likely next bit, hence
the probability mass of the error event is `min (μ(xs0)) (μ(xs1))`. -/
noncomputable def predictionErrorMass (sp : SequencePredictionProblem) (xs : List Bool) : ENNReal :=
  min (sp.μ (xs ++ [false])) (sp.μ (xs ++ [true]))

/-- Total `μ`-mass of all bitstrings of length `n`. -/
noncomputable def sumPrefixProb (sp : SequencePredictionProblem) (n : ℕ) : ENNReal :=
  ∑ xs : Fin n → Bool, sp.μ (List.ofFn xs)

theorem sumPrefixProb_succ_eq (sp : SequencePredictionProblem) (n : ℕ) :
    sumPrefixProb sp (n + 1) =
      ∑ xs : Fin n → Bool, (sp.μ (List.ofFn xs ++ [false]) + sp.μ (List.ofFn xs ++ [true])) := by
  classical
  let e := Fin.succFunEquiv Bool n
  have hEquiv :
      (∑ xs : Fin (n + 1) → Bool, sp.μ (List.ofFn xs)) =
        ∑ p : (Fin n → Bool) × Bool, sp.μ (List.ofFn (e.symm p)) := by
    refine Fintype.sum_equiv e
      (fun xs : Fin (n + 1) → Bool => sp.μ (List.ofFn xs))
      (fun p : (Fin n → Bool) × Bool => sp.μ (List.ofFn (e.symm p))) ?_
    intro xs
    -- Avoid unfolding `e` (which would erase the `symm_apply_apply` redex).
    simp
  have hAppend :
      ∀ p : (Fin n → Bool) × Bool, List.ofFn (e.symm p) = List.ofFn p.1 ++ [p.2] := by
    rintro ⟨xs, b⟩
    have hs : e.symm (xs, b) = Fin.append xs (uniqueElim b) := by
      funext i
      simp [e, Fin.succFunEquiv, Fin.appendEquiv, Equiv.prodCongrRight]
    -- Rewrite the list using `Fin.append` and then simplify the length-1 suffix.
    rw [hs, List.ofFn_fin_append]
    simp [uniqueElim_const]
  calc
    sumPrefixProb sp (n + 1) = ∑ xs : Fin (n + 1) → Bool, sp.μ (List.ofFn xs) := by
      simp [sumPrefixProb]
    _ = ∑ p : (Fin n → Bool) × Bool, sp.μ (List.ofFn (e.symm p)) := hEquiv
    _ = ∑ p : (Fin n → Bool) × Bool, sp.μ (List.ofFn p.1 ++ [p.2]) := by
      apply Fintype.sum_congr
      intro p
      simpa using congrArg sp.μ (hAppend p)
    _ = ∑ xs : Fin n → Bool, (sp.μ (List.ofFn xs ++ [false]) + sp.μ (List.ofFn xs ++ [true])) := by
      simp [Fintype.sum_prod_type, add_comm]

theorem sumPrefixProb_succ_le (sp : SequencePredictionProblem) (n : ℕ) :
    sumPrefixProb sp (n + 1) ≤ sumPrefixProb sp n := by
  classical
  -- Use the semimeasure inequality pointwise and sum it over all prefixes of length `n`.
  rw [sumPrefixProb_succ_eq, sumPrefixProb]
  simpa using
    (Finset.sum_le_sum (s := (Finset.univ : Finset (Fin n → Bool)))
      (fun xs _ => sp.semimeasure (List.ofFn xs)))

theorem sumPrefixProb_le_root (sp : SequencePredictionProblem) :
    ∀ n : ℕ, sumPrefixProb sp n ≤ sp.μ [] := by
  intro n
  induction n with
  | zero =>
      simp [sumPrefixProb]
  | succ n ih =>
      exact (sumPrefixProb_succ_le sp n).trans ih

theorem sumPrefixProb_le_one (sp : SequencePredictionProblem) (n : ℕ) :
    sumPrefixProb sp n ≤ 1 := by
  exact (sumPrefixProb_le_root sp n).trans sp.μ_base_le_one

/-- Expected `μ`-mass of the error event at step `k+1`, i.e. after observing `k` bits. -/
noncomputable def expectedPredictionErrorAtENNReal (sp : SequencePredictionProblem) (k : ℕ) : ENNReal :=
  ∑ xs : Fin k → Bool, predictionErrorMass sp (List.ofFn xs)

theorem expectedPredictionErrorAtENNReal_le_one (sp : SequencePredictionProblem) (k : ℕ) :
    expectedPredictionErrorAtENNReal sp k ≤ 1 := by
  classical
  have hpoint :
      ∀ xs : Fin k → Bool,
        predictionErrorMass sp (List.ofFn xs) ≤
          sp.μ (List.ofFn xs ++ [false]) + sp.μ (List.ofFn xs ++ [true]) := by
    intro xs
    -- `min x y ≤ x ≤ x+y`.
    exact (min_le_left _ _).trans (le_add_of_nonneg_right (zero_le _))
  have hsum :
      expectedPredictionErrorAtENNReal sp k ≤
        ∑ xs : Fin k → Bool, (sp.μ (List.ofFn xs ++ [false]) + sp.μ (List.ofFn xs ++ [true])) := by
    unfold expectedPredictionErrorAtENNReal
    simpa using
      (Finset.sum_le_sum (s := (Finset.univ : Finset (Fin k → Bool)))
        (fun xs _ => hpoint xs))
  -- Bound by the total mass of length `k+1` strings and then by `1`.
  calc
    expectedPredictionErrorAtENNReal sp k ≤
        ∑ xs : Fin k → Bool, (sp.μ (List.ofFn xs ++ [false]) + sp.μ (List.ofFn xs ++ [true])) := hsum
    _ = sumPrefixProb sp (k + 1) := by
        simp [sumPrefixProb_succ_eq]
    _ ≤ 1 := sumPrefixProb_le_one sp (k + 1)

/-- Expected number of prediction errors for the optimal predictor `SPμ`.

This is a finite-sum formalization of Hutter (2005), Eq. (6.8). We sum the `μ`-mass of the
error event at each step `k+1`, over all prefixes of length `k`, for `k = 0..n-1`. -/
noncomputable def expectedPredictionErrorsENNReal (sp : SequencePredictionProblem) (n : ℕ) : ENNReal :=
  ∑ k ∈ Finset.range n, expectedPredictionErrorAtENNReal sp k

noncomputable def expectedPredictionErrors (sp : SequencePredictionProblem) (n : ℕ) : ℝ :=
  (expectedPredictionErrorsENNReal sp n).toReal

theorem expectedPredictionErrors_le (sp : SequencePredictionProblem) (n : ℕ) :
    expectedPredictionErrors sp n ≤ n := by
  classical
  have hENN :
      expectedPredictionErrorsENNReal sp n ≤ (n : ENNReal) := by
    have hstep :
        ∀ k, k ∈ Finset.range n → expectedPredictionErrorAtENNReal sp k ≤ (1 : ENNReal) := by
      intro k _hk
      exact expectedPredictionErrorAtENNReal_le_one sp k
    calc
      expectedPredictionErrorsENNReal sp n
          ≤ ∑ k ∈ Finset.range n, (1 : ENNReal) := by
              exact Finset.sum_le_sum fun k hk => hstep k hk
      _ = n := by simp
  have hnTop : (n : ENNReal) ≠ ⊤ := by simp
  have hLeftTop : expectedPredictionErrorsENNReal sp n ≠ ⊤ :=
    ne_top_of_le_ne_top hnTop hENN
  -- Convert the ENNReal inequality back to `ℝ`.
  have hReal :
      (expectedPredictionErrorsENNReal sp n).toReal ≤ (n : ENNReal).toReal :=
    (ENNReal.toReal_le_toReal hLeftTop hnTop).2 hENN
  simpa [expectedPredictionErrors] using hReal

namespace SequencePredictionProblem

/-! ### Embedding SP into the core AIXI model -/

/-- In the SP embedding, an action is exactly a bit prediction. -/
abbrev Action : Type := Bool

/-- A percept contains the true next bit `z_k` and a reward bit `r_k ∈ {0,1}`. -/
abbrev Percept : Type := Bool × Bool  -- (obs, rewardBit)

noncomputable instance : BayesianAgents.Core.PerceptReward Percept where
  reward x := if x.2 then 1 else 0
  reward_nonneg x := by
    by_cases h : x.2 <;> simp [h]
  reward_le_one x := by
    by_cases h : x.2 <;> simp [h]

@[simp] theorem reward_pair (o r : Bool) :
    BayesianAgents.Core.PerceptReward.reward (Percept := Percept) (o, r) = (if r then 1 else 0) := rfl

/-- The sequence of observed bits extracted from the observation component of percepts. -/
def obsBits (h : BayesianAgents.Core.History Action Percept) : List Bool :=
  (BayesianAgents.Core.History.percepts h).map Prod.fst

/-- Appending an action does not change the observed-bit sequence. -/
theorem obsBits_append_act (h : BayesianAgents.Core.History Action Percept) (a : Action) :
    obsBits (h ++ [BayesianAgents.Core.HistElem.act a]) = obsBits h := by
  simp [obsBits, BayesianAgents.Core.History.percepts_append, BayesianAgents.Core.History.percepts]

/-- The induced SP probability kernel. -/
noncomputable def prob (sp : SequencePredictionProblem) :
    BayesianAgents.Core.History Action Percept → Percept → ENNReal := fun h x =>
  match h.getLast? with
  | some (BayesianAgents.Core.HistElem.act a) =>
      -- Reward bit encodes correctness: `r_k = δ_{y_k, z_k}`.
      if x.2 = (a == x.1) then sp.μ (obsBits h ++ [x.1]) else 0
  | _ => 0

/-- The AI environment induced by a sequence prediction problem (Hutter 2005, Section 6.2.1). -/
noncomputable def spToEnvironment (sp : SequencePredictionProblem) :
    BayesianAgents.Core.Environment Action Percept := by
  classical
  refine { prob := prob sp, prob_le_one := ?_ }
  intro h _hwf
  classical
  cases hlast : h.getLast? with
  | none =>
      simp [prob, hlast]
  | some e =>
      cases e with
      | per _x =>
          simp [prob, hlast]
      | act a =>
          -- For each observation bit `z`, exactly one reward bit is consistent with correctness.
          have hsum :
              (∑ x : Percept, prob sp h x) = sp.μ (obsBits h ++ [false]) + sp.μ (obsBits h ++ [true]) := by
            cases a <;>
              simp [prob, hlast, Fintype.sum_prod_type, add_comm]
          have hbound :
              sp.μ (obsBits h ++ [false]) + sp.μ (obsBits h ++ [true]) ≤ 1 := by
            calc
              sp.μ (obsBits h ++ [false]) + sp.μ (obsBits h ++ [true]) ≤ sp.μ (obsBits h) :=
                sp.semimeasure _
              _ ≤ 1 := sp.μ_le_one _
          simpa [hsum] using hbound

/-- A canonical decision history encoding an observed bit prefix.

We use a dummy prediction (`false`) before each percept. This is sufficient for Theorem 6.2.1 since
`spToEnvironment` depends only on the observation bits. -/
def spDecisionHistory : List Bool → BayesianAgents.Core.History Action Percept
  | [] => []
  | b :: bs =>
      BayesianAgents.Core.HistElem.act false ::
        BayesianAgents.Core.HistElem.per (b, false) :: spDecisionHistory bs

theorem spDecisionHistory_obsBits (bits : List Bool) :
    obsBits (spDecisionHistory bits) = bits := by
  induction bits with
  | nil => simp [spDecisionHistory, obsBits, BayesianAgents.Core.History.percepts]
  | cons b bs ih =>
      simp [spDecisionHistory, obsBits, BayesianAgents.Core.History.percepts]
      simpa [obsBits] using ih

theorem spDecisionHistory_obsBits_append_act (bits : List Bool) (a : Action) :
    obsBits (spDecisionHistory bits ++ [BayesianAgents.Core.HistElem.act a]) = bits := by
  simpa [obsBits_append_act] using (spDecisionHistory_obsBits (bits := bits))

theorem spDecisionHistory_append_act_wellFormed (bits : List Bool) (a : Action) :
    BayesianAgents.Core.History.wellFormed (Action := Action) (Percept := Percept)
      (spDecisionHistory bits ++ [BayesianAgents.Core.HistElem.act a]) = true := by
  induction bits with
  | nil => simp [spDecisionHistory, BayesianAgents.Core.History.wellFormed]
  | cons b bs ih =>
      simp [spDecisionHistory, BayesianAgents.Core.History.wellFormed, ih]

/-!
### Theorem 6.2.1: AIμ = SPμ (Sequence Prediction)

In the induced AIXI environment for sequence prediction, the one-step optimal action chooses a bit
maximizing the next-bit probability under μ (Hutter 2005, Section 6.2.1, Eq. (6.12)).
-/

theorem optimalQValue_spDecisionHistory (sp : SequencePredictionProblem)
    (γ : BayesianAgents.Core.DiscountFactor) (bits : List Bool) (b : Bool) :
    BayesianAgents.Core.optimalQValue (spToEnvironment sp) γ (spDecisionHistory bits) b 1 =
      (sp.μ (bits ++ [b])).toReal := by
  classical
  have ha_wf :
      BayesianAgents.Core.History.wellFormed (Action := Action) (Percept := Percept)
        (spDecisionHistory bits ++ [BayesianAgents.Core.HistElem.act b]) = true :=
    spDecisionHistory_append_act_wellFormed (bits := bits) (a := b)
  have ha_last :
      (spDecisionHistory bits ++ [BayesianAgents.Core.HistElem.act b]).getLast? =
        some (BayesianAgents.Core.HistElem.act b) := by
    simp
  cases b <;>
    simp [BayesianAgents.Core.optimalQValue, BayesianAgents.Core.optimalValue_zero, spToEnvironment, prob,
      ha_wf, ha_last, spDecisionHistory_obsBits_append_act, Fintype.sum_prod_type]

/-- Theorem 6.2.1 (Hutter 2005): in the induced sequence-prediction environment, the `AIμ` action
is a Bayes-optimal predictor, i.e. it maximizes `μ(x_<k b)` over bits `b`. -/
theorem aimu_eq_spμ (sp : SequencePredictionProblem) (γ : BayesianAgents.Core.DiscountFactor) (bits : List Bool) :
    ∀ b : Bool,
      sp.μ (bits ++ [b]) ≤
        sp.μ (bits ++ [BayesianAgents.Core.optimalAction (spToEnvironment sp) γ (spDecisionHistory bits) 1]) := by
  classical
  intro b
  set aStar : Bool := BayesianAgents.Core.optimalAction (spToEnvironment sp) γ (spDecisionHistory bits) 1 with haStar
  have hQ :
      BayesianAgents.Core.optimalQValue (spToEnvironment sp) γ (spDecisionHistory bits) b 1 ≤
        BayesianAgents.Core.optimalQValue (spToEnvironment sp) γ (spDecisionHistory bits) aStar 1 := by
    have hspec :=
      (BayesianAgents.Core.optimalAction_spec (μ := spToEnvironment sp) (γ := γ)
        (h := spDecisionHistory bits) (horizon := 1))
    exact hspec.2 b (by simp)
  have hReal :
      (sp.μ (bits ++ [b])).toReal ≤ (sp.μ (bits ++ [aStar])).toReal := by
    simpa [optimalQValue_spDecisionHistory, haStar, aStar] using hQ
  have hbTop : sp.μ (bits ++ [b]) ≠ (⊤ : ENNReal) := by
    exact ne_top_of_le_ne_top (by simp) (sp.μ_le_one (bits ++ [b]))
  have haTop : sp.μ (bits ++ [aStar]) ≠ (⊤ : ENNReal) := by
    exact ne_top_of_le_ne_top (by simp) (sp.μ_le_one (bits ++ [aStar]))
  exact (ENNReal.toReal_le_toReal hbTop haTop).1 hReal

end SequencePredictionProblem

/-! ## Section 6.3: Strategic Games (SG)

Two-player zero-sum games with alternating moves.
-/

/-- A strategic game specification (Hutter 2005, Section 6.3).

Player 1 (the agent) chooses moves from `Action`, and player 2 (the opponent/environment) chooses
moves from `Opp`. After `maxRounds` rounds, the game is evaluated by `gameValuation`.

We assume the payoff is bounded in `[-1,1]` so it can be encoded as a Bernoulli reward. -/
structure StrategicGameProblem (Action : Type*) (Opp : Type*) where
  /-- Maximum number of rounds. -/
  maxRounds : ℕ
  /-- Valuation function: positive = player 1 wins, negative = player 2 wins. -/
  gameValuation : List (Action × Opp) → ℝ
  /-- Valuation is in `[-1,1]`. -/
  valuation_bounded : ∀ moves, |gameValuation moves| ≤ 1

namespace StrategicGameProblem

open scoped BigOperators
open scoped Classical

variable {Action Opp : Type*} [Fintype Action] [Fintype Opp]

/-- In the SG embedding, a percept contains the opponent move and a reward bit. -/
abbrev Percept (Opp : Type*) : Type _ := Opp × Bool

noncomputable instance : BayesianAgents.Core.PerceptReward (Percept Opp) where
  reward x := if x.2 then 1 else 0
  reward_nonneg x := by
    by_cases h : x.2 <;> simp [h]
  reward_le_one x := by
    by_cases h : x.2 <;> simp [h]

omit [Fintype Action] [Fintype Opp] in
@[simp] theorem reward_pair (o : Opp) (r : Bool) :
    BayesianAgents.Core.PerceptReward.reward (Percept := Percept Opp) (o, r) = (if r then 1 else 0) := rfl

/-- The minimax value of a game position (Equation 6.18-6.19). -/
noncomputable def minimaxValue (sg : StrategicGameProblem Action Opp)
    (position : List (Action × Opp)) (remaining : ℕ) : ℝ :=
  match remaining with
  | 0 => sg.gameValuation position
  | n + 1 =>
      (Finset.univ : Finset Action).fold max (-1) fun a =>
        (Finset.univ : Finset Opp).fold min 1 fun o =>
          minimaxValue sg (position ++ [(a, o)]) n

/-- Worst-case minimax value after choosing action `a` with `n` rounds remaining afterwards. -/
noncomputable def sgWorstCaseValue (sg : StrategicGameProblem Action Opp)
    (position : List (Action × Opp)) (a : Action) (n : ℕ) : ℝ :=
  (Finset.univ : Finset Opp).fold min 1 fun o => minimaxValue sg (position ++ [(a, o)]) n

theorem minimaxValue_le_one (sg : StrategicGameProblem Action Opp) :
    ∀ (position : List (Action × Opp)) (remaining : ℕ), minimaxValue sg position remaining ≤ 1 := by
  intro position remaining
  induction remaining generalizing position with
  | zero =>
      have hb : |sg.gameValuation position| ≤ 1 := sg.valuation_bounded position
      have : sg.gameValuation position ≤ 1 := le_trans (le_abs_self _) hb
      simpa [minimaxValue] using this
  | succ n ih =>
      have hw (a : Action) : sgWorstCaseValue (sg := sg) position a n ≤ (1 : ℝ) := by
        have :
            (Finset.univ : Finset Opp).fold min (1 : ℝ)
                  (fun o => minimaxValue sg (position ++ [(a, o)]) n) ≤ (1 : ℝ) := by
          exact
            (Finset.fold_min_le (s := (Finset.univ : Finset Opp)) (b := (1 : ℝ))
              (f := fun o => minimaxValue sg (position ++ [(a, o)]) n) (c := (1 : ℝ))).2 (Or.inl le_rfl)
        simpa [sgWorstCaseValue] using this
      have hb : (-1 : ℝ) ≤ (1 : ℝ) := by linarith
      have hfold :
          (Finset.univ : Finset Action).fold max (-1) (fun a => sgWorstCaseValue (sg := sg) position a n) ≤ 1 := by
        refine
          (Finset.fold_max_le (s := (Finset.univ : Finset Action)) (b := (-1 : ℝ))
              (f := fun a => sgWorstCaseValue (sg := sg) position a n) (c := (1 : ℝ))).2 ?_
        refine ⟨hb, ?_⟩
        intro a _ha
        exact hw a
      simpa [minimaxValue] using hfold

theorem minimaxValue_ge_neg_one (sg : StrategicGameProblem Action Opp) :
    ∀ (position : List (Action × Opp)) (remaining : ℕ), (-1 : ℝ) ≤ minimaxValue sg position remaining := by
  intro position remaining
  induction remaining generalizing position with
  | zero =>
      have hb : |sg.gameValuation position| ≤ 1 := sg.valuation_bounded position
      have : (-1 : ℝ) ≤ sg.gameValuation position := (abs_le.mp hb).1
      simpa [minimaxValue] using this
  | succ n ih =>
      have :
          (-1 : ℝ) ≤
            (Finset.univ : Finset Action).fold max (-1) (fun a => sgWorstCaseValue (sg := sg) position a n) := by
        exact
          (Finset.le_fold_max (s := (Finset.univ : Finset Action)) (b := (-1 : ℝ))
              (f := fun a => sgWorstCaseValue (sg := sg) position a n) (c := (-1 : ℝ))).2 (Or.inl le_rfl)
      simpa [minimaxValue] using this

/-! ### Embedding strategic games as environments -/

/-- Extract the `(agent move, opponent move)` sequence from a history. Reward bits are ignored. -/
def sgPosition : BayesianAgents.Core.History Action (Percept Opp) → List (Action × Opp)
  | [] => []
  | BayesianAgents.Core.HistElem.act a :: BayesianAgents.Core.HistElem.per x :: rest =>
      (a, x.1) :: sgPosition rest
  | _ :: rest => sgPosition rest

/-- Encode a game position as a well-formed history.

Reward bits in the history are dummy; the strategic-game environment controls rewards. -/
def sgHistory : List (Action × Opp) → BayesianAgents.Core.History Action (Percept Opp)
  | [] => []
  | (a, o) :: rest =>
      BayesianAgents.Core.HistElem.act a ::
        BayesianAgents.Core.HistElem.per (o, false) :: sgHistory rest

omit [Fintype Action] [Fintype Opp] in
theorem sgHistory_append (p q : List (Action × Opp)) :
    sgHistory (p ++ q) = sgHistory p ++ sgHistory q := by
  induction p with
  | nil => simp [sgHistory]
  | cons x xs ih =>
      rcases x with ⟨a, o⟩
      simp [sgHistory, ih]

omit [Fintype Action] [Fintype Opp] in
theorem sgPosition_sgHistory (pos : List (Action × Opp)) :
    sgPosition (sgHistory (Action := Action) (Opp := Opp) pos) = pos := by
  induction pos with
  | nil => simp [sgPosition, sgHistory]
  | cons p ps ih =>
      rcases p with ⟨a, o⟩
      simp [sgPosition, sgHistory, ih]

omit [Fintype Action] [Fintype Opp] in
theorem sgPosition_sgHistory_append_act (pos : List (Action × Opp)) (a : Action) :
    sgPosition (sgHistory (Action := Action) (Opp := Opp) pos ++ [BayesianAgents.Core.HistElem.act a]) = pos := by
  induction pos with
  | nil => simp [sgPosition, sgHistory]
  | cons p ps ih =>
      rcases p with ⟨a', o⟩
      simp [sgPosition, sgHistory, ih]

omit [Fintype Action] [Fintype Opp] in
theorem sgHistory_wellFormed (pos : List (Action × Opp)) :
    BayesianAgents.Core.History.wellFormed (Action := Action) (Percept := Percept Opp)
      (sgHistory (Action := Action) (Opp := Opp) pos) = true := by
  induction pos with
  | nil => simp [sgHistory, BayesianAgents.Core.History.wellFormed]
  | cons p ps ih =>
      rcases p with ⟨a, o⟩
      simp [sgHistory, BayesianAgents.Core.History.wellFormed, ih]

omit [Fintype Action] [Fintype Opp] in
theorem sgHistory_append_act_wellFormed (pos : List (Action × Opp)) (a : Action) :
    BayesianAgents.Core.History.wellFormed (Action := Action) (Percept := Percept Opp)
      (sgHistory (Action := Action) (Opp := Opp) pos ++ [BayesianAgents.Core.HistElem.act a]) = true := by
  induction pos with
  | nil => simp [sgHistory, BayesianAgents.Core.History.wellFormed]
  | cons p ps ih =>
      rcases p with ⟨a', o⟩
      simp [sgHistory, BayesianAgents.Core.History.wellFormed, ih]

variable [Inhabited Opp]

/-- Opponent move chosen to minimize the minimax value (ties arbitrary). -/
noncomputable def oStar (sg : StrategicGameProblem Action Opp) (position : List (Action × Opp)) (a : Action) (n : ℕ) :
    Opp :=
  Classical.choose <|
    Finset.exists_min_image (s := (Finset.univ : Finset Opp))
      (f := fun o : Opp => minimaxValue sg (position ++ [(a, o)]) n) (by
        exact ⟨default, by simp⟩)

theorem oStar_spec (sg : StrategicGameProblem Action Opp) (position : List (Action × Opp)) (a : Action) (n : ℕ) :
    ∀ o : Opp,
      minimaxValue sg (position ++ [(a, oStar (sg := sg) position a n)]) n ≤
        minimaxValue sg (position ++ [(a, o)]) n := by
  classical
  have h :=
    (Classical.choose_spec <|
      Finset.exists_min_image (s := (Finset.univ : Finset Opp))
        (f := fun o : Opp => minimaxValue sg (position ++ [(a, o)]) n) (by
          exact ⟨default, by simp⟩))
  intro o
  exact h.2 o (by simp)

theorem minimaxValue_oStar_eq_worstCase (sg : StrategicGameProblem Action Opp)
    (position : List (Action × Opp)) (a : Action) (n : ℕ) :
    minimaxValue sg (position ++ [(a, oStar (sg := sg) position a n)]) n =
      sgWorstCaseValue (sg := sg) position a n := by
  classical
  -- Show `f(oStar)` equals the fold-`min` over all `f(o)`, using `oStar_spec`.
  let f : Opp → ℝ := fun o => minimaxValue sg (position ++ [(a, o)]) n
  have hle_fold :
      f (oStar (sg := sg) position a n) ≤ (Finset.univ : Finset Opp).fold min (1 : ℝ) f := by
    have hle_one : f (oStar (sg := sg) position a n) ≤ (1 : ℝ) := by
      simpa [f] using
        minimaxValue_le_one (sg := sg) (position := position ++ [(a, oStar (sg := sg) position a n)]) (remaining := n)
    have hle_all : ∀ o ∈ (Finset.univ : Finset Opp), f (oStar (sg := sg) position a n) ≤ f o := by
      intro o _ho
      simpa [f] using oStar_spec (sg := sg) (position := position) (a := a) (n := n) o
    exact (Finset.le_fold_min (s := (Finset.univ : Finset Opp)) (b := (1 : ℝ)) (f := f)
      (c := f (oStar (sg := sg) position a n))).2 ⟨hle_one, hle_all⟩
  have hfold_le :
      (Finset.univ : Finset Opp).fold min (1 : ℝ) f ≤ f (oStar (sg := sg) position a n) := by
    -- Use membership of `oStar` in `univ` and reflexivity.
    refine (Finset.fold_min_le (s := (Finset.univ : Finset Opp)) (b := (1 : ℝ)) (f := f)
      (c := f (oStar (sg := sg) position a n))).2 ?_
    refine Or.inr ?_
    refine ⟨oStar (sg := sg) position a n, by simp, le_rfl⟩
  have hEq :
      (Finset.univ : Finset Opp).fold min (1 : ℝ) f = f (oStar (sg := sg) position a n) :=
    le_antisymm hfold_le hle_fold
  simpa [sgWorstCaseValue, f] using hEq.symm

/-- The induced SG probability kernel. -/
noncomputable def prob (sg : StrategicGameProblem Action Opp) :
    BayesianAgents.Core.History Action (Percept Opp) → Percept Opp → ENNReal := fun h x =>
  match h.getLast? with
  | some (BayesianAgents.Core.HistElem.act a) =>
      let position := sgPosition (Action := Action) (Opp := Opp) h
      let remaining := sg.maxRounds - position.length
      match remaining with
      | 0 => 0
      | r + 1 =>
          let o := oStar (sg := sg) position a r
          if x.1 = o then
            match r with
            | 0 =>
                let v := sg.gameValuation (position ++ [(a, o)])
                let p : ENNReal := ENNReal.ofReal ((v + 1) / 2)
                if x.2 then p else (1 - p)
            | _ + 1 =>
                if x.2 then 0 else 1
          else 0
  | _ => 0

/-- The environment induced by a strategic game with a minimax opponent
(Hutter 2005, Section 6.3.3, Eq. 6.20-6.21). -/
noncomputable def sgToEnvironment (sg : StrategicGameProblem Action Opp) :
    BayesianAgents.Core.Environment Action (Percept Opp) := by
  classical
  refine { prob := prob (sg := sg), prob_le_one := ?_ }
  intro h _hwf
  classical
  cases hlast : h.getLast? with
  | none =>
      simp [prob, hlast]
  | some e =>
      cases e with
      | per _x =>
          simp [prob, hlast]
      | act a =>
          -- Split on how many rounds remain.
          let position := sgPosition (Action := Action) (Opp := Opp) h
          let remaining := sg.maxRounds - position.length
          cases hrem : remaining with
          | zero =>
              simp [prob, hlast, position, remaining, hrem]
          | succ r =>
              cases r with
              | zero =>
                  -- Terminal: total mass is `p + (1 - p) = 1` on the unique observation `oStar`.
                  let o := oStar (sg := sg) position a 0
                  let v := sg.gameValuation (position ++ [(a, o)])
                  let p : ENNReal := ENNReal.ofReal ((v + 1) / 2)
                  have hp_le : p ≤ (1 : ENNReal) := by
                    have hvBound : |v| ≤ 1 := sg.valuation_bounded (position ++ [(a, o)])
                    have hv_le : v ≤ 1 := (abs_le.mp hvBound).2
                    have : (v + 1) / 2 ≤ (1 : ℝ) := by nlinarith
                    simpa [p] using (ENNReal.ofReal_le_one).2 this
                  have hmass : p + (1 - p) = (1 : ENNReal) := by
                    simpa using add_tsub_cancel_of_le hp_le
                  have hsum :
                      (∑ x : Percept Opp, prob (sg := sg) h x) = p + (1 - p) := by
                    -- Only percepts with observation `o` contribute.
                    simp [prob, hlast, position, remaining, hrem, o, v, p, Fintype.sum_prod_type]
                  simp [hsum, hmass]
              | succ r' =>
                  -- Non-terminal: probability 1 on the unique percept `(oStar, false)`.
                  have hsum :
                      (∑ x : Percept Opp, prob (sg := sg) h x) = (1 : ENNReal) := by
                    simp [prob, hlast, position, remaining, hrem, Fintype.sum_prod_type]
                  simp [hsum]

/-! ### Theorem 6.3.1: AIμ implements minimax -/

private theorem add_one_div_two_mono_iff (x y : ℝ) :
    (x + 1) / 2 ≤ (y + 1) / 2 ↔ x ≤ y := by
  constructor <;> intro h <;> nlinarith

private theorem max_add_one_div_two (x y : ℝ) :
    max ((x + 1) / 2) ((y + 1) / 2) = (max x y + 1) / 2 := by
  by_cases hxy : x ≤ y
  · have hxy' : (x + 1) / 2 ≤ (y + 1) / 2 := by nlinarith
    simp [max_eq_right hxy, max_eq_right hxy']
  · have hyx : y ≤ x := le_of_not_ge hxy
    have hyx' : (y + 1) / 2 ≤ (x + 1) / 2 := by nlinarith
    simp [max_eq_left hyx, max_eq_left hyx']

private theorem fold_max_add_one_div_two {ι : Type*} (s : Finset ι) (b : ℝ) (f : ι → ℝ) :
    s.fold max ((b + 1) / 2) (fun i => (f i + 1) / 2) = (s.fold max b f + 1) / 2 := by
  classical
  refine Finset.induction_on s ?h0 ?hstep
  · simp
  · intro a s ha hs
    simp [Finset.fold_insert, ha, hs, max_add_one_div_two]

mutual
  private theorem optimalQValue_sgHistory_eq_worstCase_transformed (sg : StrategicGameProblem Action Opp) :
      ∀ (position : List (Action × Opp)) (a : Action) (n : ℕ),
        position.length + (n + 1) = sg.maxRounds →
          BayesianAgents.Core.optimalQValue (sgToEnvironment (sg := sg)) gameDiscount
              (sgHistory (Action := Action) (Opp := Opp) position) a (2 * n + 1) =
            (sgWorstCaseValue (sg := sg) position a n + 1) / 2 := by
    intro position a n hlen
    classical
    have ha_wf :
        BayesianAgents.Core.History.wellFormed (Action := Action) (Percept := Percept Opp)
          (sgHistory (Action := Action) (Opp := Opp) position ++ [BayesianAgents.Core.HistElem.act a]) = true :=
      sgHistory_append_act_wellFormed (Action := Action) (Opp := Opp) (pos := position) (a := a)
    have ha_last :
        (sgHistory (Action := Action) (Opp := Opp) position ++ [BayesianAgents.Core.HistElem.act a]).getLast? =
          some (BayesianAgents.Core.HistElem.act a) := by
      simp
    have hpos :
        sgPosition (Action := Action) (Opp := Opp)
            (sgHistory (Action := Action) (Opp := Opp) position ++ [BayesianAgents.Core.HistElem.act a]) = position :=
      sgPosition_sgHistory_append_act (Action := Action) (Opp := Opp) (pos := position) (a := a)
    have hrem : sg.maxRounds - position.length = n + 1 := by
      simpa [hlen] using (Nat.add_sub_cancel_left position.length (n + 1))
    cases n with
    | zero =>
        let o := oStar (sg := sg) position a 0
        have hv_nonneg : 0 ≤ (sg.gameValuation (position ++ [(a, o)]) + 1) / 2 := by
          have hb : |sg.gameValuation (position ++ [(a, o)])| ≤ 1 :=
            sg.valuation_bounded (position ++ [(a, o)])
          have hv_ge : (-1 : ℝ) ≤ sg.gameValuation (position ++ [(a, o)]) := (abs_le.mp hb).1
          nlinarith
        have hq :
            BayesianAgents.Core.optimalQValue (sgToEnvironment (sg := sg)) gameDiscount
                (sgHistory (Action := Action) (Opp := Opp) position) a 1 =
              (ENNReal.ofReal ((sg.gameValuation (position ++ [(a, o)]) + 1) / 2)).toReal := by
          simp [BayesianAgents.Core.optimalQValue, BayesianAgents.Core.optimalValue_zero, sgToEnvironment, prob,
            ha_wf, ha_last, hpos, hrem, o, gameDiscount, Fintype.sum_prod_type]
          rw [Fintype.sum_eq_single (sg.oStar position a 0)]
          · simp
          · intro x hx
            simp [hx]
        have hq' :
            (ENNReal.ofReal ((sg.gameValuation (position ++ [(a, o)]) + 1) / 2)).toReal =
              (sg.gameValuation (position ++ [(a, o)]) + 1) / 2 := by
          simp [ENNReal.toReal_ofReal, hv_nonneg]
        have hminimax :
            sg.gameValuation (position ++ [(a, o)]) =
              sgWorstCaseValue (sg := sg) position a 0 := by
          simpa [o, minimaxValue, sgWorstCaseValue] using
            (minimaxValue_oStar_eq_worstCase (sg := sg) (position := position) (a := a) (n := 0))
        calc
          BayesianAgents.Core.optimalQValue (sgToEnvironment (sg := sg)) gameDiscount
                (sgHistory (Action := Action) (Opp := Opp) position) a 1
              = (ENNReal.ofReal ((sg.gameValuation (position ++ [(a, o)]) + 1) / 2)).toReal := hq
          _ = (sg.gameValuation (position ++ [(a, o)]) + 1) / 2 := hq'
          _ = (sgWorstCaseValue (sg := sg) position a 0 + 1) / 2 := by simp [hminimax]
    | succ n =>
        let o := oStar (sg := sg) position a (n + 1)
        have hlen' : (position ++ [(a, o)]).length + (n + 1) = sg.maxRounds := by
          have hlen' : position.length + (n + 2) = sg.maxRounds := by
            simpa [Nat.add_assoc] using hlen
          -- One round is consumed.
          simpa [List.length_append, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hlen'
        have hnext :
            sgHistory (Action := Action) (Opp := Opp) position ++
                  [BayesianAgents.Core.HistElem.act a, BayesianAgents.Core.HistElem.per (o, false)] =
              sgHistory (Action := Action) (Opp := Opp) (position ++ [(a, o)]) := by
          simp [sgHistory_append, sgHistory, o]
        have hv :
            BayesianAgents.Core.optimalValue (sgToEnvironment (sg := sg)) gameDiscount
                (sgHistory (Action := Action) (Opp := Opp) (position ++ [(a, o)])) (2 * n + 2) =
              (minimaxValue sg (position ++ [(a, o)]) (n + 1) + 1) / 2 := by
          simpa using
            optimalValue_sgHistory_eq_minimax_transformed (sg := sg) (position := position ++ [(a, o)]) (n := n) hlen'
        have hq :
            BayesianAgents.Core.optimalQValue (sgToEnvironment (sg := sg)) gameDiscount
                (sgHistory (Action := Action) (Opp := Opp) position) a (2 * n + 3) =
              BayesianAgents.Core.optimalValue (sgToEnvironment (sg := sg)) gameDiscount
                (sgHistory (Action := Action) (Opp := Opp) (position ++ [(a, o)])) (2 * n + 2) := by
          -- Non-terminal: probability 1 on percept `(o, false)` with reward 0.
          have hq0 :
              BayesianAgents.Core.optimalQValue (sgToEnvironment (sg := sg)) gameDiscount
                  (sgHistory (Action := Action) (Opp := Opp) position) a (2 * n + 3) =
                BayesianAgents.Core.optimalValue (sgToEnvironment (sg := sg)) gameDiscount
                  (sgHistory (Action := Action) (Opp := Opp) position ++
                    [BayesianAgents.Core.HistElem.act a, BayesianAgents.Core.HistElem.per (o, false)]) (2 * n + 2) := by
            simp [BayesianAgents.Core.optimalQValue, sgToEnvironment, prob, ha_wf, ha_last, hpos, hrem, o,
              gameDiscount, Fintype.sum_prod_type]
            rw [Fintype.sum_eq_single (sg.oStar position a (n + 1))]
            · simp
            · intro x hx
              simp [hx]
          simpa [hnext] using hq0
        have hminimax :
            minimaxValue sg (position ++ [(a, o)]) (n + 1) =
              sgWorstCaseValue (sg := sg) position a (n + 1) := by
          simpa [o] using minimaxValue_oStar_eq_worstCase (sg := sg) (position := position) (a := a) (n := n + 1)
        calc
          BayesianAgents.Core.optimalQValue (sgToEnvironment (sg := sg)) gameDiscount
                (sgHistory (Action := Action) (Opp := Opp) position) a (2 * n + 3)
              = BayesianAgents.Core.optimalValue (sgToEnvironment (sg := sg)) gameDiscount
                  (sgHistory (Action := Action) (Opp := Opp) (position ++ [(a, o)])) (2 * n + 2) := hq
          _ = (minimaxValue sg (position ++ [(a, o)]) (n + 1) + 1) / 2 := hv
          _ = (sgWorstCaseValue (sg := sg) position a (n + 1) + 1) / 2 := by simp [hminimax]

  private theorem optimalValue_sgHistory_eq_minimax_transformed (sg : StrategicGameProblem Action Opp) :
      ∀ (position : List (Action × Opp)) (n : ℕ),
        position.length + (n + 1) = sg.maxRounds →
          BayesianAgents.Core.optimalValue (sgToEnvironment (sg := sg)) gameDiscount
              (sgHistory (Action := Action) (Opp := Opp) position) (2 * n + 2) =
            (minimaxValue sg position (n + 1) + 1) / 2 := by
    intro position n hlen
    classical
    let μ := sgToEnvironment (sg := sg)
    let γ := gameDiscount
    let h := sgHistory (Action := Action) (Opp := Opp) position
    have hw :
        BayesianAgents.Core.History.wellFormed (Action := Action) (Percept := Percept Opp) h = true :=
      sgHistory_wellFormed (Action := Action) (Opp := Opp) (pos := position)
    have hq (a : Action) :
        BayesianAgents.Core.optimalQValue μ γ h a (2 * n + 1) =
          (sgWorstCaseValue (sg := sg) position a n + 1) / 2 :=
      optimalQValue_sgHistory_eq_worstCase_transformed (sg := sg) (position := position) (a := a) (n := n) hlen
    have hOpt :
        BayesianAgents.Core.optimalValue μ γ h (2 * n + 2) =
          (Finset.univ : Finset Action).fold max 0 fun a =>
            (sgWorstCaseValue (sg := sg) position a n + 1) / 2 := by
      have hOptRaw :=
        (BayesianAgents.Core.optimalValue_succ (μ := μ) (γ := γ) (h := h) (n := 2 * n + 1))
      simp [μ, γ, h, hw, hq] at hOptRaw
      exact hOptRaw
    have hMinimax :
        minimaxValue sg position (n + 1) =
          (Finset.univ : Finset Action).fold max (-1) fun a => sgWorstCaseValue (sg := sg) position a n := by
      simp [minimaxValue, sgWorstCaseValue]
    calc
      BayesianAgents.Core.optimalValue μ γ h (2 * n + 2)
          = (Finset.univ : Finset Action).fold max 0 (fun a => (sgWorstCaseValue (sg := sg) position a n + 1) / 2) :=
            hOpt
      _ = ((Finset.univ : Finset Action).fold max (-1) (fun a => sgWorstCaseValue (sg := sg) position a n) + 1) / 2 := by
            simpa using
              (fold_max_add_one_div_two (s := (Finset.univ : Finset Action)) (b := (-1 : ℝ))
                (f := fun a => sgWorstCaseValue (sg := sg) position a n))
      _ = (minimaxValue sg position (n + 1) + 1) / 2 := by
            simp [hMinimax]
end

/-- Theorem 6.3.1 (Hutter 2005): in the induced strategic-game environment `μ^SG` modeling a minimax
opponent, the `AIμ` action achieves the minimax value. -/
theorem aimu_eq_minimax [Inhabited Action] (sg : StrategicGameProblem Action Opp)
    (position : List (Action × Opp)) (n : ℕ)
    (hlen : position.length + (n + 1) = sg.maxRounds) :
    minimaxValue sg position (n + 1) =
      sgWorstCaseValue (sg := sg) position
        (BayesianAgents.Core.optimalAction (sgToEnvironment (sg := sg)) gameDiscount
          (sgHistory (Action := Action) (Opp := Opp) position) (2 * n + 1)) n := by
  classical
  set μ := sgToEnvironment (sg := sg)
  set h := sgHistory (Action := Action) (Opp := Opp) position
  have hw :
      BayesianAgents.Core.History.wellFormed (Action := Action) (Percept := Percept Opp) h = true :=
    sgHistory_wellFormed (Action := Action) (Opp := Opp) (pos := position)
  set aStar : Action := BayesianAgents.Core.optimalAction μ gameDiscount h (2 * n + 1)
  have hq (a : Action) :
      BayesianAgents.Core.optimalQValue μ gameDiscount h a (2 * n + 1) =
        (sgWorstCaseValue (sg := sg) position a n + 1) / 2 :=
    optimalQValue_sgHistory_eq_worstCase_transformed (sg := sg) (position := position) (a := a) (n := n) hlen
  have hmax :
      ∀ a : Action, sgWorstCaseValue (sg := sg) position a n ≤ sgWorstCaseValue (sg := sg) position aStar n := by
    intro a
    have hQle :=
      (BayesianAgents.Core.optimalAction_achieves_max (μ := μ) (γ := gameDiscount) (h := h) (horizon := 2 * n + 1)
        (a := a))
    have hQle' : (sgWorstCaseValue (sg := sg) position a n + 1) / 2 ≤
        (sgWorstCaseValue (sg := sg) position aStar n + 1) / 2 := by
      simpa [aStar, hq] using hQle
    exact (add_one_div_two_mono_iff _ _).1 hQle'
  -- `aStar` achieves the `max` over actions, hence attains `minimaxValue`.
  have hFold :
      (Finset.univ : Finset Action).fold max (-1) (fun a => sgWorstCaseValue (sg := sg) position a n) =
        sgWorstCaseValue (sg := sg) position aStar n := by
    have hb : (-1 : ℝ) ≤ sgWorstCaseValue (sg := sg) position aStar n := by
      have hle_one : (-1 : ℝ) ≤ (1 : ℝ) := by linarith
      have hle_all :
          ∀ o ∈ (Finset.univ : Finset Opp), (-1 : ℝ) ≤ minimaxValue sg (position ++ [(aStar, o)]) n := by
        intro o _ho
        simpa using minimaxValue_ge_neg_one (sg := sg) (position := position ++ [(aStar, o)]) (remaining := n)
      have : (-1 : ℝ) ≤ (Finset.univ : Finset Opp).fold min (1 : ℝ) fun o =>
          minimaxValue sg (position ++ [(aStar, o)]) n :=
        (Finset.le_fold_min (s := (Finset.univ : Finset Opp)) (b := (1 : ℝ))
          (f := fun o => minimaxValue sg (position ++ [(aStar, o)]) n) (c := (-1 : ℝ))).2
          ⟨hle_one, hle_all⟩
      simpa [sgWorstCaseValue] using this
    -- Use `fold_max_le` and `le_fold_max` to show the fold equals the chosen maximum.
    apply le_antisymm
    · -- `fold max ≤ w(aStar)` from pointwise bounds.
      refine (Finset.fold_max_le (s := (Finset.univ : Finset Action)) (b := (-1 : ℝ))
        (f := fun a => sgWorstCaseValue (sg := sg) position a n) (c := sgWorstCaseValue (sg := sg) position aStar n)).2 ?_
      refine ⟨hb, ?_⟩
      intro a _ha
      exact hmax a
    · -- `w(aStar) ≤ fold max` since `aStar ∈ univ`.
      refine (Finset.le_fold_max (s := (Finset.univ : Finset Action)) (b := (-1 : ℝ))
        (f := fun a => sgWorstCaseValue (sg := sg) position a n) (c := sgWorstCaseValue (sg := sg) position aStar n)).2 ?_
      refine Or.inr ?_
      exact ⟨aStar, by simp, le_rfl⟩
  -- Finish by unfolding `minimaxValue`.
  simpa [minimaxValue, hFold]

end StrategicGameProblem

/-! ## Section 6.4: Function Minimization (FM)

Minimize f: Y → ℝ using as few function evaluations as possible.
-/

/-!
### A finite FM model (formalized)

The book allows general computable function classes and real-valued outputs, but our AIXI core
model assumes **finite alphabets per cycle**. To fully formalize the Chapter 6 reductions inside
this framework, we use a finite family of candidate objective functions and a finite output type.

This is still faithful to the reduction idea:
- the agent chooses an action/input `y_k`
- the environment returns an output `z_k`
- the objective is to minimize `∑ α_k · z_k`

We embed this as a reward-maximization problem with reward
`r_k := α_k · (1 - cost(z_k))`, where `cost(z_k) ∈ [0,1]` and `α_k ∈ [0,1]`.
-/

/-- A finite function-minimization problem.

`Func` is a finite family of candidate functions, and `prior` is a semimeasure over them.

We include the time index `k : Fin horizon` in the percept so the reward can depend on `k`. -/
structure FunctionMinimizationProblem where
  /-- Inputs the agent can try (the search space). -/
  Action : Type*
  /-- Outputs returned by the objective function (finite encoding). -/
  Value : Type*
  /-- A finite family of possible objective functions. -/
  Func : Type*
  /-- Finiteness assumptions (finite alphabet per cycle). -/
  [actionFintype : Fintype Action]
  [valueFintype : Fintype Value]
  [funcFintype : Fintype Func]
  /-- Cost of an output, normalized to `[0,1]`. -/
  cost : Value → ℝ
  cost_nonneg : ∀ v, 0 ≤ cost v
  cost_le_one : ∀ v, cost v ≤ 1
  /-- Horizon `m` (number of evaluations). -/
  horizon : ℕ
  /-- Weights `α_k ∈ [0,1]` for each cycle `k < m`. -/
  weights : Fin horizon → ℝ
  weights_nonneg : ∀ k, 0 ≤ weights k
  weights_le_one : ∀ k, weights k ≤ 1
  /-- Prior semimeasure over functions. -/
  prior : Func → ENNReal
  prior_sum_le_one : (∑ f : Func, prior f) ≤ 1
  /-- The evaluation function `f(y)`. -/
  eval : Func → Action → Value

attribute [instance] FunctionMinimizationProblem.actionFintype
attribute [instance] FunctionMinimizationProblem.valueFintype
attribute [instance] FunctionMinimizationProblem.funcFintype

namespace FunctionMinimizationProblem

open scoped Classical

/-- The FM percept alphabet: `(k, z_k)` where `k` is the cycle index. -/
abbrev Percept (fm : FunctionMinimizationProblem) : Type* :=
  Fin fm.horizon × fm.Value

instance (fm : FunctionMinimizationProblem) : Fintype (Percept fm) := by
  dsimp [Percept]
  infer_instance

/-- Reward used for the AI-embedding: `r_k = α_k · (1 - cost(z_k))`. -/
def reward (fm : FunctionMinimizationProblem) (x : Percept fm) : ℝ :=
  fm.weights x.1 * (1 - fm.cost x.2)

theorem reward_nonneg (fm : FunctionMinimizationProblem) (x : Percept fm) :
    0 ≤ fm.reward x := by
  have hw : 0 ≤ fm.weights x.1 := fm.weights_nonneg x.1
  have h1 : 0 ≤ 1 - fm.cost x.2 := by
    nlinarith [fm.cost_le_one x.2]
  exact mul_nonneg hw h1

theorem reward_le_one (fm : FunctionMinimizationProblem) (x : Percept fm) :
    fm.reward x ≤ 1 := by
  have hw0 : 0 ≤ fm.weights x.1 := fm.weights_nonneg x.1
  have hw1 : fm.weights x.1 ≤ 1 := fm.weights_le_one x.1
  have h10 : 0 ≤ 1 - fm.cost x.2 := by
    nlinarith [fm.cost_le_one x.2]
  have h11 : 1 - fm.cost x.2 ≤ 1 := by
    nlinarith [fm.cost_nonneg x.2]
  -- `α ≤ 1` and `1 - cost ≤ 1`, with both nonnegative.
  have : fm.weights x.1 * (1 - fm.cost x.2) ≤ 1 * 1 := by
    exact mul_le_mul hw1 h11 h10 (by simp)
  simpa [FunctionMinimizationProblem.reward] using this

noncomputable instance (fm : FunctionMinimizationProblem) :
    BayesianAgents.Core.PerceptReward (Percept fm) where
  reward := fm.reward
  reward_nonneg := fm.reward_nonneg
  reward_le_one := fm.reward_le_one

/-- Extract the list of observed `(action, value)` pairs from a history.

Trailing actions (if any) are ignored. -/
def actionValuePairs (fm : FunctionMinimizationProblem) :
    BayesianAgents.Core.History fm.Action (Percept fm) → List (fm.Action × fm.Value)
  | [] => []
  | BayesianAgents.Core.HistElem.act a ::
        BayesianAgents.Core.HistElem.per x :: rest =>
      (a, x.2) :: actionValuePairs fm rest
  | _ :: rest => actionValuePairs fm rest

/-- A function is consistent with a history iff it matches all previously observed evaluations. -/
def Consistent (fm : FunctionMinimizationProblem) (f : fm.Func)
    (h : BayesianAgents.Core.History fm.Action (Percept fm)) : Prop :=
  ∀ p ∈ actionValuePairs fm h, fm.eval f p.1 = p.2

/-- The induced FM environment: sampling next outputs from the prior restricted to functions
consistent with the past. (Unnormalized semimeasure form.) -/
noncomputable def toEnvironment (fm : FunctionMinimizationProblem) :
    BayesianAgents.Core.Environment fm.Action (Percept fm) := by
  classical
  let probFun : BayesianAgents.Core.History fm.Action (Percept fm) → Percept fm → ENNReal :=
    fun h x =>
      match h.getLast? with
      | some (BayesianAgents.Core.HistElem.act a) =>
          if hk : BayesianAgents.Core.History.cycles h < fm.horizon then
            let idx : Fin fm.horizon := ⟨BayesianAgents.Core.History.cycles h, hk⟩
            if x.1 = idx then
              ∑ f : fm.Func,
                if fm.Consistent f h ∧ fm.eval f a = x.2 then fm.prior f else 0
            else 0
          else 0
      | _ => 0
  refine { prob := probFun, prob_le_one := ?_ }
  intro h _hwf
  classical
  cases hlast : h.getLast? with
  | none =>
      simp [probFun, hlast]
  | some e =>
      cases e with
      | per _x =>
          simp [probFun, hlast]
      | act a =>
          by_cases hk : BayesianAgents.Core.History.cycles h < fm.horizon
          · set idx : Fin fm.horizon := ⟨BayesianAgents.Core.History.cycles h, hk⟩
            have hsum :
                (∑ x : Percept fm, probFun h x) =
                  ∑ v : fm.Value,
                    ∑ f : fm.Func, if fm.Consistent f h ∧ fm.eval f a = v then fm.prior f else 0 := by
              simp [probFun, hlast, hk, Percept, Fintype.sum_prod_type]
            have hswap :
                (∑ v : fm.Value,
                    ∑ f : fm.Func, if fm.Consistent f h ∧ fm.eval f a = v then fm.prior f else 0) =
                  ∑ f : fm.Func,
                    ∑ v : fm.Value, if fm.Consistent f h ∧ fm.eval f a = v then fm.prior f else 0 := by
              classical
              -- Both sides are sums over the same product type `Value × Func`.
              calc
                (∑ v : fm.Value,
                      ∑ f : fm.Func, if fm.Consistent f h ∧ fm.eval f a = v then fm.prior f else 0) =
                    ∑ x : fm.Value × fm.Func,
                      if fm.Consistent x.2 h ∧ fm.eval x.2 a = x.1 then fm.prior x.2 else 0 := by
                        simp [Fintype.sum_prod_type]
                _ =
                    ∑ f : fm.Func,
                      ∑ v : fm.Value, if fm.Consistent f h ∧ fm.eval f a = v then fm.prior f else 0 := by
                        simp [Fintype.sum_prod_type_right]
            have hinner (f : fm.Func) :
                (∑ v : fm.Value, if fm.Consistent f h ∧ fm.eval f a = v then fm.prior f else 0) ≤ fm.prior f := by
              classical
              by_cases hc : fm.Consistent f h
              · have hEval : (∑ v : fm.Value, if fm.eval f a = v then fm.prior f else 0) = fm.prior f := by
                  simp
                have hSum :
                    (∑ v : fm.Value, if fm.Consistent f h ∧ fm.eval f a = v then fm.prior f else 0) =
                      fm.prior f := by
                  simp [hc, hEval]
                exact le_of_eq hSum
              · simp [hc]
            have hle :
                (∑ f : fm.Func,
                    ∑ v : fm.Value, if fm.Consistent f h ∧ fm.eval f a = v then fm.prior f else 0) ≤
                  ∑ f : fm.Func, fm.prior f := by
              classical
              -- Pointwise bound `∑ v ... ≤ prior f`, then sum over `f`.
              have hle' :
                  ((Finset.univ : Finset fm.Func).sum fun f =>
                      (∑ v : fm.Value,
                        if fm.Consistent f h ∧ fm.eval f a = v then fm.prior f else 0)) ≤
                    (Finset.univ : Finset fm.Func).sum fun f => fm.prior f := by
                refine Finset.sum_le_sum ?_
                intro f _hf
                exact hinner f
              simpa using hle'
            -- Finish the semimeasure bound by chaining the reductions.
            have : (∑ x : Percept fm, probFun h x) ≤ 1 := by
              calc
                (∑ x : Percept fm, probFun h x) =
                    ∑ v : fm.Value,
                      ∑ f : fm.Func,
                        if fm.Consistent f h ∧ fm.eval f a = v then fm.prior f else 0 := hsum
                _ = ∑ f : fm.Func,
                      ∑ v : fm.Value,
                        if fm.Consistent f h ∧ fm.eval f a = v then fm.prior f else 0 := hswap
                _ ≤ ∑ f : fm.Func, fm.prior f := hle
                _ ≤ 1 := fm.prior_sum_le_one
            exact this
          · simp [probFun, hlast, hk]

/-- Total weight `∑_{k<m} α_k`. -/
noncomputable def totalWeight (fm : FunctionMinimizationProblem) : ℝ :=
  ∑ k : Fin fm.horizon, fm.weights k

/-- For the embedding reward, the weighted cost is a constant shift of the value. -/
noncomputable def expectedCost (fm : FunctionMinimizationProblem)
    (π : BayesianAgents.Core.Agent fm.Action (Percept fm))
    (γ : BayesianAgents.Core.DiscountFactor := ⟨1, by simp, by simp⟩)
    (h : BayesianAgents.Core.History fm.Action (Percept fm) := []) : ℝ :=
  fm.totalWeight - BayesianAgents.Core.value (toEnvironment fm) π γ h fm.horizon

theorem expectedCost_le_iff_value_ge (fm : FunctionMinimizationProblem)
    (π₁ π₂ : BayesianAgents.Core.Agent fm.Action (Percept fm))
    (γ : BayesianAgents.Core.DiscountFactor := ⟨1, by simp, by simp⟩)
    (h : BayesianAgents.Core.History fm.Action (Percept fm) := []) :
    fm.expectedCost π₁ γ h ≤ fm.expectedCost π₂ γ h ↔
      BayesianAgents.Core.value (toEnvironment fm) π₂ γ h fm.horizon ≤
        BayesianAgents.Core.value (toEnvironment fm) π₁ γ h fm.horizon := by
  -- Subtracting from a constant reverses the inequality.
  simpa [FunctionMinimizationProblem.expectedCost] using
    (sub_le_sub_iff_left fm.totalWeight
      (b := BayesianAgents.Core.value (toEnvironment fm) π₁ γ h fm.horizon)
      (c := BayesianAgents.Core.value (toEnvironment fm) π₂ γ h fm.horizon))

end FunctionMinimizationProblem

/-- Final model (FMF): Only the final output matters.
    α_k = 0 for k < m, α_m = 1 -/
def finalModelWeights {m : ℕ} : Fin m → ℝ :=
  fun k => if (k : ℕ) + 1 = m then 1 else 0

/-- Sum model (FMS): All outputs matter equally.
    α_k = 1 for all k -/
def sumModelWeights {m : ℕ} : Fin m → ℝ := fun _ => 1

/-- Exponential model (FME): Increasing pressure to produce good outputs.
    α_k = e^{γ(k-1)} for some γ > 0 -/
noncomputable def exponentialModelWeights {m : ℕ} (γ : ℝ) : Fin m → ℝ :=
  fun k => Real.exp (γ * ((k : ℕ) : ℝ))

/-! ### Theorem 6.4.1: FM Embeds in AI Framework (finite version)

The book's FM setting allows general computable function classes and real-valued outputs. In this
development we use a finite family of candidate functions and a finite output alphabet (to match
the finite-percept AIXI core).

The embedding is implemented by:
- `FunctionMinimizationProblem.toEnvironment`
- reward `r_k = α_k · (1 - cost(z_k))`

and the objective correspondence (minimizing expected cost vs maximizing AIXI value) is captured
by `FunctionMinimizationProblem.expectedCost_le_iff_value_ge`. -/

/-! ### Theorem 6.4.2 (finite): Optimal FM cost bound

The book's Theorem 6.4.2 is about *inventiveness* of a universal (infinite) function minimizer.
In this development we stay in the finite-alphabet AIXI core, so the literal “infinitely many
distinct inputs” statement does not apply.

What we can formalize in the finite model is the *optimality* consequence of the embedding
(Theorem 6.4.1): the policy-independent optimal value `V*` in the induced environment yields a
lower bound on the expected FM cost for any policy. -/

namespace FunctionMinimizationProblem

/-- The lower bound on expected cost induced by the optimal value `V*` in the embedded FM environment. -/
noncomputable def optimalExpectedCost (fm : FunctionMinimizationProblem)
    (γ : BayesianAgents.Core.DiscountFactor := ⟨1, by simp, by simp⟩)
    (h : BayesianAgents.Core.History fm.Action (Percept fm) := []) : ℝ :=
  fm.totalWeight - BayesianAgents.Core.optimalValue (toEnvironment fm) γ h fm.horizon

theorem optimalExpectedCost_le_expectedCost (fm : FunctionMinimizationProblem)
    (π : BayesianAgents.Core.Agent fm.Action (Percept fm))
    (γ : BayesianAgents.Core.DiscountFactor := ⟨1, by simp, by simp⟩)
    (h : BayesianAgents.Core.History fm.Action (Percept fm) := []) :
    fm.optimalExpectedCost γ h ≤ fm.expectedCost π γ h := by
  have hval :
      BayesianAgents.Core.value (toEnvironment fm) π γ h fm.horizon ≤
        BayesianAgents.Core.optimalValue (toEnvironment fm) γ h fm.horizon :=
    BayesianAgents.Core.value_le_optimalValue
      (μ := toEnvironment fm) (π := π) (γ := γ) (h := h) (n := fm.horizon)
  -- Subtracting a larger value yields a smaller cost.
  simpa [FunctionMinimizationProblem.optimalExpectedCost, FunctionMinimizationProblem.expectedCost] using
    (sub_le_sub_left hval fm.totalWeight)

end FunctionMinimizationProblem

/-! ## Section 6.5: Supervised Learning from Examples (EX)

Learn a relation R ⊆ Z × V from examples.
-/

/-!
### A finite EX model (formalized)

To stay compatible with the finite-alphabet agent/environment core (`BayesianAgents.Core`),
we formalize a finite supervised-learning setting:

* `Z` is a finite input alphabet (queries/examples).
* `V` is a finite label alphabet.
* `Hyp` is a finite hypothesis class of label functions `Z → V` with a semimeasure prior.
* The environment provides a semimeasure over streams of inputs and a boolean “is-labeled” flag.

Timing in the AIXI cycle is “one-step delayed”, matching the standard RL convention:

* At cycle `k`, the environment outputs the next input `z_k` (and, if labeled, its label).
* At cycle `k+1`, the agent outputs its prediction for `z_k`.
* The reward bit in the percept at cycle `k+1` indicates whether that prediction was correct.
-/

/-- A supervised learning problem (finite-alphabet version). -/
structure SupervisedLearningProblem where
  /-- Input alphabet. -/
  Z : Type*
  /-- Label alphabet (predictions). -/
  V : Type*
  /-- Hypothesis class (finite family of label functions). -/
  Hyp : Type*
  /-- Finiteness assumptions. -/
  [zFintype : Fintype Z]
  [vFintype : Fintype V]
  [hypFintype : Fintype Hyp]
  [vDecidableEq : DecidableEq V]
  /-- Hypothesis interpretation: a label function `Z → V`. -/
  label : Hyp → Z → V
  /-- Prior semimeasure over hypotheses. -/
  prior : Hyp → ENNReal
  prior_sum_le_one : (∑ h : Hyp, prior h) ≤ 1
  /-- Semimeasure over streams of inputs and “is-labeled” flags. -/
  μ : List (Z × Bool) → ENNReal
  μ_base_le_one : μ [] ≤ 1
  semimeasure : ∀ xs, (∑ s : Z × Bool, μ (xs ++ [s])) ≤ μ xs

attribute [instance] SupervisedLearningProblem.zFintype
attribute [instance] SupervisedLearningProblem.vFintype
attribute [instance] SupervisedLearningProblem.hypFintype
attribute [instance] SupervisedLearningProblem.vDecidableEq

namespace SupervisedLearningProblem

open scoped BigOperators
open scoped Classical

abbrev State (ex : SupervisedLearningProblem) : Type* :=
  ex.Z × Bool

/-- The observation presented by the supervisor: an input `z` and an optional label. -/
abbrev Presentation (ex : SupervisedLearningProblem) :=
  ex.Z × Option ex.V

/-- The percept alphabet: an observation together with a reward bit. -/
abbrev Percept (ex : SupervisedLearningProblem) :=
  Presentation ex × Bool

instance (ex : SupervisedLearningProblem) : Fintype (State ex) := by
  dsimp [State]
  infer_instance

instance (ex : SupervisedLearningProblem) : Fintype (Presentation ex) := by
  dsimp [Presentation]
  infer_instance

instance (ex : SupervisedLearningProblem) : Fintype (Percept ex) := by
  dsimp [Percept]
  infer_instance

/-- Extract the `(z, isLabeled)` state from a presentation. -/
def stateOfPresentation (ex : SupervisedLearningProblem) (p : Presentation ex) : State ex :=
  (p.1, p.2.isSome)

def stateOfPercept (ex : SupervisedLearningProblem) (x : Percept ex) : State ex :=
  stateOfPresentation ex x.1

/-- The canonical presentation for a given hypothesis and state. -/
noncomputable def presentationOfState (ex : SupervisedLearningProblem) (h : ex.Hyp) (s : State ex) :
    Presentation ex :=
  (s.1, if s.2 then some (ex.label h s.1) else none)

/-- Reward (as a real number) extracted from the percept reward bit. -/
def reward (ex : SupervisedLearningProblem) (x : Percept ex) : ℝ :=
  if x.2 then 1 else 0

theorem reward_nonneg (ex : SupervisedLearningProblem) (x : Percept ex) :
    0 ≤ ex.reward x := by
  by_cases hx : x.2
  · simp [reward, hx]
  · simp [reward, hx]

theorem reward_le_one (ex : SupervisedLearningProblem) (x : Percept ex) :
    ex.reward x ≤ 1 := by
  by_cases hx : x.2
  · simp [reward, hx]
  · simp [reward, hx]

noncomputable instance (ex : SupervisedLearningProblem) :
    BayesianAgents.Core.PerceptReward (Percept ex) where
  reward := ex.reward
  reward_nonneg := ex.reward_nonneg
  reward_le_one := ex.reward_le_one

/-- Extract the presentation stream from a history. -/
def presentations (ex : SupervisedLearningProblem) :
    BayesianAgents.Core.History ex.V (Percept ex) → List (Presentation ex) :=
  fun h => (BayesianAgents.Core.History.percepts (Action := ex.V) (Percept := Percept ex) h).map Prod.fst

/-- Extract the `(z, isLabeled)` stream from a history (used to index `μ`). -/
def states (ex : SupervisedLearningProblem) :
    BayesianAgents.Core.History ex.V (Percept ex) → List (State ex) :=
  fun h => (ex.presentations h).map (stateOfPresentation ex)

theorem states_append_per (ex : SupervisedLearningProblem)
    (h : BayesianAgents.Core.History ex.V (Percept ex)) (x : Percept ex) :
    ex.states (h ++ [BayesianAgents.Core.HistElem.per x]) =
      ex.states h ++ [ex.stateOfPercept x] := by
  simp [states, presentations, stateOfPercept, stateOfPresentation,
    BayesianAgents.Core.History.percepts, BayesianAgents.Core.History.percepts_append,
    List.map_append, List.map_map]

/-- The last presentation seen so far (if any). -/
def lastPresentation? (ex : SupervisedLearningProblem)
    (h : BayesianAgents.Core.History ex.V (Percept ex)) : Option (Presentation ex) :=
  (ex.presentations h).getLast?

/-- The reward bit the environment expects to output for a given hypothesis.

The reward at the next cycle is based on the *previous* presentation:
it is `true` exactly when the previous presentation was a query and the agent's action matches
the hypothesis label for that query. -/
noncomputable def expectedRewardBit (ex : SupervisedLearningProblem) (h : ex.Hyp)
    (hist : BayesianAgents.Core.History ex.V (Percept ex)) (a : ex.V) : Bool :=
  match ex.lastPresentation? hist with
  | some (z, none) => decide (a = ex.label h z)
  | _ => false

/-- A presentation is consistent with a hypothesis iff any displayed label matches it. -/
def labelConsistent (ex : SupervisedLearningProblem) (h : ex.Hyp) (p : Presentation ex) : Prop :=
  match p.2 with
  | none => True
  | some v => v = ex.label h p.1

/-- One-step consistency condition for a *new* percept, given the current history and chosen action. -/
def stepConsistent (ex : SupervisedLearningProblem) (h : ex.Hyp)
    (hist : BayesianAgents.Core.History ex.V (Percept ex)) (a : ex.V) (x : Percept ex) : Prop :=
  x.2 = ex.expectedRewardBit h hist a ∧ ex.labelConsistent h x.1

/-- Extract the completed (action, percept) cycles from a history.

Trailing actions (if any) are ignored. -/
def actionPerceptPairs (ex : SupervisedLearningProblem) :
    BayesianAgents.Core.History ex.V (Percept ex) → List (ex.V × Percept ex)
  | [] => []
  | BayesianAgents.Core.HistElem.act a ::
        BayesianAgents.Core.HistElem.per x :: rest =>
      (a, x) :: actionPerceptPairs ex rest
  | _ :: rest => actionPerceptPairs ex rest

/-- Hypothesis consistency with a full history (labels and reward bits). -/
def ConsistentAux (ex : SupervisedLearningProblem) (h : ex.Hyp) :
    Option (Presentation ex) → List (ex.V × Percept ex) → Prop
  | _prev, [] => True
  | prev, (a, x) :: rest =>
      let p := x.1
      let rewardOk : Prop :=
        match prev with
        | some (z, none) => x.2 = decide (a = ex.label h z)
        | _ => x.2 = false
      rewardOk ∧ ex.labelConsistent h p ∧ ConsistentAux ex h (some p) rest

def Consistent (ex : SupervisedLearningProblem) (h : ex.Hyp)
    (hist : BayesianAgents.Core.History ex.V (Percept ex)) : Prop :=
  ConsistentAux ex h none (actionPerceptPairs ex hist)

/-- Any prefix of the semimeasure `μ` is bounded by 1. -/
theorem μ_le_one (ex : SupervisedLearningProblem) (xs : List (State ex)) : ex.μ xs ≤ 1 := by
  classical
  induction xs using List.reverseRecOn with
  | nil =>
      simpa using ex.μ_base_le_one
  | append_singleton init s ih =>
      have hterm :
          ex.μ (init ++ [s]) ≤ ∑ t : State ex, ex.μ (init ++ [t]) := by
        -- `μ(init++[s])` is one term in the sum of all extensions.
        have :
            ex.μ (init ++ [s]) ≤
              (Finset.univ : Finset (State ex)).sum (fun t : State ex => ex.μ (init ++ [t])) := by
          refine
            Finset.single_le_sum (s := (Finset.univ : Finset (State ex)))
              (f := fun t : State ex => ex.μ (init ++ [t])) ?_ ?_
          · intro t _ht
            exact zero_le _
          · simp
        simpa using this
      have hsum : (∑ t : State ex, ex.μ (init ++ [t])) ≤ ex.μ init :=
        ex.semimeasure init
      exact hterm.trans (hsum.trans ih)

set_option maxHeartbeats 1500000

/-- Summing `μ` over step-consistent percepts yields the total `μ`-mass of all next states.

For a fixed hypothesis `h`, `stepConsistent` selects exactly one reward bit and (in the labeled case)
exactly one label for each state `(z, isLabeled)`. -/
theorem sum_stepConsistent_μ (ex : SupervisedLearningProblem) (h : ex.Hyp)
    (hist : BayesianAgents.Core.History ex.V (Percept ex)) (a : ex.V) :
    (∑ x : Percept ex,
          if ex.stepConsistent h hist a x then
            ex.μ (ex.states hist ++ [ex.stateOfPercept x])
          else 0) =
      ∑ s : State ex, ex.μ (ex.states hist ++ [s]) := by
  classical
  -- Expand the sum over `Percept = Presentation × Bool`.
  -- First collapse the sum over the reward bit.
  have hReward (p : Presentation ex) :
      (∑ r : Bool,
            if (r = ex.expectedRewardBit h hist a ∧ ex.labelConsistent h p) then
              ex.μ (ex.states hist ++ [ex.stateOfPresentation p])
            else 0) =
        if ex.labelConsistent h p then ex.μ (ex.states hist ++ [ex.stateOfPresentation p]) else 0 := by
    by_cases hp : ex.labelConsistent h p
    · have :
          (∑ r : Bool,
                if r = ex.expectedRewardBit h hist a then
                  ex.μ (ex.states hist ++ [ex.stateOfPresentation p])
                else 0) =
            ex.μ (ex.states hist ++ [ex.stateOfPresentation p]) := by
        simp
      simp [hp]
    · simp [hp]

  have hPres :
      (∑ p : Presentation ex,
            if ex.labelConsistent h p then ex.μ (ex.states hist ++ [ex.stateOfPresentation p]) else 0) =
        ∑ s : State ex, ex.μ (ex.states hist ++ [s]) := by
    classical
    -- Expand `Presentation = Z × Option V`.
    -- For each `z`, the `none` case contributes the query state `(z,false)`, and exactly one `some v`
    -- contributes the labeled state `(z,true)`.
    have hOpt (z : ex.Z) :
        (∑ ov : Option ex.V,
              let p : Presentation ex := by
                dsimp [Presentation]
                exact (z, ov)
              if ex.labelConsistent h p then
                ex.μ (ex.states hist ++ [ex.stateOfPresentation p])
              else 0)
          =
        ex.μ (ex.states hist ++ [(z, false)]) + ex.μ (ex.states hist ++ [(z, true)]) := by
      classical
      -- Define a version of the summand that packages `(z, ov)` as a `Presentation ex`.
      let f : Option ex.V → ENNReal := fun ov =>
        let p : Presentation ex := by
          dsimp [Presentation]
          exact (z, ov)
        if ex.labelConsistent h p then
          ex.μ (ex.states hist ++ [ex.stateOfPresentation p])
        else 0

      have hsplit : (∑ ov : Option ex.V, f ov) = f none + ∑ v : ex.V, f (some v) := by
        exact Fintype.sum_option (f := f)

      have hNone : f none = ex.μ (ex.states hist ++ [(z, false)]) := by
        simp [f, labelConsistent, stateOfPresentation, Presentation]

      have hSome : (∑ v : ex.V, f (some v)) = ex.μ (ex.states hist ++ [(z, true)]) := by
        have hf (v : ex.V) :
            f (some v) = if v = ex.label h z then ex.μ (ex.states hist ++ [(z, true)]) else 0 := by
          simp [f, labelConsistent, stateOfPresentation, Presentation]
        have :
            (∑ v : ex.V, if v = ex.label h z then ex.μ (ex.states hist ++ [(z, true)]) else 0) =
              ex.μ (ex.states hist ++ [(z, true)]) := by
          exact
            (Fintype.sum_ite_eq' (ι := ex.V) (M := ENNReal) (ex.label h z)
              (fun _ : ex.V => ex.μ (ex.states hist ++ [(z, true)])))
        simp [hf, this]

      have :
          (∑ ov : Option ex.V, f ov) =
            ex.μ (ex.states hist ++ [(z, false)]) + ex.μ (ex.states hist ++ [(z, true)]) := by
        calc
          (∑ ov : Option ex.V, f ov) = f none + ∑ v : ex.V, f (some v) := hsplit
          _ = ex.μ (ex.states hist ++ [(z, false)]) + ex.μ (ex.states hist ++ [(z, true)]) := by
            simp [hNone, hSome]

      simpa [f] using this
    -- Push the `Option` computation through the outer sum over `z`.
    have :
        (∑ p : Presentation ex,
              if ex.labelConsistent h p then ex.μ (ex.states hist ++ [ex.stateOfPresentation p]) else 0) =
          ∑ z : ex.Z,
            (ex.μ (ex.states hist ++ [(z, false)]) + ex.μ (ex.states hist ++ [(z, true)])) := by
      -- Expand `Presentation = Z × Option V` into nested sums and use `hOpt`.
      classical
      -- First rewrite the sum over `Presentation` as a nested sum over `(z, ov)`.
      have hExpand :
          (∑ p : Presentation ex,
                if ex.labelConsistent h p then ex.μ (ex.states hist ++ [ex.stateOfPresentation p]) else 0) =
            ∑ z : ex.Z,
              ∑ ov : Option ex.V,
                let p : Presentation ex := by
                  dsimp [Presentation]
                  exact (z, ov)
                if ex.labelConsistent h p then
                  ex.μ (ex.states hist ++ [ex.stateOfPresentation p])
                else 0 := by
        -- `abbrev` types do not always reduce during elaboration; introduce an explicit `Presentation` term.
        simpa [Presentation] using
          (Fintype.sum_prod_type (f := fun p : ex.Z × Option ex.V =>
            let p' : Presentation ex := by
              dsimp [Presentation]
              exact p
            if ex.labelConsistent h p' then
              ex.μ (ex.states hist ++ [ex.stateOfPresentation p'])
            else 0))
      -- Then use `hOpt` pointwise.
      calc
        (∑ p : Presentation ex,
              if ex.labelConsistent h p then ex.μ (ex.states hist ++ [ex.stateOfPresentation p]) else 0) =
            ∑ z : ex.Z,
              ∑ ov : Option ex.V,
                let p : Presentation ex := by
                  dsimp [Presentation]
                  exact (z, ov)
                if ex.labelConsistent h p then
                  ex.μ (ex.states hist ++ [ex.stateOfPresentation p])
                else 0 := hExpand
        _ =
            ∑ z : ex.Z,
              (ex.μ (ex.states hist ++ [(z, false)]) + ex.μ (ex.states hist ++ [(z, true)])) := by
          -- Apply `hOpt` to each `z`.
          refine Fintype.sum_congr
            (f := fun z : ex.Z =>
              ∑ ov : Option ex.V,
                let p : Presentation ex := by
                  dsimp [Presentation]
                  exact (z, ov)
                if ex.labelConsistent h p then
                  ex.μ (ex.states hist ++ [ex.stateOfPresentation p])
                else 0)
            (g := fun z : ex.Z =>
              ex.μ (ex.states hist ++ [(z, false)]) + ex.μ (ex.states hist ++ [(z, true)])) ?_
          intro z
          simpa using (hOpt z)
    -- Rewrite the RHS as a sum over `State = Z × Bool`.
    have hState :
        (∑ s : State ex, ex.μ (ex.states hist ++ [s])) =
          ∑ z : ex.Z,
            (ex.μ (ex.states hist ++ [(z, false)]) + ex.μ (ex.states hist ++ [(z, true)])) := by
      classical
      -- Expand `State = Z × Bool`.
      have :
          (∑ s : State ex, ex.μ (ex.states hist ++ [s])) =
            ∑ z : ex.Z, ∑ b : Bool, ex.μ (ex.states hist ++ [(z, b)]) := by
        simpa [State] using
          (Fintype.sum_prod_type (f := fun s : ex.Z × Bool => ex.μ (ex.states hist ++ [s])))
      -- Evaluate the Bool sum and normalize order.
      have hb (z : ex.Z) :
          (∑ b : Bool, ex.μ (ex.states hist ++ [(z, b)])) =
            ex.μ (ex.states hist ++ [(z, false)]) + ex.μ (ex.states hist ++ [(z, true)]) := by
        have ht :
            (∑ b : Bool, ex.μ (ex.states hist ++ [(z, b)])) =
              ex.μ (ex.states hist ++ [(z, true)]) + ex.μ (ex.states hist ++ [(z, false)]) := by
          simp
        calc
          (∑ b : Bool, ex.μ (ex.states hist ++ [(z, b)])) =
              ex.μ (ex.states hist ++ [(z, true)]) + ex.μ (ex.states hist ++ [(z, false)]) := ht
          _ = ex.μ (ex.states hist ++ [(z, false)]) + ex.μ (ex.states hist ++ [(z, true)]) := by
              simp [add_comm]
      -- Substitute `hb` pointwise.
      calc
        (∑ s : State ex, ex.μ (ex.states hist ++ [s])) =
            ∑ z : ex.Z, ∑ b : Bool, ex.μ (ex.states hist ++ [(z, b)]) := this
        _ =
            ∑ z : ex.Z,
              (ex.μ (ex.states hist ++ [(z, false)]) + ex.μ (ex.states hist ++ [(z, true)])) := by
              refine Fintype.sum_congr
                (f := fun z : ex.Z => ∑ b : Bool, ex.μ (ex.states hist ++ [(z, b)]))
                (g := fun z : ex.Z =>
                  ex.μ (ex.states hist ++ [(z, false)]) + ex.μ (ex.states hist ++ [(z, true)])) ?_
              intro z
              exact hb z
    -- Finish `hPres`.
    calc
      (∑ p : Presentation ex,
            if ex.labelConsistent h p then ex.μ (ex.states hist ++ [ex.stateOfPresentation p]) else 0) =
          ∑ z : ex.Z,
            (ex.μ (ex.states hist ++ [(z, false)]) + ex.μ (ex.states hist ++ [(z, true)])) := this
      _ = ∑ s : State ex, ex.μ (ex.states hist ++ [s]) := by
            simpa using hState.symm

  -- Put the pieces together.
  -- Expand the percept sum as a nested sum and apply `hReward` and `hPres`.
  -- First expand over `Percept = Presentation × Bool`.
  have :
      (∑ x : Percept ex,
            if ex.stepConsistent h hist a x then ex.μ (ex.states hist ++ [ex.stateOfPercept x]) else 0) =
        ∑ p : Presentation ex,
          (if ex.labelConsistent h p then ex.μ (ex.states hist ++ [ex.stateOfPresentation p]) else 0) := by
    classical
    -- Use `Fintype.sum_prod_type` to expand the percept sum into a nested sum over presentations and reward bits,
    -- then collapse the inner sum with `hReward`.
    -- Start by rewriting the sum over `Percept ex = Presentation ex × Bool`.
    have hprod :
        (∑ x : Percept ex,
              if ex.stepConsistent h hist a x then ex.μ (ex.states hist ++ [ex.stateOfPercept x]) else 0) =
          ∑ p : Presentation ex,
            ∑ r : Bool,
              if (r = ex.expectedRewardBit h hist a ∧ ex.labelConsistent h p) then
                ex.μ (ex.states hist ++ [ex.stateOfPresentation p])
              else 0 := by
      -- `stateOfPercept (p,r) = stateOfPresentation p`, and `stepConsistent` unfolds to the conjunction shown.
      -- Avoid `simp` rewriting the Bool sum into `true/false` cases; keep it as `∑ r : Bool, ...`.
      simpa [Percept, stepConsistent, stateOfPercept, stateOfPresentation] using
        (Fintype.sum_prod_type (f := fun x : Presentation ex × Bool =>
          if ex.stepConsistent h hist a x then
            ex.μ (ex.states hist ++ [ex.stateOfPercept x])
          else 0))
    -- Collapse the inner sum over `r` using `hReward` (pointwise in `p`).
    calc
      (∑ x : Percept ex,
            if ex.stepConsistent h hist a x then ex.μ (ex.states hist ++ [ex.stateOfPercept x]) else 0)
          = ∑ p : Presentation ex,
              ∑ r : Bool,
                if (r = ex.expectedRewardBit h hist a ∧ ex.labelConsistent h p) then
                  ex.μ (ex.states hist ++ [ex.stateOfPresentation p])
                else 0 := hprod
      _ = ∑ p : Presentation ex,
            (if ex.labelConsistent h p then ex.μ (ex.states hist ++ [ex.stateOfPresentation p]) else 0) := by
            -- rewrite the inner sum using `hReward`
            -- Apply `hReward` pointwise in `p`.
            refine Fintype.sum_congr
              (f := fun p : Presentation ex =>
                ∑ r : Bool,
                  if r = ex.expectedRewardBit h hist a ∧ ex.labelConsistent h p then
                    ex.μ (ex.states hist ++ [ex.stateOfPresentation p])
                  else 0)
              (g := fun p : Presentation ex =>
                if ex.labelConsistent h p then ex.μ (ex.states hist ++ [ex.stateOfPresentation p]) else 0) ?_
            intro p
            simpa using (hReward p)
  -- Replace the presentation sum by the state sum.
  calc
    (∑ x : Percept ex,
          if ex.stepConsistent h hist a x then ex.μ (ex.states hist ++ [ex.stateOfPercept x]) else 0) =
        ∑ p : Presentation ex,
          (if ex.labelConsistent h p then ex.μ (ex.states hist ++ [ex.stateOfPresentation p]) else 0) := this
    _ = ∑ s : State ex, ex.μ (ex.states hist ++ [s]) := hPres

/-- The induced EX environment: a mixture over hypotheses, each producing labeled examples
according to its label function. -/
noncomputable def toEnvironment (ex : SupervisedLearningProblem) :
    BayesianAgents.Core.Environment ex.V (Percept ex) := by
  classical
  let probFun :
      BayesianAgents.Core.History ex.V (Percept ex) → Percept ex → ENNReal :=
    fun hist x =>
      match hist.getLast? with
      | some (BayesianAgents.Core.HistElem.act a) =>
          ∑ h : ex.Hyp,
            if ex.Consistent h hist ∧ ex.stepConsistent h hist a x then
              ex.prior h * ex.μ (ex.states hist ++ [ex.stateOfPercept x])
            else 0
      | _ => 0
  refine { prob := probFun, prob_le_one := ?_ }
  intro hist hwf
  classical
  cases hlast : hist.getLast? with
  | none =>
      simp [probFun, hlast]
  | some e =>
      cases e with
      | per _x =>
          simp [probFun, hlast]
      | act a =>
          -- Let `extSum` be the total `μ`-mass of all one-step state extensions.
          let extSum : ENNReal := ∑ s : State ex, ex.μ (ex.states hist ++ [s])
          have extSum_le_prefix : extSum ≤ ex.μ (ex.states hist) := by
            -- This is exactly the semimeasure property for `μ` at prefix `states hist`.
            simpa [extSum] using ex.semimeasure (ex.states hist)
          have prefix_le_one : ex.μ (ex.states hist) ≤ 1 :=
            ex.μ_le_one (ex.states hist)
          have extSum_le_one : extSum ≤ 1 := extSum_le_prefix.trans prefix_le_one

          -- Swap the (finite) sums over percepts and hypotheses, then bound each hypothesis separately.
          have hswap :
              (∑ x : Percept ex, ∑ h : ex.Hyp,
                    if ex.Consistent h hist ∧ ex.stepConsistent h hist a x then
                      ex.prior h * ex.μ (ex.states hist ++ [ex.stateOfPercept x])
                    else 0) =
                ∑ h : ex.Hyp, ∑ x : Percept ex,
                    if ex.Consistent h hist ∧ ex.stepConsistent h hist a x then
                      ex.prior h * ex.μ (ex.states hist ++ [ex.stateOfPercept x])
                    else 0 := by
            -- Rewrite both sides as a sum over the product `Percept × Hyp`.
            have h1 :
                (∑ x : Percept ex, ∑ h : ex.Hyp,
                      if ex.Consistent h hist ∧ ex.stepConsistent h hist a x then
                        ex.prior h * ex.μ (ex.states hist ++ [ex.stateOfPercept x])
                      else 0) =
                  ∑ p : Percept ex × ex.Hyp,
                      if ex.Consistent p.2 hist ∧ ex.stepConsistent p.2 hist a p.1 then
                        ex.prior p.2 * ex.μ (ex.states hist ++ [ex.stateOfPercept p.1])
                      else 0 := by
              simpa using
                (Fintype.sum_prod_type (f := fun p : Percept ex × ex.Hyp =>
                    if ex.Consistent p.2 hist ∧ ex.stepConsistent p.2 hist a p.1 then
                      ex.prior p.2 * ex.μ (ex.states hist ++ [ex.stateOfPercept p.1])
                    else 0)).symm
            have h2 :
                (∑ h : ex.Hyp, ∑ x : Percept ex,
                      if ex.Consistent h hist ∧ ex.stepConsistent h hist a x then
                        ex.prior h * ex.μ (ex.states hist ++ [ex.stateOfPercept x])
                      else 0) =
                  ∑ p : Percept ex × ex.Hyp,
                      if ex.Consistent p.2 hist ∧ ex.stepConsistent p.2 hist a p.1 then
                        ex.prior p.2 * ex.μ (ex.states hist ++ [ex.stateOfPercept p.1])
                      else 0 := by
              simpa using
                (Fintype.sum_prod_type_right (f := fun p : Percept ex × ex.Hyp =>
                    if ex.Consistent p.2 hist ∧ ex.stepConsistent p.2 hist a p.1 then
                      ex.prior p.2 * ex.μ (ex.states hist ++ [ex.stateOfPercept p.1])
                    else 0)).symm
            calc
              (∑ x : Percept ex, ∑ h : ex.Hyp,
                    if ex.Consistent h hist ∧ ex.stepConsistent h hist a x then
                      ex.prior h * ex.μ (ex.states hist ++ [ex.stateOfPercept x])
                    else 0) =
                  ∑ p : Percept ex × ex.Hyp,
                    if ex.Consistent p.2 hist ∧ ex.stepConsistent p.2 hist a p.1 then
                      ex.prior p.2 * ex.μ (ex.states hist ++ [ex.stateOfPercept p.1])
                    else 0 := h1
              _ =
                  (∑ h : ex.Hyp, ∑ x : Percept ex,
                    if ex.Consistent h hist ∧ ex.stepConsistent h hist a x then
                      ex.prior h * ex.μ (ex.states hist ++ [ex.stateOfPercept x])
                    else 0) := by
                    simpa using h2.symm

          have hinner (h : ex.Hyp) :
              (∑ x : Percept ex,
                    if ex.Consistent h hist ∧ ex.stepConsistent h hist a x then
                      ex.prior h * ex.μ (ex.states hist ++ [ex.stateOfPercept x])
                    else 0) ≤
                ex.prior h * extSum := by
            by_cases hCons : ex.Consistent h hist
            · -- Reduce to the step-consistent sum and factor out the constant `prior h`.
              have hstep :
                  (∑ x : Percept ex,
                        if ex.stepConsistent h hist a x then
                          ex.μ (ex.states hist ++ [ex.stateOfPercept x])
                        else 0) = extSum := by
                simpa [extSum] using (sum_stepConsistent_μ (ex := ex) (h := h) (hist := hist) (a := a))
              -- Factor out `prior h`.
              have hfactor :
                  (∑ x : Percept ex,
                        if ex.stepConsistent h hist a x then
                          ex.prior h * ex.μ (ex.states hist ++ [ex.stateOfPercept x])
                        else 0) =
                    ex.prior h *
                      (∑ x : Percept ex,
                        if ex.stepConsistent h hist a x then
                          ex.μ (ex.states hist ++ [ex.stateOfPercept x])
                        else 0) := by
                classical
                -- Work in `Finset.univ` to use `Finset.mul_sum`.
                change
                  (Finset.univ.sum fun x : Percept ex =>
                      if ex.stepConsistent h hist a x then
                        ex.prior h * ex.μ (ex.states hist ++ [ex.stateOfPercept x])
                      else 0)
                    =
                    ex.prior h *
                      (Finset.univ.sum fun x : Percept ex =>
                        if ex.stepConsistent h hist a x then
                          ex.μ (ex.states hist ++ [ex.stateOfPercept x])
                        else 0)
                -- Rewrite each summand as `prior h * (if step then μ else 0)` and apply `mul_sum`.
                have hrewrite :
                    (fun x : Percept ex =>
                        if ex.stepConsistent h hist a x then
                          ex.prior h * ex.μ (ex.states hist ++ [ex.stateOfPercept x])
                        else 0)
                      =
                    fun x : Percept ex =>
                      ex.prior h * (if ex.stepConsistent h hist a x then
                        ex.μ (ex.states hist ++ [ex.stateOfPercept x])
                      else 0) := by
                  funext x
                  by_cases hx : ex.stepConsistent h hist a x
                  · simp [hx]
                  · simp [hx]
                rw [hrewrite]
                simpa using
                  (Finset.mul_sum (s := (Finset.univ : Finset (Percept ex)))
                    (f := fun x : Percept ex =>
                      if ex.stepConsistent h hist a x then ex.μ (ex.states hist ++ [ex.stateOfPercept x]) else 0)
                    (a := ex.prior h)).symm
              -- Now use `hCons` to drop the consistency guard and finish.
              have :
                  (∑ x : Percept ex,
                        if ex.Consistent h hist ∧ ex.stepConsistent h hist a x then
                          ex.prior h * ex.μ (ex.states hist ++ [ex.stateOfPercept x])
                        else 0) =
                    ex.prior h * extSum := by
                -- With `hCons`, the conjunction reduces to `stepConsistent`.
                have :
                    (∑ x : Percept ex,
                          if ex.stepConsistent h hist a x then
                            ex.prior h * ex.μ (ex.states hist ++ [ex.stateOfPercept x])
                          else 0) =
                      ex.prior h * extSum := by
                  calc
                    (∑ x : Percept ex,
                          if ex.stepConsistent h hist a x then
                            ex.prior h * ex.μ (ex.states hist ++ [ex.stateOfPercept x])
                          else 0) =
                        ex.prior h *
                          (∑ x : Percept ex,
                            if ex.stepConsistent h hist a x then
                              ex.μ (ex.states hist ++ [ex.stateOfPercept x])
                            else 0) := hfactor
                    _ = ex.prior h * extSum := by
                        simpa using congrArg (fun t => ex.prior h * t) hstep
                simpa [hCons] using this
              exact le_of_eq this
            · -- If inconsistent, the sum is 0.
              simp [hCons, extSum]

          have hsum_le :
              (∑ x : Percept ex, probFun hist x) ≤ 1 := by
            -- Start from the definition, swap sums, then apply `hinner` pointwise.
            have hsum_eq :
                (∑ x : Percept ex, probFun hist x) =
                  ∑ h : ex.Hyp, ∑ x : Percept ex,
                    if ex.Consistent h hist ∧ ex.stepConsistent h hist a x then
                      ex.prior h * ex.μ (ex.states hist ++ [ex.stateOfPercept x])
                    else 0 := by
              -- Unfold `probFun` in the `act` case, then swap sums.
              simp [probFun, hlast, hswap]
            -- Apply the per-hypothesis bound and collapse `∑ h prior h * extSum`.
            have hbound :
                (∑ h : ex.Hyp, ∑ x : Percept ex,
                      if ex.Consistent h hist ∧ ex.stepConsistent h hist a x then
                        ex.prior h * ex.μ (ex.states hist ++ [ex.stateOfPercept x])
                      else 0) ≤
                    (∑ h : ex.Hyp, ex.prior h) * extSum := by
              classical
              -- First bound each inner sum by `prior h * extSum`.
              have :
                  (∑ h : ex.Hyp,
                        ∑ x : Percept ex,
                          if ex.Consistent h hist ∧ ex.stepConsistent h hist a x then
                            ex.prior h * ex.μ (ex.states hist ++ [ex.stateOfPercept x])
                          else 0) ≤
                      ∑ h : ex.Hyp, ex.prior h * extSum := by
                refine Finset.sum_le_sum ?_
                intro h _hh
                simpa using hinner h
              -- Now rewrite `∑ h, prior h * extSum` as `(∑ h, prior h) * extSum`.
              have hmul :
                  (∑ h : ex.Hyp, ex.prior h * extSum) = (∑ h : ex.Hyp, ex.prior h) * extSum := by
                classical
                -- `Finset.sum_mul` with `s = univ`.
                simpa using
                  (Finset.sum_mul (s := (Finset.univ : Finset ex.Hyp)) (f := fun h : ex.Hyp => ex.prior h)
                    (a := extSum)).symm
              exact this.trans (by simp [hmul])
            -- Finish with the semimeasure bounds.
            calc
              (∑ x : Percept ex, probFun hist x)
                  ≤ (∑ h : ex.Hyp, ex.prior h) * extSum := by
                        simpa [hsum_eq] using hbound
              _ ≤ 1 * extSum := by
                    exact mul_le_mul_of_nonneg_right ex.prior_sum_le_one (zero_le _)
              _ = extSum := by simp
              _ ≤ 1 := extSum_le_one

          simpa [probFun, hlast] using hsum_le

end SupervisedLearningProblem

/-! ### Theorem 6.5.1 (finite): Optimality in the induced supervised-learning environment

The book's Section 6.5.2 contains information-theoretic efficiency claims (in terms of Kolmogorov
complexity). This development stays in a finite setting and does not model program-length
complexity.

What we *do* formalize is the core decision-theoretic statement: in the induced EX environment,
`V*` upper-bounds the expected number of correct predictions (reward bits) achieved by any policy. -/

namespace SupervisedLearningProblem

theorem value_le_optimalValue_toEnvironment (ex : SupervisedLearningProblem)
    (π : BayesianAgents.Core.Agent ex.V (Percept ex))
    (γ : BayesianAgents.Core.DiscountFactor := ⟨1, by simp, by simp⟩)
    (h : BayesianAgents.Core.History ex.V (Percept ex) := [])
    (n : ℕ := 0) :
    BayesianAgents.Core.value (toEnvironment ex) π γ h n ≤
      BayesianAgents.Core.optimalValue (toEnvironment ex) γ h n := by
  simpa using
    BayesianAgents.Core.value_le_optimalValue
      (μ := toEnvironment ex) (π := π) (γ := γ) (h := h) (n := n)

end SupervisedLearningProblem

/-! ### Comparison: Supervised vs Reinforcement Learning

Supervised learning is much more efficient than reinforcement learning
for the same task:
- Supervised: O(1) cycles to learn R (examples contain information)
- Reinforcement: O(K(R)) cycles (rewards contain limited information)

**Statement** (Hutter 2005, Section 6.5.2):
Information content in examples >> information in rewards.

**Why not formalized**: Information-theoretic comparison requires
formalizing channel capacity of reward vs example signals. -/

/-! ## Section 6.6: Other Aspects of Intelligence

Summary of how various AI concepts fit into the AIXI model:
- Probability theory and utility theory: Heart of AI models
- Reinforcement learning: Explicitly built in via rewards
- Supervised learning: Emergent phenomenon (Section 6.5)
- Planning: Expectimax series for horizon > 1
- Minimax: Special case for zero-sum games
- Knowledge: Accumulated on work tape
-/

/-! ### AIXI Incorporates Core AI Methods

The AIXI model incorporates the core components of AI:
- Decision theory (utility maximization)
- Probability theory (Bayesian beliefs)
- Algorithmic information theory (Solomonoff prior)
- Reinforcement learning (reward signals)
- Planning (expectimax lookahead)

(Hutter 2005, Section 6.6) -/

/-! ## Chapter 6 Summary

### Main Result (finite): Optimality specializes across embeddings

Each problem class (SP, SG, FM, EX) can be embedded in the AIXI framework,
and AIXI's behavior specializes to the optimal solution for that class.

**What IS formalized in this file**:
- `SequencePredictionProblem` structure with semimeasure property
- `SequencePredictionProblem.μ_le_one`: prefix probabilities are bounded
- `spToEnvironment`: embedding SP into the Environment type
- `aimu_eq_spμ`: Theorem 6.2.1 (AIμ = SPμ) in the induced SP environment
- `StrategicGameProblem` structure with minimax definitions
- `sgToEnvironment`: embedding SG into the Environment type
- `aimu_eq_minimax`: Theorem 6.3.1 (AIμ = minimax) in the induced SG environment
- `FunctionMinimizationProblem` structure with weight models
- `FunctionMinimizationProblem.optimalExpectedCost_le_expectedCost`: optimal FM cost lower bound
- `SupervisedLearningProblem` structure
- `SupervisedLearningProblem.value_le_optimalValue_toEnvironment`: optimality bound for EX value

**Not covered here**:
- Information-theoretic/Kolmogorov complexity efficiency bounds
- Convergence results for AIξ / AIXI as priors/horizons vary

### Corollary: Unified Foundation

Instead of developing specialized algorithms for each problem class,
AIXI provides a universal algorithm that automatically specializes
to the optimal solution for any given problem structure.

The computational limitations are addressed in Chapter 7 (TimeBoundedAIXI.lean),
which introduces AIXItl as a computable approximation.

(Hutter 2005, Chapter 6 conclusion) -/

end Mettapedia.UniversalAI.ProblemClasses
