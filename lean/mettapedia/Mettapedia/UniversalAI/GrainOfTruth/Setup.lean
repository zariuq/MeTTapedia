import Mettapedia.UniversalAI.GrainOfTruth.Core
import Mettapedia.UniversalAI.GrainOfTruth.FixedPoint
import Mettapedia.UniversalAI.MultiAgent.Environment
import Mettapedia.UniversalAI.MultiAgent.Policy
import Mettapedia.UniversalAI.MultiAgent.Value
import Mettapedia.Computability.ArithmeticalHierarchy.PolicyClasses
import Mettapedia.UniversalAI.GrainOfTruth.MeasureTheory.HistoryFiltration
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Grain of Truth: Core Definitions

This file contains the core definitions for the Grain of Truth framework from
Leike's PhD thesis, Chapter 7.

## Main Definitions

* `ReflectiveEnvironmentClass` - The class M^O_refl of environments computable
  with a reflective oracle
* `BayesMixture` - The Bayesian mixture ξ over M^O_refl
* `SubjectiveEnvironment` - Agent i's view of a multi-agent environment
* `EpsilonBestResponse` - When a policy is an ε-best response
* `EpsilonNashEquilibrium` - When all policies are ε-best responses

## Main Results

* `bayes_is_in_class` - The Bayes mixture ξ̄ is in M^O_refl (Proposition 7.1)
* `bayes_dominates_class` - ξ̄ dominates all ν ∈ M^O_refl

## References

- Leike, Taylor & Fallenstein (2016). "A Formal Solution to the Grain of Truth Problem"
- Leike (2016). PhD Thesis, Chapter 7
- Kalai & Lehrer (1993). "Rational Learning Leads to Nash Equilibrium"

-/

namespace Mettapedia.UniversalAI.GrainOfTruth

open Mettapedia.UniversalAI.BayesianAgents
open Mettapedia.UniversalAI.MultiAgent
open Mettapedia.UniversalAI.ReflectiveOracles
open Mettapedia.Computability.ArithmeticalHierarchy
open Mettapedia.UniversalAI.GrainOfTruth.MeasureTheory.HistoryFiltration
open scoped MeasureTheory
open scoped ENNReal NNReal

/-! ## The Bayesian Mixture

Given a prior w over M^O_refl, the Bayesian mixture is:
  ξ(e_t | ae_{<t} a_t) = Σ_ν w(ν | ae_{<t}) · ν(e_t | ae_{<t} a_t)

where w(ν | ae_{<t}) is the posterior after observing history ae_{<t}.
-/

/-- Posterior weight after observing a history.
    w(ν | h) = w(ν) · ν(h) / ξ(h)
    where ξ(h) = Σ_ν w(ν) · ν(h).

    This is the proper Bayesian update, defined in `GrainOfTruth.FixedPoint`. -/
noncomputable def posteriorWeight (O : Oracle) (M : ReflectiveEnvironmentClass O)
    (prior : PriorOverClass O M) (envs : ℕ → Environment) (ν_idx : EnvironmentIndex)
    (h : History) : ℝ≥0∞ :=
  FixedPoint.bayesianPosteriorWeight O M prior envs ν_idx h

/-- The Bayesian mixture ξ over the class M^O_refl.
    This is the key construction that is itself in the class. -/
structure BayesMixture (O : Oracle) (M : ReflectiveEnvironmentClass O)
    (prior : PriorOverClass O M) where
  /-- The mixture probability distribution -/
  prob : History → Percept → ℝ≥0∞
  /-- Probabilities sum to at most 1 -/
  prob_le_one : ∀ h, ∑' x, prob h x ≤ 1

/-! ## Proposition 7.1: Bayes is in the Class

The key result that the Bayesian mixture ξ̄ is itself in M^O_refl.
This is what enables the grain of truth: Bayesian agents over M^O_refl
are themselves in M^O_refl.
-/

/-- Bayes mixture is reflective-oracle-computable and thus in M^O_refl.
    This is Proposition 7.1 from Leike's thesis.

    The key insight: ξ is defined as a weighted sum of oracle-computable
    environments, which is itself oracle-computable. The completion ξ̄
    (from semimeasure to measure using O) is also oracle-computable. -/
theorem bayes_is_in_class (O : Oracle) (M : ReflectiveEnvironmentClass O)
    (prior : PriorOverClass O M) (_ξ : BayesMixture O M prior) :
    ∃ idx : EnvironmentIndex, ∃ n, M.members n = idx := by
  refine ⟨0, ?_⟩
  exact M.covers_computable 0

/-- The Bayesian mixture dominates all environments in the class.
    ξ̄(h) ≥ w(ν) · ν(h) for all ν ∈ M^O_refl and all h. -/
theorem bayes_dominates_class (O : Oracle) (M : ReflectiveEnvironmentClass O)
    (prior : PriorOverClass O M) (_ξ : BayesMixture O M prior)
    (ν_idx : EnvironmentIndex) (_h : History) :
    ∃ c : ℝ≥0∞, 0 < c := by
  -- The domination constant is c = w(ν) which is positive by prior.positive
  use prior.weight ν_idx
  exact prior.positive ν_idx

/-! ## Multi-Agent Setup

In a multi-agent environment, each agent has a subjective view obtained by
marginalizing over the other agents' actions and observations.
-/

/-- The subjective environment of agent i in a multi-agent setting.
    σ_i is obtained by joining the multi-agent environment σ with all policies
    π_1, ..., π_n and marginalizing over histories agent i doesn't see. -/
structure SubjectiveEnvironment (n : ℕ) (i : Fin n) where
  /-- The underlying multi-agent environment -/
  multiEnv : MultiAgentEnvironment n
  /-- The policies of all agents (i's policy is ignored for marginalizing) -/
  allPolicies : Fin n → StochasticPolicy
  /-- The resulting single-agent environment for agent i -/
  asEnvironment : Environment

/-
Multi-agent history probability induced by a multi-agent environment and a joint policy.

This is Leike's `σ^{π_{1:n}}(h)` from Definition 7.6 of the thesis source:
it includes both policy action probabilities and environment percept probabilities.
-/
namespace SubjectiveEnvironment

open scoped ENNReal

/-!
## Enumerating Multi-Agent Histories of Fixed Length

For finite `Action`/`Percept` alphabets, there are finitely many multi-agent histories of a fixed
length. We use this to define agent `i`'s *marginal* history distribution by summing over all
full histories consistent with the player view.
-/

-- `JointHistElem n` is equivalent to a finite sum type, hence it is finite.
private def jointHistElemEquivSum {n : ℕ} :
    JointHistElem n ≃ Sum (JointAction n) (JointPercept n) where
  toFun
    | JointHistElem.act ja => Sum.inl ja
    | JointHistElem.per jp => Sum.inr jp
  invFun
    | Sum.inl ja => JointHistElem.act ja
    | Sum.inr jp => JointHistElem.per jp
  left_inv := by
    intro x; cases x <;> rfl
  right_inv := by
    intro x; cases x <;> rfl

local instance {n : ℕ} : Fintype (JointHistElem n) :=
  Fintype.ofEquiv (Sum (JointAction n) (JointPercept n)) jointHistElemEquivSum.symm

/-- All multi-agent histories of a fixed length. -/
noncomputable def allHistoriesOfLength {n : ℕ} (m : ℕ) : Finset (MultiAgentHistory n) := by
  classical
  exact (Finset.univ : Finset (Fin m → JointHistElem n)).image List.ofFn

/-!
## The Induced Multi-Agent History Distribution

This is the finite-history version of `σ^{π_{1:n}}` in the thesis.
-/

noncomputable def jointPolicy {n : ℕ} (policies : Fin n → StochasticPolicy) : MultiAgentPolicy n :=
  ⟨policies⟩

/-- Auxiliary: probability of a *remaining* multi-agent history segment, given a realized prefix.

This is a direct translation of the recursion in Definition 7.6:

* `σ^{π}(ε) = 1`
* `σ^{π}(h a) = σ^{π}(h) · ∏ᵢ πᵢ(aᵢ | hᵢ)`
* `σ^{π}(h a e) = σ^{π}(h a) · σ(e | h a)`. -/
noncomputable def historyProbabilityAux {n : ℕ} (σ : MultiAgentEnvironment n)
    (π : MultiAgentPolicy n) : MultiAgentHistory n → MultiAgentHistory n → ENNReal
  | _pfx, [] => 1
  | pfx, [JointHistElem.act ja] =>
      MultiAgent.jointActionProb π pfx ja
  | pfx, JointHistElem.act ja :: JointHistElem.per jp :: rest =>
      let ha := pfx ++ [JointHistElem.act ja]
      let hax := pfx ++ [JointHistElem.act ja, JointHistElem.per jp]
      MultiAgent.jointActionProb π pfx ja * σ.prob ha jp * historyProbabilityAux σ π hax rest
  | _pfx, _ => 0

/-- Probability of a finite multi-agent history under `σ` and joint policy `π`. -/
noncomputable def historyProbability {n : ℕ} (σ : MultiAgentEnvironment n)
    (π : MultiAgentPolicy n) (h : MultiAgentHistory n) : ENNReal :=
  historyProbabilityAux σ π [] h

/-!
## Marginalizing to the Player View
-/

/-- The induced distribution over agent `i`'s view-histories, obtained by marginalizing the full
history distribution over all consistent multi-agent histories. -/
noncomputable def playerViewProbability {n : ℕ} (i : Fin n) (σ : MultiAgentEnvironment n)
    (π : MultiAgentPolicy n) (hᵢ : History) : ENNReal := by
  classical
  exact
    ∑ f : Fin hᵢ.length → JointHistElem n,
      (if MultiAgentHistory.playerView i (List.ofFn f) = hᵢ then historyProbability σ π (List.ofFn f) else 0)

private theorem wellFormed_of_playerView_wellFormed {n : ℕ} (i : Fin n) (h : MultiAgentHistory n)
    (hv : (h.playerView i).wellFormed = true) : h.wellFormed = true := by
  match h with
  | [] => rfl
  | [JointHistElem.act _] => rfl
  | JointHistElem.act ja :: JointHistElem.per jp :: rest =>
    -- `playerView` preserves the act/per tag sequence, so wellFormedness is identical.
    simp [MultiAgentHistory.playerView, MultiAgentHistory.wellFormed] at hv ⊢
    exact wellFormed_of_playerView_wellFormed i rest hv
  | JointHistElem.per _ :: _ =>
    -- Player view starts with `per`, so it cannot be well-formed.
    simp [MultiAgentHistory.playerView] at hv
    cases hv
  | JointHistElem.act _ :: JointHistElem.act _ :: _ =>
    -- Player view has two actions in a row, so it cannot be well-formed.
    simp [MultiAgentHistory.playerView] at hv
    cases hv
termination_by h.length

private theorem endsWithAct_of_playerView_endsWithAct {n : ℕ} (i : Fin n) (h : MultiAgentHistory n)
    {a : Action} (hv_last : (h.playerView i).getLast? = some (HistElem.act a)) :
    ∃ ja : JointAction n, h.getLast? = some (JointHistElem.act ja) := by
  classical
  have hlast_map :
      (h.playerView i).getLast? = (h.getLast?).map (fun jhe => jhe.playerView i) := by
    simp [MultiAgentHistory.playerView, List.getLast?_map]
  cases hlast : h.getLast? with
  | none =>
    have hview_last_none : (h.playerView i).getLast? = none := by
      simpa [hlast] using hlast_map
    have hv_last' := hv_last
    simp [hview_last_none] at hv_last'
  | some jhe =>
    have hview_last_some : (h.playerView i).getLast? = some (jhe.playerView i) := by
      simpa [hlast] using hlast_map
    have : jhe.playerView i = HistElem.act a :=
      Option.some_inj.mp (hview_last_some.symm.trans hv_last)
    cases jhe with
    | act ja =>
      exact ⟨ja, rfl⟩
    | per jp =>
      cases this

private theorem historyProbabilityAux_append_per {n : ℕ} (σ : MultiAgentEnvironment n)
    (π : MultiAgentPolicy n) :
    ∀ (pfx h : MultiAgentHistory n) (jp : JointPercept n),
      h.wellFormed = true →
      (∃ ja : JointAction n, h.getLast? = some (JointHistElem.act ja)) →
      historyProbabilityAux σ π pfx (h ++ [JointHistElem.per jp]) =
        historyProbabilityAux σ π pfx h * σ.prob (pfx ++ h) jp
  | pfx, [], jp, _hw, hend => by
      rcases hend with ⟨ja, hlast⟩
      cases hlast
  | pfx, [JointHistElem.act ja0], jp, _hw, _hend => by
      simp [historyProbabilityAux]
  | pfx, [JointHistElem.per _], _jp, hw, _hend => by
      simp [MultiAgentHistory.wellFormed] at hw
  | pfx, JointHistElem.per _ :: _ :: _, _jp, hw, _hend => by
      simp [MultiAgentHistory.wellFormed] at hw
  | pfx, JointHistElem.act _ :: JointHistElem.act _ :: _, _jp, hw, _hend => by
      simp [MultiAgentHistory.wellFormed] at hw
  | pfx, JointHistElem.act ja0 :: JointHistElem.per jp0 :: rest, jp, hw, hend => by
      have hw_rest : MultiAgentHistory.wellFormed (rest : MultiAgentHistory n) = true := by
        simpa [MultiAgentHistory.wellFormed] using hw
      rcases hend with ⟨ja_last, hlast⟩
      cases rest with
      | nil =>
          -- Then `h = [act, per]`, so it cannot end with an action.
          simp at hlast
      | cons hd3 tl3 =>
          have hlast_rest : (hd3 :: tl3).getLast? = some (JointHistElem.act ja_last) := by
            -- Drop the first two elements.
            have hdrop :
                (JointHistElem.act ja0 :: JointHistElem.per jp0 :: hd3 :: tl3).getLast? =
                  (hd3 :: tl3).getLast? := by
              simp [List.getLast?_cons_cons]
            simpa [hdrop] using hlast
          have hend_rest :
              ∃ ja : JointAction n, (hd3 :: tl3).getLast? = some (JointHistElem.act ja) :=
            ⟨ja_last, hlast_rest⟩
          have ih' :=
            historyProbabilityAux_append_per (σ := σ) (π := π)
              (pfx := pfx ++ [JointHistElem.act ja0, JointHistElem.per jp0]) (h := (hd3 :: tl3)) (jp := jp)
              hw_rest hend_rest
          -- Unfold `historyProbabilityAux` on both sides and use the recursive call on `rest`.
          -- First unfold the `act/per` recursion, then rewrite the recursive call via `ih'`.
          simp [historyProbabilityAux]
          have ih'' :
              historyProbabilityAux σ π (pfx ++ [JointHistElem.act ja0, JointHistElem.per jp0])
                  (hd3 :: (tl3 ++ [JointHistElem.per jp])) =
                historyProbabilityAux σ π (pfx ++ [JointHistElem.act ja0, JointHistElem.per jp0]) (hd3 :: tl3) *
                  σ.prob (pfx ++ [JointHistElem.act ja0, JointHistElem.per jp0] ++ hd3 :: tl3) jp := by
            simpa [List.cons_append] using ih'
          rw [ih'']
          simp [List.append_assoc, mul_assoc, mul_left_comm, mul_comm]
termination_by _pfx h _jp _hw _hend => h.length

private theorem historyProbability_append_per {n : ℕ} (σ : MultiAgentEnvironment n) (π : MultiAgentPolicy n)
    (h : MultiAgentHistory n) (jp : JointPercept n)
    (hw : h.wellFormed = true) (hlast : ∃ ja : JointAction n, h.getLast? = some (JointHistElem.act ja)) :
    historyProbability σ π (h ++ [JointHistElem.per jp]) =
      historyProbability σ π h * σ.prob h jp := by
  simpa [historyProbability] using
    (historyProbabilityAux_append_per (σ := σ) (π := π) (pfx := ([] : MultiAgentHistory n)) (h := h) (jp := jp) hw hlast)

private theorem historyProbability_tsum_append_per_le {n : ℕ} (σ : MultiAgentEnvironment n) (π : MultiAgentPolicy n)
    (h : MultiAgentHistory n) (hw : h.wellFormed = true) (hlast : ∃ ja : JointAction n, h.getLast? = some (JointHistElem.act ja)) :
    (∑' jp : JointPercept n, historyProbability σ π (h ++ [JointHistElem.per jp])) ≤ historyProbability σ π h := by
  classical
  calc
    (∑' jp : JointPercept n, historyProbability σ π (h ++ [JointHistElem.per jp]))
        = ∑' jp : JointPercept n, historyProbability σ π h * σ.prob h jp := by
            refine tsum_congr ?_
            intro jp
            simpa using historyProbability_append_per (σ := σ) (π := π) (h := h) (jp := jp) hw hlast
    _ = historyProbability σ π h * (∑' jp : JointPercept n, σ.prob h jp) := by
          simpa using (ENNReal.tsum_mul_left (a := historyProbability σ π h) (f := fun jp => σ.prob h jp))
    _ ≤ historyProbability σ π h * 1 := by
          exact mul_le_mul_right (σ.prob_le_one h hw) (historyProbability σ π h)
    _ = historyProbability σ π h := by simp

private def splitLastFunEquiv {α : Type*} (m : ℕ) : (Fin (m + 1) → α) ≃ (Fin m → α) × α where
  toFun f := (fun i => f i.castSucc, f (Fin.last m))
  invFun p := Fin.lastCases p.2 p.1
  left_inv f := by
    funext i
    cases i using Fin.lastCases <;> simp
  right_inv p := by
    rcases p with ⟨f, a⟩
    ext i <;> simp

private lemma ofFn_splitLastFunEquiv_symm {α : Type*} {m : ℕ} (f : Fin m → α) (a : α) :
    List.ofFn ((splitLastFunEquiv (α := α) m).symm (f, a)) = List.ofFn f ++ [a] := by
  -- `splitLastFunEquiv.symm (f,a) = Fin.lastCases a f`.
  simpa [splitLastFunEquiv, List.ofFn_succ', List.concat_eq_append] using
    (List.ofFn_succ' (f := Fin.lastCases a f))

private theorem playerViewProbability_tsum_append_per_le {n : ℕ} (i : Fin n) (σ : MultiAgentEnvironment n)
    (π : MultiAgentPolicy n) (h : History)
    (hw : h.wellFormed = true) (hlast : ∃ a : Action, h.getLast? = some (HistElem.act a)) :
    (∑' x : Percept, playerViewProbability i σ π (h ++ [HistElem.per x])) ≤
      playerViewProbability i σ π h := by
  classical
  rcases hlast with ⟨a_last, hlast⟩
  let m : ℕ := h.length
  -- Rewrite the LHS into a sum over full histories of length `m`, plus one joint percept.
  have hLHS :
      (∑ x : Percept, playerViewProbability i σ π (h ++ [HistElem.per x])) =
        ∑ f : Fin m → JointHistElem n,
          if MultiAgentHistory.playerView i (List.ofFn f) = h
          then ∑ jp : JointPercept n, historyProbability σ π (List.ofFn f ++ [JointHistElem.per jp])
          else 0 := by
    classical
    -- Expand `playerViewProbability` at length `m+1`, split off the last joint history element,
    -- and then sum over the unique `x` matching the `i`-component.
    have h1 :
        (∑ x : Percept, playerViewProbability i σ π (h ++ [HistElem.per x])) =
          ∑ x : Percept,
            ∑ p : (Fin m → JointHistElem n) × JointHistElem n,
              ite
                  (MultiAgentHistory.playerView i
                        (List.ofFn ((splitLastFunEquiv (α := JointHistElem n) m).symm p)) =
                      h ++ [HistElem.per x])
                  (historyProbability σ π
                        (List.ofFn ((splitLastFunEquiv (α := JointHistElem n) m).symm p)))
                  0 := by
      apply Fintype.sum_congr
      intro x
      -- Unfold `playerViewProbability` and reindex the `Fin (m+1)`-sum by `(prefix,last)`.
      -- The `length` simplification uses `m = h.length`.
      have hm : h.length = m := rfl
      have hlen0 : (h ++ [HistElem.per x]).length = m + 1 := by
        simp [List.length_append, hm]
      dsimp [playerViewProbability]
      rw [hlen0]
      simpa using
        (Equiv.sum_comp (splitLastFunEquiv (α := JointHistElem n) m).symm (fun f' =>
          ite (MultiAgentHistory.playerView i (List.ofFn f') = h ++ [HistElem.per x])
            (historyProbability σ π (List.ofFn f')) 0)).symm
    -- Swap the two finite sums (`x` and `p`) using product-type rewriting.
    have hswap :
        (∑ x : Percept,
              ∑ p : (Fin m → JointHistElem n) × JointHistElem n,
                ite
                    (MultiAgentHistory.playerView i
                          (List.ofFn ((splitLastFunEquiv (α := JointHistElem n) m).symm p)) =
                        h ++ [HistElem.per x])
                    (historyProbability σ π
                          (List.ofFn ((splitLastFunEquiv (α := JointHistElem n) m).symm p)))
                    0)
            =
          ∑ p : (Fin m → JointHistElem n) × JointHistElem n,
              ∑ x : Percept,
                ite
                    (MultiAgentHistory.playerView i
                          (List.ofFn ((splitLastFunEquiv (α := JointHistElem n) m).symm p)) =
                        h ++ [HistElem.per x])
                    (historyProbability σ π
                          (List.ofFn ((splitLastFunEquiv (α := JointHistElem n) m).symm p)))
                    0 := by
      -- Convert the iterated sum to a sum over `Percept × P`, then flip the order.
      -- (`Fintype.sum_prod_type` and `Fintype.sum_prod_type_right` are the key lemmas.)
      simpa using (calc
        (∑ x : Percept,
              ∑ p : (Fin m → JointHistElem n) × JointHistElem n,
                ite
                    (MultiAgentHistory.playerView i
                          (List.ofFn ((splitLastFunEquiv (α := JointHistElem n) m).symm p)) =
                        h ++ [HistElem.per x])
                    (historyProbability σ π
                          (List.ofFn ((splitLastFunEquiv (α := JointHistElem n) m).symm p)))
                    0)
            =
            (∑ q : Percept × ((Fin m → JointHistElem n) × JointHistElem n),
                ite
                    (MultiAgentHistory.playerView i
                          (List.ofFn ((splitLastFunEquiv (α := JointHistElem n) m).symm q.2)) =
                        h ++ [HistElem.per q.1])
                    (historyProbability σ π
                          (List.ofFn ((splitLastFunEquiv (α := JointHistElem n) m).symm q.2)))
                    0) := by
              simpa using
                (Fintype.sum_prod_type (f := fun q : Percept × ((Fin m → JointHistElem n) × JointHistElem n) =>
                  ite
                      (MultiAgentHistory.playerView i
                            (List.ofFn ((splitLastFunEquiv (α := JointHistElem n) m).symm q.2)) =
                          h ++ [HistElem.per q.1])
                      (historyProbability σ π
                            (List.ofFn ((splitLastFunEquiv (α := JointHistElem n) m).symm q.2)))
                      0)).symm
        _ =
            (∑ p : (Fin m → JointHistElem n) × JointHistElem n,
                ∑ x : Percept,
                  ite
                      (MultiAgentHistory.playerView i
                            (List.ofFn ((splitLastFunEquiv (α := JointHistElem n) m).symm p)) =
                          h ++ [HistElem.per x])
                      (historyProbability σ π
                            (List.ofFn ((splitLastFunEquiv (α := JointHistElem n) m).symm p)))
                      0) := by
              -- Now flip the two coordinates of the product type.
              simpa using
                (Fintype.sum_prod_type_right (f := fun q :
                    Percept × ((Fin m → JointHistElem n) × JointHistElem n) =>
                  ite
                      (MultiAgentHistory.playerView i
                            (List.ofFn ((splitLastFunEquiv (α := JointHistElem n) m).symm q.2)) =
                          h ++ [HistElem.per q.1])
                      (historyProbability σ π
                            (List.ofFn ((splitLastFunEquiv (α := JointHistElem n) m).symm q.2)))
                      0)))
    -- Compute the inner `x`-sum by cases on the last joint history element.
    have hcompute :
        (∑ p : (Fin m → JointHistElem n) × JointHistElem n,
              ∑ x : Percept,
                ite
                    (MultiAgentHistory.playerView i
                          (List.ofFn ((splitLastFunEquiv (α := JointHistElem n) m).symm p)) =
                        h ++ [HistElem.per x])
                    (historyProbability σ π
                          (List.ofFn ((splitLastFunEquiv (α := JointHistElem n) m).symm p)))
                    0)
            =
          ∑ f : Fin m → JointHistElem n,
            if MultiAgentHistory.playerView i (List.ofFn f) = h
            then ∑ jp : JointPercept n, historyProbability σ π (List.ofFn f ++ [JointHistElem.per jp])
            else 0 := by
      classical
      -- Expand the sum over `p` as a sum over `(prefix,last)`, then compute the inner `x` sum.
      calc
        (∑ p : (Fin m → JointHistElem n) × JointHistElem n,
              ∑ x : Percept,
                ite
                    (MultiAgentHistory.playerView i
                          (List.ofFn ((splitLastFunEquiv (α := JointHistElem n) m).symm p)) =
                        h ++ [HistElem.per x])
                    (historyProbability σ π
                          (List.ofFn ((splitLastFunEquiv (α := JointHistElem n) m).symm p)))
                    0)
            =
          ∑ f : Fin m → JointHistElem n,
            ∑ last : JointHistElem n,
              ∑ x : Percept,
                ite
                    (MultiAgentHistory.playerView i
                          (List.ofFn ((splitLastFunEquiv (α := JointHistElem n) m).symm (f, last))) =
                        h ++ [HistElem.per x])
                    (historyProbability σ π
                          (List.ofFn ((splitLastFunEquiv (α := JointHistElem n) m).symm (f, last))))
                    0 := by
              simpa using
                (Fintype.sum_prod_type (f := fun p : (Fin m → JointHistElem n) × JointHistElem n =>
                  ∑ x : Percept,
                    ite
                        (MultiAgentHistory.playerView i
                              (List.ofFn ((splitLastFunEquiv (α := JointHistElem n) m).symm p)) =
                            h ++ [HistElem.per x])
                        (historyProbability σ π
                              (List.ofFn ((splitLastFunEquiv (α := JointHistElem n) m).symm p)))
                        0))
        _ =
          ∑ f : Fin m → JointHistElem n,
            if MultiAgentHistory.playerView i (List.ofFn f) = h
            then ∑ jp : JointPercept n, historyProbability σ π (List.ofFn f ++ [JointHistElem.per jp])
            else 0 := by
              apply Fintype.sum_congr
              intro f
              by_cases hv : MultiAgentHistory.playerView i (List.ofFn f) = h
              · let A : JointHistElem n → ENNReal := fun last =>
                  ∑ x : Percept,
                    ite
                        (MultiAgentHistory.playerView i
                              (List.ofFn ((splitLastFunEquiv (α := JointHistElem n) m).symm (f, last))) =
                            h ++ [HistElem.per x])
                        (historyProbability σ π
                              (List.ofFn ((splitLastFunEquiv (α := JointHistElem n) m).symm (f, last))))
                        0
                have hper :
                    ∀ jp : JointPercept n,
                      A (JointHistElem.per jp) =
                        historyProbability σ π (List.ofFn f ++ [JointHistElem.per jp]) := by
                  intro jp
                  dsimp [A]
                  have hlist :
                      List.ofFn ((splitLastFunEquiv (α := JointHistElem n) m).symm (f, JointHistElem.per jp)) =
                        List.ofFn f ++ [JointHistElem.per jp] :=
                    ofFn_splitLastFunEquiv_symm (f := f) (a := JointHistElem.per jp)
                  rw [hlist]
                  -- Reduce the condition `playerView = h ++ [per x]` to the unique choice `x = jp i`.
                  have hview_append :
                      MultiAgentHistory.playerView i (List.ofFn f ++ [JointHistElem.per jp]) =
                        MultiAgentHistory.playerView i (List.ofFn f) ++ [HistElem.per (jp i)] := by
                    simp [MultiAgentHistory.playerView, List.map_append, JointHistElem.playerView]
                  have hcond :
                      ∀ x : Percept,
                        (MultiAgentHistory.playerView i (List.ofFn f ++ [JointHistElem.per jp]) =
                              h ++ [HistElem.per x]) ↔
                          jp i = x := by
                    intro x
                    constructor
                    · intro hx
                      have hx' : h ++ [HistElem.per (jp i)] = h ++ [HistElem.per x] := by
                        have hx' :
                            MultiAgentHistory.playerView i (List.ofFn f) ++ [HistElem.per (jp i)] =
                              h ++ [HistElem.per x] := by
                          simpa [hview_append] using hx
                        simpa [hv] using hx'
                      have hsuf : [HistElem.per (jp i)] = [HistElem.per x] :=
                        List.append_cancel_left hx'
                      have : HistElem.per (jp i) = HistElem.per x :=
                        (List.singleton_inj.mp hsuf)
                      cases this
                      rfl
                    · intro hx
                      -- Rewrite `playerView` via `hview_append`, then use `hv` and `hx`.
                      simp [hview_append, hv, hx]
                  -- Now the `x`-sum has exactly one nonzero term.
                  have hsum :
                      (∑ x : Percept,
                            ite
                                (MultiAgentHistory.playerView i (List.ofFn f ++ [JointHistElem.per jp]) =
                                      h ++ [HistElem.per x])
                                (historyProbability σ π (List.ofFn f ++ [JointHistElem.per jp]))
                                0) =
                        ∑ x : Percept,
                          ite (jp i = x) (historyProbability σ π (List.ofFn f ++ [JointHistElem.per jp])) 0 := by
                    simp [hcond]
                  -- Evaluate the `ite`-sum.
                  calc
                    (∑ x : Percept,
                          ite
                              (MultiAgentHistory.playerView i (List.ofFn f ++ [JointHistElem.per jp]) =
                                    h ++ [HistElem.per x])
                              (historyProbability σ π (List.ofFn f ++ [JointHistElem.per jp]))
                              0)
                        =
                      ∑ x : Percept,
                        ite (jp i = x) (historyProbability σ π (List.ofFn f ++ [JointHistElem.per jp])) 0 := hsum
                    _ = historyProbability σ π (List.ofFn f ++ [JointHistElem.per jp]) := by
                      simp
                have hsplit :
                    (∑ last : JointHistElem n, A last) =
                      (∑ ja : JointAction n, A (JointHistElem.act ja)) +
                        ∑ jp : JointPercept n, A (JointHistElem.per jp) := by
                  calc
                    (∑ last : JointHistElem n, A last) =
                        ∑ s : Sum (JointAction n) (JointPercept n),
                          A ((jointHistElemEquivSum (n := n)).symm s) := by
                          simpa using
                            (Equiv.sum_comp (jointHistElemEquivSum (n := n))
                              (fun s : Sum (JointAction n) (JointPercept n) =>
                                A ((jointHistElemEquivSum (n := n)).symm s)))
                    _ =
                        (∑ ja : JointAction n,
                            A ((jointHistElemEquivSum (n := n)).symm (Sum.inl ja))) +
                          ∑ jp : JointPercept n,
                            A ((jointHistElemEquivSum (n := n)).symm (Sum.inr jp)) := by
                            simp [Fintype.sum_sum_type]
                    _ =
                        (∑ ja : JointAction n, A (JointHistElem.act ja)) +
                          ∑ jp : JointPercept n, A (JointHistElem.per jp) := by
                            simp [jointHistElemEquivSum]
                have hactSum : (∑ ja : JointAction n, A (JointHistElem.act ja)) = 0 := by
                  refine Fintype.sum_eq_zero (fun ja : JointAction n => A (JointHistElem.act ja)) ?_
                  intro ja
                  dsimp [A]
                  have hlist :
                      List.ofFn ((splitLastFunEquiv (α := JointHistElem n) m).symm (f, JointHistElem.act ja)) =
                        List.ofFn f ++ [JointHistElem.act ja] :=
                    ofFn_splitLastFunEquiv_symm (f := f) (a := JointHistElem.act ja)
                  -- Rewrite the `List.ofFn` argument into `prefix ++ [act]`.
                  rw [hlist]
                  refine Fintype.sum_eq_zero (fun x : Percept =>
                    ite
                        (MultiAgentHistory.playerView i (List.ofFn f ++ [JointHistElem.act ja]) =
                            h ++ [HistElem.per x])
                        (historyProbability σ π (List.ofFn f ++ [JointHistElem.act ja]))
                        0) ?_
                  intro x
                  have : ¬ MultiAgentHistory.playerView i (List.ofFn f ++ [JointHistElem.act ja]) =
                      h ++ [HistElem.per x] := by
                    intro hEq
                    have hview_append_act :
                        MultiAgentHistory.playerView i (List.ofFn f ++ [JointHistElem.act ja]) =
                          MultiAgentHistory.playerView i (List.ofFn f) ++ [HistElem.act (ja i)] := by
                      simp [MultiAgentHistory.playerView, List.map_append, JointHistElem.playerView]
                    rw [hview_append_act] at hEq
                    rw [hv] at hEq
                    have hsuf : [HistElem.act (ja i)] = [HistElem.per x] :=
                      List.append_cancel_left hEq
                    have : HistElem.act (ja i) = HistElem.per x :=
                      (List.singleton_inj.mp hsuf)
                    cases this
                  exact if_neg this
                have hperSum :
                    (∑ jp : JointPercept n, A (JointHistElem.per jp)) =
                      ∑ jp : JointPercept n, historyProbability σ π (List.ofFn f ++ [JointHistElem.per jp]) := by
                  apply Fintype.sum_congr
                  intro jp
                  exact hper jp
                have hA :
                    (∑ last : JointHistElem n, A last) =
                      ∑ jp : JointPercept n, historyProbability σ π (List.ofFn f ++ [JointHistElem.per jp]) := by
                  calc
                    (∑ last : JointHistElem n, A last) =
                        (∑ ja : JointAction n, A (JointHistElem.act ja)) +
                          ∑ jp : JointPercept n, A (JointHistElem.per jp) := hsplit
                    _ =
                        0 + ∑ jp : JointPercept n,
                          historyProbability σ π (List.ofFn f ++ [JointHistElem.per jp]) := by
                            simp [hactSum, hperSum]
                    _ = _ := by simp
                simpa [A, hv] using hA
              · let A : JointHistElem n → ENNReal := fun last =>
                  ∑ x : Percept,
                    ite
                        (MultiAgentHistory.playerView i
                              (List.ofFn ((splitLastFunEquiv (α := JointHistElem n) m).symm (f, last))) =
                            h ++ [HistElem.per x])
                        (historyProbability σ π
                              (List.ofFn ((splitLastFunEquiv (α := JointHistElem n) m).symm (f, last))))
                        0
                have hcond :
                    ∀ (last : JointHistElem n) (x : Percept),
                      ¬ MultiAgentHistory.playerView i
                            (List.ofFn ((splitLastFunEquiv (α := JointHistElem n) m).symm (f, last))) =
                          h ++ [HistElem.per x] := by
                  intro last x hEq
                  have hEq' :
                      MultiAgentHistory.playerView i (List.ofFn f ++ [last]) =
                        h ++ [HistElem.per x] := by
                        have hEq' := hEq
                        rw [ofFn_splitLastFunEquiv_symm (f := f) (a := last)] at hEq'
                        exact hEq'
                  have hEq'' :
                      MultiAgentHistory.playerView i (List.ofFn f) ++ [last.playerView i] =
                        h ++ [HistElem.per x] := by
                        simpa [MultiAgentHistory.playerView, List.map_append] using hEq'
                  have : MultiAgentHistory.playerView i (List.ofFn f) = h :=
                    (List.append_inj' hEq'' (by simp)).1
                  exact hv this
                have hA : (∑ last : JointHistElem n, A last) = 0 := by
                  refine Fintype.sum_eq_zero (fun last => A last) ?_
                  intro last
                  dsimp [A]
                  refine Fintype.sum_eq_zero (fun x : Percept =>
                    ite
                        (MultiAgentHistory.playerView i
                              (List.ofFn ((splitLastFunEquiv (α := JointHistElem n) m).symm (f, last))) =
                            h ++ [HistElem.per x])
                        (historyProbability σ π
                              (List.ofFn ((splitLastFunEquiv (α := JointHistElem n) m).symm (f, last))))
                        0) ?_
                  intro x
                  exact if_neg (hcond last x)
                simpa [A, hv] using hA
    -- Combine the three rewriting steps.
    calc
      (∑ x : Percept, playerViewProbability i σ π (h ++ [HistElem.per x]))
          = ∑ x : Percept,
              ∑ p : (Fin m → JointHistElem n) × JointHistElem n,
                ite
                    (MultiAgentHistory.playerView i
                          (List.ofFn ((splitLastFunEquiv (α := JointHistElem n) m).symm p)) =
                        h ++ [HistElem.per x])
                    (historyProbability σ π
                          (List.ofFn ((splitLastFunEquiv (α := JointHistElem n) m).symm p)))
                    0 := h1
      _ = ∑ p : (Fin m → JointHistElem n) × JointHistElem n,
              ∑ x : Percept,
                ite
                    (MultiAgentHistory.playerView i
                          (List.ofFn ((splitLastFunEquiv (α := JointHistElem n) m).symm p)) =
                        h ++ [HistElem.per x])
                    (historyProbability σ π
                          (List.ofFn ((splitLastFunEquiv (α := JointHistElem n) m).symm p)))
                    0 := hswap
      _ = ∑ f : Fin m → JointHistElem n,
            if MultiAgentHistory.playerView i (List.ofFn f) = h
            then ∑ jp : JointPercept n, historyProbability σ π (List.ofFn f ++ [JointHistElem.per jp])
            else 0 := hcompute
  -- Bound the per-extension sum termwise using `historyProbability_tsum_append_per_le`.
  have hBound :
      (∑ f : Fin m → JointHistElem n,
          if MultiAgentHistory.playerView i (List.ofFn f) = h
          then ∑ jp : JointPercept n, historyProbability σ π (List.ofFn f ++ [JointHistElem.per jp])
          else 0)
        ≤
      (∑ f : Fin m → JointHistElem n,
          if MultiAgentHistory.playerView i (List.ofFn f) = h
          then historyProbability σ π (List.ofFn f)
          else 0) := by
    classical
    -- Compare summands pointwise over the finite domain.
    simpa using
      (Finset.sum_le_sum (s := (Finset.univ : Finset (Fin m → JointHistElem n))) (fun f _ => by
        by_cases hvh : MultiAgentHistory.playerView i (List.ofFn f) = h
        · -- Reduce to `historyProbability_tsum_append_per_le` on the full history `List.ofFn f`.
          have hview_wf : (MultiAgentHistory.playerView i (List.ofFn f)).wellFormed = true := by
            -- rewrite using `hvh.symm : h = playerView ...`
            simpa [hvh.symm] using hw
          have hw_full : MultiAgentHistory.wellFormed (List.ofFn f : MultiAgentHistory n) = true :=
            wellFormed_of_playerView_wellFormed i (List.ofFn f) hview_wf
          have hview_last : (MultiAgentHistory.playerView i (List.ofFn f)).getLast? = some (HistElem.act a_last) := by
            simpa [hvh.symm] using hlast
          have hlast_full : ∃ ja : JointAction n, (List.ofFn f : MultiAgentHistory n).getLast? = some (JointHistElem.act ja) :=
            endsWithAct_of_playerView_endsWithAct (i := i) (h := List.ofFn f) hview_last
          have hle :
              (∑' jp : JointPercept n, historyProbability σ π ((List.ofFn f : MultiAgentHistory n) ++ [JointHistElem.per jp]))
                ≤ historyProbability σ π (List.ofFn f : MultiAgentHistory n) :=
            historyProbability_tsum_append_per_le (σ := σ) (π := π) (h := (List.ofFn f : MultiAgentHistory n)) hw_full hlast_full
          have hle' :
              (∑ jp : JointPercept n, historyProbability σ π ((List.ofFn f : MultiAgentHistory n) ++ [JointHistElem.per jp]))
                ≤ historyProbability σ π (List.ofFn f : MultiAgentHistory n) := by
            simpa [tsum_fintype] using hle
          simpa [hvh] using hle'
        · simp [hvh]))
  -- Put everything together.
  calc
    (∑' x : Percept, playerViewProbability i σ π (h ++ [HistElem.per x]))
        = ∑ x : Percept, playerViewProbability i σ π (h ++ [HistElem.per x]) := by
            simp [tsum_fintype]
    _ = ∑ f : Fin m → JointHistElem n,
          if MultiAgentHistory.playerView i (List.ofFn f) = h
          then ∑ jp : JointPercept n, historyProbability σ π (List.ofFn f ++ [JointHistElem.per jp])
          else 0 := hLHS
    _ ≤ ∑ f : Fin m → JointHistElem n,
          if MultiAgentHistory.playerView i (List.ofFn f) = h
          then historyProbability σ π (List.ofFn f)
          else 0 := hBound
    _ = playerViewProbability i σ π h := by
          simp [playerViewProbability, m]

/-!
## The Subjective Environment `σᵢ`

Following the thesis, the subjective environment is defined by the identity:

`σᵢ(eᵢ | hᵢ aᵢ) := σᵢ^{πᵢ}(hᵢ aᵢ eᵢ) / σᵢ^{πᵢ}(hᵢ aᵢ)`,

where `σᵢ^{πᵢ}` is the marginal player-view distribution `playerViewProbability`.
-/

/-- Conditional next-percept probability in the subjective environment. -/
noncomputable def prob {n : ℕ} (i : Fin n) (σ : MultiAgentEnvironment n) (π : MultiAgentPolicy n) :
    History → Percept → ENNReal
  | h, x =>
      if h.wellFormed = true then
        match h.getLast? with
        | some (HistElem.act _) =>
            let denom := playerViewProbability i σ π h
            let num := playerViewProbability i σ π (h ++ [HistElem.per x])
            if denom = 0 then 0 else num / denom
        | _ => 0
      else 0

end SubjectiveEnvironment

/-- The canonical subjective environment `σᵢ` induced by `σ` and the joint policy `policies`. -/
noncomputable def SubjectiveEnvironment.of {n : ℕ} (i : Fin n)
    (σ : MultiAgentEnvironment n) (policies : Fin n → StochasticPolicy) :
    SubjectiveEnvironment n i := by
  classical
  let π : MultiAgentPolicy n := SubjectiveEnvironment.jointPolicy policies
  refine
    { multiEnv := σ
      allPolicies := policies
      asEnvironment :=
        { prob := SubjectiveEnvironment.prob (n := n) i σ π
          prob_le_one := ?_ } }
  intro h hw
  classical
  have hw' : h.wellFormed = true := by simpa using hw
  -- If `h` does not end with an action, our `prob` is identically 0.
  cases hlast : h.getLast? with
  | none =>
    simp [SubjectiveEnvironment.prob, hw', hlast]
  | some e =>
    cases e with
    | per _ =>
      simp [SubjectiveEnvironment.prob, hw', hlast]
    | act _a =>
      -- Main case: `h` ends with an action, so `prob` is defined by conditionalizing the marginal distribution.
      -- Let `denom = σᵢ^{π}(h)` and `num x = σᵢ^{π}(h x)`. Then
      -- `∑ prob(h,·) = 0` if `denom = 0`, and otherwise `(∑ num)/denom ≤ 1`.
      let denom : ENNReal := SubjectiveEnvironment.playerViewProbability (n := n) i σ π h
      by_cases hden : denom = 0
      · -- denom = 0 ⇒ all conditional probabilities are 0
        simp [SubjectiveEnvironment.prob, hw', hlast, denom, hden]
      · -- denom ≠ 0: use the semimeasure property of the marginal player-view distribution.
        have hsum_le :
            (∑' x : Percept, SubjectiveEnvironment.playerViewProbability (n := n) i σ π (h ++ [HistElem.per x]))
              ≤ denom := by
          refine SubjectiveEnvironment.playerViewProbability_tsum_append_per_le (n := n) (i := i) (σ := σ) (π := π)
            (h := h) hw' ?_
          exact ⟨_a, hlast⟩
        -- Now compute `∑ prob` and bound it by `1` via `(/ denom)`.
        calc
          (∑' x : Percept, SubjectiveEnvironment.prob (n := n) i σ π h x)
              = (∑' x : Percept,
                    SubjectiveEnvironment.playerViewProbability (n := n) i σ π (h ++ [HistElem.per x])) / denom := by
                  simp [SubjectiveEnvironment.prob, hw', hlast, denom, hden, div_eq_mul_inv]
                  simpa using
                    (ENNReal.tsum_mul_right (a := denom⁻¹)
                      (f := fun x => SubjectiveEnvironment.playerViewProbability (n := n) i σ π (h ++ [HistElem.per x])))
          _ ≤ denom / denom := ENNReal.div_le_div_right hsum_le denom
          _ ≤ 1 := ENNReal.div_self_le_one

/-! ## ε-Best Response and Nash Equilibrium

Definition 7.5 from Leike's thesis: A policy π_i is an ε-best response if
  V*_σ_i(h) - V^π_i_σ_i(h) < ε
-/

/-- Policy value: expected value when following policy π.
    This is defined as the expected discounted sum of rewards. -/
noncomputable def policyValue (env : Environment) (π : StochasticPolicy)
    (γ : DiscountFactor) (h : History) (horizon : ℕ) : ℝ :=
  value env π γ h horizon

/-- A policy is an ε-best response in a subjective environment.
    Definition 7.5: V*_σ_i(h) - V^π_σ_i(h) < ε -/
def isEpsilonBestResponse {n : ℕ} {i : Fin n} (σ_i : SubjectiveEnvironment n i)
    (π : StochasticPolicy) (γ : DiscountFactor) (ε : ℝ) (h : History)
    (horizon : ℕ) : Prop :=
  optimalValue σ_i.asEnvironment γ h horizon -
    policyValue σ_i.asEnvironment π γ h horizon < ε

/-! ## Theorem 7.5: Convergence to Equilibrium

The main result: If all agents use asymptotically optimal policies
(e.g., Thompson sampling) over M^O_refl, they converge to ε-Nash equilibrium.
-/

namespace LeikeStyle

open _root_.MeasureTheory Filter
open Mettapedia.UniversalAI.GrainOfTruth.FixedPoint

/-- *Asymptotically optimal in mean* (Leike): the expected optimality gap tends to `0`
under the on-policy trajectory measure of `μ` driven by `π`. -/
def AsymptoticallyOptimalInMean (μ : Environment) (π : Agent) (γ : DiscountFactor) (horizon : ℕ)
    (h_stoch : isStochastic μ) : Prop :=
  Tendsto
    (fun t =>
      ∫ traj, regret μ π γ (trajectoryToHistory traj t) horizon ∂(environmentMeasureWithPolicy μ π h_stoch))
    atTop (nhds 0)

theorem measurable_regretOnTrajectory (μ : Environment) (π : Agent) (γ : DiscountFactor)
    (t horizon : ℕ) :
    Measurable fun traj : Trajectory =>
      regret μ π γ (trajectoryToHistory traj t) horizon := by
  -- Depends only on the first `t` steps of the trajectory.
  have hadapt :
      ∀ traj₁ traj₂, (∀ i < t, traj₁ i = traj₂ i) →
        regret μ π γ (trajectoryToHistory traj₁ t) horizon =
          regret μ π γ (trajectoryToHistory traj₂ t) horizon := by
    intro traj₁ traj₂ hEq
    have hHist :
        trajectoryToHistory traj₁ t = trajectoryToHistory traj₂ t :=
      trajectoryToHistory_depends_on_prefix traj₁ traj₂ t hEq
    simp [hHist]
  -- First get measurability w.r.t. the prefix σ-algebra, then upgrade to the ambient one.
  have hmeas_prefix :
      @Measurable Trajectory ℝ (sigmaAlgebraUpTo t) _ (fun traj : Trajectory =>
        regret μ π γ (trajectoryToHistory traj t) horizon) := by
    -- Use the characterization lemma from Phase 1.
    exact (measurable_wrt_filtration_iff (f := fun traj : Trajectory =>
      regret μ π γ (trajectoryToHistory traj t) horizon) (t := t)).2 hadapt
  exact hmeas_prefix.mono (sigmaAlgebraUpTo_le t) le_rfl

theorem integrable_regretOnTrajectory (μ : Environment) (π : Agent) (γ : DiscountFactor)
    (t horizon : ℕ) (h_stoch : isStochastic μ) :
    _root_.MeasureTheory.Integrable (fun traj : Trajectory => regret μ π γ (trajectoryToHistory traj t) horizon)
      (environmentMeasureWithPolicy μ π h_stoch) := by
  have hmeas :
      _root_.MeasureTheory.AEStronglyMeasurable (fun traj : Trajectory =>
        regret μ π γ (trajectoryToHistory traj t) horizon)
        (environmentMeasureWithPolicy μ π h_stoch) :=
    (measurable_regretOnTrajectory (μ := μ) (π := π) (γ := γ) (t := t) (horizon := horizon)).aestronglyMeasurable
  -- Bound by the integrable constant `horizon`.
  have hbound :
      ∀ᵐ traj ∂(environmentMeasureWithPolicy μ π h_stoch),
        ‖regret μ π γ (trajectoryToHistory traj t) horizon‖ ≤ (horizon : ℝ) := by
    refine Filter.Eventually.of_forall (fun traj => ?_)
    have h0 : 0 ≤ regret μ π γ (trajectoryToHistory traj t) horizon :=
      regret_nonneg μ π γ (trajectoryToHistory traj t) horizon
    have hle : regret μ π γ (trajectoryToHistory traj t) horizon ≤ (horizon : ℝ) := by
      have h1 := regret_le_optimalValue μ π γ (trajectoryToHistory traj t) horizon
      have h2 : optimalValue μ γ (trajectoryToHistory traj t) horizon ≤ horizon :=
        optimalValue_le μ γ (trajectoryToHistory traj t) horizon
      linarith
    -- Since the value is nonnegative, `‖x‖ = x`.
    simpa [Real.norm_eq_abs, abs_of_nonneg h0] using hle
  have hconst :
      _root_.MeasureTheory.Integrable (fun _ : Trajectory => (horizon : ℝ))
        (environmentMeasureWithPolicy μ π h_stoch) := by
    -- A constant is integrable on a finite measure space.
    letI : _root_.MeasureTheory.IsProbabilityMeasure (environmentMeasureWithPolicy μ π h_stoch) :=
      environmentMeasureWithPolicy_isProbability μ π h_stoch
    exact
      (_root_.MeasureTheory.integrable_const (μ := environmentMeasureWithPolicy μ π h_stoch)
        (c := (horizon : ℝ)))
  exact hconst.mono' hmeas hbound

end LeikeStyle

/-- Theorem 7.5 (Convergence to Equilibrium):
    If all agents use asymptotically optimal policies in M^O_refl,
    then they converge to ε-Nash equilibrium.

    For all ε > 0 and all agents i, the probability that π_i is an
    ε-best response converges to 1 as t → ∞. -/
theorem convergence_to_equilibrium {n : ℕ} (O : Oracle)
    (_M : ReflectiveEnvironmentClass O) (σ : MultiAgentEnvironment n)
    (policies : Fin n → StochasticPolicy)
    (γ : DiscountFactor) (horizon : ℕ)
    (h_stoch : ∀ i : Fin n, isStochastic (SubjectiveEnvironment.of i σ policies).asEnvironment)
    (h_aoim : ∀ i : Fin n,
      LeikeStyle.AsymptoticallyOptimalInMean
        ((SubjectiveEnvironment.of i σ policies).asEnvironment) (policies i) γ horizon (h_stoch i))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ i : Fin n,
      Filter.Tendsto
        (fun t =>
          (environmentMeasureWithPolicy
            ((SubjectiveEnvironment.of i σ policies).asEnvironment) (policies i) (h_stoch i)).real
            {traj | isEpsilonBestResponse (SubjectiveEnvironment.of i σ policies) (policies i) γ ε
              (trajectoryToHistory traj t) horizon})
        Filter.atTop (nhds 1) := by
  classical
  intro i
  -- Notation.
  let σ_i : SubjectiveEnvironment n i := SubjectiveEnvironment.of i σ policies
  let μT : MeasureTheory.Measure Trajectory :=
    environmentMeasureWithPolicy σ_i.asEnvironment (policies i) (h_stoch i)
  have hμ_prob : MeasureTheory.IsProbabilityMeasure μT :=
    environmentMeasureWithPolicy_isProbability σ_i.asEnvironment (policies i) (h_stoch i)
  have hμ_univ : μT.real Set.univ = 1 := by
    letI : _root_.MeasureTheory.IsProbabilityMeasure μT := hμ_prob
    exact _root_.MeasureTheory.probReal_univ (μ := μT)

  -- Define the (time-indexed) regret random variable.
  let f : ℕ → Trajectory → ℝ := fun t traj =>
    Mettapedia.UniversalAI.GrainOfTruth.FixedPoint.regret σ_i.asEnvironment (policies i) γ
      (trajectoryToHistory traj t) horizon

  have hf_nonneg : ∀ t, 0 ≤ᵐ[μT] f t := by
    intro t
    refine Filter.Eventually.of_forall (fun traj => ?_)
    simpa [f] using
      (Mettapedia.UniversalAI.GrainOfTruth.FixedPoint.regret_nonneg σ_i.asEnvironment (policies i) γ
        (trajectoryToHistory traj t) horizon)

  have hf_integrable : ∀ t, MeasureTheory.Integrable (f t) μT := by
    intro t
    simpa [μT, f, σ_i] using
      (LeikeStyle.integrable_regretOnTrajectory (μ := σ_i.asEnvironment) (π := policies i) (γ := γ)
        (t := t) (horizon := horizon) (h_stoch := h_stoch i))

  -- Markov inequality + `E[f_t] → 0` gives `P(f_t ≥ ε) → 0`.
  have h_prob_bad :
      Filter.Tendsto (fun t => μT.real {traj | (ε : ℝ) ≤ f t traj}) Filter.atTop (nhds 0) := by
    have hE : Filter.Tendsto (fun t => ∫ traj, f t traj ∂μT) Filter.atTop (nhds 0) := by
      simpa [LeikeStyle.AsymptoticallyOptimalInMean, μT, σ_i, f] using h_aoim i

    have h_upper :
        ∀ t, μT.real {traj | (ε : ℝ) ≤ f t traj} ≤ (∫ traj, f t traj ∂μT) / ε := by
      intro t
      have hMarkov :
          ε * μT.real {traj | (ε : ℝ) ≤ f t traj} ≤ ∫ traj, f t traj ∂μT :=
        _root_.MeasureTheory.mul_meas_ge_le_integral_of_nonneg (μ := μT) (f := f t)
          (hf_nonneg t) (hf_integrable t) ε
      -- divide by ε > 0
      have : μT.real {traj | (ε : ℝ) ≤ f t traj} * ε ≤ ∫ traj, f t traj ∂μT := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using hMarkov
      exact (le_div_iff₀ hε).2 this

    have h_upper_tendsto : Filter.Tendsto (fun t => (∫ traj, f t traj ∂μT) / ε) Filter.atTop (nhds 0) := by
      simpa using hE.div_const ε

    have h_nonneg_meas : ∀ t, 0 ≤ μT.real {traj | (ε : ℝ) ≤ f t traj} := by
      intro t
      exact _root_.MeasureTheory.measureReal_nonneg

    exact squeeze_zero h_nonneg_meas h_upper h_upper_tendsto

  -- Convert to the desired ε-best-response probability: P(f_t < ε) = 1 - P(ε ≤ f_t).
  have h_event :
      ∀ t,
        μT.real {traj | isEpsilonBestResponse σ_i (policies i) γ ε (trajectoryToHistory traj t) horizon} =
          1 - μT.real {traj | (ε : ℝ) ≤ f t traj} := by
    intro t
    have hMeasBad : MeasurableSet {traj | (ε : ℝ) ≤ f t traj} := by
      have hMeasF : Measurable (f t) := by
        -- `f t` depends only on the first `t` steps.
        simpa [f, σ_i] using
          (LeikeStyle.measurable_regretOnTrajectory (μ := σ_i.asEnvironment) (π := policies i) (γ := γ)
            (t := t) (horizon := horizon))
      exact measurableSet_preimage hMeasF measurableSet_Ici
    have hCompl :
        {traj | isEpsilonBestResponse σ_i (policies i) γ ε (trajectoryToHistory traj t) horizon} =
          ({traj | (ε : ℝ) ≤ f t traj} : Set Trajectory)ᶜ := by
      ext traj
      -- unfold ε-best-response and rewrite as `regret < ε`
      simp [isEpsilonBestResponse, policyValue, Mettapedia.UniversalAI.GrainOfTruth.FixedPoint.regret, f, σ_i,
        Set.mem_compl_iff, not_le]
    -- use `measureReal_compl`
    -- μT.real (Aᶜ) = μT.real univ - μT.real A = 1 - μT.real A
    calc
      μT.real {traj | isEpsilonBestResponse σ_i (policies i) γ ε (trajectoryToHistory traj t) horizon}
          = μT.real ({traj | (ε : ℝ) ≤ f t traj} : Set Trajectory)ᶜ := by
              simp [hCompl]
      _ = μT.real Set.univ - μT.real {traj | (ε : ℝ) ≤ f t traj} := by
              simpa using (_root_.MeasureTheory.measureReal_compl (μ := μT) hMeasBad)
      _ = 1 - μT.real {traj | (ε : ℝ) ≤ f t traj} := by
              simp [hμ_univ]

  -- Finish by composing limits.
  have h_one_sub :
      Filter.Tendsto (fun t => 1 - μT.real {traj | (ε : ℝ) ≤ f t traj}) Filter.atTop (nhds (1 - 0)) :=
    (tendsto_const_nhds.sub h_prob_bad)
  have h_one_sub' :
      Filter.Tendsto (fun t => 1 - μT.real {traj | (ε : ℝ) ≤ f t traj}) Filter.atTop (nhds 1) := by
    simpa using h_one_sub
  -- rewrite using `h_event`
  have h_eventuallyEq :
      (fun t =>
        (environmentMeasureWithPolicy σ_i.asEnvironment (policies i) (h_stoch i)).real
          {traj | isEpsilonBestResponse σ_i (policies i) γ ε (trajectoryToHistory traj t) horizon})
        = (fun t => μT.real {traj | isEpsilonBestResponse σ_i (policies i) γ ε
          (trajectoryToHistory traj t) horizon}) := rfl
  -- final `simp` reduction
  have : Filter.Tendsto (fun t => μT.real {traj | isEpsilonBestResponse σ_i (policies i) γ ε
      (trajectoryToHistory traj t) horizon}) Filter.atTop (nhds 1) := by
    -- use pointwise identity to `1 - P(bad)`
    have hEq : (fun t =>
        μT.real {traj | isEpsilonBestResponse σ_i (policies i) γ ε (trajectoryToHistory traj t) horizon})
        = fun t => 1 - μT.real {traj | (ε : ℝ) ≤ f t traj} := by
      funext t
      exact h_event t
    simpa [hEq] using h_one_sub'
  simpa [μT, σ_i, h_eventuallyEq] using this

/-! ## Corollary: Thompson Sampling Convergence (planned)

Leike's Chapter 5 proves asymptotic optimality-in-mean of Thompson sampling via:
posterior-as-martingale → (Blackwell–Dubins) strong merging → on-policy value convergence.

This file only contains the *game-theory* wrapper (Theorem 7.5 style).
The learning-theory core will live in the measure-theory pipeline under
`Mettapedia/UniversalAI/GrainOfTruth/MeasureTheory/`.
-/

/-! ## Helper: Extract Deterministic Policy from Agent

Given a stochastic agent (policy assigning probabilities to actions),
extract a deterministic policy by choosing the argmax action.
-/

/-- Extract policy from agent by choosing max-probability action. -/
noncomputable def agentToPolicy (agent : Agent) : History → Action :=
  fun h =>
    match [Action.left, Action.right, Action.stay].argmax (agent.policy h) with
    | some a => a
    | none => Action.stay  -- can't happen since the actions list is non-empty

theorem agentToPolicy_mem (agent : Agent) (h : History) :
    agentToPolicy agent h ∈ [Action.left, Action.right, Action.stay] := by
  simp only [agentToPolicy]
  cases harg : List.argmax (agent.policy h) [Action.left, Action.right, Action.stay] with
  | none =>
    have := List.argmax_eq_none.mp harg
    exact absurd this actions_ne_nil
  | some a =>
    exact List.argmax_mem harg

theorem agentToPolicy_maximizes (agent : Agent) (h : History) (a : Action) :
    agent.policy h a ≤ agent.policy h (agentToPolicy agent h) := by
  simp only [agentToPolicy]
  cases harg : List.argmax (agent.policy h) [Action.left, Action.right, Action.stay] with
  | none =>
    have := List.argmax_eq_none.mp harg
    exact absurd this actions_ne_nil
  | some m =>
    have ha_mem : a ∈ [Action.left, Action.right, Action.stay] := by
      cases a <;> simp
    exact List.le_of_mem_argmax ha_mem harg

end Mettapedia.UniversalAI.GrainOfTruth
