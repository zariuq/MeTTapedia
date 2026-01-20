import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Data.Finset.Max
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Universal Bayesian Agents (Core Abstractions)

This module factors out the agent/environment interaction model used throughout
the UniversalAI development, parameterized by:

* `Action`  - a finite action alphabet
* `Percept` - a finite percept alphabet
* `PerceptReward` - a bounded reward function `Percept → ℝ` (in `[0,1]`)

The existing file `Mettapedia/UniversalAI/BayesianAgents.lean` provides a
concrete toy instantiation (3 actions, 4 percepts). This `Core` module is the
generic API intended for later chapters/book-wide reuse.
-/

namespace Mettapedia.UniversalAI.BayesianAgents.Core

open scoped BigOperators
open scoped Classical

universe uA uP

/-! ## Histories -/

/-- A history element is either an action or a percept. -/
inductive HistElem (Action : Type uA) (Percept : Type uP) : Type (max uA uP)
  | act : Action → HistElem Action Percept
  | per : Percept → HistElem Action Percept

/-- A history is a list of alternating actions and percepts. -/
abbrev History (Action : Type uA) (Percept : Type uP) : Type (max uA uP) :=
  List (HistElem Action Percept)

namespace History

variable {Action : Type uA} {Percept : Type uP}

/-- Check if a history is well-formed (alternating action/percept), optionally ending with an action. -/
def wellFormed : History Action Percept → Bool
  | [] => true
  | [HistElem.act _] => true
  | HistElem.act _ :: HistElem.per _ :: rest => wellFormed rest
  | _ => false

/-- Extract actions from a history. -/
def actions : History Action Percept → List Action
  | [] => []
  | HistElem.act a :: rest => a :: actions rest
  | HistElem.per _ :: rest => actions rest

/-- Extract percepts from a history. -/
def percepts : History Action Percept → List Percept
  | [] => []
  | HistElem.act _ :: rest => percepts rest
  | HistElem.per x :: rest => x :: percepts rest

/-- Number of action-percept cycles in a history. -/
def cycles (h : History Action Percept) : ℕ :=
  h.percepts.length

theorem percepts_append (h₁ h₂ : History Action Percept) :
    (h₁ ++ h₂).percepts = h₁.percepts ++ h₂.percepts := by
  induction h₁ with
  | nil => simp [percepts]
  | cons e rest ih =>
      cases e <;> simp [percepts, ih]

theorem cycles_append (h₁ h₂ : History Action Percept) :
    (h₁ ++ h₂).cycles = h₁.cycles + h₂.cycles := by
  simp [cycles, percepts_append]

theorem cycles_append_act_per (h : History Action Percept) (a : Action) (x : Percept) :
    (h ++ [HistElem.act a, HistElem.per x]).cycles = h.cycles + 1 := by
  calc
    (h ++ [HistElem.act a, HistElem.per x]).cycles =
        h.cycles + History.cycles ([HistElem.act a, HistElem.per x] : History Action Percept) := by
          simpa using
            (cycles_append (h₁ := h) (h₂ := ([HistElem.act a, HistElem.per x] : History Action Percept)))
    _ = h.cycles + 1 := by
          simp [cycles, percepts]

end History

/-! ## Environments and agents -/

/-- A stochastic environment mapping histories to distributions over percepts (finite alphabet). -/
structure Environment (Action : Type uA) (Percept : Type uP) [Fintype Percept] where
  /-- Probability of next percept given the current history. -/
  prob : History Action Percept → Percept → ENNReal
  /-- Semimeasure property: total mass is at most 1 on well-formed histories. -/
  prob_le_one :
    ∀ h,
      History.wellFormed (Action := Action) (Percept := Percept) h →
        (∑ x : Percept, prob h x) ≤ 1

/-- A (possibly stochastic) agent/policy mapping histories to distributions over actions. -/
structure Agent (Action : Type uA) (Percept : Type uP) [Fintype Action] where
  /-- Probability of choosing the next action given the current history. -/
  policy : History Action Percept → Action → ENNReal
  /-- Proper distribution: total mass is exactly 1 on well-formed histories. -/
  policy_sum_one :
    ∀ h,
      History.wellFormed (Action := Action) (Percept := Percept) h →
        (∑ a : Action, policy h a) = 1

/-- Discount factor γ ∈ [0,1]. -/
structure DiscountFactor where
  val : ℝ
  nonneg : 0 ≤ val
  le_one : val ≤ 1

/-- Reward function on percepts with rewards in `[0,1]`. -/
class PerceptReward (Percept : Type uP) where
  reward : Percept → ℝ
  reward_nonneg : ∀ x, 0 ≤ reward x
  reward_le_one : ∀ x, reward x ≤ 1

namespace PerceptReward

variable {Percept : Type uP} [PerceptReward Percept]

theorem nonneg (x : Percept) : 0 ≤ PerceptReward.reward x :=
  PerceptReward.reward_nonneg x

theorem le_one (x : Percept) : PerceptReward.reward x ≤ 1 :=
  PerceptReward.reward_le_one x

end PerceptReward

/-! ## Finite-horizon value functions -/

mutual
  /-- Finite-horizon value of policy `π` in environment `μ`. -/
  noncomputable def value {Action : Type uA} {Percept : Type uP}
      [Fintype Action] [Fintype Percept] [PerceptReward Percept]
      (μ : Environment Action Percept) (π : Agent Action Percept) (γ : DiscountFactor)
      (h : History Action Percept) (horizon : ℕ) : ℝ :=
    match horizon with
    | 0 => 0
    | n + 1 =>
      if ¬ History.wellFormed (Action := Action) (Percept := Percept) h then 0
      else
        ∑ a : Action, (π.policy h a).toReal * qValue μ π γ h a n

  /-- Finite-horizon Q-value for taking action `a` in history `h`. -/
  noncomputable def qValue {Action : Type uA} {Percept : Type uP}
      [Fintype Action] [Fintype Percept] [PerceptReward Percept]
      (μ : Environment Action Percept) (π : Agent Action Percept) (γ : DiscountFactor)
      (h : History Action Percept) (a : Action) (horizon : ℕ) : ℝ :=
    match horizon with
    | 0 => 0
    | n + 1 =>
      let ha := h ++ [HistElem.act a]
      if ¬ History.wellFormed (Action := Action) (Percept := Percept) ha then 0
      else
        ∑ x : Percept,
          (μ.prob ha x).toReal *
            (PerceptReward.reward x + γ.val * value μ π γ (ha ++ [HistElem.per x]) n)
end

theorem value_zero {Action : Type uA} {Percept : Type uP}
    [Fintype Action] [Fintype Percept] [PerceptReward Percept]
    (μ : Environment Action Percept) (π : Agent Action Percept) (γ : DiscountFactor)
    (h : History Action Percept) : value μ π γ h 0 = 0 := rfl

theorem qValue_zero {Action : Type uA} {Percept : Type uP}
    [Fintype Action] [Fintype Percept] [PerceptReward Percept]
    (μ : Environment Action Percept) (π : Agent Action Percept) (γ : DiscountFactor)
    (h : History Action Percept) (a : Action) : qValue μ π γ h a 0 = 0 := rfl

theorem value_succ {Action : Type uA} {Percept : Type uP}
    [Fintype Action] [Fintype Percept] [PerceptReward Percept]
    (μ : Environment Action Percept) (π : Agent Action Percept) (γ : DiscountFactor)
    (h : History Action Percept) (n : ℕ) :
    value μ π γ h (n + 1) =
      if ¬ History.wellFormed (Action := Action) (Percept := Percept) h then 0
      else ∑ a : Action, (π.policy h a).toReal * qValue μ π γ h a n := rfl

theorem qValue_succ {Action : Type uA} {Percept : Type uP}
    [Fintype Action] [Fintype Percept] [PerceptReward Percept]
    (μ : Environment Action Percept) (π : Agent Action Percept) (γ : DiscountFactor)
    (h : History Action Percept) (a : Action) (n : ℕ) :
    qValue μ π γ h a (n + 1) =
      let ha := h ++ [HistElem.act a]
      if ¬ History.wellFormed (Action := Action) (Percept := Percept) ha then 0
      else
        ∑ x : Percept,
          (μ.prob ha x).toReal *
            (PerceptReward.reward x + γ.val * value μ π γ (ha ++ [HistElem.per x]) n) := rfl

/-! ## Basic properties: nonnegativity and boundedness -/

mutual

/-- Q-value is non-negative. -/
theorem qValue_nonneg {Action : Type uA} {Percept : Type uP}
    [Fintype Action] [Fintype Percept] [PerceptReward Percept]
    (μ : Environment Action Percept) (π : Agent Action Percept) (γ : DiscountFactor)
    (h : History Action Percept) (a : Action) (n : ℕ) :
    0 ≤ qValue μ π γ h a n := by
  cases n with
  | zero =>
      simp [qValue_zero]
  | succ n =>
      rw [qValue_succ]
      set ha : History Action Percept := h ++ [HistElem.act a]
      cases hwa : History.wellFormed (Action := Action) (Percept := Percept) ha with
      | false =>
          simp [ha, hwa]
      | true =>
          -- Explicitly a finite sum of nonnegative terms.
          simp [ha, hwa]
          classical
          refine Finset.sum_nonneg ?_
          intro x _hx
          have hprob : 0 ≤ (μ.prob ha x).toReal := ENNReal.toReal_nonneg
          have hrew : 0 ≤ PerceptReward.reward x := PerceptReward.nonneg x
          have hγ : 0 ≤ γ.val := γ.nonneg
          have hfuture :
              0 ≤ value μ π γ (h ++ [HistElem.act a, HistElem.per x]) n := by
            have htmp' :
                0 ≤ value μ π γ (ha ++ [HistElem.per x]) n :=
              value_nonneg (μ := μ) (π := π) (γ := γ) (h := (ha ++ [HistElem.per x])) (n := n)
            have htmp :
                0 ≤ value μ π γ ((h ++ [HistElem.act a]) ++ [HistElem.per x]) n := by
              simpa [ha] using htmp'
            have heq :
                ((h ++ [HistElem.act a]) ++ [HistElem.per x]) =
                  (h ++ [HistElem.act a, HistElem.per x]) := by
              simp [List.append_assoc]
            simpa [heq] using htmp
          exact mul_nonneg hprob (add_nonneg hrew (mul_nonneg hγ hfuture))

/-- Value is non-negative. -/
theorem value_nonneg {Action : Type uA} {Percept : Type uP}
    [Fintype Action] [Fintype Percept] [PerceptReward Percept]
    (μ : Environment Action Percept) (π : Agent Action Percept) (γ : DiscountFactor)
    (h : History Action Percept) (n : ℕ) :
    0 ≤ value μ π γ h n := by
  cases n with
  | zero =>
      simp [value_zero]
  | succ n =>
      rw [value_succ]
      cases hwa : History.wellFormed (Action := Action) (Percept := Percept) h with
      | false =>
          simp
      | true =>
          simp
          classical
          refine Finset.sum_nonneg ?_
          intro a _ha
          have hp : 0 ≤ (π.policy h a).toReal := ENNReal.toReal_nonneg
          have hq : 0 ≤ qValue μ π γ h a n :=
            qValue_nonneg (μ := μ) (π := π) (γ := γ) (h := h) (a := a) (n := n)
          exact mul_nonneg hp hq

end

mutual

/-- Q-value is bounded by the horizon. -/
theorem qValue_le {Action : Type uA} {Percept : Type uP}
    [Fintype Action] [Fintype Percept] [PerceptReward Percept]
    (μ : Environment Action Percept) (π : Agent Action Percept) (γ : DiscountFactor)
    (h : History Action Percept) (a : Action) (n : ℕ) :
    qValue μ π γ h a n ≤ n := by
  classical
  cases n with
  | zero =>
      simp [qValue_zero]
  | succ n =>
      rw [qValue_succ]
      set ha : History Action Percept := h ++ [HistElem.act a]
      cases hwa : History.wellFormed (Action := Action) (Percept := Percept) ha with
      | false =>
          simp [ha, hwa]
          nlinarith
      | true =>
          have hwa' : History.wellFormed (Action := Action) (Percept := Percept) ha := by
            simp [hwa]
          -- Bound each term by `(n+1)` and use `∑ prob ≤ 1`.
          simp [ha, hwa]
          set B : ℝ := (n : ℝ) + 1
          have hB_nonneg : 0 ≤ B := by
            dsimp [B]
            nlinarith
          have hprob_le_one : (∑ x : Percept, μ.prob ha x) ≤ 1 :=
            μ.prob_le_one ha hwa'
          have hprob_ne_top : ∀ x : Percept, μ.prob ha x ≠ (⊤ : ENNReal) := by
            intro x
            have hx_le_sum : μ.prob ha x ≤ ∑ y : Percept, μ.prob ha y := by
              classical
              have : μ.prob ha x ≤ ∑ y ∈ (Finset.univ : Finset Percept), μ.prob ha y := by
                refine Finset.single_le_sum ?_ (by simp)
                intro y _hy
                exact zero_le _
              simpa using this
            have hx_le_one : μ.prob ha x ≤ 1 := hx_le_sum.trans hprob_le_one
            exact ne_top_of_le_ne_top ENNReal.one_ne_top hx_le_one
          have htoReal_sum :
              (∑ x ∈ (Finset.univ : Finset Percept), μ.prob ha x).toReal =
                ∑ x ∈ (Finset.univ : Finset Percept), (μ.prob ha x).toReal :=
            ENNReal.toReal_sum (s := (Finset.univ : Finset Percept)) (f := fun x : Percept => μ.prob ha x)
              (by
                intro x hx
                exact hprob_ne_top x)
          have hsum_toReal_le : (∑ x : Percept, (μ.prob ha x).toReal) ≤ 1 := by
            have hle :
                (∑ x : Percept, μ.prob ha x).toReal ≤ (1 : ENNReal).toReal :=
              (ENNReal.toReal_le_toReal (ne_top_of_le_ne_top ENNReal.one_ne_top hprob_le_one)
                ENNReal.one_ne_top).2 hprob_le_one
            simpa [htoReal_sum] using hle
          have hterm_le_B (x : Percept) :
              PerceptReward.reward x + γ.val * value μ π γ (ha ++ [HistElem.per x]) n ≤ B := by
            have hrew : PerceptReward.reward x ≤ 1 := PerceptReward.le_one x
            have hfuture_nonneg :
                0 ≤ value μ π γ (ha ++ [HistElem.per x]) n :=
              value_nonneg (μ := μ) (π := π) (γ := γ) (h := (ha ++ [HistElem.per x])) (n := n)
            have hfuture_le :
                value μ π γ (ha ++ [HistElem.per x]) n ≤ n :=
              value_le (μ := μ) (π := π) (γ := γ) (h := (ha ++ [HistElem.per x])) (n := n)
            have hγmul_le_future :
                γ.val * value μ π γ (ha ++ [HistElem.per x]) n ≤
                  value μ π γ (ha ++ [HistElem.per x]) n := by
              have := mul_le_mul_of_nonneg_right γ.le_one hfuture_nonneg
              simpa using this
            have hγmul_le_n :
                γ.val * value μ π γ (ha ++ [HistElem.per x]) n ≤ n :=
              hγmul_le_future.trans hfuture_le
            dsimp [B]
            nlinarith
          have hsum_le' :
              (∑ x : Percept,
                  (μ.prob ha x).toReal *
                    (PerceptReward.reward x + γ.val * value μ π γ (ha ++ [HistElem.per x]) n)) ≤
                (∑ x : Percept, (μ.prob ha x).toReal * B) := by
            classical
            -- Work with `Finset.univ` explicitly to use `Finset.sum_le_sum`.
            simpa using
              (Finset.sum_le_sum (s := (Finset.univ : Finset Percept))
                (f := fun x : Percept =>
                  (μ.prob ha x).toReal *
                    (PerceptReward.reward x + γ.val * value μ π γ (ha ++ [HistElem.per x]) n))
                (g := fun x : Percept => (μ.prob ha x).toReal * B)
                (by
                  intro x _hx
                  have hprob : 0 ≤ (μ.prob ha x).toReal := ENNReal.toReal_nonneg
                  exact mul_le_mul_of_nonneg_left (hterm_le_B x) hprob))
          have hsum_le :
              (∑ x : Percept,
                  (μ.prob ha x).toReal *
                    (PerceptReward.reward x + γ.val * value μ π γ (ha ++ [HistElem.per x]) n)) ≤
                (∑ x : Percept, (μ.prob ha x).toReal) * B := by
            -- Rewrite `∑ p_x * B` as `(∑ p_x) * B`.
            have hrewrite :
                (∑ x : Percept, (μ.prob ha x).toReal * B) =
                  (∑ x : Percept, (μ.prob ha x).toReal) * B := by
              classical
              simpa using
                (Finset.sum_mul (s := (Finset.univ : Finset Percept))
                  (f := fun x : Percept => (μ.prob ha x).toReal) (a := B)).symm
            simpa [hrewrite] using hsum_le'
          have hsum_le_B : (∑ x : Percept,
                  (μ.prob ha x).toReal *
                    (PerceptReward.reward x + γ.val * value μ π γ (ha ++ [HistElem.per x]) n)) ≤
                B := by
            -- `(∑ p_x) * B ≤ 1 * B = B`.
            have : (∑ x : Percept, (μ.prob ha x).toReal) * B ≤ 1 * B := by
              exact mul_le_mul_of_nonneg_right hsum_toReal_le hB_nonneg
            exact hsum_le.trans (by simpa using this)
          -- `qValue` goal is the same sum; rewrite the history and finish.
          simpa [ha, List.append_assoc, B] using hsum_le_B

/-- Value is bounded by the horizon. -/
theorem value_le {Action : Type uA} {Percept : Type uP}
    [Fintype Action] [Fintype Percept] [PerceptReward Percept]
    (μ : Environment Action Percept) (π : Agent Action Percept) (γ : DiscountFactor)
    (h : History Action Percept) (n : ℕ) :
    value μ π γ h n ≤ n := by
  classical
  cases n with
  | zero =>
      simp [value_zero]
  | succ n =>
      rw [value_succ]
      cases hwa : History.wellFormed (Action := Action) (Percept := Percept) h with
      | false =>
          simp
          nlinarith
      | true =>
          have hwa' : History.wellFormed (Action := Action) (Percept := Percept) h := by
            simp [hwa]
          simp
          have hpolicy_sum_one : (∑ a : Action, π.policy h a) = 1 :=
            π.policy_sum_one h hwa'
          have hpolicy_ne_top : ∀ a : Action, π.policy h a ≠ (⊤ : ENNReal) := by
            intro a
            have ha_le_sum : π.policy h a ≤ ∑ b : Action, π.policy h b := by
              classical
              have : π.policy h a ≤ ∑ b ∈ (Finset.univ : Finset Action), π.policy h b := by
                refine Finset.single_le_sum ?_ (by simp)
                intro b _hb
                exact zero_le _
              simpa using this
            have ha_le_one : π.policy h a ≤ 1 := by simpa [hpolicy_sum_one] using ha_le_sum
            exact ne_top_of_le_ne_top ENNReal.one_ne_top ha_le_one
          have htoReal_sum :
              (∑ a ∈ (Finset.univ : Finset Action), π.policy h a).toReal =
                ∑ a ∈ (Finset.univ : Finset Action), (π.policy h a).toReal :=
            ENNReal.toReal_sum (s := (Finset.univ : Finset Action)) (f := fun a : Action => π.policy h a)
              (by
                intro a _ha
                exact hpolicy_ne_top a)
          have hsum_toReal_eq : (∑ a : Action, (π.policy h a).toReal) = 1 := by
            have :
                (∑ a : Action, π.policy h a).toReal = (1 : ENNReal).toReal := by
              simp [hpolicy_sum_one]
            -- rewrite LHS using `ENNReal.toReal_sum`.
            simpa [htoReal_sum] using this
          have hq_le (a : Action) : qValue μ π γ h a n ≤ n := by
            simpa using qValue_le (μ := μ) (π := π) (γ := γ) (h := h) (a := a) (n := n)
          have hsum_le' :
              (∑ a : Action, (π.policy h a).toReal * qValue μ π γ h a n) ≤
                (∑ a : Action, (π.policy h a).toReal * (n : ℝ)) := by
            classical
            simpa using
              (Finset.sum_le_sum (s := (Finset.univ : Finset Action))
                (f := fun a : Action => (π.policy h a).toReal * qValue μ π γ h a n)
                (g := fun a : Action => (π.policy h a).toReal * (n : ℝ))
                (by
                  intro a _ha
                  have hp : 0 ≤ (π.policy h a).toReal := ENNReal.toReal_nonneg
                  exact mul_le_mul_of_nonneg_left (hq_le a) hp))
          have hsum_le :
              (∑ a : Action, (π.policy h a).toReal * qValue μ π γ h a n) ≤
                (∑ a : Action, (π.policy h a).toReal) * (n : ℝ) := by
            have hrewrite :
                (∑ a : Action, (π.policy h a).toReal * (n : ℝ)) =
                  (∑ a : Action, (π.policy h a).toReal) * (n : ℝ) := by
              classical
              simpa using
                (Finset.sum_mul (s := (Finset.univ : Finset Action))
                  (f := fun a : Action => (π.policy h a).toReal) (a := (n : ℝ))).symm
            simpa [hrewrite] using hsum_le'
          have hsum_le_n : (∑ a : Action, (π.policy h a).toReal * qValue μ π γ h a n) ≤ n := by
            -- rewrite `∑ p_a` to `1`.
            simpa [hsum_toReal_eq] using hsum_le
          -- and `n ≤ n+1`.
          have hn_le : (n : ℝ) ≤ (n + 1 : ℝ) := by nlinarith
          exact hsum_le_n.trans hn_le

end

/-! ## Optimal value functions -/

mutual
  /-- Finite-horizon optimal value `V*` (max over actions). -/
  noncomputable def optimalValue {Action : Type uA} {Percept : Type uP}
      [Fintype Action] [Fintype Percept] [PerceptReward Percept]
      (μ : Environment Action Percept) (γ : DiscountFactor)
      (h : History Action Percept) (horizon : ℕ) : ℝ :=
    match horizon with
    | 0 => 0
    | n + 1 =>
      if ¬ History.wellFormed (Action := Action) (Percept := Percept) h then 0
      else
        (Finset.univ : Finset Action).fold max 0 (fun a => optimalQValue μ γ h a n)

  /-- Finite-horizon optimal Q-value `Q*` (uses `optimalValue` for the future). -/
  noncomputable def optimalQValue {Action : Type uA} {Percept : Type uP}
      [Fintype Action] [Fintype Percept] [PerceptReward Percept]
      (μ : Environment Action Percept) (γ : DiscountFactor)
      (h : History Action Percept) (a : Action) (horizon : ℕ) : ℝ :=
    match horizon with
    | 0 => 0
    | n + 1 =>
      let ha := h ++ [HistElem.act a]
      if ¬ History.wellFormed (Action := Action) (Percept := Percept) ha then 0
      else
        ∑ x : Percept,
          (μ.prob ha x).toReal *
            (PerceptReward.reward x + γ.val * optimalValue μ γ (ha ++ [HistElem.per x]) n)
end

theorem optimalValue_zero {Action : Type uA} {Percept : Type uP}
    [Fintype Action] [Fintype Percept] [PerceptReward Percept]
    (μ : Environment Action Percept) (γ : DiscountFactor) (h : History Action Percept) :
    optimalValue μ γ h 0 = 0 := rfl

theorem optimalQValue_zero {Action : Type uA} {Percept : Type uP}
    [Fintype Action] [Fintype Percept] [PerceptReward Percept]
    (μ : Environment Action Percept) (γ : DiscountFactor) (h : History Action Percept) (a : Action) :
    optimalQValue μ γ h a 0 = 0 := rfl

theorem optimalValue_succ {Action : Type uA} {Percept : Type uP}
    [Fintype Action] [Fintype Percept] [PerceptReward Percept]
    (μ : Environment Action Percept) (γ : DiscountFactor) (h : History Action Percept) (n : ℕ) :
    optimalValue μ γ h (n + 1) =
      if ¬ History.wellFormed (Action := Action) (Percept := Percept) h then 0
      else
        (Finset.univ : Finset Action).fold max 0 (fun a => optimalQValue μ γ h a n) := rfl

theorem optimalQValue_succ {Action : Type uA} {Percept : Type uP}
    [Fintype Action] [Fintype Percept] [PerceptReward Percept]
    (μ : Environment Action Percept) (γ : DiscountFactor) (h : History Action Percept) (a : Action) (n : ℕ) :
    optimalQValue μ γ h a (n + 1) =
      let ha := h ++ [HistElem.act a]
      if ¬ History.wellFormed (Action := Action) (Percept := Percept) ha then 0
      else
        ∑ x : Percept,
          (μ.prob ha x).toReal *
            (PerceptReward.reward x + γ.val * optimalValue μ γ (ha ++ [HistElem.per x]) n) := rfl

/-! ## Choosing an optimal action -/

/-- An action achieving the maximum of `optimalQValue` over all actions (for the given horizon). -/
noncomputable def optimalAction {Action : Type uA} {Percept : Type uP}
    [Fintype Action] [Fintype Percept] [PerceptReward Percept] [Inhabited Action]
    (μ : Environment Action Percept) (γ : DiscountFactor)
    (h : History Action Percept) (horizon : ℕ) : Action :=
  Classical.choose <|
    Finset.exists_max_image (s := (Finset.univ : Finset Action))
      (f := fun a : Action => optimalQValue μ γ h a horizon) (by
        exact ⟨default, by simp⟩)

theorem optimalAction_spec {Action : Type uA} {Percept : Type uP}
    [Fintype Action] [Fintype Percept] [PerceptReward Percept] [Inhabited Action]
    (μ : Environment Action Percept) (γ : DiscountFactor)
    (h : History Action Percept) (horizon : ℕ) :
    (optimalAction μ γ h horizon ∈ (Finset.univ : Finset Action)) ∧
      ∀ a' ∈ (Finset.univ : Finset Action),
        optimalQValue μ γ h a' horizon ≤ optimalQValue μ γ h (optimalAction μ γ h horizon) horizon := by
  classical
  simpa [optimalAction] using
    (Classical.choose_spec <|
      Finset.exists_max_image (s := (Finset.univ : Finset Action))
        (f := fun a : Action => optimalQValue μ γ h a horizon) (by
          exact ⟨default, by simp⟩))

theorem optimalAction_achieves_max {Action : Type uA} {Percept : Type uP}
    [Fintype Action] [Fintype Percept] [PerceptReward Percept] [Inhabited Action]
    (μ : Environment Action Percept) (γ : DiscountFactor)
    (h : History Action Percept) (horizon : ℕ) (a : Action) :
    optimalQValue μ γ h a horizon ≤ optimalQValue μ γ h (optimalAction μ γ h horizon) horizon := by
  classical
  have ha : a ∈ (Finset.univ : Finset Action) := by simp
  exact (optimalAction_spec (μ := μ) (γ := γ) (h := h) (horizon := horizon)).2 a ha

/-! ## Optimal value bounds any policy -/

/-- Helper: `Q^π ≤ Q*` assuming `V^π ≤ V*` for smaller horizons. -/
theorem qValue_le_optimalQValue_strong {Action : Type uA} {Percept : Type uP}
    [Fintype Action] [Fintype Percept] [PerceptReward Percept]
    (μ : Environment Action Percept) (π : Agent Action Percept) (γ : DiscountFactor)
    (h : History Action Percept) (a : Action) (n : ℕ)
    (ih : ∀ k, k < n → ∀ h', value μ π γ h' k ≤ optimalValue μ γ h' k) :
    qValue μ π γ h a n ≤ optimalQValue μ γ h a n := by
  cases n with
  | zero =>
      simp [qValue_zero, optimalQValue_zero]
  | succ n =>
      rw [qValue_succ, optimalQValue_succ]
      set ha : History Action Percept := h ++ [HistElem.act a]
      cases hwa : History.wellFormed (Action := Action) (Percept := Percept) ha with
      | false =>
          simp [ha, hwa]
      | true =>
          classical
          simp [ha, hwa]
          -- Compare the finite sums termwise, using the IH for the future value.
          simpa using
            (Finset.sum_le_sum (s := (Finset.univ : Finset Percept))
              (f := fun x : Percept =>
                (μ.prob (h ++ [HistElem.act a]) x).toReal *
                  (PerceptReward.reward x +
                    γ.val * value μ π γ (h ++ [HistElem.act a, HistElem.per x]) n))
              (g := fun x : Percept =>
                (μ.prob (h ++ [HistElem.act a]) x).toReal *
                  (PerceptReward.reward x +
                    γ.val * optimalValue μ γ (h ++ [HistElem.act a, HistElem.per x]) n))
              (by
                intro x _hx
                have hIH :
                    value μ π γ (h ++ [HistElem.act a, HistElem.per x]) n ≤
                      optimalValue μ γ (h ++ [HistElem.act a, HistElem.per x]) n :=
                  ih n (Nat.lt_succ_self n) (h ++ [HistElem.act a, HistElem.per x])
                have hmul :
                    γ.val * value μ π γ (h ++ [HistElem.act a, HistElem.per x]) n ≤
                      γ.val * optimalValue μ γ (h ++ [HistElem.act a, HistElem.per x]) n :=
                  mul_le_mul_of_nonneg_left hIH γ.nonneg
                have hadd :
                    PerceptReward.reward x + γ.val * value μ π γ (h ++ [HistElem.act a, HistElem.per x]) n ≤
                      PerceptReward.reward x + γ.val * optimalValue μ γ (h ++ [HistElem.act a, HistElem.per x]) n :=
                  add_le_add_left hmul (PerceptReward.reward x)
                have hprob : 0 ≤ (μ.prob (h ++ [HistElem.act a]) x).toReal := ENNReal.toReal_nonneg
                exact mul_le_mul_of_nonneg_left hadd hprob))

/-- For any policy `π`, its value is bounded above by the policy-independent optimal value `V*`. -/
theorem value_le_optimalValue {Action : Type uA} {Percept : Type uP}
    [Fintype Action] [Fintype Percept] [PerceptReward Percept]
    (μ : Environment Action Percept) (π : Agent Action Percept) (γ : DiscountFactor)
    (h : History Action Percept) (n : ℕ) :
    value μ π γ h n ≤ optimalValue μ γ h n := by
  classical
  -- Strong induction to get IH for all smaller horizons (needed under `qValue`).
  induction n using Nat.strong_induction_on generalizing h with
  | _ n ih =>
      cases n with
      | zero =>
          simp [value_zero, optimalValue_zero]
      | succ n =>
          rw [value_succ, optimalValue_succ]
          cases hwa : History.wellFormed (Action := Action) (Percept := Percept) h with
          | false =>
              simp
          | true =>
              have hwa' : History.wellFormed (Action := Action) (Percept := Percept) h := by
                simp [hwa]
              -- Set the max target `M := max_a Q*(h,a,n)`.
              set M : ℝ :=
                (Finset.univ : Finset Action).fold max 0 (fun a => optimalQValue μ γ h a n)
              -- Show `∑ p_a.toReal = 1`.
              have hpolicy_sum_one : (∑ a : Action, π.policy h a) = 1 :=
                π.policy_sum_one h hwa'
              have hpolicy_ne_top : ∀ a : Action, π.policy h a ≠ (⊤ : ENNReal) := by
                intro a
                have ha_le_sum : π.policy h a ≤ ∑ b : Action, π.policy h b := by
                  classical
                  have : π.policy h a ≤ ∑ b ∈ (Finset.univ : Finset Action), π.policy h b := by
                    refine Finset.single_le_sum ?_ (by simp)
                    intro b _hb
                    exact zero_le _
                  simpa using this
                have ha_le_one : π.policy h a ≤ 1 := by
                  simpa [hpolicy_sum_one] using ha_le_sum
                exact ne_top_of_le_ne_top ENNReal.one_ne_top ha_le_one
              have htoReal_sum :
                  (∑ a ∈ (Finset.univ : Finset Action), π.policy h a).toReal =
                    ∑ a ∈ (Finset.univ : Finset Action), (π.policy h a).toReal :=
                ENNReal.toReal_sum (s := (Finset.univ : Finset Action)) (f := fun a : Action => π.policy h a)
                  (by
                    intro a _ha
                    exact hpolicy_ne_top a)
              have hsum_toReal_eq : (∑ a : Action, (π.policy h a).toReal) = 1 := by
                have :
                    (∑ a : Action, π.policy h a).toReal = (1 : ENNReal).toReal := by
                  simp [hpolicy_sum_one]
                simpa [htoReal_sum] using this
              -- Bound each `qValue` by `M`.
              have hq_le_M (a : Action) : qValue μ π γ h a n ≤ M := by
                have hq_le_opt :
                    qValue μ π γ h a n ≤ optimalQValue μ γ h a n := by
                  refine qValue_le_optimalQValue_strong (μ := μ) (π := π) (γ := γ) (h := h) (a := a) (n := n) ?_
                  intro k hk h'
                  exact ih k (lt_trans hk (Nat.lt_succ_self n)) h'
                have hopt_le_M : optimalQValue μ γ h a n ≤ M := by
                  have hex :
                      optimalQValue μ γ h a n ≤ (0 : ℝ) ∨
                        ∃ a' ∈ (Finset.univ : Finset Action),
                          optimalQValue μ γ h a n ≤ optimalQValue μ γ h a' n := by
                    refine Or.inr ?_
                    exact ⟨a, by simp, le_rfl⟩
                  exact (Finset.le_fold_max (s := (Finset.univ : Finset Action)) (b := (0 : ℝ))
                    (f := fun a' : Action => optimalQValue μ γ h a' n) (c := optimalQValue μ γ h a n)).2 hex
                exact hq_le_opt.trans hopt_le_M
              have hsum_le_M' :
                  (∑ a : Action, (π.policy h a).toReal * qValue μ π γ h a n) ≤
                    (∑ a : Action, (π.policy h a).toReal * M) := by
                classical
                simpa using
                  (Finset.sum_le_sum (s := (Finset.univ : Finset Action))
                    (f := fun a : Action => (π.policy h a).toReal * qValue μ π γ h a n)
                    (g := fun a : Action => (π.policy h a).toReal * M)
                    (by
                      intro a _ha
                      have hp : 0 ≤ (π.policy h a).toReal := ENNReal.toReal_nonneg
                      exact mul_le_mul_of_nonneg_left (hq_le_M a) hp))
              have hsum_le_M :
                  (∑ a : Action, (π.policy h a).toReal * qValue μ π γ h a n) ≤ M := by
                have hrewrite :
                    (∑ a : Action, (π.policy h a).toReal * M) =
                      (∑ a : Action, (π.policy h a).toReal) * M := by
                  classical
                  simpa using
                    (Finset.sum_mul (s := (Finset.univ : Finset Action))
                      (f := fun a : Action => (π.policy h a).toReal) (a := M)).symm
                -- `(∑ p_a) * M = 1 * M = M`.
                have : (∑ a : Action, (π.policy h a).toReal * M) ≤ M := by
                  simp [hrewrite, hsum_toReal_eq]
                exact hsum_le_M'.trans this
              -- Finish by unfolding the `if`s and rewriting `M`.
              simpa [hwa, M] using hsum_le_M

theorem optimalValue_ge_value {Action : Type uA} {Percept : Type uP}
    [Fintype Action] [Fintype Percept] [PerceptReward Percept]
    (μ : Environment Action Percept) (γ : DiscountFactor)
    (h : History Action Percept) (n : ℕ) (π : Agent Action Percept) :
    optimalValue μ γ h n ≥ value μ π γ h n := by
  simpa [ge_iff_le] using (value_le_optimalValue (μ := μ) (π := π) (γ := γ) (h := h) (n := n))

/-! ## Average value (γ = 1 friendly) -/

noncomputable def averageValue {Action : Type uA} {Percept : Type uP}
    [Fintype Action] [Fintype Percept] [PerceptReward Percept]
    (μ : Environment Action Percept) (π : Agent Action Percept) (γ : DiscountFactor)
    (h : History Action Percept) (horizon : ℕ) : ℝ :=
  if horizon = 0 then 0 else value μ π γ h horizon / horizon

theorem averageValue_nonneg {Action : Type uA} {Percept : Type uP}
    [Fintype Action] [Fintype Percept] [PerceptReward Percept]
    (μ : Environment Action Percept) (π : Agent Action Percept) (γ : DiscountFactor)
    (h : History Action Percept) (horizon : ℕ) :
    0 ≤ averageValue μ π γ h horizon := by
  by_cases hzero : horizon = 0
  · simp [averageValue, hzero]
  · have hpos : (0 : ℝ) < horizon := by
        exact Nat.cast_pos.mpr (Nat.pos_of_ne_zero hzero)
    have hval : 0 ≤ value μ π γ h horizon :=
      value_nonneg (μ := μ) (π := π) (γ := γ) (h := h) (n := horizon)
    calc
      0 ≤ value μ π γ h horizon / horizon := by
        exact div_nonneg hval hpos.le
      _ = averageValue μ π γ h horizon := by
        simp [averageValue, hzero]

theorem averageValue_le_one {Action : Type uA} {Percept : Type uP}
    [Fintype Action] [Fintype Percept] [PerceptReward Percept]
    (μ : Environment Action Percept) (π : Agent Action Percept) (γ : DiscountFactor)
    (h : History Action Percept) (horizon : ℕ) :
    averageValue μ π γ h horizon ≤ 1 := by
  by_cases hzero : horizon = 0
  · simp [averageValue, hzero]
  · have hpos : (0 : ℝ) < horizon := by
        exact Nat.cast_pos.mpr (Nat.pos_of_ne_zero hzero)
    have hval : value μ π γ h horizon ≤ horizon :=
      value_le (μ := μ) (π := π) (γ := γ) (h := h) (n := horizon)
    have hdiv : value μ π γ h horizon / horizon ≤ (horizon : ℝ) / horizon :=
      div_le_div_of_nonneg_right hval hpos.le
    calc
      averageValue μ π γ h horizon = value μ π γ h horizon / horizon := by
        simp [averageValue, hzero]
      _ ≤ (horizon : ℝ) / horizon := hdiv
      _ = 1 := by simp [hzero]

end Mettapedia.UniversalAI.BayesianAgents.Core
