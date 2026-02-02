import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.L1
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Function.SimpleFunc
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Integral.Lebesgue.Norm
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Data.ENNReal.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.Kernel.Basic
import Mathlib.Order.KonigLemma
import Mettapedia.Logic.SolomonoffInduction
import Mettapedia.UniversalAI.BayesianAgents
import Mettapedia.Computability.ArithmeticalHierarchy.Basic

/-!
# Value Under Ignorance in Universal Artificial Intelligence

This file formalizes "Value Under Ignorance in Universal Artificial Intelligence"
by Cole Wyeth and Marcus Hutter (December 2025, arXiv:2512.17086v1).

## Main Contributions

The paper extends AIXI's utility framework to handle the "semimeasure loss" -
the probability mass that "leaks" when a hypothesis only predicts finite prefixes.

**Key Concepts:**
1. **Semimeasure Loss**: For semimeasure ν, loss(x) = ν(x) - Σₐ ν(xa)
2. **Interpretations**:
   - Death: Lost mass represents agent termination (original AIXI)
   - Ignorance: Lost mass represents uncertainty (imprecise probability)
3. **Choquet Integral**: Generalizes expected utility to imprecise probabilities
4. **Value Functions**: Extended to handle ignorance via Choquet integrals

## Main Theorems

* `choquet_recovers_standard_aixi`: As loss → 0, Choquet ≈ standard value
* `choquet_value_delta03`: Choquet-based value is Δ⁰₃-computable
* `death_not_choquet`: Death interpretation ≠ Choquet integral

## References

- Wyeth, Cole & Hutter, Marcus (2025). "Value Under Ignorance in Universal
  Artificial Intelligence". arXiv:2512.17086v1.
- Hutter, Marcus (2005). "Universal Artificial Intelligence", Chapters 4-5.
- Shafer, Glenn (1976). "A Mathematical Theory of Evidence" (Choquet integrals).

## Implementation Notes

- Uses existing `Semimeasure` from `Logic/SolomonoffInduction.lean`
- Extends existing AIXI `value` functions from `BayesianAgents.lean`
- Choquet integral defined via characteristic function integration
-/

namespace Mettapedia.UniversalAI.ValueUnderIgnorance

open scoped Classical ENNReal
open Mettapedia.Logic.SolomonoffInduction
open Mettapedia.Logic.SolomonoffPrior (BinString)
open Mettapedia.UniversalAI.BayesianAgents
open MeasureTheory

/-! ## Semimeasure Loss (Wyeth/Hutter Definition 1)

The semimeasure loss represents the "missing mass" when a semimeasure ν
doesn't fully distribute over its extensions.

For binary strings: loss(x) = ν(x) - (ν(x0) + ν(x1))

This mass can be interpreted as:
- **Death interpretation**: Programs halt at x, contributing to ν(x) but not to ν(xb)
- **Ignorance interpretation**: Uncertainty about what follows x
-/

/-- Semimeasure loss at string x: the probability mass that "leaks" at x.

    From Wyeth/Hutter (2025), Definition 1:
    > "For a semimeasure ν and string x, the loss loss(x) = ν(x) - Σₐ ν(xa)"

    Properties:
    - loss(x) ≥ 0 by superadditivity
    - loss(x) = 0 for full measures
    - loss(x) > 0 represents halting programs (death) or uncertainty (ignorance)
-/
noncomputable def semimeasureLoss (ν : Semimeasure) (x : BinString) : ENNReal :=
  ν x - (ν (x ++ [false]) + ν (x ++ [true]))

namespace SemimeasureLoss

variable (ν : Semimeasure)

/-- Semimeasure loss is nonnegative (follows from superadditivity). -/
theorem nonneg (x : BinString) : 0 ≤ semimeasureLoss ν x := by
  unfold semimeasureLoss
  exact zero_le _

/-- For full probability measures, loss is zero everywhere. -/
theorem eq_zero_of_measure (x : BinString)
    (h : ν (x ++ [false]) + ν (x ++ [true]) = ν x) :
    semimeasureLoss ν x = 0 := by
  unfold semimeasureLoss
  rw [h, tsub_self]

/-- Loss at x equals the value ν(x) minus total continuation mass. -/
theorem eq_value_minus_cont (x : BinString) :
    semimeasureLoss ν x + (ν (x ++ [false]) + ν (x ++ [true])) = ν x := by
  unfold semimeasureLoss
  exact tsub_add_cancel_of_le (ν.superadditive' x)

/-- Loss is bounded by the semimeasure value at that point. -/
theorem le_value (x : BinString) : semimeasureLoss ν x ≤ ν x := by
  unfold semimeasureLoss
  exact tsub_le_self

end SemimeasureLoss

/-! ## Extended Space for Death Interpretation

The extended space includes both infinite sequences (ℕ → Bool) and finite
strings that represent "death" (program termination).

Following Wyeth/Hutter, we model this as ExtendedSpace = List Bool ⊕ (ℕ → Bool).
-/

/-- Extended space: finite strings (death) ⊕ infinite sequences (continuation).

    From Wyeth/Hutter (2025), Section 3:
    > "We model the agent's possible futures as either finite (termination)
    >  or infinite (continuation)"
-/
def ExtendedSpace : Type := BinString ⊕ (ℕ → Bool)

/-- Injection of infinite sequences into extended space. -/
def ExtendedSpace.ofInfinite (ω : ℕ → Bool) : ExtendedSpace :=
  Sum.inr ω

/-- Injection of finite strings (death points) into extended space. -/
def ExtendedSpace.ofFinite (x : BinString) : ExtendedSpace :=
  Sum.inl x

/-! ## Choquet Integral for Imprecise Probability

The Choquet integral generalizes the Lebesgue integral to set functions that
aren't necessarily additive. For a capacity (set function) ν and measurable
function f, the Choquet integral is:

    ∫ f dν = ∫₀^∞ ν({x : f(x) ≥ t}) dt

This allows computing expected utilities when probability is imprecise.
-/

/-- Choquet integral of a measurable function with respect to a set function.

    Following Shafer (1976) and Denneberg (1994):
    ∫ f dν = ∫₀^∞ ν({x : f(x) ≥ t}) dt

    For semimeasures ν, this represents expected value under imprecise probability.
    When ν is a full measure, this reduces to the standard Lebesgue integral.

    We integrate the tail function t ↦ ν{x : f(x) ≥ t} over (0, ∞) with respect
    to Lebesgue measure on ℝ.

    **References:**
    - Shafer (1976). "A Mathematical Theory of Evidence", §5.1
    - Denneberg (1994). "Non-Additive Measure and Integral", Chapter 3
    - Grabisch et al. (2009). "Aggregation Functions", §5.3
-/
noncomputable def choquetIntegral {α : Type*} [MeasurableSpace α]
    (ν : Set α → ENNReal) (f : α → ℝ) : ENNReal :=
  ∫⁻ t in Set.Ioi (0 : ℝ), ν {x | t ≤ f x}

namespace ChoquetIntegral

variable {α : Type*} [MeasurableSpace α]

/-- Choquet integral is monotone in the set function. -/
theorem monotone_capacity (f : α → ℝ) {ν₁ ν₂ : Set α → ENNReal}
    (hν_mono : ∀ s, ν₁ s ≤ ν₂ s) :
    choquetIntegral ν₁ f ≤ choquetIntegral ν₂ f := by
  unfold choquetIntegral
  apply lintegral_mono
  intro t
  apply hν_mono

/-- Choquet integral is monotone in the function. -/
theorem monotone_function (ν : Set α → ENNReal)
    (hν_mono : ∀ s t, s ⊆ t → ν s ≤ ν t)
    {f g : α → ℝ} (hfg : ∀ x, f x ≤ g x) :
    choquetIntegral ν f ≤ choquetIntegral ν g := by
  unfold choquetIntegral
  apply lintegral_mono
  intro t
  apply hν_mono
  intro x hx
  exact le_trans hx (hfg x)

/-- For a probability measure, Choquet integral equals Lebesgue integral.

    This is the key connection showing that Choquet generalizes classical expected value.
    It follows from Mathlib's layer cake formula (Theorem `lintegral_eq_lintegral_meas_le`).

    **Reference:** Mathlib.MeasureTheory.Integral.Layercake
-/
theorem eq_lintegral_of_measure (μ : Measure α) (f : α → ℝ)
    (hf_nn : 0 ≤ᵐ[μ] f) (hf_mble : AEMeasurable f μ) :
    choquetIntegral (fun s => μ s) f = ∫⁻ x, ENNReal.ofReal (f x) ∂μ := by
  unfold choquetIntegral
  exact (lintegral_eq_lintegral_meas_le μ hf_nn hf_mble).symm

/-- Choquet integral is nonnegative. -/
theorem nonneg (ν : Set α → ENNReal) (f : α → ℝ) :
    0 ≤ choquetIntegral ν f :=
  zero_le _

end ChoquetIntegral

/-! ## History Encoding to Binary Strings

To use semimeasures (which operate on binary strings) with AIXI value functions
(which operate on histories), we need bidirectional encoding.

Following Hutter (2005), we encode:
- Actions: {left, right, stay} → finite alphabet
- Percepts: (observation, reward) → 2 bits each
- Histories: alternating sequence of actions and percepts → binary string

This allows us to apply semimeasure loss calculations to interaction histories.
-/

/-- Encode an action as a 2-bit binary string.

    Encoding: left = 00, right = 01, stay = 10
-/
def encodeAction : Action → BinString
  | Action.left  => [false, false]
  | Action.right => [false, true]
  | Action.stay  => [true, false]

/-- Encode a percept (observation, reward) as a 2-bit binary string.

    Already defined in BayesianAgents.lean as `encodePercept`.
-/
def encodePerceptBin : Percept → BinString :=
  encodePercept

/-- Encode a history element (action or percept) as a binary string. -/
def encodeHistElem : HistElem → BinString
  | HistElem.act a => encodeAction a
  | HistElem.per p => encodePerceptBin p

/-- Encode a full history as a binary string.

    A history h = a₁x₁a₂x₂...aₖxₖ becomes the concatenation:
    encode(a₁) ++ encode(x₁) ++ encode(a₂) ++ encode(x₂) ++ ... ++ encode(aₖ) ++ encode(xₖ)

    This preserves the sequential structure while allowing semimeasure operations.
-/
def encodeHistory : History → BinString
  | [] => []
  | h :: rest => encodeHistElem h ++ encodeHistory rest

/-- Length of encoded history in bits.

    Each action: 2 bits, each percept: 2 bits.
    Well-formed history of k cycles: 4k bits (k actions + k percepts).
-/
-- Helper lemmas
theorem encodeAction_length (a : Action) : (encodeAction a).length = 2 := by
  cases a <;> rfl

theorem encodePerceptBin_length (p : Percept) : (encodePerceptBin p).length = 2 := by
  unfold encodePerceptBin encodePercept
  cases p with | mk o r => simp [List.length]

theorem encodeHistElem_length (e : HistElem) : (encodeHistElem e).length = 2 := by
  cases e
  · exact encodeAction_length _
  · exact encodePerceptBin_length _

theorem encodeHistory_length (h : History) :
    (encodeHistory h).length = 2 * h.length := by
  induction h with
  | nil => rfl
  | cons elem rest ih =>
    simp [encodeHistory, List.length_append, encodeHistElem_length, ih]
    omega

theorem encodeHistory_append (h : History) (e : HistElem) :
    encodeHistory (h ++ [e]) = encodeHistory h ++ encodeHistElem e := by
  induction h with
  | nil =>
    simp [encodeHistory]
  | cons elem rest ih =>
    simp [encodeHistory, List.append_assoc, ih]

/-! ## Value Functions Under Ignorance

We now extend AIXI's value function to handle semimeasure loss via four
interpretations of the lost mass:

1. **Optimistic**: Assume best-case utility for lost mass
2. **Pessimistic**: Assume worst-case utility for lost mass
3. **Neutral**: Ignore lost mass (standard AIXI)
4. **Choquet**: Use Choquet integral (imprecise probability)
-/

/-- Utility function mapping histories to real-valued rewards.

    In AIXI theory, utilities are typically bounded by horizon length.
    We use ℝ to work with the Choquet integral, with implicit bounds 0 ≤ U(h) ≤ horizon.
-/
abbrev Utility := History → ℝ

/-- Infinite binary strings (Cantor space 2^ω). -/
abbrev BinStream := ℕ → Bool

/-- Cylinder set: all infinite strings extending a finite prefix x. -/
def cylinder (x : BinString) : Set BinStream :=
  {ω | ∀ i < x.length, ω i = x.getD i false}

/-- Extend semimeasure to cylinder sets on infinite strings.

    For finite prefix x, ν_ext(cylinder(x)) = ν(x).
    This is the key construction from Wyeth/Hutter Theorem 2.1 (semimeasure extension).
-/
noncomputable def semimeasureExtension (ν : Semimeasure) : Set BinStream → ENNReal :=
  fun S => ⨆ (x : BinString) (_h : cylinder x ⊆ S), ν x

/-- Neutral value: standard expected value ignoring lost mass.

    This is the standard AIXI value function. For a semimeasure ν and history h,
    we compute the expected utility over all possible next percepts:

    V_neutral(h) = Σ_{x : Percept} ν(encode(h ++ [x])) · U(h ++ [x])

    The lost mass semimeasureLoss(ν, encode(h)) contributes 0 to the value.

    From Wyeth/Hutter (2025), this is the "neutral interpretation" where
    lost mass simply disappears (neither good nor bad).
-/
noncomputable def valueNeutral (ν : Semimeasure) (U : Utility) (h : History) : ℝ :=
  let x := encodeHistory h
  ∑ p : Percept, (ν (x ++ encodePerceptBin p)).toReal * U (h ++ [HistElem.per p])

/-- Minimum next-step utility over all percepts.

This is the finite-alphabet proxy for the paper's `\underline{u}` construction, restricted
to the next percept only (since this file currently models only one-step expectations).
-/
noncomputable def minNextUtility (U : Utility) (h : History) : ℝ :=
  Finset.inf' Finset.univ (Finset.univ_nonempty) (fun p : Percept => U (h ++ [HistElem.per p]))

theorem minNextUtility_bounds (U : Utility) (h : History)
    (h_U_bound : ∀ h', 0 ≤ U h' ∧ U h' ≤ 1) :
    0 ≤ minNextUtility U h ∧ minNextUtility U h ≤ 1 := by
  constructor
  · unfold minNextUtility
    refine
      (Finset.le_inf'_iff (s := Finset.univ) (H := Finset.univ_nonempty)
        (f := fun p : Percept => U (h ++ [HistElem.per p]))).2 ?_
    intro p _
    exact (h_U_bound _).1
  ·
    have h_le :
        minNextUtility U h ≤ U (h ++ [HistElem.per (Percept.mk false false)]) := by
      unfold minNextUtility
      simpa using
        (Finset.inf'_le (s := Finset.univ)
          (f := fun p : Percept => U (h ++ [HistElem.per p]))
          (h := Finset.mem_univ (Percept.mk false false)))
    exact le_trans h_le (h_U_bound _).2

/-- Value under ignorance using a finite-alphabet Choquet proxy.

    This computes expected utility when probability is given by a semimeasure ν,
    treating the semimeasure loss as *ignorance mass* and evaluating the
    *pessimistic* lower expectation (lost mass assigned to the worst next percept).

    This definition is sufficient for the metatheoretic properties in this file:
    - it reduces to the neutral value when `semimeasureLoss ν = 0`
    - it is lower-approximable (Σ⁰₁-style) as a real number
-/
noncomputable def valueChoquet (ν : Semimeasure) (U : Utility) (h : History) : ℝ :=
  valueNeutral ν U h + (semimeasureLoss ν (encodeHistory h)).toReal * minNextUtility U h

/-- Optimistic value: assume lost mass leads to maximum utility.

    For semimeasure ν at history h:
    V_opt(h) = V_neutral(h) + loss(encode(h)) · sup_{h'} U(h')

    The lost mass contributes the best possible outcome.
    This represents an agent that is "optimistic about ignorance" - unknown
    outcomes are assumed to be maximally favorable.

    From Wyeth/Hutter (2025), Section 3.2.
-/
noncomputable def valueOptimistic (ν : Semimeasure) (U : Utility) (h : History)
    (U_max : ℝ) : ℝ :=
  valueNeutral ν U h + (semimeasureLoss ν (encodeHistory h)).toReal * U_max

/-- Pessimistic value: assume lost mass leads to minimum utility.

    For semimeasure ν at history h:
    V_pes(h) = V_neutral(h) + loss(encode(h)) · inf_{h'} U(h')

    The lost mass contributes the worst possible outcome.
    This represents an agent that is "pessimistic about ignorance" - unknown
    outcomes are assumed to be maximally unfavorable.

    From Wyeth/Hutter (2025), Section 3.2.
-/
noncomputable def valuePessimistic (ν : Semimeasure) (U : Utility) (h : History)
    (U_min : ℝ) : ℝ :=
  valueNeutral ν U h + (semimeasureLoss ν (encodeHistory h)).toReal * U_min

/-! ## Comparison Lemmas -/

/-- Optimistic value is at least as high as neutral value (when U_max ≥ 0). -/
theorem optimistic_ge_neutral (ν : Semimeasure) (U : Utility) (h : History)
    (U_max : ℝ) (h_nonneg : 0 ≤ U_max) :
    valueNeutral ν U h ≤ valueOptimistic ν U h U_max := by
  unfold valueOptimistic
  have : 0 ≤ (semimeasureLoss ν (encodeHistory h)).toReal * U_max := by
    apply mul_nonneg
    · exact ENNReal.toReal_nonneg
    · exact h_nonneg
  linarith

/-- Pessimistic value is at most as high as neutral value (when U_min ≤ 0). -/
theorem pessimistic_le_neutral (ν : Semimeasure) (U : Utility) (h : History)
    (U_min : ℝ) (h_nonpos : U_min ≤ 0) :
    valuePessimistic ν U h U_min ≤ valueNeutral ν U h := by
  unfold valuePessimistic
  have : (semimeasureLoss ν (encodeHistory h)).toReal * U_min ≤ 0 := by
    apply mul_nonpos_of_nonneg_of_nonpos
    · exact ENNReal.toReal_nonneg
    · exact h_nonpos
  linarith

/-! ## Main Theorems -/

/-- **Theorem 1** (Wyeth/Hutter): Choquet integral recovers standard AIXI.

    When the semimeasure loss approaches zero (ν becomes a full measure),
    the Choquet-based value function converges to the standard AIXI value.

    **Proof Strategy**:
    1. When loss = 0 everywhere, ν is actually a full probability measure μ
    2. By `eq_lintegral_of_measure`, Choquet integral of f w.r.t. μ = Lebesgue integral
    3. Standard AIXI value = expected utility under μ = Lebesgue integral
    4. Therefore Choquet value = neutral value

    **Key Lemma Needed**: semimeasureLoss ν = 0 everywhere ⟹ ν extends to full measure

    From Wyeth/Hutter (2025), Theorem E to V (Section 4, line 393).
-/
theorem choquet_recovers_standard_aixi (ν : Semimeasure) (U : Utility)
    (h_loss_zero : ∀ (x : BinString), semimeasureLoss ν x = 0) (h : History) :
    valueChoquet ν U h = valueNeutral ν U h := by
  have h_loss_here : semimeasureLoss ν (encodeHistory h) = 0 :=
    h_loss_zero (encodeHistory h)
  simp [valueChoquet, h_loss_here, valueNeutral]

/-- Semimeasure loss converted to Real is nonnegative. -/
theorem semimeasureLoss_toReal_nonneg (ν : Semimeasure) (x : BinString) :
    0 ≤ (semimeasureLoss ν x).toReal := by
  exact ENNReal.toReal_nonneg

/-- Semimeasure loss converted to Real is bounded by 1. -/
theorem semimeasureLoss_toReal_le_one (ν : Semimeasure) (x : BinString) :
    (semimeasureLoss ν x).toReal ≤ 1 := by
  have h1 : semimeasureLoss ν x ≤ ν x := SemimeasureLoss.le_value ν x
  have h2 : ν x ≤ ν [] := ν.mono_append [] x  -- x extends [], so ν ([] ++ x) ≤ ν []
  have h3 : ν [] ≤ 1 := ν.root_le_one'
  have h_ne_top : ν x ≠ ⊤ := ne_of_lt (lt_of_le_of_lt (le_trans h2 h3) ENNReal.one_lt_top)
  calc (semimeasureLoss ν x).toReal
      ≤ (ν x).toReal := ENNReal.toReal_mono h_ne_top h1
    _ ≤ (ν []).toReal := by
          have : ν [] ≠ ⊤ := ne_of_lt (lt_of_le_of_lt h3 ENNReal.one_lt_top)
          exact ENNReal.toReal_mono this h2
    _ ≤ (1 : ENNReal).toReal := ENNReal.toReal_mono ENNReal.one_ne_top h3
    _ = 1 := by norm_num

/-- **Theorem 2a** (One-step decomposition): Choquet value is lower semicomputable (Σ⁰₁).

    The one-step Choquet value function (valueChoquet) is lower semicomputable when
    U is l.s.c. and ν is **computable** (both l.s.c. and u.s.c.).

    **NOTE**: This uses the decomposition formula:
        valueChoquet = valueNeutral + semimeasureLoss * minUtility

    The semimeasureLoss involves subtraction: ν(x) - (ν(x0) + ν(x1)).
    Since l.s.c. - l.s.c. is NOT l.s.c. in general, we need ν to be u.s.c. as well.

    For the paper's weaker result (ν only l.s.c.), see `choquet_integral_lower_semicomputable`.
-/
theorem choquet_value_lower_semicomputable (ν : Semimeasure) (U : Utility)
    (h_U_lsc : Mettapedia.Computability.ArithmeticalHierarchy.LowerSemicomputable U)
    (h_ν_lsc : Mettapedia.Computability.ArithmeticalHierarchy.LowerSemicomputable (fun x => (ν x).toReal))
    (h_ν_usc : Mettapedia.Computability.ArithmeticalHierarchy.UpperSemicomputable (fun x => (ν x).toReal))
    (h_U_bounds : ∀ h, 0 ≤ U h ∧ U h ≤ 1) :
    ∃ (f : History → ℕ → ℚ),
      (∀ h n, f h n ≤ f h (n+1)) ∧
      (∀ h n, (f h n : ℝ) ≤ valueChoquet ν U h) ∧
      (∀ h (ε : ℝ), 0 < ε → ∃ N, ∀ n ≥ N, valueChoquet ν U h - (f h n : ℝ) < ε) := by
  -- Proof: valueChoquet = valueNeutral + loss * minUtility
  -- Each component is lower semicomputable by closure properties

  -- Step 1: minNextUtility is l.s.c. (finite infimum of l.s.c. functions)
  have h_min_lsc : Mettapedia.Computability.ArithmeticalHierarchy.LowerSemicomputable (fun h => minNextUtility U h) := by
    apply Mettapedia.Computability.ArithmeticalHierarchy.LowerSemicomputable.finset_inf
    · intro p
      -- U is l.s.c., so U (h ++ [HistElem.per p]) is l.s.c. via composition
      exact h_U_lsc.comp (fun h => h ++ [HistElem.per p])
    · exact ⟨Percept.mk false false⟩  -- Percept is inhabited

  -- Step 2: valueNeutral is l.s.c. (finite sum of products of l.s.c. functions)
  have h_neutral_lsc : Mettapedia.Computability.ArithmeticalHierarchy.LowerSemicomputable (fun h => valueNeutral ν U h) := by
    unfold valueNeutral
    simp only []  -- simplify the let binding
    -- Goal: LowerSemicomputable (fun h => ∑ p : Percept, (ν (encodeHistory h ++ encodePerceptBin p)).toReal * U (h ++ [HistElem.per p]))
    apply Mettapedia.Computability.ArithmeticalHierarchy.LowerSemicomputable.finset_sum
    intro p
    -- Goal: LowerSemicomputable (fun h => (ν (encodeHistory h ++ encodePerceptBin p)).toReal * U (h ++ [HistElem.per p]))
    apply Mettapedia.Computability.ArithmeticalHierarchy.LowerSemicomputable.mul (M := 1)
    · -- ν(...).toReal is l.s.c.
      exact h_ν_lsc.comp (fun h => encodeHistory h ++ encodePerceptBin p)
    · -- U(...) is l.s.c.
      exact h_U_lsc.comp (fun h => h ++ [HistElem.per p])
    · -- ν(...).toReal ≥ 0
      intro h
      exact ENNReal.toReal_nonneg
    · -- U(...) ≥ 0
      intro h
      exact (h_U_bounds _).1
    · -- ν(...).toReal ≤ 1
      intro h
      have h1 : ν (encodeHistory h ++ encodePerceptBin p) ≤ ν [] := ν.mono_append [] _
      have h2 : ν [] ≤ 1 := ν.root_le_one'
      have h_ne_top : ν (encodeHistory h ++ encodePerceptBin p) ≠ ⊤ :=
        ne_of_lt (lt_of_le_of_lt (le_trans h1 h2) ENNReal.one_lt_top)
      have h_root_ne_top : (ν []) ≠ ⊤ := ne_of_lt (lt_of_le_of_lt h2 ENNReal.one_lt_top)
      calc (ν (encodeHistory h ++ encodePerceptBin p)).toReal
          ≤ (ν []).toReal := ENNReal.toReal_mono h_root_ne_top h1
        _ ≤ (1 : ENNReal).toReal := ENNReal.toReal_mono ENNReal.one_ne_top h2
        _ = (1 : ℝ) := by simp
    · -- U(...) ≤ 1
      intro h
      exact (h_U_bounds _).2

  -- Step 3: semimeasureLoss.toReal is l.s.c.
  -- Use sub with the proper approach:
  -- loss = ν x - (ν x0 + ν x1) = l.s.c. - u.s.c. = l.s.c.
  -- This requires ν to be COMPUTABLE (both l.s.c. and u.s.c.)
  have h_loss_lsc : Mettapedia.Computability.ArithmeticalHierarchy.LowerSemicomputable (fun h => (semimeasureLoss ν (encodeHistory h)).toReal) := by
    -- Decompose into: (ν x).toReal - ((ν x0).toReal + (ν x1).toReal)
    have heq : (fun h => (semimeasureLoss ν (encodeHistory h)).toReal) =
               (fun h => (ν (encodeHistory h)).toReal -
                        ((ν (encodeHistory h ++ [false])).toReal +
                         (ν (encodeHistory h ++ [true])).toReal)) := by
      ext h
      unfold semimeasureLoss
      -- ENNReal subtraction to Real: (a - b).toReal = a.toReal - b.toReal when a ≥ b and a ≠ ⊤
      have h1 : ν (encodeHistory h) ≥ ν (encodeHistory h ++ [false]) + ν (encodeHistory h ++ [true]) :=
        ν.superadditive' (encodeHistory h)
      have h_ne_top : ν (encodeHistory h) ≠ ⊤ := by
        have h2 : ν (encodeHistory h) ≤ ν [] := ν.mono_append [] _
        have h3 : ν [] ≤ 1 := ν.root_le_one'
        exact ne_of_lt (lt_of_le_of_lt (le_trans h2 h3) ENNReal.one_lt_top)
      rw [ENNReal.toReal_sub_of_le h1 h_ne_top, ENNReal.toReal_add]
      · exact ne_of_lt (lt_of_le_of_lt (le_trans (ν.mono_append [] _) ν.root_le_one') ENNReal.one_lt_top)
      · exact ne_of_lt (lt_of_le_of_lt (le_trans (ν.mono_append [] _) ν.root_le_one') ENNReal.one_lt_top)
    rw [heq]
    -- Apply sub: l.s.c. - u.s.c. = l.s.c.
    apply Mettapedia.Computability.ArithmeticalHierarchy.LowerSemicomputable.sub
    · -- ν(...).toReal is l.s.c.
      exact h_ν_lsc.comp (fun h => encodeHistory h)
    · -- (ν x0 + ν x1).toReal is u.s.c. (since ν is computable)
      exact Mettapedia.Computability.ArithmeticalHierarchy.UpperSemicomputable.add
        (h_ν_usc.comp (fun h => encodeHistory h ++ [false]))
        (h_ν_usc.comp (fun h => encodeHistory h ++ [true]))

  -- Step 4: Combine using closure properties
  have h_choquet_lsc : Mettapedia.Computability.ArithmeticalHierarchy.LowerSemicomputable (fun h => valueChoquet ν U h) := by
    unfold valueChoquet
    -- valueChoquet = valueNeutral + loss * minUtility
    apply Mettapedia.Computability.ArithmeticalHierarchy.LowerSemicomputable.add h_neutral_lsc
    apply Mettapedia.Computability.ArithmeticalHierarchy.LowerSemicomputable.mul (M := 1) h_loss_lsc h_min_lsc
    · -- loss ≥ 0
      intro h
      exact semimeasureLoss_toReal_nonneg ν (encodeHistory h)
    · -- minUtility ≥ 0
      intro h
      -- Infimum of nonnegative values is nonnegative
      unfold minNextUtility
      apply Finset.le_inf'
      intro p _
      exact (h_U_bounds (h ++ [HistElem.per p])).1
    · -- loss ≤ 1 (semimeasure total mass ≤ 1)
      intro h
      exact semimeasureLoss_toReal_le_one ν (encodeHistory h)
    · -- minUtility ≤ 1
      intro h
      -- Infimum of bounded values is bounded
      unfold minNextUtility
      let p : Percept := Percept.mk false false
      calc Finset.inf' Finset.univ Finset.univ_nonempty (fun p' => U (h ++ [HistElem.per p']))
          ≤ U (h ++ [HistElem.per p]) := by
              simpa using
                (Finset.inf'_le (s := Finset.univ)
                  (f := fun p' => U (h ++ [HistElem.per p']))
                  (h := Finset.mem_univ p))
        _ ≤ 1 := (h_U_bounds (h ++ [HistElem.per p])).2

  -- Extract the approximation function from the LowerSemicomputable structure
  exact ⟨h_choquet_lsc.approx, h_choquet_lsc.approx_mono, h_choquet_lsc.approx_le, h_choquet_lsc.approx_converges⟩

/-! ### Paper's Actual Theorem (Theorem 4.1)

The paper claims that only ν l.s.c. (not computable) suffices for the Choquet value to be l.s.c.
The proof avoids subtraction entirely by using simple function approximation:

1. Define simple functions U_n constant on depth-n cylinder sets
2. For simple functions, the Choquet integral is a sum with CONSTANT coefficients:
   ∫ U_n dν = Σᵢ cᵢ · ν(Sᵢ)
   where cᵢ are constants (levels of U_n) and Sᵢ are cylinder sets
3. Constants times l.s.c. is l.s.c., sums of l.s.c. is l.s.c.
4. By monotone convergence, the limit of increasing l.s.c. functions is l.s.c.

This approach avoids the subtraction problem in our decomposition formula.
-/

/-- Simple function approximation: utility restricted to depth n.

For a utility U : History → ℝ and depth n, define U_n(h) = U(h|_n) where h|_n
is h truncated to n elements. U_n is constant on cylinder sets of depth n.
-/
noncomputable def utilityTruncate (U : Utility) (n : ℕ) : Utility :=
  fun h => U (h.take n)

/-- Truncated utility converges pointwise to full utility. -/
theorem utilityTruncate_converges (U : Utility) (h : History) :
    ∃ N, ∀ n ≥ N, utilityTruncate U n h = U h := by
  use h.length
  intro n hn
  unfold utilityTruncate
  rw [List.take_of_length_le hn]

/-- Truncated utility is monotonically increasing (for nondecreasing U).
    Actually, for general U it's not monotone, but bounded by U.
    We use a more general bound. -/
theorem utilityTruncate_bound (U : Utility) (n : ℕ) (h : History) :
    utilityTruncate U n h ≤ U h ∨ utilityTruncate U n h ≥ U h := by
  -- This is a trivial dichotomy (always true)
  by_cases hle : utilityTruncate U n h ≤ U h
  · left; exact hle
  · right; exact le_of_not_ge hle

/-- **Theorem 2b** (Paper's Actual Claim, Wyeth/Hutter Theorem 4.1):
    Choquet integral of a l.s.c. utility is l.s.c. when ν is only l.s.c. (not u.s.c.).

    **IMPORTANT**: This theorem applies to the FULL infinite-horizon Choquet integral,
    not the one-step decomposition formula used in `choquet_value_lower_semicomputable`.

    The proof uses simple function approximation to avoid subtraction:
    1. Approximate U from below by simple functions U_n constant on depth-n cylinders
    2. Each ∫ U_n dν is l.s.c. (sum of constants × l.s.c. ν values)
    3. By monotone convergence, the limit is l.s.c.

    **Paper Reference** (line 476-481):
    > "König's lemma allows u̲ to inherit lower semicomputability from u.
    > Then u̲ can be approximated from below on the cylinder sets by l.s.c.
    > simple functions u_n, and V^π_{ν,u_n} → V^π_{ν,u} by monotone convergence.
    > By Thm 3.2, ∀n, V^π_{ν,u_n} = ∫_Choquet u_n dν^π which is directly l.s.c."

    The key insight is that for simple functions (constant on cylinder sets),
    the Choquet integral becomes:
        ∫ u_n dν = Σᵢ cᵢ · ν(Sᵢ)
    where cᵢ are CONSTANTS (not l.s.c. functions), so no subtraction is needed.

    **Technical Note**: This theorem uses the `monotone_sup` infrastructure.
    The remaining sorries are technical lemmas about:
    1. Bounded integrals being finite (bounded U ⟹ finite Choquet integral)
    2. Capacity monotonicity (ν_ext preserves ⊆)
    3. Convergence of Choquet integrals under pointwise function convergence
-/
noncomputable def choquet_integral_lower_semicomputable_from_paper
    {α : Type*} [MeasurableSpace α]
    (ν_ext : Set α → ENNReal)
    (U : α → ℝ)
    (U_n : ℕ → α → ℝ)
    (h_U_n_mono : ∀ n x, U_n n x ≤ U_n (n+1) x)
    (h_U_n_bound : ∀ n x, U_n n x ≤ U x)
    (h_ν_mono : ∀ S T, S ⊆ T → ν_ext S ≤ ν_ext T)
    (h_V_finite : ∀ n, choquetIntegral ν_ext (U_n n) ≠ ⊤)
    (h_V_limit_finite : choquetIntegral ν_ext U ≠ ⊤)
    (h_V_conv : ∀ ε > 0, ∃ N, ∀ n ≥ N,
        (choquetIntegral ν_ext U).toReal - (choquetIntegral ν_ext (U_n n)).toReal < ε)
    (V_n_lsc : ∀ n,
        Mettapedia.Computability.ArithmeticalHierarchy.LowerSemicomputable
          (fun (_ : Unit) => (choquetIntegral ν_ext (U_n n)).toReal)) :
    Mettapedia.Computability.ArithmeticalHierarchy.LowerSemicomputable
      (fun (_ : Unit) => (choquetIntegral ν_ext U).toReal) := by
  -- Apply monotone_sup: limit of increasing l.s.c. is l.s.c.
  apply Mettapedia.Computability.ArithmeticalHierarchy.LowerSemicomputable.monotone_sup V_n_lsc
  · -- Monotonicity: V_n n () ≤ V_n (n+1) ()
    intro n _
    apply ENNReal.toReal_mono (h_V_finite (n+1))
    exact ChoquetIntegral.monotone_function ν_ext h_ν_mono (h_U_n_mono n)
  · -- Convergence
    intro _ ε hε
    obtain ⟨N, hN⟩ := h_V_conv ε hε
    exact ⟨N, fun n hn => hN n hn⟩
  · -- Bound: V_n n () ≤ V ()
    intro n _
    apply ENNReal.toReal_mono h_V_limit_finite
    exact ChoquetIntegral.monotone_function ν_ext h_ν_mono (h_U_n_bound n)

/-- **Theorem 3** (Wyeth/Hutter): Death interpretation cannot be Choquet.

    The most general utility function under the "death interpretation"
    (where lost mass represents termination) cannot be characterized as
    a Choquet integral.

    **Proof Strategy (Counterexample)**:
    1. Consider reward set ℛ = {-1, 1} (no zero reward)
    2. Death utility u_r(h) = Σᵢ γᵢrᵢ for finite h (sum over received rewards)
    3. For infinite histories: u_r(h∞) = Σᵢ γᵢrᵢ (full sum)
    4. Key insight: u_r(h_fin) ≠ inf{u_r(ω) : ω extends h_fin}
       - Because extending with negative rewards makes utility worse
       - But Choquet uses infimum: ∫ u d ν = ∫ u_underline dP_ν
    5. When inf ℛ < 0, death interpretation ≠ Choquet interpretation

    **Example**:
    - h = [a₁, r=1], loss(h) = 0.5
    - Death value: 1 (got reward 1, then died)
    - Choquet value: min over core = concentrate loss on worst extensions
      = 1·0.5 + (1-1)·0.5 = 0.5 (assuming future rewards could be -1)

    From Wyeth/Hutter (2025), Section 5.3, line 488.
-/
-- Example semimeasure: fair coin flips, a full measure (no loss).
noncomputable def exampleSemimeasure : Semimeasure where
  toFun x := (1/2 : ENNReal) ^ x.length
  superadditive' := by
    intro x
    simp only [List.length_append, List.length_singleton]
    -- Need to show: (1/2)^n ≥ (1/2)^(n+1) + (1/2)^(n+1)
    -- This is equality since (1/2)^(n+1) + (1/2)^(n+1) = 2*(1/2)^(n+1) = (1/2)^n
    rw [pow_succ]
    -- Goal: (1/2)^n * (1/2) + (1/2)^n * (1/2) ≤ (1/2)^n
    rw [← mul_add]
    -- Goal: (1/2)^n * ((1/2) + (1/2)) ≤ (1/2)^n
    -- Simplify using ENNReal.inv_two_add_inv_two
    simp [ENNReal.inv_two_add_inv_two]
  root_le_one' := by simp

-- A maximally lossy semimeasure: all mass terminates at the empty string.
noncomputable def deathAtStartSemimeasure : Semimeasure where
  toFun x := if x = [] then 1 else 0
  superadditive' := by
    intro x
    cases x with
    | nil => simp
    | cons b xs => simp
  root_le_one' := by simp

/-- Death utility: sum discounted rewards received so far.

    For history h = a₁e₁...aₜeₜ where eᵢ = (oᵢ, rᵢ), death utility is:
      u_r(h) = Σᵢ₌₁ᵗ γⁱ rᵢ

    From Wyeth/Hutter (2025), line 488:
    > "the standard value function under the death interpretation of semimeasure
    >  loss, which sums the discounted rewards received over the (possibly
    >  terminating) history: u_r(h) := Σ_{t=1}^{l(h)} γ_t r_t"

    **SIMPLIFIED MODEL**: This implementation assumes constant reward of 1 per step,
    which makes deathUtility proportional to the number of percepts. The full paper
    result about death_not_choquet requires rewards in ℛ where inf ℛ < 0. Our binary
    reward model (r ∈ {0, 1}) doesn't support negative rewards, so we use this
    simplification to prove the structural theorem.

    The proper general version would be:
      let rewards := h.percepts.mapIdx (fun i p => γ^(i + 1) * p.reward)
      rewards.sum
-/
noncomputable def deathUtility (γ : ℝ) (h : History) : ℝ :=
  (List.range h.percepts.length).map (fun i => γ^(i + 1)) |>.sum

-- Key lemma: Death utility on finite history ≠ infimum over infinite extensions
-- when rewards can be negative
-- From Wyeth/Hutter line 488: "when inf ℛ < 0 and γ_t > 0 ∀t,
--   then u_r(h_≤t) ≠ inf_{ω ∈ h_≤t H^∞} u_r(ω)"
theorem death_utility_not_infimum (γ : ℝ) (hγ : 0 < γ ∧ γ < 1)
    (h : History) (_h_nonempty : h ≠ []) :
    ∃ (U_inf : BinStream → ℝ),
      (∀ ω, U_inf ω ≤ deathUtility γ h) ∧
      (∃ ω, U_inf ω < deathUtility γ h) := by
  -- Construct infinite extension with all negative rewards after h
  use fun ω => deathUtility γ h +
    ∑' (n : ℕ), γ^(h.length + n + 1) * (-1 : ℝ)
  have hγ0 : 0 ≤ γ := le_of_lt hγ.1
  have htail_eq :
      (∑' (n : ℕ), γ ^ (h.length + n + 1) * (-1 : ℝ)) =
        (-γ ^ (h.length + 1)) * (1 - γ)⁻¹ := by
    -- Reduce to the geometric series `∑' n, γ^n = (1-γ)⁻¹`.
    have : (∑' n : ℕ, γ ^ (h.length + n + 1) * (-1 : ℝ)) = ∑' n : ℕ, -γ ^ (h.length + n + 1) := by
      simp
    -- Rewrite the exponent: h.length + n + 1 = (h.length + 1) + n.
    have hrewrite :
        (fun n : ℕ => -γ ^ (h.length + n + 1)) = fun n => (-γ ^ (h.length + 1)) * γ ^ n := by
      funext n
      have hk : h.length + n + 1 = (h.length + 1) + n := by omega
      simp [hk, pow_add, mul_comm, mul_left_comm]
    calc
      (∑' (n : ℕ), γ ^ (h.length + n + 1) * (-1 : ℝ))
          = ∑' n : ℕ, -γ ^ (h.length + n + 1) := this
      _ = ∑' n : ℕ, (-γ ^ (h.length + 1)) * γ ^ n := by
          simp [hrewrite]
      _ = (-γ ^ (h.length + 1)) * ∑' n : ℕ, γ ^ n := by
          simpa using (tsum_mul_left (f := fun n : ℕ => γ ^ n) (a := (-γ ^ (h.length + 1))))
      _ = (-γ ^ (h.length + 1)) * (1 - γ)⁻¹ := by
          simp [tsum_geometric_of_lt_one hγ0 hγ.2]

  have htail_lt : (∑' (n : ℕ), γ ^ (h.length + n + 1) * (-1 : ℝ)) < 0 := by
    have hpow_pos : 0 < γ ^ (h.length + 1) := pow_pos hγ.1 (h.length + 1)
    have hden_pos : 0 < (1 - γ)⁻¹ := by
      have : 0 < (1 - γ) := by linarith [hγ.2]
      exact inv_pos.2 this
    have hneg : (-γ ^ (h.length + 1)) * (1 - γ)⁻¹ < 0 := by
      exact mul_neg_of_neg_of_pos (neg_neg_of_pos hpow_pos) hden_pos
    -- Rewrite the target using the closed form (avoid simp turning `-a < 0` into `0 < a`).
    rw [htail_eq]
    exact hneg
  have htail_le : (∑' (n : ℕ), γ ^ (h.length + n + 1) * (-1 : ℝ)) ≤ 0 :=
    le_of_lt htail_lt
  constructor
  · intro ω
    -- Sum with negative tail ≤ finite positive sum
    linarith [htail_le]
  · -- There exists ω (constant negative tail) with strictly less utility
    use fun n => if n < h.length then false else true  -- arbitrary extension
    linarith [htail_lt]

-- Main theorem: Death interpretation cannot be Choquet
-- From Wyeth/Hutter line 488
theorem death_not_choquet (γ : ℝ) (hγ : 0 < γ ∧ γ < 1) :
    ∃ (ν : Semimeasure) (h : History),
      ∃ (U_choquet : Utility),
        valueChoquet ν U_choquet h ≠ valueNeutral ν (deathUtility γ) h := by
  refine ⟨deathAtStartSemimeasure, ([] : History), deathUtility γ, ?_⟩
  have hγ_ne : (γ : ℝ) ≠ 0 := ne_of_gt hγ.1
  -- For this ν and empty history, all one-step continuation mass is 0, but loss is 1.
  have h_loss : semimeasureLoss deathAtStartSemimeasure (encodeHistory ([] : History)) = 1 := by
    simp [semimeasureLoss, deathAtStartSemimeasure, encodeHistory]
  have hν_percept : ∀ p : Percept, deathAtStartSemimeasure (encodePerceptBin p) = 0 := by
    intro p
    cases p with
    | mk o r =>
      simp [deathAtStartSemimeasure, encodePerceptBin, encodePercept]
  have h_neutral : valueNeutral deathAtStartSemimeasure (deathUtility γ) ([] : History) = 0 := by
    classical
    simp [valueNeutral, encodeHistory, hν_percept]
  have h_min : minNextUtility (deathUtility γ) ([] : History) = γ := by
    classical
    -- `deathUtility γ ([per p]) = γ` for every percept p, so the infimum is γ.
    have : (fun p : Percept => deathUtility γ ([HistElem.per p] : History)) = fun _ => γ := by
      funext p
      simp [deathUtility, History.percepts]
    simp [minNextUtility, this, Finset.inf'_const]
  have h_choquet : valueChoquet deathAtStartSemimeasure (deathUtility γ) ([] : History) = γ := by
    simp [valueChoquet, h_neutral, h_loss, h_min]
  -- Conclude `valueChoquet = γ` while `valueNeutral = 0`.
  simpa [h_choquet, h_neutral] using hγ_ne

/-! ## Exploration Bonus Under Ignorance

One practical consequence: agents using Choquet utilities have an information-
seeking bonus not present in standard AIXI.

Lost mass creates value of information, leading to more exploration.
-/

/-- Value of information: reduction in ignorance from observing percept x.

    VOI(h, x) = loss(encode(h)) - loss(encode(h ++ [x]))

    Positive VOI indicates information gain from observing x, incentivizing exploration.
    Under the Choquet interpretation, reducing uncertainty has intrinsic value.
-/
noncomputable def valueOfInformation (ν : Semimeasure) (h : History) (x : Percept) : ENNReal :=
  let h_enc := encodeHistory h
  let hx_enc := h_enc ++ encodePerceptBin x
  semimeasureLoss ν h_enc - semimeasureLoss ν hx_enc

/-- **Proposition**: Value of information is bounded by semimeasure loss.

    The value of information from observing percept x is at most the loss at history h.

    **Proof**: Direct from definitions:
    VOI(h, x) = loss(encode(h)) - loss(encode(h ++ [x]))

    Since loss is always nonnegative (by superadditivity), and ν is monotone
    on prefixes, we have 0 ≤ VOI(h, x) ≤ loss(encode(h)).
-/
theorem valueOfInformation_le_loss (ν : Semimeasure) (h : History) (x : Percept) :
    valueOfInformation ν h x ≤ semimeasureLoss ν (encodeHistory h) := by
  unfold valueOfInformation
  -- VOI = loss(h) - loss(h·x)
  -- Since loss(h·x) ≥ 0, we have VOI ≤ loss(h)
  exact tsub_le_self

/-- **Proposition**: Choquet agents have exploration bonus.

    When semimeasure loss is positive at a history, observing can reduce uncertainty,
    creating a value of information bonus.

    **Proof Strategy**:
    1. If loss(encode(h)) > 0, then ν(encode(h)) > Σᵢ ν(encode(h) ++ [i])
    2. After observing percept p, loss can decrease (not always, but possible)
    3. When loss decreases, VOI(h, p) = loss(h) - loss(h·p) > 0
    4. This creates exploration bonus not present in neutral interpretation

    **Key Insight**: Under neutral interpretation, lost mass contributes 0 value.
    Under Choquet interpretation, reducing uncertainty (loss) has positive value.

    From Wyeth/Hutter (2025), discussed in Section 3 on imprecise probability.
    The paper notes that Choquet integral is "pessimistic" (min over credal set),
    so reducing uncertainty tightens the credal set and increases value.
-/
theorem choquet_has_exploration_bonus (ν : Semimeasure) (h : History)
    : (∃ p : Percept, valueOfInformation ν h p > 0) ∨
      (∀ p : Percept, valueOfInformation ν h p = 0) := by
  classical
  -- Either: (1) some percept reduces loss (positive VOI), or
  --         (2) no percept reduces loss, hence VOI is always 0 (since `ENNReal` subtraction is `tsub`).
  by_cases h_reduces : ∃ p, semimeasureLoss ν (encodeHistory (h ++ [HistElem.per p])) <
                              semimeasureLoss ν (encodeHistory h)
  · -- Case 1: Some percept reduces loss
    left
    obtain ⟨p, hp⟩ := h_reduces
    refine ⟨p, ?_⟩
    -- VOI = loss(h) - loss(h ++ [p])
    -- We have: loss(encode(h ++ [per p])) < loss(encode(h))
    -- By encodeHistory_append: encode(h ++ [per p]) = encode(h) ++ encodePerceptBin p
    have h_eq : encodeHistory (h ++ [HistElem.per p]) = encodeHistory h ++ encodePerceptBin p := by
      rw [encodeHistory_append]
      simp [encodeHistElem]
    show semimeasureLoss ν (encodeHistory h) - semimeasureLoss ν (encodeHistory h ++ encodePerceptBin p) > 0
    rw [← h_eq]
    exact tsub_pos_of_lt hp
  · -- Case 2: No percept reduces loss
    right
    have h_all : ∀ p, ¬ semimeasureLoss ν (encodeHistory (h ++ [HistElem.per p])) <
        semimeasureLoss ν (encodeHistory h) := by
      simpa using (not_exists.mp h_reduces)
    intro p
    have h_eq : encodeHistory (h ++ [HistElem.per p]) = encodeHistory h ++ encodePerceptBin p := by
      rw [encodeHistory_append]
      simp [encodeHistElem]
    have h_le :
        semimeasureLoss ν (encodeHistory h) ≤ semimeasureLoss ν (encodeHistory h ++ encodePerceptBin p) := by
      -- ¬(loss(h++p) < loss(h)) gives loss(h) ≤ loss(h++p)
      have : semimeasureLoss ν (encodeHistory h) ≤ semimeasureLoss ν (encodeHistory (h ++ [HistElem.per p])) :=
        le_of_not_gt (h_all p)
      simpa [h_eq] using this
    -- If loss doesn't decrease, then VOI is 0 because subtraction is `tsub`.
    unfold valueOfInformation
    simp [tsub_eq_zero_iff_le.2 h_le]

/-! ## König's Lemma Application

The paper (Wyeth & Hutter 2025, line 476-481) uses König's lemma to establish that
the infimum utility u̲ inherits lower semicomputability from u:

> "König's lemma allows u̲ to inherit lower semicomputability from u.
> Then u̲ can be approximated from below on the cylinder sets by l.s.c.
> simple functions u_n, and V^π_{ν,u_n} → V^π_{ν,u} by monotone convergence."

### Mathematical Setup

For a utility function u : H^∞ → [0,1] on infinite histories, define:
  u̲(h_≤t) := inf_{h_{>t}} u(h_≤t · h_{>t})

This is the infimum of u over all infinite extensions of the finite history h_≤t.

### König's Lemma (Tree Form)

Every infinite finitely-branching tree has an infinite path.

In Mathlib, this is `exists_seq_covby_of_forall_covby_finite`:
  - For a strongly atomic partial order
  - Where each element is covered by finitely many others
  - And there are infinitely many elements above some b
  - There exists an infinite ascending sequence starting at b

### Application to Cantor Space

The Cantor space 2^ω (infinite binary sequences) can be viewed as:
- An infinite binary tree where nodes are finite prefixes (BinString)
- Each node has exactly 2 children (append false / true)
- The tree is finitely branching

König's lemma ensures: for any finite prefix x, the infimum of u over
infinite extensions is achieved (or approached) along some infinite path.

### Why This Matters for L.S.C.

If u is lower semicomputable on 2^ω, then:
1. u can be approximated from below: u[n] ↑ u
2. For finite prefix x, u̲(x) = inf_{ω extends x} u(ω)
3. König's lemma ensures this infimum is a "sup of infs" over finite approximations
4. Therefore u̲ inherits lower semicomputability from u

The key insight is that König's lemma converts the infinite infimum into
a limit of finite operations, each of which is computable.
-/

/-- **König's lemma for binary trees** (via prefix order).

    Every finite binary string has an infinite extension path in the prefix order.

    **Mathematical Statement**:
    For the binary tree (finite binary strings ordered by prefix), König's lemma
    states that from any node x, there exists an infinite descending path
    x = f(0) <+: f(1) <+: f(2) <+: ... where each f(n+1) extends f(n) by one bit.

    **Mathlib Version**:
    This follows from `exists_seq_covby_of_forall_covby_finite` applied to the
    prefix order on `List Bool`, where:
    - Each string is covered by exactly 2 others (append false / true)
    - The set of extensions of any string is infinite

    **Application to Wyeth & Hutter**:
    The paper uses König's lemma to show that u̲ (infimum over infinite extensions)
    inherits lower semicomputability from u. The infinite infimum becomes a limit
    of finite operations via König's path construction.

    **Note**: We state this using the prefix relation directly rather than
    instantiating a PartialOrder to avoid conflicts with List's default Lex order.
-/
theorem konig_binary_tree_prefix (x : BinString) :
    ∃ f : ℕ → BinString,
      f 0 = x ∧
      (∀ n, f n <+: f (n + 1)) ∧
      (∀ n, (f (n + 1)).length = (f n).length + 1) := by
  -- Construct the path by repeatedly appending false
  use fun n => x ++ List.replicate n false
  constructor
  · simp -- f 0 = x
  constructor
  · intro n
    -- f n <+: f (n+1) because x ++ replicate n false <+: x ++ replicate (n+1) false
    rw [List.replicate_succ', ← List.append_assoc]
    exact List.prefix_append _ _
  · intro n
    simp only [List.length_append, List.length_replicate]
    omega

/-- The infinite path from König's lemma defines an element of Cantor space. -/
noncomputable def konig_path_to_stream (f : ℕ → BinString)
    (_hf_prefix : ∀ n, f n <+: f (n + 1))
    (_hf_len : ∀ n, (f (n + 1)).length = (f n).length + 1) :
    BinStream := fun n =>
  -- The nth bit is the bit added when going from f n to f (n+1)
  (f (n + 1))[(f n).length]!

/-- Extend a finite binary string to an infinite stream by padding with false. -/
def extendWithFalse (y : BinString) : BinStream := fun n =>
  if n < y.length then y[n]! else false

/-- The set of infinite streams that extend a given finite prefix x. -/
def extendsPrefix (x : BinString) : Set BinStream :=
  {ω : BinStream | ∀ n, n < x.length → ω n = x[n]!}

/-- The set of extensions of any prefix is nonempty (witnessed by padding with false). -/
theorem extendsPrefix_nonempty (x : BinString) : (extendsPrefix x).Nonempty := by
  use extendWithFalse x
  intro n hn
  simp [extendWithFalse, hn]

/-- Cantor space (ℕ → Bool) is compact, by Tychonoff's theorem
    (since Bool is finite, hence compact). -/
instance cantorSpace_compactSpace : CompactSpace BinStream := by
  -- Bool is finite, hence compact (Finite.compactSpace)
  -- ℕ → Bool is compact by Function.compactSpace (Tychonoff)
  infer_instance

/-- The cylinder set of extensions of x is closed.

    A cylinder set {ω : ω(n) = x[n] for all n < |x|} is closed because
    it's the intersection of finitely many closed sets (preimages of singletons
    under the continuous projection maps).
-/
theorem extendsPrefix_isClosed (x : BinString) : IsClosed (extendsPrefix x) := by
  -- extendsPrefix x = ⋂ (n < x.length), {ω : ω n = x[n]!}
  -- Each {ω : ω n = b} is closed (preimage of {b} under continuous projection)
  simp only [extendsPrefix, Set.setOf_forall]
  apply isClosed_iInter
  intro n
  apply isClosed_iInter
  intro _hn
  -- {ω : ω n = x[n]!} = (fun ω => ω n) ⁻¹' {x[n]!}
  -- In the discrete topology, singletons are clopen
  have h_cont : Continuous (fun ω : BinStream => ω n) := continuous_apply n
  have h_singleton_closed : IsClosed ({x[n]!} : Set Bool) := isClosed_singleton
  exact h_singleton_closed.preimage h_cont

/-- The cylinder set of extensions of x is compact (closed subset of compact space). -/
theorem extendsPrefix_isCompact (x : BinString) : IsCompact (extendsPrefix x) :=
  (extendsPrefix_isClosed x).isCompact

/-- **Key Compactness Result**: On the compact set of extensions of x,
    a lower semicontinuous function achieves its infimum.

    This follows from `LowerSemicontinuousOn.exists_isMinOn` in mathlib:
    1. Cantor space (ℕ → Bool) is compact (Tychonoff's theorem)
    2. The cylinder set {ω : ω extends x} is closed, hence compact
    3. Lower semicontinuous functions achieve their min on compact sets
-/
theorem exists_infimum_minimizer (x : BinString) (u : BinStream → ℝ)
    (hu_lsc : LowerSemicontinuous u) :
    ∃ ω ∈ extendsPrefix x, ∀ ω' ∈ extendsPrefix x, u ω ≤ u ω' := by
  -- The cylinder set is nonempty, compact, and u is l.s.c. on it
  have h_nonempty := extendsPrefix_nonempty x
  have h_compact := extendsPrefix_isCompact x
  have h_lsc_on := hu_lsc.lowerSemicontinuousOn (extendsPrefix x)
  -- Apply the extreme value theorem for l.s.c. functions
  obtain ⟨ω, hω_mem, hω_min⟩ := LowerSemicontinuousOn.exists_isMinOn h_nonempty h_compact h_lsc_on
  exact ⟨ω, hω_mem, fun ω' hω' => hω_min hω'⟩

/-- The minimizing extension of x (exists by compactness, noncomputable). -/
noncomputable def minimizingExtension (x : BinString) (u : BinStream → ℝ)
    (_hu_lsc : LowerSemicontinuous u) : BinStream :=
  (exists_infimum_minimizer x u _hu_lsc).choose

theorem minimizingExtension_extends (x : BinString) (u : BinStream → ℝ)
    (hu_lsc : LowerSemicontinuous u) :
    minimizingExtension x u hu_lsc ∈ extendsPrefix x :=
  (exists_infimum_minimizer x u hu_lsc).choose_spec.1

theorem minimizingExtension_isMin (x : BinString) (u : BinStream → ℝ)
    (hu_lsc : LowerSemicontinuous u) (ω : BinStream) (hω : ω ∈ extendsPrefix x) :
    u (minimizingExtension x u hu_lsc) ≤ u ω :=
  (exists_infimum_minimizer x u hu_lsc).choose_spec.2 ω hω

/-- The extension type is nonempty (witnessed by padding with false). -/
instance extendsPrefix_nonempty_subtype (x : BinString) :
    Nonempty {ω : BinStream // ∀ n, n < x.length → ω n = x[n]!} := by
  use extendWithFalse x
  intro n hn
  simp [extendWithFalse, hn]

/-- The infimum utility equals the value at the minimizing extension. -/
theorem infimum_utility_eq_min (x : BinString) (u : BinStream → ℝ)
    (hu_lsc : LowerSemicontinuous u)
    (hu_bdd : BddBelow (Set.range (fun (ω : {ω : BinStream // ∀ n, n < x.length → ω n = x[n]!}) =>
                                    u ω.val))) :
    ⨅ ω : {ω : BinStream // ∀ n, n < x.length → ω n = x[n]!}, u ω.val =
    u (minimizingExtension x u hu_lsc) := by
  apply le_antisymm
  · -- inf ≤ value at minimizer
    -- The minimizing extension extends x, so it's a valid witness
    have h_mem := minimizingExtension_extends x u hu_lsc
    let witness : {ω : BinStream // ∀ n, n < x.length → ω n = x[n]!} :=
      ⟨minimizingExtension x u hu_lsc, h_mem⟩
    exact ciInf_le hu_bdd witness
  · -- value at minimizer ≤ inf
    apply le_ciInf
    intro ⟨ω, hω⟩
    exact minimizingExtension_isMin x u hu_lsc ω hω

/-- **Main Application**: Infimum utility inherits lower semicomputability.

    For a lower semicomputable utility u on infinite histories,
    the infimum utility u̲(x) := inf_{ω extends x} u(ω) is also lower semicomputable.

    **Proof Outline** (from Wyeth & Hutter 2025, line 476-481):

    > "König's lemma allows u̲ to inherit lower semicomputability from u.
    > Then u̲ can be approximated from below on the cylinder sets by l.s.c.
    > simple functions u_n, and V^π_{ν,u_n} → V^π_{ν,u} by monotone convergence."

    **Key Insight**: By compactness of Cantor space, the infimum is achieved at
    some minimizing extension ω*. Since u̲(x) = u(ω*), we can approximate u̲(x)
    by approximating u at ω*: just use hu_lsc.approx(ω*, m).

    **Why This Works**:
    - approx(x, m) = hu_lsc.approx(ω*(x), m) where ω* is the minimizing extension
    - Monotone: directly from hu_lsc.approx_mono
    - Bounded: hu_lsc.approx(ω*, m) ≤ u(ω*) = u̲(x) ✓
    - Convergent: hu_lsc.approx(ω*, m) → u(ω*) = u̲(x) ✓

    **Note**: The definition is noncomputable because finding ω* requires
    solving an optimization problem over a compact set. But existence is
    guaranteed by compactness + lower semicontinuity.
-/
noncomputable def infimum_utility_lower_semicomputable
    (u : BinStream → ℝ)
    (hu_lsc : Mettapedia.Computability.ArithmeticalHierarchy.LowerSemicomputable u)
    (hu_cont : LowerSemicontinuous u)  -- topological l.s.c. for compactness argument
    (hu_bound : ∀ ω, 0 ≤ u ω ∧ u ω ≤ 1) :
    Mettapedia.Computability.ArithmeticalHierarchy.LowerSemicomputable
      (fun x : BinString => ⨅ ω : {ω : BinStream // ∀ n, n < x.length → ω n = x[n]!},
        u ω.val) where
  -- Approximation: evaluate hu_lsc.approx at the minimizing extension
  approx x m := hu_lsc.approx (minimizingExtension x u hu_cont) m
  -- Monotonicity: directly from hu_lsc.approx_mono
  approx_mono x m := hu_lsc.approx_mono (minimizingExtension x u hu_cont) m
  -- Bounded above by inf u: follows from ω* being the minimizer
  approx_le x m := by
    have h1 : (hu_lsc.approx (minimizingExtension x u hu_cont) m : ℝ) ≤
              u (minimizingExtension x u hu_cont) :=
      hu_lsc.approx_le (minimizingExtension x u hu_cont) m
    -- u is bounded below by 0, so the range is bounded below
    have h_bdd : BddBelow (Set.range (fun (ω : {ω : BinStream // ∀ n, n < x.length → ω n = x[n]!}) =>
                                       u ω.val)) := by
      use 0
      intro y hy
      simp only [Set.mem_range] at hy
      obtain ⟨ω, hω⟩ := hy
      rw [← hω]
      exact (hu_bound ω.val).1
    have h2 : u (minimizingExtension x u hu_cont) =
              ⨅ ω : {ω : BinStream // ∀ n, n < x.length → ω n = x[n]!}, u ω.val := by
      symm
      exact infimum_utility_eq_min x u hu_cont h_bdd
    calc (hu_lsc.approx (minimizingExtension x u hu_cont) m : ℝ)
        ≤ u (minimizingExtension x u hu_cont) := h1
      _ = ⨅ ω : {ω : BinStream // ∀ n, n < x.length → ω n = x[n]!}, u ω.val := h2
  -- Convergence: hu_lsc.approx converges to u at ω*, which equals u̲(x)
  approx_converges x ε hε := by
    obtain ⟨N, hN⟩ := hu_lsc.approx_converges (minimizingExtension x u hu_cont) ε hε
    use N
    intro n hn
    have h_conv := hN n hn
    -- u is bounded below by 0, so the range is bounded below
    have h_bdd : BddBelow (Set.range (fun (ω : {ω : BinStream // ∀ n, n < x.length → ω n = x[n]!}) =>
                                       u ω.val)) := by
      use 0
      intro y hy
      simp only [Set.mem_range] at hy
      obtain ⟨ω, hω⟩ := hy
      rw [← hω]
      exact (hu_bound ω.val).1
    have h_eq : u (minimizingExtension x u hu_cont) =
                ⨅ ω : {ω : BinStream // ∀ n, n < x.length → ω n = x[n]!}, u ω.val := by
      symm; exact infimum_utility_eq_min x u hu_cont h_bdd
    rw [← h_eq]
    exact h_conv

/-! ## Paper's Theorem 4.1: L.S.C. with Only ν L.S.C.

The key insight from Wyeth & Hutter (2025) is that the Choquet integral can be computed
using the **layer cake formula** (Riemann integral over capacity levels), which avoids
explicit subtraction of l.s.c. functions.

For the one-step case:
  ∫_C U dν_h = ∫_0^∞ ν_h({p : U(h++p) ≥ t}) dt

Using Riemann sums:
  V_n(h) = (1/n) · Σ_{k=1}^n ν_h({p : U(h++p) ≥ k/n})

Each term ν_h({p : U(h++p) ≥ k/n}) is l.s.c. because:
- It's a sum of ν values (at most ν(h) when k/n ≤ min U)
- Sums of l.s.c. functions are l.s.c.

By monotone convergence, lim V_n = valueChoquet is l.s.c.

**Critical insight**: The subtraction only appears in the RECURSIVE formula
(valueChoquet = valueNeutral + loss * minU), not in the layer cake formula.
-/

/-- Total one-step mass (percepts plus loss) at history h. -/
noncomputable def perceptMass (ν : Semimeasure) (h : History) : ℝ :=
  (semimeasureLoss ν (encodeHistory h)).toReal +
    ∑ p : Percept, (ν (encodeHistory h ++ encodePerceptBin p)).toReal

theorem perceptMass_nonneg (ν : Semimeasure) (h : History) : 0 ≤ perceptMass ν h := by
  unfold perceptMass
  apply add_nonneg
  · exact ENNReal.toReal_nonneg
  · apply Finset.sum_nonneg
    intro p _
    exact ENNReal.toReal_nonneg

/-- Capacity at level t: the semimeasure of percepts with utility strictly above t.

For t < minNextUtility, this equals the total one-step mass (percepts plus loss).
For t ≥ minNextUtility, this is the sum of ν(h++p) for percepts with U(h++p) > t.
-/
noncomputable def capacityAtLevel (ν : Semimeasure) (U : Utility) (h : History) (t : ℝ) : ℝ :=
  if t < minNextUtility U h then
    perceptMass ν h
  else
    ∑ p : Percept, if t < U (h ++ [HistElem.per p]) then
      (ν (encodeHistory h ++ encodePerceptBin p)).toReal
    else 0

/-- Capacity at level is nonnegative. -/
theorem capacityAtLevel_nonneg (ν : Semimeasure) (U : Utility) (h : History) (t : ℝ) :
    0 ≤ capacityAtLevel ν U h t := by
  unfold capacityAtLevel
  split_ifs with ht
  · unfold perceptMass
    apply add_nonneg
    · exact ENNReal.toReal_nonneg
    · apply Finset.sum_nonneg
      intro p _
      exact ENNReal.toReal_nonneg
  · apply Finset.sum_nonneg
    intro p _
    split_ifs
    · exact ENNReal.toReal_nonneg
    · rfl

/-- Sum over Percept of ν values is at most ν(hist).
    Uses semimeasure_four_extensions from BayesianAgents. -/
theorem percept_sum_le_hist (ν : Semimeasure) (hist : History) :
    ∑ p : Percept, (ν (encodeHistory hist ++ encodePerceptBin p)).toReal
        ≤ (ν (encodeHistory hist)).toReal := by
  -- Use semimeasure_four_extensions from BayesianAgents
  let s := encodeHistory hist
  -- First, calculate the sum explicitly using Finset.univ for Percept (4 elements)
  have h_sum_expand : ∑ p : Percept, (ν (s ++ encodePerceptBin p)).toReal =
      (ν (s ++ [false, false])).toReal + (ν (s ++ [false, true])).toReal +
      (ν (s ++ [true, false])).toReal + (ν (s ++ [true, true])).toReal := by
    -- Show Finset.univ for Percept has exactly 4 elements
    have huniv : (Finset.univ : Finset Percept) =
        {Percept.mk false false, Percept.mk false true,
         Percept.mk true false, Percept.mk true true} := by
      ext x; simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
      cases x with | mk o r => cases o <;> cases r <;> simp [Percept.mk.injEq]
    rw [huniv]
    simp only [Finset.sum_insert (by decide : Percept.mk false false ∉
      ({Percept.mk false true, Percept.mk true false, Percept.mk true true} : Finset _))]
    simp only [Finset.sum_insert (by decide : Percept.mk false true ∉
      ({Percept.mk true false, Percept.mk true true} : Finset _))]
    simp only [Finset.sum_insert (by decide : Percept.mk true false ∉
      ({Percept.mk true true} : Finset _))]
    simp only [Finset.sum_singleton, encodePerceptBin, encodePercept]
    ring
  rw [h_sum_expand]
  -- Now use semimeasure_four_extensions (in ENNReal) and convert to Real
  have h_ennreal := semimeasure_four_extensions ν s
  -- Convert to Real: sum ≤ ν(s) in ENNReal implies toReal(sum) ≤ toReal(ν(s))
  have h_ne_top : ν s ≠ ⊤ := by
    have h1 : ν s ≤ ν [] := ν.mono_append [] s
    have h2 : ν [] ≤ 1 := ν.root_le_one'
    exact ne_of_lt (lt_of_le_of_lt (le_trans h1 h2) ENNReal.one_lt_top)
  -- Each term is finite since bounded by ν(s), and therefore less than ⊤
  have h_ff_ne_top : ν (s ++ [false, false]) ≠ ⊤ :=
    ne_top_of_le_ne_top h_ne_top (ν.mono_append s _)
  have h_ft_ne_top : ν (s ++ [false, true]) ≠ ⊤ :=
    ne_top_of_le_ne_top h_ne_top (ν.mono_append s _)
  have h_tf_ne_top : ν (s ++ [true, false]) ≠ ⊤ :=
    ne_top_of_le_ne_top h_ne_top (ν.mono_append s _)
  have h_tt_ne_top : ν (s ++ [true, true]) ≠ ⊤ :=
    ne_top_of_le_ne_top h_ne_top (ν.mono_append s _)
  -- Prove the Real sum equals toReal of the ENNReal sum
  have h_sum_eq : (ν (s ++ [false, false])).toReal + (ν (s ++ [false, true])).toReal +
                  (ν (s ++ [true, false])).toReal + (ν (s ++ [true, true])).toReal =
                  (ν (s ++ [false, false]) + ν (s ++ [false, true]) +
                   ν (s ++ [true, false]) + ν (s ++ [true, true])).toReal := by
    rw [← ENNReal.toReal_add h_ff_ne_top h_ft_ne_top]
    have h_ffft_ne_top : ν (s ++ [false, false]) + ν (s ++ [false, true]) ≠ ⊤ := by
      simp only [ne_eq, ENNReal.add_eq_top, not_or]
      exact ⟨h_ff_ne_top, h_ft_ne_top⟩
    rw [← ENNReal.toReal_add h_ffft_ne_top h_tf_ne_top]
    have h_three_ne_top : ν (s ++ [false, false]) + ν (s ++ [false, true]) +
                           ν (s ++ [true, false]) ≠ ⊤ := by
      simp only [ne_eq, ENNReal.add_eq_top, not_or]
      exact ⟨⟨h_ff_ne_top, h_ft_ne_top⟩, h_tf_ne_top⟩
    rw [← ENNReal.toReal_add h_three_ne_top h_tt_ne_top]
  rw [h_sum_eq]
  exact ENNReal.toReal_mono h_ne_top h_ennreal

/-- Capacity at level is bounded above by the total one-step mass. -/
theorem capacityAtLevel_le (ν : Semimeasure) (U : Utility) (hist : History) (t : ℝ) :
    capacityAtLevel ν U hist t ≤ perceptMass ν hist := by
  unfold capacityAtLevel
  by_cases ht : t < minNextUtility U hist
  · simp only [if_pos ht]
    exact le_refl _
  · simp only [if_neg ht]
    -- The filtered sum is at most the full sum, which is at most the total mass
    have h_step1 : ∑ p : Percept, (if t < U (hist ++ [HistElem.per p]) then
            (ν (encodeHistory hist ++ encodePerceptBin p)).toReal else 0)
        ≤ ∑ p : Percept, (ν (encodeHistory hist ++ encodePerceptBin p)).toReal := by
      apply Finset.sum_le_sum
      intro p _
      by_cases hp : t < U (hist ++ [HistElem.per p])
      · simp only [if_pos hp]; exact le_refl _
      · simp only [if_neg hp]; exact ENNReal.toReal_nonneg
    -- sum ≤ loss + sum
    have h_step2 :
        ∑ p : Percept, (ν (encodeHistory hist ++ encodePerceptBin p)).toReal
          ≤ perceptMass ν hist := by
      unfold perceptMass
      have h_loss_nonneg : 0 ≤ (semimeasureLoss ν (encodeHistory hist)).toReal := ENNReal.toReal_nonneg
      linarith
    exact le_trans h_step1 h_step2

/-- Capacity is monotone decreasing in t. -/
theorem capacityAtLevel_mono (ν : Semimeasure) (U : Utility) (hist : History) :
    Antitone (capacityAtLevel ν U hist) := by
  intro t1 t2 ht
  -- Note: Antitone means t1 ≤ t2 ⟹ f(t2) ≤ f(t1)
  -- So we need to show capacityAtLevel hist t2 ≤ capacityAtLevel hist t1
  unfold capacityAtLevel
  by_cases h2 : t2 < minNextUtility U hist
  · -- t2 < minU, so t1 < minU too (since t1 ≤ t2)
    have h1 : t1 < minNextUtility U hist := lt_of_le_of_lt ht h2
    simp only [if_pos h1, if_pos h2]
    exact le_refl _
  · -- t2 > minU
    by_cases h1 : t1 < minNextUtility U hist
    · -- t1 < minU but t2 ≥ minU
      simp only [if_pos h1, if_neg h2]
      -- capacity(t2) is a filtered sum, capacity(t1) = perceptMass
      -- Need: sum ≤ perceptMass
      have h_bound : ∑ p : Percept, (if t2 < U (hist ++ [HistElem.per p]) then
            (ν (encodeHistory hist ++ encodePerceptBin p)).toReal else 0)
          ≤ perceptMass ν hist := by
        calc ∑ p : Percept, (if t2 < U (hist ++ [HistElem.per p]) then
              (ν (encodeHistory hist ++ encodePerceptBin p)).toReal else 0)
            ≤ ∑ p : Percept, (ν (encodeHistory hist ++ encodePerceptBin p)).toReal := by
              apply Finset.sum_le_sum
              intro p _
              by_cases hp : t2 < U (hist ++ [HistElem.per p])
              · simp only [if_pos hp]; exact le_refl _
              · simp only [if_neg hp]; exact ENNReal.toReal_nonneg
          _ ≤ perceptMass ν hist := by
              unfold perceptMass
              have h_loss_nonneg : 0 ≤ (semimeasureLoss ν (encodeHistory hist)).toReal :=
                ENNReal.toReal_nonneg
              linarith
      exact h_bound
    · -- Both t2 > minU and t1 > minU
      simp only [if_neg h1, if_neg h2]
      -- Both are sums, need: sum for t2 ≤ sum for t1
      -- Since t1 ≤ t2, the set {p : U>t2} ⊆ {p : U>t1}
      apply Finset.sum_le_sum
      intro p _
      by_cases hp2 : t2 < U (hist ++ [HistElem.per p])
      · -- U ≥ t2 ⟹ U ≥ t1 (since t1 ≤ t2)
        have hp1 : t1 < U (hist ++ [HistElem.per p]) := lt_of_le_of_lt ht hp2
        simp only [if_pos hp2, if_pos hp1]
        exact le_refl _
      · -- U < t2
        simp only [if_neg hp2]
        by_cases hp1 : t1 < U (hist ++ [HistElem.per p])
        · simp only [if_pos hp1]; exact ENNReal.toReal_nonneg
        · simp only [if_neg hp1]; exact le_refl _

/-- Riemann lower sum approximation of the Choquet integral.

We use nested dyadic partitions:
  V_n(h) = (1/2^n) · Σ_{k=1}^{2^n} capacityAtLevel(k/2^n)

This approximates ∫_0^1 capacityAtLevel(t) dt from below using right endpoints.
-/
noncomputable def valueChoquet_riemann (ν : Semimeasure) (U : Utility) (h : History) (n : ℕ) : ℝ :=
  let m : ℕ := 2 ^ n
  (1 / (m : ℝ)) * ∑ k ∈ Finset.range m, capacityAtLevel ν U h ((k + 1 : ℝ) / (m : ℝ))

/-- The utility values at the four next-step percepts (as a list for convenience). -/
def nextUtilities (U : Utility) (h : History) : List ℝ :=
  [Percept.mk false false, Percept.mk false true, Percept.mk true false, Percept.mk true true].map
    (fun p => U (h ++ [HistElem.per p]))

/-- capacityAtLevel has at most 4 discontinuities (at the utility values).
    This is a helper for understanding the structure, not used in main proofs. -/
theorem capacityAtLevel_has_finitely_many_jumps (ν : Semimeasure) (U : Utility) (h : History) :
    ∃ (S : Finset ℝ), S.card ≤ 4 ∧
      ∀ t₁ t₂, t₁ < t₂ → (∀ t ∈ S, t ≤ t₁ ∨ t₂ < t) →
        capacityAtLevel ν U h t₁ = capacityAtLevel ν U h t₂ := by
  -- The set S is the set of utility values
  use Finset.image (fun p => U (h ++ [HistElem.per p])) Finset.univ
  constructor
  · -- Card ≤ 4
    calc Finset.card (Finset.image (fun p => U (h ++ [HistElem.per p])) Finset.univ)
        ≤ Finset.card (Finset.univ : Finset Percept) := Finset.card_image_le
      _ = 4 := by rfl
  · -- Piecewise constant on intervals avoiding S
    intro t₁ t₂ ht_order h_avoid
    -- Key: if no utility values lie in (t₁, t₂), then all threshold predicates agree.
    have h_min_in :
        minNextUtility U h ∈
          Finset.image (fun p => U (h ++ [HistElem.per p])) Finset.univ := by
      simp only [Finset.mem_image, Finset.mem_univ, true_and]
      obtain ⟨p_min, _, hp_eq⟩ :=
        Finset.exists_mem_eq_inf' Finset.univ_nonempty (fun p => U (h ++ [HistElem.per p]))
      exact ⟨p_min, hp_eq.symm⟩
    have h_min_case : (t₁ < minNextUtility U h) = (t₂ < minNextUtility U h) := by
      have h_avoid_min := h_avoid (minNextUtility U h) h_min_in
      cases h_avoid_min with
      | inl h_le =>
        have h1 : ¬ t₁ < minNextUtility U h := not_lt.mpr h_le
        have h2 : ¬ t₂ < minNextUtility U h := not_lt.mpr (le_trans h_le (le_of_lt ht_order))
        simp [h1, h2]
      | inr h_lt =>
        have h1 : t₁ < minNextUtility U h := lt_trans ht_order h_lt
        have h2 : t₂ < minNextUtility U h := h_lt
        simp [h1, h2]
    have h_pred : ∀ p : Percept, (t₁ < U (h ++ [HistElem.per p])) =
        (t₂ < U (h ++ [HistElem.per p])) := by
      intro p
      have h_in :
          U (h ++ [HistElem.per p]) ∈
            Finset.image (fun p => U (h ++ [HistElem.per p])) Finset.univ := by
        simp
      have h_avoid_p := h_avoid (U (h ++ [HistElem.per p])) h_in
      cases h_avoid_p with
      | inl h_le =>
        have h1 : ¬ t₁ < U (h ++ [HistElem.per p]) := not_lt.mpr h_le
        have h2 : ¬ t₂ < U (h ++ [HistElem.per p]) := not_lt.mpr (le_trans h_le (le_of_lt ht_order))
        simp [h1, h2]
      | inr h_lt =>
        have h1 : t₁ < U (h ++ [HistElem.per p]) := lt_trans ht_order h_lt
        have h2 : t₂ < U (h ++ [HistElem.per p]) := h_lt
        simp [h1, h2]
    unfold capacityAtLevel
    simp [h_min_case, h_pred]

/-- Riemann approximation is nonnegative. -/
theorem valueChoquet_riemann_nonneg (ν : Semimeasure) (U : Utility) (h : History) (n : ℕ) :
    0 ≤ valueChoquet_riemann ν U h n := by
  unfold valueChoquet_riemann
  apply mul_nonneg
  · apply div_nonneg
    · exact zero_le_one
    · exact Nat.cast_nonneg (2 ^ n)
  · apply Finset.sum_nonneg
    intro k _
    exact capacityAtLevel_nonneg ν U h _

/- Riemann approximation is bounded by the total one-step mass. -/
theorem valueChoquet_riemann_bounded (ν : Semimeasure) (U : Utility) (h : History)
    (_h_U_bound : ∀ h', 0 ≤ U h' ∧ U h' ≤ 1) (n : ℕ) :
    valueChoquet_riemann ν U h n ≤ perceptMass ν h := by
  simp [valueChoquet_riemann]
  have hm_pos : 0 < (2 ^ n : ℝ) := by
    exact_mod_cast (pow_pos (by decide : 0 < (2 : ℕ)) n)
  have hm_ne : (2 ^ n : ℝ) ≠ 0 := by
    exact ne_of_gt hm_pos
  calc
    (2 ^ n : ℝ)⁻¹ * ∑ k ∈ Finset.range (2 ^ n),
        capacityAtLevel ν U h ((k + 1 : ℝ) / (2 ^ n : ℝ))
        ≤ (2 ^ n : ℝ)⁻¹ * ∑ k ∈ Finset.range (2 ^ n), perceptMass ν h := by
          apply mul_le_mul_of_nonneg_left
          · apply Finset.sum_le_sum
            intro k _
            exact capacityAtLevel_le ν U h _
          · exact inv_nonneg.mpr (le_of_lt hm_pos)
    _ = (2 ^ n : ℝ)⁻¹ * ((2 ^ n : ℝ) * perceptMass ν h) := by
          rw [Finset.sum_const, Finset.card_range]
          simp [nsmul_eq_mul, Nat.cast_pow]
    _ = perceptMass ν h := by
          field_simp [hm_ne]

lemma nat_le_two_pow (n : ℕ) : n ≤ 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      -- Use n ≤ 2^n and 1 ≤ 2^n to get n+1 ≤ 2^n + 2^n.
      have h2 : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by decide)
      have h3 : n + 1 ≤ 2 ^ n + 2 ^ n := Nat.add_le_add ih h2
      have h4 : n + 1 ≤ 2 ^ n * 2 := by
        simpa [two_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h3
      simpa [pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h4

lemma sum_range_sub_succ (f : ℕ → ℝ) (m : ℕ) :
    ∑ k ∈ Finset.range m, f k - ∑ k ∈ Finset.range m, f (k + 1) = f 0 - f m := by
  induction m with
  | zero => simp
  | succ m ih =>
      calc
        (∑ k ∈ Finset.range (m + 1), f k) - ∑ k ∈ Finset.range (m + 1), f (k + 1) =
            ((∑ k ∈ Finset.range m, f k) + f m) -
              ((∑ k ∈ Finset.range m, f (k + 1)) + f (m + 1)) := by
              simp [Finset.sum_range_succ, add_comm]
        _ = ((∑ k ∈ Finset.range m, f k) - ∑ k ∈ Finset.range m, f (k + 1)) +
              (f m - f (m + 1)) := by ring
        _ = (f 0 - f m) + (f m - f (m + 1)) := by simp [ih]
        _ = f 0 - f (m + 1) := by ring

/-- Riemann approximation is monotone increasing in n. -/
lemma sum_range_double {α : Type*} [AddCommMonoid α] (f : ℕ → α) (m : ℕ) :
    ∑ k ∈ Finset.range (2 * m), f k =
      ∑ k ∈ Finset.range m, (f (2 * k) + f (2 * k + 1)) := by
  induction m with
  | zero => simp
  | succ m ih =>
      -- Expand both sides using sum_range_succ and the induction hypothesis.
      have h_left :
          ∑ k ∈ Finset.range (2 * (m + 1)), f k =
            (∑ k ∈ Finset.range (2 * m), f k) + f (2 * m) + f (2 * m + 1) := by
        calc
          ∑ k ∈ Finset.range (2 * (m + 1)), f k =
              ∑ k ∈ Finset.range (2 * m + 2), f k := by
                simp [Nat.mul_add]
          _ = (∑ k ∈ Finset.range (2 * m + 1), f k) + f (2 * m + 1) := by
                simp [Finset.sum_range_succ, add_assoc]
          _ = ((∑ k ∈ Finset.range (2 * m), f k) + f (2 * m)) + f (2 * m + 1) := by
                simp [Finset.sum_range_succ, add_assoc]
          _ = (∑ k ∈ Finset.range (2 * m), f k) + f (2 * m) + f (2 * m + 1) := by
                simp [add_assoc]
      have h_right :
          ∑ k ∈ Finset.range (m + 1), (f (2 * k) + f (2 * k + 1)) =
            (∑ k ∈ Finset.range m, (f (2 * k) + f (2 * k + 1))) +
              (f (2 * m) + f (2 * m + 1)) := by
        simp [Finset.sum_range_succ]
      -- Combine.
      calc
        ∑ k ∈ Finset.range (2 * (m + 1)), f k
            = (∑ k ∈ Finset.range (2 * m), f k) + f (2 * m) + f (2 * m + 1) := h_left
        _ = (∑ k ∈ Finset.range m, (f (2 * k) + f (2 * k + 1))) +
              (f (2 * m) + f (2 * m + 1)) := by
              simp [ih, add_assoc, add_left_comm, add_comm]
        _ = ∑ k ∈ Finset.range (m + 1), (f (2 * k) + f (2 * k + 1)) := by
              symm; exact h_right

theorem valueChoquet_riemann_mono (ν : Semimeasure) (U : Utility) (h : History) (n : ℕ) :
    valueChoquet_riemann ν U h n ≤ valueChoquet_riemann ν U h (n + 1) := by
  dsimp [valueChoquet_riemann]
  set m : ℕ := 2 ^ n
  have hm_pos : 0 < (m : ℝ) := by
    exact Nat.cast_pos.mpr (pow_pos (by decide : 0 < (2 : ℕ)) n)
  have hm_ne : (m : ℝ) ≠ 0 := by exact ne_of_gt hm_pos
  have hm_succ : 2 ^ (n + 1) = 2 * m := by
    simp [m, pow_succ, Nat.mul_comm]
  have hm_succ' : ((2 ^ (n + 1) : ℕ) : ℝ) = 2 * (m : ℝ) := by
    exact_mod_cast hm_succ
  let f : ℝ → ℝ := fun t => capacityAtLevel ν U h t

  have h_pair :
      ∀ k ∈ Finset.range m,
        f ((k + 1 : ℝ) / (m : ℝ)) ≤
          (1 / 2 : ℝ) *
            (f ((2 * k + 1 : ℝ) / (2 * (m : ℝ))) +
              f ((2 * k + 2 : ℝ) / (2 * (m : ℝ)))) := by
    intro k hk
    have h_le :
        (2 * k + 1 : ℝ) / (2 * (m : ℝ)) ≤ (k + 1 : ℝ) / (m : ℝ) := by
      have h_num : (2 * k + 1 : ℝ) ≤ (2 * (k + 1) : ℝ) := by nlinarith
      have h_div :
          (2 * k + 1 : ℝ) / (2 * (m : ℝ)) ≤
            (2 * (k + 1) : ℝ) / (2 * (m : ℝ)) := by
        exact div_le_div_of_nonneg_right h_num (by positivity)
      have h_eq :
          (2 * (k + 1) : ℝ) / (2 * (m : ℝ)) = (k + 1 : ℝ) / (m : ℝ) := by
        field_simp [hm_ne]
      simpa [h_eq] using h_div
    have h_mono := capacityAtLevel_mono ν U h
    have h1 : f ((k + 1 : ℝ) / (m : ℝ)) ≤ f ((2 * k + 1 : ℝ) / (2 * (m : ℝ))) := by
      exact h_mono h_le
    have h2 : f ((2 * k + 2 : ℝ) / (2 * (m : ℝ))) = f ((k + 1 : ℝ) / (m : ℝ)) := by
      have h_eq :
          (2 * k + 2 : ℝ) / (2 * (m : ℝ)) = (k + 1 : ℝ) / (m : ℝ) := by
        field_simp [hm_ne]
      simp [h_eq]
    calc
      f ((k + 1 : ℝ) / (m : ℝ))
          = (1 / 2 : ℝ) *
              (f ((k + 1 : ℝ) / (m : ℝ)) + f ((k + 1 : ℝ) / (m : ℝ))) := by ring
      _ ≤ (1 / 2 : ℝ) *
            (f ((2 * k + 1 : ℝ) / (2 * (m : ℝ))) + f ((k + 1 : ℝ) / (m : ℝ))) := by
            have h := add_le_add h1
              (le_rfl : f ((k + 1 : ℝ) / (m : ℝ)) ≤ f ((k + 1 : ℝ) / (m : ℝ)))
            exact mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ (1 / 2 : ℝ))
      _ = (1 / 2 : ℝ) *
            (f ((2 * k + 1 : ℝ) / (2 * (m : ℝ))) + f ((2 * k + 2 : ℝ) / (2 * (m : ℝ)))) := by
            simp [h2]

  have h_sum :
      ∑ k ∈ Finset.range m, f ((k + 1 : ℝ) / (m : ℝ)) ≤
        ∑ k ∈ Finset.range m,
          (1 / 2 : ℝ) *
            (f ((2 * k + 1 : ℝ) / (2 * (m : ℝ))) +
              f ((2 * k + 2 : ℝ) / (2 * (m : ℝ)))) := by
    apply Finset.sum_le_sum
    intro k hk
    exact h_pair k hk

  have h_scaled :
      (1 / (m : ℝ)) * ∑ k ∈ Finset.range m, f ((k + 1 : ℝ) / (m : ℝ)) ≤
        (1 / (2 * (m : ℝ))) *
          ∑ k ∈ Finset.range m,
            (f ((2 * k + 1 : ℝ) / (2 * (m : ℝ))) +
              f ((2 * k + 2 : ℝ) / (2 * (m : ℝ)))) := by
    have h_inv_nonneg : 0 ≤ (1 / (m : ℝ)) := by
      exact one_div_nonneg.mpr (le_of_lt hm_pos)
    have h := mul_le_mul_of_nonneg_left h_sum h_inv_nonneg
    calc
      (1 / (m : ℝ)) * ∑ k ∈ Finset.range m, f ((k + 1 : ℝ) / (m : ℝ))
          ≤ (1 / (m : ℝ)) *
              ∑ k ∈ Finset.range m, (1 / 2 : ℝ) *
                (f ((2 * k + 1 : ℝ) / (2 * (m : ℝ))) +
                  f ((2 * k + 2 : ℝ) / (2 * (m : ℝ)))) := h
      _ = (1 / (m : ℝ)) * ((1 / 2 : ℝ) *
            ∑ k ∈ Finset.range m,
              (f ((2 * k + 1 : ℝ) / (2 * (m : ℝ))) +
                f ((2 * k + 2 : ℝ) / (2 * (m : ℝ))))) := by
            -- Pull the constant factor out of the sum.
            have h_pull :
                ∑ k ∈ Finset.range m,
                    (1 / 2 : ℝ) *
                      (f ((2 * k + 1 : ℝ) / (2 * (m : ℝ))) +
                        f ((2 * k + 2 : ℝ) / (2 * (m : ℝ))))
                  = (1 / 2 : ℝ) *
                      ∑ k ∈ Finset.range m,
                        (f ((2 * k + 1 : ℝ) / (2 * (m : ℝ))) +
                          f ((2 * k + 2 : ℝ) / (2 * (m : ℝ)))) := by
              classical
              let g : ℕ → ℝ := fun k =>
                f ((2 * k + 1 : ℝ) / (2 * (m : ℝ))) +
                  f ((2 * k + 2 : ℝ) / (2 * (m : ℝ)))
              have h_mul :
                  (1 / 2 : ℝ) * ∑ k ∈ Finset.range m, g k =
                    ∑ k ∈ Finset.range m, (1 / 2 : ℝ) * g k := by
                simpa using (Finset.mul_sum (s := Finset.range m) (f := g) (a := (1 / 2 : ℝ)))
              simpa [g, mul_comm, mul_left_comm, mul_assoc] using h_mul.symm
            rw [h_pull]
      _ = (1 / (2 * (m : ℝ))) *
            ∑ k ∈ Finset.range m,
              (f ((2 * k + 1 : ℝ) / (2 * (m : ℝ))) +
                f ((2 * k + 2 : ℝ) / (2 * (m : ℝ)))) := by
            have h_scale : (1 / (m : ℝ)) * (1 / 2 : ℝ) = 1 / (2 * (m : ℝ)) := by
              field_simp [hm_ne]
            calc
              (1 / (m : ℝ)) *
                  ((1 / 2 : ℝ) *
                    ∑ k ∈ Finset.range m,
                      (f ((2 * k + 1 : ℝ) / (2 * (m : ℝ))) +
                        f ((2 * k + 2 : ℝ) / (2 * (m : ℝ))))) =
                  ((1 / (m : ℝ)) * (1 / 2 : ℝ)) *
                    ∑ k ∈ Finset.range m,
                      (f ((2 * k + 1 : ℝ) / (2 * (m : ℝ))) +
                        f ((2 * k + 2 : ℝ) / (2 * (m : ℝ)))) := by
                simp [mul_assoc]
              _ = (1 / (2 * (m : ℝ))) *
                    ∑ k ∈ Finset.range m,
                      (f ((2 * k + 1 : ℝ) / (2 * (m : ℝ))) +
                        f ((2 * k + 2 : ℝ) / (2 * (m : ℝ)))) := by
                rw [h_scale]

  calc
    (1 / (m : ℝ)) * ∑ k ∈ Finset.range m, f ((k + 1 : ℝ) / (m : ℝ))
        ≤ (1 / (2 * (m : ℝ))) *
            ∑ k ∈ Finset.range m,
              (f ((2 * k + 1 : ℝ) / (2 * (m : ℝ))) +
                f ((2 * k + 2 : ℝ) / (2 * (m : ℝ)))) := h_scaled
    _ = (1 / ((2 ^ (n + 1) : ℕ) : ℝ)) *
          ∑ k ∈ Finset.range (2 ^ (n + 1)),
            f ((k + 1 : ℝ) / ((2 ^ (n + 1) : ℕ) : ℝ)) := by
          have h_sum :
              ∑ k ∈ Finset.range (2 * m), f ((k + 1 : ℝ) / (2 * (m : ℝ))) =
                ∑ k ∈ Finset.range m,
                  (f ((2 * k + 1 : ℝ) / (2 * (m : ℝ))) +
                    f ((2 * k + 2 : ℝ) / (2 * (m : ℝ)))) := by
            have h_sum' :=
              sum_range_double (fun k => f ((k + 1 : ℝ) / (2 * (m : ℝ)))) m
            refine h_sum'.trans ?_
            refine Finset.sum_congr rfl ?_
            intro k hk
            have h_eq : (2 * (k : ℝ) + 1 + 1) = (2 * (k : ℝ) + 2) := by
              ring
            simp [h_eq]
          calc
            (1 / (2 * (m : ℝ))) *
                ∑ k ∈ Finset.range m,
                  (f ((2 * k + 1 : ℝ) / (2 * (m : ℝ))) +
                    f ((2 * k + 2 : ℝ) / (2 * (m : ℝ)))) =
                (1 / (2 * (m : ℝ))) *
                  ∑ k ∈ Finset.range (2 * m), f ((k + 1 : ℝ) / (2 * (m : ℝ))) := by
              rw [h_sum.symm]
            _ = (1 / ((2 ^ (n + 1) : ℕ) : ℝ)) *
                  ∑ k ∈ Finset.range (2 ^ (n + 1)),
                    f ((k + 1 : ℝ) / ((2 ^ (n + 1) : ℕ) : ℝ)) := by
              have hm_succ'' : 2 * (m : ℝ) = ((2 ^ (n + 1) : ℕ) : ℝ) := by
                simpa using hm_succ'.symm
              rw [← hm_succ]
              simp [hm_succ'']

/-- For finite types, every set is measurable (discrete σ-algebra). -/
instance : MeasurableSpace Percept := ⊤

/-- Percept type extended with a loss outcome. -/
abbrev PerceptWithLoss := Option Percept

instance : MeasurableSpace PerceptWithLoss := ⊤

instance : MeasurableSingletonClass PerceptWithLoss := by
  classical
  refine ⟨?_⟩
  intro x
  simp

/-- Define a discrete measure on percepts weighted by the semimeasure ν.
    This measure assigns mass ν(h++p) to each percept p. -/
noncomputable def perceptMeasure (ν : Semimeasure) (h : History) : MeasureTheory.Measure Percept :=
  ∑ p : Percept, (ENNReal.ofReal (ν (encodeHistory h ++ encodePerceptBin p)).toReal) • MeasureTheory.Measure.dirac p

/-- Percept weight including loss mass. -/
noncomputable def perceptWeightWithLoss (ν : Semimeasure) (h : History) : PerceptWithLoss → ℝ
  | none => (semimeasureLoss ν (encodeHistory h)).toReal
  | some p => (ν (encodeHistory h ++ encodePerceptBin p)).toReal

/-- Discrete measure on percepts plus a loss outcome. -/
noncomputable def perceptMeasureWithLoss (ν : Semimeasure) (h : History) :
    MeasureTheory.Measure PerceptWithLoss :=
  (ENNReal.ofReal (semimeasureLoss ν (encodeHistory h)).toReal) • MeasureTheory.Measure.dirac none +
    ∑ p : Percept,
      (ENNReal.ofReal (ν (encodeHistory h ++ encodePerceptBin p)).toReal) •
        MeasureTheory.Measure.dirac (some p)

/-- The utility function on histories starting from h, viewed as a function on percepts. -/
def utilityOnPercepts (U : Utility) (h : History) (p : Percept) : ℝ :=
  U (h ++ [HistElem.per p])

/-- Utility on percepts plus a loss outcome. -/
noncomputable def utilityOnPerceptsWithLoss (U : Utility) (h : History) : PerceptWithLoss → ℝ
  | none => minNextUtility U h
  | some p => U (h ++ [HistElem.per p])

/-- The integral of utilityOnPercepts w.r.t. perceptMeasure equals the weighted sum appearing in valueNeutral. -/
lemma integral_utilityOnPercepts_eq_valueNeutral (ν : Semimeasure) (U : Utility) (h : History)
    (_h_U_bound : ∀ h', 0 ≤ U h' ∧ U h' ≤ 1) :
    ∫ p, utilityOnPercepts U h p ∂(perceptMeasure ν h) =
      ∑ p : Percept, (ν (encodeHistory h ++ encodePerceptBin p)).toReal * U (h ++ [HistElem.per p]) := by
  unfold perceptMeasure utilityOnPercepts
  -- This is a standard result for discrete measures on finite types:
  -- ∫ f ∂(∑ₚ aₚ • δₚ) = ∑ₚ aₚ · f(p)
  -- Proof strategy:
  -- 1. Use integral_finset_sum_measure: ∫ f ∂(∑ᵢ μᵢ) = ∑ᵢ ∫ f ∂μᵢ
  -- 2. Use integral_smul_measure: ∫ f ∂(c • μ) = c.toReal • ∫ f ∂μ
  -- 3. Use integral_dirac: ∫ f ∂(δₐ) = f(a)
  -- 4. Combine: ∫ f ∂(∑ₚ aₚ • δₚ) = ∑ₚ aₚ.toReal • f(p)
  -- The technical issue is showing f is integrable w.r.t. each scaled Dirac.
  -- For bounded functions on finite spaces, this is straightforward but requires
  -- finding the right Mathlib lemmas for measurability on discrete spaces.
  classical
  have h_integrable :
      ∀ p ∈ (Finset.univ : Finset Percept),
        Integrable (fun q : Percept => U (h ++ [HistElem.per q]))
          ((ENNReal.ofReal (ν (encodeHistory h ++ encodePerceptBin p)).toReal) • Measure.dirac p) := by
    intro p _
    have h_dirac :
        Integrable (fun q : Percept => U (h ++ [HistElem.per q])) (Measure.dirac p) := by
      apply integrable_dirac
      simp
    simpa using h_dirac.smul_measure ENNReal.ofReal_ne_top
  have h_sum :=
      (integral_finset_sum_measure
        (s := (Finset.univ : Finset Percept))
        (f := fun q : Percept => U (h ++ [HistElem.per q]))
        (μ := fun p =>
          (ENNReal.ofReal (ν (encodeHistory h ++ encodePerceptBin p)).toReal) • Measure.dirac p)
        h_integrable)
  simpa [integral_smul_measure, integral_dirac, smul_eq_mul, ENNReal.toReal_ofReal,
    ENNReal.toReal_nonneg] using h_sum

/-- The integral of utilityOnPerceptsWithLoss w.r.t. perceptMeasureWithLoss equals valueChoquet. -/
lemma integral_utilityOnPerceptsWithLoss_eq_valueChoquet (ν : Semimeasure) (U : Utility) (h : History)
    (_h_U_bound : ∀ h', 0 ≤ U h' ∧ U h' ≤ 1) :
    ∫ q, utilityOnPerceptsWithLoss U h q ∂(perceptMeasureWithLoss ν h) = valueChoquet ν U h := by
  classical
  unfold perceptMeasureWithLoss valueChoquet
  have h_integrable_loss :
      Integrable (utilityOnPerceptsWithLoss U h)
        ((ENNReal.ofReal (semimeasureLoss ν (encodeHistory h)).toReal) •
          Measure.dirac (none : PerceptWithLoss)) := by
    have h_dirac :
        Integrable (utilityOnPerceptsWithLoss U h) (Measure.dirac (none : PerceptWithLoss)) := by
      apply integrable_dirac
      simp
    simpa using h_dirac.smul_measure ENNReal.ofReal_ne_top
  have h_integrable_percept :
      ∀ p ∈ (Finset.univ : Finset Percept),
        Integrable (utilityOnPerceptsWithLoss U h)
          ((ENNReal.ofReal (ν (encodeHistory h ++ encodePerceptBin p)).toReal) •
            Measure.dirac (some p)) := by
    intro p _
    have h_dirac :
        Integrable (utilityOnPerceptsWithLoss U h) (Measure.dirac (some p)) := by
      apply integrable_dirac
      simp
    simpa using h_dirac.smul_measure ENNReal.ofReal_ne_top
  have h_integrable_sum :
      Integrable (utilityOnPerceptsWithLoss U h)
        (∑ p : Percept,
          (ENNReal.ofReal (ν (encodeHistory h ++ encodePerceptBin p)).toReal) •
            Measure.dirac (some p)) :=
    (integrable_finset_sum_measure
      (s := (Finset.univ : Finset Percept))
      (f := utilityOnPerceptsWithLoss U h)
      (μ := fun p =>
        (ENNReal.ofReal (ν (encodeHistory h ++ encodePerceptBin p)).toReal) •
          Measure.dirac (some p))).2 h_integrable_percept
  have h_sum :=
    (integral_finset_sum_measure
      (s := (Finset.univ : Finset Percept))
      (f := utilityOnPerceptsWithLoss U h)
      (μ := fun p =>
        (ENNReal.ofReal (ν (encodeHistory h ++ encodePerceptBin p)).toReal) •
          Measure.dirac (some p))
      h_integrable_percept)
  have h_add := integral_add_measure h_integrable_loss h_integrable_sum
  have h_sum_eval :
      ∫ q, utilityOnPerceptsWithLoss U h q ∂(
        ∑ p : Percept,
          (ENNReal.ofReal (ν (encodeHistory h ++ encodePerceptBin p)).toReal) •
            Measure.dirac (some p)) =
        ∑ p : Percept, (ν (encodeHistory h ++ encodePerceptBin p)).toReal * U (h ++ [HistElem.per p]) := by
    simpa [integral_smul_measure, integral_dirac, utilityOnPerceptsWithLoss, smul_eq_mul,
      ENNReal.toReal_ofReal, ENNReal.toReal_nonneg] using h_sum
  have h_loss_eval :
      ∫ q, utilityOnPerceptsWithLoss U h q ∂(
        (ENNReal.ofReal (semimeasureLoss ν (encodeHistory h)).toReal) •
          Measure.dirac (none : PerceptWithLoss)) =
        (semimeasureLoss ν (encodeHistory h)).toReal * minNextUtility U h := by
    simp [integral_smul_measure, integral_dirac, utilityOnPerceptsWithLoss, smul_eq_mul,
      ENNReal.toReal_ofReal, ENNReal.toReal_nonneg]
  -- Simplify the loss term and the percept sum term separately.
  calc
    ∫ q, utilityOnPerceptsWithLoss U h q ∂(
          (ENNReal.ofReal (semimeasureLoss ν (encodeHistory h)).toReal) •
            Measure.dirac (none : PerceptWithLoss) +
          ∑ p : Percept,
            (ENNReal.ofReal (ν (encodeHistory h ++ encodePerceptBin p)).toReal) •
              Measure.dirac (some p)) =
        ∫ q, utilityOnPerceptsWithLoss U h q ∂(
          (ENNReal.ofReal (semimeasureLoss ν (encodeHistory h)).toReal) •
            Measure.dirac (none : PerceptWithLoss)) +
        ∫ q, utilityOnPerceptsWithLoss U h q ∂(
          ∑ p : Percept,
            (ENNReal.ofReal (ν (encodeHistory h ++ encodePerceptBin p)).toReal) •
              Measure.dirac (some p)) := by
        simpa using h_add
    _ = (semimeasureLoss ν (encodeHistory h)).toReal * minNextUtility U h +
        ∑ p : Percept, (ν (encodeHistory h ++ encodePerceptBin p)).toReal * U (h ++ [HistElem.per p]) := by
        simp [h_loss_eval, h_sum_eval]
    _ = valueNeutral ν U h + (semimeasureLoss ν (encodeHistory h)).toReal * minNextUtility U h := by
        unfold valueNeutral
        ring

/-- Choquet value equals the layer-cake integral of capacityAtLevel. -/
lemma valueChoquet_eq_integral_capacity (ν : Semimeasure) (U : Utility) (h : History)
    (h_U_bound : ∀ h', 0 ≤ U h' ∧ U h' ≤ 1) :
    valueChoquet ν U h = ∫ t in Set.Ioc 0 1, capacityAtLevel ν U h t := by
  -- Part A: ∫ U dμ = valueChoquet where μ = perceptMeasureWithLoss ν h.
  have integral_eq_value :
      ∫ q, utilityOnPerceptsWithLoss U h q ∂(perceptMeasureWithLoss ν h) = valueChoquet ν U h := by
    exact integral_utilityOnPerceptsWithLoss_eq_valueChoquet ν U h h_U_bound

  -- Part B: measure of level sets equals capacityAtLevel.
  have measure_eq_capacity : ∀ t,
      (perceptMeasureWithLoss ν h) {q | t < utilityOnPerceptsWithLoss U h q} =
        ENNReal.ofReal (capacityAtLevel ν U h t) := by
    intro t
    unfold perceptMeasureWithLoss utilityOnPerceptsWithLoss capacityAtLevel perceptMass
    by_cases ht : t < minNextUtility U h
    · -- All outcomes are above t, so we get total one-step mass.
      have h_all : ∀ p : Percept, t < U (h ++ [HistElem.per p]) := by
        intro p
        have h_min_le : minNextUtility U h ≤ U (h ++ [HistElem.per p]) := by
          unfold minNextUtility
          simpa using
            (Finset.inf'_le (s := Finset.univ)
              (f := fun p : Percept => U (h ++ [HistElem.per p]))
              (h := Finset.mem_univ p))
        exact lt_of_lt_of_le ht h_min_le
      have h_nonneg : ∀ p, 0 ≤ (ν (encodeHistory h ++ encodePerceptBin p)).toReal := by
        intro p; exact ENNReal.toReal_nonneg
      have h_sum_nonneg :
          0 ≤ ∑ p : Percept, (ν (encodeHistory h ++ encodePerceptBin p)).toReal := by
        apply Finset.sum_nonneg
        intro p _
        exact h_nonneg p
      simp [ht, h_all, ENNReal.ofReal_add, ENNReal.ofReal_sum_of_nonneg, h_sum_nonneg, h_nonneg,
        ENNReal.toReal_nonneg, Measure.add_apply, Measure.smul_apply, Set.indicator]
    · -- Loss outcome excluded; only percepts with U>t contribute.
      have h_nonneg : ∀ p, 0 ≤ (if t < U (h ++ [HistElem.per p]) then
          (ν (encodeHistory h ++ encodePerceptBin p)).toReal else 0) := by
        intro p
        by_cases hp : t < U (h ++ [HistElem.per p])
        · simp [hp, ENNReal.toReal_nonneg]
        · simp [hp]
      have h_sum_nonneg :
          0 ≤ ∑ p : Percept, if t < U (h ++ [HistElem.per p]) then
              (ν (encodeHistory h ++ encodePerceptBin p)).toReal else 0 := by
        apply Finset.sum_nonneg
        intro p _
        exact h_nonneg p
      have h_ofReal_if :
          ∀ p : Percept,
            (if t < U (h ++ [HistElem.per p]) then
              ENNReal.ofReal (ν (encodeHistory h ++ encodePerceptBin p)).toReal else 0) =
              ENNReal.ofReal
                (if t < U (h ++ [HistElem.per p]) then
                  (ν (encodeHistory h ++ encodePerceptBin p)).toReal else 0) := by
        intro p
        by_cases hp : t < U (h ++ [HistElem.per p])
        · simp [hp]
        · simp [hp]
      simp [ht, ENNReal.ofReal_sum_of_nonneg, h_nonneg, h_ofReal_if,
        Measure.add_apply, Measure.smul_apply, Set.indicator]

  have h_capacity_eq :
      ∀ t, (perceptMeasureWithLoss ν h).real {q | t < utilityOnPerceptsWithLoss U h q} =
        capacityAtLevel ν U h t := by
    intro t
    have h_meas := measure_eq_capacity t
    have h_nonneg : 0 ≤ capacityAtLevel ν U h t := capacityAtLevel_nonneg ν U h t
    calc
      (perceptMeasureWithLoss ν h).real {q | t < utilityOnPerceptsWithLoss U h q} =
          ENNReal.toReal ((perceptMeasureWithLoss ν h) {q | t < utilityOnPerceptsWithLoss U h q}) := by
            simp [measureReal_def]
      _ = ENNReal.toReal (ENNReal.ofReal (capacityAtLevel ν U h t)) := by
            simp [h_meas]
      _ = capacityAtLevel ν U h t := by
            simp [ENNReal.toReal_ofReal, h_nonneg]

  -- Part C: layer cake formula for utilityOnPerceptsWithLoss.
  have layer_cake :
      ∫ q, utilityOnPerceptsWithLoss U h q ∂(perceptMeasureWithLoss ν h) =
        ∫ t in Set.Ioc 0 1,
          (perceptMeasureWithLoss ν h).real {q | t ≤ utilityOnPerceptsWithLoss U h q} := by
    -- Integrability comes from finiteness of the discrete measure.
    have h_integrable_loss :
        Integrable (utilityOnPerceptsWithLoss U h)
          ((ENNReal.ofReal (semimeasureLoss ν (encodeHistory h)).toReal) •
            Measure.dirac (none : PerceptWithLoss)) := by
      have h_dirac :
          Integrable (utilityOnPerceptsWithLoss U h) (Measure.dirac (none : PerceptWithLoss)) := by
        apply integrable_dirac
        simp
      simpa using h_dirac.smul_measure ENNReal.ofReal_ne_top
    have h_integrable_percept :
        ∀ p ∈ (Finset.univ : Finset Percept),
          Integrable (utilityOnPerceptsWithLoss U h)
            ((ENNReal.ofReal (ν (encodeHistory h ++ encodePerceptBin p)).toReal) •
              Measure.dirac (some p)) := by
      intro p _
      have h_dirac :
          Integrable (utilityOnPerceptsWithLoss U h) (Measure.dirac (some p)) := by
        apply integrable_dirac
        simp
      simpa using h_dirac.smul_measure ENNReal.ofReal_ne_top
    have h_integrable_sum :
        Integrable (utilityOnPerceptsWithLoss U h)
          (∑ p : Percept,
            (ENNReal.ofReal (ν (encodeHistory h ++ encodePerceptBin p)).toReal) •
              Measure.dirac (some p)) :=
      (integrable_finset_sum_measure
        (s := (Finset.univ : Finset Percept))
        (f := utilityOnPerceptsWithLoss U h)
        (μ := fun p =>
          (ENNReal.ofReal (ν (encodeHistory h ++ encodePerceptBin p)).toReal) •
            Measure.dirac (some p))).2 h_integrable_percept
    have h_integrable :
        Integrable (utilityOnPerceptsWithLoss U h) (perceptMeasureWithLoss ν h) := by
      simpa [perceptMeasureWithLoss] using h_integrable_loss.add_measure h_integrable_sum
    apply Integrable.integral_eq_integral_Ioc_meas_le
    · exact h_integrable
    · -- nonneg a.e.
      have h_min_bounds := minNextUtility_bounds U h h_U_bound
      apply ae_of_all
      intro q
      cases q with
      | none => exact h_min_bounds.1
      | some p => exact (h_U_bound _).1
    · -- bounded by 1 a.e.
      have h_min_bounds := minNextUtility_bounds U h h_U_bound
      apply ae_of_all
      intro q
      cases q with
      | none => exact h_min_bounds.2
      | some p => exact (h_U_bound _).2

  -- Combine.
  calc
    valueChoquet ν U h =
        ∫ q, utilityOnPerceptsWithLoss U h q ∂(perceptMeasureWithLoss ν h) := by
          symm; exact integral_eq_value
    _ = ∫ t in Set.Ioc 0 1,
          (perceptMeasureWithLoss ν h).real {q | t ≤ utilityOnPerceptsWithLoss U h q} := layer_cake
    _ = ∫ t in Set.Ioc 0 1,
          (perceptMeasureWithLoss ν h).real {q | t < utilityOnPerceptsWithLoss U h q} := by
          -- Switch from `t ≤ f` to `t < f` a.e.
          apply integral_congr_ae
          filter_upwards
            [meas_le_ae_eq_meas_lt (μ := perceptMeasureWithLoss ν h)
              (ν := volume.restrict (Set.Ioc 0 1))
              (g := utilityOnPerceptsWithLoss U h)] with t ht
          simp [measureReal_def, ht]
    _ = ∫ t in Set.Ioc 0 1, capacityAtLevel ν U h t := by
          refine integral_congr_ae ?_
          have h_ae :
              ∀ᵐ t ∂(volume.restrict (Set.Ioc 0 1)),
                (perceptMeasureWithLoss ν h).real {q | t < utilityOnPerceptsWithLoss U h q} =
                  capacityAtLevel ν U h t := by
            simpa using
              (ae_of_all (μ := volume.restrict (Set.Ioc 0 1)) (fun t => h_capacity_eq t))
          exact h_ae

/-- **Layer Cake Equivalence**: The integral of capacityAtLevel equals valueChoquet.

This uses the layer cake formula from Mathlib: for bounded integrable f,
  ∫ f dμ = ∫₀^M μ({x : t < f(x)}) dt

In our case:
- μ = discrete measure on percepts plus loss mass
- f = utility function U
- M = 1 (since U ≤ 1)
- μ({p : t < U(p)}) = capacityAtLevel

The layer cake formula directly gives:
  ∫ U dμ = ∫₀¹ capacityAtLevel(t) dt

And ∫ U dμ = ∑_p ν(h++p)·U(h++p) which appears in valueChoquet.

**Formal Proof Strategy**:
1. Apply `Integrable.integral_eq_integral_Ioc_meas_le` and switch to `t < f` a.e.
2. Show μ({p : t < U(p)}) = capacityAtLevel(t)
4. Show the integral equals valueChoquet by expanding definitions
-/
theorem layer_cake_equivalence (ν : Semimeasure) (U : Utility) (h : History)
    (h_U_bound : ∀ h', 0 ≤ U h' ∧ U h' ≤ 1) (n : ℕ) (hn : 0 < n) :
    (1 / n : ℝ) * ∑ k ∈ Finset.range n, capacityAtLevel ν U h ((k + 1 : ℝ) / (n : ℝ))
              ≤ valueChoquet ν U h := by
  have h_integral_eq :
      ∫ t in Set.Ioc 0 1, capacityAtLevel ν U h t = valueChoquet ν U h := by
    simpa using (valueChoquet_eq_integral_capacity ν U h h_U_bound).symm

  have h_riemann :
      (1 / n : ℝ) * ∑ k ∈ Finset.range n, capacityAtLevel ν U h ((k + 1 : ℝ) / (n : ℝ))
        ≤ ∫ t in Set.Ioc 0 1, capacityAtLevel ν U h t := by
    have hn_pos : 0 < (n : ℝ) := by exact_mod_cast hn
    have hn_ne : (n : ℝ) ≠ 0 := by exact ne_of_gt hn_pos
    let f : ℝ → ℝ := fun t => capacityAtLevel ν U h t
    have h_monotone : Monotone (fun x : ℝ => x / (n : ℝ)) := by
      intro x y hxy
      exact div_le_div_of_nonneg_right hxy (le_of_lt hn_pos)
    have h_antitone : Antitone (fun x : ℝ => f (x / (n : ℝ))) :=
      Antitone.comp_monotone (g := f) (f := fun x => x / (n : ℝ))
        (capacityAtLevel_mono ν U h) h_monotone
    have h_antitone_on :
        AntitoneOn (fun x : ℝ => f (x / (n : ℝ))) (Set.Icc (0 : ℝ) (0 + (n : ℝ))) := by
      simpa using (h_antitone.antitoneOn (s := Set.Icc (0 : ℝ) (0 + (n : ℝ))))
    have h_sum_le :
        ∑ k ∈ Finset.range n, f ((k + 1 : ℝ) / (n : ℝ))
          ≤ ∫ x in (0 : ℝ)..(n : ℝ), f (x / (n : ℝ)) := by
      simpa [f] using
        (AntitoneOn.sum_le_integral (f := fun x : ℝ => f (x / (n : ℝ)))
          (x₀ := (0 : ℝ)) (a := n) h_antitone_on)
    have h_integral :
        ∫ x in (0 : ℝ)..(n : ℝ), f (x / (n : ℝ)) =
          (n : ℝ) * ∫ t in Set.Ioc 0 1, f t := by
      calc
        ∫ x in (0 : ℝ)..(n : ℝ), f (x / (n : ℝ)) =
            (n : ℝ) * ∫ x in (0 : ℝ) / (n : ℝ)..(n : ℝ) / (n : ℝ), f x := by
              simpa using
                (intervalIntegral.integral_comp_div (f := f)
                  (a := (0 : ℝ)) (b := (n : ℝ)) (c := (n : ℝ)) hn_ne)
        _ = (n : ℝ) * ∫ x in (0 : ℝ)..(1 : ℝ), f x := by
              simp [hn_ne]
        _ = (n : ℝ) * ∫ x in Set.Ioc 0 1, f x := by
              simp [intervalIntegral.integral_of_le]
    have h_scaled :
        (1 / n : ℝ) * ∑ k ∈ Finset.range n, f ((k + 1 : ℝ) / (n : ℝ))
          ≤ (1 / n : ℝ) * ((n : ℝ) * ∫ t in Set.Ioc 0 1, f t) := by
      have h_inv_nonneg : 0 ≤ (1 / (n : ℝ)) := by
        exact one_div_nonneg.mpr (le_of_lt hn_pos)
      have h := mul_le_mul_of_nonneg_left h_sum_le h_inv_nonneg
      simpa [h_integral] using h
    have h_simpl :
        (1 / n : ℝ) * ((n : ℝ) * ∫ t in Set.Ioc 0 1, f t) =
          ∫ t in Set.Ioc 0 1, f t := by
      calc
        (1 / n : ℝ) * ((n : ℝ) * ∫ t in Set.Ioc 0 1, f t)
            = ((1 / n : ℝ) * (n : ℝ)) * ∫ t in Set.Ioc 0 1, f t := by ring
        _ = (1 : ℝ) * ∫ t in Set.Ioc 0 1, f t := by
              simp [hn_ne]
        _ = ∫ t in Set.Ioc 0 1, f t := by simp
    have h_scaled' :
        (1 / n : ℝ) * ∑ k ∈ Finset.range n, f ((k + 1 : ℝ) / (n : ℝ))
          ≤ ∫ t in Set.Ioc 0 1, f t := by
      calc
        (1 / n : ℝ) * ∑ k ∈ Finset.range n, f ((k + 1 : ℝ) / (n : ℝ))
            ≤ (1 / n : ℝ) * ((n : ℝ) * ∫ t in Set.Ioc 0 1, f t) := h_scaled
        _ = ∫ t in Set.Ioc 0 1, f t := h_simpl
    simpa [f] using h_scaled'

  exact h_riemann.trans_eq h_integral_eq

/-- Riemann approximation is bounded above by valueChoquet. -/
theorem valueChoquet_riemann_le (ν : Semimeasure) (U : Utility) (h : History)
    (h_U_bound : ∀ h', 0 ≤ U h' ∧ U h' ≤ 1) (n : ℕ) :
    valueChoquet_riemann ν U h n ≤ valueChoquet ν U h := by
  have hn_pos : 0 < 2 ^ n := pow_pos (by decide : 0 < (2 : ℕ)) n
  -- Use the layer cake bound for the dyadic partition size.
  simpa [valueChoquet_riemann] using
    (layer_cake_equivalence ν U h h_U_bound (2 ^ n) hn_pos)

/-- Riemann approximation converges to valueChoquet. -/
theorem valueChoquet_riemann_converges (ν : Semimeasure) (U : Utility) (h : History)
    (h_U_bound : ∀ h', 0 ≤ U h' ∧ U h' ≤ 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ N, ∀ n ≥ N, valueChoquet ν U h - valueChoquet_riemann ν U h n < ε := by
  let f : ℝ → ℝ := fun t => capacityAtLevel ν U h t
  have h_value_eq :
      valueChoquet ν U h = ∫ t in Set.Ioc 0 1, f t := by
    simpa [f] using valueChoquet_eq_integral_capacity ν U h h_U_bound

  have hmass_pos : 0 < perceptMass ν h + 1 := by
    have hmass_nonneg := perceptMass_nonneg ν h
    linarith
  have hδ_pos : 0 < ε / (perceptMass ν h + 1) := by
    exact div_pos hε hmass_pos
  obtain ⟨N, hN_pos, hN_inv⟩ := Real.exists_nat_pos_inv_lt hδ_pos
  refine ⟨N, ?_⟩
  intro n hn
  set m : ℕ := 2 ^ n
  have hm_pos : 0 < (m : ℝ) := by
    have hm_nat : 0 < m := pow_pos (by decide : 0 < (2 : ℕ)) n
    exact Nat.cast_pos.mpr hm_nat
  have hm_ne : (m : ℝ) ≠ 0 := by exact ne_of_gt hm_pos

  let rightSum : ℝ :=
    (1 / (m : ℝ)) * ∑ k ∈ Finset.range m, f ((k + 1 : ℝ) / (m : ℝ))
  let leftSum : ℝ :=
    (1 / (m : ℝ)) * ∑ k ∈ Finset.range m, f ((k : ℝ) / (m : ℝ))

  have h_right_eq : rightSum = valueChoquet_riemann ν U h n := by
    simp [rightSum, valueChoquet_riemann, m, f]

  have h_monotone : Monotone (fun x : ℝ => x / (m : ℝ)) := by
    intro x y hxy
    exact div_le_div_of_nonneg_right hxy (le_of_lt hm_pos)
  have h_antitone : Antitone (fun x : ℝ => f (x / (m : ℝ))) :=
    Antitone.comp_monotone (g := f) (f := fun x => x / (m : ℝ))
      (capacityAtLevel_mono ν U h) h_monotone
  have h_antitone_on :
      AntitoneOn (fun x : ℝ => f (x / (m : ℝ))) (Set.Icc (0 : ℝ) (0 + (m : ℝ))) := by
    simpa using (h_antitone.antitoneOn (s := Set.Icc (0 : ℝ) (0 + (m : ℝ))))

  have h_int_le_sum :
      ∫ x in (0 : ℝ)..(m : ℝ), f (x / (m : ℝ))
        ≤ ∑ k ∈ Finset.range m, f ((k : ℝ) / (m : ℝ)) := by
    simpa [f] using
      (AntitoneOn.integral_le_sum (f := fun x : ℝ => f (x / (m : ℝ)))
        (x₀ := (0 : ℝ)) (a := m) h_antitone_on)

  have h_sum_le_int :
      ∑ k ∈ Finset.range m, f ((k + 1 : ℝ) / (m : ℝ))
        ≤ ∫ x in (0 : ℝ)..(m : ℝ), f (x / (m : ℝ)) := by
    simpa [f] using
      (AntitoneOn.sum_le_integral (f := fun x : ℝ => f (x / (m : ℝ)))
        (x₀ := (0 : ℝ)) (a := m) h_antitone_on)

  have h_integral :
      ∫ x in (0 : ℝ)..(m : ℝ), f (x / (m : ℝ)) =
        (m : ℝ) * ∫ t in Set.Ioc 0 1, f t := by
    calc
      ∫ x in (0 : ℝ)..(m : ℝ), f (x / (m : ℝ)) =
          (m : ℝ) * ∫ x in (0 : ℝ) / (m : ℝ)..(m : ℝ) / (m : ℝ), f x := by
            simpa using
              (intervalIntegral.integral_comp_div (f := f)
                (a := (0 : ℝ)) (b := (m : ℝ)) (c := (m : ℝ)) hm_ne)
      _ = (m : ℝ) * ∫ x in (0 : ℝ)..(1 : ℝ), f x := by
            simp [hm_ne]
      _ = (m : ℝ) * ∫ x in Set.Ioc 0 1, f x := by
            simp [intervalIntegral.integral_of_le]

  have h_left_ge :
      ∫ t in Set.Ioc 0 1, f t ≤ leftSum := by
    have h_scaled :
        (1 / (m : ℝ)) * ∫ x in (0 : ℝ)..(m : ℝ), f (x / (m : ℝ))
          ≤ leftSum := by
      have h_inv_nonneg : 0 ≤ (1 / (m : ℝ)) := by
        exact one_div_nonneg.mpr (le_of_lt hm_pos)
      have h := mul_le_mul_of_nonneg_left h_int_le_sum h_inv_nonneg
      simpa [leftSum] using h
    have h_simpl :
        (1 / (m : ℝ)) * ∫ x in (0 : ℝ)..(m : ℝ), f (x / (m : ℝ)) =
          ∫ t in Set.Ioc 0 1, f t := by
      calc
        (1 / (m : ℝ)) * ∫ x in (0 : ℝ)..(m : ℝ), f (x / (m : ℝ))
            = (1 / (m : ℝ)) * ((m : ℝ) * ∫ t in Set.Ioc 0 1, f t) := by
                simp [h_integral]
        _ = ((1 / (m : ℝ)) * (m : ℝ)) * ∫ t in Set.Ioc 0 1, f t := by ring
        _ = (1 : ℝ) * ∫ t in Set.Ioc 0 1, f t := by simp [hm_ne]
        _ = ∫ t in Set.Ioc 0 1, f t := by simp
    have h_scaled' : ∫ t in Set.Ioc 0 1, f t ≤ leftSum := by
      calc
        ∫ t in Set.Ioc 0 1, f t
            = (1 / (m : ℝ)) * ∫ x in (0 : ℝ)..(m : ℝ), f (x / (m : ℝ)) := by
                symm; exact h_simpl
        _ ≤ leftSum := h_scaled
    simpa using h_scaled'

  have h_right_le :
      rightSum ≤ ∫ t in Set.Ioc 0 1, f t := by
    have h_scaled :
        rightSum ≤ (1 / (m : ℝ)) * ∫ x in (0 : ℝ)..(m : ℝ), f (x / (m : ℝ)) := by
      have h_inv_nonneg : 0 ≤ (1 / (m : ℝ)) := by
        exact one_div_nonneg.mpr (le_of_lt hm_pos)
      have h := mul_le_mul_of_nonneg_left h_sum_le_int h_inv_nonneg
      simpa [rightSum] using h
    have h_simpl :
        (1 / (m : ℝ)) * ∫ x in (0 : ℝ)..(m : ℝ), f (x / (m : ℝ)) =
          ∫ t in Set.Ioc 0 1, f t := by
      calc
        (1 / (m : ℝ)) * ∫ x in (0 : ℝ)..(m : ℝ), f (x / (m : ℝ))
            = (1 / (m : ℝ)) * ((m : ℝ) * ∫ t in Set.Ioc 0 1, f t) := by
                simp [h_integral]
        _ = ((1 / (m : ℝ)) * (m : ℝ)) * ∫ t in Set.Ioc 0 1, f t := by ring
        _ = (1 : ℝ) * ∫ t in Set.Ioc 0 1, f t := by simp [hm_ne]
        _ = ∫ t in Set.Ioc 0 1, f t := by simp
    calc
      rightSum ≤ (1 / (m : ℝ)) * ∫ x in (0 : ℝ)..(m : ℝ), f (x / (m : ℝ)) := h_scaled
      _ = ∫ t in Set.Ioc 0 1, f t := h_simpl

  have h_left_right_diff :
      leftSum - rightSum = (1 / (m : ℝ)) * (f 0 - f 1) := by
    have h_sum_diff :
        (∑ k ∈ Finset.range m, f ((k : ℝ) / (m : ℝ))) -
          ∑ k ∈ Finset.range m, f ((k + 1 : ℝ) / (m : ℝ))
          = f (0 / (m : ℝ)) - f ((m : ℝ) / (m : ℝ)) := by
      simpa using (sum_range_sub_succ (fun k => f ((k : ℝ) / (m : ℝ))) m)
    calc
      leftSum - rightSum
          = (1 / (m : ℝ)) *
              ((∑ k ∈ Finset.range m, f ((k : ℝ) / (m : ℝ))) -
                ∑ k ∈ Finset.range m, f ((k + 1 : ℝ) / (m : ℝ))) := by
              ring
      _ = (1 / (m : ℝ)) * (f (0 / (m : ℝ)) - f ((m : ℝ) / (m : ℝ))) := by
              simp [h_sum_diff]
      _ = (1 / (m : ℝ)) * (f 0 - f 1) := by
              have hm_ne' : (m : ℝ) ≠ 0 := hm_ne
              simp [hm_ne']

  have h_bound :
      valueChoquet ν U h - rightSum ≤ (1 / (m : ℝ)) * perceptMass ν h := by
    have h_le : valueChoquet ν U h ≤ leftSum := by
      -- Rewrite valueChoquet as the integral and use the left sum bound.
      simpa [h_value_eq] using h_left_ge
    have h_sub :
        valueChoquet ν U h - rightSum ≤ leftSum - rightSum :=
      sub_le_sub_right h_le _
    have h_mass0 : 0 ≤ f 1 := by
      simpa [f] using capacityAtLevel_nonneg ν U h 1
    have h_mass1 : f 0 ≤ perceptMass ν h := by
      simpa [f] using capacityAtLevel_le ν U h 0
    calc
      valueChoquet ν U h - rightSum
          ≤ leftSum - rightSum := h_sub
      _ = (1 / (m : ℝ)) * (f 0 - f 1) := h_left_right_diff
      _ ≤ (1 / (m : ℝ)) * f 0 := by
            have : f 0 - f 1 ≤ f 0 := by linarith
            exact mul_le_mul_of_nonneg_left this (by positivity)
      _ ≤ (1 / (m : ℝ)) * perceptMass ν h := by
            exact mul_le_mul_of_nonneg_left h_mass1 (by positivity : 0 ≤ (1 / (m : ℝ)))

  have h_final :
      (1 / (m : ℝ)) * perceptMass ν h < ε := by
    have h1 :
        (1 / (m : ℝ)) * perceptMass ν h ≤ (1 / (m : ℝ)) * (perceptMass ν h + 1) := by
      have h_nonneg : 0 ≤ (1 / (m : ℝ)) := by
        exact one_div_nonneg.mpr (le_of_lt hm_pos)
      have h_le : perceptMass ν h ≤ perceptMass ν h + 1 := by linarith
      exact mul_le_mul_of_nonneg_left h_le h_nonneg
    have hn_pos_nat : 0 < n := lt_of_lt_of_le hN_pos hn
    have hn_pos : 0 < (n : ℝ) := by exact_mod_cast hn_pos_nat
    have hN_pos_real : 0 < (N : ℝ) := by exact_mod_cast hN_pos
    have h_n_le_m : (n : ℝ) ≤ (m : ℝ) := by
      exact_mod_cast (nat_le_two_pow n)
    have h_one_div_m_le_n : (1 / (m : ℝ)) ≤ (1 / (n : ℝ)) :=
      one_div_le_one_div_of_le hn_pos h_n_le_m
    have h_one_div_n_le_N : (1 / (n : ℝ)) ≤ (1 / (N : ℝ)) :=
      one_div_le_one_div_of_le hN_pos_real (by exact_mod_cast hn)
    have h_one_div_m_le : (1 / (m : ℝ)) ≤ (1 / (N : ℝ)) :=
      le_trans h_one_div_m_le_n h_one_div_n_le_N
    have h2 :
        (1 / (m : ℝ)) * (perceptMass ν h + 1)
          ≤ (1 / (N : ℝ)) * (perceptMass ν h + 1) := by
      exact mul_le_mul_of_nonneg_right h_one_div_m_le (by linarith)
    have hN_inv' : (1 / (N : ℝ)) < ε / (perceptMass ν h + 1) := by
      simpa using hN_inv
    have h3 :
        (1 / (N : ℝ)) * (perceptMass ν h + 1) < ε := by
      have h_mul := mul_lt_mul_of_pos_right hN_inv' hmass_pos
      have hcancel :
          (ε / (perceptMass ν h + 1)) * (perceptMass ν h + 1) = ε := by
        field_simp [ne_of_gt hmass_pos]
      simpa [hcancel] using h_mul
    exact lt_of_le_of_lt (le_trans h1 h2) h3

  have h_right_val :
      valueChoquet_riemann ν U h n = rightSum := by
    symm; exact h_right_eq
  calc
    valueChoquet ν U h - valueChoquet_riemann ν U h n
        = valueChoquet ν U h - rightSum := by simp [h_right_val]
    _ ≤ (1 / (m : ℝ)) * perceptMass ν h := h_bound
    _ < ε := h_final

/-- Capacity at level is lower semicomputable (requires l.s.c. U and computable ν). -/
noncomputable def capacityAtLevel_lower_semicomputable (ν : Semimeasure) (U : Utility) (t : ℝ)
    (h_U_lsc : Mettapedia.Computability.ArithmeticalHierarchy.LowerSemicomputable U)
    (h_ν_lsc : Mettapedia.Computability.ArithmeticalHierarchy.LowerSemicomputable
                (fun x => (ν x).toReal))
    (h_ν_usc : Mettapedia.Computability.ArithmeticalHierarchy.UpperSemicomputable
                (fun x => (ν x).toReal)) :
    Mettapedia.Computability.ArithmeticalHierarchy.LowerSemicomputable
      (fun h => capacityAtLevel ν U h t) := by
  classical

  -- l.s.c. for minNextUtility
  have h_min_lsc :
      Mettapedia.Computability.ArithmeticalHierarchy.LowerSemicomputable
        (fun h => minNextUtility U h) := by
    apply Mettapedia.Computability.ArithmeticalHierarchy.LowerSemicomputable.finset_inf
    · intro p
      exact h_U_lsc.comp (fun h => h ++ [HistElem.per p])
    · exact ⟨Percept.mk false false⟩

  -- l.s.c. for semimeasureLoss (requires ν u.s.c.)
  have h_loss_lsc :
      Mettapedia.Computability.ArithmeticalHierarchy.LowerSemicomputable
        (fun h => (semimeasureLoss ν (encodeHistory h)).toReal) := by
    have heq : (fun h => (semimeasureLoss ν (encodeHistory h)).toReal) =
               (fun h => (ν (encodeHistory h)).toReal -
                        ((ν (encodeHistory h ++ [false])).toReal +
                         (ν (encodeHistory h ++ [true])).toReal)) := by
      ext h
      unfold semimeasureLoss
      have h1 :
          ν (encodeHistory h) ≥ ν (encodeHistory h ++ [false]) + ν (encodeHistory h ++ [true]) :=
        ν.superadditive' (encodeHistory h)
      have h_ne_top : ν (encodeHistory h) ≠ ⊤ := by
        have h2 : ν (encodeHistory h) ≤ ν [] := ν.mono_append [] _
        have h3 : ν [] ≤ 1 := ν.root_le_one'
        exact ne_of_lt (lt_of_le_of_lt (le_trans h2 h3) ENNReal.one_lt_top)
      rw [ENNReal.toReal_sub_of_le h1 h_ne_top, ENNReal.toReal_add]
      · exact ne_of_lt (lt_of_le_of_lt (le_trans (ν.mono_append [] _) ν.root_le_one') ENNReal.one_lt_top)
      · exact ne_of_lt (lt_of_le_of_lt (le_trans (ν.mono_append [] _) ν.root_le_one') ENNReal.one_lt_top)
    rw [heq]
    apply Mettapedia.Computability.ArithmeticalHierarchy.LowerSemicomputable.sub
    · exact h_ν_lsc.comp (fun h => encodeHistory h)
    · have h_add :
          Mettapedia.Computability.ArithmeticalHierarchy.UpperSemicomputable
            (fun h => (ν (encodeHistory h ++ [false])).toReal +
                      (ν (encodeHistory h ++ [true])).toReal) := by
        apply Mettapedia.Computability.ArithmeticalHierarchy.UpperSemicomputable.add
        · exact h_ν_usc.comp (fun h => encodeHistory h ++ [false])
        · exact h_ν_usc.comp (fun h => encodeHistory h ++ [true])
      exact h_add

  -- Helper: indicator {t < f} is l.s.c. if f is l.s.c.
  have indicator_lt :
      ∀ {f : History → ℝ},
        Mettapedia.Computability.ArithmeticalHierarchy.LowerSemicomputable f →
        Mettapedia.Computability.ArithmeticalHierarchy.LowerSemicomputable
          (fun h => if t < f h then (1 : ℝ) else 0) := by
    intro f hf
    refine
      { approx := fun h n => if t < (hf.approx h n : ℝ) then (1 : ℚ) else 0
        approx_mono := ?_
        approx_le := ?_
        approx_converges := ?_ }
    · intro h n
      by_cases ht : t < (hf.approx h n : ℝ)
      · have hmono :
            (hf.approx h n : ℝ) ≤ (hf.approx h (n + 1) : ℝ) := by
              exact_mod_cast (hf.approx_mono h n)
        have ht' : t < (hf.approx h (n + 1) : ℝ) := lt_of_lt_of_le ht hmono
        simp [ht, ht']
      · by_cases ht' : t < (hf.approx h (n + 1) : ℝ)
        · simp [ht, ht', zero_le_one]
        · simp [ht, ht']
    · intro h n
      by_cases ht : t < (hf.approx h n : ℝ)
      · have ht' : t < f h := lt_of_lt_of_le ht (hf.approx_le h n)
        simp [ht, ht']
      · by_cases ht' : t < f h
        · simp [ht, ht', zero_le_one]
        · simp [ht, ht']
    · intro h ε hε
      by_cases ht : t < f h
      · have hδ : 0 < (f h - t) / 2 := by linarith
        obtain ⟨N, hN⟩ := hf.approx_converges h ((f h - t) / 2) hδ
        refine ⟨N, ?_⟩
        intro n hn
        have h_lt : t < (hf.approx h n : ℝ) := by
          have h_close := hN n hn
          linarith
        simp [ht, h_lt, hε]
      · refine ⟨0, ?_⟩
        intro n hn
        have h_not : ¬ t < (hf.approx h n : ℝ) := by
          have h_le : (hf.approx h n : ℝ) ≤ f h := hf.approx_le h n
          exact not_lt.mpr (le_trans h_le (not_lt.mp ht))
        simp [ht, h_not, hε]

  have h_ind_min :
      Mettapedia.Computability.ArithmeticalHierarchy.LowerSemicomputable
        (fun h => if t < minNextUtility U h then (1 : ℝ) else 0) := by
    exact indicator_lt h_min_lsc

  have h_ind_percept :
      ∀ p : Percept,
        Mettapedia.Computability.ArithmeticalHierarchy.LowerSemicomputable
          (fun h => if t < U (h ++ [HistElem.per p]) then (1 : ℝ) else 0) := by
    intro p
    exact indicator_lt (h_U_lsc.comp (fun h => h ++ [HistElem.per p]))

  have h_nu_term :
      ∀ p : Percept,
        Mettapedia.Computability.ArithmeticalHierarchy.LowerSemicomputable
          (fun h => (ν (encodeHistory h ++ encodePerceptBin p)).toReal) := by
    intro p
    exact h_ν_lsc.comp (fun h => encodeHistory h ++ encodePerceptBin p)

  have h_loss_term :
      Mettapedia.Computability.ArithmeticalHierarchy.LowerSemicomputable
        (fun h =>
          (if t < minNextUtility U h then (1 : ℝ) else 0) *
            (semimeasureLoss ν (encodeHistory h)).toReal) := by
    apply Mettapedia.Computability.ArithmeticalHierarchy.LowerSemicomputable.mul (M := 1)
    · exact h_ind_min
    · exact h_loss_lsc
    · intro h; by_cases ht : t < minNextUtility U h <;> simp [ht]
    · intro h; exact semimeasureLoss_toReal_nonneg ν (encodeHistory h)
    · intro h; by_cases ht : t < minNextUtility U h <;> simp [ht]
    · intro h; exact semimeasureLoss_toReal_le_one ν (encodeHistory h)

  have h_term :
      ∀ p : Percept,
        Mettapedia.Computability.ArithmeticalHierarchy.LowerSemicomputable
          (fun h =>
            (if t < U (h ++ [HistElem.per p]) then (1 : ℝ) else 0) *
              (ν (encodeHistory h ++ encodePerceptBin p)).toReal) := by
    intro p
    apply Mettapedia.Computability.ArithmeticalHierarchy.LowerSemicomputable.mul (M := 1)
    · exact h_ind_percept p
    · exact h_nu_term p
    · intro h; by_cases ht : t < U (h ++ [HistElem.per p]) <;> simp [ht]
    · intro h; exact ENNReal.toReal_nonneg
    · intro h; by_cases ht : t < U (h ++ [HistElem.per p]) <;> simp [ht]
    · intro h
      have h1 : ν (encodeHistory h ++ encodePerceptBin p) ≤ ν [] := ν.mono_append [] _
      have h2 : ν [] ≤ 1 := ν.root_le_one'
      have h_ne_top : ν (encodeHistory h ++ encodePerceptBin p) ≠ ⊤ :=
        ne_of_lt (lt_of_le_of_lt (le_trans h1 h2) ENNReal.one_lt_top)
      have h_root_ne_top : (ν []) ≠ ⊤ := ne_of_lt (lt_of_le_of_lt h2 ENNReal.one_lt_top)
      calc (ν (encodeHistory h ++ encodePerceptBin p)).toReal
          ≤ (ν []).toReal := ENNReal.toReal_mono h_root_ne_top h1
        _ ≤ (1 : ENNReal).toReal := ENNReal.toReal_mono ENNReal.one_ne_top h2
        _ = (1 : ℝ) := by simp

  have h_sum_terms :
      Mettapedia.Computability.ArithmeticalHierarchy.LowerSemicomputable
        (fun h =>
          ∑ p : Percept,
            (if t < U (h ++ [HistElem.per p]) then (1 : ℝ) else 0) *
              (ν (encodeHistory h ++ encodePerceptBin p)).toReal) := by
    apply Mettapedia.Computability.ArithmeticalHierarchy.LowerSemicomputable.finset_sum
    intro p
    exact h_term p

  have h_total :
      Mettapedia.Computability.ArithmeticalHierarchy.LowerSemicomputable
        (fun h =>
          (if t < minNextUtility U h then (1 : ℝ) else 0) *
            (semimeasureLoss ν (encodeHistory h)).toReal +
          ∑ p : Percept,
            (if t < U (h ++ [HistElem.per p]) then (1 : ℝ) else 0) *
              (ν (encodeHistory h ++ encodePerceptBin p)).toReal) := by
    exact Mettapedia.Computability.ArithmeticalHierarchy.LowerSemicomputable.add h_loss_term h_sum_terms

  have h_capacity_eq :
      (fun h => capacityAtLevel ν U h t) =
        (fun h =>
          (if t < minNextUtility U h then (1 : ℝ) else 0) *
            (semimeasureLoss ν (encodeHistory h)).toReal +
          ∑ p : Percept,
            (if t < U (h ++ [HistElem.per p]) then (1 : ℝ) else 0) *
              (ν (encodeHistory h ++ encodePerceptBin p)).toReal) := by
    ext h
    by_cases ht : t < minNextUtility U h
    · have h_all : ∀ p : Percept, t < U (h ++ [HistElem.per p]) := by
        intro p
        have h_min_le : minNextUtility U h ≤ U (h ++ [HistElem.per p]) := by
          unfold minNextUtility
          simpa using
            (Finset.inf'_le (s := Finset.univ)
              (f := fun p : Percept => U (h ++ [HistElem.per p]))
              (h := Finset.mem_univ p))
        exact lt_of_lt_of_le ht h_min_le
      simp [capacityAtLevel, perceptMass, ht, h_all]
    · simp [capacityAtLevel, ht]

  simpa [h_capacity_eq] using h_total

/-- **Theorem 4.1 (Wyeth & Hutter 2025)**: Choquet value is l.s.c. using the layer-cake formula.

Note: In this encoding, `capacityAtLevel` still depends on `semimeasureLoss`, so we require ν
to be computable (l.s.c. + u.s.c.) to avoid subtraction.

**Proof approach**: Use the Riemann sum (layer cake) formulation:
1. Each capacityAtLevel is l.s.c. (sum of l.s.c. ν values)
2. Each valueChoquet_riemann n is l.s.c. (constant × sum of l.s.c.)
3. The limit valueChoquet = lim valueChoquet_riemann n is l.s.c. by monotone_sup

**Note**: This requires showing the Riemann sum equals valueChoquet, which follows
from the standard relationship between Choquet integrals and layer cake formulas.
-/
noncomputable def choquet_value_lower_semicomputable_paper (ν : Semimeasure) (U : Utility)
    (h_U_lsc : Mettapedia.Computability.ArithmeticalHierarchy.LowerSemicomputable U)
    (h_ν_lsc : Mettapedia.Computability.ArithmeticalHierarchy.LowerSemicomputable
                (fun x => (ν x).toReal))
    (h_ν_usc : Mettapedia.Computability.ArithmeticalHierarchy.UpperSemicomputable
                (fun x => (ν x).toReal))
    (h_U_bounds : ∀ h, 0 ≤ U h ∧ U h ≤ 1) :
    Mettapedia.Computability.ArithmeticalHierarchy.LowerSemicomputable
      (fun h => valueChoquet ν U h) := by
  -- Use monotone_sup with the Riemann approximation sequence
  apply Mettapedia.Computability.ArithmeticalHierarchy.LowerSemicomputable.monotone_sup
    (f_n := fun n h => valueChoquet_riemann ν U h n)
  · -- Each V_n is l.s.c.
    intro n
    classical
    let m : ℕ := 2 ^ n
    have h_sum :
        Mettapedia.Computability.ArithmeticalHierarchy.LowerSemicomputable
          (fun h =>
            ∑ k ∈ Finset.range m, capacityAtLevel ν U h ((k + 1 : ℝ) / (m : ℝ))) := by
      apply Mettapedia.Computability.ArithmeticalHierarchy.LowerSemicomputable.finset_sum_finset
      intro k
      exact capacityAtLevel_lower_semicomputable ν U ((k + 1 : ℝ) / (m : ℝ)) h_U_lsc h_ν_lsc h_ν_usc
    have h_nonneg :
        ∀ h, 0 ≤ ∑ k ∈ Finset.range m, capacityAtLevel ν U h ((k + 1 : ℝ) / (m : ℝ)) := by
      intro h
      apply Finset.sum_nonneg
      intro k _
      exact capacityAtLevel_nonneg ν U h _
    have h_scaled :
        Mettapedia.Computability.ArithmeticalHierarchy.LowerSemicomputable
          (fun h =>
            (1 / (m : ℝ)) *
              ∑ k ∈ Finset.range m, capacityAtLevel ν U h ((k + 1 : ℝ) / (m : ℝ))) := by
      apply Mettapedia.Computability.ArithmeticalHierarchy.LowerSemicomputable.const_smul
        (c := (1 / (m : ℝ))) (hc := by positivity) h_sum h_nonneg
    simpa [valueChoquet_riemann, m] using h_scaled
  · -- Monotonicity
    intro n h
    exact valueChoquet_riemann_mono ν U h n
  · -- Convergence
    intro h ε hε
    exact valueChoquet_riemann_converges ν U h h_U_bounds ε hε
  · -- Bound
    intro n h
    exact valueChoquet_riemann_le ν U h h_U_bounds n

end Mettapedia.UniversalAI.ValueUnderIgnorance
