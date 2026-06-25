import Mettapedia.ProbabilityTheory.HigherOrderProbability.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Kyburg's Flattening Theorem

**Status**: Week 2 - Main Theorem 🚧
**Dependencies**: Basic.lean (Week 1 ✅)

This file formalizes Kyburg's key result from "Higher Order Probabilities" (1988):

> "Higher-order probabilities can always be replaced by marginal distributions
> of joint probability distributions."

## Mathematical Content

Given a parametrized distribution (kernel + mixing measure), we prove:
1. **Flattening preserves predictions**: Marginalizing the joint recovers the mixture
2. **Expectation consistency**: E[U] under flattened = E[E[U|θ]]
3. **No computational advantage**: Decisions using joint = decisions using flattened

## Main Theorems

* `kyburg_flattening` : The core reduction theorem
* `expectation_consistency` : Expected utilities are preserved
* `kyburg_no_advantage` : Decision-theoretic equivalence

## Proof Strategy

1. Start with definition of flattening (from Basic.lean)
2. Use Fubini's theorem to interchange integration
3. Show marginalization property: ∫_Θ P(θ, x) dθ = P(x)
4. Extend to expectation of utilities

## References

- Kyburg, H.E. (1988). "Higher Order Probabilities". Technical Report.
- This is the multiplication/join operation of the Giry monad

-/

namespace Mettapedia.ProbabilityTheory.HigherOrderProbability

open MeasureTheory ProbabilityTheory ParametrizedDistribution
open scoped ENNReal

variable {Θ X : Type*} [MeasurableSpace Θ] [MeasurableSpace X]

/-! ## The Main Theorem -/

/-- **Kyburg's Flattening Theorem** (1988).

Given a "second-order" probability represented as a parametrized distribution,
marginalizing the joint distribution P(θ, x) = μ(θ) · kernel(θ)(x) over Θ
recovers the flattened distribution that makes the same predictions on X.

**Interpretation**: "Higher-order probabilities offer no computational or conceptual
advantage" - they can always be replaced by a joint distribution whose marginals
give the same predictions.

**Formal Statement**: For any measurable set A ⊆ X,
  P_flattened(A) = ∫_Θ P_θ(A) dμ(θ)

This says: the probability of A under the flattened distribution equals the expected
probability of A under the parametrized family, weighted by the mixing measure.
-/
theorem kyburg_flattening (pd : ParametrizedDistribution Θ X) (A : Set X)
    (hA : MeasurableSet A) :
    (flatten pd) A = ∫⁻ θ, (pd.kernel θ) A ∂pd.mixingMeasure := by
  -- This is exactly flatten_apply from Basic.lean
  exact flatten_apply pd A hA

/-! ## Corollaries and Extensions -/

/-- The flattening is the marginal of the joint over X.

This makes explicit that Kyburg's construction satisfies the classical
marginalization property: P(x) = ∫_Θ P(θ, x) dθ.
-/
theorem flatten_is_marginal (pd : ParametrizedDistribution Θ X) :
    flatten pd = (kyburgJoint pd).map Prod.snd := by
  rw [flatten_eq_snd_kyburgJoint]
  -- snd is defined as map Prod.snd
  rfl

/-- **Expectation Consistency** (Kyburg's Expectation Condition).

The expectation of a utility U under the flattened distribution equals
the "meta-expectation": first compute E[U|θ] for each θ, then average
these conditional expectations weighted by μ.

Formally: E_flattened[U] = E_μ[E_θ[U]]

This is the key to Kyburg's "no advantage" result: any decision problem
can be solved using just the flattened distribution.
-/
theorem expectation_consistency (pd : ParametrizedDistribution Θ X)
    (U : X → ℝ≥0∞) (hU : Measurable U) :
    ∫⁻ x, U x ∂(flatten pd) = ∫⁻ θ, (∫⁻ x, U x ∂(pd.kernel θ)) ∂pd.mixingMeasure := by
  unfold flatten
  rw [Measure.lintegral_bind pd.kernel.aemeasurable hU.aemeasurable]

/-! ## Decision-Theoretic Equivalence -/

/-- **Kyburg's No-Advantage Theorem** (informal version).

For any decision problem with utilities U(action, x), the optimal action
is the same whether we:
- Use the full joint P(θ, x) and integrate out θ
- Use the flattened distribution P(x) directly

This formalizes Kyburg's conclusion: "there is no conceptual advantage to
representing [probabilities] as first and second order as opposed to joint."

We prove this for expected utilities (the foundation of decision theory).
-/
theorem kyburg_no_advantage {Action : Type*} (pd : ParametrizedDistribution Θ X)
    (U : Action → X → ℝ≥0∞) (hU : ∀ a, Measurable (U a)) (a : Action) :
    ∫⁻ x, U a x ∂(flatten pd) =
    ∫⁻ θ, (∫⁻ x, U a x ∂(pd.kernel θ)) ∂pd.mixingMeasure := by
  exact expectation_consistency pd (U a) (hU a)

/-! ## Special Cases and Examples -/

section FiniteSpaces

variable (Θ_fin : Type*) [Fintype Θ_fin] [MeasurableSpace Θ_fin]
  [MeasurableSingletonClass Θ_fin]

/-- In the finite case, the flattening formula becomes a finite sum.

This is pedagogically useful: Kyburg's reduction is just a weighted average
when both parameter space and observation space are finite.
-/
theorem kyburg_flattening_finite (pd : ParametrizedDistribution Θ_fin X)
    (A : Set X) (hA : MeasurableSet A) :
    (flatten pd) A = ∑' θ : Θ_fin, (pd.mixingMeasure {θ}) * (pd.kernel θ A) := by
  -- This follows from kyburg_flattening; the finite case is just notation
  -- For fintype, ∑ and ∑' are equivalent
  simp [kyburg_flattening pd A hA, lintegral_fintype, mul_comm]

end FiniteSpaces

/-! ## Connection to Probability Monad -/

/-- Flattening is the monadic join/multiplication operation.

In categorical terms, the Giry monad has:
- Unit: η(x) = δ_x (Dirac measure)
- Multiplication: μ ⋆ (Θ → Measure X) ↦ flatten(μ, kernel)

Kyburg's theorem says this multiplication is well-defined and gives
the "right" semantics for higher-order probability.
-/
theorem flatten_is_monad_multiplication (pd : ParametrizedDistribution Θ X) :
    flatten pd = pd.mixingMeasure.bind pd.kernel := by
  rfl  -- This is definitional

/-! ## Remarks

1. **Sufficient for Decision Theory**: The theorem shows that for any utility function,
   decisions made with the flattened distribution are identical to decisions made with
   the full joint distribution.

2. **Computational Efficiency**: In practice, storing just the flattened distribution
   can be much more efficient than maintaining the full joint, especially when Θ is
   high-dimensional.

3. **Connection to PLN**: PLN's evidence (n⁺, n⁻) is exactly the sufficient statistic
   for a Beta-Bernoulli Kyburg flattening. This will be formalized in
   PLN/Bridges/ProbabilityTheory/PLNKyburgReduction.lean (Phase 2).

4. **De Finetti Connection**: De Finetti's representation theorem is a special case
   where Θ = [0,1] and kernel(θ) = Bernoulli(θ). This will be formalized in
   DeFinettiConnection.lean (Week 3).
-/

end Mettapedia.ProbabilityTheory.HigherOrderProbability
