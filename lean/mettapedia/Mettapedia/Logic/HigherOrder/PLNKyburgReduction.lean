import Mettapedia.Logic.EvidenceQuantale
import Mettapedia.Logic.EvidenceBeta
import Mettapedia.ProbabilityTheory.HigherOrderProbability.KyburgFlattening
import Mettapedia.ProbabilityTheory.HigherOrderProbability.GiryMonad
import Mettapedia.ProbabilityTheory.HigherOrderProbability.DeFinettiConnection

/-!
# PLN Distributional-HigherOrder (Kyburg) Reduction Bridge

This module exposes a theorem-level, sorry-free bridge between:

- PLN evidence/distributional semantics (`BinaryEvidence`, Beta-style updates), and
- Kyburg higher-order flattening (`ParametrizedDistribution`, flattening/expectation laws).

It is intentionally lightweight and re-exports proved theorems from:

- `Mettapedia.Logic.EvidenceBeta`
- `Mettapedia.ProbabilityTheory.HigherOrderProbability.KyburgFlattening`
- `Mettapedia.ProbabilityTheory.HigherOrderProbability.GiryMonad`
- `Mettapedia.ProbabilityTheory.HigherOrderProbability.DeFinettiConnection`
-/

namespace Mettapedia.Logic.PLNKyburgReduction

open scoped ENNReal
open MeasureTheory
open Mettapedia.Logic.EvidenceQuantale

abbrev BinaryContext := Mettapedia.Logic.EvidenceClass.BinaryContext

abbrev ParametrizedDistribution :=
  Mettapedia.ProbabilityTheory.HigherOrderProbability.ParametrizedDistribution

/-! ## BinaryEvidence-side bridge lemmas -/

/-- Context-aware PLN strength is exactly a Beta posterior-mean form over
shifted pseudo-count coordinates in `ℝ≥0∞`. -/
theorem strengthWith_eq_beta_posterior_meanENN (e : BinaryEvidence) (ctx : BinaryContext) :
    Mettapedia.Logic.EvidenceQuantale.BinaryEvidence.strengthWith ctx e =
      (ctx.α₀ + e.pos) / ((ctx.α₀ + e.pos) + (ctx.β₀ + e.neg)) := by
  simp [Mettapedia.Logic.EvidenceQuantale.BinaryEvidence.strengthWith, add_comm, add_left_comm]

/-- BinaryEvidence determines the shifted Beta pseudo-count coordinates used by
`strengthWith`; this is the compact sufficient-statistic encoding view. -/
theorem evidence_encodes_beta_parameters (e : BinaryEvidence) (ctx : BinaryContext) :
    ∃ α β : ℝ≥0∞,
      α = ctx.α₀ + e.pos ∧
      β = ctx.β₀ + e.neg ∧
      Mettapedia.Logic.EvidenceQuantale.BinaryEvidence.strengthWith ctx e = α / (α + β) := by
  refine ⟨ctx.α₀ + e.pos, ctx.β₀ + e.neg, rfl, rfl, ?_⟩
  simpa [add_assoc, add_comm, add_left_comm] using
    strengthWith_eq_beta_posterior_meanENN (e := e) (ctx := ctx)

/-- PLN evidence aggregation is coordinatewise count aggregation
(Beta conjugate update at the sufficient-statistic level). -/
abbrev hplus_is_bayesian_update :=
  Mettapedia.Logic.EvidenceBeta.hplus_is_beta_aggregation

/-- Explicit parameter-level conjugate-update identity for Beta pseudo-counts. -/
abbrev evidence_aggregation_is_conjugate_update :=
  Mettapedia.Logic.EvidenceBeta.evidence_aggregation_is_conjugate_update

/-- Exchangeable binary PLN evidence gives the Bayes-optimal sufficient-statistic story. -/
abbrev pln_is_bayes_optimal_for_exchangeable :=
  Mettapedia.Logic.EvidenceBeta.pln_is_bayes_optimal_for_exchangeable

/-! ## Kyburg flattening and decision-equivalence re-exports -/

abbrev kyburg_flattening :=
  @Mettapedia.ProbabilityTheory.HigherOrderProbability.kyburg_flattening

abbrev flatten_is_marginal :=
  @Mettapedia.ProbabilityTheory.HigherOrderProbability.flatten_is_marginal

abbrev expectation_consistency :=
  @Mettapedia.ProbabilityTheory.HigherOrderProbability.expectation_consistency

abbrev kyburg_no_advantage :=
  @Mettapedia.ProbabilityTheory.HigherOrderProbability.kyburg_no_advantage

abbrev flatten_is_monad_multiplication :=
  @Mettapedia.ProbabilityTheory.HigherOrderProbability.flatten_is_monad_multiplication

abbrev flatten_is_bind :=
  @Mettapedia.ProbabilityTheory.HigherOrderProbability.flatten_is_bind

abbrev flatten_is_join :=
  @Mettapedia.ProbabilityTheory.HigherOrderProbability.flatten_is_join

abbrev flatten_associativity :=
  @Mettapedia.ProbabilityTheory.HigherOrderProbability.flatten_associativity

abbrev flatten_associativity_kernel :=
  @Mettapedia.ProbabilityTheory.HigherOrderProbability.flatten_associativity_kernel

abbrev kyburg_no_advantage_via_monad :=
  @Mettapedia.ProbabilityTheory.HigherOrderProbability.kyburg_no_advantage_via_monad

/-! ## Concrete De Finetti -> Kyburg flattening bridge (Bool words) -/

abbrev deFinetti_flatten_apply_singleton :=
  Mettapedia.ProbabilityTheory.HigherOrderProbability.DeFinettiConnection.flatten_apply_singleton

/-! ## Concrete Chapter-7 worked fixture -/

/-- Concrete worked example (Chapter 7):
with uniform Beta prior `(α₀,β₀)=(1,1)` and observed evidence `(n⁺,n⁻)=(3,1)`,
the context-aware PLN strength is exactly the corresponding posterior-mean ratio. -/
theorem chapter7_worked_example_strength_uniform_3_1 :
    Mettapedia.Logic.EvidenceQuantale.BinaryEvidence.strengthWith
        Mettapedia.Logic.EvidenceClass.BinaryContext.uniform
        ({ pos := (3 : ℝ≥0∞), neg := (1 : ℝ≥0∞) } : BinaryEvidence) =
      ((1 : ℝ≥0∞) + 3) / (((1 : ℝ≥0∞) + 3) + ((1 : ℝ≥0∞) + 1)) := by
  simpa [Mettapedia.Logic.EvidenceClass.BinaryContext.uniform] using
    strengthWith_eq_beta_posterior_meanENN
      ({ pos := (3 : ℝ≥0∞), neg := (1 : ℝ≥0∞) } : BinaryEvidence)
      Mettapedia.Logic.EvidenceClass.BinaryContext.uniform

/-! ## Chapter-7-facing aggregate statement -/

/-- Compact chapter-facing bundle: PLN evidence aggregation + Kyburg flattening
decision-equivalence are both available as proved endpoints in the core stack. -/
theorem chapter7_distributional_kyburg_bridge_available :
    (∀ e₁ e₂ : BinaryEvidence,
      (e₁ + e₂).pos = e₁.pos + e₂.pos ∧ (e₁ + e₂).neg = e₁.neg + e₂.neg) ∧
    (∀ {Θ X : Type*} [MeasurableSpace Θ] [MeasurableSpace X]
        (pd : ParametrizedDistribution Θ X) (A : Set X),
        MeasurableSet A →
          (Mettapedia.ProbabilityTheory.HigherOrderProbability.ParametrizedDistribution.flatten pd) A =
            ∫⁻ θ, (pd.kernel θ) A ∂pd.mixingMeasure) := by
  constructor
  · intro e₁ e₂
    exact hplus_is_bayesian_update e₁ e₂
  · intro Θ X _ _ pd A hA
    simpa using kyburg_flattening pd A hA

end Mettapedia.Logic.PLNKyburgReduction
