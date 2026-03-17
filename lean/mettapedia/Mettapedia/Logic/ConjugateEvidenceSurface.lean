import Mettapedia.Logic.PLNWorldModelAdditive
import Mettapedia.Logic.PLNWorldModelAdditiveNoGo
import Mettapedia.Logic.EvidenceDirichlet
import Mettapedia.Logic.EvidenceNormalGamma

/-!
# Conjugate BinaryEvidence Surface

Minimal shared interface for conjugate-family evidence types, capturing only
what Beta (`BinaryEvidence`), Dirichlet (`MultiEvidence k`), and Normal-Gamma
(`NormalGammaEvidence`) actually share:

- `AddCommMonoid` (hplus = coordinatewise addition)
- Observation count extraction (ℝ≥0∞-valued)
- Additive count law: `count(e₁ + e₂) = count(e₁) + count(e₂)`
- Zero count law: `count(0) = 0`

Does NOT impose: prior type, posterior mean, confidence formula, or
convergence theorem — those differ across families.

## Instances

- `BinaryEvidence` (Beta-Bernoulli): count = `pos + neg`
- `MultiEvidence k` (Dirichlet-Multinomial): count = `↑(∑ i, counts i)`
- `NormalGammaEvidence` (Normal-Gamma): count = `↑n`

## Bridge

The generic `genAdditiveExtension` from `PLNWorldModelAdditive` applies to all
three families via the `AddCommMonoid` constraint. The `ConjugateEvidence` class
adds the observation-count homomorphism, enabling count-distribution theorems
across arbitrary multisets of observations.
-/

namespace Mettapedia.Logic.ConjugateEvidenceSurface

open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.Logic.EvidenceBeta
open Mettapedia.Logic.EvidenceDirichlet
open Mettapedia.Logic.EvidenceNormalGamma
open Mettapedia.Logic.PLNWorldModelAdditive
open scoped ENNReal

/-! ## Conjugate BinaryEvidence Class -/

/-- Shared interface for conjugate-family evidence types.

    Captures the observation-count homomorphism: evidence aggregation (hplus)
    preserves total observation count. This is the common structure across
    Beta-Bernoulli, Dirichlet-Multinomial, and Normal-Gamma families. -/
class ConjugateEvidence (Ev : Type*) extends AddCommMonoid Ev where
  /-- Total observation count as ℝ≥0∞. -/
  observationCount : Ev → ℝ≥0∞
  /-- Observation count is additive over hplus. -/
  observationCount_add : ∀ e₁ e₂ : Ev,
    observationCount (e₁ + e₂) = observationCount e₁ + observationCount e₂
  /-- Zero evidence has zero observation count. -/
  observationCount_zero : observationCount 0 = 0

/-- Generic confidence view induced only by total observation count.

    This is the common `n / (n + κ)` pattern shared by binary PLN evidence and
    the continuous Normal-Gamma layer, phrased at the abstract conjugate-evidence
    level. -/
noncomputable def observationConfidence {Ev : Type*} [ConjugateEvidence Ev]
    (κ : ℝ≥0∞) (e : Ev) : ℝ≥0∞ :=
  ConjugateEvidence.observationCount e /
    (ConjugateEvidence.observationCount e + κ)

@[simp] theorem observationConfidence_zero {Ev : Type*} [ConjugateEvidence Ev]
    (κ : ℝ≥0∞) :
    observationConfidence κ (0 : Ev) = 0 := by
  simp [observationConfidence, ConjugateEvidence.observationCount_zero]

theorem observationCount_eq_zero_of_add_idempotent {Ev : Type*} [ConjugateEvidence Ev]
    {e : Ev}
    (hfin : ConjugateEvidence.observationCount e ≠ ⊤)
    (hidem : e + e = e) :
    ConjugateEvidence.observationCount e = 0 := by
  have hcountIdem :
      ConjugateEvidence.observationCount e + ConjugateEvidence.observationCount e =
        ConjugateEvidence.observationCount e := by
    calc
      ConjugateEvidence.observationCount e + ConjugateEvidence.observationCount e
        = ConjugateEvidence.observationCount (e + e) := by
            rw [ConjugateEvidence.observationCount_add]
      _ = ConjugateEvidence.observationCount e := by simp [hidem]
  exact
    Mettapedia.Logic.PLNWorldModelAdditiveNoGo.EvidenceQuantale.BinaryEvidence.finite_coord_add_idempotent_eq_zero
      hfin hcountIdem

theorem not_add_idempotent_of_finite_nonzero_observationCount {Ev : Type*}
    [ConjugateEvidence Ev] {e : Ev}
    (hfin : ConjugateEvidence.observationCount e ≠ ⊤)
    (hne : ConjugateEvidence.observationCount e ≠ 0) :
    e + e ≠ e := by
  intro hidem
  exact hne (observationCount_eq_zero_of_add_idempotent hfin hidem)

/-! ## Instances -/

/-- Beta-Bernoulli: observation count = positive + negative evidence. -/
noncomputable instance instConjugateEvidenceBeta : ConjugateEvidence BinaryEvidence where
  observationCount e := e.pos + e.neg
  observationCount_add e₁ e₂ := by
    show (e₁ + e₂).pos + (e₁ + e₂).neg = (e₁.pos + e₁.neg) + (e₂.pos + e₂.neg)
    simp only [BinaryEvidence.hplus_def]; ring
  observationCount_zero := by
    show BinaryEvidence.pos (BinaryEvidence.zero) + BinaryEvidence.neg (BinaryEvidence.zero) = 0
    simp [BinaryEvidence.zero]

/-- `Zero` instance for `MultiEvidence k`. -/
instance instZeroMultiEvidence : Zero (MultiEvidence k) := ⟨MultiEvidence.zero⟩

/-- `AddCommMonoid` instance for `MultiEvidence k`. -/
instance instAddCommMonoidMultiEvidence : AddCommMonoid (MultiEvidence k) where
  add := MultiEvidence.hplus
  add_assoc := MultiEvidence.hplus_assoc
  zero_add := MultiEvidence.zero_hplus
  add_zero := MultiEvidence.hplus_zero
  add_comm := MultiEvidence.hplus_comm
  nsmul := nsmulRec

/-- Dirichlet-Multinomial: observation count = ↑(∑ i, counts i). -/
noncomputable instance instConjugateEvidenceDirichlet :
    ConjugateEvidence (MultiEvidence k) where
  observationCount e := ↑e.total
  observationCount_add e₁ e₂ := by
    show ↑(MultiEvidence.hplus e₁ e₂).total = (↑e₁.total : ℝ≥0∞) + ↑e₂.total
    have h : (MultiEvidence.hplus e₁ e₂).total = e₁.total + e₂.total :=
      MultiEvidence.total_hplus e₁ e₂
    rw [h, Nat.cast_add]
  observationCount_zero := by
    show (↑(MultiEvidence.zero : MultiEvidence k).total : ℝ≥0∞) = 0
    simp [MultiEvidence.total, MultiEvidence.zero]

/-- Normal-Gamma: observation count = ↑n. -/
noncomputable instance instConjugateEvidenceNormalGamma :
    ConjugateEvidence NormalGammaEvidence where
  observationCount e := ↑e.n
  observationCount_add e₁ e₂ := by
    show (↑(NormalGammaEvidence.hplus e₁ e₂).n : ℝ≥0∞) = ↑e₁.n + ↑e₂.n
    simp only [NormalGammaEvidence.hplus]
    exact Nat.cast_add (R := ℝ≥0∞) e₁.n e₂.n
  observationCount_zero := by simp

/-! ## Conjugate-Update Fact Index

Each conjugate family has an "aggregation = update" theorem connecting
`hplus` to posterior parameter update. These aliases provide a single
audit-friendly entry point.

| Family | Theorem | Status |
|---|---|---|
| Beta | `beta_hplus_is_aggregation` | ✅ fully proved (`EvidenceBeta:602`) |
| Dirichlet | `dirichlet_hplus_is_update` | ✅ fully proved (`EvidenceDirichlet:211`) |
| Normal-Gamma | `normalGamma_hplus_sufficient_statistics` | ✅ componentwise (`EvidenceNormalGamma:466–473`) |

Normal-Gamma gap: no explicit `evidence_aggregation_is_conjugate_update` theorem
connecting hplus to Normal-Gamma posterior parameter update. The docstring in
`EvidenceNormalGamma.lean` (line 507) asserts this correspondence but the machine-checked
theorem only covers componentwise additivity of (n, sum, sumSq), not the full
posterior parameter equations. This is a current formalization gap.
-/

/-- Beta: hplus sums sufficient statistics (pos, neg).
    Alias for `EvidenceBeta.hplus_is_beta_aggregation`. -/
theorem beta_hplus_is_aggregation (e₁ e₂ : BinaryEvidence) :
    (e₁ + e₂).pos = e₁.pos + e₂.pos ∧
    (e₁ + e₂).neg = e₁.neg + e₂.neg :=
  Mettapedia.Logic.EvidenceBeta.hplus_is_beta_aggregation e₁ e₂

/-- Dirichlet: hplus = conjugate posterior update, coordinatewise.
    Alias for `EvidenceDirichlet.evidence_aggregation_is_dirichlet_update`. -/
theorem dirichlet_hplus_is_update {k : ℕ}
    (prior : DirichletParams k)
    (e₁ e₂ : MultiEvidence k) (i : Fin k) :
    (⟨prior, e₁ + e₂⟩ : EvidenceDirichletParams k).posteriorParam i =
    (⟨prior, e₁⟩ : EvidenceDirichletParams k).posteriorParam i +
      e₂.counts i :=
  evidence_aggregation_is_dirichlet_update prior e₁ e₂ i

/-- Normal-Gamma: hplus is componentwise additive on sufficient statistics (n, sum, sumSq).

    This is the machine-checked part of the Normal-Gamma conjugate-update
    correspondence. The full posterior parameter update (involving the prior
    μ₀, κ₀, α₀, β₀) is documented in `EvidenceNormalGamma.lean` but not yet
    formalized as a single theorem. -/
theorem normalGamma_hplus_sufficient_statistics (e₁ e₂ : NormalGammaEvidence) :
    (e₁ + e₂).n = e₁.n + e₂.n ∧
    (e₁ + e₂).sum = e₁.sum + e₂.sum ∧
    (e₁ + e₂).sumSq = e₁.sumSq + e₂.sumSq :=
  ⟨hplus_n e₁ e₂, hplus_sum e₁ e₂, hplus_sumSq e₁ e₂⟩

/-! ## Bridge to Generic Additive Extension -/

/-- Observation count distributes through the generic additive extension.

    For any conjugate evidence type and atomic contribution function,
    the total observation count of the aggregated evidence equals the
    sum of individual observation counts. -/
theorem observationCount_genAdditiveExtension
    {Obs Query Ev : Type*} [ConjugateEvidence Ev]
    (a : GenAtomicEvidenceContribution Obs Query Ev)
    (σ : Multiset Obs) (q : Query) :
    ConjugateEvidence.observationCount (genAdditiveExtension a σ q) =
      genAdditiveExtension
        (Ev := ℝ≥0∞)
        (fun o q => ConjugateEvidence.observationCount (a o q)) σ q := by
  induction σ using Multiset.induction_on with
  | empty => simp [ConjugateEvidence.observationCount_zero]
  | @cons o σ ih =>
    rw [genAdditiveExtension_cons, ConjugateEvidence.observationCount_add,
        ih, genAdditiveExtension_cons]

/-- When each atomic contribution represents one observation, the generic additive
    extension recovers the multiset cardinality through `observationCount`. -/
theorem observationCount_genAdditiveExtension_of_unit
    {Obs Query Ev : Type*} [ConjugateEvidence Ev]
    (a : GenAtomicEvidenceContribution Obs Query Ev)
    (hunit : ∀ o q, ConjugateEvidence.observationCount (a o q) = 1)
    (σ : Multiset Obs) (q : Query) :
    ConjugateEvidence.observationCount (genAdditiveExtension a σ q) =
      (σ.card : ℝ≥0∞) := by
  induction σ using Multiset.induction_on with
  | empty =>
      simp [ConjugateEvidence.observationCount_zero]
  | @cons o σ ih =>
      rw [genAdditiveExtension_cons, ConjugateEvidence.observationCount_add,
        hunit, ih]
      rw [add_comm]
      simp

/-- The abstract count-induced confidence of a unit-observation additive extension
    depends only on the multiset cardinality. -/
theorem observationConfidence_genAdditiveExtension_of_unit
    {Obs Query Ev : Type*} [ConjugateEvidence Ev]
    (κ : ℝ≥0∞)
    (a : GenAtomicEvidenceContribution Obs Query Ev)
    (hunit : ∀ o q, ConjugateEvidence.observationCount (a o q) = 1)
    (σ : Multiset Obs) (q : Query) :
    observationConfidence κ (genAdditiveExtension a σ q) =
      (σ.card : ℝ≥0∞) / ((σ.card : ℝ≥0∞) + κ) := by
  simp [observationConfidence, observationCount_genAdditiveExtension_of_unit, hunit]

/-- For binary PLN evidence, the abstract count-induced confidence is exactly the
    existing `BinaryEvidence.toConfidence` view. -/
theorem beta_observationConfidence_eq_toConfidence
    (κ : ℝ≥0∞) (e : BinaryEvidence) :
    observationConfidence κ e = BinaryEvidence.toConfidence κ e := by
  rfl

end Mettapedia.Logic.ConjugateEvidenceSurface
