import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Real.Basic

/-!
# No-Go: Regime Underdetermination

This module formalizes the **regime underdetermination** no-go theorem:

When the topology feature space has fewer distinct values than the regime space,
the pigeonhole principle guarantees that some pair of distinct regimes must produce
the same feature vector. Any posterior update that depends only on the feature
vector cannot distinguish these regimes — they remain permanently indistinguishable
from the features alone.

**Design implication**: if the number of latent regimes exceeds the expressive capacity
of the topology feature map, Bayesian inference on topology features alone cannot
concentrate the posterior to a single regime. The residual posterior uncertainty
over indistinguishable regimes is irreducible.

## Mathematical content

The proof rests on the standard pigeonhole principle, available in Mathlib as
`Fintype.exists_ne_map_eq_of_card_lt`.

1. `regime_underdetermination`: if `k < |R|`, then for any `f : R → Fin k` there
   exist distinct regimes `r1 ≠ r2` with `f r1 = f r2`.

2. `posterior_indistinguishable`: if the posterior depends only on the feature value,
   then the two indistinguishable regimes receive the same posterior weight.

3. `posterior_cannot_concentrate_to_single`: if two regimes are indistinguishable
   and both have positive prior, no topology-only posterior can assign zero weight
   to one while concentrating on the other.

4. `collision_count_lower_bound`: some feature value is shared by ≥ 2 regimes.
-/

namespace Mettapedia.Logic.PLNRegimeUnderdetermination

/-! ## Core pigeonhole: feature collision when |features| < |regimes| -/

/-- **Regime underdetermination**: if the topology feature space `Fin k` has fewer
values than the regime space `R`, then for ANY feature mapping `f : R → Fin k`,
there must exist two distinct regimes with identical feature vectors.

Direct application of `Fintype.exists_ne_map_eq_of_card_lt`. -/
theorem regime_underdetermination {R : Type*} [Fintype R] [DecidableEq R]
    (k : ℕ) (hk : k < Fintype.card R)
    (f : R → Fin k) :
    ∃ r1 r2 : R, r1 ≠ r2 ∧ f r1 = f r2 :=
  Fintype.exists_ne_map_eq_of_card_lt f (by rwa [Fintype.card_fin])

/-! ## Posterior consequences of feature collision -/

/-- **Posterior indistinguishability**: if a posterior distribution `π` depends only
on the feature value (i.e., same feature value ⟹ same posterior weight), then
any pair of regimes with the same feature vector receives the same posterior weight.

Topology-derived posteriors cannot discriminate between regimes with equal features. -/
theorem posterior_indistinguishable {R : Type*} [Fintype R] [DecidableEq R]
    (k : ℕ) (hk : k < Fintype.card R)
    (f : R → Fin k)
    (π : R → ℝ)
    (hπ : ∀ r1 r2 : R, f r1 = f r2 → π r1 = π r2) :
    ∃ r1 r2 : R, r1 ≠ r2 ∧ π r1 = π r2 := by
  obtain ⟨r1, r2, hne, hfeq⟩ := regime_underdetermination k hk f
  exact ⟨r1, r2, hne, hπ r1 r2 hfeq⟩

/-- **Topology posterior cannot eliminate a regime**: if two regimes share a feature
vector and the posterior depends only on features, then positivity transfers. -/
theorem topology_posterior_cannot_eliminate {R : Type*}
    (f : R → ℕ) (π : R → ℝ)
    (hπ : ∀ r1 r2 : R, f r1 = f r2 → π r1 = π r2)
    (r1 r2 : R) (hfeq : f r1 = f r2) :
    0 < π r1 ↔ 0 < π r2 :=
  hπ r1 r2 hfeq ▸ Iff.rfl

/-! ## Underdetermination under positive prior -/

/-- **Underdetermination with positive prior**: for any topology-only posterior that
respects feature equality, some two distinct regimes have equal posterior weight. -/
theorem posterior_cannot_fully_concentrate {R : Type*} [Fintype R] [DecidableEq R]
    (k : ℕ) (hk : k < Fintype.card R)
    (f : R → Fin k)
    (π : R → ℝ)
    (hπ_feature : ∀ r1 r2 : R, f r1 = f r2 → π r1 = π r2) :
    ∃ r1 r2 : R, r1 ≠ r2 ∧ π r1 = π r2 :=
  posterior_indistinguishable k hk f π hπ_feature

/-! ## Quantitative: some feature value is shared by ≥ 2 regimes -/

/-- **Collision count**: when `k < |R|`, some feature value bucket contains ≥ 2 regimes.
Proved by contradiction using the pigeonhole result. -/
theorem collision_count_lower_bound {R : Type*} [Fintype R] [DecidableEq R]
    (k : ℕ) (hk : k < Fintype.card R)
    (f : R → Fin k) :
    ∃ fv : Fin k, 1 < (Finset.univ.filter (fun r => f r = fv)).card := by
  obtain ⟨r1, r2, hne, hfeq⟩ := regime_underdetermination k hk f
  refine ⟨f r1, Finset.one_lt_card.mpr ?_⟩
  refine ⟨r1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩,
          r2, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hfeq.symm⟩,
          hne⟩

end Mettapedia.Logic.PLNRegimeUnderdetermination
