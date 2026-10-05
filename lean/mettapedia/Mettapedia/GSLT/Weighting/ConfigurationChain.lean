import Mettapedia.GSLT.Weighting.WeightTheory
import Mettapedia.GSLT.Weighting.RateGenerator

/-!
# The chain on configurations

The weighted coalgebra, read on a finite set of configurations, has a generator
that is a rate matrix, and its exponential is a Markov semigroup: at every time
a stochastic matrix, composing over time and differentiating to the generator.
The chain lives on configurations, terms with their weight maps.
`DynamicWeights.no_term_rate` shows that the rate out of a term may depend on
the map, so it is not in general a chain on terms.

On a set closed under successors nothing leaves the set, and the generator's
exit rate is the total propensity less the weight of the steps that return to
the same configuration.

The finite reading is a hypothesis, not a convenience. The book's configuration
space is terms with real weight maps, a continuum. With infinitely many
configurations a generator may explode: a redex whose firing doubles its own
weight has holding times whose sum is finite. The reachable configurations
must be finite in number, or the chain must be shown not to explode.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Weighting

open Mettapedia.GSLT
open Mettapedia.GSLT.Core.InteractionEvent

universe uTerm uSite uEvent uKey uCtx

section Chain

variable {theory : GSLT.{uTerm}} {P : InteractionPresentation.{uSite, uEvent} theory}
  {K : Keyed.{uTerm, uSite, uEvent, uKey} P} (A : Augmented K ℝ)
  (funded : ∀ {source : theory.Term}, P.Enabled source → Prop)
  [∀ {source : theory.Term} (redex : P.Enabled source), Decidable (funded redex)]
  [∀ source : theory.Term, Fintype (P.Enabled source)]
  [DecidableEq (theory.Term × WeightMap K ℝ)]

namespace Augmented

/-- The weighted coalgebra read on a finite set of configurations. -/
def restricted (S : Finset (theory.Term × WeightMap K ℝ)) (c c' : S) : ℝ :=
  A.coalgebra funded c.val c'.val

omit [∀ source : theory.Term, Fintype (P.Enabled source)]
  [DecidableEq (theory.Term × WeightMap K ℝ)] in
theorem geometricFactor_nonneg (nonneg : ∀ context, 0 ≤ A.geometric context)
    {rule : P.Site} {source target : theory.Term} (event : P.Event rule source target) :
    0 ≤ A.geometricFactor event :=
  List.prod_nonneg fun _ member => by
    obtain ⟨context, _, rfl⟩ := List.mem_map.mp member
    exact nonneg context

theorem coalgebra_nonneg (geometricNonneg : ∀ context, 0 ≤ A.geometric context)
    (configuration successorConfiguration : theory.Term × WeightMap K ℝ)
    (mapNonneg : ∀ key, 0 ≤ configuration.2 key) :
    0 ≤ A.coalgebra funded configuration successorConfiguration :=
  Finset.sum_nonneg fun redex _ =>
    mul_nonneg (mul_nonneg (mapNonneg _) (A.geometricFactor_nonneg geometricNonneg _))
      (show (0 : ℝ) ≤ gate funded redex by unfold gate; split_ifs <;> norm_num)

/-- **The chain on configurations.** On a finite set of configurations whose
maps are nonnegative, with nonnegative geometric factors, the generator of the
weighted coalgebra is a rate matrix, and its exponential is a stochastic
matrix at every time. -/
theorem configuration_chain (S : Finset (theory.Term × WeightMap K ℝ))
    (geometricNonneg : ∀ context, 0 ≤ A.geometric context)
    (mapsNonneg : ∀ configuration ∈ S, ∀ key, 0 ≤ configuration.2 key) :
    IsRateMatrix (generator (A.restricted funded S)) ∧
      ∀ t, 0 ≤ t → IsStochastic (markov (generator (A.restricted funded S)) t) := by
  have rates : IsRateMatrix (generator (A.restricted funded S)) :=
    generator_isRateMatrix fun c c' _ =>
      A.coalgebra_nonneg funded geometricNonneg c.val c'.val (mapsNonneg c.val c.property)
  exact ⟨rates, fun _ nonnegTime => markov_isStochastic rates nonnegTime⟩

/-- **Closed under successors, the exit rate is the total propensity less the
self-loops.** -/
theorem generator_diag_of_closed (S : Finset (theory.Term × WeightMap K ℝ))
    (closed : ∀ configuration ∈ S, ∀ redex : P.Enabled configuration.1,
      A.successor configuration.2 redex ∈ S)
    (c : S) :
    generator (A.restricted funded S) c c =
      -(A.totalPropensity funded c.val.2 c.val.1 - A.restricted funded S c c) := by
  rw [generator_diag_eq]
  congr 2
  rw [totalRate, ← A.coalgebra_sum funded c.val]
  unfold restricted
  rw [Finset.sum_coe_sort S (fun configuration => A.coalgebra funded c.val configuration)]
  refine (Finset.sum_subset ?_ ?_).symm
  · intro configuration member
    obtain ⟨redex, -, rfl⟩ := Finset.mem_image.mp member
    exact closed c.val c.property redex
  · intro configuration _ notReached
    refine Finset.sum_eq_zero fun redex inFilter => absurd ?_ notReached
    rw [← (Finset.mem_filter.mp inFilter).2]
    exact Finset.mem_image_of_mem _ (Finset.mem_univ redex)

end Augmented

end Chain

end Mettapedia.GSLT.Weighting
