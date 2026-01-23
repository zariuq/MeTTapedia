import Mettapedia.ProbabilityTheory.KnuthSkilling.Core.Algebra

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.Additive.Axioms.AnomalousPairs

open Classical
open KSSemigroupBase
open KnuthSkillingAlgebraBase
open KnuthSkillingAlgebra

variable {α : Type*} [KSSemigroupBase α]

/-!
# No Anomalous Pairs (Unified Definition)

This file defines the "no anomalous pairs" condition from the ordered-semigroup literature
in the **identity-free** `iterate_op_pnat` language.

## References

- Alimov, N. G. (1950). "On ordered semigroups." Izv. Akad. Nauk SSSR Ser. Mat. 14, 569–576.
- Fuchs, L. (1963). "Partially Ordered Algebraic Systems." Pergamon Press.
- Binder, D. (2016). "Non-Anomalous Semigroups and Real Numbers." arXiv:1607.05997
- **Luap, E.** (2024). "OrderedSemigroups: Formalization of Ordered Semigroups in Lean 4."
  github.com/ericluap/OrderedSemigroups

We follow **Eric Luap's approach** from OrderedSemigroups, using a **unified definition**
that handles both positive and negative elements symmetrically:

*An anomalous pair `(a, b)` has iterates that stay "squeezed" in one of two ways:*
- *Positive squeeze: `a^n < b^n < a^(n+1)` for all n (when a, b > ident)*
- *Negative squeeze: `a^n > b^n > a^(n+1)` for all n (when a, b < ident)*

## Note on the K&S Setting

**Knuth & Skilling work exclusively with R⁺ (positive reals / log-probabilities).**

In their framework, `ident` represents the certain event (probability 1), and all elements
represent "sub-events" with probability ≤ 1. In the additive (log-probability) representation,
this means `ident` is the minimum element: `∀ a, ident ≤ a`.

This naturally rules out "negative elements" (a < ident), making the negative anomalous pair
case vacuous. The `IdentIsMinimum` typeclass captures this assumption, and
`noAnomalousPairs_of_KSSeparation_with_IdentMin` provides the complete proof under this
natural assumption.

**Credit**: The unified approach and negative element handling follows Eric Luap's
OrderedSemigroups formalization, which elegantly avoids the need for separate
NoNegAnomalousPairs classes.
-/

/-- **Unified anomalous pair definition** (following Eric Luap's OrderedSemigroups).

`a` and `b` form an anomalous pair if for every `n : ℕ+`, the iterates stay squeezed in one
of two symmetric ways:
- Positive case: `a^n < b^n < a^(n+1)` (when ident < a < b)
- Negative case: `a^n > b^n > a^(n+1)` (when b < a < ident)

This unified definition avoids the need for separate positive/negative pair classes.
-/
def AnomalousPair (a b : α) : Prop :=
  ∀ n : ℕ+,
    (iterate_op_pnat a n < iterate_op_pnat b n ∧ iterate_op_pnat b n < iterate_op_pnat a (n + 1)) ∨
    (iterate_op_pnat a n > iterate_op_pnat b n ∧ iterate_op_pnat b n > iterate_op_pnat a (n + 1))

/-- **No anomalous pairs**: no pair of elements forms an anomalous pair. -/
class NoAnomalousPairs (α : Type*) [KSSemigroupBase α] : Prop where
  not_anomalous : ∀ a b : α, ¬ AnomalousPair a b

/-! ### Identity-based convenience layer -/

section WithIdentity

variable {α : Type*} [KnuthSkillingAlgebraBase α]

/-- **IdentIsMinimum**: the identity element is the minimum of the order.

In probability theory, `ident` represents the certain event, and all elements
are "sub-events" with `a ≤ ident`. This rules out negative elements (a < ident),
making negative anomalous pairs impossible. -/
class IdentIsMinimum (α : Type*) [KnuthSkillingAlgebraBase α] : Prop where
  ident_le : ∀ a : α, ident ≤ a

namespace KSSeparation

variable [KSSeparation α]

/-- `KSSeparation` + `IdentIsMinimum` implies `NoAnomalousPairs` (complete proof).

When `ident` is the minimum element (natural for probability theory where ident represents
the certain event), there are no negative elements, so only the positive case needs to
be handled, which is done by KSSeparation. -/
theorem noAnomalousPairs_of_KSSeparation_with_IdentMin [IdentIsMinimum α] : NoAnomalousPairs α := by
  constructor
  intro a b hAnom
  rcases hAnom 1 with ⟨ha1_lt, hb1_lt⟩ | ⟨ha1_gt, hb1_gt⟩

  · -- Positive case: a¹ < b¹ < a²
    have hab : a < b := by
      simpa [iterate_op_pnat_one] using ha1_lt
    have h_a2 : iterate_op_pnat a (1 + 1) = op a a := by
      simpa [iterate_op_pnat_one] using (iterate_op_pnat_succ a 1)
    have hb1_lt' : b < op a a := by
      simpa [iterate_op_pnat_one, h_a2] using hb1_lt

    have ha_pos : ident < a := by
      by_contra h_not
      push_neg at h_not
      rcases h_not.lt_or_eq with ha_neg | ha_eq
      · have : op a a < a := by
          calc op a a < op a ident := op_strictMono_right a ha_neg
            _ = a := op_ident_right a
        exact absurd (lt_trans hab (lt_trans hb1_lt' this)) (lt_irrefl a)
      · rw [ha_eq, op_ident_left] at hb1_lt'
        rw [ha_eq] at hab
        exact absurd (lt_trans hab hb1_lt') (lt_irrefl ident)

    have hb_pos : ident < b := lt_trans ha_pos hab

    -- Use identity-free separation via KSSeparationSemigroup
    haveI : KSSeparationSemigroup α := inferInstance
    have ha_pos' : IsPositive a := (isPositive_iff_ident_lt a).mpr ha_pos
    have hb_pos' : IsPositive b := (isPositive_iff_ident_lt b).mpr hb_pos
    rcases KSSeparationSemigroup.sep (a := a) (x := a) (y := b) ha_pos' ha_pos' hb_pos' hab with
      ⟨n, m, hlt, hle⟩

    have h_am_lt_bm : iterate_op_pnat a m < iterate_op_pnat b m := lt_of_lt_of_le hlt hle

    -- Show m < n (otherwise contradict hlt)
    have hmn : m < n := by
      by_contra h_not
      have hle' : n ≤ m := le_of_not_gt h_not
      have hmono := iterate_op_pnat_mono a ha_pos' hle'
      exact (not_lt_of_ge hmono) hlt

    -- Then a^(m+1) ≤ a^n ≤ b^m
    have h_m_le : m ≤ n - 1 := PNat.le_sub_one_of_lt hmn
    have h1 : 1 < n := PNat.one_lt_of_lt hmn
    have h_m1_le : m + 1 ≤ n := by
      have h' : m + 1 ≤ (n - 1) + 1 := add_le_add_right h_m_le 1
      simpa [PNat.sub_add_of_lt h1] using h'

    have h_a_m1_le : iterate_op_pnat a (m + 1) ≤ iterate_op_pnat a n :=
      iterate_op_pnat_mono a ha_pos' h_m1_le
    have h_a_m1_le_bm : iterate_op_pnat a (m + 1) ≤ iterate_op_pnat b m :=
      le_trans h_a_m1_le hle

    -- Contradiction from anomalous behavior at m
    rcases hAnom m with ⟨_, h_bm_lt⟩ | ⟨h_am_gt_bm, _⟩
    · exact (not_le_of_gt h_bm_lt) h_a_m1_le_bm
    · exact (not_lt_of_ge (le_of_lt h_am_lt_bm)) h_am_gt_bm

  · -- Negative case: impossible under IdentIsMinimum
    have hab : b < a := by
      simpa [iterate_op_pnat_one] using ha1_gt
    have h_a2 : iterate_op_pnat a (1 + 1) = op a a := by
      simpa [iterate_op_pnat_one] using (iterate_op_pnat_succ a 1)
    have hb1_gt' : op a a < b := by
      simpa [iterate_op_pnat_one, h_a2] using hb1_gt

    -- From a > b > a·a, we need a > a·a, which requires a < ident
    -- But IdentIsMinimum says ident ≤ a for all a, so a ≮ ident
    have ha_neg : a < ident := by
      by_contra h_not
      push_neg at h_not
      rcases h_not.lt_or_eq with ha_pos | ha_eq
      · have : a < op a a := by
          calc a = op a ident := (op_ident_right a).symm
            _ < op a a := op_strictMono_right a ha_pos
        exact absurd this (not_lt.mpr (le_of_lt (lt_trans hb1_gt' hab)))
      · rw [← ha_eq, op_ident_left] at hb1_gt'
        rw [← ha_eq] at hab
        exact absurd (lt_trans hb1_gt' hab) (lt_irrefl ident)

    -- But IdentIsMinimum says ident ≤ a, contradicting a < ident
    have h_ident_le := IdentIsMinimum.ident_le a
    exact absurd ha_neg (not_lt.mpr h_ident_le)

end KSSeparation

/-!
## Key Lemmas for Negative Elements

Following Eric Luap's approach, we establish helper lemmas for negative elements.
-/

/-- For x < ident, op z x < z (multiplying on the right by negative decreases).
This is the key lemma for the negative anomalous pair construction. -/
lemma op_right_neg_lt {x z : α} (hx : x < ident) : op z x < z := by
  calc op z x < op z ident := op_strictMono_right z hx
    _ = z := op_ident_right z

/-- For x < ident, op x z < z (multiplying on the left by negative decreases). -/
lemma op_left_neg_lt {x z : α} (hx : x < ident) : op x z < z := by
  calc op x z < op ident z := op_strictMono_left z hx
    _ = z := op_ident_left z

end WithIdentity

end Mettapedia.ProbabilityTheory.KnuthSkilling.Additive.Axioms.AnomalousPairs
