import Mettapedia.GSLT.Logic.GradedSupport
import Mettapedia.Algebra.TropicalAffineSummary
import Mettapedia.Algorithms.OrdinalPriority
import Mettapedia.Algebra.RationalComplexAmplitude
import Mettapedia.PLN.Evidence.BinEvNat

/-!
# Witnesses separating readings of a weight

Each theorem gives two readings of a weight different verdicts on one observer, for the readings
as the option graph defines them: the OR/AND algebra, natural numbers and nonnegative rationals,
min-plus costs with an actual infinity, checked ordinal priorities, objective vectors and
matrices, exact rational complex amplitudes, and PLN evidence counts.

* **Idempotence.** OR is idempotent, addition of naturals and of nonnegative rationals is not;
  AND is idempotent, sequencing of min-plus costs is not.
* **Size.** The OR/AND algebra has two values; checked ordinal priorities are infinitely many,
  since none is greatest.
* **Well-foundedness.** Nonnegative rationals descend forever; checked priorities do not.
* **A greatest value.** Min-plus has its infinity above every cost; every checked priority has a
  larger one.
* **Cancellation.** In min-plus an alternative is infinite only when both sides are; evidence
  counts add to zero only when both are zero. Opposite amplitudes cancel.
* **Zero divisors.** A product of nonzero amplitudes is nonzero.

The theorems on the OR/AND algebra and on natural numbers use no axioms, those on min-plus costs
propositional extensionality only, and the one on evidence counts no choice. The others take
choice from the results they rest on: the instances of the nonnegative rationals and positive
naturals, the comparison semantics and well-foundedness of ordinal notations, and the complex
numbers.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Distinction.FrontierWitnesses.Weights

open Mettapedia.GSLT.GradedSupport
open Mettapedia.Algebra.TropicalCoefficient
open Mettapedia.Algorithms.OrdinalPriority
open Mettapedia.Algebra.RationalComplexAmplitude
open Mettapedia.PLN.Evidence

/-! ## Idempotence -/

/-- **OR is idempotent.** -/
theorem orBool_add_self (a : OrBool) : a + a = a :=
  OrBool.ext' (Bool.or_self a.val)

/-- **AND is idempotent.** -/
theorem orBool_mul_self (a : OrBool) : a * a = a :=
  OrBool.ext' (Bool.and_self a.val)

/-- **Adding natural counts is not idempotent.** -/
theorem nat_add_not_idempotent : (1 : ℕ) + 1 ≠ 1 := by decide

/-- **Adding nonnegative rational weights is not idempotent.** -/
theorem nonnegativeRat_add_not_idempotent : (1 : ℚ≥0) + 1 ≠ 1 :=
  fun same => one_ne_zero (add_eq_left.mp same)

/-- **Sequencing min-plus costs is not idempotent**: the cost 1 twice is the cost 2. -/
theorem minPlus_sequential_not_idempotent :
    sequential (Value.finite (1 : ℕ)) (Value.finite 1) = Value.finite 2 ∧
      sequential (Value.finite (1 : ℕ)) (Value.finite 1) ≠ Value.finite 1 := by
  decide

/-! ## Size -/

/-- **The OR/AND algebra has two values.** -/
theorem orBool_two_values (a : OrBool) : a = 0 ∨ a = 1 := by
  rcases a with ⟨_ | _⟩
  · exact Or.inl rfl
  · exact Or.inr rfl

/-! ## Well-foundedness -/

/-- **Nonnegative rationals descend forever**: `1 / (n + 1)` strictly decreases. -/
theorem nonnegativeRat_descends : ∀ n : ℕ, (1 : ℚ≥0) / (n + 2) < 1 / (n + 1) := by
  intro n
  apply NNRat.coe_lt_coe.mp
  push_cast
  apply one_div_lt_one_div_of_lt
  · positivity
  · linarith

/-- **Checked ordinal priorities do not descend forever.** -/
theorem priorities_no_infinite_descent :
    ¬ ∃ chain : ℕ → NONote, ∀ n, chain (n + 1) < chain n := by
  rintro ⟨chain, descends⟩
  obtain ⟨_, ⟨k, rfl⟩, minimal⟩ := NONote.lt_wf.has_min (Set.range chain) ⟨chain 0, 0, rfl⟩
  exact minimal (chain (k + 1)) ⟨k + 1, rfl⟩ (descends k)

/-! ## A greatest value -/

/-- **Min-plus has a greatest value**: the alternative of any cost with infinity is the cost. -/
theorem minPlus_infinity_greatest {G : Type} [LinearOrder G] (value : Value G) :
    alternative value Value.infinity = value :=
  (alternative_infinity value).2

/-- Raise the leading coefficient of a list of terms, or start from one. -/
def bump : CantorTerms → CantorTerms
  | [] => [(0, 1)]
  | (exponent, coefficient) :: rest => (exponent, coefficient + 1) :: rest

theorem bump_descending {terms : CantorTerms} (descending : Descending terms) :
    Descending (bump terms) := by
  match terms, descending with
  | [], _ => trivial
  | [_], _ => trivial
  | (_, _) :: (_, _) :: _, descending => exact descending

theorem compare_bump (terms : CantorTerms) : compare (bump terms) terms = .gt := by
  match terms with
  | [] => rfl
  | (exponent, coefficient) :: rest =>
    have larger : _root_.cmp ((coefficient + 1 : ℕ+) : ℕ) (coefficient : ℕ) = .gt := by
      rw [cmp_eq_gt_iff]
      simp
    show (_root_.cmp exponent exponent).then ((_root_.cmp ((coefficient + 1 : ℕ+) : ℕ)
      (coefficient : ℕ)).then (Mettapedia.Algorithms.OrdinalPriority.compare rest rest)) = .gt
    rw [cmp_self_eq_eq, larger]
    rfl

/-- **No checked priority is greatest**: every checked priority has a strictly larger one. -/
theorem checked_priority_not_greatest {terms : CantorTerms} {priority : NONote}
    (checked : check terms = some priority) :
    ∃ terms' larger, check terms' = some larger ∧ priority.repr < larger.repr := by
  have descending : Descending terms := by
    by_contra not_descending
    rw [← check_eq_none_iff] at not_descending
    rw [not_descending] at checked
    cases checked
  have bumped : Descending (bump terms) := bump_descending descending
  obtain ⟨larger, checkedLarger⟩ : ∃ larger, check (bump terms) = some larger :=
    ⟨_, by unfold check; exact dif_pos bumped⟩
  refine ⟨bump terms, larger, checkedLarger, ?_⟩
  have compared := comparison_semantics checkedLarger checked
  rw [compare_bump] at compared
  exact compared

/-- **Checked priorities are infinitely many**: there is one, and none is greatest. -/
theorem checked_priorities_infinite :
    {priority : NONote | ∃ terms, check terms = some priority}.Infinite := by
  intro finite
  obtain ⟨greatest, ⟨terms, checked⟩, above⟩ := Set.exists_max_image _ NONote.repr finite
    ⟨_, [], by unfold check; exact dif_pos trivial⟩
  obtain ⟨terms', larger, checkedLarger, lt⟩ := checked_priority_not_greatest checked
  exact absurd (above larger ⟨terms', checkedLarger⟩) (not_le.mpr lt)

/-! ## Cancellation -/

/-- **An alternative of min-plus costs is infinite only when both are.** -/
theorem minPlus_alternative_eq_infinity_iff {G : Type} [LinearOrder G] (left right : Value G) :
    alternative left right = Value.infinity ↔ left = Value.infinity ∧ right = Value.infinity := by
  cases left <;> cases right <;> simp [alternative]

/-- **Evidence counts add to zero only when both are zero.** -/
theorem evidence_add_eq_zero {left right : BinEvNat} (sum : left + right = 0) :
    left = 0 ∧ right = 0 := by
  have positive := congrArg BinEvNat.pos sum
  have negative := congrArg BinEvNat.neg sum
  change left.pos + right.pos = 0 at positive
  change left.neg + right.neg = 0 at negative
  constructor
  · exact BinEvNat.ext (by change left.pos = 0; omega) (by change left.neg = 0; omega)
  · exact BinEvNat.ext (by change right.pos = 0; omega) (by change right.neg = 0; omega)

/-! ## Zero divisors -/

/-- **A product of nonzero amplitudes is nonzero**: amplitudes embed in the complex numbers. -/
theorem amplitude_mul_eq_zero {left right : Amplitude} (product : left * right = 0) :
    left = 0 ∨ right = 0 := by
  have image := congrArg intoComplex product
  rw [map_mul, map_zero] at image
  rcases mul_eq_zero.mp image with zero | zero
  · exact Or.inl (intoComplex_injective (zero.trans (map_zero intoComplex).symm))
  · exact Or.inr (intoComplex_injective (zero.trans (map_zero intoComplex).symm))

end Mettapedia.GSLT.Distinction.FrontierWitnesses.Weights
