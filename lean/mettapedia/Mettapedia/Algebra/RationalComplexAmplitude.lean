import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic

/-!
# Exact rational complex amplitudes

Executable amplitudes are Mathlib's quadratic algebra over the rationals
with the relation `i² = -1`. Pair arithmetic is proved to agree with that
algebra, and its interpretation into the complex numbers is injective.

Squared norm is a nonnegative, multiplicative readout. It is not additive:
alternative amplitudes may interfere. Consequently normalization and support
must be declared observations, rather than silent changes of coefficient
algebra.
-/

set_option autoImplicit false

namespace Mettapedia.Algebra.RationalComplexAmplitude

open scoped QuadraticAlgebra

abbrev Amplitude := QuadraticAlgebra ℚ (-1) 0

def pairAdd (left right : ℚ × ℚ) : ℚ × ℚ :=
  (left.1 + right.1, left.2 + right.2)

def pairMultiply (left right : ℚ × ℚ) : ℚ × ℚ :=
  (left.1 * right.1 - left.2 * right.2,
    left.1 * right.2 + left.2 * right.1)

def fromPair (pair : ℚ × ℚ) : Amplitude := ⟨pair.1, pair.2⟩
def toPair (value : Amplitude) : ℚ × ℚ := (value.re, value.im)

theorem pair_add_agrees (left right : ℚ × ℚ) :
    fromPair (pairAdd left right) = fromPair left + fromPair right := rfl

theorem pair_multiply_agrees (left right : ℚ × ℚ) :
    fromPair (pairMultiply left right) = fromPair left * fromPair right := by
  ext <;> simp [fromPair, pairMultiply, sub_eq_add_neg]

@[simp] theorem fromPair_toPair (value : Amplitude) : fromPair (toPair value) = value := rfl
@[simp] theorem toPair_fromPair (pair : ℚ × ℚ) : toPair (fromPair pair) = pair := rfl

noncomputable def intoComplex : Amplitude →ₐ[ℚ] ℂ :=
  QuadraticAlgebra.lift ⟨Complex.I, by simp [Algebra.smul_def]⟩

theorem intoComplex_re (value : Amplitude) : (intoComplex value).re = (value.re : ℝ) := by
  simp [intoComplex, QuadraticAlgebra.lift, Algebra.smul_def]

theorem intoComplex_im (value : Amplitude) : (intoComplex value).im = (value.im : ℝ) := by
  simp [intoComplex, QuadraticAlgebra.lift, Algebra.smul_def]

theorem intoComplex_injective : Function.Injective intoComplex := by
  intro left right equality
  ext
  · have reals := congrArg Complex.re equality
    rw [intoComplex_re, intoComplex_re] at reals
    exact_mod_cast reals
  · have imaginaries := congrArg Complex.im equality
    rw [intoComplex_im, intoComplex_im] at imaginaries
    exact_mod_cast imaginaries

/-- The exact Born readout, supplied by the standard quadratic norm. -/
def born : Amplitude →* ℚ := QuadraticAlgebra.norm

theorem born_formula (value : Amplitude) :
    born value = value.re * value.re + value.im * value.im := by
  simp [born, QuadraticAlgebra.norm_def]

theorem born_nonnegative (value : Amplitude) : 0 ≤ born value := by
  rw [born_formula]
  exact add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)

theorem born_zero_iff (value : Amplitude) : born value = 0 ↔ value = 0 := by
  constructor
  · intro zero
    rw [born_formula] at zero
    have realZero : value.re = 0 := by nlinarith [sq_nonneg value.im]
    have imaginaryZero : value.im = 0 := by nlinarith [sq_nonneg value.re]
    ext
    · exact realZero
    · exact imaginaryZero
  · rintro rfl
    exact QuadraticAlgebra.norm_zero

theorem born_agrees_complex (value : Amplitude) :
    (born value : ℝ) = Complex.normSq (intoComplex value) := by
  rw [born_formula, Complex.normSq_apply, intoComplex_re, intoComplex_im]
  norm_cast

theorem conjugation_agrees (value : Amplitude) :
    toPair (star value) = (value.re, -value.im) := by
  simp [toPair]

theorem imaginary_square : fromPair (0, 1) * fromPair (0, 1) = (-1 : Amplitude) := by
  ext <;> norm_num [fromPair, Amplitude]

theorem interference_cancels : (1 : Amplitude) + (-1) = 0 := add_neg_cancel _

theorem born_not_additive :
    born ((1 : Amplitude) + (-1)) ≠ born 1 + born (-1) := by
  norm_num [born, QuadraticAlgebra.norm_def, Amplitude]

theorem exact_mixed_product :
    pairMultiply (2, 3) (5, 7) = (-11, 29) := by norm_num [pairMultiply]


/-- The norm of a finite, already aggregated readout. Labels may retain both
answer identity and provenance; occurrences are not deduplicated. -/
def bornTotal {Label : Type*} (entries : List (Label × Amplitude)) : ℚ :=
  (entries.map (fun entry => born entry.2)).sum

/-- Normalization is a partial observation of amplitudes. A zero total norm
has no probability readout. Every supplied label and occurrence is retained. -/
def normalizeBorn {Label : Type*} (entries : List (Label × Amplitude)) :
    Option (List (Label × ℚ)) :=
  if bornTotal entries = 0 then none
  else some (entries.map (fun entry => (entry.1, born entry.2 / bornTotal entries)))

theorem bornTotal_nonnegative {Label : Type*} (entries : List (Label × Amplitude)) :
    0 ≤ bornTotal entries := by
  induction entries with
  | nil => simp [bornTotal]
  | cons entry entries ih =>
    simpa [bornTotal] using add_nonneg (born_nonnegative entry.2) ih

theorem bornTotal_zero_iff {Label : Type*} (entries : List (Label × Amplitude)) :
    bornTotal entries = 0 ↔ ∀ entry ∈ entries, entry.2 = 0 := by
  induction entries with
  | nil => simp [bornTotal]
  | cons entry entries ih =>
    have nonnegativeHead := born_nonnegative entry.2
    have nonnegativeTail := bornTotal_nonnegative entries
    have totalCons : bornTotal (entry :: entries) = born entry.2 + bornTotal entries := by
      simp [bornTotal]
    constructor
    · intro zero item membership
      rw [totalCons] at zero
      have headZero : born entry.2 = 0 := by linarith
      have tailZero : bornTotal entries = 0 := by linarith
      rcases List.mem_cons.mp membership with same | later
      · subst item
        exact (born_zero_iff entry.2).mp headZero
      · exact ih.mp tailZero item later
    · intro allZero
      have headZero := (born_zero_iff entry.2).mpr (allZero entry (by simp))
      have tailZero := ih.mpr (fun item membership => allZero item (by simp [membership]))
      rw [totalCons, headZero, tailZero, add_zero]

theorem normalizeBorn_none_iff {Label : Type*} (entries : List (Label × Amplitude)) :
    normalizeBorn entries = none ↔ bornTotal entries = 0 := by
  by_cases zero : bornTotal entries = 0 <;> simp [normalizeBorn, zero]

theorem normalizeBorn_eq_some_iff {Label : Type*}
    (entries : List (Label × Amplitude)) (probabilities : List (Label × ℚ)) :
    normalizeBorn entries = some probabilities ↔
      bornTotal entries ≠ 0 ∧
        probabilities = entries.map (fun entry => (entry.1, born entry.2 / bornTotal entries)) := by
  by_cases zero : bornTotal entries = 0
  · simp [normalizeBorn, zero]
  · simp [normalizeBorn, zero, eq_comm]

theorem normalizeBorn_preserves_labels {Label : Type*}
    (entries : List (Label × Amplitude)) (probabilities : List (Label × ℚ))
    (accepted : normalizeBorn entries = some probabilities) :
    probabilities.map Prod.fst = entries.map Prod.fst := by
  rw [(normalizeBorn_eq_some_iff entries probabilities).mp accepted |>.2]
  simp [List.map_map]

theorem normalizeBorn_preserves_occurrences {Label : Type*}
    (entries : List (Label × Amplitude)) (probabilities : List (Label × ℚ))
    (accepted : normalizeBorn entries = some probabilities) :
    probabilities.length = entries.length := by
  rw [(normalizeBorn_eq_some_iff entries probabilities).mp accepted |>.2]
  simp

theorem normalizeBorn_nonnegative {Label : Type*}
    (entries : List (Label × Amplitude)) (probabilities : List (Label × ℚ))
    (accepted : normalizeBorn entries = some probabilities)
    (entry : Label × ℚ) (membership : entry ∈ probabilities) : 0 ≤ entry.2 := by
  rw [(normalizeBorn_eq_some_iff entries probabilities).mp accepted |>.2] at membership
  obtain ⟨source, _, rfl⟩ := List.mem_map.mp membership
  exact div_nonneg (born_nonnegative source.2) (bornTotal_nonnegative entries)

theorem normalizeBorn_sum_one {Label : Type*}
    (entries : List (Label × Amplitude)) (probabilities : List (Label × ℚ))
    (accepted : normalizeBorn entries = some probabilities) :
    (probabilities.map Prod.snd).sum = 1 := by
  have admitted := (normalizeBorn_eq_some_iff entries probabilities).mp accepted
  rw [admitted.2]
  simp only [List.map_map, Function.comp_def]
  change (entries.map (fun entry => born entry.2 / bornTotal entries)).sum = 1
  simp only [div_eq_mul_inv]
  rw [List.sum_map_mul_right]
  exact mul_inv_cancel₀ admitted.1

/-- Two distinct evidence labels keep their own probabilities, even when their
answer label agrees. The finite observation has total probability one. -/
theorem normalized_provenance_control :
    normalizeBorn [((0, 7), fromPair (3, 4)), ((0, 8), fromPair (0, 1))] =
      some [((0, 7), (25 / 26 : ℚ)), ((0, 8), (1 / 26 : ℚ))] := by
  norm_num [normalizeBorn, bornTotal, born, QuadraticAlgebra.norm_def, fromPair, Amplitude]

/-- Equal labels do not collapse supplied occurrences during normalization. -/
theorem normalized_duplicate_occurrences_control :
    normalizeBorn [(0, (1 : Amplitude)), (0, 1)] =
      some [(0, (1 / 2 : ℚ)), (0, (1 / 2 : ℚ))] := by
  norm_num [normalizeBorn, bornTotal, born, QuadraticAlgebra.norm_def, Amplitude]

/-- Interference is resolved before readout: an amplitude cancelled by its
alternative has zero norm and cannot be normalized. -/
theorem cancelled_readout_refused :
    normalizeBorn [(0, (1 : Amplitude) + (-1))] = none := by
  norm_num [normalizeBorn, bornTotal, born, QuadraticAlgebra.norm_def, Amplitude]

end Mettapedia.Algebra.RationalComplexAmplitude
