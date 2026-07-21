import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.PrimeCounting
import Mettapedia.Sequences.OEIS.Elementary49
import Mettapedia.Sequences.OEIS.OrderedPredicate
import Mettapedia.Sequences.OEIS.QuadraticFormSeven

/-!
# Predicate-defined OEIS specifications

These specifications enumerate mathematical predicates in increasing order.
They are independent of candidate programs.  `OrderedPredicate.spec` makes the
domain explicit when it is not yet known whether a predicate has infinitely
many witnesses.
-/

namespace Mettapedia.Sequences.OEIS.PredicateDefined

open Mettapedia.Sequences.OEIS.Elementary49
open Mettapedia.Sequences.OEIS.OrderedPredicate

/-- The one-based `k`-th prime.  Sequence predicates below separately require
`0 < k`, so the truncated predecessor is never used at zero. -/
noncomputable def oneBasedPrime (k : Nat) : Nat :=
  Nat.nth Nat.Prime (k - 1)

theorem oneBasedPrime_prime {k : Nat} (_positive : 0 < k) :
    Nat.Prime (oneBasedPrime k) := by
  simp only [oneBasedPrime, Nat.prime_nth_prime]

namespace A260981

def source : EntrySource :=
  sourceOf "A260981"
    "a4f87dc70bfdac7717317863258fd51f4e66e9700f9a0adada798f66f292d996" 1

/-- Sum of the first `k` primes, with `k` one-based in the source entry. -/
noncomputable def sumFirstPrimes (k : Nat) : Nat :=
  ∑ index ∈ Finset.range k, Nat.nth Nat.Prime index

/-- The prime whose one-based index is itself the `k`-th prime. -/
noncomputable def nestedPrime (k : Nat) : Nat :=
  oneBasedPrime (oneBasedPrime k)

/-- A value occurs when it is `prime(prime(k))` for a positive `k` and also
equals the sum of the first `k` primes.  No finiteness assertion is built into
the predicate. -/
noncomputable def Qualifies (value : Nat) : Prop :=
  ∃ k : Nat, 0 < k ∧ sumFirstPrimes k = nestedPrime k ∧
    value = nestedPrime k

noncomputable def spec : SequenceSpec :=
  OrderedPredicate.spec 1 Qualifies

noncomputable def formalization : Formalization :=
  formalizationOf source spec

theorem five_qualifies : Qualifies 5 := by
  refine ⟨2, by norm_num, ?_, ?_⟩
  · norm_num [sumFirstPrimes, Finset.sum_range_succ, nestedPrime, oneBasedPrime,
      Nat.nth_prime_zero_eq_two, Nat.nth_prime_one_eq_three,
      Nat.nth_prime_two_eq_five]
  · norm_num [nestedPrime, oneBasedPrime, Nat.nth_prime_one_eq_three,
      Nat.nth_prime_two_eq_five]

end A260981

namespace A100605

def source : EntrySource :=
  sourceOf "A100605"
    "1b9d877ca42c2c6c8efb2bf811ebc8aaa990d2dca3a2f0bd2f3e5bbf404f2479" 1

/-- A positive prime index `k` qualifies when `(prime(k)-1)! + prime(k)^2`
is prime. -/
noncomputable def Qualifies (k : Nat) : Prop :=
  0 < k ∧ Nat.Prime ((oneBasedPrime k - 1).factorial + oneBasedPrime k ^ 2)

noncomputable def spec : SequenceSpec :=
  OrderedPredicate.spec 1 Qualifies

noncomputable def formalization : Formalization :=
  formalizationOf source spec

theorem first_index_qualifies : Qualifies 1 := by
  refine ⟨by norm_num, ?_⟩
  simpa [oneBasedPrime, Nat.nth_prime_zero_eq_two] using Nat.prime_five

end A100605

namespace A216517

open Mettapedia.Sequences.OEIS.QuadraticFormSeven

def source : EntrySource :=
  sourceOf "A216517"
    "d2ecc6545ed8b8d8f3f73a2e1799bc2ed06ab609c93aa29ab95b631a88c1aff6" 1

/-- The exponent `n` is positive and even, and its Mersenne number is
represented by the binary quadratic form `a^2 + 7*b^2`. -/
def Qualifies (n : Nat) : Prop :=
  0 < n ∧ Even n ∧ ∃ a b : Nat, 2 ^ n - 1 = a ^ 2 + 7 * b ^ 2

noncomputable def spec : SequenceSpec :=
  OrderedPredicate.spec 1 Qualifies

noncomputable def formalization : Formalization :=
  formalizationOf source spec

/-- The first published exponent has the elementary certificate
`2^6 - 1 = 0^2 + 7*3^2`. -/
theorem six_qualifies : Qualifies 6 := by
  refine ⟨by norm_num, ⟨3, by norm_num⟩, 0, 3, by norm_num⟩

theorem one_does_not_qualify : ¬ Qualifies 1 := by
  simp [Qualifies]

/-- The source's four published exponents belong to an infinite certified
subfamily: `6 * 7^r`. -/
theorem six_mul_seven_pow_qualifies (r : Nat) : Qualifies (6 * 7 ^ r) := by
  refine ⟨by positivity, ?_, ?_⟩
  · refine ⟨3 * 7 ^ r, by ring⟩
  · simpa [QuadraticFormSeven.Represents, QuadraticFormSeven.mersenne] using
      QuadraticFormSeven.mersenne_six_mul_seven_pow_represents r

theorem qualifies_infinite : {value : Nat | Qualifies value}.Infinite := by
  have injective : Function.Injective (fun r : Nat => 6 * 7 ^ r) := by
    intro first second equality
    have powersEqual : 7 ^ first = 7 ^ second :=
      Nat.eq_of_mul_eq_mul_left (by norm_num) equality
    exact (pow_right_strictMono₀ (by norm_num : 1 < (7 : Nat))).injective powersEqual
  exact (Set.infinite_range_of_injective injective).mono <| by
    rintro value ⟨r, rfl⟩
    exact six_mul_seven_pow_qualifies r

/-- Consequently the mathematical specification has a value at every finite
enumeration position, without assuming that the displayed subfamily exhausts
the sequence. -/
theorem spec_domain_all (position : Nat) :
    spec.Domain (spec.index position) := by
  exact OrderedPredicate.domain_all_of_infinite 1 qualifies_infinite position

end A216517

namespace A085621

def source : EntrySource :=
  sourceOf "A085621"
    "c20383880ab15955fc2b9adc3d9d6ae03dc6b1e941e9151b9b08e8b2a9fb359a" 1

/-- Pinned auxiliary source for the prime indices whose mean gap is integral. -/
def sourceA049036 : EntrySource :=
  sourceOf "A049036"
    "7cc484d6fb703a92155793655e01fbf5b7bb382e2d74d21069de56b27bcf9057" 1

/-- Pinned auxiliary source for the associated integral mean-gap values. -/
def sourceA049066 : EntrySource :=
  sourceOf "A049066"
    "f48689bded02da2f1d2b9d4eb9095a5dae59e8b646b0963670a5a0c6463962ad" 1

/-- `k` is an index at which the mean number of integers between successive
primes is integral. -/
noncomputable def IsIntegralMeanGapIndex (k : Nat) : Prop :=
  2 ≤ k ∧ (k - 1) ∣ (oneBasedPrime k - 2)

/-- The integral mean number of integers between successive primes up through
the `k`-th prime.  The subtraction by one distinguishes A049066's values from
the mean endpoint-to-endpoint gap. -/
noncomputable def meanInteriorPrimeGap (k : Nat) : Nat :=
  (oneBasedPrime k - 2) / (k - 1) - 1

noncomputable def OccursAsMeanGap (value : Nat) : Prop :=
  ∃ k : Nat, IsIntegralMeanGapIndex k ∧ meanInteriorPrimeGap k = value

/-- The positive integers missing from the distinct values of A049066. -/
noncomputable def Qualifies (value : Nat) : Prop :=
  0 < value ∧ ¬ OccursAsMeanGap value

noncomputable def spec : SequenceSpec :=
  OrderedPredicate.spec 1 Qualifies

noncomputable def formalization : Formalization :=
  formalizationOf source spec

theorem zero_does_not_qualify : ¬ Qualifies 0 := by
  simp [Qualifies]

end A085621

/-- The four source-locked predicate-defined specifications in this tranche. -/
noncomputable def registry : List (String × SequenceSpec) :=
  [("A260981", A260981.spec), ("A100605", A100605.spec),
   ("A216517", A216517.spec), ("A085621", A085621.spec)]

theorem registry_length : registry.length = 4 := by rfl

#print axioms A100605.first_index_qualifies
#print axioms A260981.five_qualifies
#print axioms A216517.six_qualifies
#print axioms A216517.one_does_not_qualify
#print axioms A216517.six_mul_seven_pow_qualifies
#print axioms A216517.spec_domain_all
#print axioms A085621.zero_does_not_qualify
#print axioms registry_length

end Mettapedia.Sequences.OEIS.PredicateDefined
