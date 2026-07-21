import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval
import Mathlib.RingTheory.Polynomial.Cyclotomic.Expand
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.NumberTheory.Multiplicity
import Mathlib.Tactic
import Mettapedia.Sequences.OEIS.Basic

/-!
# A divisibility sieve for cyclotomic values

This file separates a general arithmetic sieve from the OEIS specification
whose values are evaluations of cyclotomic polynomials.  The sieve keeps its
previous outputs in reverse chronological order and removes each divisor at
most once from a new candidate.
-/

namespace Mettapedia.Sequences.OEIS.CyclotomicSieve

/-- Divide by `divisor` once when it divides `candidate`. -/
def removeIfDivides (candidate divisor : Nat) : Nat :=
  if candidate % divisor = 0 then candidate / divisor else candidate

theorem removeIfDivides_pos {candidate divisor : Nat}
    (candidatePositive : 0 < candidate) (divisorPositive : 0 < divisor) :
    0 < removeIfDivides candidate divisor := by
  unfold removeIfDivides
  split
  next divides =>
    have divisorDvd : divisor ∣ candidate := Nat.dvd_of_mod_eq_zero divides
    exact Nat.div_pos (Nat.le_of_dvd candidatePositive divisorDvd) divisorPositive
  next => exact candidatePositive

/-- Scan divisors from the head of a reverse-chronological history. -/
def scan : List Nat → Nat → Nat
  | [], candidate => candidate
  | divisor :: divisors, candidate =>
      scan divisors (removeIfDivides candidate divisor)

@[simp] theorem scan_nil (candidate : Nat) : scan [] candidate = candidate := rfl

@[simp] theorem scan_cons (divisor : Nat) (divisors : List Nat) (candidate : Nat) :
    scan (divisor :: divisors) candidate =
      scan divisors (removeIfDivides candidate divisor) := rfl

theorem scan_append (first second : List Nat) (candidate : Nat) :
    scan (first ++ second) candidate = scan second (scan first candidate) := by
  induction first generalizing candidate with
  | nil => rfl
  | cons divisor divisors inductionHypothesis =>
      simp only [List.cons_append, scan_cons]
      exact inductionHypothesis (removeIfDivides candidate divisor)

/-- When the entire divisor product divides the candidate, the conditional
scan performs exact division by that product. -/
theorem scan_eq_div_prod_of_prod_dvd :
    ∀ (divisors : List Nat) (candidate : Nat),
      divisors.prod ∣ candidate →
        scan divisors candidate = candidate / divisors.prod := by
  intro divisors
  induction divisors with
  | nil => simp
  | cons divisor divisors inductionHypothesis =>
      intro candidate productDivides
      change divisor * divisors.prod ∣ candidate at productDivides
      change scan (divisor :: divisors) candidate =
        candidate / (divisor * divisors.prod)
      have divisorDivides : divisor ∣ candidate :=
        dvd_trans (dvd_mul_right divisor divisors.prod) productDivides
      have tailProductDivides : divisors.prod ∣ candidate / divisor := by
        rw [Nat.dvd_div_iff_mul_dvd divisorDivides]
        simpa [mul_comm] using productDivides
      rw [scan_cons, removeIfDivides,
        if_pos (Nat.dvd_iff_mod_eq_zero.mp divisorDivides),
        inductionHypothesis (candidate / divisor) tailProductDivides,
        Nat.div_div_eq_div_mul]

/-- A list whose members do not divide the candidate leaves it unchanged. -/
theorem scan_eq_self_of_forall_not_dvd :
    ∀ (divisors : List Nat) (candidate : Nat),
      (∀ divisor ∈ divisors, ¬divisor ∣ candidate) →
        scan divisors candidate = candidate := by
  intro divisors
  induction divisors with
  | nil => simp
  | cons divisor divisors inductionHypothesis =>
      intro candidate noneDivides
      have headDoesNotDivide : ¬divisor ∣ candidate :=
        noneDivides divisor (by simp)
      have tailDoesNotDivide : ∀ value ∈ divisors, ¬value ∣ candidate := by
        intro value membership
        exact noneDivides value (by simp [membership])
      simp only [scan_cons, removeIfDivides,
        Nat.dvd_iff_mod_eq_zero.not.mp headDoesNotDivide, if_false]
      exact inductionHypothesis candidate tailDoesNotDivide

/-- A general correctness theorem for conditional scans.  If the product of
the selected values divides the candidate, while every unselected value does
not divide it, then scanning every value is equivalent to exact division by
the selected product. -/
theorem scan_map_eq_div_filter_prod
    {α : Type*} [DecidableEq α]
    (items : List α) (value : α → Nat) (selected : α → Prop)
    [DecidablePred selected] (candidate : Nat)
    (selectedProductDivides :
      ((items.filter selected).map value).prod ∣ candidate)
    (unselectedDoesNotDivide :
      ∀ item ∈ items, ¬selected item → ¬value item ∣ candidate) :
    scan (items.map value) candidate =
      candidate / ((items.filter selected).map value).prod := by
  induction items generalizing candidate with
  | nil => simp
  | cons item items inductionHypothesis =>
      by_cases itemSelected : selected item
      · have itemDivides : value item ∣ candidate := by
          exact dvd_trans
            (dvd_mul_right (value item)
              ((items.filter selected).map value).prod)
            (by simpa [itemSelected] using selectedProductDivides)
        have tailProductDivides :
            ((items.filter selected).map value).prod ∣
              candidate / value item := by
          rw [Nat.dvd_div_iff_mul_dvd itemDivides]
          simpa [itemSelected] using selectedProductDivides
        have quotientDivides : candidate / value item ∣ candidate :=
          Nat.div_dvd_of_dvd itemDivides
        have tailUnselectedDoesNotDivide :
            ∀ other ∈ items, ¬selected other →
              ¬value other ∣ candidate / value item := by
          intro other membership otherUnselected otherDivides
          exact unselectedDoesNotDivide other (by simp [membership])
            otherUnselected (dvd_trans otherDivides quotientDivides)
        rw [List.map_cons, scan_cons, removeIfDivides,
          if_pos (Nat.dvd_iff_mod_eq_zero.mp itemDivides),
          inductionHypothesis (candidate / value item)
            tailProductDivides tailUnselectedDoesNotDivide,
          Nat.div_div_eq_div_mul]
        simp [itemSelected]
      · have itemDoesNotDivide : ¬value item ∣ candidate :=
          unselectedDoesNotDivide item (by simp) itemSelected
        have tailUnselectedDoesNotDivide :
            ∀ other ∈ items, ¬selected other → ¬value other ∣ candidate := by
          intro other membership otherUnselected
          exact unselectedDoesNotDivide other (by simp [membership]) otherUnselected
        rw [List.map_cons, scan_cons, removeIfDivides,
          if_neg (Nat.dvd_iff_mod_eq_zero.not.mp itemDoesNotDivide),
          inductionHypothesis candidate]
        · simp [itemSelected]
        · simpa [itemSelected] using selectedProductDivides
        · exact tailUnselectedDoesNotDivide

/-- Order-aware scan correctness with persistent nondivisors.  Unlike
`scan_map_eq_div_filter_prod`, an unselected value need not be known absent
only from the initial candidate: it must be absent from every residual that
divides that candidate.  This is the form supplied naturally by a
divisibility-separating prime. -/
theorem scan_map_eq_div_filter_prod_of_persistent_nondivisors
    {α : Type*} [DecidableEq α]
    (items : List α) (value : α → Nat) (selected : α → Prop)
    [DecidablePred selected] (candidate : Nat)
    (selectedProductDivides :
      ((items.filter selected).map value).prod ∣ candidate)
    (unselectedPersistent :
      ∀ item ∈ items, ¬selected item →
        ∀ residual, residual ∣ candidate → ¬value item ∣ residual) :
    scan (items.map value) candidate =
      candidate / ((items.filter selected).map value).prod := by
  induction items generalizing candidate with
  | nil => simp
  | cons item items inductionHypothesis =>
      by_cases itemSelected : selected item
      · have itemDivides : value item ∣ candidate :=
          dvd_trans
            (dvd_mul_right (value item)
              ((items.filter selected).map value).prod)
            (by simpa [itemSelected] using selectedProductDivides)
        have tailProductDivides :
            ((items.filter selected).map value).prod ∣
              candidate / value item := by
          rw [Nat.dvd_div_iff_mul_dvd itemDivides]
          simpa [itemSelected] using selectedProductDivides
        have quotientDivides : candidate / value item ∣ candidate :=
          Nat.div_dvd_of_dvd itemDivides
        have tailPersistent :
            ∀ other ∈ items, ¬selected other →
              ∀ residual, residual ∣ candidate / value item →
                ¬value other ∣ residual := by
          intro other membership otherUnselected residual residualDivides
          exact unselectedPersistent other (by simp [membership])
            otherUnselected residual
            (dvd_trans residualDivides quotientDivides)
        rw [List.map_cons, scan_cons, removeIfDivides,
          if_pos (Nat.dvd_iff_mod_eq_zero.mp itemDivides),
          inductionHypothesis (candidate / value item)
            tailProductDivides tailPersistent,
          Nat.div_div_eq_div_mul]
        simp [itemSelected]
      · have itemDoesNotDivide : ¬value item ∣ candidate :=
          unselectedPersistent item (by simp) itemSelected candidate
            (dvd_refl candidate)
        have tailPersistent :
            ∀ other ∈ items, ¬selected other →
              ∀ residual, residual ∣ candidate → ¬value other ∣ residual := by
          intro other membership otherUnselected
          exact unselectedPersistent other (by simp [membership])
            otherUnselected
        rw [List.map_cons, scan_cons, removeIfDivides,
          if_neg (Nat.dvd_iff_mod_eq_zero.not.mp itemDoesNotDivide),
          inductionHypothesis candidate]
        · simp [itemSelected]
        · simpa [itemSelected] using selectedProductDivides
        · exact tailPersistent

theorem removeIfDivides_dvd_candidate (candidate divisor : Nat) :
    removeIfDivides candidate divisor ∣ candidate := by
  unfold removeIfDivides
  split
  next divides =>
    exact Nat.div_dvd_of_dvd (Nat.dvd_of_mod_eq_zero divides)
  next => exact dvd_refl candidate

theorem scan_dvd_candidate : ∀ (divisors : List Nat) (candidate : Nat),
    scan divisors candidate ∣ candidate := by
  intro divisors
  induction divisors with
  | nil => exact fun candidate => dvd_refl candidate
  | cons divisor divisors inductionHypothesis =>
      intro candidate
      exact dvd_trans
        (inductionHypothesis (removeIfDivides candidate divisor))
        (removeIfDivides_dvd_candidate candidate divisor)

/-- The scan is intentionally order-sensitive when no global product
divisibility invariant is available. -/
theorem scan_order_sensitive : scan [4, 6] 12 ≠ scan [6, 4] 12 := by
  decide

/-- The positive integer obtained by evaluating the `index`-th cyclotomic
polynomial at two. -/
noncomputable def cyclotomicAtTwo (index : Nat) : Nat :=
  ((Polynomial.cyclotomic index Int).eval 2).natAbs

theorem cyclotomicAtTwo_cast (index : Nat) :
    (cyclotomicAtTwo index : Int) =
      (Polynomial.cyclotomic index Int).eval 2 := by
  unfold cyclotomicAtTwo
  exact Int.natAbs_of_nonneg
    (Polynomial.cyclotomic_pos' index (by norm_num)).le

theorem cyclotomicAtTwo_positive (index : Nat) : 0 < cyclotomicAtTwo index := by
  unfold cyclotomicAtTwo
  exact Int.natAbs_pos.mpr
    (Polynomial.cyclotomic_pos' index (by norm_num)).ne'

@[simp] theorem cyclotomicAtTwo_one : cyclotomicAtTwo 1 = 1 := by
  norm_num [cyclotomicAtTwo, Polynomial.cyclotomic_one]

@[simp] theorem cyclotomicAtTwo_three : cyclotomicAtTwo 3 = 7 := by
  norm_num [cyclotomicAtTwo, Polynomial.cyclotomic_three]

@[simp] theorem cyclotomicAtTwo_four : cyclotomicAtTwo 4 = 5 := by
  unfold cyclotomicAtTwo
  rw [show 4 = 2 ^ (1 + 1) by norm_num,
    Polynomial.cyclotomic_prime_pow_eq_geom_sum Nat.prime_two]
  norm_num

@[simp] theorem cyclotomicAtTwo_five : cyclotomicAtTwo 5 = 31 := by
  unfold cyclotomicAtTwo
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  rw [Polynomial.cyclotomic_prime]
  norm_num

/-- A prime divisor of `Φ_n(2)` makes two a root of the same cyclotomic
polynomial modulo that prime. -/
theorem cyclotomicAtTwo_isRoot {index prime : Nat}
    (primeIsPrime : prime.Prime)
    (primeDivides : prime ∣ cyclotomicAtTwo index) :
    (Polynomial.cyclotomic index (ZMod prime)).IsRoot (2 : ZMod prime) := by
  letI : Fact prime.Prime := ⟨primeIsPrime⟩
  rw [Polynomial.IsRoot]
  calc
    Polynomial.eval (2 : ZMod prime)
        (Polynomial.cyclotomic index (ZMod prime)) =
        Int.castRingHom (ZMod prime)
          ((Polynomial.cyclotomic index Int).eval 2) := by
            simpa using Polynomial.cyclotomic.eval_apply
              (2 : Int) index (Int.castRingHom (ZMod prime))
    _ = 0 := by
      rw [← cyclotomicAtTwo_cast]
      simpa using
        (ZMod.natCast_eq_zero_iff (cyclotomicAtTwo index) prime).2
          primeDivides

/-- If an intrinsic prime `p` divides both `n` and `Φ_n(2)`, removing the
full `p`-power from `n` leaves exactly the multiplicative order of two
modulo `p`. -/
theorem orderOf_two_eq_ordCompl_of_prime_dvd_cyclotomicAtTwo
    {index prime : Nat} (indexPositive : 0 < index)
    (primeIsPrime : prime.Prime)
    (primeDivides : prime ∣ cyclotomicAtTwo index) :
    orderOf (2 : ZMod prime) = ordCompl[prime] index := by
  letI : Fact prime.Prime := ⟨primeIsPrime⟩
  have root := cyclotomicAtTwo_isRoot primeIsPrime primeDivides
  have primeFree : ¬prime ∣ ordCompl[prime] index :=
    Nat.not_dvd_ordCompl primeIsPrime indexPositive.ne'
  letI : NeZero ((ordCompl[prime] index : Nat) : ZMod prime) :=
    NeZero.of_not_dvd (ZMod prime) primeFree
  have decomposition :
      prime ^ index.factorization prime * ordCompl[prime] index = index :=
    Nat.ordProj_mul_ordCompl_eq_self index prime
  rw [← decomposition] at root
  exact
    (Polynomial.isRoot_cyclotomic_prime_pow_mul_iff_of_charP.mp root).eq_orderOf.symm

/-- For an odd prime, divisibility of `Φ_n(2)` is characterized exactly by
the prime-free part of `n`: it must be the multiplicative order of two. -/
theorem prime_dvd_cyclotomicAtTwo_iff_orderOf_eq_ordCompl
    {index prime : Nat} (indexPositive : 0 < index)
    (primeIsPrime : prime.Prime) :
    prime ∣ cyclotomicAtTwo index ↔
      orderOf (2 : ZMod prime) = ordCompl[prime] index := by
  constructor
  · exact orderOf_two_eq_ordCompl_of_prime_dvd_cyclotomicAtTwo
      indexPositive primeIsPrime
  · intro orderEquality
    letI : Fact prime.Prime := ⟨primeIsPrime⟩
    have primeFree : ¬prime ∣ ordCompl[prime] index :=
      Nat.not_dvd_ordCompl primeIsPrime indexPositive.ne'
    letI : NeZero ((ordCompl[prime] index : Nat) : ZMod prime) :=
      NeZero.of_not_dvd (ZMod prime) primeFree
    have primitive : IsPrimitiveRoot (2 : ZMod prime) (ordCompl[prime] index) :=
      IsPrimitiveRoot.iff_orderOf.mpr orderEquality
    have decomposition :
        prime ^ index.factorization prime * ordCompl[prime] index = index :=
      Nat.ordProj_mul_ordCompl_eq_self index prime
    have root :
        (Polynomial.cyclotomic index (ZMod prime)).IsRoot
          (2 : ZMod prime) := by
      rw [← decomposition]
      exact
        Polynomial.isRoot_cyclotomic_prime_pow_mul_iff_of_charP.mpr primitive
    have mappedEvaluation :
        Int.castRingHom (ZMod prime)
          ((Polynomial.cyclotomic index Int).eval 2) = 0 := by
      calc
        Int.castRingHom (ZMod prime)
            ((Polynomial.cyclotomic index Int).eval 2) =
            Polynomial.eval (2 : ZMod prime)
              (Polynomial.cyclotomic index (ZMod prime)) := by
                symm
                simpa using Polynomial.cyclotomic.eval_apply
                  (2 : Int) index (Int.castRingHom (ZMod prime))
        _ = 0 := root
    rw [← cyclotomicAtTwo_cast] at mappedEvaluation
    exact (ZMod.natCast_eq_zero_iff (cyclotomicAtTwo index) prime).mp
      (by simpa using mappedEvaluation)

/-- Once the multiplicative order `m` of two modulo `p` is fixed, the
cyclotomic values divisible by `p` occur exactly at indices `p^k*m`. -/
theorem prime_dvd_cyclotomicAtTwo_iff_eq_prime_pow_mul
    {prime order index : Nat} (primeIsPrime : prime.Prime)
    (primeDoesNotDivideOrder : ¬prime ∣ order)
    (orderEquality : orderOf (2 : ZMod prime) = order)
    (indexPositive : 0 < index) :
    prime ∣ cyclotomicAtTwo index ↔
      ∃ exponent : Nat, index = prime ^ exponent * order := by
  rw [prime_dvd_cyclotomicAtTwo_iff_orderOf_eq_ordCompl
    indexPositive primeIsPrime, orderEquality]
  constructor
  · intro complementEquality
    refine ⟨index.factorization prime, ?_⟩
    calc
      index = prime ^ index.factorization prime * ordCompl[prime] index :=
        (Nat.ordProj_mul_ordCompl_eq_self index prime).symm
      _ = prime ^ index.factorization prime * order := by
        rw [← complementEquality]
  · rintro ⟨exponent, rfl⟩
    exact (Nat.ordCompl_pow_mul_of_not_dvd exponent primeIsPrime
      primeDoesNotDivideOrder).symm

/-- Odd-prime LTE stated directly in terms of natural-number
factorizations of Mersenne numbers. -/
theorem factorization_two_pow_mul_sub_one
    {prime exponent multiplier : Nat}
    (primeIsPrime : prime.Prime) (primeIsOdd : Odd prime)
    (exponentPositive : 0 < exponent) (multiplierPositive : 0 < multiplier)
    (primeDivides : prime ∣ 2 ^ exponent - 1) :
    (2 ^ (exponent * multiplier) - 1).factorization prime =
      (2 ^ exponent - 1).factorization prime +
        multiplier.factorization prime := by
  have primeDoesNotDividePower : ¬prime ∣ 2 ^ exponent := by
    intro divides
    have primeDividesTwo := primeIsPrime.dvd_of_dvd_pow divides
    rcases (Nat.dvd_prime Nat.prime_two).mp primeDividesTwo with
      primeIsOne | primeIsTwo
    · exact primeIsPrime.ne_one primeIsOne
    · subst prime
      norm_num at primeIsOdd
  have lte := Nat.emultiplicity_pow_sub_pow primeIsPrime primeIsOdd
    primeDivides primeDoesNotDividePower multiplier
  rw [one_pow, ← pow_mul] at lte
  have leftNonzero : 2 ^ (exponent * multiplier) - 1 ≠ 0 :=
    (Nat.sub_pos_of_lt
      (one_lt_pow₀ (by omega)
        (mul_pos exponentPositive multiplierPositive).ne')).ne'
  have middleNonzero : 2 ^ exponent - 1 ≠ 0 :=
    (Nat.sub_pos_of_lt
      (one_lt_pow₀ (by omega) exponentPositive.ne')).ne'
  have multiplierNonzero : multiplier ≠ 0 := multiplierPositive.ne'
  have leftFinite :
      FiniteMultiplicity prime (2 ^ (exponent * multiplier) - 1) :=
    Nat.finiteMultiplicity_iff.mpr
      ⟨primeIsPrime.ne_one, Nat.pos_of_ne_zero leftNonzero⟩
  have middleFinite : FiniteMultiplicity prime (2 ^ exponent - 1) :=
    Nat.finiteMultiplicity_iff.mpr
      ⟨primeIsPrime.ne_one, Nat.pos_of_ne_zero middleNonzero⟩
  have multiplierFinite : FiniteMultiplicity prime multiplier :=
    Nat.finiteMultiplicity_iff.mpr
      ⟨primeIsPrime.ne_one, multiplierPositive⟩
  rw [leftFinite.emultiplicity_eq_multiplicity,
    middleFinite.emultiplicity_eq_multiplicity,
    multiplierFinite.emultiplicity_eq_multiplicity] at lte
  norm_cast at lte
  rw [Nat.factorization_def _ primeIsPrime,
    Nat.factorization_def _ primeIsPrime,
    Nat.factorization_def _ primeIsPrime,
    padicValNat_def' primeIsPrime.ne_one leftNonzero,
    padicValNat_def' primeIsPrime.ne_one middleNonzero,
    padicValNat_def' primeIsPrime.ne_one multiplierNonzero]
  exact lte

/-- Two distinct prime factors of a cyclotomic value cannot both be
intrinsic factors of its index. -/
theorem intrinsic_prime_unique {index first second : Nat}
    (firstIsPrime : first.Prime) (secondIsPrime : second.Prime)
    (firstDividesValue : first ∣ cyclotomicAtTwo index)
    (secondDividesValue : second ∣ cyclotomicAtTwo index)
    (firstDividesIndex : first ∣ index)
    (secondDividesIndex : second ∣ index) :
    first = second := by
  by_contra distinct
  have indexNonzero : index ≠ 0 := by
    intro indexZero
    subst index
    have firstDividesOne : first ∣ 1 := by
      simpa [cyclotomicAtTwo] using firstDividesValue
    exact firstIsPrime.not_dvd_one firstDividesOne
  have indexPositive : 0 < index := Nat.pos_of_ne_zero indexNonzero
  have firstNotDvdSecond : ¬first ∣ second := by
    intro divides
    rcases (Nat.dvd_prime secondIsPrime).mp divides with firstIsOne | equal
    · exact firstIsPrime.ne_one firstIsOne
    · exact distinct equal
  have secondNotDvdFirst : ¬second ∣ first := by
    intro divides
    rcases (Nat.dvd_prime firstIsPrime).mp divides with secondIsOne | equal
    · exact secondIsPrime.ne_one secondIsOne
    · exact distinct equal.symm
  have secondDividesComplement : second ∣ ordCompl[first] index :=
    Nat.dvd_ordCompl_of_dvd_not_dvd secondDividesIndex firstNotDvdSecond
  have firstDividesComplement : first ∣ ordCompl[second] index :=
    Nat.dvd_ordCompl_of_dvd_not_dvd firstDividesIndex secondNotDvdFirst
  have firstRoot := cyclotomicAtTwo_isRoot firstIsPrime firstDividesValue
  have secondRoot := cyclotomicAtTwo_isRoot secondIsPrime secondDividesValue
  have firstCoprime : Nat.Coprime 2 first := by
    letI : Fact first.Prime := ⟨firstIsPrime⟩
    exact Polynomial.coprime_of_root_cyclotomic indexPositive firstRoot
  have secondCoprime : Nat.Coprime 2 second := by
    letI : Fact second.Prime := ⟨secondIsPrime⟩
    exact Polynomial.coprime_of_root_cyclotomic indexPositive secondRoot
  have firstOrderDivides : orderOf (2 : ZMod first) ∣ first - 1 := by
    letI : Fact first.Prime := ⟨firstIsPrime⟩
    exact ZMod.orderOf_dvd_card_sub_one
      (mt (CharP.cast_eq_zero_iff (ZMod first) first 2).1
        (firstIsPrime.coprime_iff_not_dvd.mp firstCoprime.symm))
  have secondOrderDivides : orderOf (2 : ZMod second) ∣ second - 1 := by
    letI : Fact second.Prime := ⟨secondIsPrime⟩
    exact ZMod.orderOf_dvd_card_sub_one
      (mt (CharP.cast_eq_zero_iff (ZMod second) second 2).1
        (secondIsPrime.coprime_iff_not_dvd.mp secondCoprime.symm))
  rw [orderOf_two_eq_ordCompl_of_prime_dvd_cyclotomicAtTwo
      indexPositive firstIsPrime firstDividesValue] at firstOrderDivides
  rw [orderOf_two_eq_ordCompl_of_prime_dvd_cyclotomicAtTwo
      indexPositive secondIsPrime secondDividesValue] at secondOrderDivides
  have secondLtFirst : second < first := by
    have complementLe : ordCompl[first] index ≤ first - 1 :=
      Nat.le_of_dvd (Nat.sub_pos_of_lt firstIsPrime.one_lt) firstOrderDivides
    have secondLe : second ≤ ordCompl[first] index :=
      Nat.le_of_dvd (Nat.ordCompl_pos first indexPositive.ne')
        secondDividesComplement
    omega
  have firstLtSecond : first < second := by
    have complementLe : ordCompl[second] index ≤ second - 1 :=
      Nat.le_of_dvd (Nat.sub_pos_of_lt secondIsPrime.one_lt) secondOrderDivides
    have firstLe : first ≤ ordCompl[second] index :=
      Nat.le_of_dvd (Nat.ordCompl_pos second indexPositive.ne')
        firstDividesComplement
    omega
  omega

/-- A prime factor that certifies the index of a value by the exponents of
Mersenne numbers it can divide. -/
structure DivisibilitySeparatingPrime (base index value : Nat) where
  prime : Nat
  primeIsPrime : prime.Prime
  primeDividesValue : prime ∣ value
  indexDividesOfPrimeDivides :
    ∀ exponent, prime ∣ base ^ exponent - 1 → index ∣ exponent

theorem index_dvd_of_value_dvd_pow_sub_one
    {base index value exponent : Nat}
    (witness : DivisibilitySeparatingPrime base index value)
    (valueDivides : value ∣ base ^ exponent - 1) :
    index ∣ exponent := by
  exact witness.indexDividesOfPrimeDivides exponent
    (dvd_trans witness.primeDividesValue valueDivides)

/-- A prime divisor of `Φ_n(2)` that does not divide `n` separates index
`n`: modulo that prime, two has multiplicative order exactly `n`. -/
def separatingPrimeOfPrimeDvdCyclotomicAtTwo
    {index prime : Nat} (primeIsPrime : prime.Prime)
    (primeDivides : prime ∣ cyclotomicAtTwo index)
    (primeDoesNotDivideIndex : ¬prime ∣ index) :
    DivisibilitySeparatingPrime 2 index (cyclotomicAtTwo index) := by
  letI : Fact prime.Prime := ⟨primeIsPrime⟩
  have evaluationIsZero :
      Int.castRingHom (ZMod prime)
          ((Polynomial.cyclotomic index Int).eval 2) = 0 := by
    rw [← cyclotomicAtTwo_cast]
    simpa using
      (ZMod.natCast_eq_zero_iff (cyclotomicAtTwo index) prime).2 primeDivides
  have isRoot :
      (Polynomial.cyclotomic index (ZMod prime)).IsRoot
        (2 : ZMod prime) := by
    rw [Polynomial.IsRoot]
    calc
      Polynomial.eval (2 : ZMod prime)
          (Polynomial.cyclotomic index (ZMod prime)) =
          Int.castRingHom (ZMod prime)
            ((Polynomial.cyclotomic index Int).eval 2) := by
              simpa using Polynomial.cyclotomic.eval_apply
                (2 : Int) index (Int.castRingHom (ZMod prime))
      _ = 0 := evaluationIsZero
  haveI : NeZero (index : ZMod prime) :=
    NeZero.of_not_dvd (ZMod prime) primeDoesNotDivideIndex
  have primitive : IsPrimitiveRoot (2 : ZMod prime) index :=
    Polynomial.isRoot_cyclotomic_iff.mp isRoot
  exact
    { prime := prime
      primeIsPrime := primeIsPrime
      primeDividesValue := primeDivides
      indexDividesOfPrimeDivides := by
        intro exponent dividesPower
        have congruence : 1 ≡ 2 ^ exponent [MOD prime] :=
          (Nat.modEq_iff_dvd'
            (Nat.one_le_pow exponent 2 (by omega))).2 dividesPower
        have castEquality :
            ((2 ^ exponent : Nat) : ZMod prime) =
              ((1 : Nat) : ZMod prime) :=
          (ZMod.natCast_eq_natCast_iff' (2 ^ exponent) 1 prime).2
            congruence.symm
        have powerEquality : (2 : ZMod prime) ^ exponent = 1 := by
          simpa using castEquality
        rw [primitive.eq_orderOf]
        exact orderOf_dvd_of_pow_eq_one powerEquality }

theorem prime_dvd_index_of_no_separatingPrime
    {index prime : Nat}
    (noWitness :
      ¬Nonempty (DivisibilitySeparatingPrime 2 index
        (cyclotomicAtTwo index)))
    (primeIsPrime : prime.Prime)
    (primeDivides : prime ∣ cyclotomicAtTwo index) :
    prime ∣ index := by
  by_contra primeDoesNotDivide
  exact noWitness ⟨separatingPrimeOfPrimeDvdCyclotomicAtTwo
    primeIsPrime primeDivides primeDoesNotDivide⟩

theorem removeIfDivides_eq_self_of_separated_index
    {base index value exponent residual : Nat}
    (witness : DivisibilitySeparatingPrime base index value)
    (indexDoesNotDivide : ¬index ∣ exponent)
    (residualDivides : residual ∣ base ^ exponent - 1) :
    removeIfDivides residual value = residual := by
  have valueDoesNotDivide : ¬value ∣ residual := by
    intro valueDivides
    exact indexDoesNotDivide
      (index_dvd_of_value_dvd_pow_sub_one witness
        (dvd_trans valueDivides residualDivides))
  simp [removeIfDivides, Nat.dvd_iff_mod_eq_zero.not.mp valueDoesNotDivide]

theorem cyclotomicAtTwo_two : cyclotomicAtTwo 2 = 3 := by
  norm_num [cyclotomicAtTwo, Polynomial.cyclotomic_two]

/-- Index two has the expected separating prime `3`. -/
def separatingPrimeAtTwo :
    DivisibilitySeparatingPrime 2 2 (cyclotomicAtTwo 2) where
  prime := 3
  primeIsPrime := by norm_num
  primeDividesValue := by simp [cyclotomicAtTwo_two]
  indexDividesOfPrimeDivides := by
    intro exponent primeDivides
    have congruence : 1 ≡ 2 ^ exponent [MOD 3] :=
      (Nat.modEq_iff_dvd'
        (Nat.one_le_pow exponent 2 (by omega))).2 primeDivides
    have castEquality :
        ((2 ^ exponent : Nat) : ZMod 3) = ((1 : Nat) : ZMod 3) :=
      (ZMod.natCast_eq_natCast_iff' (2 ^ exponent) 1 3).2 congruence.symm
    have powerEquality : (2 : ZMod 3) ^ exponent = 1 := by
      simpa using castEquality
    have orderEquality : orderOf (2 : ZMod 3) = 2 := by
      apply orderOf_eq_prime (p := 2)
      · decide
      · decide
    rw [← orderEquality]
    exact orderOf_dvd_of_pow_eq_one powerEquality

theorem cyclotomicAtTwo_six : cyclotomicAtTwo 6 = 3 := by
  norm_num [cyclotomicAtTwo, Polynomial.cyclotomic_six]

/-- Index six is the exceptional collision: its value is again `3`, so no
prime factor of the value can distinguish exponent six from exponent two. -/
theorem no_separatingPrimeAtSix :
    ¬Nonempty (DivisibilitySeparatingPrime 2 6 (cyclotomicAtTwo 6)) := by
  rintro ⟨witness⟩
  have primeDividesThree : witness.prime ∣ 3 := by
    simpa [cyclotomicAtTwo_six] using witness.primeDividesValue
  have primeIsThree : witness.prime = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp primeDividesThree with
      primeIsOne | primeIsThree
    · exact (witness.primeIsPrime.ne_one primeIsOne).elim
    · exact primeIsThree
  have sixDividesTwo := witness.indexDividesOfPrimeDivides 2 (by
    simp [primeIsThree])
  norm_num at sixDividesTwo

/-- Divisibility of a Mersenne number by a modulus is exactly the
multiplicative-order condition for two modulo that modulus. -/
theorem modulus_dvd_two_pow_sub_one_iff_orderOf_dvd
    (modulus exponent : Nat) :
    modulus ∣ 2 ^ exponent - 1 ↔
      orderOf (2 : ZMod modulus) ∣ exponent := by
  constructor
  · intro divides
    have congruence : 1 ≡ 2 ^ exponent [MOD modulus] :=
      (Nat.modEq_iff_dvd'
        (Nat.one_le_pow exponent 2 (by omega))).2 divides
    have castEquality :
        (2 : ZMod modulus) ^ exponent = 1 := by
      simpa using
        (ZMod.natCast_eq_natCast_iff' (2 ^ exponent) 1 modulus).2
          congruence.symm
    exact orderOf_dvd_of_pow_eq_one castEquality
  · intro orderDivides
    have castEquality : (2 : ZMod modulus) ^ exponent = 1 :=
      orderOf_dvd_iff_pow_eq_one.mp orderDivides
    have congruence : 1 ≡ 2 ^ exponent [MOD modulus] := by
      apply (ZMod.natCast_eq_natCast_iff' 1 (2 ^ exponent) modulus).mp
      simpa using castEquality.symm
    exact (Nat.modEq_iff_dvd'
      (Nat.one_le_pow exponent 2 (by omega))).1 congruence

theorem orderOf_two_mod_three : orderOf (2 : ZMod 3) = 2 := by
  apply (orderOf_eq_iff (x := (2 : ZMod 3)) (by norm_num)).2
  constructor
  · decide
  · intro exponent exponentLt exponentPositive
    have exponentEq : exponent = 1 := by omega
    subst exponent
    decide

theorem orderOf_two_mod_nine : orderOf (2 : ZMod 9) = 6 := by
  apply (orderOf_eq_iff (x := (2 : ZMod 9)) (by norm_num)).2
  constructor
  · decide
  · intro exponent exponentLt exponentPositive
    interval_cases exponent <;> decide

/-- One copy of the exceptional value `3` is removable precisely at even
exponents. -/
theorem three_dvd_two_pow_sub_one_iff (exponent : Nat) :
    3 ∣ 2 ^ exponent - 1 ↔ 2 ∣ exponent := by
  rw [modulus_dvd_two_pow_sub_one_iff_orderOf_dvd, orderOf_two_mod_three]

/-- Both copies `Φ₂(2)=Φ₆(2)=3` are removable precisely when the
exponent is divisible by six. -/
theorem nine_dvd_two_pow_sub_one_iff (exponent : Nat) :
    9 ∣ 2 ^ exponent - 1 ↔ 6 ∣ exponent := by
  rw [modulus_dvd_two_pow_sub_one_iff_orderOf_dvd, orderOf_two_mod_nine]

/-- Evaluated cyclotomic factorization of `2^n - 1`. -/
theorem prod_cyclotomicAtTwo_eq_two_pow_sub_one
    (index : Nat) (indexPositive : 0 < index) :
    ∏ divisor ∈ index.divisors, cyclotomicAtTwo divisor = 2 ^ index - 1 := by
  have polynomialIdentity :=
    Polynomial.prod_cyclotomic_eq_X_pow_sub_one indexPositive Int
  have evaluated :
      (∏ divisor ∈ index.divisors,
          (Polynomial.cyclotomic divisor Int).eval 2) =
        (2 : Int) ^ index - 1 := by
    simpa only [Polynomial.eval_prod, Polynomial.eval_sub,
      Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one] using
      congrArg (Polynomial.eval (2 : Int)) polynomialIdentity
  apply Nat.cast_injective (R := Int)
  rw [Nat.cast_prod]
  simp_rw [cyclotomicAtTwo_cast]
  rw [Nat.cast_sub (Nat.one_le_pow index 2 (by omega)), Nat.cast_pow]
  norm_num
  exact evaluated

/-- Prime-factor accounting for the evaluated cyclotomic factorization. -/
theorem factorization_two_pow_sub_one_eq_sum_cyclotomicAtTwo
    (index prime : Nat) (indexPositive : 0 < index) :
    (2 ^ index - 1).factorization prime =
      ∑ divisor ∈ index.divisors,
        (cyclotomicAtTwo divisor).factorization prime := by
  rw [← prod_cyclotomicAtTwo_eq_two_pow_sub_one index indexPositive]
  exact Nat.factorization_prod_apply fun divisor _ =>
    (cyclotomicAtTwo_positive divisor).ne'

/-- Among the divisors of `p^k*m`, exactly the indices `p^j*m` with
`j ≤ k` have cyclotomic values divisible by `p`, provided `m` is the
multiplicative order of two modulo `p`. -/
theorem divisors_filter_prime_dvd_cyclotomicAtTwo_eq_image
    {prime order exponent : Nat} (primeIsPrime : prime.Prime)
    (orderPositive : 0 < order) (primeDoesNotDivideOrder : ¬prime ∣ order)
    (orderEquality : orderOf (2 : ZMod prime) = order) :
    (prime ^ exponent * order).divisors.filter
        (fun index => prime ∣ cyclotomicAtTwo index) =
      (Finset.range (exponent + 1)).image
        (fun power => prime ^ power * order) := by
  classical
  ext index
  simp only [Finset.mem_filter, Nat.mem_divisors,
    Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨⟨indexDivides, _ambientNonzero⟩, primeDividesValue⟩
    have indexPositive : 0 < index :=
      Nat.pos_of_dvd_of_pos indexDivides
        (mul_pos (pow_pos primeIsPrime.pos exponent) orderPositive)
    obtain ⟨power, indexShape⟩ :=
      (prime_dvd_cyclotomicAtTwo_iff_eq_prime_pow_mul
        primeIsPrime primeDoesNotDivideOrder orderEquality indexPositive).mp
        primeDividesValue
    have powerDivides : prime ^ power ∣ prime ^ exponent := by
      apply (mul_dvd_mul_iff_right orderPositive.ne').mp
      simpa [indexShape] using indexDivides
    have powerLe : power ≤ exponent :=
      (Nat.pow_dvd_pow_iff_le_right primeIsPrime.one_lt).mp powerDivides
    exact ⟨power, by omega, indexShape.symm⟩
  · rintro ⟨power, powerLt, rfl⟩
    have powerLe : power ≤ exponent := by omega
    have indexDivides : prime ^ power * order ∣ prime ^ exponent * order :=
      (mul_dvd_mul_iff_right orderPositive.ne').mpr
        ((Nat.pow_dvd_pow_iff_le_right primeIsPrime.one_lt).mpr powerLe)
    have indexPositive : 0 < prime ^ power * order :=
      mul_pos (pow_pos primeIsPrime.pos power) orderPositive
    exact ⟨⟨indexDivides,
        mul_ne_zero (pow_ne_zero _ primeIsPrime.ne_zero) orderPositive.ne'⟩,
      (prime_dvd_cyclotomicAtTwo_iff_eq_prime_pow_mul primeIsPrime
        primeDoesNotDivideOrder orderEquality indexPositive).mpr ⟨power, rfl⟩⟩

/-- The `p`-adic contribution to the Mersenne factorization at exponent
`p^k*m` is the sum of the contributions along the unique intrinsic chain. -/
theorem sum_cyclotomic_factorization_eq_intrinsic_chain
    {prime order exponent : Nat} (primeIsPrime : prime.Prime)
    (orderPositive : 0 < order) (primeDoesNotDivideOrder : ¬prime ∣ order)
    (orderEquality : orderOf (2 : ZMod prime) = order) :
    (∑ index ∈ (prime ^ exponent * order).divisors,
        (cyclotomicAtTwo index).factorization prime) =
      ∑ power ∈ Finset.range (exponent + 1),
        (cyclotomicAtTwo (prime ^ power * order)).factorization prime := by
  classical
  calc
    (∑ index ∈ (prime ^ exponent * order).divisors,
        (cyclotomicAtTwo index).factorization prime) =
        ∑ index ∈ (prime ^ exponent * order).divisors.filter
          (fun index => prime ∣ cyclotomicAtTwo index),
            (cyclotomicAtTwo index).factorization prime := by
              symm
              rw [Finset.sum_filter]
              apply Finset.sum_congr rfl
              intro index indexMembership
              split
              · rfl
              · symm
                exact Nat.factorization_eq_zero_of_not_dvd ‹_›
    _ = ∑ index ∈ (Finset.range (exponent + 1)).image
          (fun power => prime ^ power * order),
            (cyclotomicAtTwo index).factorization prime := by
              rw [divisors_filter_prime_dvd_cyclotomicAtTwo_eq_image
                primeIsPrime orderPositive primeDoesNotDivideOrder orderEquality]
    _ = ∑ power ∈ Finset.range (exponent + 1),
          (cyclotomicAtTwo (prime ^ power * order)).factorization prime := by
            rw [Finset.sum_image]
            intro first firstMembership second secondMembership equality
            have productsEqual :
                prime ^ first * order = prime ^ second * order := equality
            have powersEqual : prime ^ first = prime ^ second :=
              mul_right_cancel₀ orderPositive.ne' productsEqual
            exact Nat.pow_right_injective primeIsPrime.one_lt powersEqual

/-- LTE and the exact divisor classification determine the total
`p`-adic mass along the intrinsic chain. -/
theorem sum_intrinsic_chain_eq_base_add_exponent
    {prime order : Nat} (primeIsPrime : prime.Prime)
    (primeIsOdd : Odd prime) (orderPositive : 0 < order)
    (primeDoesNotDivideOrder : ¬prime ∣ order)
    (orderEquality : orderOf (2 : ZMod prime) = order)
    (exponent : Nat) :
    (∑ power ∈ Finset.range (exponent + 1),
        (cyclotomicAtTwo (prime ^ power * order)).factorization prime) =
      (cyclotomicAtTwo order).factorization prime + exponent := by
  have primeDividesBase : prime ∣ cyclotomicAtTwo order :=
    (prime_dvd_cyclotomicAtTwo_iff_eq_prime_pow_mul primeIsPrime
      primeDoesNotDivideOrder orderEquality orderPositive).mpr ⟨0, by simp⟩
  have cyclotomicDividesMersenne :
      cyclotomicAtTwo order ∣ 2 ^ order - 1 := by
    have factorization :=
      prod_cyclotomicAtTwo_eq_two_pow_sub_one order orderPositive
    have membership : order ∈ order.divisors :=
      Nat.mem_divisors.mpr ⟨dvd_refl order, orderPositive.ne'⟩
    have dividesProduct :
        cyclotomicAtTwo order ∣
          ∏ divisor ∈ order.divisors, cyclotomicAtTwo divisor :=
      Finset.dvd_prod_of_mem (fun divisor => cyclotomicAtTwo divisor) membership
    rwa [factorization] at dividesProduct
  have primeDividesMersenne : prime ∣ 2 ^ order - 1 :=
    dvd_trans primeDividesBase cyclotomicDividesMersenne
  have lte := factorization_two_pow_mul_sub_one primeIsPrime primeIsOdd
    orderPositive (pow_pos primeIsPrime.pos exponent)
    primeDividesMersenne
  rw [Nat.factorization_pow_self primeIsPrime] at lte
  have expandedPositive : 0 < prime ^ exponent * order :=
    mul_pos (pow_pos primeIsPrime.pos exponent) orderPositive
  have fullFactorization :
      (2 ^ (prime ^ exponent * order) - 1).factorization prime =
        ∑ power ∈ Finset.range (exponent + 1),
          (cyclotomicAtTwo (prime ^ power * order)).factorization prime := by
    calc
      (2 ^ (prime ^ exponent * order) - 1).factorization prime =
          ∑ index ∈ (prime ^ exponent * order).divisors,
            (cyclotomicAtTwo index).factorization prime :=
        factorization_two_pow_sub_one_eq_sum_cyclotomicAtTwo
          (prime ^ exponent * order) prime expandedPositive
      _ = _ := sum_cyclotomic_factorization_eq_intrinsic_chain
        primeIsPrime orderPositive primeDoesNotDivideOrder orderEquality
  have baseFactorization :
      (2 ^ order - 1).factorization prime =
        (cyclotomicAtTwo order).factorization prime := by
    calc
      (2 ^ order - 1).factorization prime =
          ∑ index ∈ order.divisors,
            (cyclotomicAtTwo index).factorization prime :=
        factorization_two_pow_sub_one_eq_sum_cyclotomicAtTwo
          order prime orderPositive
      _ = ∑ power ∈ Finset.range (0 + 1),
          (cyclotomicAtTwo (prime ^ power * order)).factorization prime := by
            simpa using
              (sum_cyclotomic_factorization_eq_intrinsic_chain
                primeIsPrime orderPositive primeDoesNotDivideOrder
                orderEquality (exponent := 0))
      _ = (cyclotomicAtTwo order).factorization prime := by simp
  rw [← fullFactorization, ← baseFactorization]
  simpa [mul_comm] using lte

/-- Every intrinsic occurrence of an odd prime in `Φ_(p^k*m)(2)` has
factorization exponent exactly one. -/
theorem intrinsic_prime_factorization_eq_one
    {prime order exponent : Nat} (primeIsPrime : prime.Prime)
    (primeIsOdd : Odd prime) (orderPositive : 0 < order)
    (primeDoesNotDivideOrder : ¬prime ∣ order)
    (orderEquality : orderOf (2 : ZMod prime) = order)
    (exponentPositive : 0 < exponent) :
    (cyclotomicAtTwo (prime ^ exponent * order)).factorization prime = 1 := by
  obtain ⟨previous, rfl⟩ := Nat.exists_eq_succ_of_ne_zero exponentPositive.ne'
  have previousEquation := sum_intrinsic_chain_eq_base_add_exponent
    primeIsPrime primeIsOdd orderPositive primeDoesNotDivideOrder
    orderEquality previous
  have nextEquation := sum_intrinsic_chain_eq_base_add_exponent
    primeIsPrime primeIsOdd orderPositive primeDoesNotDivideOrder
    orderEquality (previous + 1)
  rw [show previous + 1 + 1 = (previous + 1) + 1 by rfl,
    Finset.sum_range_succ] at nextEquation
  rw [previousEquation] at nextEquation
  have afterBaseCancellation :
      previous +
          (cyclotomicAtTwo (prime ^ (previous + 1) * order)).factorization prime =
        previous + 1 :=
    by simpa [Nat.add_assoc] using nextEquation
  have finalFactorization :
      (cyclotomicAtTwo (prime ^ (previous + 1) * order)).factorization prime = 1 :=
    Nat.add_left_cancel afterBaseCancellation
  simpa [Nat.succ_eq_add_one] using finalFactorization

/-- If `Φ_n(2)` has no separating prime, then any one of its prime factors
is the whole value.  Thus the remaining primitive-divisor problem is a
pure size question. -/
theorem cyclotomicAtTwo_eq_prime_of_no_separatingPrime
    {index prime : Nat} (indexGreaterThanOne : 1 < index)
    (noWitness :
      ¬Nonempty (DivisibilitySeparatingPrime 2 index
        (cyclotomicAtTwo index)))
    (primeIsPrime : prime.Prime)
    (primeDividesValue : prime ∣ cyclotomicAtTwo index) :
    cyclotomicAtTwo index = prime := by
  have indexPositive : 0 < index := indexGreaterThanOne.trans_le' (by omega)
  have primeDividesIndex : prime ∣ index :=
    prime_dvd_index_of_no_separatingPrime noWitness primeIsPrime
      primeDividesValue
  have root := cyclotomicAtTwo_isRoot primeIsPrime primeDividesValue
  have primeCoprime : Nat.Coprime 2 prime := by
    letI : Fact prime.Prime := ⟨primeIsPrime⟩
    exact Polynomial.coprime_of_root_cyclotomic indexPositive root
  have primeIsNotTwo : prime ≠ 2 := by
    intro primeIsTwo
    subst prime
    norm_num at primeCoprime
  have primeIsOdd : Odd prime := primeIsPrime.odd_of_ne_two primeIsNotTwo
  let order := ordCompl[prime] index
  have orderPositive : 0 < order :=
    Nat.ordCompl_pos prime indexPositive.ne'
  have primeDoesNotDivideOrder : ¬prime ∣ order :=
    Nat.not_dvd_ordCompl primeIsPrime indexPositive.ne'
  have orderEquality : orderOf (2 : ZMod prime) = order :=
    orderOf_two_eq_ordCompl_of_prime_dvd_cyclotomicAtTwo
      indexPositive primeIsPrime primeDividesValue
  have exponentPositive : 0 < index.factorization prime :=
    primeIsPrime.factorization_pos_of_dvd indexPositive.ne' primeDividesIndex
  have decomposition :
      prime ^ index.factorization prime * order = index :=
    Nat.ordProj_mul_ordCompl_eq_self index prime
  have primeFactorization :
      (cyclotomicAtTwo index).factorization prime = 1 := by
    rw [← decomposition]
    exact intrinsic_prime_factorization_eq_one primeIsPrime primeIsOdd
      orderPositive primeDoesNotDivideOrder orderEquality exponentPositive
  apply Nat.eq_of_factorization_eq (cyclotomicAtTwo_positive index).ne'
    primeIsPrime.ne_zero
  intro other
  by_cases otherIsPrime : other.Prime
  · by_cases samePrime : other = prime
    · subst other
      simpa [primeIsPrime.factorization] using primeFactorization
    · have otherDoesNotDivideValue :
          ¬other ∣ cyclotomicAtTwo index := by
        intro otherDividesValue
        have otherDividesIndex : other ∣ index :=
          prime_dvd_index_of_no_separatingPrime noWitness otherIsPrime
            otherDividesValue
        exact samePrime (intrinsic_prime_unique otherIsPrime primeIsPrime
          otherDividesValue primeDividesValue otherDividesIndex
          primeDividesIndex)
      rw [Nat.factorization_eq_zero_of_not_dvd otherDoesNotDivideValue]
      simp [primeIsPrime.factorization, samePrime]
  · simp [Nat.factorization_eq_zero_of_not_prime, otherIsPrime]

/-- Elementary growth needed by the cyclotomic size argument. -/
theorem succ_lt_two_pow (number : Nat) (numberBound : 3 ≤ number) :
    number + 1 < 2 ^ number := by
  induction number, numberBound using Nat.le_induction with
  | base => norm_num
  | succ number _ inductionHypothesis =>
      rw [pow_succ]
      have powerPositive : 0 < 2 ^ number := pow_pos (by omega) number
      omega

/-- A form of exponential domination stable under taking positive powers. -/
theorem prime_mul_three_pow_lt_two_pow_sub_one_pow
    (prime exponent : Nat) (primeBound : 5 ≤ prime)
    (exponentPositive : 0 < exponent) :
    prime * 3 ^ exponent < (2 ^ prime - 1) ^ exponent := by
  obtain ⟨previous, rfl⟩ := Nat.exists_eq_succ_of_ne_zero exponentPositive.ne'
  have baseBound : 3 * prime < 2 ^ prime - 1 := by
    induction prime, primeBound using Nat.le_induction with
    | base => norm_num
    | succ number numberBound inductionHypothesis =>
        rw [pow_succ]
        have powerLarge : 4 ≤ 2 ^ number := by
          exact Nat.pow_le_pow_right (n := 2) (by omega)
            (by omega : 2 ≤ number)
        omega
  have threeLeBase : 3 ≤ 2 ^ prime - 1 := by omega
  have powersLe : 3 ^ previous ≤ (2 ^ prime - 1) ^ previous :=
    Nat.pow_le_pow_left threeLeBase previous
  simp only [pow_succ]
  calc
    prime * (3 ^ previous * 3) = (3 * prime) * 3 ^ previous := by ring
    _ < (2 ^ prime - 1) * 3 ^ previous :=
      Nat.mul_lt_mul_of_pos_right baseBound (pow_pos (by omega) previous)
    _ ≤ (2 ^ prime - 1) * (2 ^ prime - 1) ^ previous :=
      Nat.mul_le_mul_left _ powersLe
    _ = (2 ^ prime - 1) ^ previous * (2 ^ prime - 1) := by ring

/-- Real evaluation of the natural cyclotomic value. -/
theorem cyclotomicAtTwo_cast_real (index : Nat) :
    (cyclotomicAtTwo index : Real) =
      (Polynomial.cyclotomic index Real).eval 2 := by
  calc
    (cyclotomicAtTwo index : Real) =
        ((cyclotomicAtTwo index : Int) : Real) := by norm_num
    _ = (((Polynomial.cyclotomic index Int).eval 2 : Int) : Real) := by
      rw [cyclotomicAtTwo_cast]
    _ = (Polynomial.cyclotomic index Real).eval 2 := by
      symm
      simpa using Polynomial.cyclotomic.eval_apply
        (2 : Int) index (Int.castRingHom Real)

/-- Evaluation form of the prime-step expansion when the prime already
divides the index. -/
theorem cyclotomic_eval_prime_step_of_dvd
    {prime index : Nat} (primeIsPrime : prime.Prime)
    (primeDividesIndex : prime ∣ index) :
    (Polynomial.cyclotomic (index * prime) Real).eval 2 =
      (Polynomial.cyclotomic index Real).eval ((2 : Real) ^ prime) := by
  rw [← Polynomial.cyclotomic_expand_eq_cyclotomic
    primeIsPrime primeDividesIndex]
  exact Polynomial.expand_eval prime (Polynomial.cyclotomic index Real) 2

/-- Evaluation form of the prime-step expansion when the prime is new to
the index. -/
theorem cyclotomic_eval_prime_step_of_not_dvd
    {prime index : Nat} (primeIsPrime : prime.Prime)
    (primeDoesNotDivideIndex : ¬prime ∣ index) :
    (Polynomial.cyclotomic index Real).eval ((2 : Real) ^ prime) =
      (Polynomial.cyclotomic (index * prime) Real).eval 2 *
        (Polynomial.cyclotomic index Real).eval 2 := by
  calc
    (Polynomial.cyclotomic index Real).eval ((2 : Real) ^ prime) =
        (Polynomial.expand Real prime
          (Polynomial.cyclotomic index Real)).eval 2 :=
      (Polynomial.expand_eval prime (Polynomial.cyclotomic index Real) 2).symm
    _ = (Polynomial.cyclotomic (index * prime) Real *
          Polynomial.cyclotomic index Real).eval 2 := by
      rw [Polynomial.cyclotomic_expand_eq_cyclotomic_mul
        primeIsPrime primeDoesNotDivideIndex]
    _ = _ := by rw [Polynomial.eval_mul]

/-- The intrinsic prime is strictly smaller than its cyclotomic value except
for the base-two collision `Φ₆(2)=3`. -/
theorem prime_lt_cyclotomicAtTwo_of_intrinsic_not_exception
    {prime order exponent : Nat} (primeIsPrime : prime.Prime)
    (primeIsOdd : Odd prime) (orderPositive : 0 < order)
    (primeDoesNotDivideOrder : ¬prime ∣ order)
    (orderEquality : orderOf (2 : ZMod prime) = order)
    (exponentPositive : 0 < exponent)
    (notException : ¬(prime = 3 ∧ order = 2 ∧ exponent = 1)) :
    prime < cyclotomicAtTwo (prime ^ exponent * order) := by
  have primeIsNotTwo : prime ≠ 2 := by
    intro primeIsTwo
    subst prime
    norm_num at primeIsOdd
  have primeAtLeastThree : 3 ≤ prime := by
    have := primeIsPrime.two_le
    omega
  obtain ⟨previous, rfl⟩ := Nat.exists_eq_succ_of_ne_zero exponentPositive.ne'
  rcases previous.eq_zero_or_pos with previousZero | previousPositive
  · subst previous
    have orderIsNotOne : order ≠ 1 := by
      intro orderIsOne
      have primeDividesOne : prime ∣ 2 ^ 1 - 1 :=
        (modulus_dvd_two_pow_sub_one_iff_orderOf_dvd prime 1).mpr (by
          rw [orderEquality, orderIsOne])
      norm_num at primeDividesOne
      exact primeIsPrime.ne_one primeDividesOne
    have orderAtLeastTwo : 2 ≤ order := by omega
    have orderAtLeastThree : 3 ≤ order := by
      by_contra orderNotThree
      have orderIsTwo : order = 2 := by omega
      have primeDividesThree : prime ∣ 3 := by
        have dividesMersenne : prime ∣ 2 ^ 2 - 1 :=
          (modulus_dvd_two_pow_sub_one_iff_orderOf_dvd prime 2).mpr (by
            rw [orderEquality, orderIsTwo])
        norm_num at dividesMersenne ⊢
        exact dividesMersenne
      have primeIsThree : prime = 3 := by
        rcases (Nat.dvd_prime Nat.prime_three).mp primeDividesThree with
          primeIsOne | primeIsThree
        · exact (primeIsPrime.ne_one primeIsOne).elim
        · exact primeIsThree
      exact notException ⟨primeIsThree, orderIsTwo, rfl⟩
    have primeAtLeastFive : 5 ≤ prime := by
      by_contra primeNotFive
      have primeIsThree : prime = 3 := by
        rcases primeIsOdd with ⟨half, primeForm⟩
        omega
      have orderIsTwo : order = 2 := by
        calc
          order = orderOf (2 : ZMod prime) := orderEquality.symm
          _ = orderOf (2 : ZMod 3) := by rw [primeIsThree]
          _ = 2 := orderOf_two_mod_three
      omega
    have totientPositive : 0 < order.totient :=
      Nat.totient_pos.mpr orderPositive
    have lowerBound :=
      Polynomial.sub_one_pow_totient_lt_cyclotomic_eval
        (n := order) (q := (2 : Real) ^ prime)
        (by omega) (one_lt_pow₀ (by norm_num) primeIsPrime.pos.ne')
    have upperBound :=
      Polynomial.cyclotomic_eval_lt_add_one_pow_totient
        (n := order) (q := (2 : Real)) orderAtLeastThree (by norm_num)
    have upperBoundThree :
        (Polynomial.cyclotomic order Real).eval 2 <
          (3 : Real) ^ order.totient := by
      norm_num at upperBound
      exact upperBound
    have stepEquality := cyclotomic_eval_prime_step_of_not_dvd
      primeIsPrime primeDoesNotDivideOrder
    have stepValues :
        (Polynomial.cyclotomic order Real).eval ((2 : Real) ^ prime) =
          (cyclotomicAtTwo (prime * order) : Real) *
            (Polynomial.cyclotomic order Real).eval 2 := by
      calc
        (Polynomial.cyclotomic order Real).eval ((2 : Real) ^ prime) =
            (Polynomial.cyclotomic (order * prime) Real).eval 2 *
              (Polynomial.cyclotomic order Real).eval 2 := stepEquality
        _ = (cyclotomicAtTwo (prime * order) : Real) *
              (Polynomial.cyclotomic order Real).eval 2 := by
          rw [cyclotomicAtTwo_cast_real]
          congr 2
          rw [mul_comm]
    have numericGapNat := prime_mul_three_pow_lt_two_pow_sub_one_pow
      prime order.totient primeAtLeastFive totientPositive
    have numericGap :
        (prime : Real) * 3 ^ order.totient <
          (((2 : Real) ^ prime) - 1) ^ order.totient := by
      calc
        (prime : Real) * 3 ^ order.totient =
            ((prime * 3 ^ order.totient : Nat) : Real) := by norm_num
        _ < (((2 ^ prime - 1) ^ order.totient : Nat) : Real) := by
          exact_mod_cast numericGapNat
        _ = (((2 : Real) ^ prime) - 1) ^ order.totient := by
          rw [Nat.cast_pow, Nat.cast_sub
            (Nat.one_le_pow prime 2 (by omega)), Nat.cast_pow]
          norm_num
    by_contra desiredNotStrict
    have targetLePrime :
        cyclotomicAtTwo (prime * order) ≤ prime := by
      simpa using (Nat.le_of_not_gt desiredNotStrict)
    have targetPositiveReal :
        (0 : Real) < cyclotomicAtTwo (prime * order) := by
      exact_mod_cast (cyclotomicAtTwo_positive (prime * order))
    have targetCastLe :
        (cyclotomicAtTwo (prime * order) : Real) ≤ (prime : Real) := by
      exact_mod_cast targetLePrime
    have productUpper :
        (cyclotomicAtTwo (prime * order) : Real) *
            (Polynomial.cyclotomic order Real).eval 2 <
          (prime : Real) * 3 ^ order.totient := by
      calc
        (cyclotomicAtTwo (prime * order) : Real) *
            (Polynomial.cyclotomic order Real).eval 2 <
            (cyclotomicAtTwo (prime * order) : Real) *
              3 ^ order.totient :=
          mul_lt_mul_of_pos_left upperBoundThree targetPositiveReal
        _ ≤ (prime : Real) * 3 ^ order.totient :=
          mul_le_mul_of_nonneg_right targetCastLe (by positivity)
    have lowerThanProduct :
        (((2 : Real) ^ prime) - 1) ^ order.totient <
          (cyclotomicAtTwo (prime * order) : Real) *
            (Polynomial.cyclotomic order Real).eval 2 := by
      calc
        (((2 : Real) ^ prime) - 1) ^ order.totient <
            (Polynomial.cyclotomic order Real).eval
              ((2 : Real) ^ prime) := lowerBound
        _ = _ := stepValues
    exact (lt_asymm (numericGap.trans lowerThanProduct)) productUpper
  · obtain ⟨earlier, rfl⟩ := Nat.exists_eq_succ_of_ne_zero previousPositive.ne'
    let priorIndex := prime ^ (earlier + 1) * order
    have primeDividesPrior : prime ∣ priorIndex := by
      refine ⟨prime ^ earlier * order, ?_⟩
      simp [priorIndex, pow_succ, mul_comm, mul_left_comm]
    have priorAtLeastTwo : 2 ≤ priorIndex := by
      have powerAtLeastPrime : prime ≤ prime ^ (earlier + 1) := by
        rw [pow_succ]
        calc
          prime = 1 * prime := by simp
          _ ≤ prime ^ earlier * prime :=
            Nat.mul_le_mul_right prime
              (Nat.one_le_pow earlier prime primeIsPrime.pos)
      dsimp [priorIndex]
      exact primeIsPrime.two_le.trans
        (powerAtLeastPrime.trans
          (Nat.le_mul_of_pos_right (prime ^ (earlier + 1)) orderPositive))
    have targetIndexEquality :
        priorIndex * prime = prime ^ (earlier + 2) * order := by
      simp [priorIndex, pow_succ, mul_comm, mul_left_comm]
    have stepEquality := cyclotomic_eval_prime_step_of_dvd
      primeIsPrime primeDividesPrior
    have stepValues :
        (cyclotomicAtTwo (prime ^ (earlier + 2) * order) : Real) =
          (Polynomial.cyclotomic priorIndex Real).eval
            ((2 : Real) ^ prime) := by
      calc
        (cyclotomicAtTwo (prime ^ (earlier + 2) * order) : Real) =
            (Polynomial.cyclotomic
              (prime ^ (earlier + 2) * order) Real).eval 2 :=
          cyclotomicAtTwo_cast_real _
        _ = (Polynomial.cyclotomic (priorIndex * prime) Real).eval 2 := by
          rw [targetIndexEquality]
        _ = _ := stepEquality
    have lowerBound :=
      Polynomial.sub_one_pow_totient_lt_cyclotomic_eval
        (n := priorIndex) (q := (2 : Real) ^ prime)
        priorAtLeastTwo (one_lt_pow₀ (by norm_num) primeIsPrime.pos.ne')
    have baseLargerThanPrimeNat : prime < 2 ^ prime - 1 := by
      have := succ_lt_two_pow prime primeAtLeastThree
      omega
    have totientPositive : 0 < priorIndex.totient :=
      Nat.totient_pos.mpr (by omega)
    have primeBelowPowerNat :
        prime < (2 ^ prime - 1) ^ priorIndex.totient :=
      baseLargerThanPrimeNat.trans_le (Nat.le_pow totientPositive)
    have primeBelowPower :
        (prime : Real) <
          (((2 : Real) ^ prime) - 1) ^ priorIndex.totient := by
      calc
        (prime : Real) <
            (((2 ^ prime - 1) ^ priorIndex.totient : Nat) : Real) := by
          exact_mod_cast primeBelowPowerNat
        _ = (((2 : Real) ^ prime) - 1) ^ priorIndex.totient := by
          rw [Nat.cast_pow, Nat.cast_sub
            (Nat.one_le_pow prime 2 (by omega)), Nat.cast_pow]
          norm_num
    have lowerThanTarget :
        (((2 : Real) ^ prime) - 1) ^ priorIndex.totient <
          (cyclotomicAtTwo (prime ^ (earlier + 2) * order) : Real) := by
      calc
        (((2 : Real) ^ prime) - 1) ^ priorIndex.totient <
            (Polynomial.cyclotomic priorIndex Real).eval
              ((2 : Real) ^ prime) := lowerBound
        _ = _ := stepValues.symm
    have realConclusion :
        (prime : Real) <
          (cyclotomicAtTwo (prime ^ (earlier + 2) * order) : Real) :=
      primeBelowPower.trans lowerThanTarget
    exact_mod_cast realConclusion

/-- Base-two Bang theorem in exactly the form needed by the sieve.  Every
cyclotomic value after index one has a divisibility-separating prime, with
the unique exception `Φ₆(2) = Φ₂(2) = 3`.

This proof is internal: it combines the cyclotomic root/order
characterization, odd-prime LTE, uniqueness of an intrinsic prime, and the
size estimate above. -/
theorem exists_separatingPrime_of_index_ne_six
    {index : Nat} (indexGreaterThanOne : 1 < index)
    (indexIsNotSix : index ≠ 6) :
    Nonempty (DivisibilitySeparatingPrime 2 index
      (cyclotomicAtTwo index)) := by
  by_contra noWitness
  have valueGreaterThanOne : 1 < cyclotomicAtTwo index := by
    simpa [cyclotomicAtTwo] using
      (Polynomial.sub_one_lt_natAbs_cyclotomic_eval
        (n := index) (q := 2) indexGreaterThanOne (by norm_num))
  let prime := (cyclotomicAtTwo index).minFac
  have primeIsPrime : prime.Prime :=
    Nat.minFac_prime valueGreaterThanOne.ne'
  have primeDividesValue : prime ∣ cyclotomicAtTwo index :=
    Nat.minFac_dvd _
  have valueEqualsPrime : cyclotomicAtTwo index = prime :=
    cyclotomicAtTwo_eq_prime_of_no_separatingPrime indexGreaterThanOne
      noWitness primeIsPrime primeDividesValue
  have primeDividesIndex : prime ∣ index :=
    prime_dvd_index_of_no_separatingPrime noWitness primeIsPrime
      primeDividesValue
  have indexPositive : 0 < index := by omega
  have root := cyclotomicAtTwo_isRoot primeIsPrime primeDividesValue
  have primeCoprime : Nat.Coprime 2 prime := by
    letI : Fact prime.Prime := ⟨primeIsPrime⟩
    exact Polynomial.coprime_of_root_cyclotomic indexPositive root
  have primeIsNotTwo : prime ≠ 2 := by
    intro primeIsTwo
    rw [primeIsTwo] at primeCoprime
    norm_num at primeCoprime
  have primeIsOdd : Odd prime :=
    primeIsPrime.odd_of_ne_two primeIsNotTwo
  let order := ordCompl[prime] index
  have orderPositive : 0 < order :=
    Nat.ordCompl_pos prime indexPositive.ne'
  have primeDoesNotDivideOrder : ¬prime ∣ order :=
    Nat.not_dvd_ordCompl primeIsPrime indexPositive.ne'
  have orderEquality : orderOf (2 : ZMod prime) = order :=
    orderOf_two_eq_ordCompl_of_prime_dvd_cyclotomicAtTwo
      indexPositive primeIsPrime primeDividesValue
  have exponentPositive : 0 < index.factorization prime :=
    primeIsPrime.factorization_pos_of_dvd indexPositive.ne'
      primeDividesIndex
  have decomposition :
      prime ^ index.factorization prime * order = index :=
    Nat.ordProj_mul_ordCompl_eq_self index prime
  have notException :
      ¬(prime = 3 ∧ order = 2 ∧ index.factorization prime = 1) := by
    rintro ⟨primeIsThree, orderIsTwo, exponentIsOne⟩
    have exponentIsOneThree : index.factorization 3 = 1 := by
      simpa [primeIsThree] using exponentIsOne
    apply indexIsNotSix
    rw [← decomposition, primeIsThree, orderIsTwo, exponentIsOneThree]
    norm_num
  have primeLessThanValue : prime < cyclotomicAtTwo index := by
    rw [← decomposition]
    exact prime_lt_cyclotomicAtTwo_of_intrinsic_not_exception
      primeIsPrime primeIsOdd orderPositive primeDoesNotDivideOrder
      orderEquality exponentPositive notException
  rw [valueEqualsPrime] at primeLessThanValue
  exact (Nat.lt_irrefl prime) primeLessThanValue

theorem toList_map_prod {α M : Type*} [DecidableEq α] [CommMonoid M]
    (items : Finset α) (f : α → M) :
    (items.toList.map f).prod = ∏ item ∈ items, f item := by
  induction items using Finset.induction_on with
  | empty => simp
  | @insert item items itemFresh inductionHypothesis =>
      simp [itemFresh]

/-- Values at two for the proper divisors of `index`.  Their list order is
irrelevant because their full product is known to divide the candidate. -/
noncomputable def properDivisorValues (index : Nat) : List Nat :=
  index.properDivisors.toList.map cyclotomicAtTwo

theorem properDivisorValues_prod (index : Nat) :
    (properDivisorValues index).prod =
      ∏ divisor ∈ index.properDivisors, cyclotomicAtTwo divisor := by
  exact toList_map_prod index.properDivisors cyclotomicAtTwo

/-- The conventional indexed cyclotomic sieve is correct: divide `2^n-1`
by the values belonging to every proper divisor of `n`. -/
theorem scan_properDivisorValues_eq_cyclotomicAtTwo
    (index : Nat) (indexPositive : 0 < index) :
    scan (properDivisorValues index) (2 ^ index - 1) =
      cyclotomicAtTwo index := by
  let divisorProduct :=
    ∏ divisor ∈ index.properDivisors, cyclotomicAtTwo divisor
  have factorization :=
    prod_cyclotomicAtTwo_eq_two_pow_sub_one index indexPositive
  have divisorsDecomposition :
      (∏ divisor ∈ index.divisors, cyclotomicAtTwo divisor) =
        cyclotomicAtTwo index * divisorProduct := by
    rw [← Nat.cons_self_properDivisors indexPositive.ne']
    simp [divisorProduct]
  rw [divisorsDecomposition] at factorization
  have productDivides : divisorProduct ∣ 2 ^ index - 1 := by
    refine ⟨cyclotomicAtTwo index, ?_⟩
    rw [mul_comm]
    exact factorization.symm
  have productPositive : 0 < divisorProduct := by
    apply Finset.prod_pos
    intro divisor divisorMembership
    exact cyclotomicAtTwo_positive divisor
  rw [scan_eq_div_prod_of_prod_dvd (properDivisorValues index)
      (2 ^ index - 1)]
  · rw [properDivisorValues_prod]
    change (2 ^ index - 1) / divisorProduct = cyclotomicAtTwo index
    rw [← factorization, mul_comm, Nat.mul_div_right _ productPositive]
  · simpa [properDivisorValues_prod] using productDivides

/-- Positive indices in reverse chronological order: `n,n-1,...,1`. -/
def descendingIndices : Nat → List Nat
  | 0 => []
  | bound + 1 => (bound + 1) :: descendingIndices bound

@[simp] theorem descendingIndices_zero : descendingIndices 0 = [] := rfl

@[simp] theorem descendingIndices_succ (bound : Nat) :
    descendingIndices (bound + 1) =
      (bound + 1) :: descendingIndices bound := rfl

@[simp] theorem mem_descendingIndices {index bound : Nat} :
    index ∈ descendingIndices bound ↔ 1 ≤ index ∧ index ≤ bound := by
  induction bound with
  | zero => simp; omega
  | succ bound inductionHypothesis =>
      simp only [descendingIndices_succ, List.mem_cons, inductionHypothesis]
      omega

theorem descendingIndices_nodup (bound : Nat) :
    (descendingIndices bound).Nodup := by
  induction bound with
  | zero => simp
  | succ bound inductionHypothesis =>
      simp [inductionHypothesis]

/-- The full reverse history of cyclotomic values through `bound`. -/
noncomputable def descendingValues (bound : Nat) : List Nat :=
  (descendingIndices bound).map cyclotomicAtTwo

@[simp] theorem descendingValues_zero : descendingValues 0 = [] := rfl

@[simp] theorem descendingValues_succ (bound : Nat) :
    descendingValues (bound + 1) =
      cyclotomicAtTwo (bound + 1) :: descendingValues bound := rfl

/-- At even exponents not divisible by six, the earlier occurrence
`Φ₆(2)=3` consumes the factor conventionally assigned to `Φ₂(2)=3`.
This predicate records that single order-aware swap. -/
def effectiveDivisor (exponent index : Nat) : Prop :=
  if 2 ∣ exponent ∧ ¬6 ∣ exponent then
    index = 6 ∨ (index ∣ exponent ∧ index ≠ 2)
  else
    index ∣ exponent

instance (exponent : Nat) : DecidablePred (effectiveDivisor exponent) :=
  fun _ => by
    unfold effectiveDivisor
    infer_instance

theorem effectiveDivisor_of_no_swap {exponent : Nat}
    (noSwap : ¬(2 ∣ exponent ∧ ¬6 ∣ exponent)) (index : Nat) :
    effectiveDivisor exponent index ↔ index ∣ exponent := by
  simp [effectiveDivisor, noSwap]

theorem effectiveDivisor_six_of_swap {exponent : Nat}
    (swap : 2 ∣ exponent ∧ ¬6 ∣ exponent) :
    effectiveDivisor exponent 6 := by
  simp [effectiveDivisor, swap]

theorem effectiveDivisor_one (exponent : Nat) :
    effectiveDivisor exponent 1 := by
  by_cases swap : 2 ∣ exponent ∧ ¬6 ∣ exponent
  · simp [effectiveDivisor, swap]
  · simp [effectiveDivisor, swap]

theorem not_effectiveDivisor_two_of_swap {exponent : Nat}
    (swap : 2 ∣ exponent ∧ ¬6 ∣ exponent) :
    ¬effectiveDivisor exponent 2 := by
  simp [effectiveDivisor, swap]

theorem effectiveDivisor_iff_dvd_of_ne_two_ne_six
    {exponent index : Nat} (indexIsNotTwo : index ≠ 2)
    (indexIsNotSix : index ≠ 6) :
    effectiveDivisor exponent index ↔ index ∣ exponent := by
  by_cases swap : 2 ∣ exponent ∧ ¬6 ∣ exponent
  · simp [effectiveDivisor, swap, indexIsNotTwo, indexIsNotSix]
  · simp [effectiveDivisor, swap]

theorem two_not_dvd_of_not_effectiveDivisor_six {exponent : Nat}
    (notSelected : ¬effectiveDivisor exponent 6) :
    ¬2 ∣ exponent := by
  intro twoDivides
  by_cases sixDivides : 6 ∣ exponent
  · exact notSelected (by
      simp [effectiveDivisor, sixDivides])
  · exact notSelected (by
      simp [effectiveDivisor, twoDivides, sixDivides])

theorem six_not_dvd_of_two_dvd_not_effectiveDivisor_two {exponent : Nat}
    (twoDivides : 2 ∣ exponent)
    (notSelected : ¬effectiveDivisor exponent 2) :
    ¬6 ∣ exponent := by
  intro sixDivides
  apply notSelected
  apply (effectiveDivisor_of_no_swap (exponent := exponent) ?_ 2).2
  · exact twoDivides
  · rintro ⟨_, sixDoesNotDivide⟩
    exact sixDoesNotDivide sixDivides

/-- Product of the order-aware selected values among `bound,...,1`. -/
noncomputable def effectiveDivisorProduct
    (exponent bound : Nat) : Nat :=
  (((descendingIndices bound).filter (effectiveDivisor exponent)).map
    cyclotomicAtTwo).prod

@[simp] theorem effectiveDivisorProduct_zero (exponent : Nat) :
    effectiveDivisorProduct exponent 0 = 1 := rfl

@[simp] theorem effectiveDivisorProduct_succ
    (exponent bound : Nat) :
    effectiveDivisorProduct exponent (bound + 1) =
      if effectiveDivisor exponent (bound + 1) then
        cyclotomicAtTwo (bound + 1) *
          effectiveDivisorProduct exponent bound
      else
        effectiveDivisorProduct exponent bound := by
  by_cases selected : effectiveDivisor exponent (bound + 1)
  · simp [effectiveDivisorProduct, selected]
  · simp [effectiveDivisorProduct, selected]

@[simp] theorem effectiveDivisorProduct_one (exponent : Nat) :
    effectiveDivisorProduct exponent 1 = 1 := by
  rw [effectiveDivisorProduct_succ]
  simp [effectiveDivisor_one]

/-- The order-aware swap changes which occurrence of the value `3` is
consumed, but not the selected product. -/
theorem effectiveDivisorProduct_pred_eq_properDivisorProduct
    {exponent : Nat} (exponentAtLeastSeven : 7 ≤ exponent) :
    effectiveDivisorProduct exponent (exponent - 1) =
      ∏ divisor ∈ exponent.properDivisors, cyclotomicAtTwo divisor := by
  classical
  let selectedList :=
    (descendingIndices (exponent - 1)).filter (effectiveDivisor exponent)
  have selectedNodup : selectedList.Nodup :=
    (descendingIndices_nodup (exponent - 1)).filter _
  rw [effectiveDivisorProduct, ← List.prod_toFinset cyclotomicAtTwo selectedNodup]
  by_cases swap : 2 ∣ exponent ∧ ¬6 ∣ exponent
  · have selectedFinset :
        selectedList.toFinset =
          insert 6 (exponent.properDivisors.erase 2) := by
      ext index
      simp only [selectedList, List.mem_toFinset, List.mem_filter,
        decide_eq_true_eq, mem_descendingIndices, effectiveDivisor, if_pos swap,
        Finset.mem_insert, Finset.mem_erase, Nat.mem_properDivisors]
      constructor
      · rintro ⟨⟨indexPositive, indexBound⟩,
          indexIsSix | ⟨indexDivides, indexIsNotTwo⟩⟩
        · exact Or.inl indexIsSix
        · exact Or.inr ⟨indexIsNotTwo, indexDivides, by omega⟩
      · rintro (indexIsSix | ⟨indexIsNotTwo, indexDivides, indexLess⟩)
        · subst index
          exact ⟨by omega, Or.inl rfl⟩
        · have indexPositive : 0 < index :=
            Nat.pos_of_dvd_of_pos indexDivides (by omega)
          exact ⟨by omega, Or.inr ⟨indexDivides, indexIsNotTwo⟩⟩
    rw [selectedFinset]
    have sixNotInErased : 6 ∉ exponent.properDivisors.erase 2 := by
      simp [Nat.mem_properDivisors, swap.2]
    rw [Finset.prod_insert sixNotInErased]
    have twoInProper : 2 ∈ exponent.properDivisors :=
      Nat.mem_properDivisors.mpr ⟨swap.1, by omega⟩
    calc
      cyclotomicAtTwo 6 *
          ∏ divisor ∈ exponent.properDivisors.erase 2,
            cyclotomicAtTwo divisor =
        cyclotomicAtTwo 2 *
          ∏ divisor ∈ exponent.properDivisors.erase 2,
            cyclotomicAtTwo divisor := by
          rw [cyclotomicAtTwo_six, cyclotomicAtTwo_two]
      _ = ∏ divisor ∈ exponent.properDivisors,
            cyclotomicAtTwo divisor := by
          rw [← Finset.prod_insert (by simp : 2 ∉ exponent.properDivisors.erase 2),
            Finset.insert_erase twoInProper]
  · have selectedFinset :
        selectedList.toFinset = exponent.properDivisors := by
      ext index
      simp only [selectedList, List.mem_toFinset, List.mem_filter,
        decide_eq_true_eq, mem_descendingIndices, effectiveDivisor, if_neg swap,
        Nat.mem_properDivisors]
      constructor
      · rintro ⟨⟨indexPositive, indexBound⟩, indexDivides⟩
        exact ⟨indexDivides, by omega⟩
      · rintro ⟨indexDivides, indexLess⟩
        have indexPositive : 0 < index :=
          Nat.pos_of_dvd_of_pos indexDivides (by omega)
        exact ⟨by omega, indexDivides⟩
    rw [selectedFinset]

/-- The reverse all-history scan is correct whenever its current residual
is the target cyclotomic value times the not-yet-consumed effective
product.  The only non-separated case is handled explicitly: at even
exponents not divisible by six, index six consumes the unique factor `3`
before index two is reached. -/
theorem scan_descendingValues_eq_cyclotomicAtTwo_of_invariant
    {exponent bound residual : Nat}
    (exponentAtLeastSeven : 7 ≤ exponent)
    (boundLessThanExponent : bound < exponent)
    (residualEquation :
      residual = cyclotomicAtTwo exponent *
        effectiveDivisorProduct exponent bound)
    (residualDivides : residual ∣ 2 ^ exponent - 1) :
    scan (descendingValues bound) residual = cyclotomicAtTwo exponent := by
  induction bound generalizing residual with
  | zero =>
      simpa using residualEquation
  | succ bound inductionHypothesis =>
      let current := bound + 1
      by_cases currentSelected : effectiveDivisor exponent current
      · have productEquation :
            effectiveDivisorProduct exponent current =
              cyclotomicAtTwo current *
                effectiveDivisorProduct exponent bound := by
          simp [current, currentSelected]
        have currentDividesResidual : cyclotomicAtTwo current ∣ residual := by
          refine ⟨cyclotomicAtTwo exponent *
            effectiveDivisorProduct exponent bound, ?_⟩
          rw [residualEquation, productEquation]
          ring
        have removalEquation :
            removeIfDivides residual (cyclotomicAtTwo current) =
              cyclotomicAtTwo exponent *
                effectiveDivisorProduct exponent bound := by
          rw [removeIfDivides,
            if_pos (Nat.dvd_iff_mod_eq_zero.mp currentDividesResidual)]
          calc
            residual / cyclotomicAtTwo current =
                (cyclotomicAtTwo exponent *
                    effectiveDivisorProduct exponent bound) *
                  cyclotomicAtTwo current /
                    cyclotomicAtTwo current := by
              rw [residualEquation, productEquation]
              congr 1
              ring
            _ = cyclotomicAtTwo exponent *
                effectiveDivisorProduct exponent bound :=
              Nat.mul_div_left _ (cyclotomicAtTwo_positive current)
        rw [descendingValues_succ, scan_cons, removalEquation]
        apply inductionHypothesis
        · omega
        · rfl
        · have removalDivides :=
            removeIfDivides_dvd_candidate residual
              (cyclotomicAtTwo current)
          rw [removalEquation] at removalDivides
          exact dvd_trans removalDivides residualDivides
      · have tailEquation :
            residual = cyclotomicAtTwo exponent *
              effectiveDivisorProduct exponent bound := by
          simpa [current, currentSelected] using residualEquation
        have removalEquation :
            removeIfDivides residual (cyclotomicAtTwo current) = residual := by
          by_cases currentIsSix : current = 6
          · have sixNotSelected : ¬effectiveDivisor exponent 6 := by
              simpa [current, currentIsSix] using currentSelected
            have twoDoesNotDivide : ¬2 ∣ exponent :=
              two_not_dvd_of_not_effectiveDivisor_six sixNotSelected
            have threeDoesNotDivideCandidate : ¬3 ∣ 2 ^ exponent - 1 :=
              (three_dvd_two_pow_sub_one_iff exponent).not.mpr
                twoDoesNotDivide
            have threeDoesNotDivideResidual : ¬3 ∣ residual := by
              intro dividesResidual
              exact threeDoesNotDivideCandidate
                (dvd_trans dividesResidual residualDivides)
            have unchangedThree : removeIfDivides residual 3 = residual := by
              simp [removeIfDivides,
                Nat.dvd_iff_mod_eq_zero.not.mp threeDoesNotDivideResidual]
            simpa [current, currentIsSix, cyclotomicAtTwo_six] using
              unchangedThree
          · by_cases currentIsTwo : current = 2
            · have twoNotSelected : ¬effectiveDivisor exponent 2 := by
                simpa [current, currentIsTwo] using currentSelected
              by_cases twoDivides : 2 ∣ exponent
              · have sixDoesNotDivide : ¬6 ∣ exponent :=
                  six_not_dvd_of_two_dvd_not_effectiveDivisor_two
                    twoDivides twoNotSelected
                have boundIsOne : bound = 1 := by omega
                subst bound
                have residualIsTarget :
                    residual = cyclotomicAtTwo exponent := by
                  simpa using tailEquation
                have threeDoesNotDivideTarget :
                    ¬3 ∣ cyclotomicAtTwo exponent := by
                  intro threeDivides
                  have characterization :=
                    (prime_dvd_cyclotomicAtTwo_iff_eq_prime_pow_mul
                      Nat.prime_three (by norm_num : ¬3 ∣ 2)
                      orderOf_two_mod_three (by omega : 0 < exponent)).mp
                      threeDivides
                  rcases characterization with ⟨power, exponentForm⟩
                  cases power with
                  | zero => simp at exponentForm; omega
                  | succ power =>
                      apply sixDoesNotDivide
                      refine ⟨3 ^ power, ?_⟩
                      rw [exponentForm, pow_succ]
                      ring
                have threeDoesNotDivideResidual : ¬3 ∣ residual := by
                  rwa [residualIsTarget]
                have unchangedThree : removeIfDivides residual 3 = residual := by
                  simp [removeIfDivides,
                    Nat.dvd_iff_mod_eq_zero.not.mp
                      threeDoesNotDivideResidual]
                simpa [current, currentIsTwo, cyclotomicAtTwo_two] using
                  unchangedThree
              · have unchanged :=
                  removeIfDivides_eq_self_of_separated_index
                    separatingPrimeAtTwo twoDivides residualDivides
                simpa [current, currentIsTwo, cyclotomicAtTwo_two] using
                  unchanged
            · have currentDoesNotDivideExponent : ¬current ∣ exponent :=
                ((effectiveDivisor_iff_dvd_of_ne_two_ne_six
                  currentIsTwo currentIsSix).not).mp currentSelected
              have currentGreaterThanOne : 1 < current := by
                have currentPositive : 0 < current := by omega
                have currentIsNotOne : current ≠ 1 := by
                  intro currentIsOne
                  have oneNotSelected : ¬effectiveDivisor exponent 1 := by
                    simpa [current, currentIsOne] using currentSelected
                  exact oneNotSelected (effectiveDivisor_one exponent)
                omega
              rcases exists_separatingPrime_of_index_ne_six
                  currentGreaterThanOne currentIsSix with ⟨witness⟩
              exact removeIfDivides_eq_self_of_separated_index witness
                currentDoesNotDivideExponent residualDivides
        rw [descendingValues_succ, scan_cons, removalEquation]
        exact inductionHypothesis (by omega) tailEquation residualDivides

/-- Scanning the entire reverse history through `n-1` leaves exactly
`Φ_n(2)`.  For `n ≥ 7` this is the primitive-divisor theorem plus the
single order-aware `Φ₆/Φ₂` swap; the finite prefix is kernel computation. -/
theorem scan_descendingValues_eq_cyclotomicAtTwo
    (exponent : Nat) (exponentPositive : 0 < exponent) :
    scan (descendingValues (exponent - 1)) (2 ^ exponent - 1) =
      cyclotomicAtTwo exponent := by
  by_cases exponentAtLeastSeven : 7 ≤ exponent
  · have factorization :=
      prod_cyclotomicAtTwo_eq_two_pow_sub_one exponent exponentPositive
    let properProduct :=
      ∏ divisor ∈ exponent.properDivisors, cyclotomicAtTwo divisor
    have divisorDecomposition :
        (∏ divisor ∈ exponent.divisors, cyclotomicAtTwo divisor) =
          cyclotomicAtTwo exponent * properProduct := by
      rw [← Nat.cons_self_properDivisors exponentPositive.ne']
      simp [properProduct]
    rw [divisorDecomposition] at factorization
    have effectiveProductEquation :
        effectiveDivisorProduct exponent (exponent - 1) = properProduct := by
      exact effectiveDivisorProduct_pred_eq_properDivisorProduct
        exponentAtLeastSeven
    apply scan_descendingValues_eq_cyclotomicAtTwo_of_invariant
      exponentAtLeastSeven (by omega)
    · rw [effectiveProductEquation]
      exact factorization.symm
    · exact dvd_refl _
  · interval_cases exponent <;>
      norm_num [descendingValues, descendingIndices, scan,
        removeIfDivides, cyclotomicAtTwo_one, cyclotomicAtTwo_two,
        cyclotomicAtTwo_three, cyclotomicAtTwo_four,
        cyclotomicAtTwo_five, cyclotomicAtTwo_six]

theorem scan_pos : ∀ {divisors : List Nat} {candidate : Nat},
    0 < candidate → (∀ divisor ∈ divisors, 0 < divisor) →
      0 < scan divisors candidate := by
  intro divisors
  induction divisors with
  | nil =>
      intro candidate candidatePositive divisorsPositive
      exact candidatePositive
  | cons divisor divisors inductionHypothesis =>
      intro candidate candidatePositive divisorsPositive
      apply inductionHypothesis
      · exact removeIfDivides_pos candidatePositive
          (divisorsPositive divisor (by simp))
      · intro value membership
        exact divisorsPositive value (by simp [membership])

/-- A nonempty reverse history of positive sieve values. -/
structure State where
  history : List Nat
  nonempty : history ≠ []
  positive : ∀ value ∈ history, 0 < value

/-- Add the sieved value of `2^exponent - 1` to the history. -/
def State.advance (state : State) (exponent : Nat) (exponentPositive : 0 < exponent) :
    State := by
  let candidate := 2 ^ exponent - 1
  have candidatePositive : 0 < candidate := by
    have powerLarge : 1 < 2 ^ exponent := one_lt_pow₀ (by omega) exponentPositive.ne'
    omega
  let next := scan state.history candidate
  have nextPositive : 0 < next :=
    scan_pos candidatePositive state.positive
  exact
    { history := next :: state.history
      nonempty := by simp
      positive := by
        intro value membership
        simp only [List.mem_cons] at membership
        rcases membership with rfl | old
        · exact nextPositive
        · exact state.positive value old }

/-- History through `step`, where step zero contains `Φ1(2) = 1`. -/
def build : Nat → State
  | 0 =>
      { history := [1]
        nonempty := by simp
        positive := by simp }
  | step + 1 => (build step).advance (step + 2) (by omega)

/-- The newest sieve value at a build step. -/
def value (step : Nat) : Nat :=
  (build step).history.head (build step).nonempty

@[simp] theorem build_zero_history : (build 0).history = [1] := rfl

@[simp] theorem value_zero : value 0 = 1 := rfl

theorem build_succ_history (step : Nat) :
    (build (step + 1)).history =
      scan (build step).history (2 ^ (step + 2) - 1) ::
        (build step).history := by
  rfl

@[simp] theorem build_history_length (step : Nat) :
    (build step).history.length = step + 1 := by
  induction step with
  | zero => rfl
  | succ step inductionHypothesis =>
      rw [build_succ_history]
      simp [inductionHypothesis]

theorem build_history_head (step : Nat) :
    (build step).history = value step :: (build step).history.tail := by
  have nonempty := (build step).nonempty
  unfold value
  exact (List.cons_head_tail nonempty).symm

theorem value_succ (step : Nat) :
    value (step + 1) =
      scan (build step).history (2 ^ (step + 2) - 1) := by
  rfl

theorem value_positive (step : Nat) : 0 < value step := by
  exact (build step).positive _ (List.head_mem (build step).nonempty)

/-- The operational state is exactly the reverse chronological list of
cyclotomic values. -/
theorem build_history_eq_descendingValues (step : Nat) :
    (build step).history = descendingValues (step + 1) := by
  induction step with
  | zero => simp [descendingValues, descendingIndices]
  | succ step inductionHypothesis =>
      have scanEquation :
          scan (descendingValues (step + 1)) (2 ^ (step + 2) - 1) =
            cyclotomicAtTwo (step + 2) := by
        simpa using
          scan_descendingValues_eq_cyclotomicAtTwo (step + 2) (by omega)
      calc
        (build (step + 1)).history =
            scan (descendingValues (step + 1)) (2 ^ (step + 2) - 1) ::
              descendingValues (step + 1) := by
          rw [build_succ_history, inductionHypothesis]
        _ = cyclotomicAtTwo (step + 2) ::
              descendingValues (step + 1) := by rw [scanEquation]
        _ = descendingValues (step + 1 + 1) :=
          (descendingValues_succ (step + 1)).symm

/-- Every value produced by the all-history sieve is the corresponding
cyclotomic evaluation at two. -/
theorem value_eq_cyclotomicAtTwo (step : Nat) :
    value step = cyclotomicAtTwo (step + 1) := by
  have shape :
      value step :: (build step).history.tail =
        cyclotomicAtTwo (step + 1) :: descendingValues step := by
    calc
      value step :: (build step).history.tail = (build step).history :=
        (build_history_head step).symm
      _ = descendingValues (step + 1) :=
        build_history_eq_descendingValues step
      _ = cyclotomicAtTwo (step + 1) :: descendingValues step :=
        descendingValues_succ step
  exact (List.cons.inj shape).1

theorem two_pow_sub_one_step (exponent : Nat) :
    1 + ((2 ^ (exponent + 1) - 1) + (2 ^ (exponent + 1) - 1)) =
      2 ^ (exponent + 2) - 1 := by
  rw [show exponent + 2 = (exponent + 1) + 1 by omega, pow_succ]
  have powerPositive : 1 ≤ 2 ^ (exponent + 1) :=
    Nat.one_le_pow (exponent + 1) 2 (by omega)
  omega

/-- Number of outer updates made by the reported program at input `position`. -/
def outerIterations (position : Nat) : Nat := (position + 2) * position

/-- The sieve index reached from a zero-based OEIS position. -/
def targetIndex (position : Nat) : Nat := (position + 1) ^ 2

theorem outerIterations_add_one (position : Nat) :
    outerIterations position + 1 = targetIndex position := by
  simp [outerIterations, targetIndex]
  ring

theorem value_outerIterations_eq_target (position : Nat) :
    value (outerIterations position) =
      cyclotomicAtTwo (targetIndex position) := by
  rw [value_eq_cyclotomicAtTwo, outerIterations_add_one]

/-- Expanding a cyclotomic polynomial by factors already supported in its
index multiplies that index.  This packages repeated applications of the
prime-factor expansion theorem into a reusable form. -/
theorem expand_cyclotomic_of_prime_dvd
    (R : Type*) [CommRing R] {index factor : Nat}
    (factorNonzero : factor ≠ 0)
    (primeSupport : ∀ prime, prime.Prime → prime ∣ factor → prime ∣ index) :
    Polynomial.expand R factor (Polynomial.cyclotomic index R) =
      Polynomial.cyclotomic (index * factor) R := by
  induction factor using induction_on_primes with
  | zero => contradiction
  | one => simp
  | prime_mul prime factor primeIsPrime inductionHypothesis =>
      have factorNonzero' : factor ≠ 0 := by
        intro factorZero
        simp [factorZero] at factorNonzero
      have factorPrimeSupport :
          ∀ divisor, divisor.Prime → divisor ∣ factor → divisor ∣ index := by
        intro divisor divisorIsPrime divisorDivides
        exact primeSupport divisor divisorIsPrime
          (dvd_trans divisorDivides (dvd_mul_left factor prime))
      rw [Polynomial.expand_mul,
        inductionHypothesis factorNonzero' factorPrimeSupport,
        Polynomial.cyclotomic_expand_eq_cyclotomic primeIsPrime]
      · congr 1
        ac_rfl
      · exact dvd_mul_of_dvd_left
          (primeSupport prime primeIsPrime (dvd_mul_right prime factor)) factor

/-- Substituting `X^n` into the `n`-th cyclotomic polynomial gives the
`n^2`-th cyclotomic polynomial. -/
theorem expand_cyclotomic_self (R : Type*) [CommRing R]
    (index : Nat) (indexPositive : 0 < index) :
    Polynomial.expand R index (Polynomial.cyclotomic index R) =
      Polynomial.cyclotomic (index ^ 2) R := by
  rw [expand_cyclotomic_of_prime_dvd R indexPositive.ne']
  · congr 1
    ring
  · intro prime primeIsPrime primeDivides
    exact primeDivides

/-- The evaluation identity behind OEIS A070526: evaluating `Φ_n` at
`2^n` equals evaluating `Φ_(n^2)` at `2`. -/
theorem eval_cyclotomic_pow_self_eq_square (index : Nat)
    (indexPositive : 0 < index) :
    (Polynomial.cyclotomic index Int).eval ((2 : Int) ^ index) =
      (Polynomial.cyclotomic (index ^ 2) Int).eval 2 := by
  rw [← expand_cyclotomic_self Int index indexPositive]
  exact (Polynomial.expand_eval index (Polynomial.cyclotomic index Int) 2).symm

/-- The defining cyclotomic-polynomial value used by OEIS A070526. -/
noncomputable def cyclotomicValue (index : Nat) : Int :=
  (Polynomial.cyclotomic index Int).eval ((2 : Int) ^ index)

theorem cyclotomicValue_eq_square_eval (index : Nat)
    (indexPositive : 0 < index) :
    cyclotomicValue index =
      (Polynomial.cyclotomic (index ^ 2) Int).eval 2 := by
  simpa [cyclotomicValue] using
    eval_cyclotomic_pow_self_eq_square index indexPositive

/-- Re-express the sequence value at zero-based `position` as the value of
the cyclotomic polynomial reached by the reported program's outer loop. -/
theorem cyclotomicValue_eq_target_eval (position : Nat) :
    cyclotomicValue (position + 1) =
      (Polynomial.cyclotomic (targetIndex position) Int).eval 2 := by
  simpa [targetIndex] using
    cyclotomicValue_eq_square_eval (position + 1) (by omega)

theorem cyclotomicValue_positive (index : Nat) : 0 < cyclotomicValue index := by
  cases index with
  | zero => simp [cyclotomicValue]
  | succ index =>
      unfold cyclotomicValue
      exact Polynomial.cyclotomic_pos' (index + 1)
        (one_lt_pow₀ (by norm_num : (1 : Int) < 2) (by omega))

/-- Source coordinates for OEIS A070526 in the pinned snapshot. -/
def sourceA070526 : EntrySource where
  oeisId := "A070526"
  snapshotRevision := "a6e0f22854cc1c307da428e9d6295093781df7fa"
  entrySha256 := "0b45ada534de282a9c05a52f4ed52a37a8b263a3c6b0c88d6902c5a72639966d"
  offset := 1

/-- OEIS A070526: the `n`-th cyclotomic polynomial evaluated at `2^n`. -/
noncomputable def specA070526 : SequenceSpec where
  offset := 1
  Domain := fun index => 1 ≤ index
  value := fun index => cyclotomicValue index.toNat

noncomputable def formalizationA070526 : Formalization where
  source := sourceA070526
  spec := specA070526
  offsetMatches := rfl

#print axioms expand_cyclotomic_of_prime_dvd
#print axioms expand_cyclotomic_self
#print axioms eval_cyclotomic_pow_self_eq_square
#print axioms cyclotomicValue_eq_target_eval
#print axioms prime_dvd_cyclotomicAtTwo_iff_eq_prime_pow_mul
#print axioms factorization_two_pow_mul_sub_one
#print axioms intrinsic_prime_unique
#print axioms intrinsic_prime_factorization_eq_one
#print axioms prime_lt_cyclotomicAtTwo_of_intrinsic_not_exception
#print axioms exists_separatingPrime_of_index_ne_six
#print axioms scan_descendingValues_eq_cyclotomicAtTwo_of_invariant
#print axioms scan_descendingValues_eq_cyclotomicAtTwo
#print axioms build_history_eq_descendingValues
#print axioms value_eq_cyclotomicAtTwo

end Mettapedia.Sequences.OEIS.CyclotomicSieve
