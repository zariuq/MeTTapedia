import Mettapedia.Computability.KolmogorovComplexity.KraftChaitinEffective

/-!
# Dyadic threshold requests for discrete coding

This file isolates the finite integer ledger behind the discrete coding
theorem.  A numerator `a` at denominator level `D` crosses threshold `ell`
when `2^(D-ell) ≤ a`.  Crossing a threshold issues a code-length request.

The crossed thresholds form a geometric tail.  Their total binary mass is at
most twice the numerator.  Adding one reserve bit to every requested length
therefore places a dyadic subprobability profile in at most half of the Kraft
space.  The reserve is useful when a finite profile is embedded in a total
effective request stream.

All statements use `Nat` capacities; no real-valued limits are needed.
-/

namespace KolmogorovComplexity

namespace KraftChaitin

/-- Integer capacity consumed by a finite list of requested lengths at a
common denominator level. -/
def lengthMass (level : Nat) (lengths : List Nat) : Nat :=
  (lengths.map fun length => 2 ^ (level - length)).sum

/-- The usual finite Kraft mass, kept in exact rational arithmetic. -/
def rationalLengthMass (lengths : List Nat) : ℚ :=
  (lengths.map fun length => (1 : ℚ) / (2 : ℚ) ^ length).sum

/-- The rational length mass of a finite prefix-free code is at most one.
This is the list-valued bridge between the real-valued finite Kraft theorem
and the exact rational ledger used by the executable allocator. -/
theorem rationalLengthMass_map_length_le_one
    (codes : List BinString)
    (hnodup : codes.Nodup)
    (hprefixFree : PrefixFree (↑codes.toFinset : Set BinString)) :
    rationalLengthMass (codes.map List.length) ≤ 1 := by
  classical
  have hkraft := kraft_inequality codes.toFinset hprefixFree
  have hreal :
      (((rationalLengthMass (codes.map List.length) : ℚ) : ℝ)) =
        kraftSum codes.toFinset := by
    unfold rationalLengthMass
    rw [List.map_map]
    change
      (((codes.map fun code => (1 : ℚ) / (2 : ℚ) ^ code.length).sum : ℚ) : ℝ) =
        codes.toFinset.sum fun code => (2 : ℝ) ^ (-(code.length : ℤ))
    rw [← List.sum_toFinset
      (fun code => (1 : ℚ) / (2 : ℚ) ^ code.length) hnodup]
    rw [Rat.cast_sum]
    apply Finset.sum_congr rfl
    intro code _hcode
    simp [zpow_neg, zpow_natCast]
  rw [← hreal] at hkraft
  exact_mod_cast hkraft

theorem pow_sub_div_pow_eq_inv_pow {length level : Nat}
    (h : length ≤ level) :
    (2 : ℚ) ^ (level - length) / (2 : ℚ) ^ level =
      (1 : ℚ) / (2 : ℚ) ^ length := by
  have hlevel : level - length + length = level := Nat.sub_add_cancel h
  have hpow : (2 : ℚ) ^ level =
      (2 : ℚ) ^ (level - length) * (2 : ℚ) ^ length := by
    rw [← pow_add, hlevel]
  rw [hpow]
  field_simp

/-- Integer common-denominator mass divided by its capacity is exactly the
rational Kraft mass. -/
theorem lengthMass_div_pow_eq_rationalLengthMass
    {level : Nat} {lengths : List Nat}
    (h : ∀ length ∈ lengths, length ≤ level) :
    (lengthMass level lengths : ℚ) / (2 : ℚ) ^ level =
      rationalLengthMass lengths := by
  induction lengths with
  | nil => simp [lengthMass, rationalLengthMass]
  | cons length lengths ih =>
      have hhead : length ≤ level := h length List.mem_cons_self
      have htail : ∀ item ∈ lengths, item ≤ level := by
        intro item hitem
        exact h item (List.mem_cons_of_mem _ hitem)
      have htailEq :
          (((lengths.map fun item => (2 : Nat) ^ (level - item)).sum : Nat) : ℚ) /
              (2 : ℚ) ^ level =
            (lengths.map fun item => (1 : ℚ) / (2 : ℚ) ^ item).sum := by
        simpa [lengthMass, rationalLengthMass] using ih htail
      simp only [lengthMass, rationalLengthMass, List.map_cons, List.sum_cons,
        Nat.cast_add]
      norm_num only [Nat.cast_pow, Nat.cast_ofNat]
      rw [add_div, pow_sub_div_pow_eq_inv_pow hhead, htailEq]

/-- A rational Kraft bound on every finite prefix implies the executable
integer budget expected by the online allocator. -/
theorem kraftBudget_of_rational
    {Value : Type*} {requests : BinString → Nat → Request Value}
    (h : ∀ condition count,
      rationalLengthMass (requestedLengthsUpTo requests condition count) ≤ 1) :
    KraftBudget requests := by
  intro condition count level hlengths
  have hratio :
      (lengthMass level (requestedLengthsUpTo requests condition count) : ℚ) /
          (2 : ℚ) ^ level ≤ 1 := by
    rw [lengthMass_div_pow_eq_rationalLengthMass hlengths]
    exact h condition count
  have hden : 0 < (2 : ℚ) ^ level := by positivity
  have hcast :
      (lengthMass level (requestedLengthsUpTo requests condition count) : ℚ) ≤
        (2 : ℚ) ^ level := (div_le_one hden).mp hratio
  exact_mod_cast hcast

/-- Threshold crossings for a numerator at denominator level `D`.  The
unshifted request for threshold `ell` has length `ell + 1`. -/
def thresholdLengths : Nat → Nat → List Nat
  | 0, numerator => if 1 ≤ numerator then [1] else []
  | level + 1, numerator =>
      (if 2 ^ (level + 1) ≤ numerator then [1] else []) ++
        (thresholdLengths level numerator).map Nat.succ

/-- Add one reserve bit to every threshold request. -/
def codingLengths (level numerator : Nat) : List Nat :=
  (thresholdLengths level numerator).map Nat.succ

/-- Concatenate the coding requests for a finite dyadic numerator profile. -/
def batchCodingLengths (level : Nat) (numerators : List Nat) : List Nat :=
  numerators.flatMap (codingLengths level)

/-- A finite numerator profile is a dyadic subprobability profile. -/
def DyadicNumeratorBudget (level : Nat) (numerators : List Nat) : Prop :=
  numerators.sum ≤ 2 ^ level

/-- Crossing threshold `ell` contributes its unshifted request length
`ell + 1`. -/
theorem thresholdLength_mem {level threshold numerator : Nat}
    (hthreshold : threshold ≤ level)
    (hcross : 2 ^ (level - threshold) ≤ numerator) :
    threshold + 1 ∈ thresholdLengths level numerator := by
  induction level generalizing threshold with
  | zero =>
      have hzero : threshold = 0 := by omega
      subst threshold
      simpa [thresholdLengths] using hcross
  | succ level ih =>
      cases threshold with
      | zero =>
          have hcross' : 2 ^ (level + 1) ≤ numerator := by
            simpa using hcross
          simp only [thresholdLengths, List.mem_append]
          exact Or.inl (by simp [hcross'])
      | succ threshold =>
          have hthreshold' : threshold ≤ level := by omega
          have hcross' : 2 ^ (level - threshold) ≤ numerator := by
            simpa only [Nat.succ_sub_succ_eq_sub] using hcross
          have hmem := ih hthreshold' hcross'
          simp only [thresholdLengths, List.mem_append, List.mem_map]
          exact Or.inr ⟨threshold + 1, hmem, by omega⟩

/-- After the reserve-bit shift, a threshold crossing contributes a request
of length `ell + 2`. -/
theorem codingLength_mem {level threshold numerator : Nat}
    (hthreshold : threshold ≤ level)
    (hcross : 2 ^ (level - threshold) ≤ numerator) :
    threshold + 2 ∈ codingLengths level numerator := by
  simp only [codingLengths, List.mem_map]
  exact ⟨threshold + 1, thresholdLength_mem hthreshold hcross, by omega⟩

theorem lengthMass_map_succ (level : Nat) (lengths : List Nat) :
    lengthMass (level + 1) (lengths.map Nat.succ) =
      lengthMass level lengths := by
  induction lengths with
  | nil => rfl
  | cons length lengths ih =>
      simp only [List.map_cons, lengthMass, List.sum_cons] at ih ⊢
      have hsub : level + 1 - (length + 1) = level - length := by omega
      rw [hsub, ih]

theorem lengthMass_append (level : Nat) (left right : List Nat) :
    lengthMass level (left ++ right) =
      lengthMass level left + lengthMass level right := by
  simp [lengthMass]

theorem thresholdLengths_mass_succ (level numerator : Nat) :
    lengthMass (level + 2) (thresholdLengths (level + 1) numerator) =
      (if 2 ^ (level + 1) ≤ numerator then 2 ^ (level + 1) else 0) +
        lengthMass (level + 1) (thresholdLengths level numerator) := by
  change
    lengthMass (level + 2)
        ((if 2 ^ (level + 1) ≤ numerator then [1] else []) ++
          (thresholdLengths level numerator).map Nat.succ) = _
  rw [lengthMass_append, lengthMass_map_succ]
  by_cases h : 2 ^ (level + 1) ≤ numerator
  · simp [h, lengthMass]
  · simp [h, lengthMass]

/-- Threshold requests always occupy strictly less than their common Kraft
capacity.  This is the finite geometric-tail estimate. -/
theorem thresholdLengths_mass_lt_capacity (level numerator : Nat) :
    lengthMass (level + 1) (thresholdLengths level numerator) <
      2 ^ (level + 1) := by
  induction level with
  | zero =>
      by_cases h : 1 ≤ numerator <;> simp [thresholdLengths, lengthMass, h]
  | succ level ih =>
      rw [thresholdLengths_mass_succ]
      by_cases h : 2 ^ (level + 1) ≤ numerator
      · simp only [if_pos h]
        rw [pow_succ]
        omega
      · simp only [if_neg h]
        rw [pow_succ]
        have hpow : 0 < 2 ^ (level + 1) := by positivity
        omega

/-- The geometric threshold tail consumes at most twice its numerator. -/
theorem thresholdLengths_mass_le_twice (level numerator : Nat) :
    lengthMass (level + 1) (thresholdLengths level numerator) ≤
      2 * numerator := by
  induction level with
  | zero =>
      by_cases h : 1 ≤ numerator
      · simp [thresholdLengths, lengthMass, h]
        omega
      · simp [thresholdLengths, lengthMass, h]
  | succ level ih =>
      rw [thresholdLengths_mass_succ]
      by_cases h : 2 ^ (level + 1) ≤ numerator
      · simp only [if_pos h]
        have htail := thresholdLengths_mass_lt_capacity level numerator
        omega
      · simp only [if_neg h, Nat.zero_add]
        exact ih

/-- The reserve-bit presentation has the same integer mass one level higher. -/
theorem codingLengths_mass (level numerator : Nat) :
    lengthMass (level + 2) (codingLengths level numerator) =
      lengthMass (level + 1) (thresholdLengths level numerator) := by
  exact lengthMass_map_succ (level + 1) _

theorem codingLengths_mass_le_twice (level numerator : Nat) :
    lengthMass (level + 2) (codingLengths level numerator) ≤
      2 * numerator := by
  rw [codingLengths_mass]
  exact thresholdLengths_mass_le_twice level numerator

theorem thresholdLengths_all_le {level numerator length : Nat}
    (h : length ∈ thresholdLengths level numerator) :
    length ≤ level + 1 := by
  induction level generalizing length with
  | zero =>
      by_cases hnum : 1 ≤ numerator
      · simp [thresholdLengths, hnum] at h
        omega
      · simp [thresholdLengths, hnum] at h
  | succ level ih =>
      simp only [thresholdLengths, List.mem_append, List.mem_map] at h
      rcases h with hhead | ⟨previous, hprevious, rfl⟩
      · by_cases hnum : 2 ^ (level + 1) ≤ numerator
        · simp [hnum] at hhead
          omega
        · simp [hnum] at hhead
      · have hbound := ih hprevious
        omega

theorem codingLengths_all_le {level numerator length : Nat}
    (h : length ∈ codingLengths level numerator) :
    length ≤ level + 2 := by
  simp only [codingLengths, List.mem_map] at h
  obtain ⟨previous, hprevious, rfl⟩ := h
  have hbound := thresholdLengths_all_le hprevious
  omega

/-- Rational mass of one reserve-bit threshold family. -/
theorem rationalLengthMass_codingLengths_le
    (level numerator : Nat) :
    rationalLengthMass (codingLengths level numerator) ≤
      (numerator : ℚ) / (2 : ℚ) ^ (level + 1) := by
  have hall : ∀ length ∈ codingLengths level numerator,
      length ≤ level + 2 := by
    intro length hlength
    exact codingLengths_all_le hlength
  have hmass := codingLengths_mass_le_twice level numerator
  have hratio := lengthMass_div_pow_eq_rationalLengthMass hall
  rw [← hratio]
  have hden : 0 < (2 : ℚ) ^ (level + 2) := by positivity
  have hcast :
      (lengthMass (level + 2) (codingLengths level numerator) : ℚ) ≤
        2 * (numerator : ℚ) := by exact_mod_cast hmass
  calc
    (lengthMass (level + 2) (codingLengths level numerator) : ℚ) /
          (2 : ℚ) ^ (level + 2)
        ≤ (2 * numerator : ℚ) / (2 : ℚ) ^ (level + 2) :=
          div_le_div_of_nonneg_right hcast hden.le
    _ = (numerator : ℚ) / (2 : ℚ) ^ (level + 1) := by
      rw [show level + 2 = (level + 1) + 1 by omega, pow_succ]
      ring

theorem lengthMass_flatMap {Value : Type*} (level : Nat)
    (values : List Value) (lengths : Value → List Nat) :
    lengthMass level (values.flatMap lengths) =
      (values.map fun value => lengthMass level (lengths value)).sum := by
  induction values with
  | nil => rfl
  | cons value values ih =>
      simp only [List.flatMap_cons, List.map_cons, List.sum_cons]
      rw [lengthMass_append, ih]

/-- A batch of reserve-bit requests consumes at most twice the total
numerator mass. -/
theorem batchCodingLengths_mass_le_twice_sum
    (level : Nat) (numerators : List Nat) :
    lengthMass (level + 2) (batchCodingLengths level numerators) ≤
      2 * numerators.sum := by
  rw [batchCodingLengths, lengthMass_flatMap]
  induction numerators with
  | nil => simp
  | cons numerator numerators ih =>
      simp only [List.map_cons, List.sum_cons]
      have hhead := codingLengths_mass_le_twice level numerator
      omega

/-- A dyadic subprobability profile occupies at most half of the Kraft space
after the reserve-bit shift. -/
theorem batchCodingLengths_mass_le_half_capacity
    {level : Nat} {numerators : List Nat}
    (budget : DyadicNumeratorBudget level numerators) :
    lengthMass (level + 2) (batchCodingLengths level numerators) ≤
      2 ^ (level + 1) := by
  have hmass := batchCodingLengths_mass_le_twice_sum level numerators
  unfold DyadicNumeratorBudget at budget
  rw [pow_succ]
  omega

theorem batchCodingLengths_mass_le_capacity
    {level : Nat} {numerators : List Nat}
    (budget : DyadicNumeratorBudget level numerators) :
    lengthMass (level + 2) (batchCodingLengths level numerators) ≤
      2 ^ (level + 2) := by
  have hhalf := batchCodingLengths_mass_le_half_capacity budget
  have hpow : 2 ^ (level + 1) ≤ 2 ^ (level + 2) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  exact hhalf.trans hpow

/-- Rational form of the reserve-bit half-capacity theorem. -/
theorem rationalLengthMass_batchCodingLengths_le_half
    {level : Nat} {numerators : List Nat}
    (budget : DyadicNumeratorBudget level numerators) :
    rationalLengthMass (batchCodingLengths level numerators) ≤ (1 : ℚ) / 2 := by
  have hall : ∀ length ∈ batchCodingLengths level numerators,
      length ≤ level + 2 := by
    intro length hlength
    simp only [batchCodingLengths, List.mem_flatMap] at hlength
    obtain ⟨numerator, _hnumerator, hlength⟩ := hlength
    exact codingLengths_all_le hlength
  have hratio := lengthMass_div_pow_eq_rationalLengthMass hall
  have hmass := batchCodingLengths_mass_le_half_capacity budget
  rw [← hratio]
  have hden : 0 < (2 : ℚ) ^ (level + 2) := by positivity
  have hcast :
      (lengthMass (level + 2) (batchCodingLengths level numerators) : ℚ) ≤
        (2 : ℚ) ^ (level + 1) := by
    exact_mod_cast hmass
  calc
    (lengthMass (level + 2) (batchCodingLengths level numerators) : ℚ) /
          (2 : ℚ) ^ (level + 2)
        ≤ (2 : ℚ) ^ (level + 1) / (2 : ℚ) ^ (level + 2) :=
          div_le_div_of_nonneg_right hcast hden.le
    _ = (1 : ℚ) / 2 := by
      rw [show level + 2 = (level + 1) + 1 by omega, pow_succ]
      field_simp
      simp [pow_add]
      ring

/-! ## Positive and negative controls -/

example : DyadicNumeratorBudget 2 [2, 1, 1] := by
  norm_num [DyadicNumeratorBudget]

example : batchCodingLengths 2 [2, 1, 1] = [3, 4, 4, 4] := by decide

example : lengthMass 4 (batchCodingLengths 2 [2, 1, 1]) = 5 := by decide

/-- Two full-mass numerators are not a subprobability profile. -/
example : ¬ DyadicNumeratorBudget 2 [4, 4] := by
  norm_num [DyadicNumeratorBudget]

/-- Without the subprobability premise, the reserve-bit half-capacity bound
can fail. -/
example :
    2 ^ (2 + 1) < lengthMass (2 + 2) (batchCodingLengths 2 [4, 4]) := by
  decide

#print axioms thresholdLengths_mass_le_twice
#print axioms codingLength_mem
#print axioms batchCodingLengths_mass_le_half_capacity
#print axioms batchCodingLengths_mass_le_capacity
#print axioms rationalLengthMass_batchCodingLengths_le_half

end KraftChaitin

end KolmogorovComplexity
