import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Instances.TemporalEquilibrium
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# Finite root-of-unity phase readout

This module closes the algebraic bridge between finite phase sampling and the
coefficient alias classes used to audit holomorphic equilibrium-propagation
claims.  It does not formalize the continuous contour theorem or the implicit
fixed-point hypotheses of holomorphic equilibrium propagation.

The main theorem is field-generic.  An `N`-point readout against a primitive
`N`-th root of unity returns exactly the sum of coefficients in the requested
residue class, multiplied by `N`.  Normalization recovers the requested
coefficient only under both a no-alias degree bound and a nonzero
characteristic condition for `N`.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Instances

open Finset Polynomial

/-- Shifting a degree by `sampleCount - residue` makes divisibility by the
sample count equivalent to membership in the requested residue class. -/
theorem dvd_phaseShift_add_iff_mod_eq
    (sampleCount residue degree : ℕ) (residue_lt : residue < sampleCount) :
    sampleCount ∣ (sampleCount - residue) + degree ↔
      degree % sampleCount = residue := by
  have residue_le : residue ≤ sampleCount := Nat.le_of_lt residue_lt
  have shifted_residue : sampleCount - residue + residue = sampleCount :=
    Nat.sub_add_cancel residue_le
  have reference_zero :
      sampleCount - residue + residue ≡ 0 [MOD sampleCount] := by
    rw [shifted_residue]
    exact Nat.modulus_modEq_zero
  constructor
  · intro shifted_dvd
    have shifted_zero :
        sampleCount - residue + degree ≡ 0 [MOD sampleCount] :=
      shifted_dvd.modEq_zero_nat
    have degree_modEq : degree ≡ residue [MOD sampleCount] :=
      Nat.ModEq.add_left_cancel' (sampleCount - residue)
        (shifted_zero.trans reference_zero.symm)
    simpa [Nat.ModEq, Nat.mod_eq_of_lt residue_lt] using degree_modEq
  · intro degree_mod
    have degree_modEq : degree ≡ residue [MOD sampleCount] := by
      simpa [Nat.ModEq, Nat.mod_eq_of_lt residue_lt] using degree_mod
    have shifted_zero :
        sampleCount - residue + degree ≡ 0 [MOD sampleCount] :=
      (degree_modEq.add_left (sampleCount - residue)).trans reference_zero
    exact Nat.modEq_zero_iff_dvd.mp shifted_zero

/-- Orthogonality of the powers of a primitive root, stated without dividing
by the sample count. -/
theorem primitiveRoot_geometric_sum
    {K : Type*} [Field K] {ζ : K} {sampleCount : ℕ}
    (primitive : IsPrimitiveRoot ζ sampleCount) (degree : ℕ) :
    ∑ phase ∈ Finset.range sampleCount, (ζ ^ degree) ^ phase =
      if sampleCount ∣ degree then (sampleCount : K) else 0 := by
  by_cases divides : sampleCount ∣ degree
  · have power_eq : ζ ^ degree = 1 :=
      (primitive.pow_eq_one_iff_dvd degree).mpr divides
    simp [divides, power_eq]
  · have power_ne : ζ ^ degree ≠ 1 :=
      mt (primitive.pow_eq_one_iff_dvd degree).mp divides
    have cycle_eq : (ζ ^ degree) ^ sampleCount = 1 := by
      rw [← pow_mul, Nat.mul_comm, pow_mul, primitive.pow_eq_one, one_pow]
    have product_zero :
        (ζ ^ degree - 1) *
            (∑ phase ∈ Finset.range sampleCount, (ζ ^ degree) ^ phase) = 0 := by
      rw [mul_geom_sum, cycle_eq, sub_self]
    have sum_zero :
        ∑ phase ∈ Finset.range sampleCount, (ζ ^ degree) ^ phase = 0 :=
      (mul_eq_zero.mp product_zero).resolve_left (sub_ne_zero.mpr power_ne)
    simp [divides, sum_zero]

/-- Unnormalized finite phase readout for a requested coefficient residue. -/
noncomputable def finitePhaseReadout
    {K : Type*} [Field K]
    (ζ : K) (sampleCount residue : ℕ) (response : Polynomial K) : K :=
  ∑ phase ∈ Finset.range sampleCount,
    ζ ^ ((sampleCount - residue) * phase) * response.eval (ζ ^ phase)

/-- A finite root-of-unity readout is exactly the requested coefficient alias
class, scaled by the phase count.  This is the discrete algebraic identity;
it does not invoke a continuous contour or an equilibrium theorem. -/
theorem finitePhaseReadout_eq_cast_mul_phaseAliasCoefficient
    {K : Type*} [Field K] {ζ : K} {sampleCount residue : ℕ}
    (response : Polynomial K) (primitive : IsPrimitiveRoot ζ sampleCount)
    (residue_lt : residue < sampleCount) :
    finitePhaseReadout ζ sampleCount residue response =
      (sampleCount : K) * phaseAliasCoefficient sampleCount residue response := by
  unfold finitePhaseReadout phaseAliasCoefficient
  simp_rw [Polynomial.eval_eq_sum, Polynomial.sum_def]
  calc
    (∑ phase ∈ Finset.range sampleCount,
        ζ ^ ((sampleCount - residue) * phase) *
          ∑ degree ∈ response.support,
            response.coeff degree * (ζ ^ phase) ^ degree) =
        ∑ phase ∈ Finset.range sampleCount,
          ∑ degree ∈ response.support,
            ζ ^ ((sampleCount - residue) * phase) *
              (response.coeff degree * (ζ ^ phase) ^ degree) := by
      apply Finset.sum_congr rfl
      intro phase _
      rw [Finset.mul_sum]
    _ = ∑ degree ∈ response.support,
          ∑ phase ∈ Finset.range sampleCount,
            ζ ^ ((sampleCount - residue) * phase) *
              (response.coeff degree * (ζ ^ phase) ^ degree) := by
      rw [Finset.sum_comm]
    _ = ∑ degree ∈ response.support,
          response.coeff degree *
            ∑ phase ∈ Finset.range sampleCount,
              (ζ ^ ((sampleCount - residue) + degree)) ^ phase := by
      apply Finset.sum_congr rfl
      intro degree _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro phase _
      simp only [pow_add, pow_mul]
      ring
    _ = ∑ degree ∈ response.support,
          response.coeff degree *
            (if sampleCount ∣ (sampleCount - residue) + degree
              then (sampleCount : K) else 0) := by
      apply Finset.sum_congr rfl
      intro degree _
      rw [primitiveRoot_geometric_sum primitive]
    _ = (sampleCount : K) *
          ∑ degree ∈ response.support.filter
            (fun degree => sampleCount ∣ (sampleCount - residue) + degree),
              response.coeff degree := by
      rw [Finset.mul_sum, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro degree _
      by_cases divides : sampleCount ∣ (sampleCount - residue) + degree
      · simp [divides, mul_comm]
      · simp [divides]
    _ = (sampleCount : K) *
          ∑ degree ∈ response.support.filter
            (fun degree => degree % sampleCount = residue), response.coeff degree := by
      have filter_eq :
          response.support.filter
              (fun degree => sampleCount ∣ (sampleCount - residue) + degree) =
            response.support.filter (fun degree => degree % sampleCount = residue) := by
        ext degree
        simp only [Finset.mem_filter]
        rw [dvd_phaseShift_add_iff_mod_eq sampleCount residue degree residue_lt]
      rw [filter_eq]

/-- Normalized phase readout.  The explicit inverse records the characteristic
condition needed to divide by the number of phases. -/
noncomputable def normalizedFinitePhaseReadout
    {K : Type*} [Field K]
    (ζ : K) (sampleCount residue : ℕ) (response : Polynomial K) : K :=
  (sampleCount : K)⁻¹ * finitePhaseReadout ζ sampleCount residue response

/-- With enough phases to avoid aliasing and a nonzero phase-count scalar, the
normalized finite readout recovers the requested coefficient exactly. -/
theorem normalizedFinitePhaseReadout_eq_coeff_of_natDegree_lt
    {K : Type*} [Field K] {ζ : K} {sampleCount residue : ℕ}
    (response : Polynomial K) (primitive : IsPrimitiveRoot ζ sampleCount)
    (residue_lt : residue < sampleCount)
    (degree_lt : response.natDegree < sampleCount)
    (sampleCount_ne : (sampleCount : K) ≠ 0) :
    normalizedFinitePhaseReadout ζ sampleCount residue response =
      response.coeff residue := by
  rw [normalizedFinitePhaseReadout,
    finitePhaseReadout_eq_cast_mul_phaseAliasCoefficient response primitive residue_lt,
    phaseAliasCoefficient_eq_coeff_of_natDegree_lt response sampleCount residue degree_lt
      residue_lt]
  field_simp

/-! ## Concrete complex positive and negative fixtures -/

noncomputable def complexPrimitiveCubeRoot : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I / 3)

noncomputable def complexQuadraticPhaseResponse : Polynomial ℂ :=
  Polynomial.C 7 + Polynomial.C 3 * Polynomial.X + Polynomial.C 5 * Polynomial.X ^ 2

noncomputable def complexAliasedQuarticPhaseResponse : Polynomial ℂ :=
  Polynomial.C 3 * Polynomial.X + Polynomial.C 11 * Polynomial.X ^ 4

theorem complexPrimitiveCubeRoot_isPrimitive :
    IsPrimitiveRoot complexPrimitiveCubeRoot 3 := by
  exact Complex.isPrimitiveRoot_exp 3 (by norm_num)

theorem complexAliasedQuarticPhaseResponse_support :
    complexAliasedQuarticPhaseResponse.support = {1, 4} := by
  ext degree
  by_cases degree_one : degree = 1
  · subst degree
    norm_num [complexAliasedQuarticPhaseResponse, Polynomial.mem_support_iff]
  · by_cases degree_four : degree = 4
    · subst degree
      norm_num [complexAliasedQuarticPhaseResponse, Polynomial.mem_support_iff]
    · simp [complexAliasedQuarticPhaseResponse, Polynomial.mem_support_iff,
        Polynomial.coeff_X_of_ne_one degree_one, degree_one, degree_four]

/-- Three normalized complex phases exactly recover the linear coefficient of
a quadratic response. -/
theorem complex_threePhase_quadratic_recovers_linear_coefficient :
    normalizedFinitePhaseReadout complexPrimitiveCubeRoot 3 1
      complexQuadraticPhaseResponse = 3 := by
  have degree_lt : complexQuadraticPhaseResponse.natDegree < 3 := by
    unfold complexQuadraticPhaseResponse
    compute_degree
    all_goals norm_num
  rw [normalizedFinitePhaseReadout_eq_coeff_of_natDegree_lt
    complexQuadraticPhaseResponse complexPrimitiveCubeRoot_isPrimitive (by norm_num)
      degree_lt (by norm_num)]
  norm_num [complexQuadraticPhaseResponse]

/-- The same three-phase readout of a quartic response returns `3 + 11`, not
the degree-one coefficient `3`, because degree four aliases with degree one. -/
theorem complex_threePhase_quartic_returns_aliased_sum :
    normalizedFinitePhaseReadout complexPrimitiveCubeRoot 3 1
      complexAliasedQuarticPhaseResponse = 14 ∧
    complexAliasedQuarticPhaseResponse.coeff 1 = 3 := by
  unfold normalizedFinitePhaseReadout
  rw [finitePhaseReadout_eq_cast_mul_phaseAliasCoefficient
    complexAliasedQuarticPhaseResponse complexPrimitiveCubeRoot_isPrimitive (by norm_num)]
  rw [show phaseAliasCoefficient 3 1 complexAliasedQuarticPhaseResponse = 14 by
    unfold phaseAliasCoefficient
    rw [complexAliasedQuarticPhaseResponse_support]
    have filtered_eq :
        ({1, 4} : Finset ℕ).filter (fun degree => degree % 3 = 1) = {1, 4} := by
      decide
    rw [filtered_eq]
    norm_num [complexAliasedQuarticPhaseResponse, Polynomial.coeff_X]]
  norm_num [complexAliasedQuarticPhaseResponse]

#print axioms dvd_phaseShift_add_iff_mod_eq
#print axioms primitiveRoot_geometric_sum
#print axioms finitePhaseReadout_eq_cast_mul_phaseAliasCoefficient
#print axioms normalizedFinitePhaseReadout_eq_coeff_of_natDegree_lt
#print axioms complex_threePhase_quadratic_recovers_linear_coefficient
#print axioms complex_threePhase_quartic_returns_aliased_sum

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Instances
