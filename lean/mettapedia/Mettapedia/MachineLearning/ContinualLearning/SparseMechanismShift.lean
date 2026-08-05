import Mathlib.Probability.Independence.Basic

/-!
# Sparse mechanism shifts: finite-pair identification rates

Perry, von Kügelgen, and Schölkopf (2022) identify causal graphs by comparing
mechanism changes across disjoint pairs of environments.  Their probabilistic
argument has a reusable event-theoretic spine:

* each false candidate survives one pair only if that pair fails to
  discriminate it;
* independent disjoint pairs turn the survival probability into a product;
* a finite union bound lifts the per-candidate estimate to failure of global
  identification.

This file proves that spine for arbitrary finite candidate and pair types.  It
then exposes the paper's sparse-shift factor

`1 - (1 - rhoTargetUpper) * rhoWitnessLower`

and proves geometric convergence when the target is not always shifted and a
discriminating witness has positive shift probability.

The causal correspondence is deliberately not hidden in the probability
theorem: applying it to the Mechanism Shift Score still requires the source's
faithfulness, shared-mechanism, independent-causal-mechanism, and
pseudo-causal-sufficiency assumptions to establish the per-pair failure bound.
-/

namespace Mettapedia.MachineLearning.ContinualLearning

namespace SparseMechanismShift

open Filter MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal Topology

noncomputable section

variable {Omega Candidate Pair : Type*}
variable [MeasurableSpace Omega]

/-- A false candidate survives all paired comparisons exactly when every pair
fails to discriminate it. -/
def candidateSurvives
    (pairFails : Candidate → Pair → Set Omega) (candidate : Candidate) :
    Set Omega :=
  ⋂ pair, pairFails candidate pair

/-- Global identification fails when at least one false candidate survives all
paired comparisons. -/
def identificationFailure
    (pairFails : Candidate → Pair → Set Omega) : Set Omega :=
  ⋃ candidate, candidateSurvives pairFails candidate

/-- Successful identification is the complement of global failure. -/
def identificationSuccess
    (pairFails : Candidate → Pair → Set Omega) : Set Omega :=
  (identificationFailure pairFails)ᶜ

theorem measurableSet_candidateSurvives
    [Fintype Pair]
    {pairFails : Candidate → Pair → Set Omega}
    (hmeasurable : ∀ candidate pair, MeasurableSet (pairFails candidate pair))
    (candidate : Candidate) :
    MeasurableSet (candidateSurvives pairFails candidate) := by
  exact MeasurableSet.iInter (hmeasurable candidate)

theorem measurableSet_identificationFailure
    [Fintype Candidate] [Fintype Pair]
    {pairFails : Candidate → Pair → Set Omega}
    (hmeasurable : ∀ candidate pair, MeasurableSet (pairFails candidate pair)) :
    MeasurableSet (identificationFailure pairFails) := by
  exact MeasurableSet.iUnion fun candidate =>
    measurableSet_candidateSurvives hmeasurable candidate

/-- Independence of disjoint environment-pair failures gives the exact
per-candidate product used in the sparse-mechanism-shift rate. -/
theorem measure_candidateSurvives_eq_prod
    [Fintype Pair]
    (mu : Measure Omega)
    {pairFails : Candidate → Pair → Set Omega}
    (hindependent : ∀ candidate, iIndepSet (pairFails candidate) mu)
    (candidate : Candidate) :
    mu (candidateSurvives pairFails candidate) =
      ∏ pair, mu (pairFails candidate pair) := by
  simpa [candidateSurvives] using
    (hindependent candidate).meas_biInter Finset.univ

/-- If every paired comparison fails with probability at most `rate`, a false
candidate survives all independent comparisons with probability at most
`rate ^ numberOfPairs`. -/
theorem measure_candidateSurvives_le_pow
    [Fintype Pair]
    (mu : Measure Omega)
    {pairFails : Candidate → Pair → Set Omega}
    (hindependent : ∀ candidate, iIndepSet (pairFails candidate) mu)
    (rate : ℝ≥0∞)
    (hpair : ∀ candidate pair, mu (pairFails candidate pair) ≤ rate)
    (candidate : Candidate) :
    mu (candidateSurvives pairFails candidate) ≤
      rate ^ Fintype.card Pair := by
  rw [measure_candidateSurvives_eq_prod mu hindependent candidate]
  calc
    (∏ pair, mu (pairFails candidate pair)) ≤ ∏ _pair : Pair, rate := by
      gcongr with pair
      exact hpair candidate pair
    _ = rate ^ Fintype.card Pair := by simp

/-- Finite-candidate identification bound: independent paired comparisons
give geometric failure decay, and the only cross-candidate step is a union
bound.  Candidate failure events need not be mutually independent. -/
theorem measure_identificationFailure_le
    [Fintype Candidate] [Fintype Pair]
    (mu : Measure Omega)
    {pairFails : Candidate → Pair → Set Omega}
    (hindependent : ∀ candidate, iIndepSet (pairFails candidate) mu)
    (rate : ℝ≥0∞)
    (hpair : ∀ candidate pair, mu (pairFails candidate pair) ≤ rate) :
    mu (identificationFailure pairFails) ≤
      (Fintype.card Candidate : ℝ≥0∞) *
        rate ^ Fintype.card Pair := by
  calc
    mu (identificationFailure pairFails) ≤
        ∑ candidate, mu (candidateSurvives pairFails candidate) := by
      simpa [identificationFailure] using
        measure_iUnion_fintype_le mu
          (fun candidate => candidateSurvives pairFails candidate)
    _ ≤ ∑ _candidate : Candidate, rate ^ Fintype.card Pair := by
      gcongr with candidate
      exact measure_candidateSurvives_le_pow
        mu hindependent rate hpair candidate
    _ = (Fintype.card Candidate : ℝ≥0∞) *
        rate ^ Fintype.card Pair := by
      simp

/-- Complement form of the finite-candidate bound. -/
theorem measure_identificationSuccess_ge
    [Fintype Candidate] [Fintype Pair]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    {pairFails : Candidate → Pair → Set Omega}
    (hmeasurable : ∀ candidate pair, MeasurableSet (pairFails candidate pair))
    (hindependent : ∀ candidate, iIndepSet (pairFails candidate) mu)
    (rate : ℝ≥0∞)
    (hpair : ∀ candidate pair, mu (pairFails candidate pair) ≤ rate) :
    1 - (Fintype.card Candidate : ℝ≥0∞) *
          rate ^ Fintype.card Pair ≤
      mu (identificationSuccess pairFails) := by
  rw [identificationSuccess,
    measure_compl
      (measurableSet_identificationFailure hmeasurable)
      (measure_ne_top mu _),
    measure_univ]
  exact tsub_le_tsub_left
    (measure_identificationFailure_le mu hindependent rate hpair) 1

/-! ## Sparse-shift specialization -/

/-- Per-pair failure factor from the sparse mechanism shift argument.
`rhoTargetUpper` bounds how often the target mechanism changes, while
`rhoWitnessLower` lower-bounds a mechanism change that distinguishes the
false parent set. -/
def sparsePairFailure
    (rhoTargetUpper rhoWitnessLower : NNReal) : NNReal :=
  1 - (1 - rhoTargetUpper) * rhoWitnessLower

/-- Exact one-pair failure probability under independent target-shift and
witness-shift indicators: discrimination occurs when the target stays fixed
while the witness changes. -/
def pairFailureProbability
    (rhoTarget rhoWitness : NNReal) : NNReal :=
  1 - (1 - rhoTarget) * rhoWitness

theorem sparsePairFailure_le_one
    (rhoTargetUpper rhoWitnessLower : NNReal) :
    sparsePairFailure rhoTargetUpper rhoWitnessLower ≤ 1 := by
  exact tsub_le_self

/-- Replacing the target shift probability by an upper bound and the witness
shift probability by a lower bound yields a valid worst-case pair-failure
rate.  This is the arithmetic step in the source's Lemma 5.2. -/
theorem pairFailureProbability_le_sparsePairFailure
    {rhoTarget rhoWitness rhoTargetUpper rhoWitnessLower : NNReal}
    (htarget : rhoTarget ≤ rhoTargetUpper)
    (hwitness : rhoWitnessLower ≤ rhoWitness) :
    pairFailureProbability rhoTarget rhoWitness ≤
      sparsePairFailure rhoTargetUpper rhoWitnessLower := by
  unfold pairFailureProbability sparsePairFailure
  apply tsub_le_tsub_left
  exact mul_le_mul
    (tsub_le_tsub_left htarget 1)
    hwitness
    zero_le
    zero_le

/-- Event-level bridge: once causal faithfulness and independent mechanism
shifts identify a pair-failure event with the exact two-indicator
probability, the sparse upper/lower rate bounds discharge its probability
obligation. -/
theorem measure_pairFailure_le_sparsePairFailure
    (mu : Measure Omega) (failure : Set Omega)
    {rhoTarget rhoWitness rhoTargetUpper rhoWitnessLower : NNReal}
    (hmeasure :
      mu failure = (pairFailureProbability rhoTarget rhoWitness : ℝ≥0∞))
    (htarget : rhoTarget ≤ rhoTargetUpper)
    (hwitness : rhoWitnessLower ≤ rhoWitness) :
    mu failure ≤
      (sparsePairFailure rhoTargetUpper rhoWitnessLower : ℝ≥0∞) := by
  rw [hmeasure]
  exact_mod_cast
    pairFailureProbability_le_sparsePairFailure htarget hwitness

/-- A target that is not always shifted and a witness that sometimes shifts
make the per-pair failure factor strictly smaller than one. -/
theorem sparsePairFailure_lt_one
    {rhoTargetUpper rhoWitnessLower : NNReal}
    (htarget : rhoTargetUpper < 1)
    (hwitness : 0 < rhoWitnessLower) :
    sparsePairFailure rhoTargetUpper rhoWitnessLower < 1 := by
  exact tsub_lt_self zero_lt_one
    (mul_pos (tsub_pos_of_lt htarget) hwitness)

/-- Whole-candidate sparse-shift bound, corresponding to the finite-rate core
of Theorem 5.3 in the source. -/
theorem measure_identificationFailure_le_sparseShift
    [Fintype Candidate] [Fintype Pair]
    (mu : Measure Omega)
    {pairFails : Candidate → Pair → Set Omega}
    (hindependent : ∀ candidate, iIndepSet (pairFails candidate) mu)
    (rhoTargetUpper rhoWitnessLower : NNReal)
    (hpair : ∀ candidate pair,
      mu (pairFails candidate pair) ≤
        (sparsePairFailure rhoTargetUpper rhoWitnessLower : ℝ≥0∞)) :
    mu (identificationFailure pairFails) ≤
      (Fintype.card Candidate : ℝ≥0∞) *
        (sparsePairFailure rhoTargetUpper rhoWitnessLower : ℝ≥0∞) ^
          Fintype.card Pair :=
  measure_identificationFailure_le mu hindependent
    (sparsePairFailure rhoTargetUpper rhoWitnessLower : ℝ≥0∞) hpair

/-- The finite-candidate failure bound converges to zero as the number of
independent environment pairs grows whenever the per-pair rate is below one.
-/
theorem finiteCandidateFailureBound_tendsto_zero
    (candidateCount : ℕ) {rate : ℝ≥0∞} (hrate : rate < 1) :
    Tendsto
      (fun pairCount : ℕ =>
        (candidateCount : ℝ≥0∞) * rate ^ pairCount)
      atTop (𝓝 0) := by
  simpa using
    ENNReal.Tendsto.const_mul
      (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hrate)
      (Or.inr (by simp : (candidateCount : ℝ≥0∞) ≠ ∞))

/-- Sparse shifts with nondegenerate target and witness probabilities make
the global finite-candidate upper bound converge to zero. -/
theorem sparseShiftFailureBound_tendsto_zero
    (candidateCount : ℕ)
    {rhoTargetUpper rhoWitnessLower : NNReal}
    (htarget : rhoTargetUpper < 1)
    (hwitness : 0 < rhoWitnessLower) :
    Tendsto
      (fun pairCount : ℕ =>
        (candidateCount : ℝ≥0∞) *
          (sparsePairFailure rhoTargetUpper rhoWitnessLower : ℝ≥0∞) ^ pairCount)
      atTop (𝓝 0) :=
  finiteCandidateFailureBound_tendsto_zero candidateCount
    (by
      exact_mod_cast sparsePairFailure_lt_one htarget hwitness)

/-! ## Executable endpoints and separation fixtures -/

/-- If the distinguishing witness never changes, the sparse-shift bound does
not improve with additional pairs. -/
theorem zero_witness_has_unit_failure
    (rhoTargetUpper : NNReal) :
    sparsePairFailure rhoTargetUpper 0 = 1 := by
  simp [sparsePairFailure]

/-- If the target may change on every pair, the sparse-shift bound likewise
does not improve. -/
theorem always_shifted_target_has_unit_failure
    (rhoWitnessLower : NNReal) :
    sparsePairFailure 1 rhoWitnessLower = 1 := by
  simp [sparsePairFailure]

/-- A nondegenerate numerical fixture: target-shift upper bound `1/4` and
witness-shift lower bound `1/2` give per-pair failure `5/8`. -/
theorem sparsePairFailure_quarter_half :
    sparsePairFailure (1 / 4 : NNReal) (1 / 2 : NNReal) = 5 / 8 := by
  have hquarter : (1 / 4 : NNReal) ≤ 1 :=
    (div_le_one (by norm_num : (0 : NNReal) < 4)).2 (by norm_num)
  have hhalf : (1 / 2 : NNReal) ≤ 1 :=
    (div_le_one (by norm_num : (0 : NNReal) < 2)).2 (by norm_num)
  have hproduct :
      (1 - (1 / 4 : NNReal)) * (1 / 2 : NNReal) ≤ 1 :=
    mul_le_one₀ tsub_le_self zero_le hhalf
  apply NNReal.eq
  norm_num [sparsePairFailure, NNReal.coe_sub hproduct,
    NNReal.coe_sub hquarter]

/-- Two false candidates and four independent pairs give the explicit upper
bound `625/2048` in the preceding fixture. -/
theorem two_candidates_four_pairs :
    (2 : NNReal) * sparsePairFailure (1 / 4 : NNReal) (1 / 2 : NNReal) ^ 4 =
      625 / 2048 := by
  rw [sparsePairFailure_quarter_half]
  norm_num

omit [MeasurableSpace Omega] in
/-- With no pair able to discriminate anything, global failure is the whole
sample space. -/
theorem all_pairs_fail_identificationFailure
    [Nonempty Candidate] [Nonempty Pair] :
    identificationFailure
      (Omega := Omega) (Candidate := Candidate) (Pair := Pair)
      (fun (_candidate : Candidate) (_pair : Pair) => Set.univ) = Set.univ := by
  ext omega
  constructor
  · intro _
    exact Set.mem_univ omega
  · intro _
    let candidate : Candidate := Classical.choice inferInstance
    refine Set.mem_iUnion.mpr ⟨candidate, ?_⟩
    exact Set.mem_iInter.mpr fun _pair => Set.mem_univ omega

omit [MeasurableSpace Omega] in
/-- When every pair discriminates every candidate, global failure is empty. -/
theorem no_pair_fails_identificationFailure
    [Nonempty Pair] :
    identificationFailure
      (Omega := Omega) (Candidate := Candidate) (Pair := Pair)
      (fun (_candidate : Candidate) (_pair : Pair) => (∅ : Set Omega)) = ∅ := by
  ext omega
  constructor
  · intro hfailure
    rcases Set.mem_iUnion.mp hfailure with ⟨_candidate, hcandidate⟩
    let pair : Pair := Classical.choice inferInstance
    exact Set.mem_iInter.mp hcandidate pair
  · intro himpossible
    exact himpossible.elim

end

end SparseMechanismShift

end Mettapedia.MachineLearning.ContinualLearning
