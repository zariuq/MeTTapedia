import Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier.FastWeightMemory

/-!
# Routed rank-one associative experts

Lu et al., *Little by Little: Continual Learning via Incremental Mixture of
Rank-1 Associative Memory Experts* (arXiv:2506.21035), Definition 3.1 and
Equations (2)--(8), treat a rank-`r` adapter as `r` atomic key--value memories.
Each atom contributes its value scaled by key/query similarity and an
input-dependent route weight.

This file proves the exact finite matrix/read decomposition and three reusable
boundaries:

* a positive activation-energy premise makes the source's L2 self-scores have
  unit squared mass;
* restricting routes to an active set bounds nonzero support by the active-set
  cardinality;
* neither dense routing nor thresholding is automatically harmless: duplicate
  keys create an explicit retrieval sum, and thresholding already-normalized
  weights need not preserve normalization.

The zero-activation fixture records the denominator boundary explicitly.
No empirical specialization, forgetting, or scaling claim follows from these
finite identities.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier

namespace RankOneAssociativeExperts

noncomputable section

open scoped BigOperators

variable {Atom Key Value : Type*}

/-- Equation (4), interpreted pointwise at an input query: a routed collection
of rank-one key--value atoms. -/
def routedRankOneRead [Fintype Atom] [Fintype Key]
    (keys : Atom → Key → ℝ) (values : Atom → Value → ℝ)
    (weights : Atom → ℝ) (query : Key → ℝ) : Value → ℝ :=
  ∑ atom, weights atom • ((keys atom ⬝ᵥ query) • values atom)

/-- The corresponding routed sum of rank-one parameter matrices. -/
def routedRankOneMemory [Fintype Atom]
    (keys : Atom → Key → ℝ) (values : Atom → Value → ℝ)
    (weights : Atom → ℝ) :
    FastWeightMemory.Memory Value Key :=
  ∑ atom,
    weights atom • Matrix.vecMulVec (values atom) (keys atom)

/-- Definition 3.1 and Equations (2)--(4): multiplying the routed rank-one
matrix by a query is exactly the sum of its atomic associative reads. -/
theorem read_routedRankOneMemory [Fintype Atom] [Fintype Key]
    (keys : Atom → Key → ℝ) (values : Atom → Value → ℝ)
    (weights : Atom → ℝ) (query : Key → ℝ) :
    FastWeightMemory.read
        (routedRankOneMemory keys values weights) query =
      routedRankOneRead keys values weights query := by
  classical
  simp [routedRankOneMemory, routedRankOneRead,
    FastWeightMemory.read, Matrix.sum_mulVec, Matrix.smul_mulVec,
    Matrix.vecMulVec_mulVec]

/-- A one-hot route recovers exactly the selected atom's associative read. -/
theorem routedRankOneRead_oneHot [Fintype Atom] [Fintype Key]
    [DecidableEq Atom]
    (keys : Atom → Key → ℝ) (values : Atom → Value → ℝ)
    (selected : Atom) (query : Key → ℝ) :
    routedRankOneRead keys values
        (fun atom => if atom = selected then 1 else 0) query =
      (keys selected ⬝ᵥ query) • values selected := by
  classical
  simp [routedRankOneRead]

/-- Raw key/query activation used by Equation (5). -/
def rawActivation [Fintype Key]
    (keys : Atom → Key → ℝ) (query : Key → ℝ) (atom : Atom) : ℝ :=
  keys atom ⬝ᵥ query

/-- Squared activation mass in Equation (5)'s denominator. -/
def activationEnergy [Fintype Atom] [Fintype Key]
    (keys : Atom → Key → ℝ) (query : Key → ℝ) : ℝ :=
  ∑ atom, (rawActivation keys query atom) ^ 2

/-- The L2-normalized intrinsic relevance score from Equation (5). -/
def l2SelfScore [Fintype Atom] [Fintype Key]
    (keys : Atom → Key → ℝ) (query : Key → ℝ) (atom : Atom) : ℝ :=
  rawActivation keys query atom /
    Real.sqrt (activationEnergy keys query)

theorem activationEnergy_nonneg [Fintype Atom] [Fintype Key]
    (keys : Atom → Key → ℝ) (query : Key → ℝ) :
    0 ≤ activationEnergy keys query := by
  unfold activationEnergy
  positivity

/-- Positive activation energy is exactly the missing premise needed for the
L2 self-scores to have unit squared mass. -/
theorem sum_sq_l2SelfScore_eq_one [Fintype Atom] [Fintype Key]
    (keys : Atom → Key → ℝ) (query : Key → ℝ)
    (positive : 0 < activationEnergy keys query) :
    ∑ atom, (l2SelfScore keys query atom) ^ 2 = 1 := by
  have nonnegative := activationEnergy_nonneg keys query
  have sqrtSq :
      Real.sqrt (activationEnergy keys query) ^ 2 =
        activationEnergy keys query :=
    Real.sq_sqrt nonnegative
  simp only [l2SelfScore, div_pow]
  rw [← Finset.sum_div, sqrtSq]
  exact div_self (ne_of_gt positive)

/-- At zero activation energy, Lean's totalized division returns zero scores;
the unit-mass conclusion therefore cannot be stated without a positive-energy
premise. -/
theorem sum_sq_l2SelfScore_eq_zero_of_energy_zero
    [Fintype Atom] [Fintype Key]
    (keys : Atom → Key → ℝ) (query : Key → ℝ)
    (zero : activationEnergy keys query = 0) :
    ∑ atom, (l2SelfScore keys query atom) ^ 2 = 0 := by
  simp [l2SelfScore, zero]

/-! ## Sparse support semantics -/

/-- Semantic active-set restriction underlying a top-`k` route. -/
def restrictedWeight [DecidableEq Atom]
    (active : Finset Atom) (weights : Atom → ℝ) (atom : Atom) : ℝ :=
  if atom ∈ active then weights atom else 0

/-- Restricting weights is exactly summing only the active atoms. -/
theorem routedRankOneRead_restricted
    [Fintype Atom] [DecidableEq Atom] [Fintype Key]
    (keys : Atom → Key → ℝ) (values : Atom → Value → ℝ)
    (weights : Atom → ℝ) (active : Finset Atom) (query : Key → ℝ) :
    routedRankOneRead keys values
        (restrictedWeight active weights) query =
      ∑ atom ∈ active,
        weights atom • ((keys atom ⬝ᵥ query) • values atom) := by
  classical
  simp [routedRankOneRead, restrictedWeight]

/-- Nonzero support after active-set restriction. -/
noncomputable def nonzeroSupport [Fintype Atom] [DecidableEq Atom]
    (active : Finset Atom) (weights : Atom → ℝ) : Finset Atom := by
  classical
  exact Finset.univ.filter
    (fun atom => restrictedWeight active weights atom ≠ 0)

theorem nonzeroSupport_subset_active
    [Fintype Atom] [DecidableEq Atom]
    (active : Finset Atom) (weights : Atom → ℝ) :
    nonzeroSupport active weights ⊆ active := by
  classical
  intro atom member
  simp only [nonzeroSupport, Finset.mem_filter, Finset.mem_univ,
    true_and] at member
  by_contra outside
  simp [restrictedWeight, outside] at member

/-- Any active-set selector with at most `k` atoms yields at most `k` nonzero
routes, irrespective of the values of the retained weights. -/
theorem card_nonzeroSupport_le
    [Fintype Atom] [DecidableEq Atom]
    (active : Finset Atom) (weights : Atom → ℝ) (k : ℕ)
    (budget : active.card ≤ k) :
    (nonzeroSupport active weights).card ≤ k :=
  le_trans
    (Finset.card_le_card (nonzeroSupport_subset_active active weights))
    budget

/-! ## Threshold and interference boundaries -/

/-- Equation (8)'s post-normalization threshold, without an additional
renormalization step. -/
def thresholdWeight
    (threshold : ℝ) (weights : Atom → ℝ) (atom : Atom) : ℝ :=
  if threshold ≤ weights atom then weights atom else 0

abbrev TwoAtom := Fin 2
abbrev Scalar := Fin 1

def duplicateKeys (_atom : TwoAtom) (_coordinate : Scalar) : ℝ := 1

def twoAtomValues (atom : TwoAtom) (_coordinate : Scalar) : ℝ :=
  if atom = 0 then 2 else 3

def denseWeights (_atom : TwoAtom) : ℝ := 1

def firstOnlyWeight (atom : TwoAtom) : ℝ :=
  if atom = 0 then 1 else 0

def unitQuery (_coordinate : Scalar) : ℝ := 1

/-- Duplicate keys make dense rank-one routing retrieve both values, whereas a
one-hot route recovers only the selected value. Atomic decomposition by itself
does not prevent interference. -/
theorem dense_routing_interferes :
    routedRankOneRead duplicateKeys twoAtomValues
        denseWeights unitQuery 0 = 5 ∧
      routedRankOneRead duplicateKeys twoAtomValues
        firstOnlyWeight unitQuery 0 = 2 := by
  norm_num [routedRankOneRead, duplicateKeys, twoAtomValues,
    denseWeights, firstOnlyWeight, unitQuery, dotProduct,
    Fin.sum_univ_two]

def zeroKey (_atom : Scalar) (_coordinate : Scalar) : ℝ := 0

/-- An all-zero key activation hits Equation (5)'s denominator boundary:
totalized scores have squared mass zero, not one. -/
theorem zero_activation_has_no_normalized_self_score :
    activationEnergy zeroKey unitQuery = 0 ∧
      (∑ atom, (l2SelfScore zeroKey unitQuery atom) ^ 2) = 0 ∧
      (∑ atom, (l2SelfScore zeroKey unitQuery atom) ^ 2) ≠ 1 := by
  norm_num [activationEnergy, rawActivation, l2SelfScore,
    zeroKey, unitQuery, dotProduct]

def normalizedTwoAtomWeight (atom : TwoAtom) : ℝ :=
  if atom = 0 then 3 / 4 else 1 / 4

/-- Thresholding a normalized two-atom route at `1/2` removes the smaller
weight and leaves total mass `3/4`. Equation (8) therefore does not preserve
normalization unless the surviving weights are renormalized. -/
theorem threshold_can_destroy_normalization :
    (∑ atom, normalizedTwoAtomWeight atom) = 1 ∧
      (∑ atom,
        thresholdWeight (1 / 2) normalizedTwoAtomWeight atom) = 3 / 4 ∧
      (∑ atom,
        thresholdWeight (1 / 2) normalizedTwoAtomWeight atom) ≠ 1 := by
  norm_num [normalizedTwoAtomWeight, thresholdWeight, Fin.sum_univ_two]

#print axioms read_routedRankOneMemory
#print axioms routedRankOneRead_oneHot
#print axioms sum_sq_l2SelfScore_eq_one
#print axioms sum_sq_l2SelfScore_eq_zero_of_energy_zero
#print axioms routedRankOneRead_restricted
#print axioms card_nonzeroSupport_le
#print axioms dense_routing_interferes
#print axioms zero_activation_has_no_normalized_self_score
#print axioms threshold_can_destroy_normalization

end

end RankOneAssociativeExperts

end Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier
