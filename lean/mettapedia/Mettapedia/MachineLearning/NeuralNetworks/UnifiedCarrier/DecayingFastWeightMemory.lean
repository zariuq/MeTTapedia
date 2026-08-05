import Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier.FastWeightMemory

/-!
# Decaying fast-weight memory

Ba, Hinton, Mnih, Leibo, and Ionescu (2016), *Using Fast Weights to
Attend to the Recent Past*, define a rapidly changing associative matrix by

`A(t) = decay * A(t - 1) + rate * h(t) h(t)ᵀ`.

Their Equations (3)--(4) unroll this recurrence and identify its matrix-vector
product with a decay-weighted attention read over earlier hidden states.

This file proves that identity for arbitrary finite key and value coordinates,
arbitrary initial memory, and an ordered finite instruction stream.  The
zero-memory specialization recovers the source equations.  The exact
two-instruction formula also exposes an execution boundary: unless the decay is
zero or the two contributions agree, reversing the stream changes the result.

The results are finite exact-real algebra.  They do not establish empirical
memory capacity, convergence of the source inner settling loop, or
floating-point implementation correspondence.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier

namespace DecayingFastWeightMemory

noncomputable section

open scoped BigOperators
open FastWeightMemory

variable {Key Value : Type*} [Fintype Key]

/-- One decayed outer-product write, corresponding to Equation (1). -/
def decayingWrite
    (decay rate : ℝ) (memory : Memory Value Key)
    (association : Association Key Value) :
    Memory Value Key :=
  decay • memory +
    rate • Matrix.vecMulVec association.value association.key

/-- Execute a chronological stream of decayed writes. -/
def writeAllWithDecay
    (decay rate : ℝ) :
    List (Association Key Value) →
      Memory Value Key → Memory Value Key
  | [], memory => memory
  | association :: associations, memory =>
      writeAllWithDecay decay rate associations
        (decayingWrite decay rate memory association)

/-- The oldest contribution is discounted once for every later write. -/
def decayedContributionSum
    (decay : ℝ) :
    List (Association Key Value) →
      (Key → ℝ) → (Value → ℝ)
  | [], _query => 0
  | association :: associations, query =>
      decay ^ associations.length • contribution association query +
        decayedContributionSum decay associations query

/-- Exact read effect of one decayed outer-product write. -/
theorem read_decayingWrite
    (decay rate : ℝ) (memory : Memory Value Key)
    (association : Association Key Value)
    (query : Key → ℝ) :
    FastWeightMemory.read
        (decayingWrite decay rate memory association) query =
      decay • FastWeightMemory.read memory query +
        rate • contribution association query := by
  simp only [FastWeightMemory.read, decayingWrite, contribution,
    Matrix.add_mulVec,
    Matrix.smul_mulVec, Matrix.vecMulVec_mulVec]
  simp

/-- Exact finite unrolling from an arbitrary initial memory. -/
theorem read_writeAllWithDecay
    (decay rate : ℝ)
    (associations : List (Association Key Value))
    (memory : Memory Value Key) (query : Key → ℝ) :
    FastWeightMemory.read
        (writeAllWithDecay decay rate associations memory) query =
      decay ^ associations.length • FastWeightMemory.read memory query +
        rate • decayedContributionSum decay associations query := by
  induction associations generalizing memory with
  | nil =>
      simp [writeAllWithDecay, decayedContributionSum]
  | cons association associations ih =>
      rw [writeAllWithDecay, ih, read_decayingWrite]
      simp only [decayedContributionSum, List.length_cons, pow_succ']
      module

/-- Equations (3)--(4): zero initial memory gives precisely the
decay-weighted attention read. -/
theorem zeroMemory_writeAllWithDecay_eq_decayedAttention
    (decay rate : ℝ)
    (associations : List (Association Key Value))
    (query : Key → ℝ) :
    FastWeightMemory.read
        (writeAllWithDecay decay rate associations 0) query =
      rate • decayedContributionSum decay associations query := by
  rw [read_writeAllWithDecay]
  simp [FastWeightMemory.read]

/-- With no decay, only the newest of two instructions remains. -/
theorem zeroDecay_twoInstructions_keeps_latest
    (rate : ℝ)
    (first second : Association Key Value)
    (query : Key → ℝ) :
    FastWeightMemory.read
        (writeAllWithDecay 0 rate [first, second] 0)
        query =
      rate • contribution second query := by
  rw [zeroMemory_writeAllWithDecay_eq_decayedAttention]
  simp [decayedContributionSum]

/-- Unit decay reduces the weighted sum to ordinary additive attention. -/
theorem decayedContributionSum_one
    (associations : List (Association Key Value))
    (query : Key → ℝ) :
    decayedContributionSum 1 associations query =
      (associations.map
        (fun association => contribution association query)).sum := by
  induction associations with
  | nil =>
      simp [decayedContributionSum]
  | cons association associations ih =>
      simp [decayedContributionSum, ih]

/-- Unit decay recovers the additive fast-weight read, up to the common
write rate. -/
theorem zeroMemory_unitDecay_eq_scaledLinearAttention
    (rate : ℝ)
    (associations : List (Association Key Value))
    (query : Key → ℝ) :
    FastWeightMemory.read
        (writeAllWithDecay 1 rate associations 0) query =
      rate •
        (associations.map
          (fun association => contribution association query)).sum := by
  rw [zeroMemory_writeAllWithDecay_eq_decayedAttention,
    decayedContributionSum_one]

/-- Exact swap discrepancy for two chronological instructions. -/
theorem twoInstruction_swap_discrepancy
    (decay rate : ℝ)
    (first second : Association Key Value)
    (query : Key → ℝ) :
    FastWeightMemory.read
          (writeAllWithDecay decay rate [first, second] 0)
          query -
        FastWeightMemory.read
          (writeAllWithDecay decay rate [second, first] 0)
          query =
      (rate * (decay - 1)) •
        (contribution first query - contribution second query) := by
  rw [zeroMemory_writeAllWithDecay_eq_decayedAttention,
    zeroMemory_writeAllWithDecay_eq_decayedAttention]
  simp only [decayedContributionSum, List.length_cons, List.length_nil,
    pow_one, pow_zero, one_smul, zero_add]
  module

/-! ## Executable scalar fixtures -/

abbrev ScalarIndex := Fin 1

def scalarAssociation (value : ℝ) :
    Association ScalarIndex ScalarIndex :=
  ⟨fun _ => 1, fun _ => value⟩

def scalarQuery : ScalarIndex → ℝ :=
  fun _ => 1

theorem scalarContribution
    (value : ℝ) :
    contribution (scalarAssociation value) scalarQuery 0 = value := by
  simp [contribution, scalarAssociation, scalarQuery, dotProduct]

/-- At decay one-half, values two then five read as six. -/
theorem chronological_decay :
    FastWeightMemory.read
        (writeAllWithDecay (1 / 2) 1
          [scalarAssociation 2, scalarAssociation 5] 0)
        scalarQuery 0 =
      6 := by
  norm_num [FastWeightMemory.read, writeAllWithDecay, decayingWrite,
    scalarAssociation,
    scalarQuery, Matrix.mulVec, Matrix.vecMulVec, dotProduct]

/-- Reversing the same stream reads as nine-halves, so decayed memory is not
permutation invariant. -/
theorem reversed_decay :
    FastWeightMemory.read
        (writeAllWithDecay (1 / 2) 1
          [scalarAssociation 5, scalarAssociation 2] 0)
        scalarQuery 0 =
      9 / 2 := by
  norm_num [FastWeightMemory.read, writeAllWithDecay, decayingWrite,
    scalarAssociation,
    scalarQuery, Matrix.mulVec, Matrix.vecMulVec, dotProduct]

theorem decayed_write_order_matters :
    FastWeightMemory.read
        (writeAllWithDecay (1 / 2) 1
          [scalarAssociation 2, scalarAssociation 5] 0)
        scalarQuery ≠
      FastWeightMemory.read
        (writeAllWithDecay (1 / 2) 1
          [scalarAssociation 5, scalarAssociation 2] 0)
        scalarQuery := by
  intro equality
  have at_zero := congrFun equality 0
  rw [chronological_decay, reversed_decay] at at_zero
  norm_num at at_zero

#print axioms read_decayingWrite
#print axioms read_writeAllWithDecay
#print axioms zeroMemory_writeAllWithDecay_eq_decayedAttention
#print axioms zeroDecay_twoInstructions_keeps_latest
#print axioms decayedContributionSum_one
#print axioms zeroMemory_unitDecay_eq_scaledLinearAttention
#print axioms twoInstruction_swap_discrepancy
#print axioms chronological_decay
#print axioms reversed_decay
#print axioms decayed_write_order_matters

end

end DecayingFastWeightMemory

end Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier
