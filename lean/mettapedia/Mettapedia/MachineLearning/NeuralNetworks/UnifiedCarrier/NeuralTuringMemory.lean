import Mathlib.Tactic

/-!
# Neural Turing Machine memory algebra

Graves, Wayne, and Danihelka (2014), *Neural Turing Machines*, couple a
controller to an addressable memory through normalized differentiable heads.
Their Equation (2) reads a convex combination of memory rows.  Equations (3)
and (4) write by applying every head's pointwise erase and then every head's
add.

This file formalizes the scalar-coordinate algebra shared by every memory
feature.  A normalized read remains inside the range of the addressed
locations and a one-hot head recovers one location exactly.  Erase heads
commute, add heads commute, and the source's two-head batch is invariant under
head order.

The batching convention is load-bearing.  If each head instead performs its
complete erase-then-add operation before the next head, the exact order defect
is `w₁ w₂ (e₁ a₂ - e₂ a₁)`, and a concrete fixture realizes different final
memories.  An unnormalized read can also leave the convex hull.  These
boundaries separate the verified memory algebra from learned addressing,
controller behavior, capacity, and empirical algorithm induction.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier

namespace NeuralTuringMemory

noncomputable section

open scoped BigOperators

/-- Scalar-coordinate memory read from Equation (2).  Vector reads apply this
definition independently to every feature coordinate. -/
def read
    {Location : Type*} [Fintype Location]
    (memory weighting : Location → ℝ) : ℝ :=
  ∑ location, weighting location * memory location

/-- The source's normalization and unit-interval conditions for one head. -/
def NormalizedWeighting
    {Location : Type*} [Fintype Location]
    (weighting : Location → ℝ) : Prop :=
  (∀ location, weighting location ∈ Set.Icc 0 1) ∧
    ∑ location, weighting location = 1

/-- Equation (2) is a genuine convex read: it cannot leave a common interval
containing every addressed memory value. -/
theorem read_mem_Icc
    {Location : Type*} [Fintype Location]
    (memory weighting : Location → ℝ) (lower upper : ℝ)
    (normalized : NormalizedWeighting weighting)
    (memoryBounded :
      ∀ location, memory location ∈ Set.Icc lower upper) :
    read memory weighting ∈ Set.Icc lower upper := by
  rcases normalized with ⟨weightBounds, weightSum⟩
  constructor
  · calc
      lower = ∑ location, weighting location * lower := by
        rw [← Finset.sum_mul, weightSum, one_mul]
      _ ≤ ∑ location, weighting location * memory location :=
        Finset.sum_le_sum (fun location _ =>
          mul_le_mul_of_nonneg_left
            (memoryBounded location).1 (weightBounds location).1)
      _ = read memory weighting := rfl
  · calc
      read memory weighting =
          ∑ location, weighting location * memory location := rfl
      _ ≤ ∑ location, weighting location * upper :=
        Finset.sum_le_sum (fun location _ =>
          mul_le_mul_of_nonneg_left
            (memoryBounded location).2 (weightBounds location).1)
      _ = upper := by
        rw [← Finset.sum_mul, weightSum, one_mul]

/-- A discrete one-hot head, used only as an exact recovery boundary. -/
def oneHot
    {Location : Type*} [DecidableEq Location]
    (target : Location) : Location → ℝ :=
  fun location => if location = target then 1 else 0

@[simp] theorem read_oneHot
    {Location : Type*} [Fintype Location] [DecidableEq Location]
    (memory : Location → ℝ) (target : Location) :
    read memory (oneHot target) = memory target := by
  simp [read, oneHot]

theorem oneHot_normalized
    {Location : Type*} [Fintype Location] [DecidableEq Location]
    (target : Location) :
    NormalizedWeighting (oneHot target) := by
  constructor
  · intro location
    by_cases equal : location = target
    · simp [oneHot, equal]
    · simp [oneHot, equal]
  · simp [oneHot]

/-! ## Erase and add writes -/

/-- One scalar coordinate of Equation (3). -/
def eraseCell
    (memory weighting erase : ℝ) : ℝ :=
  memory * (1 - weighting * erase)

/-- One scalar coordinate of Equation (4). -/
def addCell
    (memory weighting addition : ℝ) : ℝ :=
  memory + weighting * addition

/-- A complete one-head erase-then-add operation. -/
def writeCell
    (memory weighting erase addition : ℝ) : ℝ :=
  addCell (eraseCell memory weighting erase) weighting addition

@[simp] theorem writeCell_zeroWeight
    (memory erase addition : ℝ) :
    writeCell memory 0 erase addition = memory := by
  simp [writeCell, eraseCell, addCell]

/-- Full attention and full erasure replace the cell by the add vector. -/
@[simp] theorem writeCell_fullErase
    (memory addition : ℝ) :
    writeCell memory 1 1 addition = addition := by
  simp [writeCell, eraseCell, addCell]

/-- With erasure disabled, the NTM write reduces to an additive gated write. -/
@[simp] theorem writeCell_zeroErase
    (memory weighting addition : ℝ) :
    writeCell memory weighting 0 addition =
      memory + weighting * addition := by
  simp [writeCell, eraseCell, addCell]

/-- Two erase heads commute, as stated after Equation (3). -/
theorem eraseCell_commute
    (memory firstWeight firstErase secondWeight secondErase : ℝ) :
    eraseCell
        (eraseCell memory firstWeight firstErase)
        secondWeight secondErase =
      eraseCell
        (eraseCell memory secondWeight secondErase)
        firstWeight firstErase := by
  simp [eraseCell]
  ring

/-- Two add heads commute, as stated after Equation (4). -/
theorem addCell_commute
    (memory firstWeight firstAddition secondWeight secondAddition : ℝ) :
    addCell
        (addCell memory firstWeight firstAddition)
        secondWeight secondAddition =
      addCell
        (addCell memory secondWeight secondAddition)
        firstWeight firstAddition := by
  simp [addCell]
  ring

/-- The source's multi-head convention: apply all erasures, then all adds. -/
def batchedTwoHeadWrite
    (memory
      firstWeight firstErase firstAddition
      secondWeight secondErase secondAddition : ℝ) : ℝ :=
  memory * (1 - firstWeight * firstErase) *
      (1 - secondWeight * secondErase) +
    firstWeight * firstAddition +
    secondWeight * secondAddition

/-- Swapping two heads leaves the source's batched write unchanged. -/
theorem batchedTwoHeadWrite_commute
    (memory
      firstWeight firstErase firstAddition
      secondWeight secondErase secondAddition : ℝ) :
    batchedTwoHeadWrite
        memory
        firstWeight firstErase firstAddition
        secondWeight secondErase secondAddition =
      batchedTwoHeadWrite
        memory
        secondWeight secondErase secondAddition
        firstWeight firstErase firstAddition := by
  simp [batchedTwoHeadWrite]
  ring

/-! ## Order boundary for complete sequential heads -/

/-- Exact defect if complete erase-then-add heads are sequenced rather than
batched according to the source. -/
theorem sequentialWrite_orderDefect_exact
    (memory
      firstWeight firstErase firstAddition
      secondWeight secondErase secondAddition : ℝ) :
    writeCell
          (writeCell memory
            firstWeight firstErase firstAddition)
          secondWeight secondErase secondAddition -
        writeCell
          (writeCell memory
            secondWeight secondErase secondAddition)
          firstWeight firstErase firstAddition =
      firstWeight * secondWeight *
        (firstErase * secondAddition -
          secondErase * firstAddition) := by
  simp [writeCell, eraseCell, addCell]
  ring

/-- Concrete order sensitivity: adding `1` and then fully erasing produces
`0`, whereas erasing first and adding second produces `1`. -/
theorem sequentialWrite_order_matters :
    writeCell (writeCell 0 1 0 1) 1 1 0 = 0 ∧
      writeCell (writeCell 0 1 1 0) 1 0 1 = 1 := by
  norm_num [writeCell, eraseCell, addCell]

/-! ## Normalization boundary -/

abbrev TwoLocations := Fin 2

def twoUnitMemory : TwoLocations → ℝ :=
  fun _ => 1

def unnormalizedTwoWeight : TwoLocations → ℝ :=
  fun _ => 1

/-- Dropping Equation (1)'s normalization lets the read escape the memory
range even though every individual weight remains nonnegative. -/
theorem unnormalized_read_escapes_convexHull :
    read twoUnitMemory unnormalizedTwoWeight = 2 ∧
      ¬ NormalizedWeighting unnormalizedTwoWeight := by
  constructor
  · norm_num [read, twoUnitMemory, unnormalizedTwoWeight]
  · intro normalized
    have sumOne := normalized.2
    norm_num [unnormalizedTwoWeight] at sumOne

#print axioms read_mem_Icc
#print axioms read_oneHot
#print axioms oneHot_normalized
#print axioms eraseCell_commute
#print axioms addCell_commute
#print axioms batchedTwoHeadWrite_commute
#print axioms sequentialWrite_orderDefect_exact
#print axioms sequentialWrite_order_matters
#print axioms unnormalized_read_escapes_convexHull

end

end NeuralTuringMemory

end Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier
