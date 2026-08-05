import Mettapedia.MachineLearning.NeuralNetworks.Architecture.RoutingExpansion

/-!
# Progressive columns: exact preservation, transfer, and scaling boundaries

Rusu et al., *Progressive Neural Networks* (2016), Equation (1), add a new
column for each task.  A new column reads its own previous-layer features and
features from older frozen columns through one-way lateral connections.
Older parameters are excluded from the new task's optimizer.

This file isolates the architectural content in a scalar two-column model.
Arbitrary sequences of new-column updates preserve the old task exactly,
while a lateral connection can make a frozen old feature available to the new
task.  The directionality is load-bearing: a backward connection from the new
column into the old readout permits a new-column update to change old
behavior.

The final section records the other structural cost of the source
architecture.  Giving every later column a separate connection from every
older column has triangular growth.  A fixed-width shared lateral pool instead
has a constant per-column increment, but that compression is an architectural
alternative rather than an identity with the source construction.
-/

namespace Mettapedia.MachineLearning.ContinualLearning

namespace ProgressiveNetworks

noncomputable section

/-! ## A scalar progressive pair -/

/-- Two scalar columns with a one-way lateral connection from old to new. -/
structure ScalarPair where
  oldInputWeight : ℝ
  oldReadoutWeight : ℝ
  newInputWeight : ℝ
  newReadoutWeight : ℝ
  oldToNewWeight : ℝ

/-- A training update restricted to the new column and its lateral adapter. -/
structure NewColumnUpdate where
  inputDelta : ℝ
  readoutDelta : ℝ
  lateralDelta : ℝ

def oldHidden (network : ScalarPair) (input : ℝ) : ℝ :=
  network.oldInputWeight * input

def newHidden (network : ScalarPair) (input : ℝ) : ℝ :=
  network.newInputWeight * input +
    network.oldToNewWeight * oldHidden network input

def oldOutput (network : ScalarPair) (input : ℝ) : ℝ :=
  network.oldReadoutWeight * oldHidden network input

def newOutput (network : ScalarPair) (input : ℝ) : ℝ :=
  network.newReadoutWeight * newHidden network input

/-- Apply one optimizer displacement only to the new column and its lateral
adapter. -/
def applyNewColumnUpdate
    (network : ScalarPair) (update : NewColumnUpdate) : ScalarPair where
  oldInputWeight := network.oldInputWeight
  oldReadoutWeight := network.oldReadoutWeight
  newInputWeight := network.newInputWeight + update.inputDelta
  newReadoutWeight := network.newReadoutWeight + update.readoutDelta
  oldToNewWeight := network.oldToNewWeight + update.lateralDelta

/-- Execute new-task optimizer displacements in their recorded order. -/
def applyNewColumnUpdates
    (network : ScalarPair) (updates : List NewColumnUpdate) : ScalarPair :=
  updates.foldl applyNewColumnUpdate network

@[simp] theorem oldHidden_applyNewColumnUpdate
    (network : ScalarPair) (update : NewColumnUpdate) (input : ℝ) :
    oldHidden (applyNewColumnUpdate network update) input =
      oldHidden network input := rfl

@[simp] theorem oldOutput_applyNewColumnUpdate
    (network : ScalarPair) (update : NewColumnUpdate) (input : ℝ) :
    oldOutput (applyNewColumnUpdate network update) input =
      oldOutput network input := rfl

/-- Exact no-forgetting for an arbitrary finite new-task training trace.  The
statement quantifies over the actual ordered update list, not just one
parameter snapshot. -/
theorem oldOutput_applyNewColumnUpdates
    (network : ScalarPair) (updates : List NewColumnUpdate) (input : ℝ) :
    oldOutput (applyNewColumnUpdates network updates) input =
      oldOutput network input := by
  induction updates generalizing network with
  | nil =>
      rfl
  | cons update rest inductionHypothesis =>
      simp only [applyNewColumnUpdates, List.foldl_cons]
      change
        oldOutput
            (applyNewColumnUpdates
              (applyNewColumnUpdate network update) rest)
            input =
          oldOutput network input
      rw [inductionHypothesis, oldOutput_applyNewColumnUpdate]

/-- With the lateral edge disabled, the new column is an independent scalar
column. -/
theorem newOutput_zeroLateral
    (network : ScalarPair) (input : ℝ)
    (lateralZero : network.oldToNewWeight = 0) :
    newOutput network input =
      network.newReadoutWeight * (network.newInputWeight * input) := by
  simp [newOutput, newHidden, lateralZero]

/-- Positive transfer fixture: the new column has zero direct input weight but
reuses the frozen old feature through the lateral connection. -/
theorem lateral_reuses_frozen_feature (input : ℝ) :
    let network : ScalarPair :=
      ⟨2, 1, 0, 3, 1 / 2⟩
    oldOutput network input = 2 * input ∧
      newOutput network input = 3 * input := by
  dsimp [oldOutput, oldHidden, newOutput, newHidden]
  constructor <;> ring

/-- New-column training can change the new behavior while old behavior remains
exactly fixed. -/
theorem new_update_changes_new_but_not_old :
    let network : ScalarPair := ⟨2, 1, 0, 1, 1 / 2⟩
    let update : NewColumnUpdate := ⟨1, 1, 0⟩
    oldOutput (applyNewColumnUpdate network update) 1 =
        oldOutput network 1 ∧
      newOutput (applyNewColumnUpdate network update) 1 ≠
        newOutput network 1 := by
  norm_num [
    oldOutput,
    oldHidden,
    newOutput,
    newHidden,
    applyNewColumnUpdate,
  ]

/-! ## Directionality boundary -/

/-- A non-progressive variant in which the old column also reads the current
new feature.  This creates a path from new-task updates back into old
behavior. -/
structure BackwardCoupledPair where
  oldInputWeight : ℝ
  oldReadoutWeight : ℝ
  newInputWeight : ℝ
  newToOldWeight : ℝ

def backwardOldOutput
    (network : BackwardCoupledPair) (input : ℝ) : ℝ :=
  network.oldReadoutWeight *
    (network.oldInputWeight * input +
      network.newToOldWeight * (network.newInputWeight * input))

def updateBackwardNewInput
    (network : BackwardCoupledPair) (inputDelta : ℝ) :
    BackwardCoupledPair :=
  { network with
    newInputWeight := network.newInputWeight + inputDelta }

/-- Exact displacement of old behavior caused by updating a backward-coupled
new column. -/
theorem backwardOldOutput_update_sub
    (network : BackwardCoupledPair) (inputDelta input : ℝ) :
    backwardOldOutput (updateBackwardNewInput network inputDelta) input -
        backwardOldOutput network input =
      network.oldReadoutWeight * network.newToOldWeight *
        inputDelta * input := by
  simp only [backwardOldOutput, updateBackwardNewInput]
  ring

/-- Negative fixture: freezing the old parameters is insufficient when the
forward graph contains a new-to-old edge. -/
theorem backward_connection_breaks_old_preservation :
    let network : BackwardCoupledPair := ⟨1, 1, 1, 1⟩
    backwardOldOutput (updateBackwardNewInput network 1) 1 = 3 ∧
      backwardOldOutput network 1 = 2 := by
  norm_num [backwardOldOutput, updateBackwardNewInput]

/-! ## Capacity growth -/

/-- Number of distinct older-to-newer column pairs among `columns` columns. -/
def pairwiseLateralCount : ℕ → ℕ
  | 0 => 0
  | columns + 1 => pairwiseLateralCount columns + columns

/-- Parameter count for fixed per-column capacity and a distinct fixed-size
lateral adapter for every ordered older-to-newer column pair. -/
def unsharedProgressiveCapacity
    (columnCapacity lateralCapacity columns : ℕ) : ℕ :=
  columns * columnCapacity +
    pairwiseLateralCount columns * lateralCapacity

/-- A fixed-width shared lateral pool has one fixed adapter budget per
column, rather than one budget per earlier column. -/
def sharedPoolCapacity
    (columnCapacity lateralCapacity columns : ℕ) : ℕ :=
  columns * (columnCapacity + lateralCapacity)

/-- Adding column `columns + 1` to the unshared construction costs one column
plus one lateral adapter for every older column. -/
theorem unsharedProgressiveCapacity_succ
    (columnCapacity lateralCapacity columns : ℕ) :
    unsharedProgressiveCapacity columnCapacity lateralCapacity
        (columns + 1) =
      unsharedProgressiveCapacity columnCapacity lateralCapacity columns +
        columnCapacity + columns * lateralCapacity := by
  simp [unsharedProgressiveCapacity, pairwiseLateralCount, Nat.add_mul]
  ac_rfl

/-- Adding a column to the shared-pool alternative has a constant increment. -/
theorem sharedPoolCapacity_succ
    (columnCapacity lateralCapacity columns : ℕ) :
    sharedPoolCapacity columnCapacity lateralCapacity (columns + 1) =
      sharedPoolCapacity columnCapacity lateralCapacity columns +
        (columnCapacity + lateralCapacity) := by
  simp [sharedPoolCapacity, Nat.add_mul]

theorem pairwiseLateralCount_four :
    pairwiseLateralCount 4 = 6 := by
  norm_num [pairwiseLateralCount]

/-- Concrete scaling separation: with unit column and lateral capacities,
four unshared progressive columns need ten units, while a fixed shared pool
needs eight. -/
theorem unshared_exceeds_shared :
    unsharedProgressiveCapacity 1 1 4 = 10 ∧
      sharedPoolCapacity 1 1 4 = 8 := by
  norm_num [
    unsharedProgressiveCapacity,
    sharedPoolCapacity,
    pairwiseLateralCount,
  ]

#print axioms oldOutput_applyNewColumnUpdates
#print axioms lateral_reuses_frozen_feature
#print axioms new_update_changes_new_but_not_old
#print axioms backwardOldOutput_update_sub
#print axioms backward_connection_breaks_old_preservation
#print axioms unsharedProgressiveCapacity_succ
#print axioms sharedPoolCapacity_succ
#print axioms unshared_exceeds_shared

end

end ProgressiveNetworks

end Mettapedia.MachineLearning.ContinualLearning
