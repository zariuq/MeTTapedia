import Mettapedia.MachineLearning.NeuralNetworks.Architecture.LowRankAdaptation

/-!
# Online low-rank consolidation

Online-LoRA (Wei, Li, and Marculescu, 2024) uses a task-free lifecycle:
train one low-rank branch, detect a loss plateau, merge the branch into the
frozen weight, and start a fresh zero-output branch.  It also estimates
diagonal parameter importance from squared score gradients.

This file recovers the exact algebraic parts of that lifecycle.  Merge and
zero-reset preserve the effective weight and every linear output, even if an
external plateau detector fires at the wrong time.  Repeated consolidation is
addition of the completed low-rank packets, so packet order is irrelevant.
Two rank-one packets can consolidate to a rank-two matrix, exposing an
important distinction: active trainable rank remains bounded while the
accumulated merged update need not.

The empirical-Fisher diagonal is nonnegative and therefore induces a
nonnegative source-style quadratic penalty.  Negative importance is an
explicit invalid boundary.  No theorem here identifies distribution shifts
from loss windows, proves that plateau-triggered segmentation is optimal, or
establishes the source's empirical accuracy and forgetting results.
-/

namespace Mettapedia.MachineLearning.ContinualLearning

open Mettapedia.MachineLearning.NeuralNetworks.Architecture

namespace OnlineLowRankConsolidation

noncomputable section

variable {Output Input : Type*} {rankBudget : ℕ}

/-! ## One active branch and exact consolidation -/

/-- A dense base weight with exactly one active low-rank branch. -/
structure OnlineLowRankState
    (Output Input : Type*) (rankBudget : ℕ) where
  base : Matrix Output Input ℝ
  activeScale : ℝ
  activeUp : Matrix Output (Fin rankBudget) ℝ
  activeDown : Matrix (Fin rankBudget) Input ℝ

/-- Weight used by the current forward computation. -/
def OnlineLowRankState.effectiveWeight
    (state : OnlineLowRankState Output Input rankBudget) :
    Matrix Output Input ℝ :=
  mergedLowRankWeight state.base state.activeScale
    state.activeUp state.activeDown

/-- Merge the completed branch into the base and create a new branch whose
output factor is exactly zero. -/
def OnlineLowRankState.consolidateAndReset
    (state : OnlineLowRankState Output Input rankBudget)
    (newScale : ℝ)
    (newDown : Matrix (Fin rankBudget) Input ℝ) :
    OnlineLowRankState Output Input rankBudget where
  base := state.effectiveWeight
  activeScale := newScale
  activeUp := 0
  activeDown := newDown

/-- Exact source lifecycle invariant: merge followed by zero-output reset
does not change the effective weight. -/
@[simp] theorem OnlineLowRankState.effectiveWeight_consolidateAndReset
    (state : OnlineLowRankState Output Input rankBudget)
    (newScale : ℝ)
    (newDown : Matrix (Fin rankBudget) Input ℝ) :
    (state.consolidateAndReset newScale newDown).effectiveWeight =
      state.effectiveWeight := by
  simp [OnlineLowRankState.effectiveWeight,
    OnlineLowRankState.consolidateAndReset, mergedLowRankWeight]

/-- Consequently, every linear output is preserved at the consolidation
boundary. -/
theorem OnlineLowRankState.mulVec_consolidateAndReset
    [Fintype Input]
    (state : OnlineLowRankState Output Input rankBudget)
    (newScale : ℝ)
    (newDown : Matrix (Fin rankBudget) Input ℝ)
    (input : Input → ℝ) :
    (state.consolidateAndReset newScale newDown).effectiveWeight.mulVec input =
      state.effectiveWeight.mulVec input := by
  rw [state.effectiveWeight_consolidateAndReset]

/-- An arbitrary Boolean plateau trigger is function-preserving at the instant
it either consolidates or leaves the state unchanged.  This is an execution
safety statement, not a claim that the trigger is statistically correct. -/
def OnlineLowRankState.maybeConsolidate
    (trigger : Bool)
    (state : OnlineLowRankState Output Input rankBudget)
    (newScale : ℝ)
    (newDown : Matrix (Fin rankBudget) Input ℝ) :
    OnlineLowRankState Output Input rankBudget :=
  if trigger then state.consolidateAndReset newScale newDown else state

theorem OnlineLowRankState.effectiveWeight_maybeConsolidate
    (trigger : Bool)
    (state : OnlineLowRankState Output Input rankBudget)
    (newScale : ℝ)
    (newDown : Matrix (Fin rankBudget) Input ℝ) :
    (state.maybeConsolidate trigger newScale newDown).effectiveWeight =
      state.effectiveWeight := by
  cases trigger <;>
    simp [OnlineLowRankState.maybeConsolidate]

/-- The number of trainable factor coordinates stays independent of the
number of already consolidated segments. -/
def OnlineLowRankState.trainableParameterCount
    [Fintype Output] [Fintype Input]
    (_state : OnlineLowRankState Output Input rankBudget) : ℕ :=
  lowRankParameterCount
    (Fintype.card Output) (Fintype.card Input) rankBudget

@[simp] theorem OnlineLowRankState.trainableParameterCount_consolidateAndReset
    [Fintype Output] [Fintype Input]
    (state : OnlineLowRankState Output Input rankBudget)
    (newScale : ℝ)
    (newDown : Matrix (Fin rankBudget) Input ℝ) :
    (state.consolidateAndReset newScale newDown).trainableParameterCount =
      state.trainableParameterCount := by
  rfl

/-! ## Repeated completed packets -/

/-- One completed branch ready to be folded into the dense base. -/
structure LowRankPacket
    (Output Input : Type*) (rankBudget : ℕ) where
  scale : ℝ
  up : Matrix Output (Fin rankBudget) ℝ
  down : Matrix (Fin rankBudget) Input ℝ

def LowRankPacket.delta
    (packet : LowRankPacket Output Input rankBudget) :
    Matrix Output Input ℝ :=
  lowRankDelta packet.scale packet.up packet.down

def consolidatePacket
    (base : Matrix Output Input ℝ)
    (packet : LowRankPacket Output Input rankBudget) :
    Matrix Output Input ℝ :=
  base + packet.delta

/-- Operational left-to-right consolidation trace. -/
def consolidatePackets
    (base : Matrix Output Input ℝ) :
    List (LowRankPacket Output Input rankBudget) →
      Matrix Output Input ℝ
  | [] => base
  | packet :: rest =>
      consolidatePackets (consolidatePacket base packet) rest

def totalPacketDelta
    (packets : List (LowRankPacket Output Input rankBudget)) :
    Matrix Output Input ℝ :=
  (packets.map LowRankPacket.delta).sum

/-- Closed form for an arbitrary consolidation trace. -/
theorem consolidatePackets_eq_base_add_totalPacketDelta
    (base : Matrix Output Input ℝ)
    (packets : List (LowRankPacket Output Input rankBudget)) :
    consolidatePackets base packets =
      base + totalPacketDelta packets := by
  induction packets generalizing base with
  | nil =>
      simp [consolidatePackets, totalPacketDelta]
  | cons packet rest induction =>
      rw [consolidatePackets, induction]
      simp [consolidatePacket, totalPacketDelta, add_assoc]

/-- Two completed branches commute when folded into the dense base. -/
theorem consolidatePacket_commute
    (base : Matrix Output Input ℝ)
    (first second : LowRankPacket Output Input rankBudget) :
    consolidatePacket (consolidatePacket base first) second =
      consolidatePacket (consolidatePacket base second) first := by
  simp [consolidatePacket]
  abel

/-- Consolidating a prefix and then a suffix agrees with one combined trace. -/
theorem consolidatePackets_append
    (base : Matrix Output Input ℝ)
    (first second : List (LowRankPacket Output Input rankBudget)) :
    consolidatePackets base (first ++ second) =
      consolidatePackets (consolidatePackets base first) second := by
  induction first generalizing base with
  | nil => simp [consolidatePackets]
  | cons packet rest induction =>
      simp only [List.cons_append, consolidatePackets]
      exact induction (consolidatePacket base packet)

/-! ## Active-rank versus accumulated-rank boundary -/

def firstAxisPacket : LowRankPacket (Fin 2) (Fin 2) 1 where
  scale := 1
  up := fun output _ => if output = 0 then 1 else 0
  down := fun _ input => if input = 0 then 1 else 0

def secondAxisPacket : LowRankPacket (Fin 2) (Fin 2) 1 where
  scale := 1
  up := fun output _ => if output = 1 then 1 else 0
  down := fun _ input => if input = 1 then 1 else 0

/-- Two individually rank-one packets accumulate to the rank-two identity. -/
theorem two_rankOne_packets_consolidate_to_identity :
    consolidatePackets (0 : Matrix (Fin 2) (Fin 2) ℝ)
      [firstAxisPacket, secondAxisPacket] = 1 := by
  funext row column
  fin_cases row <;>
    fin_cases column <;>
    norm_num [consolidatePackets, consolidatePacket, LowRankPacket.delta,
      firstAxisPacket, secondAxisPacket, lowRankDelta, Matrix.mul_apply,
      Fin.sum_univ_one]

/-- Constant active rank does not imply that the accumulated merged update
has that rank. -/
theorem accumulated_twoPacket_update_not_representable_by_one_rankOne_branch :
    ¬ ∃ (scale : ℝ)
        (up : Matrix (Fin 2) (Fin 1) ℝ)
        (down : Matrix (Fin 1) (Fin 2) ℝ),
      lowRankDelta scale up down =
        consolidatePackets (0 : Matrix (Fin 2) (Fin 2) ℝ)
          [firstAxisPacket, secondAxisPacket] := by
  rintro ⟨scale, up, down, equality⟩
  apply rankOne_lowRankDelta_cannot_equal_identityTwo
  exact ⟨scale, up, down,
    equality.trans two_rankOne_packets_consolidate_to_identity⟩

/-! ## Missing-merge negative fixture -/

/-- Resetting the active branch without first merging it into the base. -/
def OnlineLowRankState.resetWithoutConsolidating
    (state : OnlineLowRankState Output Input rankBudget)
    (newScale : ℝ)
    (newDown : Matrix (Fin rankBudget) Input ℝ) :
    OnlineLowRankState Output Input rankBudget where
  base := state.base
  activeScale := newScale
  activeUp := 0
  activeDown := newDown

def liveScalarState : OnlineLowRankState Unit Unit 1 where
  base := 0
  activeScale := 1
  activeUp := fun _ _ => 1
  activeDown := fun _ _ => 1

/-- The merge is load-bearing: a bare reset discards a live branch. -/
theorem reset_without_consolidating_changes_effectiveWeight :
    (liveScalarState.resetWithoutConsolidating
        1 (fun _ _ => 1)).effectiveWeight ≠
      liveScalarState.effectiveWeight := by
  intro equality
  have coordinate := congrFun (congrFun equality Unit.unit) Unit.unit
  norm_num [OnlineLowRankState.resetWithoutConsolidating,
    OnlineLowRankState.effectiveWeight, liveScalarState,
    mergedLowRankWeight, lowRankDelta, Matrix.mul_apply,
    Fin.sum_univ_one] at coordinate

/-! ## Online diagonal empirical Fisher -/

section Importance

variable {Parameter : Type*}

/-- Source-style diagonal empirical Fisher from a nonempty finite sample
window. -/
def empiricalFisherDiagonal
    (sampleCount : ℕ)
    (score : Fin (sampleCount + 1) → Parameter → ℝ)
    (parameter : Parameter) : ℝ :=
  (∑ sample, (score sample parameter) ^ 2) /
    ((sampleCount + 1 : ℕ) : ℝ)

theorem empiricalFisherDiagonal_nonnegative
    (sampleCount : ℕ)
    (score : Fin (sampleCount + 1) → Parameter → ℝ)
    (parameter : Parameter) :
    0 ≤ empiricalFisherDiagonal sampleCount score parameter := by
  unfold empiricalFisherDiagonal
  exact div_nonneg
    (Finset.sum_nonneg fun sample _ => sq_nonneg (score sample parameter))
    (by positivity)

/-- Diagonal quadratic penalty used after estimating parameter importance. -/
def diagonalImportancePenalty
    [Fintype Parameter]
    (importance value : Parameter → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ parameter,
    importance parameter * (value parameter) ^ 2

theorem diagonalImportancePenalty_nonnegative
    [Fintype Parameter]
    (importance value : Parameter → ℝ)
    (importanceNonnegative : ∀ parameter, 0 ≤ importance parameter) :
    0 ≤ diagonalImportancePenalty importance value := by
  unfold diagonalImportancePenalty
  apply mul_nonneg
  · norm_num
  · exact Finset.sum_nonneg fun parameter _ =>
      mul_nonneg (importanceNonnegative parameter)
        (sq_nonneg (value parameter))

/-- Importance produced by the source's squared-score estimator gives a
proper nonnegative quadratic penalty. -/
theorem empiricalFisher_penalty_nonnegative
    [Fintype Parameter]
    (sampleCount : ℕ)
    (score : Fin (sampleCount + 1) → Parameter → ℝ)
    (value : Parameter → ℝ) :
    0 ≤ diagonalImportancePenalty
      (empiricalFisherDiagonal sampleCount score) value := by
  apply diagonalImportancePenalty_nonnegative
  exact empiricalFisherDiagonal_nonnegative sampleCount score

/-- Negative importance is outside the empirical-Fisher image and makes the
purported regularizer reward displacement. -/
theorem negativeImportance_lowers_penalty :
    diagonalImportancePenalty
      (fun _ : Unit => -1) (fun _ : Unit => 1) = -1 / 2 := by
  norm_num [diagonalImportancePenalty]

end Importance

#print axioms OnlineLowRankState.effectiveWeight_consolidateAndReset
#print axioms OnlineLowRankState.effectiveWeight_maybeConsolidate
#print axioms consolidatePackets_eq_base_add_totalPacketDelta
#print axioms two_rankOne_packets_consolidate_to_identity
#print axioms accumulated_twoPacket_update_not_representable_by_one_rankOne_branch
#print axioms reset_without_consolidating_changes_effectiveWeight
#print axioms empiricalFisher_penalty_nonnegative

end

end OnlineLowRankConsolidation

end Mettapedia.MachineLearning.ContinualLearning
