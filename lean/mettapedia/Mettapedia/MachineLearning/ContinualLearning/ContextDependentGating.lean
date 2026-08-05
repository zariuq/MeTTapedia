import Mathlib.Tactic

/-!
# Context-dependent gating

Masse, Grant, and Freedman (2018), *Alleviating Catastrophic
Forgetting Using Context-Dependent Gating and Synaptic Stabilization*,
multiply a fixed task-specific fraction of hidden-unit activations by zero.
With eighty percent of each of two adjacent hidden layers gated, only four
percent of their connecting weights are active for that task.

This file isolates the finite support algebra behind that mechanism:

* active connection support is the Cartesian product of the active endpoint
  sets, so its cardinality and pairwise task overlap factor exactly;
* a masked gradient update supported away from an old task's connections
  preserves that task's masked linear readout exactly;
* the source's eighty-percent unit gate gives the stated four-percent active,
  ninety-six-percent inactive hidden-to-hidden connection count.

The scope boundary is explicit. Disjoint hidden connection supports do not
protect a shared downstream bias, so mask separation alone is not a
whole-network no-forgetting theorem. The source's reported task accuracies
remain empirical.
-/

namespace Mettapedia.MachineLearning.ContinualLearning

namespace ContextDependentGating

noncomputable section

open scoped BigOperators

variable {Input Output : Type*}

/-- A weight is active exactly when both of its endpoint units are active. -/
def connectionSupport
    (activeOutput : Finset Output)
    (activeInput : Finset Input) : Finset (Output × Input) :=
  activeOutput ×ˢ activeInput

@[simp] theorem mem_connectionSupport
    (activeOutput : Finset Output)
    (activeInput : Finset Input)
    (output : Output) (input : Input) :
    (output, input) ∈ connectionSupport activeOutput activeInput ↔
      output ∈ activeOutput ∧ input ∈ activeInput := by
  simp [connectionSupport]

/-- Active connection count factors into the two active-unit counts. -/
@[simp] theorem card_connectionSupport
    (activeOutput : Finset Output)
    (activeInput : Finset Input) :
    (connectionSupport activeOutput activeInput).card =
      activeOutput.card * activeInput.card := by
  simp [connectionSupport]

variable [DecidableEq Input] [DecidableEq Output]

/-- Task overlap in connection space is exactly the product of the endpoint
overlaps. -/
theorem connectionSupport_inter
    (leftOutput rightOutput : Finset Output)
    (leftInput rightInput : Finset Input) :
    connectionSupport leftOutput leftInput ∩
        connectionSupport rightOutput rightInput =
      connectionSupport
        (leftOutput ∩ rightOutput) (leftInput ∩ rightInput) := by
  ext ⟨output, input⟩
  simp [connectionSupport, and_left_comm, and_assoc]

/-- The number of connections shared by two task masks factors into the
numbers of output and input units shared by those masks. -/
theorem card_connectionSupport_inter
    (leftOutput rightOutput : Finset Output)
    (leftInput rightInput : Finset Input) :
    (connectionSupport leftOutput leftInput ∩
        connectionSupport rightOutput rightInput).card =
      (leftOutput ∩ rightOutput).card *
        (leftInput ∩ rightInput).card := by
  rw [connectionSupport_inter, card_connectionSupport]

/-! ## Masked gradients and exact old-readout preservation -/

/-- Coordinate gradient after the task mask is applied. -/
def maskedConnectionGradient
    (activeOutput : Finset Output)
    (activeInput : Finset Input)
    (gradient : Output → Input → ℝ)
    (output : Output) (input : Input) : ℝ :=
  if (output, input) ∈ connectionSupport activeOutput activeInput then
    gradient output input
  else
    0

theorem maskedConnectionGradient_eq_zero_of_not_mem
    (activeOutput : Finset Output)
    (activeInput : Finset Input)
    (gradient : Output → Input → ℝ)
    {output : Output} {input : Input}
    (inactive :
      (output, input) ∉ connectionSupport activeOutput activeInput) :
    maskedConnectionGradient
        activeOutput activeInput gradient output input = 0 := by
  simp [maskedConnectionGradient, inactive]

theorem maskedConnectionGradient_eq_of_mem
    (activeOutput : Finset Output)
    (activeInput : Finset Input)
    (gradient : Output → Input → ℝ)
    {output : Output} {input : Input}
    (active :
      (output, input) ∈ connectionSupport activeOutput activeInput) :
    maskedConnectionGradient
        activeOutput activeInput gradient output input =
      gradient output input := by
  simp [maskedConnectionGradient, active]

/-- One parameter update whose support is restricted by a task mask. -/
def applyMaskedUpdate
    (weights gradient : Output → Input → ℝ)
    (rate : ℝ)
    (activeOutput : Finset Output)
    (activeInput : Finset Input)
    (output : Output) (input : Input) : ℝ :=
  weights output input -
    rate *
      maskedConnectionGradient
        activeOutput activeInput gradient output input

/-- A masked update leaves every coordinate outside its active connection
support unchanged. -/
theorem applyMaskedUpdate_eq_of_not_mem
    (weights gradient : Output → Input → ℝ)
    (rate : ℝ)
    (activeOutput : Finset Output)
    (activeInput : Finset Input)
    {output : Output} {input : Input}
    (inactive :
      (output, input) ∉ connectionSupport activeOutput activeInput) :
    applyMaskedUpdate
        weights gradient rate activeOutput activeInput output input =
      weights output input := by
  simp [applyMaskedUpdate,
    maskedConnectionGradient_eq_zero_of_not_mem
      activeOutput activeInput gradient inactive]

/-- Linear readout of one masked layer. -/
def maskedLinear
    (activeOutput : Finset Output)
    (activeInput : Finset Input)
    (weights : Output → Input → ℝ)
    (inputValue : Input → ℝ)
    (output : Output) : ℝ :=
  if output ∈ activeOutput then
    ∑ input ∈ activeInput, weights output input * inputValue input
  else
    0

omit [DecidableEq Input] in
/-- A masked readout depends only on weights in its declared connection
support. -/
theorem maskedLinear_congr_on_support
    (activeOutput : Finset Output)
    (activeInput : Finset Input)
    (leftWeights rightWeights : Output → Input → ℝ)
    (inputValue : Input → ℝ)
    (agree :
      ∀ output input,
        (output, input) ∈
            connectionSupport activeOutput activeInput →
          leftWeights output input = rightWeights output input) :
    maskedLinear activeOutput activeInput leftWeights inputValue =
      maskedLinear activeOutput activeInput rightWeights inputValue := by
  funext output
  by_cases outputActive : output ∈ activeOutput
  · simp only [maskedLinear, if_pos outputActive]
    apply Finset.sum_congr rfl
    intro input inputActive
    rw [agree output input]
    simp [outputActive, inputActive]
  · simp [maskedLinear, outputActive]

/-- **XdG noninterference theorem.** If the new task's active connection
support is disjoint from the old task's support, one masked gradient update
preserves the old task's masked linear readout exactly. -/
theorem disjoint_support_update_preserves_maskedLinear
    (oldOutput : Finset Output) (oldInput : Finset Input)
    (newOutput : Finset Output) (newInput : Finset Input)
    (weights gradient : Output → Input → ℝ)
    (rate : ℝ) (inputValue : Input → ℝ)
    (disjoint :
      Disjoint
        (connectionSupport oldOutput oldInput)
        (connectionSupport newOutput newInput)) :
    maskedLinear oldOutput oldInput
        (applyMaskedUpdate weights gradient rate newOutput newInput)
        inputValue =
      maskedLinear oldOutput oldInput weights inputValue := by
  apply maskedLinear_congr_on_support
  intro output input oldActive
  apply applyMaskedUpdate_eq_of_not_mem
  exact fun newActive =>
    Finset.disjoint_left.mp disjoint oldActive newActive

/-! ## Source count: eighty-percent unit gating -/

/-- Four hundred active units among two thousand: twenty percent active,
eighty percent gated. -/
def sourceActiveHidden : Finset ℕ :=
  Finset.range 400

def sourceAllHidden : Finset ℕ :=
  Finset.range 2000

/-- The source's eighty-percent unit gate activates exactly 160,000 of the
four million hidden-to-hidden connections: four percent. -/
theorem eightyPercent_unit_gating_leaves_fourPercent_hidden_connections :
    (connectionSupport sourceActiveHidden sourceActiveHidden).card =
        160000 ∧
      (connectionSupport sourceAllHidden sourceAllHidden).card =
        4000000 ∧
      25 *
          (connectionSupport
            sourceActiveHidden sourceActiveHidden).card =
        (connectionSupport sourceAllHidden sourceAllHidden).card := by
  norm_num [sourceActiveHidden, sourceAllHidden]

/-- Equivalently, 3,840,000 connections are inactive: ninety-six percent. -/
theorem eightyPercent_unit_gating_leaves_ninetySixPercent_hidden_connections_inactive :
    (connectionSupport sourceAllHidden sourceAllHidden).card -
          (connectionSupport sourceActiveHidden sourceActiveHidden).card =
        3840000 ∧
      25 *
          ((connectionSupport sourceAllHidden sourceAllHidden).card -
            (connectionSupport sourceActiveHidden sourceActiveHidden).card) =
        24 *
          (connectionSupport sourceAllHidden sourceAllHidden).card := by
  norm_num [sourceActiveHidden, sourceAllHidden]

/-! ## Executable positive and negative fixtures -/

def firstUnit : Finset (Fin 2) :=
  {0}

def secondUnit : Finset (Fin 2) :=
  {1}

theorem firstSecondConnectionSupports_disjoint :
    Disjoint
      (connectionSupport firstUnit firstUnit)
      (connectionSupport secondUnit secondUnit) := by
  decide

def zeroWeights : Fin 2 → Fin 2 → ℝ :=
  fun _ _ => 0

def unitGradient : Fin 2 → Fin 2 → ℝ :=
  fun _ _ => 1

def unitInput : Fin 2 → ℝ :=
  fun _ => 1

/-- A concrete update on the second unit leaves the first unit's masked
linear readout unchanged. -/
theorem twoUnit_disjoint_update_preserves_first_readout :
    maskedLinear firstUnit firstUnit
        (applyMaskedUpdate
          zeroWeights unitGradient 1 secondUnit secondUnit)
        unitInput =
      maskedLinear firstUnit firstUnit zeroWeights unitInput :=
  disjoint_support_update_preserves_maskedLinear
    firstUnit firstUnit secondUnit secondUnit
    zeroWeights unitGradient 1 unitInput
    firstSecondConnectionSupports_disjoint

/-- A scalar head with a task-specific hidden sum and one shared bias. -/
def sharedBiasReadout
    {Hidden : Type*} [DecidableEq Hidden]
    (activeHidden : Finset Hidden)
    (hiddenValue : Hidden → ℝ)
    (sharedBias : ℝ) : ℝ :=
  (∑ hidden ∈ activeHidden, hiddenValue hidden) + sharedBias

/-- Negative boundary: even disjoint hidden connection supports do not
protect an old task when a shared downstream bias is changed. -/
theorem disjoint_hidden_support_does_not_protect_shared_bias :
    Disjoint
        (connectionSupport firstUnit firstUnit)
        (connectionSupport secondUnit secondUnit) ∧
      sharedBiasReadout firstUnit (fun _ => 0) 0 ≠
        sharedBiasReadout firstUnit (fun _ => 0) 1 := by
  constructor
  · exact firstSecondConnectionSupports_disjoint
  · norm_num [sharedBiasReadout, firstUnit]

#print axioms connectionSupport_inter
#print axioms card_connectionSupport_inter
#print axioms disjoint_support_update_preserves_maskedLinear
#print axioms eightyPercent_unit_gating_leaves_fourPercent_hidden_connections
#print axioms eightyPercent_unit_gating_leaves_ninetySixPercent_hidden_connections_inactive
#print axioms twoUnit_disjoint_update_preserves_first_readout
#print axioms disjoint_hidden_support_does_not_protect_shared_bias

end

end ContextDependentGating

end Mettapedia.MachineLearning.ContinualLearning
