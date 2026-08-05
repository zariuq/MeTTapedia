import Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier.RecurrentIndependentMechanisms
import Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier.NeuromodulatedPlasticity

/-!
# Sparse neuromodulated memory

This module composes two independently source-bound mechanisms:

* recurrent independent mechanisms supply a finite active-set write boundary;
* neuromodulated plasticity supplies episode-local trace and eligibility
  updates.

The resulting bank applies retroactive plasticity only to active mechanisms.
Inactive mechanisms preserve both trace and eligibility exactly.  With zero
modulation and a valid clipping invariant, the trace plane is preserved
globally even though active eligibility may continue to accumulate.  The
negative fixture shows why the active mask must guard plastic writes as well
as recurrent content: a dense update modifies dormant memory.

The active set and modulation signals are inputs to the semantics.  This file
does not assert that a learned router or modulator selects them well.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier

namespace SparseNeuromodulatedMemory

noncomputable section

open FastWeightMemory
open NeuromodulatedPlasticity

variable {Mechanism Input Output : Type*} [DecidableEq Mechanism]

/-- One retroactive plastic-memory state per mechanism. -/
abbrev BankState (Mechanism Output Input : Type*) :=
  Mechanism → RetroState Output Input

/-- Apply one retroactive plasticity step only to selected mechanisms. -/
def sparseStep
    (active : Finset Mechanism)
    (clip : ℝ → ℝ)
    (modulation rate : Mechanism → ℝ)
    (pre : Mechanism → Input → ℝ)
    (post : Mechanism → Output → ℝ)
    (state : BankState Mechanism Output Input) :
    BankState Mechanism Output Input :=
  fun mechanism =>
    if mechanism ∈ active then
      retroStep clip (modulation mechanism) (rate mechanism)
        (state mechanism) (pre mechanism) (post mechanism)
    else
      state mechanism

/-- Inactive mechanisms preserve the complete plastic state. -/
theorem sparseStep_eq_of_not_mem
    (active : Finset Mechanism)
    (clip : ℝ → ℝ)
    (modulation rate : Mechanism → ℝ)
    (pre : Mechanism → Input → ℝ)
    (post : Mechanism → Output → ℝ)
    (state : BankState Mechanism Output Input)
    {mechanism : Mechanism}
    (inactive : mechanism ∉ active) :
    sparseStep active clip modulation rate pre post state mechanism =
      state mechanism := by
  simp [sparseStep, inactive]

/-- In particular, dormant traces are unchanged. -/
theorem sparseStep_trace_eq_of_not_mem
    (active : Finset Mechanism)
    (clip : ℝ → ℝ)
    (modulation rate : Mechanism → ℝ)
    (pre : Mechanism → Input → ℝ)
    (post : Mechanism → Output → ℝ)
    (state : BankState Mechanism Output Input)
    {mechanism : Mechanism}
    (inactive : mechanism ∉ active) :
    (sparseStep active clip modulation rate pre post state mechanism).trace =
      (state mechanism).trace := by
  rw [sparseStep_eq_of_not_mem active clip modulation rate pre post state
    inactive]

/-- Dormant eligibility is unchanged as well. -/
theorem sparseStep_eligibility_eq_of_not_mem
    (active : Finset Mechanism)
    (clip : ℝ → ℝ)
    (modulation rate : Mechanism → ℝ)
    (pre : Mechanism → Input → ℝ)
    (post : Mechanism → Output → ℝ)
    (state : BankState Mechanism Output Input)
    {mechanism : Mechanism}
    (inactive : mechanism ∉ active) :
    (sparseStep active clip modulation rate pre post state mechanism).eligibility =
      (state mechanism).eligibility := by
  rw [sparseStep_eq_of_not_mem active clip modulation rate pre post state
    inactive]

/-- Controls for inactive mechanisms are observationally irrelevant. -/
theorem sparseStep_eq_of_controls_agree_on_active
    (active : Finset Mechanism)
    (clip : ℝ → ℝ)
    (leftModulation rightModulation : Mechanism → ℝ)
    (leftRate rightRate : Mechanism → ℝ)
    (leftPre rightPre : Mechanism → Input → ℝ)
    (leftPost rightPost : Mechanism → Output → ℝ)
    (state : BankState Mechanism Output Input)
    (modulationAgree :
      ∀ mechanism ∈ active,
        leftModulation mechanism = rightModulation mechanism)
    (rateAgree :
      ∀ mechanism ∈ active, leftRate mechanism = rightRate mechanism)
    (preAgree :
      ∀ mechanism ∈ active, leftPre mechanism = rightPre mechanism)
    (postAgree :
      ∀ mechanism ∈ active, leftPost mechanism = rightPost mechanism) :
    sparseStep active clip leftModulation leftRate leftPre leftPost state =
      sparseStep active clip rightModulation rightRate rightPre rightPost
        state := by
  funext mechanism
  by_cases activated : mechanism ∈ active
  · simp [sparseStep, activated, modulationAgree mechanism activated,
      rateAgree mechanism activated, preAgree mechanism activated,
      postAgree mechanism activated]
  · simp [sparseStep, activated]

/-- When modulation is zero and clipping fixes all current trace entries, the
trace plane is globally preserved.  Active eligibility may still change. -/
theorem sparseStep_zero_modulation_preserves_trace
    (active : Finset Mechanism)
    (clip : ℝ → ℝ)
    (rate : Mechanism → ℝ)
    (pre : Mechanism → Input → ℝ)
    (post : Mechanism → Output → ℝ)
    (state : BankState Mechanism Output Input)
    (fixed :
      ∀ mechanism output input,
        clip ((state mechanism).trace output input) =
          (state mechanism).trace output input) :
    ∀ mechanism,
      (sparseStep active clip (fun _ => 0) rate pre post state
          mechanism).trace =
        (state mechanism).trace := by
  intro mechanism
  by_cases activated : mechanism ∈ active
  · simp only [sparseStep, activated, if_true]
    exact retroStep_trace_zero_of_clip_fixed
      clip (rate mechanism) (state mechanism)
      (pre mechanism) (post mechanism)
      (fixed mechanism)
  · exact sparseStep_trace_eq_of_not_mem
      active clip (fun _ => 0) rate pre post state activated

/-! ## Executable mask boundary -/

abbrev TwoMechanisms := Fin 2
abbrev Scalar := Fin 1

def firstActive : Finset TwoMechanisms := {0}

def dormantEligibilityState :
    BankState TwoMechanisms Scalar Scalar :=
  fun mechanism =>
    if mechanism = 1 then
      { trace := 0
        eligibility := scalarMemory (1 / 2) }
    else
      zeroRetroState

def unitSignal : TwoMechanisms → ℝ :=
  fun _ => 1

def zeroSignals : TwoMechanisms → Scalar → ℝ :=
  fun _ _ => 0

/-- The sparse transition leaves the dormant mechanism's eligible memory
untouched even under a nonzero global modulation signal. -/
theorem sparse_mask_preserves_dormant_plastic_state :
    sparseStep firstActive unitClip unitSignal unitSignal
        zeroSignals zeroSignals dormantEligibilityState 1 =
      dormantEligibilityState 1 := by
  exact sparseStep_eq_of_not_mem
    firstActive unitClip unitSignal unitSignal zeroSignals zeroSignals
    dormantEligibilityState (by decide)

/-- If the same plastic transition is applied densely, dormant eligibility is
written into its trace.  The active mask is therefore semantically
load-bearing rather than a compute-only optimization. -/
theorem omitting_sparse_mask_changes_dormant_trace :
    (retroStep unitClip 1 1
        (dormantEligibilityState 1) zeroActivity zeroActivity).trace 0 0 =
      1 / 2 ∧
    (sparseStep firstActive unitClip unitSignal unitSignal
        zeroSignals zeroSignals dormantEligibilityState 1).trace 0 0 =
      0 := by
  norm_num [retroStep, dormantEligibilityState, eligibilityStep, clipMemory,
    unitClip, sparseStep, firstActive, unitSignal, zeroSignals, zeroActivity,
    zeroRetroState, scalarMemory, scalarValue, scalarKey, Matrix.vecMulVec]

#print axioms sparseStep_eq_of_not_mem
#print axioms sparseStep_eq_of_controls_agree_on_active
#print axioms sparseStep_zero_modulation_preserves_trace
#print axioms sparse_mask_preserves_dormant_plastic_state
#print axioms omitting_sparse_mask_changes_dormant_trace

end

end SparseNeuromodulatedMemory

end Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier
