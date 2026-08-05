import Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier.DifferentiablePlasticity

/-!
# Neuromodulated plasticity

Miconi, Rawal, Clune, and Stanley, *Backpropamine: training
self-modifying neural networks with differentiable neuromodulated plasticity*
(arXiv:2002.10585), replace a fixed Hebbian update rate with a
network-controlled modulation signal.  Their Equations (3)--(5) distinguish
two constructions:

* simple modulation clips the old trace plus the current modulation times the
  current pre/post outer product;
* retroactive modulation first applies the current modulation to the *old*
  eligibility trace, while the next eligibility trace is a decayed current
  pre/post outer product.

This file gives both transitions over arbitrary connection matrices.  It
proves the zero-modulation boundary under an explicit clipping fixed-point
hypothesis, the eligibility-rate endpoints, and the exact old-eligibility
dependency.  Executable scalar fixtures demonstrate delayed credit and reject
the tempting but source-inconsistent eager update that uses the newly computed
eligibility trace in the same timestep.

The modulation signal is supplied.  No theorem claims that a learned network
discovers useful modulators, prevents catastrophic forgetting, or reproduces
the source's empirical results.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier

namespace NeuromodulatedPlasticity

noncomputable section

open FastWeightMemory

variable {Input Output : Type*}

/-- Apply a scalar clipping function independently to every connection. -/
def clipMemory
    (clip : ℝ → ℝ)
    (memory : Memory Output Input) :
    Memory Output Input :=
  fun output input => clip (memory output input)

/-- Source Equation (3): directly modulate the current Hebbian outer-product
write before clipping. -/
def simpleModulatedStep
    (clip : ℝ → ℝ)
    (modulation : ℝ)
    (trace : Memory Output Input)
    (pre : Input → ℝ)
    (post : Output → ℝ) :
    Memory Output Input :=
  clipMemory clip
    (trace + modulation • Matrix.vecMulVec post pre)

/-- Entrywise form of simple neuromodulation. -/
theorem simpleModulatedStep_apply
    (clip : ℝ → ℝ)
    (modulation : ℝ)
    (trace : Memory Output Input)
    (pre : Input → ℝ)
    (post : Output → ℝ)
    (output : Output) (input : Input) :
    simpleModulatedStep clip modulation trace pre post output input =
      clip
        (trace output input +
          modulation * (post output * pre input)) := by
  simp [simpleModulatedStep, clipMemory, Matrix.vecMulVec]

/-- Zero modulation preserves a trace whenever clipping already fixes every
entry of that trace. -/
theorem simpleModulatedStep_zero_of_clip_fixed
    (clip : ℝ → ℝ)
    (trace : Memory Output Input)
    (pre : Input → ℝ)
    (post : Output → ℝ)
    (fixed : ∀ output input, clip (trace output input) = trace output input) :
    simpleModulatedStep clip 0 trace pre post = trace := by
  ext output input
  simp [simpleModulatedStep_apply, fixed output input]

/-- Source Equation (5): exponentially update the eligibility trace. -/
def eligibilityStep
    (rate : ℝ)
    (eligibility : Memory Output Input)
    (pre : Input → ℝ)
    (post : Output → ℝ) :
    Memory Output Input :=
  (1 - rate) • eligibility +
    rate • Matrix.vecMulVec post pre

theorem eligibilityStep_zero
    (eligibility : Memory Output Input)
    (pre : Input → ℝ)
    (post : Output → ℝ) :
    eligibilityStep 0 eligibility pre post = eligibility := by
  simp [eligibilityStep]

theorem eligibilityStep_one
    (eligibility : Memory Output Input)
    (pre : Input → ℝ)
    (post : Output → ℝ) :
    eligibilityStep 1 eligibility pre post =
      Matrix.vecMulVec post pre := by
  simp [eligibilityStep]

/-- The two episode-local memories used by retroactive modulation. -/
structure RetroState (Output Input : Type*) where
  trace : Memory Output Input
  eligibility : Memory Output Input

/-- Source Equations (4)--(5), with their simultaneous old-state semantics
made explicit. -/
def retroStep
    (clip : ℝ → ℝ)
    (modulation rate : ℝ)
    (state : RetroState Output Input)
    (pre : Input → ℝ)
    (post : Output → ℝ) :
    RetroState Output Input :=
  { trace :=
      clipMemory clip
        (state.trace + modulation • state.eligibility)
    eligibility :=
      eligibilityStep rate state.eligibility pre post }

/-- The trace write uses the old eligibility trace and is therefore
independent of the current pre/post activities once the old state and
modulation are fixed. -/
theorem retroStep_trace
    (clip : ℝ → ℝ)
    (modulation rate : ℝ)
    (state : RetroState Output Input)
    (pre : Input → ℝ)
    (post : Output → ℝ) :
    (retroStep clip modulation rate state pre post).trace =
      clipMemory clip
        (state.trace + modulation • state.eligibility) :=
  rfl

/-- Current activities affect the next eligibility trace exactly through
Equation (5). -/
theorem retroStep_eligibility
    (clip : ℝ → ℝ)
    (modulation rate : ℝ)
    (state : RetroState Output Input)
    (pre : Input → ℝ)
    (post : Output → ℝ) :
    (retroStep clip modulation rate state pre post).eligibility =
      eligibilityStep rate state.eligibility pre post :=
  rfl

/-- Zero modulation preserves a valid trace, although eligibility may still
advance. -/
theorem retroStep_trace_zero_of_clip_fixed
    (clip : ℝ → ℝ)
    (rate : ℝ)
    (state : RetroState Output Input)
    (pre : Input → ℝ)
    (post : Output → ℝ)
    (fixed :
      ∀ output input,
        clip (state.trace output input) = state.trace output input) :
    (retroStep clip 0 rate state pre post).trace = state.trace := by
  ext output input
  simp [retroStep, clipMemory, fixed output input]

/-- The source's hard clip to the interval `[-1, 1]`. -/
def unitClip (value : ℝ) : ℝ :=
  max (-1) (min 1 value)

theorem unitClip_eq_self
    {value : ℝ}
    (lower : -1 ≤ value)
    (upper : value ≤ 1) :
    unitClip value = value := by
  simp [unitClip, min_eq_right upper, max_eq_right lower]

/-! ## Executable timing fixtures -/

abbrev Scalar := Fin 1

def zeroRetroState : RetroState Scalar Scalar where
  trace := 0
  eligibility := 0

def halfActivity : Scalar → ℝ :=
  fun _ => 1 / 2

def zeroActivity : Scalar → ℝ :=
  fun _ => 0

/-- Activity at the first step creates eligibility but no plastic trace when
modulation is zero.  Modulation at the next step then incorporates that old
eligibility even though current activity is zero. -/
theorem delayed_modulation :
    let afterActivity :=
      retroStep unitClip 0 1 zeroRetroState halfActivity halfActivity
    let afterModulation :=
      retroStep unitClip 1 1 afterActivity zeroActivity zeroActivity
    afterActivity.trace 0 0 = 0 ∧
      afterActivity.eligibility 0 0 = 1 / 4 ∧
      afterModulation.trace 0 0 = 1 / 4 ∧
      afterModulation.eligibility 0 0 = 0 := by
  norm_num [retroStep, zeroRetroState, eligibilityStep, clipMemory,
    unitClip, halfActivity, zeroActivity, Matrix.vecMulVec]

/-- A source-inconsistent eager trace write, included only as a negative
fixture: it uses the newly computed eligibility in the same timestep. -/
def eagerTrace
    (clip : ℝ → ℝ)
    (modulation rate : ℝ)
    (state : RetroState Output Input)
    (pre : Input → ℝ)
    (post : Output → ℝ) :
    Memory Output Input :=
  clipMemory clip
    (state.trace +
      modulation • eligibilityStep rate state.eligibility pre post)

/-- The eager and source transitions are observably different on the first
rewarded activity: the source trace is still zero, whereas eager timing writes
one quarter immediately. -/
theorem eager_new_eligibility_is_not_source_timing :
    (retroStep unitClip 1 1 zeroRetroState
          halfActivity halfActivity).trace 0 0 =
        0 ∧
      eagerTrace unitClip 1 1 zeroRetroState
          halfActivity halfActivity 0 0 =
        1 / 4 := by
  norm_num [retroStep, eagerTrace, zeroRetroState, eligibilityStep,
    clipMemory, unitClip, halfActivity, Matrix.vecMulVec]

/-- A zero modulation signal alone is insufficient without the declared
clipping fixed-point invariant. -/
theorem zero_modulation_without_clip_invariant_can_change_trace :
    let erase : ℝ → ℝ := fun _ => 0
    simpleModulatedStep erase 0 (scalarMemory 1)
        zeroActivity zeroActivity ≠ scalarMemory 1 := by
  dsimp
  intro equality
  have atZero := congrFun (congrFun equality 0) 0
  norm_num [simpleModulatedStep, clipMemory, scalarMemory, scalarValue,
    scalarKey, zeroActivity, Matrix.vecMulVec] at atZero

#print axioms simpleModulatedStep_apply
#print axioms simpleModulatedStep_zero_of_clip_fixed
#print axioms eligibilityStep_zero
#print axioms eligibilityStep_one
#print axioms retroStep_trace
#print axioms retroStep_trace_zero_of_clip_fixed
#print axioms delayed_modulation
#print axioms eager_new_eligibility_is_not_source_timing
#print axioms zero_modulation_without_clip_invariant_can_change_trace

end

end NeuromodulatedPlasticity

end Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier
