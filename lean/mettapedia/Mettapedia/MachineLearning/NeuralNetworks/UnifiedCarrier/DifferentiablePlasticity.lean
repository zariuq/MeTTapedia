import Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier.DecayingFastWeightMemory

/-!
# Differentiable plasticity

Miconi, Clune, and Stanley, *Differentiable plasticity: training plastic
neural networks with backpropagation* (arXiv:1804.02464), give every
connection a fixed weight, an episode-local Hebbian trace, and a learned
plasticity coefficient.  Their Equations (1)--(2) use the effective weight

`fixed + plasticity * trace`

and update the trace by an exponentially decayed pre/post outer product.

This file recovers that finite exact-real algebra over arbitrary finite input
coordinates.  It separates structural weights and plasticity coefficients
from episode-local traces, proves the fixed-network and fully plastic
endpoints, identifies the Hebbian update with decaying fast-weight memory, and
inherits its finite chronological expansion.  Scalar fixtures show both that
nonzero plasticity makes a trace observable and that the source's decayed
Hebbian rule forgets even under zero activity.

The results do not prove meta-learning convergence, biological plausibility,
Oja-rule stability, or any empirical claim in the source.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier

namespace DifferentiablePlasticity

noncomputable section

open FastWeightMemory
open DecayingFastWeightMemory

variable {Input Output : Type*}

/-- Pointwise plastic contribution `alphaᵢⱼ * Hebbᵢⱼ`. -/
def plasticPart
    (plasticity trace : Memory Output Input) :
    Memory Output Input :=
  fun output input => plasticity output input * trace output input

/-- Source Equation (1)'s effective weight before applying the neuron
nonlinearity. -/
def effectiveMemory
    (fixed plasticity trace : Memory Output Input) :
    Memory Output Input :=
  fixed + plasticPart plasticity trace

/-- The effective read separates into fixed and plastic contributions. -/
theorem read_effectiveMemory
    [Fintype Input]
    (fixed plasticity trace : Memory Output Input)
    (input : Input → ℝ) :
    FastWeightMemory.read (effectiveMemory fixed plasticity trace) input =
      FastWeightMemory.read fixed input +
        FastWeightMemory.read (plasticPart plasticity trace) input := by
  simp [effectiveMemory, FastWeightMemory.read, Matrix.add_mulVec]

/-- With zero plasticity coefficients, every trace is observationally
irrelevant and the ordinary fixed network is recovered exactly. -/
theorem effectiveMemory_zero_plasticity
    (fixed trace : Memory Output Input) :
    effectiveMemory fixed 0 trace = fixed := by
  ext output input
  simp [effectiveMemory, plasticPart]

/-- With zero fixed weights, the effective memory is entirely plastic. -/
theorem effectiveMemory_zero_fixed
    (plasticity trace : Memory Output Input) :
    effectiveMemory 0 plasticity trace =
      plasticPart plasticity trace := by
  simp [effectiveMemory]

/-- Source Equation (2): a decayed Hebbian trace update. -/
def hebbianStep
    (learningRate : ℝ)
    (trace : Memory Output Input)
    (pre : Input → ℝ)
    (post : Output → ℝ) :
    Memory Output Input :=
  (1 - learningRate) • trace +
    learningRate • Matrix.vecMulVec post pre

/-- Entrywise form of the source Hebbian update. -/
theorem hebbianStep_apply
    (learningRate : ℝ)
    (trace : Memory Output Input)
    (pre : Input → ℝ)
    (post : Output → ℝ)
    (output : Output) (input : Input) :
    hebbianStep learningRate trace pre post output input =
      learningRate * pre input * post output +
        (1 - learningRate) * trace output input := by
  simp [hebbianStep, Matrix.vecMulVec]
  ring

/-- Equation (2) is the decaying fast-weight update with decay `1 - eta` and
write rate `eta`. -/
theorem hebbianStep_eq_decayingWrite
    (learningRate : ℝ)
    (trace : Memory Output Input)
    (pre : Input → ℝ)
    (post : Output → ℝ) :
    hebbianStep learningRate trace pre post =
      decayingWrite (1 - learningRate) learningRate trace
        ⟨pre, post⟩ := by
  rfl

/-- At learning rate zero the episode-local trace is unchanged. -/
theorem hebbianStep_zero
    (trace : Memory Output Input)
    (pre : Input → ℝ)
    (post : Output → ℝ) :
    hebbianStep 0 trace pre post = trace := by
  simp [hebbianStep]

/-- At learning rate one the newest outer product replaces the trace. -/
theorem hebbianStep_one
    (trace : Memory Output Input)
    (pre : Input → ℝ)
    (post : Output → ℝ) :
    hebbianStep 1 trace pre post =
      Matrix.vecMulVec post pre := by
  simp [hebbianStep]

/-- Execute the source Hebbian rule over a chronological episode. -/
def hebbianEpisode
    (learningRate : ℝ)
    (associations : List (Association Input Output))
    (trace : Memory Output Input) :
    Memory Output Input :=
  writeAllWithDecay (1 - learningRate) learningRate associations trace

/-- Exact finite unrolling of an episode-local Hebbian trace read. -/
theorem read_hebbianEpisode
    [Fintype Input]
    (learningRate : ℝ)
    (associations : List (Association Input Output))
    (trace : Memory Output Input)
    (query : Input → ℝ) :
    FastWeightMemory.read
        (hebbianEpisode learningRate associations trace) query =
      (1 - learningRate) ^ associations.length •
          FastWeightMemory.read trace query +
        learningRate •
          decayedContributionSum (1 - learningRate) associations query :=
  read_writeAllWithDecay
    (1 - learningRate) learningRate associations trace query

/-- A zero-initialized episode recovers precisely the finite
decay-weighted Hebbian association sum. -/
theorem read_zeroTrace_hebbianEpisode
    [Fintype Input]
    (learningRate : ℝ)
    (associations : List (Association Input Output))
    (query : Input → ℝ) :
    FastWeightMemory.read
        (hebbianEpisode learningRate associations 0) query =
      learningRate •
        decayedContributionSum (1 - learningRate) associations query := by
  simpa [hebbianEpisode] using
    (zeroMemory_writeAllWithDecay_eq_decayedAttention
      (1 - learningRate) learningRate associations query)

/-! ## Executable positive and negative fixtures -/

abbrev Scalar := Fin 1

def scalarEffectiveMemory
    (fixed plasticity trace : ℝ) :
    Memory Scalar Scalar :=
  effectiveMemory (scalarMemory fixed) (scalarMemory plasticity)
    (scalarMemory trace)

/-- A learned nonzero plasticity coefficient makes the episode-local trace
observable in the effective read. -/
theorem nonzero_plasticity_trace_is_observable :
    FastWeightMemory.read (scalarEffectiveMemory 1 2 3) scalarKey 0 = 7 ∧
      FastWeightMemory.read (scalarEffectiveMemory 1 0 3) scalarKey 0 = 1 := by
  norm_num [scalarEffectiveMemory, effectiveMemory, plasticPart,
    FastWeightMemory.read,
    scalarMemory, scalarValue, scalarKey, Matrix.mulVec, Matrix.vecMulVec,
    dotProduct]

/-- The source's Equation (2) is not a persistent-memory rule: at eta one
half, a trace of two decays to one even when both activities are zero. -/
theorem zero_activity_still_decays_trace :
    hebbianStep (1 / 2) (scalarMemory 2) (scalarValue 0) (scalarValue 0)
        0 0 =
      1 := by
  norm_num [hebbianStep, scalarMemory, scalarValue, scalarKey,
    Matrix.vecMulVec]

/-- Therefore zero activity does not generally preserve a nonzero trace. -/
theorem zero_activity_does_not_preserve_trace :
    hebbianStep (1 / 2) (scalarMemory 2) (scalarValue 0) (scalarValue 0) ≠
      scalarMemory 2 := by
  intro equality
  have atZero := congrFun (congrFun equality 0) 0
  norm_num [hebbianStep, scalarMemory, scalarValue, scalarKey,
    Matrix.vecMulVec] at atZero

#print axioms read_effectiveMemory
#print axioms effectiveMemory_zero_plasticity
#print axioms hebbianStep_apply
#print axioms hebbianStep_eq_decayingWrite
#print axioms read_hebbianEpisode
#print axioms nonzero_plasticity_trace_is_observable
#print axioms zero_activity_does_not_preserve_trace

end

end DifferentiablePlasticity

end Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier
