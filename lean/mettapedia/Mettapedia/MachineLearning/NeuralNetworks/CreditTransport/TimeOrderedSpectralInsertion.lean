import Mathlib

/-!
# Time-ordered spectral insertion

Pasechnyuk-Vilensky and Takáč, *Chebyshev-Exact Acceleration under
Hessian Variation, I: Sine-Jacobi Method* (arXiv:2606.16671), Lemma 1.1
and Appendix A.1, identify the first variation of a finite accelerated
schedule.  An insertion from a source eigenspace to a target eigenspace is
transported by source-spectrum factors before its time index and
target-spectrum factors afterward.

This file recovers that time-ordered algebra for arbitrary finite memory.
Each phase has a target-fibre matrix, a source-fibre matrix, and a directed
insertion matrix.  The coupled triangular execution is exactly affine in a
shared perturbation scale.  Its coefficient is a recursively defined
time-ordered insertion response, so the nonzero finite-difference quotient is
exactly that response.

The result is deliberately realization-sensitive.  Two scalar schedules can
have identical fixed target and source terminal products while their
insertion responses differ.  Thus a terminal residual polynomial alone does
not determine first-order curvature-drift sensitivity.

The primary PDF used here has SHA-256
`765fb89609bf4884ea2c69e8a314f8ab9f0bd52a56cdac0f361714eefb1c775b`.
This file does not formalize the source's Chebyshev/Jacobi constructions,
sharp asymptotic constants, nonlinear objectives, or experiments.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace TimeOrderedSpectralInsertion

noncomputable section

variable {Memory : Type*} [Fintype Memory]

abbrev FibreState (Memory : Type*) := Memory → ℝ

/-- One chronological phase restricted to a source/target spectral pair. -/
structure SpectralPairPhase (Memory : Type*) where
  targetFactor : Matrix Memory Memory ℝ
  sourceFactor : Matrix Memory Memory ℝ
  insertion : Matrix Memory Memory ℝ

/-- Coupled target/source state for one directed spectral insertion. -/
structure SpectralPairState (Memory : Type*) where
  target : FibreState Memory
  source : FibreState Memory

/-- One triangular phase.  The perturbation maps source to target, while the
source fibre itself evolves independently. -/
def spectralPairStep
    (scale : ℝ) (phase : SpectralPairPhase Memory)
    (state : SpectralPairState Memory) : SpectralPairState Memory where
  target :=
    Matrix.mulVec phase.targetFactor state.target +
      scale • Matrix.mulVec phase.insertion state.source
  source := Matrix.mulVec phase.sourceFactor state.source

/-- Execute phases in chronological list order. -/
def runSpectralPair
    (scale : ℝ) :
    List (SpectralPairPhase Memory) →
      SpectralPairState Memory → SpectralPairState Memory
  | [], state => state
  | phase :: phases, state =>
      runSpectralPair scale phases (spectralPairStep scale phase state)

/-- Target-fibre propagation with all insertions suppressed. -/
def fixedTargetPropagation :
    List (SpectralPairPhase Memory) → FibreState Memory → FibreState Memory
  | [], state => state
  | phase :: phases, state =>
      fixedTargetPropagation phases (Matrix.mulVec phase.targetFactor state)

/-- Source-fibre propagation, which is independent of the perturbation. -/
def fixedSourcePropagation :
    List (SpectralPairPhase Memory) → FibreState Memory → FibreState Memory
  | [], state => state
  | phase :: phases, state =>
      fixedSourcePropagation phases (Matrix.mulVec phase.sourceFactor state)

/-- Sum of every insertion transported by the source factors before it and
the target factors after it.  This is the source's time-ordered spectral
first-variation kernel applied to the per-phase insertions. -/
def timeOrderedInsertionResponse :
    List (SpectralPairPhase Memory) → FibreState Memory → FibreState Memory
  | [], _ => 0
  | phase :: phases, state =>
      fixedTargetPropagation phases (Matrix.mulVec phase.insertion state) +
        timeOrderedInsertionResponse phases
          (Matrix.mulVec phase.sourceFactor state)

@[simp] theorem fixedTargetPropagation_zero
    (phases : List (SpectralPairPhase Memory)) :
    fixedTargetPropagation phases (0 : FibreState Memory) = 0 := by
  induction phases with
  | nil => rfl
  | cons phase phases ih =>
      simp [fixedTargetPropagation, ih]

theorem fixedTargetPropagation_add
    (phases : List (SpectralPairPhase Memory))
    (left right : FibreState Memory) :
    fixedTargetPropagation phases (left + right) =
      fixedTargetPropagation phases left +
        fixedTargetPropagation phases right := by
  induction phases generalizing left right with
  | nil => rfl
  | cons phase phases ih =>
      simp only [fixedTargetPropagation, Matrix.mulVec_add]
      exact ih _ _

theorem fixedTargetPropagation_smul
    (phases : List (SpectralPairPhase Memory))
    (scale : ℝ) (state : FibreState Memory) :
    fixedTargetPropagation phases (scale • state) =
      scale • fixedTargetPropagation phases state := by
  induction phases generalizing state with
  | nil => rfl
  | cons phase phases ih =>
      simp only [fixedTargetPropagation, Matrix.mulVec_smul]
      exact ih _

/-- The source fibre never depends on the insertion scale. -/
theorem runSpectralPair_source
    (scale : ℝ) (phases : List (SpectralPairPhase Memory))
    (state : SpectralPairState Memory) :
    (runSpectralPair scale phases state).source =
      fixedSourcePropagation phases state.source := by
  induction phases generalizing state with
  | nil => rfl
  | cons phase phases ih =>
      simpa [runSpectralPair, spectralPairStep, fixedSourcePropagation]
        using ih (spectralPairStep scale phase state)

/-- Finite-horizon first-variation crown.  The target execution is exactly
its fixed propagation plus the perturbation scale times the time-ordered
insertion response. -/
theorem runSpectralPair_target_eq_fixed_add_smul_response
    (scale : ℝ) (phases : List (SpectralPairPhase Memory))
    (state : SpectralPairState Memory) :
    (runSpectralPair scale phases state).target =
      fixedTargetPropagation phases state.target +
        scale • timeOrderedInsertionResponse phases state.source := by
  induction phases generalizing state with
  | nil =>
      simp [runSpectralPair, fixedTargetPropagation,
        timeOrderedInsertionResponse]
  | cons phase phases ih =>
      rw [runSpectralPair, ih]
      simp only [spectralPairStep, fixedTargetPropagation,
        timeOrderedInsertionResponse, fixedTargetPropagation_add,
        fixedTargetPropagation_smul]
      module

@[simp] theorem runSpectralPair_target_zeroScale
    (phases : List (SpectralPairPhase Memory))
    (state : SpectralPairState Memory) :
    (runSpectralPair 0 phases state).target =
      fixedTargetPropagation phases state.target := by
  simp [runSpectralPair_target_eq_fixed_add_smul_response]

/-- Exact finite difference from the zero-perturbation execution. -/
theorem runSpectralPair_target_sub_zeroScale
    (scale : ℝ) (phases : List (SpectralPairPhase Memory))
    (state : SpectralPairState Memory) :
    (runSpectralPair scale phases state).target -
        (runSpectralPair 0 phases state).target =
      scale • timeOrderedInsertionResponse phases state.source := by
  rw [runSpectralPair_target_eq_fixed_add_smul_response,
    runSpectralPair_target_zeroScale]
  module

/-- For every nonzero perturbation scale, the exact finite-difference
quotient equals the time-ordered insertion response. -/
theorem inv_smul_runSpectralPair_target_sub_zeroScale
    {scale : ℝ} (scale_ne : scale ≠ 0)
    (phases : List (SpectralPairPhase Memory))
    (state : SpectralPairState Memory) :
    scale⁻¹ •
        ((runSpectralPair scale phases state).target -
          (runSpectralPair 0 phases state).target) =
      timeOrderedInsertionResponse phases state.source := by
  rw [runSpectralPair_target_sub_zeroScale]
  simp [smul_smul, scale_ne]

/-- Suppress the insertion while retaining both fixed spectral factors. -/
def withoutInsertion
    (phase : SpectralPairPhase Memory) : SpectralPairPhase Memory where
  targetFactor := phase.targetFactor
  sourceFactor := phase.sourceFactor
  insertion := 0

/-- With every directed insertion suppressed, the first variation vanishes. -/
@[simp] theorem timeOrderedInsertionResponse_map_withoutInsertion
    (phases : List (SpectralPairPhase Memory))
    (state : FibreState Memory) :
    timeOrderedInsertionResponse (phases.map withoutInsertion) state = 0 := by
  induction phases generalizing state with
  | nil => rfl
  | cons phase phases ih =>
      simp [timeOrderedInsertionResponse, withoutInsertion,
        fixedTargetPropagation_zero, ih]

/-! ## Scalar realization-sensitivity fixture -/

abbrev ScalarMemory := Fin 1

def scalarMatrix (value : ℝ) : Matrix ScalarMemory ScalarMemory ℝ :=
  fun _ _ => value

def scalarState (value : ℝ) : FibreState ScalarMemory :=
  fun _ => value

def scalarPhase
    (targetFactor sourceFactor insertion : ℝ) :
    SpectralPairPhase ScalarMemory where
  targetFactor := scalarMatrix targetFactor
  sourceFactor := scalarMatrix sourceFactor
  insertion := scalarMatrix insertion

def earlyInsertionSchedule : List (SpectralPairPhase ScalarMemory) :=
  [scalarPhase 2 3 1, scalarPhase 5 7 0]

def lateInsertionSchedule : List (SpectralPairPhase ScalarMemory) :=
  [scalarPhase 5 7 0, scalarPhase 2 3 1]

/-- Reordering two scalar phases preserves both fixed terminal products but
changes the time-ordered insertion response from `5` to `7`.  This is the
minimal realization-sensitive boundary behind the source's Hessian-drift
comparison. -/
theorem same_fixed_terminal_different_insertion_response :
    fixedTargetPropagation earlyInsertionSchedule (scalarState 1) =
        fixedTargetPropagation lateInsertionSchedule (scalarState 1) ∧
      fixedSourcePropagation earlyInsertionSchedule (scalarState 1) =
        fixedSourcePropagation lateInsertionSchedule (scalarState 1) ∧
      timeOrderedInsertionResponse earlyInsertionSchedule (scalarState 1) ≠
        timeOrderedInsertionResponse lateInsertionSchedule (scalarState 1) := by
  constructor
  · funext index
    fin_cases index
    norm_num [earlyInsertionSchedule, lateInsertionSchedule, scalarPhase,
      scalarMatrix, scalarState, fixedTargetPropagation, Matrix.mulVec,
      dotProduct, Fin.sum_univ_one]
  constructor
  · funext index
    fin_cases index
    norm_num [earlyInsertionSchedule, lateInsertionSchedule, scalarPhase,
      scalarMatrix, scalarState, fixedSourcePropagation, Matrix.mulVec,
      dotProduct, Fin.sum_univ_one]
  · intro equal
    have atZero := congrFun equal 0
    norm_num [earlyInsertionSchedule, lateInsertionSchedule, scalarPhase,
      scalarMatrix, scalarState, timeOrderedInsertionResponse,
      fixedTargetPropagation, Matrix.mulVec, Matrix.mul_apply, dotProduct,
      Fin.sum_univ_one] at atZero

#print axioms runSpectralPair_source
#print axioms runSpectralPair_target_eq_fixed_add_smul_response
#print axioms inv_smul_runSpectralPair_target_sub_zeroScale
#print axioms timeOrderedInsertionResponse_map_withoutInsertion
#print axioms same_fixed_terminal_different_insertion_response

end

end TimeOrderedSpectralInsertion

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
