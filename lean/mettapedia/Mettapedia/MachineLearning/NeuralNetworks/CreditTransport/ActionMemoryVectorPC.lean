import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.ActionMemoryLocalPCEnergy
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.CyclicEPCRefinement
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Width-generic local predictive coding

This module is the exact-real, width-generic linear-quadratic bridge for the
two-node active/evidence reasoner.  Hidden and readout spaces are arbitrary
real Hilbert spaces.  Dense runtime matrices are represented by continuous
linear maps; no coordinatewise independence assumption is made.

The results establish the vector residual energy, its two local state
gradients, contraction and unique equilibrium of the damped coupled map, and
the support boundary of a masked cross-entropy readout.  A nonzero width-32
fixture instantiates the generic statements.

These theorems characterize the update form.  They do not certify floating-
point executions or optimizer transitions.  Such transitions require a
source-bound conformance fixture and the realized-displacement admission gate.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
namespace ActionMemoryVectorPC

noncomputable section

open scoped InnerProductSpace
open InnerProduct

universe uH uO

variable {Hidden : Type uH} {Output : Type uO}
variable [NormedAddCommGroup Hidden] [InnerProductSpace ℝ Hidden] [CompleteSpace Hidden]
variable [NormedAddCommGroup Output] [InnerProductSpace ℝ Output] [CompleteSpace Output]

abbrev VectorTwoNodeState (Hidden : Type uH) := Hidden × Hidden

/-! ## Precision-weighted vector energy -/

structure VectorPCProblem (Hidden : Type uH) (Output : Type uO)
    [NormedAddCommGroup Hidden] [InnerProductSpace ℝ Hidden]
    [NormedAddCommGroup Output] [InnerProductSpace ℝ Output] where
  activeDrive : Hidden
  evidenceDrive : Hidden
  activeCoupling : Hidden →L[ℝ] Hidden
  evidenceCoupling : Hidden →L[ℝ] Hidden
  taskReadout : Hidden →L[ℝ] Output
  taskTarget : Output
  activePrecision : ℝ
  evidencePrecision : ℝ
  taskPrecision : ℝ

def VectorPCProblem.activeResidual
    (problem : VectorPCProblem Hidden Output)
    (state : VectorTwoNodeState Hidden) : Hidden :=
  state.1 - problem.activeDrive - problem.activeCoupling state.2

def VectorPCProblem.evidenceResidual
    (problem : VectorPCProblem Hidden Output)
    (state : VectorTwoNodeState Hidden) : Hidden :=
  state.2 - problem.evidenceDrive - problem.evidenceCoupling state.1

def VectorPCProblem.taskResidual
    (problem : VectorPCProblem Hidden Output)
    (state : VectorTwoNodeState Hidden) : Output :=
  problem.taskReadout state.1 - problem.taskTarget

/-- Precision-weighted local residual energy with a task readout. -/
def VectorPCProblem.energy
    (problem : VectorPCProblem Hidden Output)
    (state : VectorTwoNodeState Hidden) : ℝ :=
  problem.activePrecision / 2 * ‖problem.activeResidual state‖ ^ 2 +
    problem.evidencePrecision / 2 * ‖problem.evidenceResidual state‖ ^ 2 +
    problem.taskPrecision / 2 * ‖problem.taskResidual state‖ ^ 2

/-- The active-state gradient uses only incident residuals and adjoints of the
two incident linear maps. -/
def VectorPCProblem.activeStateGradient
    (problem : VectorPCProblem Hidden Output)
    (state : VectorTwoNodeState Hidden) : Hidden :=
  problem.activePrecision • problem.activeResidual state -
    problem.evidencePrecision •
      problem.evidenceCoupling.adjoint (problem.evidenceResidual state) +
    problem.taskPrecision • problem.taskReadout.adjoint (problem.taskResidual state)

/-- The evidence-state gradient is likewise local to its two incident
residual terms. -/
def VectorPCProblem.evidenceStateGradient
    (problem : VectorPCProblem Hidden Output)
    (state : VectorTwoNodeState Hidden) : Hidden :=
  problem.evidencePrecision • problem.evidenceResidual state -
    problem.activePrecision •
      problem.activeCoupling.adjoint (problem.activeResidual state)

private theorem hasDerivAt_weightedNormSq_line
    {Space : Type*} [NormedAddCommGroup Space] [InnerProductSpace ℝ Space]
    (precision : ℝ) (residual direction : Space) :
    HasDerivAt
      (fun time : ℝ => precision / 2 * ‖residual + time • direction‖ ^ 2)
      (precision * ⟪residual, direction⟫_ℝ) 0 := by
  have hline : HasDerivAt (fun time : ℝ => residual + time • direction) direction 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const direction).const_add residual
  have hweighted :
      HasDerivAt
        (fun time : ℝ => precision / 2 * ‖residual + time • direction‖ ^ 2)
        (precision / 2 * (2 * ⟪residual, direction⟫_ℝ)) 0 := by
    simpa using hline.norm_sq.const_mul (precision / 2)
  apply hweighted.congr_deriv
  ring

omit [CompleteSpace Hidden] [CompleteSpace Output] in
@[simp] theorem activeResidual_activeLine
    (problem : VectorPCProblem Hidden Output)
    (state : VectorTwoNodeState Hidden) (direction : Hidden) (time : ℝ) :
    problem.activeResidual (state.1 + time • direction, state.2) =
      problem.activeResidual state + time • direction := by
  simp [VectorPCProblem.activeResidual]
  module

omit [CompleteSpace Hidden] [CompleteSpace Output] in
@[simp] theorem evidenceResidual_activeLine
    (problem : VectorPCProblem Hidden Output)
    (state : VectorTwoNodeState Hidden) (direction : Hidden) (time : ℝ) :
    problem.evidenceResidual (state.1 + time • direction, state.2) =
      problem.evidenceResidual state +
        time • (-(problem.evidenceCoupling direction)) := by
  simp [VectorPCProblem.evidenceResidual, map_add, map_smul]
  module

omit [CompleteSpace Hidden] [CompleteSpace Output] in
@[simp] theorem taskResidual_activeLine
    (problem : VectorPCProblem Hidden Output)
    (state : VectorTwoNodeState Hidden) (direction : Hidden) (time : ℝ) :
    problem.taskResidual (state.1 + time • direction, state.2) =
      problem.taskResidual state + time • problem.taskReadout direction := by
  simp [VectorPCProblem.taskResidual, map_add, map_smul]
  module

omit [CompleteSpace Hidden] [CompleteSpace Output] in
@[simp] theorem activeResidual_evidenceLine
    (problem : VectorPCProblem Hidden Output)
    (state : VectorTwoNodeState Hidden) (direction : Hidden) (time : ℝ) :
    problem.activeResidual (state.1, state.2 + time • direction) =
      problem.activeResidual state + time • (-(problem.activeCoupling direction)) := by
  simp [VectorPCProblem.activeResidual, map_add, map_smul]
  module

omit [CompleteSpace Hidden] [CompleteSpace Output] in
@[simp] theorem evidenceResidual_evidenceLine
    (problem : VectorPCProblem Hidden Output)
    (state : VectorTwoNodeState Hidden) (direction : Hidden) (time : ℝ) :
    problem.evidenceResidual (state.1, state.2 + time • direction) =
      problem.evidenceResidual state + time • direction := by
  simp [VectorPCProblem.evidenceResidual]
  module

omit [CompleteSpace Hidden] [CompleteSpace Output] in
@[simp] theorem taskResidual_evidenceLine
    (problem : VectorPCProblem Hidden Output)
    (state : VectorTwoNodeState Hidden) (direction : Hidden) (time : ℝ) :
    problem.taskResidual (state.1, state.2 + time • direction) =
      problem.taskResidual state := by
  rfl

/-- The declared active local form is the exact directional derivative of the
full vector energy. -/
theorem VectorPCProblem.hasDerivAt_energy_activeLine
    (problem : VectorPCProblem Hidden Output)
    (state : VectorTwoNodeState Hidden) (direction : Hidden) :
    HasDerivAt
      (fun time : ℝ => problem.energy (state.1 + time • direction, state.2))
      ⟪problem.activeStateGradient state, direction⟫_ℝ 0 := by
  have hactive := hasDerivAt_weightedNormSq_line problem.activePrecision
    (problem.activeResidual state) direction
  have hevidence := hasDerivAt_weightedNormSq_line problem.evidencePrecision
    (problem.evidenceResidual state) (-(problem.evidenceCoupling direction))
  have htask := hasDerivAt_weightedNormSq_line problem.taskPrecision
    (problem.taskResidual state) (problem.taskReadout direction)
  have hsum := hactive.add hevidence |>.add htask
  have hfunction :
      (fun time : ℝ => problem.energy (state.1 + time • direction, state.2)) =
        ((fun time : ℝ => problem.activePrecision / 2 *
            ‖problem.activeResidual state + time • direction‖ ^ 2) +
          (fun time : ℝ => problem.evidencePrecision / 2 *
            ‖problem.evidenceResidual state +
              time • (-(problem.evidenceCoupling direction))‖ ^ 2)) +
          (fun time : ℝ => problem.taskPrecision / 2 *
            ‖problem.taskResidual state + time • problem.taskReadout direction‖ ^ 2) := by
    funext time
    simp [VectorPCProblem.energy]
  have hderivative :
      ⟪problem.activeStateGradient state, direction⟫_ℝ =
        problem.activePrecision * ⟪problem.activeResidual state, direction⟫_ℝ +
          problem.evidencePrecision *
            ⟪problem.evidenceResidual state,
              -(problem.evidenceCoupling direction)⟫_ℝ +
          problem.taskPrecision *
            ⟪problem.taskResidual state, problem.taskReadout direction⟫_ℝ := by
    rw [VectorPCProblem.activeStateGradient, inner_add_left, inner_sub_left,
      real_inner_smul_left, real_inner_smul_left, real_inner_smul_left,
      ContinuousLinearMap.adjoint_inner_left,
      ContinuousLinearMap.adjoint_inner_left]
    rw [inner_neg_right]
    ring
  rw [hfunction, hderivative]
  exact hsum

omit [CompleteSpace Output] in
/-- The declared evidence local form is the exact directional derivative of
the full vector energy. -/
theorem VectorPCProblem.hasDerivAt_energy_evidenceLine
    (problem : VectorPCProblem Hidden Output)
    (state : VectorTwoNodeState Hidden) (direction : Hidden) :
    HasDerivAt
      (fun time : ℝ => problem.energy (state.1, state.2 + time • direction))
      ⟪problem.evidenceStateGradient state, direction⟫_ℝ 0 := by
  have hactive := hasDerivAt_weightedNormSq_line problem.activePrecision
    (problem.activeResidual state) (-(problem.activeCoupling direction))
  have hevidence := hasDerivAt_weightedNormSq_line problem.evidencePrecision
    (problem.evidenceResidual state) direction
  have htask : HasDerivAt
      (fun _time : ℝ => problem.taskPrecision / 2 * ‖problem.taskResidual state‖ ^ 2)
      0 0 := hasDerivAt_const _ _
  have hsum := hactive.add hevidence |>.add htask
  have hfunction :
      (fun time : ℝ => problem.energy (state.1, state.2 + time • direction)) =
        ((fun time : ℝ => problem.activePrecision / 2 *
            ‖problem.activeResidual state +
              time • (-(problem.activeCoupling direction))‖ ^ 2) +
          (fun time : ℝ => problem.evidencePrecision / 2 *
            ‖problem.evidenceResidual state + time • direction‖ ^ 2)) +
          (fun _time : ℝ => problem.taskPrecision / 2 *
            ‖problem.taskResidual state‖ ^ 2) := by
    funext time
    simp [VectorPCProblem.energy]
  have hderivative :
      ⟪problem.evidenceStateGradient state, direction⟫_ℝ =
        problem.activePrecision *
            ⟪problem.activeResidual state,
              -(problem.activeCoupling direction)⟫_ℝ +
          problem.evidencePrecision *
            ⟪problem.evidenceResidual state, direction⟫_ℝ + 0 := by
    rw [VectorPCProblem.evidenceStateGradient, inner_sub_left,
      real_inner_smul_left, real_inner_smul_left,
      ContinuousLinearMap.adjoint_inner_left]
    rw [inner_neg_right]
    ring
  rw [hfunction, hderivative]
  exact hsum

/-! ## Damped coupled-map contraction and equilibrium -/

def vectorCandidateMap
    (activeDrive evidenceDrive : Hidden)
    (activeCoupling evidenceCoupling : Hidden →L[ℝ] Hidden)
    (state : VectorTwoNodeState Hidden) : VectorTwoNodeState Hidden :=
  (activeDrive + activeCoupling state.2,
    evidenceDrive + evidenceCoupling state.1)

def vectorDampedMap
    (damping : ℝ) (activeDrive evidenceDrive : Hidden)
    (activeCoupling evidenceCoupling : Hidden →L[ℝ] Hidden)
    (state : VectorTwoNodeState Hidden) : VectorTwoNodeState Hidden :=
  let candidate := vectorCandidateMap activeDrive evidenceDrive activeCoupling
    evidenceCoupling state
  ((1 - damping) • state.1 + damping • candidate.1,
    (1 - damping) • state.2 + damping • candidate.2)

def vectorBlockDistance
    (left right : VectorTwoNodeState Hidden) : ℝ :=
  max ‖left.1 - right.1‖ ‖left.2 - right.2‖

def vectorCouplingFactor
    (activeCoupling evidenceCoupling : Hidden →L[ℝ] Hidden) : ℝ :=
  max ‖activeCoupling‖ ‖evidenceCoupling‖

def vectorDampedFactor
    (damping : ℝ)
    (activeCoupling evidenceCoupling : Hidden →L[ℝ] Hidden) : ℝ :=
  (1 - damping) + damping * vectorCouplingFactor activeCoupling evidenceCoupling

/-- Off-diagonal coupling as one continuous linear operator on the product
state.  This is the cycle operator consumed by `CyclicEPCRefinement`. -/
def vectorCouplingOperator
    (activeCoupling evidenceCoupling : Hidden →L[ℝ] Hidden) :
    VectorTwoNodeState Hidden →L[ℝ] VectorTwoNodeState Hidden :=
  (activeCoupling.comp (ContinuousLinearMap.snd ℝ Hidden Hidden)).prod
    (evidenceCoupling.comp (ContinuousLinearMap.fst ℝ Hidden Hidden))

omit [CompleteSpace Hidden] in
@[simp] theorem vectorCouplingOperator_apply
    (activeCoupling evidenceCoupling : Hidden →L[ℝ] Hidden)
    (state : VectorTwoNodeState Hidden) :
    vectorCouplingOperator activeCoupling evidenceCoupling state =
      (activeCoupling state.2, evidenceCoupling state.1) := by
  rfl

omit [CompleteSpace Hidden] in
/-- The reasoner's damped coupled update is exactly the generic damped cycle
step applied to the off-diagonal product operator. -/
theorem vectorDampedMap_eq_dampedCycleStep
    (damping : ℝ) (activeDrive evidenceDrive : Hidden)
    (activeCoupling evidenceCoupling : Hidden →L[ℝ] Hidden)
    (state : VectorTwoNodeState Hidden) :
    vectorDampedMap damping activeDrive evidenceDrive activeCoupling
        evidenceCoupling state =
      CyclicEPCRefinement.dampedCycleStep damping
        (vectorCouplingOperator activeCoupling evidenceCoupling)
        (activeDrive, evidenceDrive) state := by
  ext <;>
    simp [vectorDampedMap, vectorCandidateMap,
      CyclicEPCRefinement.dampedCycleStep,
      CyclicEPCRefinement.dampedCycleOperator_apply] <;>
    module

omit [CompleteSpace Hidden] in
/-- Hence every solution of the undamped coupled equilibrium equation is a
fixed point of every damped presentation. -/
theorem vectorDampedMap_fixed_of_cycleSolution
    (damping : ℝ) (activeDrive evidenceDrive : Hidden)
    (activeCoupling evidenceCoupling : Hidden →L[ℝ] Hidden)
    (state : VectorTwoNodeState Hidden)
    (solution :
      state - vectorCouplingOperator activeCoupling evidenceCoupling state =
        (activeDrive, evidenceDrive)) :
    vectorDampedMap damping activeDrive evidenceDrive activeCoupling
      evidenceCoupling state = state := by
  rw [vectorDampedMap_eq_dampedCycleStep]
  unfold CyclicEPCRefinement.dampedCycleStep
  have scaled := CyclicEPCRefinement.dampedCycle_exactSolution damping
    (vectorCouplingOperator activeCoupling evidenceCoupling)
    (activeDrive, evidenceDrive) state solution
  rw [← scaled]
  abel

omit [CompleteSpace Hidden] in
theorem vectorCandidateMap_contracts
    (activeDrive evidenceDrive : Hidden)
    (activeCoupling evidenceCoupling : Hidden →L[ℝ] Hidden)
    (left right : VectorTwoNodeState Hidden) :
    vectorBlockDistance
        (vectorCandidateMap activeDrive evidenceDrive activeCoupling evidenceCoupling left)
        (vectorCandidateMap activeDrive evidenceDrive activeCoupling evidenceCoupling right) ≤
      vectorCouplingFactor activeCoupling evidenceCoupling *
        vectorBlockDistance left right := by
  apply max_le
  · calc
      ‖(vectorCandidateMap activeDrive evidenceDrive activeCoupling evidenceCoupling left).1 -
          (vectorCandidateMap activeDrive evidenceDrive activeCoupling evidenceCoupling right).1‖ =
          ‖activeCoupling (left.2 - right.2)‖ := by
            simp [vectorCandidateMap, map_sub]
      _ ≤ ‖activeCoupling‖ * ‖left.2 - right.2‖ :=
        activeCoupling.le_opNorm _
      _ ≤ vectorCouplingFactor activeCoupling evidenceCoupling *
          ‖left.2 - right.2‖ := by
        exact mul_le_mul_of_nonneg_right
          (le_max_left ‖activeCoupling‖ ‖evidenceCoupling‖)
          (norm_nonneg _)
      _ ≤ vectorCouplingFactor activeCoupling evidenceCoupling *
          vectorBlockDistance left right := by
        exact mul_le_mul_of_nonneg_left
          (le_max_right ‖left.1 - right.1‖ ‖left.2 - right.2‖)
          ((norm_nonneg activeCoupling).trans
            (le_max_left ‖activeCoupling‖ ‖evidenceCoupling‖))
  · calc
      ‖(vectorCandidateMap activeDrive evidenceDrive activeCoupling evidenceCoupling left).2 -
          (vectorCandidateMap activeDrive evidenceDrive activeCoupling evidenceCoupling right).2‖ =
          ‖evidenceCoupling (left.1 - right.1)‖ := by
            simp [vectorCandidateMap, map_sub]
      _ ≤ ‖evidenceCoupling‖ * ‖left.1 - right.1‖ :=
        evidenceCoupling.le_opNorm _
      _ ≤ vectorCouplingFactor activeCoupling evidenceCoupling *
          ‖left.1 - right.1‖ := by
        exact mul_le_mul_of_nonneg_right
          (le_max_right ‖activeCoupling‖ ‖evidenceCoupling‖)
          (norm_nonneg _)
      _ ≤ vectorCouplingFactor activeCoupling evidenceCoupling *
          vectorBlockDistance left right := by
        exact mul_le_mul_of_nonneg_left
          (le_max_left ‖left.1 - right.1‖ ‖left.2 - right.2‖)
          ((norm_nonneg activeCoupling).trans
            (le_max_left ‖activeCoupling‖ ‖evidenceCoupling‖))

omit [CompleteSpace Hidden] in
theorem vectorDampedMap_contracts
    {damping : ℝ} (hdamping0 : 0 ≤ damping) (hdamping1 : damping ≤ 1)
    (activeDrive evidenceDrive : Hidden)
    (activeCoupling evidenceCoupling : Hidden →L[ℝ] Hidden)
    (left right : VectorTwoNodeState Hidden) :
    vectorBlockDistance
        (vectorDampedMap damping activeDrive evidenceDrive activeCoupling evidenceCoupling left)
        (vectorDampedMap damping activeDrive evidenceDrive activeCoupling evidenceCoupling right) ≤
      vectorDampedFactor damping activeCoupling evidenceCoupling *
        vectorBlockDistance left right := by
  let κ := vectorCouplingFactor activeCoupling evidenceCoupling
  have hκ : 0 ≤ κ := (norm_nonneg activeCoupling).trans (le_max_left _ _)
  have hcandidate := vectorCandidateMap_contracts activeDrive evidenceDrive
    activeCoupling evidenceCoupling left right
  apply max_le
  · calc
      _ ≤ ‖(1 - damping) • (left.1 - right.1)‖ +
          ‖damping •
            ((vectorCandidateMap activeDrive evidenceDrive activeCoupling evidenceCoupling left).1 -
              (vectorCandidateMap activeDrive evidenceDrive activeCoupling evidenceCoupling right).1)‖ := by
        simpa [vectorDampedMap, sub_eq_add_neg, add_assoc, add_left_comm,
          add_comm, smul_add, smul_neg] using
          norm_add_le ((1 - damping) • (left.1 - right.1))
            (damping •
              ((vectorCandidateMap activeDrive evidenceDrive activeCoupling evidenceCoupling left).1 -
                (vectorCandidateMap activeDrive evidenceDrive activeCoupling evidenceCoupling right).1))
      _ ≤ (1 - damping) * vectorBlockDistance left right +
          damping * (κ * vectorBlockDistance left right) := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs,
          Real.norm_eq_abs, abs_of_nonneg hdamping0,
          abs_of_nonneg (sub_nonneg.mpr hdamping1)]
        gcongr
        · exact le_max_left _ _
        · exact (le_max_left _ _).trans hcandidate
      _ = vectorDampedFactor damping activeCoupling evidenceCoupling *
          vectorBlockDistance left right := by
        simp [vectorDampedFactor, κ]
        ring
  · calc
      _ ≤ ‖(1 - damping) • (left.2 - right.2)‖ +
          ‖damping •
            ((vectorCandidateMap activeDrive evidenceDrive activeCoupling evidenceCoupling left).2 -
              (vectorCandidateMap activeDrive evidenceDrive activeCoupling evidenceCoupling right).2)‖ := by
        simpa [vectorDampedMap, sub_eq_add_neg, add_assoc, add_left_comm,
          add_comm, smul_add, smul_neg] using
          norm_add_le ((1 - damping) • (left.2 - right.2))
            (damping •
              ((vectorCandidateMap activeDrive evidenceDrive activeCoupling evidenceCoupling left).2 -
                (vectorCandidateMap activeDrive evidenceDrive activeCoupling evidenceCoupling right).2))
      _ ≤ (1 - damping) * vectorBlockDistance left right +
          damping * (κ * vectorBlockDistance left right) := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs,
          Real.norm_eq_abs, abs_of_nonneg hdamping0,
          abs_of_nonneg (sub_nonneg.mpr hdamping1)]
        gcongr
        · exact le_max_right _ _
        · exact (le_max_right _ _).trans hcandidate
      _ = vectorDampedFactor damping activeCoupling evidenceCoupling *
          vectorBlockDistance left right := by
        simp [vectorDampedFactor, κ]
        ring

omit [CompleteSpace Hidden] in
theorem vectorDampedMap_contracting
    {damping : ℝ} (hdamping0 : 0 ≤ damping) (hdamping1 : damping ≤ 1)
    (activeDrive evidenceDrive : Hidden)
    (activeCoupling evidenceCoupling : Hidden →L[ℝ] Hidden)
    (hfactor0 : 0 ≤ vectorDampedFactor damping activeCoupling evidenceCoupling)
    (hfactor1 : vectorDampedFactor damping activeCoupling evidenceCoupling < 1) :
    ContractingWith
      ⟨vectorDampedFactor damping activeCoupling evidenceCoupling, hfactor0⟩
      (vectorDampedMap damping activeDrive evidenceDrive activeCoupling
        evidenceCoupling) := by
  constructor
  · exact_mod_cast hfactor1
  · apply LipschitzWith.of_dist_le_mul
    intro left right
    change dist
        (vectorDampedMap damping activeDrive evidenceDrive activeCoupling
          evidenceCoupling left)
        (vectorDampedMap damping activeDrive evidenceDrive activeCoupling
          evidenceCoupling right) ≤
      vectorDampedFactor damping activeCoupling evidenceCoupling * dist left right
    simpa [Prod.dist_eq, dist_eq_norm, Prod.norm_def, vectorBlockDistance] using
      vectorDampedMap_contracts hdamping0 hdamping1 activeDrive evidenceDrive
        activeCoupling evidenceCoupling left right

/-- Operator-norm contraction gives one width-independent equilibrium. -/
theorem vectorDampedMap_existsUnique_equilibrium
    {damping : ℝ} (hdamping0 : 0 ≤ damping) (hdamping1 : damping ≤ 1)
    (activeDrive evidenceDrive : Hidden)
    (activeCoupling evidenceCoupling : Hidden →L[ℝ] Hidden)
    (hfactor0 : 0 ≤ vectorDampedFactor damping activeCoupling evidenceCoupling)
    (hfactor1 : vectorDampedFactor damping activeCoupling evidenceCoupling < 1) :
    ∃! state : VectorTwoNodeState Hidden,
      vectorDampedMap damping activeDrive evidenceDrive activeCoupling
        evidenceCoupling state = state := by
  let factor : NNReal :=
    ⟨vectorDampedFactor damping activeCoupling evidenceCoupling, hfactor0⟩
  let step := vectorDampedMap damping activeDrive evidenceDrive activeCoupling
    evidenceCoupling
  have hcontracting : ContractingWith factor step :=
    vectorDampedMap_contracting hdamping0 hdamping1 activeDrive evidenceDrive
      activeCoupling evidenceCoupling hfactor0 hfactor1
  obtain ⟨target, htarget, _converges, _bound⟩ :=
    hcontracting.exists_fixedPoint (0, 0) (edist_ne_top _ _)
  refine ⟨target, htarget, ?_⟩
  intro other hother
  exact hcontracting.fixedPoint_unique' hother htarget

/-! ## Masked readout support -/

def maskedLogPartition
    {Action : Type*} [Fintype Action] [DecidableEq Action]
    (legal : Finset Action) (logit : Action → ℝ) : ℝ :=
  Real.log (∑ action ∈ legal, Real.exp (logit action))

def maskedCrossEntropy
    {Action : Type*} [Fintype Action] [DecidableEq Action]
    (legal : Finset Action) (target : Action) (logit : Action → ℝ) : ℝ :=
  -logit target + maskedLogPartition legal logit

def maskedCrossEntropyGradient
    {Action : Type*} [Fintype Action] [DecidableEq Action]
    (legal : Finset Action) (target : Action) (logit : Action → ℝ)
    (action : Action) : ℝ :=
  if action ∈ legal then
    Real.exp (logit action) /
        (∑ candidate ∈ legal, Real.exp (logit candidate)) -
      if action = target then 1 else 0
  else 0

@[simp] theorem maskedCrossEntropyGradient_illegal
    {Action : Type*} [Fintype Action] [DecidableEq Action]
    (legal : Finset Action) (target : Action) (logit : Action → ℝ)
    {action : Action} (illegal : action ∉ legal) :
    maskedCrossEntropyGradient legal target logit action = 0 := by
  simp [maskedCrossEntropyGradient, illegal]

theorem maskedCrossEntropy_update_illegal_invariant
    {Action : Type*} [Fintype Action] [DecidableEq Action]
    (legal : Finset Action) {target action : Action}
    (targetLegal : target ∈ legal) (illegal : action ∉ legal)
    (logit : Action → ℝ) (value : ℝ) :
    maskedCrossEntropy legal target (Function.update logit action value) =
      maskedCrossEntropy legal target logit := by
  have targetNe : target ≠ action := by
    intro equal
    subst action
    exact illegal targetLegal
  simp only [maskedCrossEntropy, maskedLogPartition]
  rw [Function.update_of_ne targetNe]
  congr 2
  apply Finset.sum_congr rfl
  intro candidate candidateLegal
  rw [Function.update_of_ne]
  intro equal
  subst candidate
  exact illegal candidateLegal

def maskedGradientStep
    {Action : Type*} [Fintype Action] [DecidableEq Action]
    (rate : ℝ) (legal : Finset Action) (target : Action)
    (logit : Action → ℝ) : Action → ℝ :=
  fun action => logit action -
    rate * maskedCrossEntropyGradient legal target logit action

theorem maskedGradientStep_illegal_coordinate_unchanged
    {Action : Type*} [Fintype Action] [DecidableEq Action]
    (rate : ℝ) (legal : Finset Action) (target : Action)
    (logit : Action → ℝ) {action : Action} (illegal : action ∉ legal) :
    maskedGradientStep rate legal target logit action = logit action := by
  simp [maskedGradientStep, maskedCrossEntropyGradient_illegal _ _ _ illegal]

/-- The actual masked loss is constant along an illegal coordinate, so its
directional derivative there is zero independently of the closed-form
gradient definition. -/
theorem hasDerivAt_maskedCrossEntropy_illegal
    {Action : Type*} [Fintype Action] [DecidableEq Action]
    (legal : Finset Action) {target action : Action}
    (targetLegal : target ∈ legal) (illegal : action ∉ legal)
    (logit : Action → ℝ) :
    HasDerivAt
      (fun time : ℝ => maskedCrossEntropy legal target
        (Function.update logit action (logit action + time))) 0 0 := by
  have constant :
      (fun time : ℝ => maskedCrossEntropy legal target
        (Function.update logit action (logit action + time))) =
        fun _time : ℝ => maskedCrossEntropy legal target logit := by
    funext time
    exact maskedCrossEntropy_update_illegal_invariant legal targetLegal illegal
      logit (logit action + time)
  rw [constant]
  exact hasDerivAt_const _ _

def maskedProbability
    {Action : Type*} [Fintype Action] [DecidableEq Action]
    (legal : Finset Action) (logit : Action → ℝ) (action : Action) : ℝ :=
  if action ∈ legal then
    Real.exp (logit action) /
      (∑ candidate ∈ legal, Real.exp (logit candidate))
  else 0

@[simp] theorem maskedProbability_illegal
    {Action : Type*} [Fintype Action] [DecidableEq Action]
    (legal : Finset Action) (logit : Action → ℝ)
    {action : Action} (illegal : action ∉ legal) :
    maskedProbability legal logit action = 0 := by
  simp [maskedProbability, illegal]

theorem maskedGradientStep_cannot_assign_illegal_probability
    {Action : Type*} [Fintype Action] [DecidableEq Action]
    (rate : ℝ) (legal : Finset Action) (target : Action)
    (logit : Action → ℝ) {action : Action} (illegal : action ∉ legal) :
    maskedProbability legal (maskedGradientStep rate legal target logit) action = 0 := by
  exact maskedProbability_illegal legal _ illegal

/-! ## A nontrivial width-32 instance -/

abbrev Width32 := EuclideanSpace ℝ (Fin 32)

def width32Coupling : Width32 →L[ℝ] Width32 :=
  (1 / 5 : ℝ) • ContinuousLinearMap.id ℝ Width32

def width32Problem : VectorPCProblem Width32 Width32 where
  activeDrive := 0
  evidenceDrive := 0
  activeCoupling := width32Coupling
  evidenceCoupling := width32Coupling
  taskReadout := ContinuousLinearMap.id ℝ Width32
  taskTarget := 0
  activePrecision := 1
  evidencePrecision := 1
  taskPrecision := 1

theorem width32Coupling_ne_zero : width32Coupling ≠ 0 := by
  intro equalZero
  let witness : Width32 :=
    (WithLp.equiv 2 (Fin 32 → ℝ)).symm fun index => if index = 0 then 1 else 0
  have applied := congrArg (fun operator : Width32 →L[ℝ] Width32 => operator witness)
    equalZero
  have coordinate := congrArg (fun vector : Width32 => vector 0) applied
  norm_num [width32Coupling, witness, WithLp.equiv] at coordinate

theorem width32Coupling_norm : ‖width32Coupling‖ = 1 / 5 := by
  simp [width32Coupling, norm_smul]

theorem width32_registered_vector_contraction :
    vectorDampedFactor (Hidden := Width32) (1 / 2)
      width32Coupling width32Coupling = 3 / 5 ∧
    vectorDampedFactor (Hidden := Width32) (1 / 2)
      width32Coupling width32Coupling < 1 := by
  rw [show vectorDampedFactor (Hidden := Width32) (1 / 2)
      width32Coupling width32Coupling =
      (1 - (1 / 2 : ℝ)) + (1 / 2 : ℝ) *
        max ‖width32Coupling‖ ‖width32Coupling‖ by rfl,
    max_self, width32Coupling_norm]
  norm_num

theorem width32_existsUnique_equilibrium :
    ∃! state : VectorTwoNodeState Width32,
      vectorDampedMap (1 / 2) width32Problem.activeDrive
        width32Problem.evidenceDrive width32Problem.activeCoupling
        width32Problem.evidenceCoupling state = state := by
  apply vectorDampedMap_existsUnique_equilibrium
  · norm_num
  · norm_num
  · change 0 ≤ vectorDampedFactor (Hidden := Width32) (1 / 2)
      width32Coupling width32Coupling
    rw [width32_registered_vector_contraction.1]
    norm_num
  · change vectorDampedFactor (Hidden := Width32) (1 / 2)
      width32Coupling width32Coupling < 1
    exact width32_registered_vector_contraction.2

def oneActionLegalMask : Finset Bool := {false}

def bothActionsLegalMask : Finset Bool := Finset.univ

theorem masked_readout_positive_and_negative_fixture :
    maskedCrossEntropyGradient oneActionLegalMask false (fun _ => 0) true = 0 ∧
      maskedCrossEntropyGradient bothActionsLegalMask false (fun _ => 0) true = 1 / 2 := by
  constructor
  · simp [maskedCrossEntropyGradient, oneActionLegalMask]
  · norm_num [maskedCrossEntropyGradient, bothActionsLegalMask]

#print axioms VectorPCProblem.hasDerivAt_energy_activeLine
#print axioms VectorPCProblem.hasDerivAt_energy_evidenceLine
#print axioms vectorDampedMap_contracts
#print axioms vectorDampedMap_eq_dampedCycleStep
#print axioms vectorDampedMap_fixed_of_cycleSolution
#print axioms vectorDampedMap_existsUnique_equilibrium
#print axioms maskedCrossEntropy_update_illegal_invariant
#print axioms hasDerivAt_maskedCrossEntropy_illegal
#print axioms maskedGradientStep_illegal_coordinate_unchanged
#print axioms width32Coupling_ne_zero
#print axioms width32_existsUnique_equilibrium

end
end ActionMemoryVectorPC
end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
