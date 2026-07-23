import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.RoutedCaromCommutingHermitianStability
import Mathlib.Analysis.Matrix.Spectrum

/-!
# Routed CAROM: real commuting Schur stability

This file transports the commuting complex Hermitian certificate to real
matrix dynamics.  Real Schur stability is stated through the spectrum of the
exact complexified matrix endomorphism.  The resulting real energy is positive,
quadratic, and contracts every command with one strict rate.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder

open Function

namespace RoutedCarom

universe uCommand uIndex uReal uComplex

section RealQuadraticRestriction

variable {Command : Type uCommand}
variable {RealState : Type uReal} [AddCommGroup RealState] [Module ℝ RealState]
variable {ComplexState : Type uComplex}
variable [AddCommGroup ComplexState] [Module ℂ ComplexState]

/-- A coordinate-free positive real quadratic energy shared by a family of
real-linear transitions. -/
structure CommonRealQuadraticEnergyLyapunov
    (transition : Command → Module.End ℝ RealState) where
  energy : RealState → ℝ
  rate : ℝ
  rate_nonneg : 0 ≤ rate
  rate_lt_one : rate < 1
  energy_nonneg : ∀ state, 0 ≤ energy state
  energy_pos : ∀ {state}, state ≠ 0 → 0 < energy state
  energy_smul : ∀ (scalar : ℝ) (state : RealState),
    energy (scalar • state) = scalar ^ 2 * energy state
  parallelogram : ∀ first second,
    energy (first + second) + energy (first - second) =
      2 * (energy first + energy second)
  contracts : ∀ command state,
    energy (transition command state) ≤ rate * energy state

/-- Execute a finite schedule of real-linear commands in list order. -/
def runRealEndSchedule
    (transition : Command → Module.End ℝ RealState) :
    List Command → RealState → RealState
  | [], state => state
  | command :: schedule, state =>
      runRealEndSchedule transition schedule (transition command state)

/-- One common positive quadratic energy gives a geometric envelope for every
finite command schedule. -/
theorem CommonRealQuadraticEnergyLyapunov.runRealEndSchedule_energy_le
    {transition : Command → Module.End ℝ RealState}
    (certificate : CommonRealQuadraticEnergyLyapunov transition)
    (schedule : List Command) (initial : RealState) :
    certificate.energy (runRealEndSchedule transition schedule initial) ≤
      certificate.rate ^ schedule.length * certificate.energy initial := by
  induction schedule generalizing initial with
  | nil => simp [runRealEndSchedule]
  | cons command schedule inductionHypothesis =>
      calc
        certificate.energy
            (runRealEndSchedule transition (command :: schedule) initial) =
            certificate.energy
              (runRealEndSchedule transition schedule (transition command initial)) := rfl
        _ ≤ certificate.rate ^ schedule.length *
              certificate.energy (transition command initial) :=
          inductionHypothesis _
        _ ≤ certificate.rate ^ schedule.length *
              (certificate.rate * certificate.energy initial) :=
          mul_le_mul_of_nonneg_left (certificate.contracts command initial)
            (pow_nonneg certificate.rate_nonneg _)
        _ = certificate.rate ^ (command :: schedule).length *
              certificate.energy initial := by
          simp [pow_succ, mul_assoc]

/-- Restrict a complex Hermitian contraction energy along an injective exact
real-linear embedding. -/
noncomputable def CommonHermitianEnergyLyapunov.restrictToReal
    (complexTransition : Command → Module.End ℂ ComplexState)
    (realTransition : Command → Module.End ℝ RealState)
    (embedding : RealState →ₗ[ℝ] ComplexState)
    (embedding_injective : Function.Injective embedding)
    (intertwines : ∀ command state,
      embedding (realTransition command state) =
        complexTransition command (embedding state))
    (certificate : CommonHermitianEnergyLyapunov complexTransition) :
    CommonRealQuadraticEnergyLyapunov realTransition where
  energy := fun state => certificate.energy (embedding state)
  rate := certificate.rate
  rate_nonneg := certificate.rate_nonneg
  rate_lt_one := certificate.rate_lt_one
  energy_nonneg := fun state => certificate.energy_nonneg _
  energy_pos := by
    intro state state_ne_zero
    apply certificate.energy_pos
    intro embedded_zero
    apply state_ne_zero
    apply embedding_injective
    simpa using embedded_zero
  energy_smul := by
    intro scalar state
    rw [map_smul]
    change certificate.energy ((scalar : ℂ) • embedding state) = _
    rw [certificate.energy_smul]
    simp [sq_abs]
  parallelogram := by
    intro first second
    simpa only [map_add, map_sub] using
      certificate.parallelogram (embedding first) (embedding second)
  contracts := by
    intro command state
    rw [intertwines]
    exact certificate.contracts command (embedding state)

#print axioms CommonRealQuadraticEnergyLyapunov
#print axioms CommonRealQuadraticEnergyLyapunov.runRealEndSchedule_energy_le
#print axioms CommonHermitianEnergyLyapunov.restrictToReal

end RealQuadraticRestriction

section MatrixComplexification

variable {Command : Type uCommand} [Fintype Command] [DecidableEq Command]
variable {Index : Type uIndex} [Fintype Index] [DecidableEq Index]

/-- Entrywise complexification of a real square matrix. -/
noncomputable def complexifyMatrix (matrix : Matrix Index Index ℝ) :
    Matrix Index Index ℂ :=
  matrix.map Complex.ofRealHom

/-- The complex-linear endomorphism induced by a complexified real matrix. -/
noncomputable def complexifyMatrixEnd (matrix : Matrix Index Index ℝ) :
    Module.End ℂ (EuclideanSpace ℂ Index) :=
  Matrix.toEuclideanLin (complexifyMatrix matrix)

/-- The original real-linear matrix endomorphism. -/
noncomputable def realMatrixEnd (matrix : Matrix Index Index ℝ) :
    Module.End ℝ (EuclideanSpace ℝ Index) :=
  Matrix.toEuclideanLin matrix

/-- Coordinatewise inclusion of real state vectors into complex state
vectors. -/
noncomputable def realVectorToComplex :
    EuclideanSpace ℝ Index →ₗ[ℝ] EuclideanSpace ℂ Index where
  toFun := fun state => WithLp.toLp 2 fun index => (WithLp.ofLp state index : ℂ)
  map_add' := by
    intro first second
    ext index
    simp
  map_smul' := by
    intro scalar state
    ext index
    simp

omit [Fintype Index] [DecidableEq Index] in
theorem realVectorToComplex_injective :
    Function.Injective (realVectorToComplex (Index := Index)) := by
  intro first second equal_complex
  ext index
  have equal_functions := congrArg WithLp.ofLp equal_complex
  exact Complex.ofReal_injective
    (congrFun equal_functions index)

/-- Complexification exactly preserves real matrix action. -/
theorem realVectorToComplex_intertwines
    (matrix : Matrix Index Index ℝ) (state : EuclideanSpace ℝ Index) :
    realVectorToComplex (realMatrixEnd matrix state) =
      complexifyMatrixEnd matrix (realVectorToComplex state) := by
  ext index
  exact RingHom.map_mulVec Complex.ofRealHom matrix (WithLp.ofLp state) index

/-- Pairwise matrix commutation survives entrywise complexification and the
matrix-to-endomorphism equivalence. -/
theorem complexifyMatrixEnd_commute
    {first second : Matrix Index Index ℝ}
    (commutes : Commute first second) :
    Commute (complexifyMatrixEnd first) (complexifyMatrixEnd second) := by
  rw [Commute, SemiconjBy] at commutes ⊢
  simp only [complexifyMatrixEnd, Module.End.mul_eq_comp]
  rw [← Matrix.toLpLin_mul_same, ← Matrix.toLpLin_mul_same]
  congr 1
  simp only [complexifyMatrix]
  rw [← Matrix.map_mul, ← Matrix.map_mul, commutes]

/-- A finite pairwise-commuting real matrix family whose exact
complexifications are individually Schur-stable has one common Hermitian
energy on the complexified state space. -/
theorem exists_commonHermitianEnergy_complexifyMatrix_of_commuting_schurStable
    (transition : Command → Matrix Index Index ℝ)
    (commutes : Pairwise fun first second =>
      Commute (transition first) (transition second))
    (schurStable : ∀ command,
      spectralRadius ℂ (complexifyMatrixEnd (transition command)) < 1) :
    Nonempty
      (CommonHermitianEnergyLyapunov
        (fun command => complexifyMatrixEnd (transition command))) := by
  let complexTransition : Command → Module.End ℂ (EuclideanSpace ℂ Index) :=
    fun command => complexifyMatrixEnd (transition command)
  change Nonempty (CommonHermitianEnergyLyapunov complexTransition)
  refine exists_commonHermitianEnergy_of_commuting_spectralRadius_lt_one
    (Command := Command) (V := EuclideanSpace ℂ Index) complexTransition ?_ ?_
  · intro first second distinct
    exact complexifyMatrixEnd_commute (commutes distinct)
  · intro command
    exact schurStable command

/-- A finite pairwise-commuting real matrix family whose exact
complexifications are individually Schur-stable has one positive real
quadratic contraction energy shared by all commands. -/
theorem exists_commonRealQuadraticEnergy_of_commuting_schurStable
    (transition : Command → Matrix Index Index ℝ)
    (commutes : Pairwise fun first second =>
      Commute (transition first) (transition second))
    (schurStable : ∀ command,
      spectralRadius ℂ (complexifyMatrixEnd (transition command)) < 1) :
    Nonempty
      (CommonRealQuadraticEnergyLyapunov
        (fun command => realMatrixEnd (transition command))) := by
  obtain ⟨complexCertificate⟩ :=
    exists_commonHermitianEnergy_complexifyMatrix_of_commuting_schurStable
      transition commutes schurStable
  exact ⟨complexCertificate.restrictToReal
    (fun command => complexifyMatrixEnd (transition command))
    (fun command => realMatrixEnd (transition command))
    realVectorToComplex realVectorToComplex_injective
    (fun command state =>
      realVectorToComplex_intertwines (transition command) state)⟩

#print axioms complexifyMatrix
#print axioms complexifyMatrixEnd
#print axioms realMatrixEnd
#print axioms realVectorToComplex_injective
#print axioms realVectorToComplex_intertwines
#print axioms complexifyMatrixEnd_commute
#print axioms exists_commonHermitianEnergy_complexifyMatrix_of_commuting_schurStable
#print axioms exists_commonRealQuadraticEnergy_of_commuting_schurStable

end MatrixComplexification

section RealEnergyFixtures

/-- A one-dimensional half contraction. -/
noncomputable def halfRealEndTransition (_ : Unit) : Module.End ℝ ℝ :=
  (1 / 2 : ℝ) • LinearMap.id

/-- Squared magnitude is a positive quadratic energy for the half
contraction, with the exact energy rate `1/4`. -/
noncomputable def halfRealEndCommonQuadraticEnergy :
    CommonRealQuadraticEnergyLyapunov halfRealEndTransition where
  energy := fun state => state ^ 2
  rate := 1 / 4
  rate_nonneg := by norm_num
  rate_lt_one := by norm_num
  energy_nonneg := fun state => sq_nonneg state
  energy_pos := by
    intro state state_ne_zero
    exact sq_pos_of_ne_zero state_ne_zero
  energy_smul := by
    intro scalar state
    simp [mul_pow]
  parallelogram := by
    intro first second
    ring
  contracts := by
    intro command state
    simp [halfRealEndTransition]
    ring_nf
    exact le_rfl

/-- The schedule theorem is non-vacuous on the half-contraction fixture. -/
theorem halfRealEnd_allSchedules_energy_le
    (schedule : List Unit) (initial : ℝ) :
    halfRealEndCommonQuadraticEnergy.energy
        (runRealEndSchedule halfRealEndTransition schedule initial) ≤
      (1 / 4 : ℝ) ^ schedule.length *
        halfRealEndCommonQuadraticEnergy.energy initial :=
  halfRealEndCommonQuadraticEnergy.runRealEndSchedule_energy_le schedule initial

/-- A unit-modulus real identity command cannot possess a strict positive
quadratic contraction energy. -/
theorem realIdentityTransition_noCommonQuadraticEnergy :
    ¬ Nonempty
      (CommonRealQuadraticEnergyLyapunov
        (fun _ : Unit => (LinearMap.id : Module.End ℝ ℝ))) := by
  rintro ⟨certificate⟩
  have positive : 0 < certificate.energy 1 :=
    certificate.energy_pos one_ne_zero
  have contracts := certificate.contracts () (1 : ℝ)
  simp only [LinearMap.id_apply] at contracts
  have strict := mul_lt_mul_of_pos_right certificate.rate_lt_one positive
  linarith

#print axioms halfRealEndCommonQuadraticEnergy
#print axioms halfRealEnd_allSchedules_energy_le
#print axioms realIdentityTransition_noCommonQuadraticEnergy

end RealEnergyFixtures

end RoutedCarom

end Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder
