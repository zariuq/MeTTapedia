import Mettapedia.MachineLearning.NeuralNetworks.ForgettingGeometry.RankOneTrichotomy
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.Matrix.PosDef

/-!
# Elementary holonomy boundary for quadratic curricula

For a product of symmetric positive-definite damping factors, a trivial
orthogonal factor in the polar decomposition forces the product itself to be
symmetric.  Because the current library does not expose the required matrix
polar decomposition, this file formalizes that exact elementary symmetry
criterion as `TrivialRotationProxy`; it does not manufacture a polar factor.

For two symmetric factors the proxy is equivalent to commutation.  Pairwise
commuting quadratic Hessians therefore give a trivial two-task proxy after
matrix exponentiation.  The converse does not extend to arbitrary curricula:
a noncommuting palindrome `A * B * A` is symmetric.  This is a formal
counterexample to the unrestricted proposed biconditional.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.ForgettingGeometry

open NormedSpace

/-- Elementary criterion corresponding to zero polar rotation when the
monodromy is known to be positive definite. -/
def TrivialRotationProxy {Index : Type*}
    (monodromy : Matrix Index Index ℝ) : Prop :=
  monodromy.IsSymm

/-- A continuous-time quadratic damping factor `exp (-t H)`. -/
noncomputable def quadraticDampingFactor {Index : Type*}
    [Fintype Index] [DecidableEq Index]
    (time : ℝ) (curvature : Matrix Index Index ℝ) :
    Matrix Index Index ℝ :=
  exp ((-time) • curvature)

/-- A symmetric Hessian has a symmetric exponential damping factor. -/
theorem quadraticDampingFactor_isSymm {Index : Type*}
    [Fintype Index] [DecidableEq Index]
    (time : ℝ) (curvature : Matrix Index Index ℝ)
    (hcurvature : curvature.IsSymm) :
    (quadraticDampingFactor time curvature).IsSymm := by
  simpa [quadraticDampingFactor] using (hcurvature.smul (-time)).exp

/-- Exact two-factor theorem: the product of two symmetric matrices has
trivial rotation proxy exactly when the factors commute. -/
theorem twoSymmetricFactors_trivialRotationProxy_iff_commute
    {Index : Type*} [Fintype Index]
    (first second : Matrix Index Index ℝ)
    (hfirst : first.IsSymm) (hsecond : second.IsSymm) :
    TrivialRotationProxy (first * second) ↔ Commute first second := by
  unfold TrivialRotationProxy Matrix.IsSymm Commute SemiconjBy
  rw [Matrix.transpose_mul, hfirst.eq, hsecond.eq]
  exact eq_comm

/-- Commuting Hessians yield commuting exponential factors and hence a
trivial two-task rotation proxy. -/
theorem commutingHessians_twoTaskMonodromy_trivialRotationProxy
    {Index : Type*} [Fintype Index] [DecidableEq Index]
    (firstTime secondTime : ℝ)
    (first second : Matrix Index Index ℝ)
    (hfirst : first.IsSymm) (hsecond : second.IsSymm)
    (hcommute : Commute first second) :
    TrivialRotationProxy
      (quadraticDampingFactor firstTime first *
        quadraticDampingFactor secondTime second) := by
  apply (twoSymmetricFactors_trivialRotationProxy_iff_commute
    (quadraticDampingFactor firstTime first)
    (quadraticDampingFactor secondTime second)
    (quadraticDampingFactor_isSymm firstTime first hfirst)
    (quadraticDampingFactor_isSymm secondTime second hsecond)).2
  simpa [quadraticDampingFactor] using
    ((hcommute.smul_left (-firstTime)).smul_right (-secondTime)).exp

/-! ## Scalar identity shifts -/

/-- Adding scalar identity curvature scales the damping factor by the scalar
exponential.  This is the elementary content behind identity-shift
invariance of polar rotation. -/
theorem quadraticDampingFactor_add_identity
    {Index : Type*} [Fintype Index] [DecidableEq Index]
    (time shift : ℝ) (curvature : Matrix Index Index ℝ) :
    quadraticDampingFactor time
        (curvature + shift • (1 : Matrix Index Index ℝ)) =
      exp (-time * shift) • quadraticDampingFactor time curvature := by
  unfold quadraticDampingFactor
  have hsplit :
      (-time) • (curvature + shift • (1 : Matrix Index Index ℝ)) =
        (-time) • curvature +
          (-time * shift) • (1 : Matrix Index Index ℝ) := by
    rw [smul_add, smul_smul]
  rw [hsplit]
  have hcommute : Commute
      ((-time) • curvature)
      ((-time * shift) • (1 : Matrix Index Index ℝ)) := by
    exact (Commute.one_right ((-time) • curvature)).smul_right
      (-time * shift)
  rw [Matrix.exp_add_of_commute _ _ hcommute]
  have hscalar :
      exp ((-time * shift) • (1 : Matrix Index Index ℝ)) =
        exp (-time * shift) • (1 : Matrix Index Index ℝ) := by
    calc
      exp ((-time * shift) • (1 : Matrix Index Index ℝ)) =
          exp (Matrix.diagonal (fun _ : Index => -time * shift)) := by
        congr 1
        ext i j
        by_cases hij : i = j
        · subst j
          simp
        · simp [hij]
      _ = Matrix.diagonal (fun _ : Index => exp (-time * shift)) := by
        rw [Matrix.exp_diagonal]
        simp [Pi.exp_def]
      _ = exp (-time * shift) • (1 : Matrix Index Index ℝ) := by
        ext i j
        by_cases hij : i = j
        · subst j
          simp
        · simp [hij]
  rw [hscalar]
  simp

/-- Multiplying a monodromy by a nonzero scalar leaves the elementary
rotation proxy unchanged. -/
theorem scalar_smul_trivialRotationProxy_iff
    {Index : Type*} (scale : ℝ) (hscale : scale ≠ 0)
    (monodromy : Matrix Index Index ℝ) :
    TrivialRotationProxy (scale • monodromy) ↔
      TrivialRotationProxy monodromy := by
  letI := invertibleOfNonzero hscale
  exact Matrix.isSymm_smul_iff scale

/-- Adding independent scalar identity shifts to both task Hessians leaves
the elementary two-task rotation criterion unchanged. -/
theorem twoTaskMonodromy_add_identities_trivialRotationProxy_iff
    {Index : Type*} [Fintype Index] [DecidableEq Index]
    (firstTime secondTime firstShift secondShift : ℝ)
    (first second : Matrix Index Index ℝ) :
    TrivialRotationProxy
        (quadraticDampingFactor firstTime
            (first + firstShift • (1 : Matrix Index Index ℝ)) *
          quadraticDampingFactor secondTime
            (second + secondShift • (1 : Matrix Index Index ℝ))) ↔
      TrivialRotationProxy
        (quadraticDampingFactor firstTime first *
          quadraticDampingFactor secondTime second) := by
  rw [quadraticDampingFactor_add_identity,
    quadraticDampingFactor_add_identity]
  rw [smul_mul_smul]
  apply scalar_smul_trivialRotationProxy_iff
  exact mul_ne_zero (isUnit_exp _).ne_zero (isUnit_exp _).ne_zero

/-! ## The longer-curriculum counterexample -/

/-- First positive-definite symmetric factor in the palindrome fixture. -/
noncomputable def palindromeFactorA : Matrix (Fin 2) (Fin 2) ℝ :=
  !![2, 0; 0, 1]

/-- Second positive-definite symmetric factor in the palindrome fixture. -/
noncomputable def palindromeFactorB : Matrix (Fin 2) (Fin 2) ℝ :=
  !![2, 1; 1, 2]

theorem palindromeFactorA_posDef : palindromeFactorA.PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · ext i j
    fin_cases i <;> fin_cases j <;> norm_num [palindromeFactorA]
  · intro x hx
    simp [palindromeFactorA, dotProduct, Matrix.mulVec, Fin.sum_univ_two]
    have hcoordinate : x 0 ≠ 0 ∨ x 1 ≠ 0 := by
      by_contra h
      push Not at h
      apply hx
      funext i
      fin_cases i <;> simp [h.1, h.2]
    rcases hcoordinate with h0 | h1
    · nlinarith [sq_pos_of_ne_zero h0, sq_nonneg (x 1)]
    · nlinarith [sq_nonneg (x 0), sq_pos_of_ne_zero h1]

theorem palindromeFactorB_posDef : palindromeFactorB.PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · ext i j
    fin_cases i <;> fin_cases j <;> norm_num [palindromeFactorB]
  · intro x hx
    simp [palindromeFactorB, dotProduct, Matrix.mulVec, Fin.sum_univ_two]
    have hcoordinate : x 0 ≠ 0 ∨ x 1 ≠ 0 := by
      by_contra h
      push Not at h
      apply hx
      funext i
      fin_cases i <;> simp [h.1, h.2]
    rcases hcoordinate with h0 | h1
    · nlinarith [sq_pos_of_ne_zero h0, sq_nonneg (x 0 + x 1)]
    · nlinarith [sq_pos_of_ne_zero h1, sq_nonneg (x 0 + x 1)]

/-- The positive-definite factors in the fixture do not commute. -/
theorem palindromeFactors_noncommuting :
    ¬ Commute palindromeFactorA palindromeFactorB := by
  intro hcommute
  have h01 := congrArg (fun matrix => matrix 0 1) hcommute.eq
  norm_num [palindromeFactorA, palindromeFactorB,
    Matrix.mul_apply, Fin.sum_univ_two] at h01

/-- Nevertheless, their three-step palindrome has trivial rotation proxy. -/
theorem noncommutingPalindrome_trivialRotationProxy :
    TrivialRotationProxy
      (palindromeFactorA * palindromeFactorB * palindromeFactorA) := by
  unfold TrivialRotationProxy
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [palindromeFactorA, palindromeFactorB,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- Refutation of the unrestricted longer-curriculum converse: trivial
rotation proxy does not imply pairwise factor commutation, even for explicit
positive-definite symmetric factors. -/
theorem trivialRotationProxy_does_not_imply_pairwiseCommute_negativeExample :
    palindromeFactorA.PosDef ∧ palindromeFactorB.PosDef ∧
      TrivialRotationProxy
        (palindromeFactorA * palindromeFactorB * palindromeFactorA) ∧
      ¬ Commute palindromeFactorA palindromeFactorB :=
  ⟨palindromeFactorA_posDef, palindromeFactorB_posDef,
    noncommutingPalindrome_trivialRotationProxy,
    palindromeFactors_noncommuting⟩

#print axioms twoSymmetricFactors_trivialRotationProxy_iff_commute
#print axioms commutingHessians_twoTaskMonodromy_trivialRotationProxy
#print axioms quadraticDampingFactor_add_identity
#print axioms twoTaskMonodromy_add_identities_trivialRotationProxy_iff
#print axioms trivialRotationProxy_does_not_imply_pairwiseCommute_negativeExample

end Mettapedia.MachineLearning.NeuralNetworks.ForgettingGeometry
