import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.RoutedCaromNonlinearCommutation
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.GroupTheory.Perm.Basic

/-!
# Routed CAROM: adjoints and time-symmetric compositions

This file isolates the exact group-theoretic content of adjoint and symmetric
composition methods.  It follows the constructions in Sections 2.1 and 3.3 of
Blanes, Casas, and Murua, *Splitting and composition methods in the numerical
integration of differential equations* (arXiv:0812.0377):

* the adjoint of a step family is its inverse step at negative time;
* composing a half-step with its adjoint half-step is time-symmetric;
* a palindromic scaled composition of a time-symmetric stage is again
  time-symmetric.

The abstraction is a group-valued step family.  For an executable state space,
the group may be a permutation group; for exact numerical flows it may be a
group of invertible maps.  The results concern reversibility only.  They do not
assert numerical order, consistency, convergence, symplecticity, or that an
arbitrary learned phase is invertible.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder

namespace RoutedCarom

universe uGroup

/-- An invertible execution step indexed by a real step parameter. -/
abbrev ReversibleStepFamily (G : Type uGroup) := ℝ → G

section GroupAlgebra

variable {G : Type uGroup} [Group G]

/-- The adjoint family: reverse the step parameter and invert the execution. -/
def stepAdjoint (step : ReversibleStepFamily G) : ReversibleStepFamily G :=
  fun h => (step (-h))⁻¹

/-- Pointwise execution composition.  Multiplication supplies the declared
execution-order convention of `G`. -/
def pointwiseStepComposition
    (first second : ReversibleStepFamily G) : ReversibleStepFamily G :=
  fun h => first h * second h

/-- A step family is time-symmetric when it equals its adjoint at every step. -/
def TimeSymmetric (step : ReversibleStepFamily G) : Prop :=
  ∀ h, stepAdjoint step h = step h

/-- Compose one half-step with the adjoint half-step. -/
noncomputable def adjointPair
    (step : ReversibleStepFamily G) : ReversibleStepFamily G :=
  fun h => step (h / 2) * stepAdjoint step (h / 2)

/-- Compose copies of one stage at coefficient-scaled step sizes. -/
def scaledStageComposition
    (step : ReversibleStepFamily G)
    (coefficients : List ℝ) : ReversibleStepFamily G :=
  fun h => (coefficients.map fun coefficient => step (coefficient * h)).prod

/-- Taking the adjoint twice recovers the original step family. -/
@[simp]
theorem stepAdjoint_stepAdjoint (step : ReversibleStepFamily G) :
    stepAdjoint (stepAdjoint step) = step := by
  funext h
  simp [stepAdjoint]

/-- Adjoint reverses the order of pointwise execution composition. -/
theorem stepAdjoint_pointwiseStepComposition
    (first second : ReversibleStepFamily G) :
    stepAdjoint (pointwiseStepComposition first second) =
      pointwiseStepComposition (stepAdjoint second) (stepAdjoint first) := by
  funext h
  simp [stepAdjoint, pointwiseStepComposition]

/-- Time symmetry is equivalently the usual negative-step inverse law. -/
theorem timeSymmetric_iff_negativeStep_eq_inverse
    (step : ReversibleStepFamily G) :
    TimeSymmetric step ↔ ∀ h, step (-h) = (step h)⁻¹ := by
  constructor
  · intro hs h
    have hh := hs h
    simp only [stepAdjoint] at hh
    rw [← hh]
    simp
  · intro hs h
    simp only [stepAdjoint]
    rw [hs h]
    simp

/-- The method-adjoint half-step construction is exactly time-symmetric. -/
theorem adjointPair_timeSymmetric (step : ReversibleStepFamily G) :
    TimeSymmetric (adjointPair step) := by
  intro h
  change (step (-h / 2) * (step (-(-h / 2)))⁻¹)⁻¹ =
    step (h / 2) * (step (-(h / 2)))⁻¹
  rw [mul_inv_rev]
  simp only [inv_inv]
  congr 2 <;> ring_nf

/-- The adjoint of a scaled composition is the same composition with its
coefficient list reversed, provided that the base stage is time-symmetric. -/
theorem stepAdjoint_scaledStageComposition
    (step : ReversibleStepFamily G)
    (hs : TimeSymmetric step)
    (coefficients : List ℝ) :
    stepAdjoint (scaledStageComposition step coefficients) =
      scaledStageComposition step coefficients.reverse := by
  funext h
  simp only [stepAdjoint, scaledStageComposition, List.prod_inv_reverse,
    List.map_reverse]
  congr 2
  rw [List.map_map]
  apply List.map_congr_left
  intro coefficient _
  change (step (coefficient * -h))⁻¹ = step (coefficient * h)
  rw [show coefficient * -h = -(coefficient * h) by ring]
  simpa only [stepAdjoint] using hs (coefficient * h)

/-- A palindromic scaled composition of a time-symmetric stage is
time-symmetric, without a commutativity assumption on the execution group. -/
theorem palindromic_scaledStageComposition_timeSymmetric
    (step : ReversibleStepFamily G)
    (hs : TimeSymmetric step)
    (coefficients : List ℝ)
    (hpalindrome : coefficients.reverse = coefficients) :
    TimeSymmetric (scaledStageComposition step coefficients) := by
  intro h
  have hfamily :=
    congrFun (stepAdjoint_scaledStageComposition step hs coefficients) h
  simpa [hpalindrome] using hfamily

end GroupAlgebra

/-! ## Positive and negative executable boundaries -/

/-- A noncommuting, individually reversible stage family on three states.
Absolute step size one swaps states zero and one; absolute step size two swaps
states one and two. -/
noncomputable def noncommutingPermutationStage
    (h : ℝ) : Equiv.Perm (Fin 3) :=
  if |h| = 1 then Equiv.swap 0 1
  else if |h| = 2 then Equiv.swap 1 2
  else 1

/-- The noncommuting permutation stage is itself time-symmetric. -/
theorem noncommutingPermutationStage_timeSymmetric :
    TimeSymmetric noncommutingPermutationStage := by
  intro h
  simp only [stepAdjoint, noncommutingPermutationStage, abs_neg]
  by_cases h1 : |h| = 1
  · simp [h1, Equiv.swap_inv]
  by_cases h2 : |h| = 2
  · simp [h2, Equiv.swap_inv]
  · simp [h1, h2]

/-- Palindromic composition remains time-symmetric even when its two
nontrivial stages do not commute. -/
theorem palindromic_noncommutingComposition_timeSymmetric :
    TimeSymmetric
      (scaledStageComposition noncommutingPermutationStage [1, 2, 1]) := by
  apply palindromic_scaledStageComposition_timeSymmetric
  · exact noncommutingPermutationStage_timeSymmetric
  · norm_num

/-- Removing the closing stage from the noncommuting palindrome destroys time
symmetry.  Thus time symmetry is not inherited by arbitrary stage lists. -/
theorem nonpalindromic_noncommutingComposition_not_timeSymmetric :
    ¬ TimeSymmetric
      (scaledStageComposition noncommutingPermutationStage [1, 2]) := by
  intro hs
  have h := hs 1
  have hx := congrArg (fun p : Equiv.Perm (Fin 3) => p 0) h
  norm_num [stepAdjoint, scaledStageComposition, noncommutingPermutationStage,
    Equiv.Perm.mul_apply] at hx
  have hright :
      (Equiv.swap (0 : Fin 3) 1) ((Equiv.swap (1 : Fin 3) 2) 0) = 1 := by
    decide
  rw [hright] at hx
  omega

/-- Translation supplies a nontrivial commuting boundary: a nonpalindromic
coefficient list can still happen to be time-symmetric. -/
noncomputable def translationStage (h : ℝ) : Equiv.Perm ℝ :=
  Equiv.addRight h

/-- Syntactic palindromicity is sufficient, but not necessary, for time
symmetry: translations commute and the coefficient list `[1, 2]` is not a
palindrome. -/
theorem nonpalindromic_can_still_be_timeSymmetric :
    ([1, 2] : List ℝ).reverse ≠ [1, 2] ∧
      TimeSymmetric (scaledStageComposition translationStage [1, 2]) := by
  constructor
  · norm_num
  · intro h
    ext x
    simp [stepAdjoint, scaledStageComposition, translationStage,
      Equiv.Perm.mul_apply]
    ring

end RoutedCarom

end Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder
