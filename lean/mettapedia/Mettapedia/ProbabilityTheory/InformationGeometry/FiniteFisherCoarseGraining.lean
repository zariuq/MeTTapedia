import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
# Finite Fisher information under deterministic coarse-graining

For a positive finite mass `mass` and a tangent direction `tangent`, the
Fisher quadratic form is the weighted sum

`sum i, tangent i ^ 2 / mass i`.

A deterministic observation map combines the mass and tangent coordinates in
each observation fibre.  Cauchy--Schwarz then proves that the observed Fisher
quadratic form cannot exceed the original one.  This is the finite
data-processing direction needed by observer-relative value geometry; it is
not a proof of the full Chentsov uniqueness theorem or of monotonicity for
arbitrary stochastic kernels.

Unused target points have both pushed-forward mass and tangent equal to zero.
Lean's field convention makes their contribution `0 / 0 = 0`, so no
surjectivity hypothesis is needed.

References:

* Shun-ichi Amari, *Information Geometry*, Japanese Journal of Mathematics
  16 (2021), 1--48.
* L. L. Campbell, "An extended Chentsov characterization of the information
  metric", Proceedings of the AMS 98 (1986), 135--141.
-/

set_option autoImplicit false

namespace Mettapedia.ProbabilityTheory.InformationGeometry
namespace FiniteFisherCoarseGraining

open scoped BigOperators

universe uFine uCoarse

/-! ## Finite mass, tangents, and deterministic pushforward -/

/-- Add all coordinates in one fibre of a deterministic observation map. -/
noncomputable def fiberSum
    {Fine : Type uFine} {Coarse : Type uCoarse}
    [Fintype Fine] [DecidableEq Coarse]
    (observe : Fine → Coarse) (coordinate : Fine → ℝ)
    (coarse : Coarse) : ℝ :=
  ∑ fine with observe fine = coarse, coordinate fine

/-- The deterministic pushforward of a finite real-valued coordinate. -/
noncomputable def pushforward
    {Fine : Type uFine} {Coarse : Type uCoarse}
    [Fintype Fine] [DecidableEq Coarse]
    (observe : Fine → Coarse) (coordinate : Fine → ℝ) :
    Coarse → ℝ :=
  fiberSum observe coordinate

/-- Fisher's quadratic form on a finite positive mass and one tangent
direction.  Positivity is imposed by the theorems that use this expression,
rather than hidden inside the definition. -/
noncomputable def fisherQuadratic
    {Index : Type*} [Fintype Index]
    (mass tangent : Index → ℝ) : ℝ :=
  ∑ index, tangent index ^ 2 / mass index

/-! ## Additive conservation -/

/-- Deterministic pushforward preserves the total of every finite additive
coordinate.  Coarse-graining may lose distinctions, but it neither creates nor
destroys the aggregate mass carried through the observation map. -/
theorem sum_pushforward
    {Fine : Type uFine} {Coarse : Type uCoarse}
    [Fintype Fine] [Fintype Coarse] [DecidableEq Coarse]
    (observe : Fine → Coarse) (coordinate : Fine → ℝ) :
    ∑ coarse, pushforward observe coordinate coarse =
      ∑ fine, coordinate fine := by
  classical
  unfold pushforward fiberSum
  simpa only [Finset.sum_filter] using
    (Finset.sum_fiberwise (Finset.univ : Finset Fine) observe coordinate)

/-- In particular, deterministic observation preserves the tangent-space
zero-sum constraint of a probability simplex. -/
theorem sum_pushforward_eq_zero
    {Fine : Type uFine} {Coarse : Type uCoarse}
    [Fintype Fine] [Fintype Coarse] [DecidableEq Coarse]
    (observe : Fine → Coarse) (tangent : Fine → ℝ)
    (zeroSum : ∑ fine, tangent fine = 0) :
    ∑ coarse, pushforward observe tangent coarse = 0 := by
  rw [sum_pushforward observe tangent, zeroSum]

/-! ## Data processing -/

/-- One observation fibre cannot gain Fisher information when its coordinates
are added.  This is Engel's form of the finite Cauchy--Schwarz inequality. -/
theorem fiber_fisher_le
    {Fine : Type uFine} {Coarse : Type uCoarse}
    [Fintype Fine] [DecidableEq Coarse]
    (observe : Fine → Coarse) (mass tangent : Fine → ℝ)
    (massPositive : ∀ fine, 0 < mass fine) (coarse : Coarse) :
    (fiberSum observe tangent coarse) ^ 2 /
        fiberSum observe mass coarse ≤
      ∑ fine with observe fine = coarse,
        tangent fine ^ 2 / mass fine := by
  classical
  exact Finset.sq_sum_div_le_sum_sq_div
    (Finset.univ.filter fun fine ↦ observe fine = coarse)
    tangent (fun fine _ ↦ massPositive fine)

/-- Deterministic coarse-graining cannot increase the finite Fisher quadratic
form.  The theorem keeps multiplicity inside fibres and makes no injectivity
assumption on the observer. -/
theorem fisherQuadratic_pushforward_le
    {Fine : Type uFine} {Coarse : Type uCoarse}
    [Fintype Fine] [Fintype Coarse] [DecidableEq Coarse]
    (observe : Fine → Coarse) (mass tangent : Fine → ℝ)
    (massPositive : ∀ fine, 0 < mass fine) :
    fisherQuadratic (pushforward observe mass)
        (pushforward observe tangent) ≤
      fisherQuadratic mass tangent := by
  classical
  unfold fisherQuadratic pushforward
  calc
    (∑ coarse,
        (fiberSum observe tangent coarse) ^ 2 /
          fiberSum observe mass coarse) ≤
        ∑ coarse, ∑ fine with observe fine = coarse,
          tangent fine ^ 2 / mass fine := by
      apply Finset.sum_le_sum
      intro coarse _
      exact fiber_fisher_le observe mass tangent massPositive coarse
    _ = ∑ fine, tangent fine ^ 2 / mass fine := by
      simpa only [Finset.sum_filter] using
        (Finset.sum_fiberwise (Finset.univ : Finset Fine) observe
          (fun fine ↦ tangent fine ^ 2 / mass fine))

/-! ## Coordinate relabeling and a strict-loss canary -/

/-- A bijective coordinate relabeling preserves the Fisher quadratic form
exactly.  Information loss begins with genuinely non-injective observation,
not with a harmless change of finite names. -/
theorem fisherQuadratic_relabel
    {Fine : Type uFine} {Renamed : Type uCoarse}
    [Fintype Fine] [Fintype Renamed]
    (rename : Fine ≃ Renamed) (mass tangent : Fine → ℝ) :
    fisherQuadratic (fun renamed ↦ mass (rename.symm renamed))
        (fun renamed ↦ tangent (rename.symm renamed)) =
      fisherQuadratic mass tangent := by
  unfold fisherQuadratic
  simpa using
    (Equiv.sum_comp rename.symm
      (fun fine ↦ tangent fine ^ 2 / mass fine))

namespace Canary

/-- A balanced two-point mass. -/
noncomputable def balancedMass : Bool → ℝ :=
  fun _ ↦ 1 / 2

/-- A tangent that distinguishes the two points but cancels after they are
identified. -/
def cancellingTangent : Bool → ℝ
  | false => 1
  | true => -1

/-- The coarsest deterministic observer identifies both Boolean points. -/
def forgetBool : Bool → Unit :=
  fun _ ↦ ()

/-- Coarse observation strictly loses the direction distinguishing the two
fine states: its Fisher information falls from `4` to `0`. -/
theorem forgetBool_strictly_loses_fisher :
    fisherQuadratic (pushforward forgetBool balancedMass)
        (pushforward forgetBool cancellingTangent) = 0 ∧
      fisherQuadratic balancedMass cancellingTangent = 4 ∧
      fisherQuadratic (pushforward forgetBool balancedMass)
          (pushforward forgetBool cancellingTangent) <
        fisherQuadratic balancedMass cancellingTangent := by
  norm_num [fisherQuadratic, pushforward, fiberSum, forgetBool,
    balancedMass, cancellingTangent, Fintype.sum_bool]

end Canary

/-! ## Axiom audit -/

#print axioms fiber_fisher_le
#print axioms sum_pushforward
#print axioms sum_pushforward_eq_zero
#print axioms fisherQuadratic_pushforward_le
#print axioms fisherQuadratic_relabel
#print axioms Canary.forgetBool_strictly_loses_fisher

end FiniteFisherCoarseGraining
end Mettapedia.ProbabilityTheory.InformationGeometry
