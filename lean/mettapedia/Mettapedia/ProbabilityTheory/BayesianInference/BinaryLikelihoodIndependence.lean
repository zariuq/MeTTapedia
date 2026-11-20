import Mettapedia.ProbabilityTheory.FiniteEventMass
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Independence of two binary coordinates after conditioning

Independent prior coordinates admit a product shortcut for their posterior
conjunction precisely when the likelihood has zero determinant on their
common binary support. The signed defect also quantifies the error.
-/

set_option autoImplicit false

namespace Mettapedia.ProbabilityTheory.BayesianInference.BinaryLikelihoodIndependence

open FiniteEventMass

/-- A product prior, scored by a likelihood on the two coordinates. -/
def weight (left right : Bool → ℝ) (likelihood : Bool → Bool → ℝ) : Bool × Bool → ℝ :=
  fun w => left w.1 * right w.2 * likelihood w.1 w.2

theorem screeningDefect_weight (left right : Bool → ℝ) (likelihood : Bool → Bool → ℝ) :
    screeningDefect (weight left right likelihood) Prod.fst (fun _ => true) Prod.snd =
      (left false * left true * right false * right true) *
        (likelihood false false * likelihood true true -
          likelihood false true * likelihood true false) := by
  simp [screeningDefect, mass, weight, Fintype.sum_prod_type]
  ring

/-- The joint posterior of both true bits minus the product of the two
posterior marginals. The original product prior appears as a scalar factor. -/
theorem posterior_conjunction_sub_product (left right : Bool → ℝ)
    (likelihood : Bool → Bool → ℝ)
    (possible : mass (weight left right likelihood) (fun _ => true) ≠ 0) :
    let w := weight left right likelihood
    let z := mass w (fun _ => true)
    mass w (fun x => x.1 && x.2) / z -
      (mass w Prod.fst / z) * (mass w Prod.snd / z) =
    ((left false * left true * right false * right true) *
      (likelihood false false * likelihood true true -
        likelihood false true * likelihood true false)) / (z * z) := by
  dsimp only
  rw [← screeningDefect_weight]
  simp only [screeningDefect, Bool.and_true, Bool.true_and]
  field_simp [possible]

/-- For a fully supported product prior, multiplying posterior marginals
is exact precisely when the likelihood determinant vanishes. -/
theorem posterior_conjunction_eq_product_iff (left right : Bool → ℝ)
    (likelihood : Bool → Bool → ℝ)
    (leftSupported : ∀ b, left b ≠ 0) (rightSupported : ∀ b, right b ≠ 0)
    (possible : mass (weight left right likelihood) (fun _ => true) ≠ 0) :
    let w := weight left right likelihood
    let z := mass w (fun _ => true)
    mass w (fun x => x.1 && x.2) / z =
      (mass w Prod.fst / z) * (mass w Prod.snd / z) ↔
    likelihood false false * likelihood true true =
      likelihood false true * likelihood true false := by
  dsimp only
  rw [← sub_eq_zero, posterior_conjunction_sub_product left right likelihood possible]
  simp [div_eq_zero_iff, possible, leftSupported, rightSupported, sub_eq_zero]

end Mettapedia.ProbabilityTheory.BayesianInference.BinaryLikelihoodIndependence
