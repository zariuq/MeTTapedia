import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.AffineCoreBridge
import Mettapedia.Algebra.AffineMonoid

/-!
# Scalar state-space transitions are the scalar affine monoid

`AffineTransition State` in `StateSpaceScan` is the neural representation of
an affine map of a real normed space, with a continuous linear part. It
composes in execution order, as the generic coefficient monoid
`Mettapedia.Algebra.AffineSummary` does. `AffineCoreBridge` maps every such
transition into the additive core `AffineAction State`. This module adds the
scalar comparison, and derives the neural scan theorem from the generic one.

* `scalarEquiv : AffineTransition ℝ ≃* AffineSummary ℝ`. A continuous linear
  endomorphism of `ℝ` is multiplication by its value at `1`, so for
  `State = ℝ` the neural transition monoid is the scalar coefficient monoid.
* `scalarEquiv_act` and `toAction_scalarEquiv`: the equivalence preserves the
  action, and it commutes with the two maps into the additive core.
  `toCoreHom` packages the core bridge as a monoid homomorphism.
* Neural transitions act on states on the right, so
  `Mettapedia.Algebra.ActionFold` applies. `affinePrefixScan_eq_scanl`
  identifies the neural prefix scan with the monoid's prefix products.
  `affinePrefixScan_correct_generic` obtains
  `LinearStateSpaceCell.affinePrefixScan_correct` from the generic scan law,
  for every normed state space.
* `scalar_affinePrefixScan`: for a scalar cell, the scan's coefficients are
  the scalar prefix products. `scalarCell_coefficient_scan` checks this on
  the existing fixture.

The neural representation keeps its continuity data where it is. Nothing
here concerns floating-point execution.
-/

set_option autoImplicit false

namespace Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder

open scoped RightActions
open Mettapedia.Algebra

namespace AffineTransition

section General

variable {State : Type*} [NormedAddCommGroup State] [NormedSpace ℝ State]

/-- Neural affine transitions act on states on the right:
`x <• f = f.act x`. -/
noncomputable instance : MulAction (AffineTransition State)ᵐᵒᵖ State where
  smul f x := f.unop.act x
  one_smul := act_one
  mul_smul f g x := act_mul g.unop f.unop x

@[simp] theorem op_smul_eq_act (f : AffineTransition State) (x : State) :
    x <• f = f.act x := rfl

/-- The core bridge as a monoid homomorphism. -/
noncomputable def toCoreHom : AffineTransition State →* AffineAction State where
  toFun := toCore
  map_one' := by
    apply AffineAction.ext
    · ext x
      rfl
    · rfl
  map_mul' := toCore_compose

theorem toCoreHom_injective : Function.Injective (toCoreHom (State := State)) :=
  toCore_injective

end General

/-! ## The scalar case -/

/-- A continuous linear endomorphism of `ℝ` multiplies by its value at `1`. -/
theorem linear_apply_eq_mul (f : AffineTransition ℝ) (x : ℝ) :
    f.linear x = f.linear 1 * x := by
  have h := f.linear.map_smul x 1
  rw [smul_eq_mul, mul_one, smul_eq_mul] at h
  rw [h, mul_comm]

/-- The scalar coefficients of a transition of `ℝ`. -/
noncomputable def toScalar (f : AffineTransition ℝ) : AffineSummary ℝ :=
  ⟨f.linear 1, f.offset⟩

/-- The transition of `ℝ` with the given scalar coefficients. -/
noncomputable def ofScalar (s : AffineSummary ℝ) : AffineTransition ℝ :=
  ⟨s.scale • ContinuousLinearMap.id ℝ ℝ, s.offset⟩

/-- **Scalar comparison.** For `State = ℝ`, the neural transition monoid is
the scalar affine coefficient monoid. -/
noncomputable def scalarEquiv : AffineTransition ℝ ≃* AffineSummary ℝ where
  toFun := toScalar
  invFun := ofScalar
  left_inv f := by
    apply AffineTransition.ext'
    · ext
      simp [ofScalar, toScalar]
    · rfl
  right_inv s := by
    apply AffineSummary.ext
    · simp [ofScalar, toScalar]
    · rfl
  map_mul' f g := by
    apply AffineSummary.ext
    · change g.linear (f.linear 1) = g.linear 1 * f.linear 1
      rw [linear_apply_eq_mul g (f.linear 1)]
    · change g.linear f.offset + g.offset = g.linear 1 * f.offset + g.offset
      rw [linear_apply_eq_mul g f.offset]

@[simp] theorem scalarEquiv_apply (f : AffineTransition ℝ) :
    scalarEquiv f = ⟨f.linear 1, f.offset⟩ := rfl

theorem scalarEquiv_scale (f : AffineTransition ℝ) :
    (scalarEquiv f).scale = f.linear 1 := rfl

theorem scalarEquiv_offset (f : AffineTransition ℝ) :
    (scalarEquiv f).offset = f.offset := rfl

/-- The comparison preserves the action on states. -/
theorem scalarEquiv_act (f : AffineTransition ℝ) (x : ℝ) :
    (scalarEquiv f).act x = f.act x := by
  change f.linear 1 * x + f.offset = f.linear x + f.offset
  rw [linear_apply_eq_mul f x]

/-- The comparison commutes with the two maps into the additive core. -/
theorem toAction_scalarEquiv (f : AffineTransition ℝ) :
    (scalarEquiv f).toAction = f.toCore := by
  apply AffineAction.ext
  · ext x
    exact (linear_apply_eq_mul f x).symm
  · rfl

end AffineTransition

/-! ## The neural scan as an instance of the generic scan law -/

namespace LinearStateSpaceCell

variable {State : Type*} {Input : Type*} {Output : Type*}
  [NormedAddCommGroup State] [NormedSpace ℝ State]
  [NormedAddCommGroup Input] [NormedSpace ℝ Input]
  [NormedAddCommGroup Output] [NormedSpace ℝ Output]

theorem affineScanFrom_eq_scanl (cell : LinearStateSpaceCell State Input Output)
    (accumulator : AffineTransition State) (inputs : List Input) :
    cell.affineScanFrom accumulator inputs =
      (inputs.map cell.affineTransition).scanl (· * ·) accumulator := by
  induction inputs generalizing accumulator with
  | nil => rfl
  | cons input inputs ih => simp [affineScanFrom, ih]

/-- The neural prefix scan is the list of prefix products of the input
transitions. -/
theorem affinePrefixScan_eq_scanl (cell : LinearStateSpaceCell State Input Output)
    (inputs : List Input) :
    cell.affinePrefixScan inputs = (inputs.map cell.affineTransition).scanl (· * ·) 1 :=
  affineScanFrom_eq_scanl cell 1 inputs

theorem trajectoryFrom_eq_scanl (cell : LinearStateSpaceCell State Input Output)
    (state : State) (inputs : List Input) :
    cell.trajectoryFrom state inputs = inputs.scanl (fun s u => cell.step s u) state := by
  induction inputs generalizing state with
  | nil => rfl
  | cons input inputs ih => simp [trajectoryFrom, ih]

/-- `LinearStateSpaceCell.affinePrefixScan_correct`, derived from the generic
scan law `ActionFold.scanl_op_smul`. -/
theorem affinePrefixScan_correct_generic (cell : LinearStateSpaceCell State Input Output)
    (initial : State) (inputs : List Input) :
    (cell.affinePrefixScan inputs).map (fun transition => transition.act initial) =
      cell.trajectory initial inputs := by
  have hstep : ∀ s u, cell.step s u = s <• cell.affineTransition u :=
    fun s u => (affineTransition_act cell u s).symm
  have hmap : inputs.scanl (fun s u => s <• cell.affineTransition u) initial =
      (inputs.map cell.affineTransition).scanl (fun s m => s <• m) initial := by
    rw [List.scanl_map]
  rw [affinePrefixScan_eq_scanl, trajectory, trajectoryFrom_eq_scanl]
  simp only [hstep]
  rw [hmap, ActionFold.scanl_op_smul]
  rfl

/-- For a scalar cell, the prefix scan's coefficients are the scalar prefix
products of the input coefficients. -/
theorem scalar_affinePrefixScan (cell : LinearStateSpaceCell ℝ Input Output)
    (inputs : List Input) :
    (cell.affinePrefixScan inputs).map AffineTransition.scalarEquiv =
      (inputs.map fun u => AffineTransition.scalarEquiv (cell.affineTransition u)).scanl
        (· * ·) 1 := by
  rw [affinePrefixScan_eq_scanl, ActionFold.map_scanl_mul, map_one, List.map_map]
  rfl

end LinearStateSpaceCell

/-- The existing scalar fixture `x ↦ 2x + u` on inputs `[1, 2]`: the
coefficient scan is `1, ⟨2, 1⟩, ⟨4, 4⟩`, whose action on `0` is the
trajectory `0, 1, 4` of `scalarCell_scan_positiveExample`. -/
theorem scalarCell_coefficient_scan :
    (StateSpaceFixtures.scalarCell.affinePrefixScan [1, 2]).map
        AffineTransition.scalarEquiv = [1, ⟨2, 1⟩, ⟨4, 4⟩] := by
  rw [LinearStateSpaceCell.scalar_affinePrefixScan]
  norm_num [StateSpaceFixtures.scalarCell, LinearStateSpaceCell.affineTransition]

end Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder
