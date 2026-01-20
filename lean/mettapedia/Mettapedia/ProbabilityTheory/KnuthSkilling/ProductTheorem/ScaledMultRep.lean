import Mettapedia.ProbabilityTheory.KnuthSkilling.ProductTheorem.Basic

/-!
# ScaledMultRep: Common Interface for Appendix B Results

This file provides the **single source of truth** for K&S Appendix B's conclusion:
the tensor operation ⊗ on positive reals is scaled multiplication.

## Design Principle

Like `AdditiveOrderIsoRep` for Appendix A, this interface captures the OUTPUT of Appendix B
without depending on HOW it was proven. Multiple proof paths can provide this interface:

- `Main.lean`: K&S's actual path (uses AdditiveOrderIsoRep from Appendix A)
- `Alternative/DirectProof.lean`: Direct algebraic proof (weaker assumptions)

Downstream code (ProbabilityDerivation, Section 7, etc.) depends only on this interface.

## The Result

**Appendix B Theorem**: Any tensor ⊗ on (0,∞) satisfying distributivity and associativity
(plus regularity conditions) must be scaled multiplication:

  `x ⊗ y = (x * y) / C` for some global constant C > 0

Setting C = 1 by normalization gives `x ⊗ y = x * y`.
-/

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.ProductTheorem

open Mettapedia.ProbabilityTheory.KnuthSkilling.Literature

/-! ## The Interface -/

/-- **ScaledMultRep**: The tensor operation has a scaled multiplication representation.

This is the OUTPUT of K&S Appendix B: the tensor ⊗ on positive reals equals
multiplication up to a global scale constant C > 0.

Multiple proof paths provide this interface:
- K&S path: AdditiveOrderIsoRep + Distributivity → ScaledMultRep
- Direct path: TensorRegularity + Distributivity → ScaledMultRep
-/
structure ScaledMultRep (tensor : PosReal → PosReal → PosReal) where
  /-- The scale constant C > 0 -/
  C : ℝ
  /-- C is positive -/
  C_pos : 0 < C
  /-- The tensor equals scaled multiplication: x ⊗ y = (x * y) / C -/
  tensor_eq : ∀ x y : PosReal, ((tensor x y : PosReal) : ℝ) = ((x : ℝ) * (y : ℝ)) / C

namespace ScaledMultRep

variable {tensor : PosReal → PosReal → PosReal}

/-- C is nonzero -/
theorem C_ne_zero (h : ScaledMultRep tensor) : h.C ≠ 0 := ne_of_gt h.C_pos

/-- Tensor expressed in terms of C -/
theorem tensor_eq' (h : ScaledMultRep tensor) (x y : PosReal) :
    ((tensor x y : PosReal) : ℝ) = ((x : ℝ) * (y : ℝ)) / h.C :=
  h.tensor_eq x y

/-- After normalizing by C, tensor becomes actual multiplication.

This corresponds to K&S's "set C = 1 without loss of generality". -/
theorem tensor_normalized (h : ScaledMultRep tensor) (x y : PosReal) :
    ((tensor x y : PosReal) : ℝ) / h.C = (((x : ℝ) / h.C) * ((y : ℝ) / h.C)) := by
  have hC := h.C_ne_zero
  rw [h.tensor_eq]
  field_simp

/-- Tensor is commutative (follows from multiplication being commutative) -/
theorem tensor_comm (h : ScaledMultRep tensor) (x y : PosReal) :
    tensor x y = tensor y x := by
  apply Subtype.ext
  simp only [h.tensor_eq]
  ring

/-- Tensor is associative (follows from multiplication being associative) -/
theorem tensor_assoc (h : ScaledMultRep tensor) (x y z : PosReal) :
    tensor (tensor x y) z = tensor x (tensor y z) := by
  apply Subtype.ext
  have hC := h.C_ne_zero
  have hC_pos := h.C_pos
  simp only [h.tensor_eq]
  have hxy_pos : 0 < (x : ℝ) * (y : ℝ) := mul_pos x.2 y.2
  have hyz_pos : 0 < (y : ℝ) * (z : ℝ) := mul_pos y.2 z.2
  field_simp

end ScaledMultRep

/-! ## Constructors from Existence Proofs -/

/-- Build `ScaledMultRep` from an existence proof.

This is the bridge from theorem statements like `tensor_coe_eq_mul_div_const` to the interface. -/
noncomputable def ScaledMultRep.ofExists
    {tensor : PosReal → PosReal → PosReal}
    (h : ∃ C : ℝ, 0 < C ∧ ∀ x y : PosReal, ((tensor x y : PosReal) : ℝ) = ((x : ℝ) * (y : ℝ)) / C) :
    ScaledMultRep tensor :=
  ⟨h.choose, h.choose_spec.1, h.choose_spec.2⟩

end Mettapedia.ProbabilityTheory.KnuthSkilling.ProductTheorem
