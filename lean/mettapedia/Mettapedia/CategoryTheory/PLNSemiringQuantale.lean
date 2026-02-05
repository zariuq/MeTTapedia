import Mettapedia.Logic.EvidenceQuantale

/-!
# PLN Semiring Quantale

This file formalizes the semiring quantale structure on Evidence:
- ⊗ = componentwise multiplication (sequential composition)
- ⊕ = componentwise addition (parallel aggregation)

## Proven Results

1. Associativity of ⊗ and ⊕
2. Distributivity: x ⊗ (y ⊕ z) = (x ⊗ y) ⊕ (x ⊗ z)
3. Weakness ordering for uniform valuations

## References

- Goertzel, "Weakness: A Quantale-Theoretic Approach"
-/

set_option linter.dupNamespace false

namespace Mettapedia.CategoryTheory.PLNSemiringQuantale

open Mettapedia.Logic.EvidenceQuantale

/-! ## Semiring Quantale Operations -/

/-- Tensor product ⊗: sequential composition (componentwise multiplication) -/
noncomputable def tensor (x y : Evidence) : Evidence :=
  ⟨x.pos * y.pos, x.neg * y.neg⟩

/-- Par ⊕: parallel aggregation (componentwise addition) -/
noncomputable def par (x y : Evidence) : Evidence :=
  ⟨x.pos + y.pos, x.neg + y.neg⟩

/-! ## Algebraic Laws (Proven) -/

theorem tensor_assoc (x y z : Evidence) :
    tensor (tensor x y) z = tensor x (tensor y z) :=
  Evidence.tensor_assoc x y z

theorem par_assoc (x y z : Evidence) :
    par (par x y) z = par x (par y z) :=
  Evidence.hplus_assoc x y z

theorem tensor_comm (x y : Evidence) :
    tensor x y = tensor y x :=
  Evidence.tensor_comm x y

theorem par_comm (x y : Evidence) :
    par x y = par y x :=
  Evidence.hplus_comm x y

/-- The quantale law: tensor distributes over par -/
theorem tensor_par_distrib (x y z : Evidence) :
    tensor x (par y z) = par (tensor x y) (tensor x z) := by
  simp only [tensor, par]
  ext
  · simp only [mul_add]
  · simp only [mul_add]

/-- Right distributivity -/
theorem par_tensor_distrib_right (x y z : Evidence) :
    tensor (par x y) z = par (tensor x z) (tensor y z) := by
  simp only [tensor, par]
  ext
  · simp only [add_mul]
  · simp only [add_mul]

/-! ## Weakness Formula

Given edges in an inference hypergraph, the weakness is:
  w(H) = ⊕_{edges} [μ(source) ⊗ μ(target)]
-/

/-- Weakness of a single edge: μ(u) ⊗ μ(v) -/
noncomputable def edgeWeakness (μu μv : Evidence) : Evidence :=
  tensor μu μv

/-- Weakness of two parallel edges -/
noncomputable def twoEdgeWeakness (μ1u μ1v μ2u μ2v : Evidence) : Evidence :=
  par (edgeWeakness μ1u μ1v) (edgeWeakness μ2u μ2v)

/-! ## Weakness Ordering (Proven)

For a uniform valuation where all nodes have the same evidence e:
- One-edge weakness = e ⊗ e
- Two-edge weakness = (e ⊗ e) ⊕ (e ⊗ e)

Since par adds components, two-edge > one-edge.
-/

/-- One edge weakness for uniform valuation -/
noncomputable def oneEdgeUniform (e : Evidence) : Evidence :=
  edgeWeakness e e

/-- Two edge weakness for uniform valuation -/
noncomputable def twoEdgeUniform (e : Evidence) : Evidence :=
  twoEdgeWeakness e e e e

/-- Two edges have at least as much weakness as one edge (uniform case) -/
theorem twoEdge_ge_oneEdge (e : Evidence) :
    oneEdgeUniform e ≤ twoEdgeUniform e := by
  unfold oneEdgeUniform twoEdgeUniform twoEdgeWeakness edgeWeakness par
  simp only [Evidence.le_def]
  constructor
  · -- pos component: e.pos * e.pos ≤ e.pos * e.pos + e.pos * e.pos
    exact le_add_of_nonneg_right (zero_le _)
  · -- neg component: e.neg * e.neg ≤ e.neg * e.neg + e.neg * e.neg
    exact le_add_of_nonneg_right (zero_le _)

/-- Two edges have strictly more weakness when evidence is positive and finite (`pos ≠ ⊤`). -/
theorem twoEdge_gt_oneEdge (e : Evidence) (hpos : 0 < e.pos) (hfinite : e.pos ≠ ⊤) :
    oneEdgeUniform e < twoEdgeUniform e := by
  refine ⟨twoEdge_ge_oneEdge e, ?_⟩
  intro hle
  have hpos_le : (twoEdgeUniform e).pos ≤ (oneEdgeUniform e).pos := hle.1
  have hpos_le' : e.pos * e.pos + e.pos * e.pos ≤ e.pos * e.pos := by
    simpa [twoEdgeUniform, oneEdgeUniform, twoEdgeWeakness, edgeWeakness, par, tensor] using hpos_le

  have hmul_ne_top : e.pos * e.pos ≠ ⊤ := by
    exact ENNReal.mul_ne_top hfinite hfinite
  have hmul_ne_zero : e.pos * e.pos ≠ 0 := by
    have hpos0 : e.pos ≠ 0 := ne_of_gt hpos
    intro hmul0
    rcases (mul_eq_zero.mp hmul0) with h0 | h0 <;> exact hpos0 h0

  have hgt : e.pos * e.pos + e.pos * e.pos > e.pos * e.pos :=
    (ENNReal.lt_add_right hmul_ne_top hmul_ne_zero)

  exact (not_le_of_gt hgt) hpos_le'

/-! ## Deduction Formula as Semiring Expression

The PLN deduction formula decomposes into tensor and par:
  s_AC = (s_AB ⊗ s_BC) ⊕ ((1-s_AB) ⊗ complement)
       = direct_path ⊕ indirect_path
-/

/-- The deduction formula IS a par of two tensor paths -/
theorem deduction_as_semiring (s_AB s_BC pB pC : ENNReal) :
    Evidence.deductionStrength s_AB s_BC pB pC =
    s_AB * s_BC + (1 - s_AB) * Evidence.complementStrength pB pC s_BC := by
  unfold Evidence.deductionStrength Evidence.directPathStrength Evidence.indirectPathStrength
  rfl

/-! ## Summary

Proven:
1. ⊗ and ⊕ are associative and commutative
2. ⊗ distributes over ⊕ (both sides)
3. `twoEdge_ge_oneEdge`: Two-edge weakness ≥ one-edge weakness (uniform valuations)
4. `twoEdge_gt_oneEdge`: Two-edge weakness > one-edge weakness (when pos evidence is positive and finite)
5. `deduction_as_semiring`: Deduction formula = direct_path ⊕ indirect_path

**Key Result**: Inference rules with more parallel paths have higher weakness.
- Deduction (1 path) < Induction/Abduction (2 paths)
- More paths = more "general" but less "constrained"
-/

end Mettapedia.CategoryTheory.PLNSemiringQuantale
