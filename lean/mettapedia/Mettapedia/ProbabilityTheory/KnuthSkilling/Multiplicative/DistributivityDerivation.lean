import Mettapedia.ProbabilityTheory.KnuthSkilling.Probability.ProbabilityDerivation
import Mettapedia.ProbabilityTheory.KnuthSkilling.Multiplicative.DirectProduct

/-!
# Deriving Scalar Distributivity from Lattice Structure

This module shows that `DistributesOverAdd` for the tensor operation
is **DERIVED** (not assumed!) from:
1. Lattice-level `prod_sup_left` (DirectProduct structure)
2. Disjoint additivity of valuations (CoxConsistency.sum_rule)
3. The bridge predicate `RectTensorCompatible`

## Main Result

`distributes_over_add_from_lattice` proves:
  Given lattice distributivity `prod (a₁ ⊔ a₂) b = prod a₁ b ⊔ prod a₂ b`
  and valuation additivity `v(a ⊔ b) = v(a) + v(b)` for disjoint elements,
  the scalar tensor operation satisfies `tensor(x+y, t) = tensor(x,t) + tensor(y,t)`.

## K&S Paper Correspondence

| K&S Paper | Lean Code | Domain |
|-----------|-----------|--------|
| `×` | `prod` | Events (lattice) |
| `⊗` | `tensor` | Scalars (ℝ⁺) |
| `m(·)` | `v.val` | Event → ℝ |

Connection: `m(x × t) = m(x) ⊗ m(t)` (paper) = `RectTensorCompatible` (Lean)
-/

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.Multiplicative

open Mettapedia.ProbabilityTheory.KnuthSkilling

/-! ## Hypotheses for the Derivation -/

/-- A lattice is "rich enough" if we can find disjoint preimages with any prescribed
positive valuations. This holds in natural models:
- **Set model**: Take disjoint subsets with prescribed measures
- **K&S algebra after representation**: Density ensures this -/
def HasDisjointPreimages {α : Type*} [PlausibilitySpace α] (v : Valuation α) : Prop :=
  ∀ x y : PosReal, ∃ a₁ a₂ : α,
    Disjoint a₁ a₂ ∧
    v.val a₁ = (x : ℝ) ∧
    v.val a₂ = (y : ℝ) ∧
    0 < v.val a₁ ∧
    0 < v.val a₂

/-- A valuation hits all positive real values (surjectivity onto (0,∞)). -/
def ValuationSurjective {α : Type*} [PlausibilitySpace α] (v : Valuation α) : Prop :=
  ∀ t : PosReal, ∃ a : α, v.val a = (t : ℝ) ∧ 0 < v.val a

/-! ## The Main Derivation -/

/-- **Main Theorem**: Scalar distributivity is DERIVED from lattice structure.

Given:
- `DirectProduct` with `prod_sup_left` (lattice-level distributivity)
- `CoxConsistency` for α and γ valuations (disjoint additivity)
- `RectTensorCompatible` (bridge: `v(prod a b) = tensor(v(a), v(b))`)
- Rich enough lattices (can construct disjoint preimages)

Then: `tensor` satisfies `DistributesOverAdd`.

This is the key bridge from "Symmetry 3" (lattice level) to "Axiom 3" (scalar level)! -/
theorem distributes_over_add_from_lattice
    {α β γ : Type*}
    [PlausibilitySpace α] [ComplementedLattice α]
    [PlausibilitySpace β] [ComplementedLattice β]
    [PlausibilitySpace γ] [ComplementedLattice γ]
    (P : DirectProduct α β γ)
    (vα : Valuation α) (vβ : Valuation β) (vγ : Valuation γ)
    (hCα : Mettapedia.ProbabilityTheory.KnuthSkilling.Probability.CoxConsistency α vα)
    (hCγ : Mettapedia.ProbabilityTheory.KnuthSkilling.Probability.CoxConsistency γ vγ)
    {tensor : PosReal → PosReal → PosReal}
    (hCompat : Mettapedia.ProbabilityTheory.KnuthSkilling.Probability.AppendixB.RectTensorCompatible
      P vα vβ vγ tensor)
    (hDisjoint : HasDisjointPreimages vα)
    (hSurj_β : ValuationSurjective vβ) :
    DistributesOverAdd tensor := by
  -- DistributesOverAdd: ∀ x y t, tensor (addPos x y) t = addPos (tensor x t) (tensor y t)
  intro x y t
  -- Step 1: Get disjoint preimages a₁, a₂ with v(a₁)=x, v(a₂)=y
  obtain ⟨a₁, a₂, hDisj, ha₁_eq, ha₂_eq, ha₁_pos, ha₂_pos⟩ := hDisjoint x y
  -- Step 2: Get preimage b with v(b)=t
  obtain ⟨b, hb_eq, hb_pos⟩ := hSurj_β t
  -- Step 3: v(a₁ ⊔ a₂) = v(a₁) + v(a₂) by sum_rule
  have hsum_α : vα.val (a₁ ⊔ a₂) = vα.val a₁ + vα.val a₂ :=
    Mettapedia.ProbabilityTheory.KnuthSkilling.Probability.sum_rule vα hCα hDisj
  -- Step 4: prod (a₁ ⊔ a₂) b = prod a₁ b ⊔ prod a₂ b by prod_sup_left
  have hprod : P.prod (a₁ ⊔ a₂) b = P.prod a₁ b ⊔ P.prod a₂ b := P.prod_sup_left a₁ a₂ b
  -- Step 5: disjoint_prod_left preserves disjointness
  have hDisj_γ : Disjoint (P.prod a₁ b) (P.prod a₂ b) := P.disjoint_prod_left hDisj
  -- Step 6: sum_rule on γ: v(prod a₁ b ⊔ prod a₂ b) = v(prod a₁ b) + v(prod a₂ b)
  have hsum_γ : vγ.val (P.prod a₁ b ⊔ P.prod a₂ b) =
      vγ.val (P.prod a₁ b) + vγ.val (P.prod a₂ b) :=
    Mettapedia.ProbabilityTheory.KnuthSkilling.Probability.sum_rule vγ hCγ hDisj_γ
  -- Step 7: RectTensorCompatible for each term
  have h1 : vγ.val (P.prod a₁ b) = ((tensor ⟨vα.val a₁, ha₁_pos⟩ ⟨vβ.val b, hb_pos⟩ : PosReal) : ℝ) :=
    hCompat a₁ b ha₁_pos hb_pos
  have h2 : vγ.val (P.prod a₂ b) = ((tensor ⟨vα.val a₂, ha₂_pos⟩ ⟨vβ.val b, hb_pos⟩ : PosReal) : ℝ) :=
    hCompat a₂ b ha₂_pos hb_pos
  -- Step 8: Positivity of v(a₁ ⊔ a₂) to use RectTensorCompatible on LHS
  have ha_sup_pos : 0 < vα.val (a₁ ⊔ a₂) := by
    rw [hsum_α]; linarith [ha₁_pos, ha₂_pos]
  have h3 : vγ.val (P.prod (a₁ ⊔ a₂) b) =
      ((tensor ⟨vα.val (a₁ ⊔ a₂), ha_sup_pos⟩ ⟨vβ.val b, hb_pos⟩ : PosReal) : ℝ) :=
    hCompat (a₁ ⊔ a₂) b ha_sup_pos hb_pos
  -- Now combine everything using the chain:
  -- LHS: tensor(addPos x y, t) = tensor(⟨v(a₁⊔a₂), _⟩, ⟨v(b), _⟩)  [since v(a₁⊔a₂)=x+y]
  --                            = v(prod(a₁⊔a₂, b))                  [by RectTensorCompatible]
  --                            = v(prod a₁ b ⊔ prod a₂ b)          [by prod_sup_left]
  --                            = v(prod a₁ b) + v(prod a₂ b)       [by sum_rule]
  --                            = tensor(x,t) + tensor(y,t)         [by RectTensorCompatible]
  -- RHS: addPos (tensor x t) (tensor y t) = tensor x t + tensor y t

  -- To prove equality of PosReal, we use Subtype.ext
  apply Subtype.ext
  -- Now we prove equality of the underlying reals

  -- Key: addPos x y has value x+y, and by hsum_α we know v(a₁⊔a₂) = x + y
  have key_x : x = ⟨vα.val a₁, ha₁_pos⟩ := by ext; exact ha₁_eq.symm
  have key_y : y = ⟨vα.val a₂, ha₂_pos⟩ := by ext; exact ha₂_eq.symm
  have key_t : t = ⟨vβ.val b, hb_pos⟩ := by ext; exact hb_eq.symm

  -- LHS simplification
  have lhs_eq : (addPos x y : ℝ) = vα.val (a₁ ⊔ a₂) := by
    simp only [addPos, Subtype.coe_mk]
    rw [← ha₁_eq, ← ha₂_eq]
    exact hsum_α.symm

  -- addPos x y = ⟨v(a₁⊔a₂), ha_sup_pos⟩ as PosReal
  have addPos_eq : addPos x y = ⟨vα.val (a₁ ⊔ a₂), ha_sup_pos⟩ := by
    ext; exact lhs_eq

  -- Now the calculation at the real level
  calc (tensor (addPos x y) t : ℝ)
      _ = (tensor ⟨vα.val (a₁ ⊔ a₂), ha_sup_pos⟩ ⟨vβ.val b, hb_pos⟩ : ℝ) := by
            rw [addPos_eq, key_t]
      _ = vγ.val (P.prod (a₁ ⊔ a₂) b) := by rw [h3]
      _ = vγ.val (P.prod a₁ b ⊔ P.prod a₂ b) := by rw [hprod]
      _ = vγ.val (P.prod a₁ b) + vγ.val (P.prod a₂ b) := hsum_γ
      _ = (tensor ⟨vα.val a₁, ha₁_pos⟩ ⟨vβ.val b, hb_pos⟩ : ℝ) +
          (tensor ⟨vα.val a₂, ha₂_pos⟩ ⟨vβ.val b, hb_pos⟩ : ℝ) := by rw [h1, h2]
      _ = (tensor x t : ℝ) + (tensor y t : ℝ) := by rw [key_x, key_y, key_t]
      _ = (addPos (tensor x t) (tensor y t) : ℝ) := rfl

end Mettapedia.ProbabilityTheory.KnuthSkilling.Multiplicative
