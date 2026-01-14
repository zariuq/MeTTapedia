/-
# Inclusion-Exclusion for K&S Valuations

Proves: m(x ⊔ y) + m(x ⊓ y) = m(x) + m(y) for arbitrary x, y.

This connects the K&S additive representation (for disjoint combinations)
to the standard measure-theoretic inclusion-exclusion formula.

## Key Mathlib Lemmas Used
- `sup_sdiff_inf`: x \ y ⊔ x ⊓ y = x
- `sup_eq_sdiff_sup_sdiff_sup_inf`: x ⊔ y = x \ y ⊔ y \ x ⊔ x ⊓ y
- `disjoint_inf_sdiff`: Disjoint (x ⊓ y) (x \ y)
- `disjoint_sdiff_sdiff`: Disjoint (x \ y) (y \ x)

## References
- K&S "Foundations of Inference" (2012), equation after (19)
-/

import Mathlib.Order.BooleanAlgebra.Basic
import Mathlib.Order.Disjoint
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.InclusionExclusion

/-! ## Additive Valuation on Boolean Algebras -/

/-- A valuation on a Boolean algebra that's additive on disjoint elements. -/
structure AdditiveValuation (α : Type*) [BooleanAlgebra α] where
  val : α → ℝ
  val_bot : val ⊥ = 0
  val_additive : ∀ x y : α, Disjoint x y → val (x ⊔ y) = val x + val y

namespace AdditiveValuation

variable {α : Type*} [BooleanAlgebra α] (m : AdditiveValuation α)

/-! ## Key Decomposition Lemmas -/

/-- x = (x \ y) ⊔ (x ⊓ y) -/
theorem decompose_elem (x y : α) : x = (x \ y) ⊔ (x ⊓ y) := (sup_sdiff_inf x y).symm

/-- x ⊔ y = (x \ y) ⊔ (y \ x) ⊔ (x ⊓ y) -/
theorem decompose_sup (x y : α) : x ⊔ y = (x \ y) ⊔ (y \ x) ⊔ (x ⊓ y) :=
  sup_eq_sdiff_sup_sdiff_sup_inf

/-- x \ y and x ⊓ y are disjoint -/
theorem disjoint_sdiff_inf (x y : α) : Disjoint (x \ y) (x ⊓ y) := disjoint_inf_sdiff.symm

/-- y \ x and x ⊓ y are disjoint -/
theorem disjoint_sdiff_inf' (x y : α) : Disjoint (y \ x) (x ⊓ y) := by
  rw [inf_comm]; exact disjoint_inf_sdiff.symm

/-- x \ y and y \ x are disjoint -/
theorem disjoint_sdiff_sdiff' (x y : α) : Disjoint (x \ y) (y \ x) := disjoint_sdiff_sdiff

/-- (x \ y) ⊔ (y \ x) is disjoint from (x ⊓ y) -/
theorem disjoint_sdiffs_inf (x y : α) : Disjoint ((x \ y) ⊔ (y \ x)) (x ⊓ y) := by
  rw [disjoint_sup_left]
  exact ⟨disjoint_sdiff_inf x y, disjoint_sdiff_inf' x y⟩

/-! ## Main Theorem: Inclusion-Exclusion -/

/-- **Inclusion-Exclusion Formula**
    m(x ⊔ y) + m(x ⊓ y) = m(x) + m(y)

This is the fundamental formula connecting additive valuations
on disjoint combinations to arbitrary joins and meets. -/
theorem inclusion_exclusion (x y : α) :
    m.val (x ⊔ y) + m.val (x ⊓ y) = m.val x + m.val y := by
  -- Key decompositions:
  -- x = (x \ y) ⊔ (x ⊓ y)           [disjoint]
  -- y = (y \ x) ⊔ (x ⊓ y)           [disjoint]
  -- x ⊔ y = (x \ y) ⊔ (y \ x) ⊔ (x ⊓ y)  [all pairwise disjoint]

  -- Abbreviations
  let a := x \ y   -- "only x"
  let b := x ⊓ y   -- "both"
  let c := y \ x   -- "only y"

  -- Disjointness
  have hab : Disjoint a b := disjoint_sdiff_inf x y
  have hcb : Disjoint c b := disjoint_sdiff_inf' x y
  have hac : Disjoint a c := disjoint_sdiff_sdiff' x y
  have hac_b : Disjoint (a ⊔ c) b := disjoint_sdiffs_inf x y

  -- Decompositions
  have hx : x = a ⊔ b := decompose_elem x y
  have hy : y = c ⊔ b := by rw [decompose_elem y x, inf_comm]
  have hxy : x ⊔ y = (a ⊔ c) ⊔ b := decompose_sup x y

  -- Calculate m(x ⊔ y)
  have h_xy : m.val (x ⊔ y) = m.val a + m.val c + m.val b := by
    calc m.val (x ⊔ y)
        = m.val ((a ⊔ c) ⊔ b) := by rw [hxy]
      _ = m.val (a ⊔ c) + m.val b := m.val_additive _ _ hac_b
      _ = (m.val a + m.val c) + m.val b := by rw [m.val_additive _ _ hac]

  -- Calculate m(x)
  have h_x : m.val x = m.val a + m.val b := by
    rw [hx, m.val_additive _ _ hab]

  -- Calculate m(y)
  have h_y : m.val y = m.val c + m.val b := by
    rw [hy, m.val_additive _ _ hcb]

  -- Final calculation
  calc m.val (x ⊔ y) + m.val (x ⊓ y)
      = (m.val a + m.val c + m.val b) + m.val b := by rw [h_xy]
    _ = m.val a + m.val b + (m.val c + m.val b) := by ring
    _ = m.val x + m.val y := by rw [← h_x, ← h_y]

/-! ## Corollaries -/

/-- For disjoint x, y: m(x ⊔ y) = m(x) + m(y) (since x ⊓ y = ⊥) -/
theorem val_sup_of_disjoint (x y : α) (h : Disjoint x y) :
    m.val (x ⊔ y) = m.val x + m.val y := by
  have hxy : x ⊓ y = ⊥ := h.eq_bot
  have := inclusion_exclusion m x y
  simp [hxy, m.val_bot] at this
  exact this

/-- Alternative form: m(x ⊔ y) = m(x) + m(y) - m(x ⊓ y) -/
theorem val_sup_eq (x y : α) :
    m.val (x ⊔ y) = m.val x + m.val y - m.val (x ⊓ y) := by
  have h := inclusion_exclusion m x y
  linarith

/-- Alternative form: m(x ⊓ y) = m(x) + m(y) - m(x ⊔ y) -/
theorem val_inf_eq (x y : α) :
    m.val (x ⊓ y) = m.val x + m.val y - m.val (x ⊔ y) := by
  have h := inclusion_exclusion m x y
  linarith

end AdditiveValuation

/-! ## Connection to K&S Representation Theorem

When we have a K&S representation Θ : α → ℝ with Θ(op x y) = Θ(x) + Θ(y)
for disjoint x, y, this gives an AdditiveValuation.

The inclusion-exclusion formula then follows automatically.
-/

/-- Build an AdditiveValuation from a K&S-style additive representation. -/
def ofKSRepresentation {α : Type*} [BooleanAlgebra α]
    (Θ : α → ℝ)
    (hΘ_bot : Θ ⊥ = 0)
    (hΘ_add : ∀ x y : α, Disjoint x y → Θ (x ⊔ y) = Θ x + Θ y) :
    AdditiveValuation α where
  val := Θ
  val_bot := hΘ_bot
  val_additive := hΘ_add

end Mettapedia.ProbabilityTheory.KnuthSkilling.InclusionExclusion
