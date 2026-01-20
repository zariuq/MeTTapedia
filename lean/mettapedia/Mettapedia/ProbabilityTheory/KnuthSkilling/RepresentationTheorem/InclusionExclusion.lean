import Mathlib.Order.Lattice
import Mathlib.Order.BooleanAlgebra.Basic
import Mathlib.Order.BooleanAlgebra.Defs
import Mathlib.Order.Disjoint
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mettapedia.ProbabilityTheory.KnuthSkilling.Literature.FunctionalEquations

/-!
# Inclusion-Exclusion from the Representation Theorem

**Paper reference**: Knuth & Skilling (2012), Section 5.2 "Arbitrary Arguments"

This file proves inclusion-exclusion formulas as consequences of Appendix A
(the representation theorem), NOT as input assumptions.

## Key quote from the paper (Section 5.1):

> "According to the scalar associativity theorem (Appendix A), an operator ⊕ obeying
> axioms 1 and 2 exists and can without loss of generality be taken to be addition +,
> giving the sum rule."

## Architecture note:

This file depends on `AdditiveOrderIsoRep α op` (the OUTPUT of Appendix A),
not on any particular proof route (grid/cuts/no-anom). Everything here works
regardless of which Appendix A proof you use.

## Three versions of inclusion-exclusion:

1. **Generalized Boolean algebras** (distributive + relative complements):
   Proven from disjoint additivity using `x \ y` decomposition

2. **Pure distributive lattices** (no relative complements):
   CANNOT be proven from disjoint additivity alone (see counterexample)
   Must be added as an axiom if needed

3. **Boolean algebras** (with global complements):
   Special case of (1), gives classical set formula

## Important Counterexample

See `Counterexamples/NonModularDistributive.lean` for a concrete 7-element
distributive lattice with a disjoint-additive valuation that FAILS the modular law.

This proves that K&S Section 5.2's decomposition argument `x = u ⊔ v, y = v ⊔ w`
requires relative complements (generalized Boolean algebra), not just distributivity.

-/

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.RepresentationTheorem

open Classical
open Literature (AdditiveOrderIsoRep)

/-! ## Valuation from Representation -/

/-- Given an additive order isomorphism representation `Θ : α ≃o ℝ`,
    we get a real-valued "measure" by composing with Θ.

    This is the "m(x) = x" valuation mentioned in Section 5.1 of the paper. -/
def valuationFromRep {α : Type*} [LinearOrder α] {op : α → α → α}
    (hRep : AdditiveOrderIsoRep α op) : α → ℝ := hRep.Θ

namespace valuationFromRep

variable {α : Type*} [LinearOrder α] {op : α → α → α} (hRep : AdditiveOrderIsoRep α op)

/-- Valuation respects order -/
theorem monotone : Monotone (valuationFromRep hRep) := hRep.Θ.monotone

/-- Valuation is strictly monotone -/
theorem strictMono : StrictMono (valuationFromRep hRep) := hRep.Θ.strictMono

/-- Valuation is injective -/
theorem injective : Function.Injective (valuationFromRep hRep) := hRep.Θ.injective

/-- **Sum rule for disjoint elements** (from the representation theorem).

    When elements are combined via `op` (which represents disjoint combination),
    their valuations add. This is equation (19) in the paper. -/
theorem additive (x y : α) :
    valuationFromRep hRep (op x y) = valuationFromRep hRep x + valuationFromRep hRep y :=
  hRep.map_op x y

end valuationFromRep

/-! ## Generalized Boolean Algebras: WHERE K&S PROOF WORKS

Generalized Boolean algebras are distributive lattices with `⊥` and relative complements `\`.
This is the minimal structure needed for K&S Section 5.2's decomposition argument.

**Key property**: For all x, y:
- `x = (x \ y) ⊔ (x ⊓ y)` where `(x \ y) ⊓ (x ⊓ y) = ⊥`
- This gives us the disjoint pieces needed for K&S's proof

Examples:
- Finite sets (Finset α)
- Regular open sets
- Boolean algebras (special case)

-/

section GeneralizedBoolean

variable {α : Type*} [GeneralizedBooleanAlgebra α] [LinearOrder α]
variable {op : α → α → α}
variable (hRep : AdditiveOrderIsoRep α op)

/-- **Inclusion-Exclusion (Modular Law)** for generalized Boolean algebras.

    For arbitrary (not necessarily disjoint) elements x and y:
    `m(x ⊔ y) + m(x ⊓ y) = m(x) + m(y)`

    **Paper reference**: K&S Section 5.2, equation (21)

    **Proof**: K&S's decomposition `x = u ⊔ v, y = v ⊔ w` with disjoint u, v, w.
    - Let v = x ⊓ y (the common part)
    - Let u = x \ v (relative complement of v in x, exists by GeneralizedBooleanAlgebra)
    - Let w = y \ v (relative complement of v in y)
    - From GeneralizedBooleanAlgebra axioms: x = u ⊔ v, y = w ⊔ v with u,v,w pairwise disjoint
    - Apply disjoint additivity via bridge hypothesis

    **Bridge hypothesis**: We need `op x y = x ⊔ y` when `x ⊓ y = ⊥` to connect
    the K&S operation to lattice joins. -/
theorem inclusion_exclusion_generalized_boolean (x y : α)
    (h_bridge : ∀ a b : α, a ⊓ b = ⊥ → op a b = a ⊔ b) :
    valuationFromRep hRep (x ⊔ y) + valuationFromRep hRep (x ⊓ y) =
      valuationFromRep hRep x + valuationFromRep hRep y := by
  -- K&S's 3-piece decomposition
  let v := x ⊓ y  -- common part
  let u := x \ v  -- x-only part
  let w := y \ v  -- y-only part

  -- Step 1: From GeneralizedBooleanAlgebra, x = (x ⊓ v) ⊔ u = v ⊔ u
  -- Note: x ⊓ v = x ⊓ (x ⊓ y) = x ⊓ y = v by absorption
  have x_inf_v : x ⊓ v = v := inf_of_le_right (inf_le_left)
  have x_decomp : x = v ⊔ u := by
    have h := GeneralizedBooleanAlgebra.sup_inf_sdiff x v
    rw [x_inf_v] at h
    exact h.symm

  -- Similarly y = v ⊔ w
  have y_inf_v : y ⊓ v = v := inf_of_le_right (inf_le_right)
  have y_decomp : y = v ⊔ w := by
    have h := GeneralizedBooleanAlgebra.sup_inf_sdiff y v
    rw [y_inf_v] at h
    exact h.symm

  -- Step 2: u, v, w are pairwise disjoint
  -- From inf_inf_sdiff: (x ⊓ v) ⊓ (x \ v) = ⊥, so v ⊓ u = ⊥
  have u_v_disj : u ⊓ v = ⊥ := by
    have h := GeneralizedBooleanAlgebra.inf_inf_sdiff x v
    rw [x_inf_v] at h
    rw [inf_comm]
    exact h

  have w_v_disj : w ⊓ v = ⊥ := by
    have h := GeneralizedBooleanAlgebra.inf_inf_sdiff y v
    rw [y_inf_v] at h
    rw [inf_comm]
    exact h

  -- Step 3: Prove u = x \ y and w = y \ x using uniqueness of relative complements
  -- We have u = x \ v where v = x ⊓ y, so u = x \ (x ⊓ y)
  -- We want to show u = x \ y

  have u_eq_sdiff : u = x \ y := by
    -- Use sdiff_unique: if z satisfies x ⊓ y ⊔ z = x and x ⊓ y ⊓ z = ⊥, then z = x \ y
    -- We have x = v ⊔ u = (x ⊓ y) ⊔ u from x_decomp, so (x ⊓ y) ⊔ u = x
    -- and u ⊓ v = ⊥ from u_v_disj, so (x ⊓ y) ⊓ u = v ⊓ u = ⊥
    -- First convert hypotheses to the form sdiff_unique expects
    have s : x ⊓ y ⊔ u = x := by show v ⊔ u = x; exact x_decomp.symm
    have i : x ⊓ y ⊓ u = ⊥ := by show v ⊓ u = ⊥; rw [inf_comm]; exact u_v_disj
    exact (sdiff_unique s i).symm

  have w_eq_sdiff : w = y \ x := by
    -- Similarly: (y ⊓ x) ⊔ w = y and (y ⊓ x) ⊓ w = ⊥
    -- We have y = v ⊔ w where v = x ⊓ y, so (y ⊓ x) ⊔ w = (x ⊓ y) ⊔ w
    -- First establish that y ⊓ x = v = x ⊓ y
    have yx_eq_v : y ⊓ x = v := inf_comm (a := y) (b := x)
    have s : y ⊓ x ⊔ w = y := by
      rw [yx_eq_v]
      exact y_decomp.symm
    have i : y ⊓ x ⊓ w = ⊥ := by
      rw [yx_eq_v, inf_comm]
      exact w_v_disj
    exact (sdiff_unique s i).symm

  -- Step 4: Now u ⊓ w = ⊥ follows from sdiff_inf_sdiff
  have u_w_disj : u ⊓ w = ⊥ := by
    rw [u_eq_sdiff, w_eq_sdiff]
    exact sdiff_inf_sdiff

  -- Step 5: Express x ⊔ y in terms of u, v, w
  have join_decomp : x ⊔ y = u ⊔ v ⊔ w := by
    -- Strategy: prove it directly without substitution
    -- sup_eq_sdiff_sup_sdiff_sup_inf gives: x ⊔ y = x \ y ⊔ y \ x ⊔ x ⊓ y
    -- which is (x \ y ⊔ y \ x) ⊔ x ⊓ y in left-associative form
    -- Reassociate and swap to get x \ y ⊔ (x ⊓ y ⊔ y \ x) = x \ y ⊔ v ⊔ y \ x (since v = x ⊓ y)
    have h1 := sup_eq_sdiff_sup_sdiff_sup_inf (x := x) (y := y)
    rw [sup_assoc] at h1  -- (a ⊔ b) ⊔ c = a ⊔ (b ⊔ c)
    rw [sup_comm (a := y \ x) (b := x ⊓ y)] at h1  -- swap b and c inside
    -- h1 : x ⊔ y = x \ y ⊔ (x ⊓ y ⊔ y \ x)
    -- Now substitute u and w
    calc x ⊔ y
        = x \ y ⊔ (x ⊓ y ⊔ y \ x) := h1
      _ = u ⊔ (v ⊔ w) := by rw [← u_eq_sdiff, ← w_eq_sdiff]  -- v = x ⊓ y by definition
      _ = u ⊔ v ⊔ w := (sup_assoc (a := u) (b := v) (c := w)).symm

  -- Step 5: Apply K&S counting via bridge hypothesis and additivity
  -- m(x) = m(v ⊔ u) = m(v) + m(u) [by h_bridge and commutativity]
  have mx_eq : valuationFromRep hRep x = valuationFromRep hRep v + valuationFromRep hRep u := by
    rw [x_decomp]
    -- v ⊓ u = ⊥ by commutativity of u_v_disj
    have v_u_disj : v ⊓ u = ⊥ := by rw [inf_comm]; exact u_v_disj
    have : op v u = v ⊔ u := h_bridge v u v_u_disj
    rw [← this]
    exact valuationFromRep.additive hRep v u

  -- m(y) = m(v ⊔ w) = m(v) + m(w) [by h_bridge and commutativity]
  have my_eq : valuationFromRep hRep y = valuationFromRep hRep v + valuationFromRep hRep w := by
    rw [y_decomp]
    have v_w_disj : v ⊓ w = ⊥ := by rw [inf_comm]; exact w_v_disj
    have : op v w = v ⊔ w := h_bridge v w v_w_disj
    rw [← this]
    exact valuationFromRep.additive hRep v w

  -- m(x ⊔ y) = m(u ⊔ v ⊔ w) = m(u) + m(v) + m(w) [by repeated application]
  have mxy_eq : valuationFromRep hRep (x ⊔ y) =
      valuationFromRep hRep u + valuationFromRep hRep v + valuationFromRep hRep w := by
    rw [join_decomp]
    -- First combine u ⊔ v
    have uv_disj : (u ⊔ v) ⊓ w = ⊥ := by
      -- From Mathlib: Disjoint.sup_left says if u ⊓ w = ⊥ and v ⊓ w = ⊥, then (u ⊔ v) ⊓ w = ⊥
      have u_disj_w : Disjoint u w := disjoint_iff.mpr u_w_disj
      have v_disj_w : Disjoint v w := disjoint_iff.mpr (by rw [inf_comm]; exact w_v_disj)
      exact disjoint_iff.mp (u_disj_w.sup_left v_disj_w)
    have : op (u ⊔ v) w = (u ⊔ v) ⊔ w := h_bridge (u ⊔ v) w uv_disj
    rw [← this, valuationFromRep.additive]
    -- Now use u ⊔ v = op u v
    have : op u v = u ⊔ v := h_bridge u v u_v_disj
    rw [← this, valuationFromRep.additive]

  -- m(x ⊓ y) = m(v)
  have mv_eq : valuationFromRep hRep (x ⊓ y) = valuationFromRep hRep v := rfl

  -- Final algebra: LHS = m(u) + m(v) + m(w) + m(v) = m(u) + 2·m(v) + m(w)
  --                RHS = (m(v) + m(u)) + (m(v) + m(w)) = 2·m(v) + m(u) + m(w)
  calc valuationFromRep hRep (x ⊔ y) + valuationFromRep hRep (x ⊓ y)
      = (valuationFromRep hRep u + valuationFromRep hRep v + valuationFromRep hRep w)
        + valuationFromRep hRep v := by rw [mxy_eq, mv_eq]
    _ = (valuationFromRep hRep v + valuationFromRep hRep u)
        + (valuationFromRep hRep v + valuationFromRep hRep w) := by ring
    _ = valuationFromRep hRep x + valuationFromRep hRep y := by rw [← mx_eq, ← my_eq]

end GeneralizedBoolean

/-! ## Pure Distributive Lattices: MODULAR LAW UNPROVABLE

**Counterexample** (see `Counterexamples/NonModularDistributive.lean`):
There exists a 7-element distributive lattice with a monotone, disjoint-additive valuation
that FAILS the modular law.

This proves: Disjoint additivity + distributive lattice ≠ Modular law

**Conclusion**: For pure distributive lattices (without relative complements),
if you want the modular law, you must ADD IT AS AN AXIOM, not derive it.

-/

section DistribLattice

variable {α : Type*} [DistribLattice α] [OrderBot α] [LinearOrder α]
variable {op : α → α → α}
variable (hRep : AdditiveOrderIsoRep α op)

/-- **Modular Law for pure distributive lattices** - REQUIRES EXTRA HYPOTHESIS.

    For arbitrary (not necessarily disjoint) elements x and y:
    `m(x ⊔ y) + m(x ⊓ y) = m(x) + m(y)`

    **This CANNOT be proven** from disjoint additivity + distributivity alone.
    (See `Counterexamples/NonModularDistributive.lean` for explicit counterexample.)

    If your specific distributive lattice satisfies this, you must assume it
    as an explicit hypothesis. -/
theorem modular_law_requires_hypothesis (x y : α)
    (h_modular : ∀ a b : α, valuationFromRep hRep (a ⊔ b) + valuationFromRep hRep (a ⊓ b) =
                 valuationFromRep hRep a + valuationFromRep hRep b) :
    valuationFromRep hRep (x ⊔ y) + valuationFromRep hRep (x ⊓ y) =
      valuationFromRep hRep x + valuationFromRep hRep y :=
  h_modular x y

end DistribLattice

/-! ## Boolean Lattice Specialization

When complements exist (Boolean lattice), we can derive the classical
set-theoretic inclusion-exclusion formula. -/

section BooleanLattice

variable {α : Type*} [BooleanAlgebra α] [LinearOrder α]
variable {op : α → α → α}
variable (hRep : AdditiveOrderIsoRep α op)

/-- **Classical Inclusion-Exclusion** for Boolean algebras.

    `m(x ⊔ y) = m(x) + m(y) - m(x ⊓ y)`

    This is the familiar set-theoretic version. It follows from the modular
    law by rearrangement. -/
theorem inclusion_exclusion_classical (x y : α)
    (h_modular : valuationFromRep hRep (x ⊔ y) + valuationFromRep hRep (x ⊓ y) =
                 valuationFromRep hRep x + valuationFromRep hRep y) :
    valuationFromRep hRep (x ⊔ y) =
      valuationFromRep hRep x + valuationFromRep hRep y - valuationFromRep hRep (x ⊓ y) := by
  linarith

/-- In Boolean algebras, we can use set difference explicitly.

    This requires the bridge hypothesis connecting the K&S operation `op` to
    lattice joins for disjoint elements. -/
theorem using_sdiff (x y : α)
    (h_bridge : ∀ a b : α, a ⊓ b = ⊥ → op a b = a ⊔ b) :
    valuationFromRep hRep (x ⊔ y) =
      valuationFromRep hRep (x \ y) + valuationFromRep hRep y := by
  -- Key facts in Boolean algebra:
  -- 1. (x \ y) ⊓ y = ⊥ (they are disjoint) - from inf_sdiff_self_left
  -- 2. (x \ y) ⊔ y = x ⊔ y - from sdiff_sup_self
  have h_disj : (x \ y) ⊓ y = ⊥ := inf_sdiff_self_left
  have h_sup : (x \ y) ⊔ y = x ⊔ y := sdiff_sup_self y x
  -- By bridge: op (x \ y) y = (x \ y) ⊔ y = x ⊔ y
  have h_op : op (x \ y) y = x ⊔ y := by rw [h_bridge _ _ h_disj, h_sup]
  -- By additivity: m(x \ y) + m(y) = m(op (x \ y) y) = m(x ⊔ y)
  calc valuationFromRep hRep (x ⊔ y)
      = valuationFromRep hRep (op (x \ y) y) := by rw [h_op]
    _ = valuationFromRep hRep (x \ y) + valuationFromRep hRep y :=
        valuationFromRep.additive hRep _ _

end BooleanLattice

/-! ## Commutativity of Join and Meet

**Paper quote** (K&S Section 5.2):
> "Commutativity of join and meet follow:
>  m(x ∨ y) = m(y ∨ x), m(x ∧ y) = m(y ∧ x)"

These are immediate from lattice structure (⊔ and ⊓ are commutative by definition),
but we record them explicitly for completeness. -/

section Commutativity

variable {α : Type*} [Lattice α] [LinearOrder α]
variable {op : α → α → α}
variable (hRep : AdditiveOrderIsoRep α op)

theorem join_comm (x y : α) : x ⊔ y = y ⊔ x := sup_comm x y

theorem meet_comm (x y : α) : x ⊓ y = y ⊓ x := inf_comm x y

theorem valuation_join_comm (x y : α) :
    valuationFromRep hRep (x ⊔ y) = valuationFromRep hRep (y ⊔ x) := by
  rw [join_comm]

theorem valuation_meet_comm (x y : α) :
    valuationFromRep hRep (x ⊓ y) = valuationFromRep hRep (y ⊓ x) := by
  rw [meet_comm]

end Commutativity

/-! ## TODO: Connect op to lattice structure

The main gap in this file is formalizing the connection between:
1. The `op : α → α → α` operation (from K&S axioms, represents disjoint combination)
2. The lattice structure `⊔`, `⊓` (for arbitrary joins and meets)

The paper implicitly assumes these are related by:
- When x and y are "disjoint" (in some sense), then x ⊔ y = op x y
- Disjointness can be expressed via the lattice: x ⊓ y = ⊥

This connection needs to be either:
(a) Added as an explicit hypothesis when we have both structures, or
(b) Derived from a more primitive setup where the lattice operations
    are defined in terms of op (less general), or
(c) Proven in specific models where both structures are explicitly constructed
    (e.g., finite Boolean algebras, open sets, etc.)

The examples in `Examples/` folder take approach (c). A general theory would
need (a) or (b). -/

end Mettapedia.ProbabilityTheory.KnuthSkilling.RepresentationTheorem
