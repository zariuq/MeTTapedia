import Mettapedia.GSLT.Core.GSLT
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Group.Defs

/-!
# Resource Algebras and Cost Maps

This file formalizes resource algebras (Definition 7.1) and cost maps
(Definition 7.2) from Meredith's "Computation, Causality, and Consciousness"
(2026), Part I, §7.

## Main Definitions

* `ResourceAlgebra` — A commutative ordered monoid for tracking resources
* `VectorialAccount` — A vector of resource values across resource types
* `CostMap` — Maps rewrite steps to resource costs
* `WeightMap` — Maps rewrite steps to complex amplitudes (Definition 6.1)

## Key Insight

Resources in a computation are heterogeneous (channels, memory, energy, names).
A vectorial account tracks each resource type independently. The conservation
theorem (Theorem 7.1) states that net account change is zero on closed paths
in the reversible envelope — this is the GSLT analogue of energy conservation.

## References

- Meredith, "Computation, Causality, and Consciousness" (2026), §§6–7
-/

namespace Mettapedia.GSLT

/-! ## Resource Algebras

    Definition 7.1 (Meredith 2026): A resource algebra is a commutative
    ordered monoid (A, +, 0, ≤).
-/

/-- A resource algebra is a commutative ordered monoid.

    Definition 7.1 (Meredith 2026): Resources form a commutative ordered
    monoid where:
    - Addition models resource combination
    - The zero element models "no resource"
    - The order models "has at least this much resource"
-/
class ResourceAlgebra (A : Type*) extends
    AddCommMonoid A, PartialOrder A where
  /-- Addition is monotone: a ≤ b → a + c ≤ b + c -/
  add_le_add_right : ∀ {a b : A}, a ≤ b → ∀ (c : A), a + c ≤ b + c

namespace ResourceAlgebra

variable {A : Type*} [ResourceAlgebra A]

/-- Addition is monotone on the left -/
theorem add_le_add_left {a b : A} (h : a ≤ b) (c : A) : c + a ≤ c + b := by
  rw [add_comm c a, add_comm c b]
  exact add_le_add_right h c

/-- Both sides monotone -/
theorem add_le_add {a b c d : A} (h1 : a ≤ c) (h2 : b ≤ d) : a + b ≤ c + d :=
  le_trans (add_le_add_right h1 b) (add_le_add_left h2 c)

end ResourceAlgebra

/-! ## Vectorial Accounts

    A vectorial account over k resource types is an element of A^k.
    Each component tracks a different resource.
-/

/-- A vectorial account over k resource types.

    Definition 7.1 (Meredith 2026): A vectorial account over resource types
    I = {1, ..., k} is an element A = (A₁, ..., Aₖ) of Aᵏ.

    For the Rho calculus, natural resource types include:
    - A_name: available fresh names
    - A_comm: available synchronizations
    - A_rep: available persistent-receive firings
-/
def VectorialAccount (A : Type*) (k : Nat) := Fin k → A

namespace VectorialAccount

variable {A : Type*} {k : Nat}

/-- Zero account -/
instance [Zero A] : Zero (VectorialAccount A k) where
  zero := fun _ => 0

/-- Component-wise addition -/
instance [Add A] : Add (VectorialAccount A k) where
  add a b := fun i => a i + b i

/-- Component-wise ordering -/
instance [LE A] : LE (VectorialAccount A k) where
  le a b := ∀ i, a i ≤ b i

/-- The account is affordable if costs don't exceed budget -/
def affordable [LE A] (cost budget : VectorialAccount A k) : Prop :=
  cost ≤ budget

/-- Debit: subtract cost from budget (requires subtraction) -/
def debit [Sub A] (budget cost : VectorialAccount A k) : VectorialAccount A k :=
  fun i => budget i - cost i

/-- Credit: add amount to budget -/
def credit [Add A] (budget amount : VectorialAccount A k) : VectorialAccount A k :=
  budget + amount

end VectorialAccount

/-! ## Weight Maps

    Definition 6.1 (Meredith 2026): A weight map assigns complex amplitudes
    to rewrite steps. For now, we use an abstract type for amplitudes.
-/

/-- A weight map assigns amplitudes to rewrite steps.

    Definition 6.1 (Meredith 2026): w_r^+ : HML(K) → ℂ assigns an amplitude
    to each rewrite step based on the logical formula satisfied by the source term.

    We abstract over the amplitude type (could be ℝ, ℂ, or any ring).
-/
structure WeightMap (S : GSLT) (W : Type*) where
  /-- The weight assigned to a rewrite step -/
  weight : {t u : S.Term} → S.Step t u → W

/-- The path amplitude is the product of weights along a path.

    Definition 6.3 (Meredith 2026): W(γ) = ∏ᵢ w_rᵢ⁺(ϕᵢ)
-/
def pathAmplitude {S : GSLT} {W : Type*} [Monoid W]
    (wm : WeightMap S W) : {t u : S.Term} → S.RewritePath t u → W
  | _, _, .nil _ => 1
  | _, _, .cons h rest => wm.weight h * pathAmplitude wm rest

/-- The action functional is the sum of log-weights along a path.

    Definition 6.4 (Meredith 2026): S[γ] = Σᵢ log w_rᵢ⁺(ϕᵢ)

    We represent this additively: the action is the sum of step actions.
-/
structure ActionMap (S : GSLT) (A : Type*) where
  /-- The action (log-weight) of a single step -/
  action : {t u : S.Term} → S.Step t u → A

/-- Total action along a path -/
def totalAction {S : GSLT} {A : Type*} [AddMonoid A]
    (am : ActionMap S A) : {t u : S.Term} → S.RewritePath t u → A
  | _, _, .nil _ => 0
  | _, _, .cons h rest => am.action h + totalAction am rest

/-! ## Cost Maps

    Definition 7.2 (Meredith 2026): A cost map assigns resource costs
    to rewrite steps.
-/

/-- A cost map assigns resource costs to rewrite steps.

    Definition 7.2 (Meredith 2026): c_r : HML(K) → Aᵏ assigns a cost vector
    to each rewrite step.
-/
structure CostMap (S : GSLT) (A : Type*) (k : Nat) where
  /-- The cost of a rewrite step -/
  cost : {t u : S.Term} → S.Step t u → VectorialAccount A k

/-- Total cost along a path -/
def totalCost {S : GSLT} {A : Type*} {k : Nat} [Add A] [Zero A]
    (cm : CostMap S A k) : {t u : S.Term} → S.RewritePath t u → VectorialAccount A k
  | _, _, .nil _ => 0
  | _, _, .cons h rest => cm.cost h + totalCost cm rest

/-! ## The Weighted GSLT

    Definition 6.2 (Meredith 2026): A weighted GSLT is a pair (S, w⁺).
-/

/-- A weighted GSLT bundles a GSLT with weight and cost maps.

    Combines Definitions 6.2 and 7.2.
-/
structure WeightedGSLT (W : Type*) (A : Type*) (k : Nat) where
  /-- The underlying GSLT -/
  gslt : GSLT
  /-- The weight map (amplitudes) -/
  weights : WeightMap gslt W
  /-- The cost map (resources) -/
  costs : CostMap gslt A k

/-! ## Conservation Theorem (Statement)

    Theorem 7.1 (Meredith 2026): In S†_C, for any closed rewrite path γ,
    the net account change is zero.

    A "closed path" is one that returns to its starting term.
    Conservation follows from the reversibility of S†: every forward
    debit is matched by a backward credit.
-/

/-- A closed path starts and ends at the same term -/
def isClosedPath {S : GSLT} {t : S.Term} (_path : S.RewritePath t t) : Prop := True

/-- Statement of the conservation theorem.

    Theorem 7.1 (Meredith 2026): For any closed rewrite path in the
    reversible envelope, the net resource change is zero.

    This is stated as a property that a cost map may satisfy.
    It holds automatically for cost maps derived from the reversible
    envelope construction where backward steps credit exactly what
    forward steps debit.
-/
def CostMap.conserves {S : GSLT} {A : Type*} {k : Nat}
    [AddGroup A] (cm : CostMap S A k) : Prop :=
  ∀ (t : S.Term) (γ : S.RewritePath t t), totalCost cm γ = 0

/-! ## Summary

This file establishes:

1. **ResourceAlgebra**: Commutative ordered monoid (Definition 7.1)
2. **VectorialAccount**: Vector of resource values across types
3. **WeightMap**: Amplitude assignment to steps (Definition 6.1)
4. **pathAmplitude**: Product of weights along a path (Definition 6.3)
5. **ActionMap/totalAction**: Additive action functional (Definition 6.4)
6. **CostMap**: Resource cost assignment (Definition 7.2)
7. **WeightedGSLT**: Bundled GSLT + weights + costs (Definition 6.2)
8. **Conservation statement**: Net cost = 0 on closed paths (Theorem 7.1)

**Paper Coverage**: Definitions 6.1–6.4, 7.1–7.2; Theorem 7.1 (statement)

**No sorry statements** — everything is fully proven or cleanly stated.

**Next**: `Dynamics/ExtendedHML.lean` (Definition 8.1)
-/

end Mettapedia.GSLT
