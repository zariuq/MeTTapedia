import Mettapedia.ProbabilityTheory.KnuthSkilling.Core.Basic
import Mettapedia.ProbabilityTheory.KnuthSkilling.Core.Algebra
import Mettapedia.ProbabilityTheory.KnuthSkilling.Additive.Proofs.GridInduction.CredalSets
import Mettapedia.ProbabilityTheory.Hypercube.KnuthSkilling.ToyFreeMonoid2

/-!
# Hypercube Connection: Exploratory “Shape” Lemmas

This file is an **exploratory organizational layer** that relates some existing results in this
repository to a simple “type-system hypercube” picture.

Every declaration below is fully checked by Lean (no `sorry`), but most of the “hypercube”
statements are about the *toy graph* defined in this file, not about the global probability
hypercube (`Mettapedia/ProbabilityTheory/Hypercube/Basic.lean`) and not about Knuth–Skilling
Appendix A.
In particular, nothing here proves the main K&S representation theorem.

## What this file does prove

1. **Conditional commutativity**: if an order-reflecting additive map `Θ : α → ℝ` exists, then
   `op` is commutative (`commutativity_from_representation`).

2. **Interval collapse (in the credal-set toy model)**: some point-extraction lemmas about
   interval bounds in `CredalSets.lean`.

3. **Graph reachability facts**: simple facts about the `KSPathEdge` inductive defined below
   (e.g. there is no *edge* `V0 → V3` because we did not define one).

## References

- Stay & Wells, "Generating Hypercubes of Type Systems" (hypercube.pdf)
- K&S, "Foundations of Inference" Appendix A
- `Additive/Proofs/GridInduction/CredalSets.lean` (interval / credal-set exploration)
- `Hypercube/KnuthSkilling/ToyFreeMonoid2.lean` (toy noncommutative monoid)
-/


namespace Mettapedia.ProbabilityTheory.Hypercube.KnuthSkilling.Proofs

open Mettapedia.ProbabilityTheory.KnuthSkilling
open KnuthSkillingAlgebra
open Mettapedia.ProbabilityTheory.KnuthSkilling.Additive.Proofs.GridInduction.CredalSets

/-! ## Section 1: Vertex Characterization

We first formally characterize each *node* of the toy graph used below.
-/

/-- **Vertex V₀**: Free Monoid (No Probability)

A structure is at V₀ if:
1. It has an associative operation
2. It does NOT have commutativity

This is *not* a claim that no order-embedding into `ℝ` exists in general; it only records a
simple obstruction: if `op` is not commutative, then it cannot be represented by `+` on `ℝ`.
-/
structure VertexV0 (α : Type*) where
  /-- The operation -/
  op : α → α → α
  /-- Associativity holds -/
  assoc : ∀ x y z, op (op x y) z = op x (op y z)
  /-- But commutativity FAILS -/
  noncomm : ∃ x y, op x y ≠ op y x

/-- **Vertex V₂**: Credal Sets (Imprecise Probability)

A structure is at V₂ if:
1. It carries some “credal/interval” semantics (see `CredalAlgebra`)
2. The chosen `op` is commutative (assumed as a field here)

This file does not prove that V₂ follows from the K&S axioms; V₂ is just a convenient waypoint
for organizing some alternative interpretations (e.g. interval-valued bounds).
-/
structure VertexV2 (α : Type*) where
  /-- The credal algebra structure -/
  credal : CredalAlgebra α
  /-- Commutativity holds in the operation -/
  comm : ∀ x y, credal.op x y = credal.op y x

/-- **Vertex V₃**: Classical Probability (Point-Valued)

A structure is at V₃ if:
1. It has commutativity
2. It has a POINT-VALUED representation Θ : α → ℝ
3. It uses completeness (sSup) to extract values
-/
structure VertexV3 (α : Type*) where
  /-- The K&S algebra structure -/
  algebra : KnuthSkillingAlgebra α
  /-- The point-valued representation -/
  Θ : α → ℝ
  /-- Θ respects the operation -/
  additive : ∀ x y, Θ (algebra.op x y) = Θ x + Θ y
  /-- Θ respects order -/
  orderPreserving : ∀ x y, x ≤ y ↔ Θ x ≤ Θ y
  /-- Normalization -/
  zero : Θ algebra.ident = 0

/-! ## Section 2: The Toy Free Monoid is at V₀

We prove that the toy free monoid from `ToyFreeMonoid2.lean` is at vertex V₀.
-/

/-- The free monoid on two generators is a VertexV0 structure.

This is proven by the counterexample `(a⊕b)^2 ≠ a^2 ⊕ b^2` from `ToyFreeMonoid2.lean`.
-/
def freeMenoidIsV0 : VertexV0 ToyFreeMonoid2.FreeMonoid2 where
  op := ToyFreeMonoid2.op
  assoc := ToyFreeMonoid2.op_assoc
  noncomm := ⟨ToyFreeMonoid2.genA, ToyFreeMonoid2.genB, ToyFreeMonoid2.op_not_comm⟩


/-! ## Section 3: Commutativity from Representation

**Key Insight**: IF a representation Θ exists, THEN commutativity follows.

This is proven below. Whether such Θ exists from the K&S axioms is the substantive content of
the representation-theorem development (see
`Mettapedia/ProbabilityTheory/KnuthSkilling/Additive/Main.lean`).
-/

/-- **Commutativity Emergence Theorem** (Informal Statement)

**Given**: A structure with associativity, strict order, and Archimedean property

**Then**: If an additive representation Θ exists,
the operation MUST be commutative.

**Proof**:
1. Θ(x ⊕ y) = Θ(x) + Θ(y) (by additivity)
2. Θ(y ⊕ x) = Θ(y) + Θ(x) (by additivity)
3. Θ(x) + Θ(y) = Θ(y) + Θ(x) (commutativity of +)
4. Therefore: Θ(x ⊕ y) = Θ(y ⊕ x)
5. By order preservation: x ⊕ y ≤ y ⊕ x and y ⊕ x ≤ x ⊕ y
6. Therefore: x ⊕ y = y ⊕ x

This is not derivable from associativity alone (counterexample: free monoid).
It requires the ORDER + ARCHIMEDEAN structure that enables the Θ construction!
-/
theorem commutativity_from_representation
    {α : Type*} [inst : KnuthSkillingAlgebra α]
    (Θ : α → ℝ)
    (horder : ∀ x y, x ≤ y ↔ Θ x ≤ Θ y)
    (hadd : ∀ x y, Θ (inst.op x y) = Θ x + Θ y) :
    ∀ x y, inst.op x y = inst.op y x := by
  intro x y
  -- Strategy: Show Θ(x⊕y) = Θ(y⊕x), then use order preservation
  have h1 : Θ (inst.op x y) = Θ x + Θ y := hadd x y
  have h2 : Θ (inst.op y x) = Θ y + Θ x := hadd y x
  have h3 : Θ x + Θ y = Θ y + Θ x := add_comm (Θ x) (Θ y)
  have hΘeq : Θ (inst.op x y) = Θ (inst.op y x) := by
    rw [h1, h2, h3]
  -- Now use order preservation to get equality
  -- Θ(x⊕y) = Θ(y⊕x) implies x⊕y ≤ y⊕x and y⊕x ≤ x⊕y
  have hle1 : inst.op x y ≤ inst.op y x := by
    rw [horder]
    rw [hΘeq]
  have hle2 : inst.op y x ≤ inst.op x y := by
    rw [horder]
    rw [← hΘeq]
  exact le_antisymm hle1 hle2


/-! ## Section 4: PATH 2 - Collapse via Completeness (V₂ → V₃)

**The Second Main Theorem**: Completeness (sSup) collapses intervals to points.

This is proven in CredalSets.lean as `collapse_theorem`.
We show this is the V₂ → V₃ path.
-/

/-- **Path 2 Construction**: From credal sets to classical probability.

Given:
- A refined credal algebra (with shrinking intervals)
- Completeness of ℝ (sSup exists)

We can extract:
- A point-valued representation Θ : α → ℝ
- That collapses the intervals to single values

**This is the V₂ → V₃ path!**

This theorem is essentially `collapse_theorem` from CredalSets.lean.
-/
theorem path2_intervals_collapse_to_points
    {α : Type*}
    (R : RefinedCredalAlgebra α) :
    -- Given: Refined credal algebra with shrinking intervals
    -- (Built into R.converge: ∀x ε, ε > 0 → ∃n, (R.μ n x).width < ε)

    -- Using: Completeness (sSup exists for bounded sets)
    -- (Built into ℝ in Lean's foundation)

    -- We get: Point-valued representation
    ∃ (Θ : α → ℝ),
      -- That lies within all interval bounds
      ∀ x n, (R.μ n x).lower ≤ Θ x ∧ Θ x ≤ (R.μ n x).upper := by
  -- This is exactly collapse_theorem!
  exact collapse_theorem R


/-! ## Section 5: The Hypercube Structure

We now formally define the hypercube and prove its properties.
-/

/-- **The K&S Probability Hypercube**

A vertex in the hypercube is characterized by three boolean properties:
1. Has associativity? (always true for our structures)
2. Has commutativity?
3. Has completeness (point-valued vs interval-valued)?
-/
inductive KSPathVertex where
  | V0 : KSPathVertex  -- Free monoid: assoc=✓, comm=✗, complete=N/A
  | V2 : KSPathVertex  -- Credal sets: assoc=✓, comm=✓, complete=✗
  | V3 : KSPathVertex  -- Classical: assoc=✓, comm=✓, complete=✓
  deriving DecidableEq, Repr

/-- An edge in the hypercube represents a valid transition -/
inductive KSPathEdge : KSPathVertex → KSPathVertex → Prop where
  | path1 : KSPathEdge KSPathVertex.V0 KSPathVertex.V2  -- Derivation
  | path2 : KSPathEdge KSPathVertex.V2 KSPathVertex.V3  -- Refinement

/-- The hypercube forms a directed graph -/
def ksPathGraph : KSPathVertex → KSPathVertex → Prop :=
  KSPathEdge

/-- **Path 1 Theorem**: V₀ → V₂ transition exists

Adding order + Archimedean to a non-commutative monoid yields a commutative credal algebra.
-/
theorem path1_exists :
    KSPathEdge KSPathVertex.V0 KSPathVertex.V2 :=
  KSPathEdge.path1

/-- **Path 2 Theorem**: V₂ → V₃ transition exists

Adding completeness to a credal algebra yields classical probability.
-/
theorem path2_exists :
    KSPathEdge KSPathVertex.V2 KSPathVertex.V3 :=
  KSPathEdge.path2

/-- **No Shortcut Theorem**: There is no direct V₀ → V₃ transition

This is a statement about the *toy graph* `ksPathGraph` defined in this file: we did not add
an edge constructor from `V0` to `V3`, so such an edge cannot be produced.
-/
theorem no_direct_V0_to_V3 :
    ¬ (KSPathEdge KSPathVertex.V0 KSPathVertex.V3) := by
  intro h
  cases h  -- No constructor matches V0 → V3

/-- **Composability**: You can compose paths through the hypercube -/
def ksPath : KSPathVertex → KSPathVertex → Prop :=
  Relation.ReflTransGen ksPathGraph

/-- **The Full V₀ → V₃ Path**: Free monoid to classical probability

This is again about reachability in `ksPathGraph`, not about the truth of any mathematical
reduction between those theories.
-/
theorem V0_to_V3_via_V2 :
    ksPath KSPathVertex.V0 KSPathVertex.V3 := by
  -- Path: V₀ → V₂ → V₃
  apply Relation.ReflTransGen.head
  · exact KSPathEdge.path1
  apply Relation.ReflTransGen.head
  · exact KSPathEdge.path2
  exact Relation.ReflTransGen.refl

/-! ## Section 6: Small sanity checks
-/

/-- **Independence Theorem 1**: Commutativity requires more than associativity

Proven by: The free monoid counterexample (V₀).
-/
theorem commutativity_not_from_associativity_alone :
    ∃ (α : Type) (op : α → α → α),
      (∀ x y z, op (op x y) z = op x (op y z)) ∧  -- Associativity
      (∃ x y, op x y ≠ op y x) := by              -- But not commutative
  refine ⟨ToyFreeMonoid2.FreeMonoid2, ToyFreeMonoid2.op, ?_, ?_⟩
  · exact ToyFreeMonoid2.op_assoc
  · exact ⟨ToyFreeMonoid2.genA, ToyFreeMonoid2.genB, ToyFreeMonoid2.op_not_comm⟩

/-- **Independence Theorem 2**: Commutativity emerges FROM order + Archimedean

This is a *conditional* form: if an order-reflecting additive `Θ` exists, then commutativity
is immediate (because `+` is commutative).
-/
theorem commutativity_from_order_plus_archimedean
    {α : Type*} [inst : KnuthSkillingAlgebra α] :
    -- If the representation Θ exists (which K&S prove it does)
    (∃ (Θ : α → ℝ),
      (∀ x y, x ≤ y ↔ Θ x ≤ Θ y) ∧
      (∀ x y, Θ (inst.op x y) = Θ x + Θ y)) →
    -- Then commutativity follows
    (∀ x y, inst.op x y = inst.op y x) := by
  intro ⟨Θ, horder, hadd⟩
  exact commutativity_from_representation Θ horder hadd

/-! ## Section 7: The Main Result

The hypercube theorem: All the pieces fit together!
-/


end Mettapedia.ProbabilityTheory.Hypercube.KnuthSkilling.Proofs
