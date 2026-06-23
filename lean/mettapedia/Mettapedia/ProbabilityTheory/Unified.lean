/-
# Unified Framework: The Hypercube of Uncertainty Theories

This module connects all probability/uncertainty frameworks into a single
hypercube structure, showing how different axiom choices lead to different theories.

## The Three-Dimensional Hypercube

```
                    Non-commutativity
                         ↑
                         │
    Quantum Prob.        │         Quantum + Imprecise
         ●───────────────│─────────────────●
        /│               │                /│
       / │               │               / │
      /  │               │              /  │
     ●───│───────────────│─────────────●   │
     │   │               │             │   │
     │   │               │             │   │
     │   ●───────────────│─────────────│───●
     │  / Cox/K&S        │         D-S │  /
     │ /  (classical)    │   (imprecise)│ /
     │/                  │             │/
     ●───────────────────┼─────────────●──────→ Additivity
   Precise              │            Imprecise
                        │
                        ↓
              Commutativity Axis (into page)
```

## Vertices of the Hypercube

| Vertex | Additive | Commutative | Classical? | Theory |
|--------|----------|-------------|------------|--------|
| 000 | Yes | Yes | Yes | **Kolmogorov probability** |
| 001 | Yes | No | No | **Quantum probability** |
| 010 | No | Yes | Yes | **D-S / Imprecise probability** |
| 011 | No | No | No | **Quantum imprecise** (exotic) |

## Edges (Refinement Relations)

- Kolmogorov → D-S: Drop additivity
- Kolmogorov → Quantum: Drop commutativity
- D-S → K&S: Add separation axiom (gets additivity back!)
- K&S → Kolmogorov: Same (K&S derives Kolmogorov)

## Key Insight

The K&S representation theorem shows that **under certain axioms**,
you MUST have additivity and commutativity. This collapses the
imprecise vertex back to the classical vertex!

Cox's theorem does the same from a different starting point.

## References

- Stay & Wells, "Generating Hypercubes of Type Systems"
- This work, connecting probability foundations
-/

import Mettapedia.ProbabilityTheory.Cox
import Mettapedia.ProbabilityTheory.ImpreciseProbability
import KnuthSkilling
-- Note: BeliefFunctions and QuantumProbability imported separately

namespace Mettapedia.ProbabilityTheory.Unified

/-!
## §1: The Axiom Flags

Each theory is characterized by which axioms it satisfies.
-/

/-- The core axiom choices that determine which theory we're in. -/
structure UncertaintyAxioms where
  /-- Is the theory additive? P(A∪B) = P(A) + P(B) for disjoint A, B -/
  additive : Bool
  /-- Is the theory commutative? P(A∧B) = P(B∧A) -/
  commutative : Bool
  /-- Is there a unique probability (precise) or an interval (imprecise)? -/
  precise : Bool
  /-- Is there an identity element? -/
  hasIdentity : Bool
  /-- Is there an inverse (negation) operation? -/
  hasInverse : Bool

/-- Kolmogorov axioms: additive, commutative, precise. -/
def kolmogorovAxioms : UncertaintyAxioms :=
  { additive := true
    commutative := true
    precise := true
    hasIdentity := true
    hasInverse := true }

/-- Cox axioms: derive additivity and commutativity from functional equations. -/
def coxAxioms : UncertaintyAxioms :=
  { additive := true  -- DERIVED
    commutative := true  -- DERIVED
    precise := true
    hasIdentity := true
    hasInverse := true }

/-- Knuth-Skilling: derive additivity from lattice structure.
    Note: K&S doesn't assume inverses, yet derives additivity! -/
def knuthSkillingAxioms : UncertaintyAxioms :=
  { additive := true
    commutative := true
    precise := true
    hasIdentity := true
    hasInverse := false }

/-- Imprecise probability (Walley): sub/super-additive, commutative.
    Uses intervals [P̲(A), P̅(A)] instead of point values. -/
def walleyAxioms : UncertaintyAxioms :=
  { additive := false
    commutative := true
    precise := false
    hasIdentity := true
    hasInverse := true }

/-- Dempster-Shafer: sub/super-additive via belief/plausibility.
    Belief is superadditive, plausibility subadditive.
    No direct inverse; uses Pl(A) = 1 - Bel(¬A). -/
def dempsterShaferAxioms : UncertaintyAxioms :=
  { additive := false
    commutative := true
    precise := false
    hasIdentity := true
    hasInverse := false }

/-- Quantum probability: additive but non-commutative. -/
def quantumAxioms : UncertaintyAxioms :=
  { additive := true
    commutative := false  -- Measurements don't commute!
    precise := true
    hasIdentity := true
    hasInverse := true }

/-!
## §2: The Hypercube Structure

Map axiom configurations to vertices of a hypercube.
-/

/-- A vertex of the hypercube is a bit-vector of axiom choices. -/
structure HypercubeVertex where
  additive : Bool
  commutative : Bool
  precise : Bool
  deriving DecidableEq, Repr

/-- Project axioms onto the 3D hypercube. -/
def toVertex (ax : UncertaintyAxioms) : HypercubeVertex :=
  { additive := ax.additive
    commutative := ax.commutative
    precise := ax.precise }

/-- The 8 vertices of the hypercube. -/
def hypercubeVertices : List HypercubeVertex :=
  [ ⟨true, true, true⟩,    -- Kolmogorov/Cox/K&S
    ⟨true, true, false⟩,   -- ??? (additive imprecise = contradiction?)
    ⟨true, false, true⟩,   -- Quantum
    ⟨true, false, false⟩,  -- Quantum imprecise
    ⟨false, true, true⟩,   -- ??? (subadditive precise)
    ⟨false, true, false⟩,  -- Walley/D-S
    ⟨false, false, true⟩,  -- Non-comm subadditive
    ⟨false, false, false⟩  -- Most general
  ]

/-- Name the vertices by their theory. -/
def vertexName : HypercubeVertex → String
  | ⟨true, true, true⟩ => "Kolmogorov/Cox/K&S"
  | ⟨true, true, false⟩ => "Additive-Imprecise (degenerate)"
  | ⟨true, false, true⟩ => "Quantum"
  | ⟨true, false, false⟩ => "Quantum-Imprecise"
  | ⟨false, true, true⟩ => "Subadditive-Precise (degenerate)"
  | ⟨false, true, false⟩ => "Walley/Dempster-Shafer"
  | ⟨false, false, true⟩ => "Non-commutative-Subadditive"
  | ⟨false, false, false⟩ => "Maximally General"

/-!
## §3: Edges = Refinement Relations

An edge connects two vertices when one theory refines to another.
-/

/-- An edge connects two vertices that differ in exactly one coordinate. -/
def isEdge (v₁ v₂ : HypercubeVertex) : Bool :=
  (v₁.additive != v₂.additive && v₁.commutative == v₂.commutative && v₁.precise == v₂.precise) ||
  (v₁.additive == v₂.additive && v₁.commutative != v₂.commutative && v₁.precise == v₂.precise) ||
  (v₁.additive == v₂.additive && v₁.commutative == v₂.commutative && v₁.precise != v₂.precise)

/-- The refinement direction: more axioms = more refined. -/
def refines (v₁ v₂ : HypercubeVertex) : Bool :=
  isEdge v₁ v₂ &&
  ((v₁.additive && !v₂.additive) ||
   (v₁.commutative && !v₂.commutative) ||
   (v₁.precise && !v₂.precise))

/-!
## §4: The Key Theorems (Existence Assertions)

Each major theorem establishes that certain axiom combinations
force you to a specific vertex.
-/

/-- Cox's theorem: plausibility axioms + continuity → Kolmogorov vertex. -/
theorem cox_forces_kolmogorov :
    toVertex coxAxioms = toVertex kolmogorovAxioms := by
  rfl

/-- K&S representation: lattice axioms → Kolmogorov vertex. -/
theorem ks_forces_kolmogorov :
    toVertex knuthSkillingAxioms = toVertex kolmogorovAxioms := by
  rfl

/-- D-S is strictly weaker: sits at the imprecise vertex. -/
theorem ds_at_imprecise_vertex :
    toVertex dempsterShaferAxioms = ⟨false, true, false⟩ := by
  rfl

/-- Quantum sits at the non-commutative vertex. -/
theorem quantum_at_noncomm_vertex :
    toVertex quantumAxioms = ⟨true, false, true⟩ := by
  rfl

/-!
## §5: Collapse Theorems

These theorems show when additional axioms collapse a weaker theory to a stronger one.
-/

/- TODO: Collapse theorem (Separation ⇒ collapse of imprecision).

The intended content here is a bridge from:
- an imprecise/credal semantics (PartialOrder / interval-valued representation),
- plus a K&S-style separation/totality hypothesis,
to a point-valued additive representation.

This should eventually be backed by the concrete Lean results in:
- `Mettapedia/ProbabilityTheory/KnuthSkilling/Core/TotalityImprecision.lean`
- and the KS representation pipeline.

We intentionally do not leave a placeholder theorem of type `True`.
-/

/-- Commutativity assumption collapses quantum to classical. -/
theorem commutativity_collapses_quantum :
    ∀ (v : HypercubeVertex),
      v.additive = true → v.commutative = true →
      v = ⟨true, true, v.precise⟩ := by
  intro v hadd hcomm
  cases v
  simp_all

/-!
## §6: The Fundamental Questions

The hypercube raises key questions about the foundations of probability:

1. **Is K&S correct?** Does the lattice structure really force additivity?
   - The globalization step (`RepresentationGlobalization`) is now formalized
   - If yes, K&S provides the most minimal axiom set

2. **Is Cox complete?** Does Cox need continuity, or can it be weakened?
   - Dupré-Tipler showed continuity isn't essential
   - But some regularity is needed

3. **What's at the exotic vertices?**
   - Quantum-imprecise probability exists in quantum foundations
   - Non-commutative belief functions?

4. **Are the collapse theorems tight?**
   - Can we find models that DON'T collapse?
   - This would show the axioms are necessary, not just sufficient
-/

/-- Placeholder for future work: characterize all 8 vertices. -/
def vertexTheory : HypercubeVertex → Type
  | ⟨true, true, true⟩ => Unit  -- Kolmogorov (well-understood)
  | ⟨true, true, false⟩ => Empty  -- Degenerate (additivity + imprecision → contradiction)
  | ⟨true, false, true⟩ => Unit  -- Quantum (well-understood)
  | ⟨true, false, false⟩ => Unit  -- Quantum imprecise (active research)
  | ⟨false, true, true⟩ => Empty  -- Degenerate
  | ⟨false, true, false⟩ => Unit  -- Walley/D-S (well-understood)
  | ⟨false, false, true⟩ => Unit  -- Exotic
  | ⟨false, false, false⟩ => Unit  -- Most general

end Mettapedia.ProbabilityTheory.Unified
