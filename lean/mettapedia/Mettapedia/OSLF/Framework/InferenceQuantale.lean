import Mettapedia.OSLF.Framework.GSLTEvidence

/-!
# The Inference Quantale: Unifying KS, Meredith, and WM-PLN

Three frameworks for reasoning under uncertainty are instances of one
construction — `GSLTEvidenceAssignment` (from `GSLTEvidence.lean`):

| Framework | State | Query | V |
|-----------|-------|-------|---|
| Knuth-Skilling | Models (Finset) | Propositions | ℝ≥0∞ |
| Meredith | T(S)/∼ (bisim) | HML(K) formulae | ℂ |
| WM-PLN | Multiset T | DecProp T | BinaryEvidence |

The value monoids are connected by shadow morphisms:

    ℂ  ──|·|²──▶  ℝ≥0  ──count──▶  BinaryEvidence  ──str──▶  [0,1]

**Critical**: The Born rule |·|² is NOT additive (quantum interference).
The shadow chain is functorial only post-Born.

## References

- Knuth & Skilling, "Foundations of Inference" (2012)
- L. Gregory Meredith, "Computation, Causality, and Consciousness" (2026)
-/

namespace Mettapedia.OSLF.Framework.InferenceQuantale

open Mettapedia.OSLF.Framework.GSLTEvidence

/-! ## Shadow Morphisms -/

/-- Lift an evidence assignment along an additive morphism between
    value monoids.  If you have evidence valued in V₁ and a
    monoid hom f : V₁ →+ V₂, you get evidence valued in V₂.

    This is the key functorial operation: shadow morphisms
    between value monoids induce morphisms between evidence assignments. -/
def shadow
    {State Query V₁ V₂ : Type*}
    [AddCommMonoid State] [AddCommMonoid V₁] [AddCommMonoid V₂]
    (ea : GSLTEvidenceAssignment State Query V₁)
    (f : AddMonoidHom V₁ V₂) :
    GSLTEvidenceAssignment State Query V₂ where
  extract W q := f (ea.extract W q)
  extract_add W₁ W₂ q := by
    simp only [ea.extract_add]
    exact f.map_add _ _
  extract_zero q := by
    simp only [ea.extract_zero]
    exact f.map_zero

/-- Shadow preserves the profile hom structure. -/
theorem shadow_profileHom
    {State Query V₁ V₂ : Type*}
    [AddCommMonoid State] [AddCommMonoid V₁] [AddCommMonoid V₂]
    (ea : GSLTEvidenceAssignment State Query V₁)
    (f : AddMonoidHom V₁ V₂)
    (W : State) (q : Query) :
    (shadow ea f).toProfileHom W q = f (ea.toProfileHom W q) := rfl

/-! ## Composition of Shadows -/

/-- Composing two shadows = shadowing the composed morphism. -/
theorem shadow_comp
    {State Query V₁ V₂ V₃ : Type*}
    [AddCommMonoid State] [AddCommMonoid V₁]
    [AddCommMonoid V₂] [AddCommMonoid V₃]
    (ea : GSLTEvidenceAssignment State Query V₁)
    (f : AddMonoidHom V₁ V₂) (g : AddMonoidHom V₂ V₃)
    (W : State) (q : Query) :
    (shadow (shadow ea f) g).extract W q =
    (shadow ea (g.comp f)).extract W q := rfl

/-- The identity shadow is the identity. -/
theorem shadow_id
    {State Query V : Type*}
    [AddCommMonoid State] [AddCommMonoid V]
    (ea : GSLTEvidenceAssignment State Query V)
    (W : State) (q : Query) :
    (shadow ea (AddMonoidHom.id V)).extract W q = ea.extract W q := rfl

/-! ## The Born Rule Obstruction

The Born rule |z|² : ℂ → ℝ≥0 is NOT an AddMonoidHom.
|z₁ + z₂|² ≠ |z₁|² + |z₂|² in general — this IS quantum interference.

The shadow chain is therefore:

    ℂ  ──|·|²──▶  ℝ≥0  ──count──▶  BinaryEvidence  ──str──▶  [0,1]
         ╲                   ╱
          not additive      additive

The first arrow (Born rule) breaks additivity.  The remaining
arrows preserve it.  This is why quantum mechanics is fundamentally
different from classical probability.

In Meredith's framework, the ℂ-valued evidence assignment IS additive
(his weight map w satisfies w(P|Q) = w(P) + w(Q)).  The Born rule
projects to classical probabilities, losing the interference structure.
Our WM-PLN evidence framework lives at the post-Born level.

**The universal theorem (post-Born):** Every GSLT with parallel
composition has a canonical BinaryWorldModel (proven in GSLTWorldModel.lean).

**The universal theorem (pre-Born):** Every GSLT has a canonical
GSLTEvidenceAssignment over ℂ — but this does NOT shadow additively
to a BinaryWorldModel.  The non-additivity IS quantum interference.

**Connection to Knuth-Skilling:** KS derives probability from valuation
axioms on a distributive lattice.  Our GSLTEvidenceAssignment IS a
KS valuation when V = ℝ≥0∞ and the observation algebra is a lattice.
The sum rule (v(A∨B) = v(A) + v(B) for disjoint A,B) is exactly
extract_add when state composition = disjoint union of models. -/

/-! ## The Unified Picture

The ultimate core abstraction is:

1. `GSLTEvidenceAssignment State Query V` — a single additive morphism
   State →+ (Query → V), parameterized by value monoid V.

2. `shadow f` — transforms V₁-valued to V₂-valued assignments
   along any AddMonoidHom f : V₁ →+ V₂.

3. `factors_through_canonical` (from GSLTEvidence.lean) — every
   assignment factors through the terminal profile `Query → V`.

KS, Meredith, and WM-PLN are all instances, differing only in V.
The shadow chain connects them.  The Born rule is the one place
where the chain breaks additivity — and that breaking IS the
content of quantum mechanics.

This means WM-PLN is not "a reasoning system."  It is the canonical
post-Born inference layer for ANY computational structure.  Every
GSLT has a natural PLN over it. -/

end Mettapedia.OSLF.Framework.InferenceQuantale
