import Mettapedia.GSLT.Meredith.Bisimulation
import Mettapedia.Algebra.QuantaleWeakness

/-!
# GSLT Bisimulation ↔ Quantale Weakness Bridge

The central bridge connecting Greg Meredith's operational ontology
to Ben Goertzel's evidence/weakness framework.

## The Key Correspondence

    GSLT operational semantics    ↔    Quantale weakness theory
    ──────────────────────────────────────────────────────────────
    Bisimulation quotient U       =    Universe of outcomes
    Bisimulation class [p]        =    An outcome / atomic event
    Distinction event {(u,v)|u≠v} =    The set measured by weakness
    Weight map μ : U → Q          =    Evidence/probability assignment
    weakness(distinction)          =    Logical entropy / evidence strength

## Why This Matters for PNP

Ben's proof uses weakness over quantales as the foundation for
plausibility theory. Greg's framework says the "true" sample space
is the bisimulation quotient. This means:

1. Evidence strength IS operational distinguishability
2. The quantale weakness order on evidence theories corresponds to
   the hypercube of type systems (weaker types = coarser quotient)
3. PLN's imprecise probabilities arise from coarsening the quotient

## References

- Meredith, "Computation, Causality, and Consciousness" (2026)
- Goertzel, "Weakness and Its Quantale"
- Bennett, "Notes on the Concept of Information" (1973, 2003)
-/

namespace Mettapedia.GSLT.Meredith.WeaknessBridge

open Mettapedia.GSLT
open Mettapedia.GSLT.Meredith.Bisimulation
open Mettapedia.Algebra.QuantaleWeakness

/-! ## GSLT Evidence Assignment -/

variable (S : GSLT)

/-- An evidence assignment on a finite GSLT: a finite index type for
    bisimulation classes and a weight function to a quantale Q.

    This is the bridge data: once you have this, you can compute
    weakness over the bisimulation quotient.
-/
structure GSLTEvidence (U : Type*) (Q : Type*) [Fintype U] [Monoid Q] where
  /-- Weight assigned to each bisimulation class. -/
  weight : U → Q

variable {U : Type*} [Fintype U] [DecidableEq U] {Q : Type*} [Monoid Q] [CompleteLattice Q]

set_option linter.unusedSectionVars false

/-- Convert a GSLT evidence assignment to a quantale weight function. -/
def GSLTEvidence.toWeightFn (ev : GSLTEvidence U Q) : WeightFunction U Q :=
  ⟨ev.weight⟩

/-- Compute weakness of an event over the GSLT's bisimulation quotient. -/
noncomputable def gsltWeakness (ev : GSLTEvidence U Q)
    (event : Finset (U × U)) : Q :=
  weakness ev.toWeightFn event

/-! ## Distinction and Non-Distinction Events -/

/-- Weakness of the distinction event: pairs of different classes.
    This is the "logical entropy" — the total distinguishability. -/
noncomputable def distinctionWeakness (ev : GSLTEvidence U Q) : Q :=
  gsltWeakness ev (distinctionEvent (U := U))

/-- Weakness of the non-distinction event: diagonal pairs.
    This is the "self-similarity" or "coherence" measure. -/
noncomputable def nonDistinctionWeakness (ev : GSLTEvidence U Q) : Q :=
  gsltWeakness ev (nonDistinctionEvent (U := U))

/-! ## Bennett's Cardinality Remark

    The distinction and non-distinction events partition U × U:
    |distinction| + |non-distinction| = |U|²

    This follows from `distinction_card` + `nonDistinction_card` in
    QuantaleWeakness.lean:
      |distinction| = |U|² - |U|  and  |non-distinction| = |U|
    so their sum is |U|² (by Nat.sub_add_cancel with |U| ≤ |U|²).

    We omit the Lean proof here to avoid ℕ subtraction bookkeeping,
    since the key result is `transport_commutes` below.
-/

/-! ## Transport Along Quantale Morphisms -/

section Transport

variable {Q' : Type*} [Monoid Q'] [CompleteLattice Q']

/-- Transport evidence along a quantale morphism. -/
def transportEvidence (ev : GSLTEvidence U Q) (g : QuantaleHom Q Q') :
    GSLTEvidence U Q' :=
  ⟨g ∘ ev.weight⟩

/-- Weakness transports along quantale morphisms.

    `g(weakness_Q(H)) = weakness_{Q'}(H)` over transported evidence.
-/
theorem transport_commutes (ev : GSLTEvidence U Q) (g : QuantaleHom Q Q')
    (H : Finset (U × U)) :
    g (gsltWeakness ev H) = gsltWeakness (transportEvidence ev g) H := by
  unfold gsltWeakness transportEvidence GSLTEvidence.toWeightFn
  exact QuantaleHom.map_weakness g ev.toWeightFn H

end Transport

/-! ## Connection to the Hypercube

    The hypercube of type systems (§5.6) orders vertices by sort assignment.
    A coarser type system (fewer sorts at □) gives a coarser bisimulation
    quotient (fewer observable distinctions).

    Conjecture (to be proved):
    If vertex A ≤ vertex B in the hypercube order, then
    distinction_weakness(A) ≤ distinction_weakness(B).

    This would formalize: **weaker type systems have less evidence**.
    PLN's imprecise probabilities = weakness from coarsened quotients.
-/

-- The monotonicity principle connecting type system strength to weakness
-- is the key theorem that would unify Greg's and Ben's frameworks.
-- It requires:
-- 1. The hypercube vertex order from ModalHypercube.lean
-- 2. A map from vertices to bisimulation granularities
-- 3. Monotonicity of weakness under coarsening
-- This is the program for future work.

end Mettapedia.GSLT.Meredith.WeaknessBridge
