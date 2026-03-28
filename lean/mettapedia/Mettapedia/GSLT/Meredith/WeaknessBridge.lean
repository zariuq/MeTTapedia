import Mettapedia.GSLT.Meredith.Bisimulation
import Mettapedia.GSLT.Logic.LogicalMetric
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

/-! ## Finite-Depth Observation ⇒ Distinction

The abstract weakness bridge becomes operational once finite-depth HML
distinctions are tied back to bisimulation classes.  The only global hypothesis
needed is the sound direction of Meredith's adequacy theorem:

* bisimilar terms satisfy the same HML formulae.

Under that hypothesis, any depth-bounded distinguishing witness is already a
genuine distinction event in the bisimulation quotient.  Equivalently, the
binary-valued logical metric approximation `d_n` can only take the value `1`
on genuinely distinct classes.
-/

section ObservationBridge

variable {S : GSLT} [HasMinimalContexts S]

theorem no_distinguishingWitness_of_hmlEquiv {n : Nat} {t u : S.Term}
    (h : HMLFormula.hmlEquiv S t u) :
    ¬ HMLFormula.DistinguishingWitness (S := S) n t u := by
  rintro ⟨ϕ, _, hdist⟩
  exact hdist (h ϕ)

theorem distinguishingWitness_implies_not_hmlEquiv {n : Nat} {t u : S.Term}
    (h : HMLFormula.DistinguishingWitness (S := S) n t u) :
    ¬ HMLFormula.hmlEquiv S t u := by
  intro hhml
  exact no_distinguishingWitness_of_hmlEquiv (S := S) (n := n) hhml h

theorem bisimilar_implies_hmlEquivUpTo_of_adequacySound
    (hAdeq : S.adequacy_sound) {n : Nat} {t u : S.Term}
    (hbis : S.Bisimilar t u) :
    HMLFormula.hmlEquivUpTo (S := S) n t u := by
  exact HMLFormula.hmlEquiv_implies_hmlEquivUpTo (S := S) (hAdeq hbis) n

theorem distinguishingWitness_implies_distinguished_of_adequacySound
    (hAdeq : S.adequacy_sound) {n : Nat} {t u : S.Term}
    (h : HMLFormula.DistinguishingWitness (S := S) n t u) :
    IsDistinguished S t u := by
  intro hbis
  exact distinguishingWitness_implies_not_hmlEquiv (S := S) h (hAdeq hbis)

theorem logicalDistanceApprox_eq_zero_of_bisimilar_of_adequacySound
    (hAdeq : S.adequacy_sound) {n : Nat} {t u : S.Term}
    (hbis : S.Bisimilar t u) :
    HMLFormula.logicalDistanceApprox (S := S) n t u = 0 := by
  exact (HMLFormula.logicalDistanceApprox_eq_zero_iff (S := S) n t u).2
    (bisimilar_implies_hmlEquivUpTo_of_adequacySound (S := S) hAdeq hbis)

theorem logicalDistanceApprox_eq_one_implies_distinguished_of_adequacySound
    (hAdeq : S.adequacy_sound) {n : Nat} {t u : S.Term}
    (h : HMLFormula.logicalDistanceApprox (S := S) n t u = 1) :
    IsDistinguished S t u := by
  exact distinguishingWitness_implies_distinguished_of_adequacySound (S := S) hAdeq
    ((HMLFormula.logicalDistanceApprox_eq_one_iff (S := S) n t u).1 h)

theorem logicalDistanceApprox_eq_one_implies_classes_ne_of_adequacySound
    (hAdeq : S.adequacy_sound) {n : Nat} {t u : S.Term}
    (h : HMLFormula.logicalDistanceApprox (S := S) n t u = 1) :
    toBisimClass S t ≠ toBisimClass S u := by
  exact distinguished_classes_ne S
    (logicalDistanceApprox_eq_one_implies_distinguished_of_adequacySound
      (S := S) hAdeq h)

end ObservationBridge

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
