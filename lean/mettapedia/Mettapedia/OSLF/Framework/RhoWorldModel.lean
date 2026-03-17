import Mettapedia.OSLF.Framework.GSLTEvidence
import Mettapedia.Logic.PLNWorldModel

/-!
# Rho Calculus BinaryWorldModel Instance

The Rho calculus — L. Gregory Meredith's running example GSLT in
"Computation, Causality, and Consciousness" (2026) — instantiates
the WM evidence framework.

## Construction

- **State**: `Multiset Pattern` (a process ensemble; parallel composition
  = multiset union, which is an `AddCommMonoid`)
- **Query**: `RhoQuery` (a decidable property of patterns)
- **BinaryEvidence**: count of satisfying/refuting processes in the ensemble

The core theorem is `rhoEvidence_add`: evidence extraction is additive
over ensemble union.  This is the WM axiom `evidence(W₁ + W₂, q) =
evidence(W₁, q) + evidence(W₂, q)` instantiated for the Rho calculus.

## What This Means

Every GSLT with parallel composition (every process calculus) has a
natural BinaryWorldModel over it.  The WM evidence framework is the canonical
Bayesian counting layer for any GSLT — not just the WM posterior-state
calculus.  This is the first step toward the universal theorem:

  WM evidence extraction is the canonical sufficient-statistic functor
  from GSLTs to evidence profiles.

## References

- L. Gregory Meredith, "Computation, Causality, and Consciousness" (2026),
  §1.2 (Rho calculus as running example)
- PLNWorldModelKripke.lean (Kripke instance, same pattern)
-/

namespace Mettapedia.OSLF.Framework.RhoWorldModel

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.OSLF.Framework.GSLTEvidence
open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.EvidenceClass

/-! ## Process Ensemble -/

/-- A Rho process ensemble: a multiset of process patterns.
    Parallel composition corresponds to multiset union.
    `Multiset` is already an `AddCommMonoid` via Mathlib
    (add = union, zero = empty). -/
abbrev RhoEnsemble := Multiset Pattern

/-! ## Query Type -/

/-- A query about Rho processes: a decidable property of patterns.
    Decidability is needed for `Multiset.countP` to count
    satisfying/refuting processes. -/
structure RhoQuery where
  /-- The property being queried -/
  property : Pattern → Prop
  /-- Decidability witness -/
  dec : DecidablePred property

/-! ## BinaryEvidence Extraction -/

/-- Count processes satisfying/refuting a query in an ensemble.
    Positive evidence = number of processes satisfying the property.
    Negative evidence = number of processes refuting it. -/
noncomputable def rhoEvidence (W : RhoEnsemble) (q : RhoQuery) : BinaryEvidence := by
  classical
  exact ⟨↑(Multiset.countP q.property W),
         ↑(Multiset.countP (fun p => ¬ q.property p) W)⟩

/-! ## Core Theorem: Additivity -/

/-- BinaryEvidence extraction is additive over ensemble composition.
    Counting over a union = sum of counts over parts.

    This is the WM axiom `evidence(W₁ + W₂, q) = evidence(W₁, q) + evidence(W₂, q)`
    instantiated for the Rho calculus.  It holds because `Multiset.countP`
    distributes over multiset addition. -/
theorem rhoEvidence_add (W₁ W₂ : RhoEnsemble) (q : RhoQuery) :
    rhoEvidence (W₁ + W₂) q = rhoEvidence W₁ q + rhoEvidence W₂ q := by
  classical
  apply BinaryEvidence.ext'
  · simp [rhoEvidence, Multiset.countP_add, BinaryEvidence.hplus_def]
  · simp [rhoEvidence, Multiset.countP_add, BinaryEvidence.hplus_def]

/-- The empty ensemble has zero evidence for every query. -/
theorem rhoEvidence_zero (q : RhoQuery) :
    rhoEvidence 0 q = 0 := by
  classical
  simp only [rhoEvidence, Multiset.countP_zero, Nat.cast_zero]
  rfl

/-- RhoEnsemble (Multiset Pattern) is an EvidenceType via its AddCommMonoid. -/
instance : EvidenceType RhoEnsemble where

/-! ## BinaryWorldModel Instance -/

/-- **The Rho calculus BinaryWorldModel.**

    Process ensembles (multisets of patterns) queried by decidable
    properties.  BinaryEvidence extraction counts satisfying/refuting
    processes, and is additive over parallel composition (ensemble union).

    This instantiates the WM evidence framework for L. Gregory Meredith's
    running example GSLT.  The same construction works for any process
    calculus with parallel composition — the Rho calculus is the first
    concrete instance on the path to the universal theorem.

    Reference: L. Gregory Meredith, "Computation, Causality, and
    Consciousness" (2026), §1.2. -/
noncomputable instance rhoWorldModel :
    BinaryWorldModel RhoEnsemble RhoQuery where
  evidence := rhoEvidence
  evidence_add := rhoEvidence_add
  evidence_zero := rhoEvidence_zero

/-! ## GSLTEvidenceAssignment Instance -/

/-- The Rho calculus as a GSLTEvidenceAssignment over BinaryEvidence.

    This is the V = BinaryEvidence specialization of the general framework.
    Replacing V with ℂ would give L. Gregory Meredith's weight map
    (quantum amplitudes).  The additive structure is the same in both
    cases — the difference is only in the value monoid. -/
noncomputable def rhoGSLTEvidence :
    GSLTEvidenceAssignment RhoEnsemble RhoQuery BinaryEvidence where
  extract := rhoEvidence
  extract_add := rhoEvidence_add
  extract_zero := rhoEvidence_zero

/-! ## Singleton Lemma -/

/-- A singleton ensemble with a satisfying process has evidence ⟨1, 0⟩. -/
theorem rhoEvidence_singleton_of_satisfies
    (p : Pattern) (q : RhoQuery) (h : q.property p) :
    rhoEvidence ({p} : RhoEnsemble) q = ⟨1, 0⟩ := by
  classical
  apply BinaryEvidence.ext' <;> simp [rhoEvidence, ← Multiset.cons_zero, h]

/-- A singleton ensemble with a refuting process has evidence ⟨0, 1⟩. -/
theorem rhoEvidence_singleton_of_refutes
    (p : Pattern) (q : RhoQuery) (h : ¬ q.property p) :
    rhoEvidence ({p} : RhoEnsemble) q = ⟨0, 1⟩ := by
  classical
  apply BinaryEvidence.ext' <;> simp [rhoEvidence, ← Multiset.cons_zero, h]

end Mettapedia.OSLF.Framework.RhoWorldModel
