import Mettapedia.OSLF.Framework.GSLTEvidence
import Mettapedia.PLN.WorldModel.PLNWorldModel

/-!
# Binary world models of sampled computational entities

Any type T of "computational entities" (processes, terms, states) gives
rise to a BinaryWorldModel over multiset ensembles of T.  The construction:

- **State** = `Multiset T` (an ensemble of samples or candidate entities)
- **Query** = decidable property of T
- **BinaryEvidence** = count of satisfying / refuting entities

Additivity is automatic: `Multiset.countP` distributes over addition.

This is the Stage 2 abstraction from the Rho calculus instance
(`RhoWorldModel.lean`).  The Rho calculus is T = Pattern; but the
construction works for ANY T.

## The Universal Theorem

For any type T, the multiset-counting evidence assignment is a
`BinaryWorldModel (Multiset T) (DecProp T)`.  This means:

**Every carrier has a multiset-counting BinaryWorldModel.**

No parallel operator, dynamics, sampling distribution, or independence
assumption is required for this construction. Ensemble addition pools samples;
it must not be identified with operational parallel composition. Interaction
can create observations absent from both components in isolation. The
`RhoContextualWorldModel` module connects actual parallel interactions to these
counts using queries about an agent in a sampled environment.

## Connection to Meredith

Meredith's weight maps motivate value-valued readings of computation.
The theorem here is specifically about counts of predicate-satisfying samples;
no Born-rule, path-integral, or Bayesian adequacy theorem follows from
additivity alone.

## References

- `RhoWorldModel.lean` — the Rho calculus instance (T = Pattern)
- `PLNWorldModelKripke.lean` — the Kripke instance (T = PointedKripke)
- `GSLTEvidence.lean` — the value-monoid-parameterized bridge
- L. Gregory Meredith, "Computation, Causality, and Consciousness" (2026)
-/

namespace Mettapedia.OSLF.Framework.GSLTWorldModel

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.PLN.Evidence.EvidenceQuantale
open Mettapedia.PLN.Evidence.EvidenceClass
open Mettapedia.PLN.WorldModel.PLNWorldModel
open Mettapedia.OSLF.Framework.GSLTEvidence

/-! ## Generic Ensemble and Query -/

/-- A decidable property of entities of type T.
    This is the generic query type for multiset-counting WorldModels. -/
structure DecProp (T : Type*) where
  /-- The property being queried -/
  property : T → Prop
  /-- Decidability witness -/
  dec : DecidablePred property

/-! ## Generic BinaryEvidence Extraction -/

/-- Count entities satisfying/refuting a query in a multiset ensemble.
    Works for ANY type T — not just Pattern. -/
noncomputable def ensembleEvidence {T : Type*}
    (W : Multiset T) (q : DecProp T) : BinaryEvidence := by
  classical
  exact ⟨↑(Multiset.countP q.property W),
         ↑(Multiset.countP (fun x => ¬ q.property x) W)⟩

/-! ## Core Theorem: Additivity for Any T -/

/-- BinaryEvidence extraction is additive over multiset union, for ANY type T.

    This is the universal version of `rhoEvidence_add`.  The proof is
    identical because `Multiset.countP_add` works for any type. -/
theorem ensembleEvidence_add {T : Type*}
    (W₁ W₂ : Multiset T) (q : DecProp T) :
    ensembleEvidence (W₁ + W₂) q =
    ensembleEvidence W₁ q + ensembleEvidence W₂ q := by
  classical
  apply BinaryEvidence.ext'
  · simp [ensembleEvidence, Multiset.countP_add, BinaryEvidence.hplus_def]
  · simp [ensembleEvidence, Multiset.countP_add, BinaryEvidence.hplus_def]

/-- The empty ensemble has zero evidence for every query. -/
theorem ensembleEvidence_zero {T : Type*} (q : DecProp T) :
    ensembleEvidence (0 : Multiset T) q = 0 := by
  classical
  simp only [ensembleEvidence, Multiset.countP_zero, Nat.cast_zero]
  rfl

/-! ## Universal BinaryWorldModel Instance -/

/-- Multiset T is an EvidenceType (AddCommMonoid via multiset union). -/
instance {T : Type*} : EvidenceType (Multiset T) where

/-- **The Universal BinaryWorldModel for Multiset Ensembles.**

    For ANY type T, multiset ensembles of T form a BinaryWorldModel when
    queried by decidable properties.  BinaryEvidence extraction counts
    satisfying/refuting entities, and is additive over sample pooling
    (multiset union).

    This is the Stage 2 universal theorem:
    every carrier admits a multiset-counting BinaryWorldModel.

    Instances:
    - T = Pattern (Rho calculus) → `RhoWorldModel.lean`
    - T = PointedKripke (modal logic) → `PLNWorldModelKripke.lean`
    - T = PointedFOL L (first-order logic) → `PLNWorldModelFOL.lean`
    - T = any type → this file -/
noncomputable instance universalEnsembleWorldModel (T : Type*) :
    BinaryWorldModel (Multiset T) (DecProp T) where
  evidence := ensembleEvidence
  evidence_add := ensembleEvidence_add
  evidence_zero := ensembleEvidence_zero

/-! ## Universal GSLTEvidenceAssignment -/

/-- The ensemble evidence assignment into binary counts. General value-monoid
assignments require their own atomic contributions and interpretation laws. -/
noncomputable def universalGSLTEvidence (T : Type*) :
    GSLTEvidenceAssignment (Multiset T) (DecProp T) BinaryEvidence where
  extract := ensembleEvidence
  extract_add := ensembleEvidence_add
  extract_zero := ensembleEvidence_zero

/-! ## Singleton Lemmas -/

/-- A singleton ensemble with a satisfying entity has evidence ⟨1, 0⟩. -/
theorem ensembleEvidence_singleton_of_satisfies {T : Type*}
    (x : T) (q : DecProp T) (h : q.property x) :
    ensembleEvidence ({x} : Multiset T) q = ⟨1, 0⟩ := by
  classical
  apply BinaryEvidence.ext' <;> simp [ensembleEvidence, ← Multiset.cons_zero, h]

/-- A singleton ensemble with a refuting entity has evidence ⟨0, 1⟩. -/
theorem ensembleEvidence_singleton_of_refutes {T : Type*}
    (x : T) (q : DecProp T) (h : ¬ q.property x) :
    ensembleEvidence ({x} : Multiset T) q = ⟨0, 1⟩ := by
  classical
  apply BinaryEvidence.ext' <;> simp [ensembleEvidence, ← Multiset.cons_zero, h]

/-! ## Witnesses and transport -/

/-- Positive count means that a sampled entity satisfies the query. -/
theorem ensembleEvidence_pos_iff {T : Type*} (W : Multiset T) (q : DecProp T) :
    0 < (ensembleEvidence W q).pos ↔ ∃ x ∈ W, q.property x := by
  classical
  simp only [ensembleEvidence, Nat.cast_pos]
  exact Multiset.countP_pos

/-- Transforming every sample and pulling the query back give the same
evidence whenever the query predicates agree along the transformation. -/
theorem ensembleEvidence_map {T U : Type*} (W : Multiset T) (transform : T → U)
    (q : DecProp U) (pulled : DecProp T)
    (commutes : ∀ x, q.property (transform x) ↔ pulled.property x) :
    ensembleEvidence (W.map transform) q = ensembleEvidence W pulled := by
  classical
  have positives : (fun x => q.property (transform x)) = pulled.property :=
    funext (fun x => propext (commutes x))
  have negatives : (fun x => ¬ q.property (transform x)) = (fun x => ¬ pulled.property x) :=
    funext (fun x => propext (not_congr (commutes x)))
  apply BinaryEvidence.ext' <;>
    simp only [ensembleEvidence, Multiset.countP_map,
      ← Multiset.countP_eq_card_filter, positives, negatives]

/-! ## Total BinaryEvidence = Ensemble Size

The total evidence (pos + neg) for any query equals the ensemble size.
Every entity either satisfies or refutes the query. -/

theorem ensembleEvidence_total {T : Type*}
    (W : Multiset T) (q : DecProp T) :
    (ensembleEvidence W q).pos + (ensembleEvidence W q).neg =
    ↑(Multiset.card W) := by
  classical
  simp only [ensembleEvidence]
  exact_mod_cast (Multiset.card_eq_countP_add_countP q.property W).symm

end Mettapedia.OSLF.Framework.GSLTWorldModel
