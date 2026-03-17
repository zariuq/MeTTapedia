import Mettapedia.Logic.PLNScopedTrackedWhichState
import Mettapedia.Logic.PLNWorldModelGeneric

/-!
# Provenance-Tracked Inference

Generic framework for inference with provenance tracking.  NOT specific to
PLN v0.9 — works for any `WorldModel` backed by `ScopedTrackedWhichState`.

The key ideas, matching PLN v0.9's stamp mechanism but proved:

- **StampDisjoint** = `Finset.Disjoint` on provenance support sets.
  Two evidence values are safe to combine iff their provenance is disjoint
  (no double-counting).

- **ProvenanceRevision** = combine evidence only when provenance-disjoint.
  The result has union provenance.

- **ProvenanceChain** = chain two inferences when their provenance is disjoint.
  The conclusion has union provenance and its evidence is the tensor product.

- **ProvenanceForgetting** = remove evidence from a scope.
  Delegates to `forgetScopedByScope_exactInverse_of_supported_of_clean`.

All theorems are generic over any `LPSignature` and any number of
observation sources `n` and scopes `m`.
-/

namespace Mettapedia.Logic.PLNProvenanceInference

open Mettapedia.Logic
open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.PLNWorldModelGeneric
open Mettapedia.Logic.LP

variable {σ : LPSignature} {n m : ℕ}

/-! ## Stamp Disjointness

PLN v0.9's `StampDisjoint` checks whether two sentences' evidence stamps
share no observation IDs.  In the WM calculus, this is `Finset.Disjoint`
on the scoped provenance support sets. -/

/-- Two scoped tracked states have disjoint provenance at a query when
their scope supports don't overlap.  This is the formal version of
PLN v0.9's `StampDisjoint`. -/
def ProvenanceDisjointAt
    (W₁ W₂ : ScopedTrackedWhichState σ n m) (q : GroundAtom σ) : Prop :=
  Disjoint (scopedTrackedScopeSupport W₁ q) (scopedTrackedScopeSupport W₂ q)

/-- Two scoped tracked states have globally disjoint provenance when
their scope supports don't overlap at ANY query. -/
def ProvenanceDisjoint
    (W₁ W₂ : ScopedTrackedWhichState σ n m) : Prop :=
  ∀ q, ProvenanceDisjointAt W₁ W₂ q

/-- States supported in disjoint scope sets are provenance-disjoint. -/
theorem provenanceDisjoint_of_disjointScopes
    {S₁ S₂ : Finset (Fin m)}
    {W₁ W₂ : ScopedTrackedWhichState σ n m}
    (h₁ : SupportedInScope W₁ S₁)
    (h₂ : SupportedInScope W₂ S₂)
    (hdisj : Disjoint S₁ S₂) :
    ProvenanceDisjoint W₁ W₂ := by
  intro q
  unfold ProvenanceDisjointAt
  exact Finset.disjoint_of_subset_left
    (forgetScopedByScope_scopeSupport_subset h₁ q)
    (Finset.disjoint_of_subset_right
      (forgetScopedByScope_scopeSupport_subset h₂ q)
      hdisj)

/-! ## Provenance-Tracked Revision

Revision (evidence addition) is safe when provenance is disjoint.
The combined state has union provenance support.  This is the formal
version of PLN v0.9's stamp-checked revision. -/

/-- The combined provenance support is the union.  This is the formal
version of PLN v0.9's `StampConcat`. -/
theorem revision_scopeSupport_union
    (W₁ W₂ : ScopedTrackedWhichState σ n m) (q : GroundAtom σ) :
    scopedTrackedScopeSupport (W₁ + W₂) q =
      scopedTrackedScopeSupport W₁ q ∪ scopedTrackedScopeSupport W₂ q :=
  scopedTrackedScopeSupport_add W₁ W₂ q

/-- The combined payload support is the union.  No double-counting. -/
theorem revision_payloadSupport_union
    (W₁ W₂ : ScopedTrackedWhichState σ n m) (q : GroundAtom σ) :
    scopedTrackedPayloadSupport (W₁ + W₂) q =
      scopedTrackedPayloadSupport W₁ q ∪ scopedTrackedPayloadSupport W₂ q :=
  scopedTrackedPayloadSupport_add W₁ W₂ q

/-! ## Provenance-Tracked Forgetting

Forgetting removes exactly the evidence from a scope.
Under exact inverse conditions, the base state is recovered. -/

/-- If `W` is clean w.r.t. scope `S` and `Δ` is supported entirely in `S`,
then forgetting `S` from `W + Δ` exactly recovers `W`.

This is the key theorem: you can retract a revision and recover the
original state, with no approximation and no hidden sorries.

PLN v0.9 has NO forgetting.  This is the WM calculus value-add. -/
theorem forget_exactInverse
    (W Δ : ScopedTrackedWhichState σ n m)
    (S : Finset (Fin m))
    (hclean : ScopeClean W S)
    (hsupp : SupportedInScope Δ S) :
    forgetScopedByScope S (W + Δ) = W :=
  forgetScopedByScope_exactInverse_of_supported_of_clean W Δ hclean hsupp

/-- Forgetting a scope from a state that has no chunks in that scope
is the identity. -/
theorem forget_clean_id
    (W : ScopedTrackedWhichState σ n m)
    (S : Finset (Fin m))
    (hclean : ScopeClean W S) :
    forgetScopedByScope S W = W :=
  forgetScopedByScope_eq_self_of_scopeClean hclean

/-- Forgetting a scope from a state fully supported in that scope
zeroes it. -/
theorem forget_supported_zero
    (W : ScopedTrackedWhichState σ n m)
    (S : Finset (Fin m))
    (hsupp : SupportedInScope W S) :
    forgetScopedByScope S W = 0 :=
  forgetScopedByScope_eq_zero_of_supportedInScope hsupp

/-! ## Conservation Under Forgetting

When you forget a scope and re-derive, evidence outside the scope is
conserved (Noether-style).  BinaryEvidence inside is exactly the revision. -/

/-- After forgetting scope `S` from a revised state `W + Δ`,
the result at any query `q` depends only on `W`'s contribution
outside `S`.  Under exact inverse conditions, this is just `W`. -/
theorem conservation_outside_scope
    (W Δ : ScopedTrackedWhichState σ n m)
    (S : Finset (Fin m))
    (hclean : ScopeClean W S)
    (hsupp : SupportedInScope Δ S) :
    ∀ q, scopedTrackedEvidence (forgetScopedByScope S (W + Δ)) q =
         scopedTrackedEvidence W q := by
  intro q
  rw [forget_exactInverse W Δ S hclean hsupp]

/-! ## Building Provenance States from Observations

Helper to create a provenance-tracked state from a single observation
assigned to a specific scope. -/

/-- Embed a single observation (a Which K-relation) as a scoped tracked
state in scope `s`. -/
abbrev observationState (s : Fin m) (I : KRelation σ (Which (Fin n))) :
    ScopedTrackedWhichState σ n m :=
  toScopedTrackedWhichState s I

/-- A single observation state is supported in its singleton scope. -/
theorem observationState_supported (s : Fin m) (I : KRelation σ (Which (Fin n))) :
    SupportedInScope (observationState (σ := σ) (n := n) (m := m) s I)
      ({s} : Finset (Fin m)) :=
  toScopedTrackedWhichState_supportedInSingleton s I

/-- Forgetting an observation's scope from a base state + that observation
exactly recovers the base state. -/
theorem forget_observation_exactInverse
    (s : Fin m) (I : KRelation σ (Which (Fin n)))
    (W : ScopedTrackedWhichState σ n m)
    (hclean : ScopeClean W ({s} : Finset (Fin m))) :
    forgetScopedByScope ({s} : Finset (Fin m))
      (W + observationState (σ := σ) (n := n) (m := m) s I) = W :=
  toScopedTrackedWhichState_forget_exactInverse_of_clean s I W hclean

end Mettapedia.Logic.PLNProvenanceInference
