import Mettapedia.KR.ConceptGeometry.AbstractInheritanceStampedWitness
import Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceBeta
import Mettapedia.PLN.RuleFamilies.FirstOrder.PLNRevision

/-!
# Stamped Witnesses as Guarded PLN Revision Inputs

This bridge connects the generic KR stamped-witness guard to the raw finite
PLN Revision rule.  Raw Revision stays additive; stamped inputs are allowed to
feed it only when the existing pairwise stamp-disjointness certificate succeeds.
-/

namespace Mettapedia.PLN.Bridges.KR.RevisionStampedWitnessBridge

open Mettapedia.KR.ConceptGeometry.AbstractInheritance
open Mettapedia.PLN.Evidence.EvidenceQuantale
open Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceBeta
open Mettapedia.PLN.RuleFamilies.FirstOrder.PLNRevision

universe u

variable {Stamp : Type u}

/-- Count-pair evidence with an explicit finite provenance stamp. -/
noncomputable def countPairStampedEvidence
    (stamp : Finset Stamp) (nm : ℕ × ℕ) : StampedBinaryEvidence Stamp where
  evidence := countPairEvidence nm
  stamp := stamp

@[simp] theorem countPairStampedEvidence_evidence
    (stamp : Finset Stamp) (nm : ℕ × ℕ) :
    (countPairStampedEvidence (Stamp := Stamp) stamp nm).evidence =
      countPairEvidence nm := rfl

@[simp] theorem countPairStampedEvidence_stamp
    (stamp : Finset Stamp) (nm : ℕ × ℕ) :
    (countPairStampedEvidence (Stamp := Stamp) stamp nm).stamp = stamp := rfl

/-- Count-pair stamped packets obtained from `(stamp, positive/negative count)`
records. -/
noncomputable def countPairStampedBatch
    (xs : List (Finset Stamp × (ℕ × ℕ))) : List (StampedBinaryEvidence Stamp) :=
  xs.map fun x => countPairStampedEvidence x.1 x.2

/-- The raw count ledger underlying a stamped count-pair batch. -/
def countPairLedger (xs : List (Finset Stamp × (ℕ × ℕ))) : List (ℕ × ℕ) :=
  xs.map Prod.snd

@[simp] theorem countPairStampedBatch_evidence_map
    (xs : List (Finset Stamp × (ℕ × ℕ))) :
    (countPairStampedBatch (Stamp := Stamp) xs).map (fun x => x.evidence) =
      (countPairLedger xs).map countPairEvidence := by
  simp [countPairStampedBatch, countPairLedger, List.map_map, Function.comp_def]

variable [DecidableEq Stamp]

/-- Guarded raw-Revision payload for stamped evidence packets.

The guard is inherited from `StampedBinaryEvidence.guardedListRevise`: success
means the stamps are pairwise disjoint, so the payload may be passed to raw
additive `revisionMany` without double-counting provenance. -/
noncomputable def guardedRevisionManyEvidence
    (xs : List (StampedBinaryEvidence Stamp)) : Option BinaryEvidence :=
  (StampedBinaryEvidence.guardedListRevise xs).map fun r => r.evidence

/-- The guarded stamped-witness surface computes exactly raw finite PLN
Revision on the payloads iff the stamps are pairwise disjoint. -/
theorem guardedRevisionManyEvidence_eq_some_revisionMany_iff_pairwise
    (xs : List (StampedBinaryEvidence Stamp)) :
    guardedRevisionManyEvidence xs =
        some (revisionMany (xs.map fun x => x.evidence)) ↔
      xs.Pairwise StampedBinaryEvidence.StampDisjoint := by
  constructor
  · intro h
    have hSome : (StampedBinaryEvidence.guardedListRevise xs).isSome := by
      unfold guardedRevisionManyEvidence at h
      cases hRev : StampedBinaryEvidence.guardedListRevise xs with
      | none => simp [hRev] at h
      | some _ => simp
    exact (StampedBinaryEvidence.guardedListRevise_isSome_iff_pairwise xs).mp hSome
  · intro hPair
    unfold guardedRevisionManyEvidence
    rw [(StampedBinaryEvidence.guardedListRevise_eq_some_iff_pairwise xs).mpr hPair]
    simp [StampedBinaryEvidence.listRevise_evidence, revisionMany]

/-- Guarded stamped Revision rejects exactly the non-pairwise-disjoint
provenance families. -/
theorem guardedRevisionManyEvidence_eq_none_iff_not_pairwise
    (xs : List (StampedBinaryEvidence Stamp)) :
    guardedRevisionManyEvidence xs = none ↔
      ¬ xs.Pairwise StampedBinaryEvidence.StampDisjoint := by
  unfold guardedRevisionManyEvidence
  simp [StampedBinaryEvidence.guardedListRevise_eq_none_iff_not_pairwise]

/-- Concrete negative canary: two packets sharing a stamp are rejected before
their payloads can be handed to raw additive Revision. -/
theorem guardedRevisionManyEvidence_pair_rejects_shared_stamp
    {x y : StampedBinaryEvidence Stamp} {a : Stamp}
    (hx : a ∈ x.stamp) (hy : a ∈ y.stamp) :
    guardedRevisionManyEvidence [x, y] = none := by
  rw [guardedRevisionManyEvidence_eq_none_iff_not_pairwise]
  intro hPair
  have hxy : StampedBinaryEvidence.StampDisjoint x y := by
    exact (List.pairwise_cons.mp hPair).1 y (by simp)
  exact StampedBinaryEvidence.not_stampDisjoint_of_mem hx hy hxy

/-! ## Count-pair / Beta-Bernoulli readout

This section specializes the stamped guard to the count-pair packets consumed by
the existing `EvidenceBeta` bridge.  The guard remains provenance-only; the
Bayesian sufficient-statistic update is exactly the raw finite Revision update
already proven in `EvidenceBeta`.
-/

/-- Stamped count-pair packets compute the raw finite count-pair Revision
payload iff their provenance stamps are pairwise disjoint. -/
theorem guardedRevisionManyCountPairEvidence_eq_some_iff_pairwise
    (xs : List (Finset Stamp × (ℕ × ℕ))) :
    guardedRevisionManyEvidence (countPairStampedBatch (Stamp := Stamp) xs) =
        some (revisionMany ((countPairLedger xs).map countPairEvidence)) ↔
      (countPairStampedBatch (Stamp := Stamp) xs).Pairwise
        StampedBinaryEvidence.StampDisjoint := by
  simpa [countPairStampedBatch_evidence_map] using
    (guardedRevisionManyEvidence_eq_some_revisionMany_iff_pairwise
      (Stamp := Stamp)
      (countPairStampedBatch (Stamp := Stamp) xs))

/-- When the provenance stamps are pairwise disjoint, guarded count-pair
Revision has the same Beta-Bernoulli sufficient-statistic readout as raw
finite-source Revision over the count ledger. -/
theorem guardedRevisionManyCountPairEvidence_is_beta_batch_update_of_pairwise
    (prior_param : ℝ) (hprior : 0 < prior_param)
    (xs : List (Finset Stamp × (ℕ × ℕ)))
    (hPair :
      (countPairStampedBatch (Stamp := Stamp) xs).Pairwise
        StampedBinaryEvidence.StampDisjoint) :
    guardedRevisionManyEvidence (countPairStampedBatch (Stamp := Stamp) xs) =
        some (revisionMany ((countPairLedger xs).map countPairEvidence)) ∧
      (revisionMany ((countPairLedger xs).map countPairEvidence)).pos =
          ((countPairLedger xs).map (fun nm => (nm.1 : ENNReal))).sum ∧
        (revisionMany ((countPairLedger xs).map countPairEvidence)).neg =
          ((countPairLedger xs).map (fun nm => (nm.2 : ENNReal))).sum ∧
        (batchEvidenceBetaParams prior_param hprior (countPairLedger xs)).alpha =
          prior_param + ((countPairLedger xs).map Prod.fst).sum ∧
        (batchEvidenceBetaParams prior_param hprior (countPairLedger xs)).beta =
          prior_param + ((countPairLedger xs).map Prod.snd).sum := by
  constructor
  · exact (guardedRevisionManyCountPairEvidence_eq_some_iff_pairwise
      (Stamp := Stamp) xs).mpr hPair
  · exact
      revisionMany_countPairEvidence_is_beta_batch_update
        prior_param hprior (countPairLedger xs)

/-- Reader-facing handle for Revision guarded by KR stamped provenance. -/
structure RevisionStampedWitnessBridgeProfile where
  guardedComputesRawRevisionIffPairwise :
    ∀ (xs : List (StampedBinaryEvidence Stamp)),
      guardedRevisionManyEvidence xs =
          some (revisionMany (xs.map fun x => x.evidence)) ↔
        xs.Pairwise StampedBinaryEvidence.StampDisjoint
  guardedRejectsOverlaps :
    ∀ (xs : List (StampedBinaryEvidence Stamp)),
      guardedRevisionManyEvidence xs = none ↔
        ¬ xs.Pairwise StampedBinaryEvidence.StampDisjoint
  sharedStampPairRejected :
    ∀ {x y : StampedBinaryEvidence Stamp} {a : Stamp},
      a ∈ x.stamp → a ∈ y.stamp →
        guardedRevisionManyEvidence [x, y] = none
  countPairGuardedComputesRawRevisionIffPairwise :
    ∀ (xs : List (Finset Stamp × (ℕ × ℕ))),
      guardedRevisionManyEvidence (countPairStampedBatch (Stamp := Stamp) xs) =
          some (revisionMany ((countPairLedger xs).map countPairEvidence)) ↔
        (countPairStampedBatch (Stamp := Stamp) xs).Pairwise
          StampedBinaryEvidence.StampDisjoint
  countPairGuardedBetaBatchUpdate :
    ∀ (prior_param : ℝ) (hprior : 0 < prior_param)
      (xs : List (Finset Stamp × (ℕ × ℕ))),
      (countPairStampedBatch (Stamp := Stamp) xs).Pairwise
          StampedBinaryEvidence.StampDisjoint →
        guardedRevisionManyEvidence (countPairStampedBatch (Stamp := Stamp) xs) =
            some (revisionMany ((countPairLedger xs).map countPairEvidence)) ∧
          (revisionMany ((countPairLedger xs).map countPairEvidence)).pos =
              ((countPairLedger xs).map (fun nm => (nm.1 : ENNReal))).sum ∧
            (revisionMany ((countPairLedger xs).map countPairEvidence)).neg =
              ((countPairLedger xs).map (fun nm => (nm.2 : ENNReal))).sum ∧
            (batchEvidenceBetaParams prior_param hprior (countPairLedger xs)).alpha =
              prior_param + ((countPairLedger xs).map Prod.fst).sum ∧
            (batchEvidenceBetaParams prior_param hprior (countPairLedger xs)).beta =
              prior_param + ((countPairLedger xs).map Prod.snd).sum

/-- Compact profile for the stamped-provenance guard in front of raw
finite-source Revision. -/
noncomputable def revisionStampedWitnessBridgeProfile :
    RevisionStampedWitnessBridgeProfile (Stamp := Stamp) where
  guardedComputesRawRevisionIffPairwise :=
    guardedRevisionManyEvidence_eq_some_revisionMany_iff_pairwise
  guardedRejectsOverlaps :=
    guardedRevisionManyEvidence_eq_none_iff_not_pairwise
  sharedStampPairRejected := by
    intro x y a hx hy
    exact guardedRevisionManyEvidence_pair_rejects_shared_stamp hx hy
  countPairGuardedComputesRawRevisionIffPairwise :=
    guardedRevisionManyCountPairEvidence_eq_some_iff_pairwise
  countPairGuardedBetaBatchUpdate :=
    guardedRevisionManyCountPairEvidence_is_beta_batch_update_of_pairwise

end Mettapedia.PLN.Bridges.KR.RevisionStampedWitnessBridge
