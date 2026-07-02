import Mettapedia.PLN.RuleFamilies.FirstOrder.PLNRevision

/-!
# Revision Rule-Family Profile

This file exposes a compact proof-carrying handle for the current Revision
rule-family surface.  It does not add new revision semantics: finite PLN
Revision continues to be the `BinaryEvidence` additive evidence-count rule.

The profile also carries the duplicate-source negative canary, so callers do
not confuse raw additive revision with provenance-aware duplicate suppression.
-/

namespace Mettapedia.PLN.RuleFamilies.FirstOrder.PLNRevision

open scoped ENNReal
open Mettapedia.PLN.Evidence.EvidenceQuantale
open BinaryEvidence

/-- Reader-facing theorem profile for the finite binary-evidence Revision rule.

The positive fields expose the hplus/evidence-addition algebra and its strength
readout.  The negative field records that unguarded finite-source revision
double-counts duplicate packets; provenance guards live at the caller layer. -/
structure RevisionRuleFamilyProfile where
  binaryComm :
    ∀ e₁ e₂ : BinaryEvidence, revision e₁ e₂ = revision e₂ e₁
  binaryAssoc :
    ∀ e₁ e₂ e₃ : BinaryEvidence,
      revision (revision e₁ e₂) e₃ = revision e₁ (revision e₂ e₃)
  rightZero :
    ∀ e : BinaryEvidence, revision e 0 = e
  leftZero :
    ∀ e : BinaryEvidence, revision 0 e = e
  finitePair :
    ∀ e₁ e₂ : BinaryEvidence, revisionMany [e₁, e₂] = revision e₁ e₂
  finiteAppend :
    ∀ xs ys : List BinaryEvidence,
      revisionMany (xs ++ ys) = revision (revisionMany xs) (revisionMany ys)
  finiteOrderInvariant :
    ∀ {xs ys : List BinaryEvidence}, xs.Perm ys → revisionMany xs = revisionMany ys
  finiteTotal :
    ∀ xs : List BinaryEvidence,
      (revisionMany xs).total = (xs.map (fun e => e.total)).sum
  duplicatePositiveUnitDoubleCounts :
    revisionMany [positiveUnitEvidence, positiveUnitEvidence] ≠
      positiveUnitEvidence
  strengthWeightedAverage :
    ∀ e₁ e₂ : BinaryEvidence,
      e₁.total ≠ 0 →
        e₂.total ≠ 0 →
          (e₁ + e₂).total ≠ 0 →
            e₁.total ≠ ⊤ →
              e₂.total ≠ ⊤ →
                toStrength (revision e₁ e₂) =
                  (e₁.total / (e₁ + e₂).total) * toStrength e₁ +
                    (e₂.total / (e₁ + e₂).total) * toStrength e₂
  totalAdd :
    ∀ e₁ e₂ : BinaryEvidence,
      (revision e₁ e₂).total = e₁.total + e₂.total
  finiteTotalNeTop :
    ∀ e₁ e₂ : BinaryEvidence,
      e₁.total ≠ ⊤ →
        e₂.total ≠ ⊤ →
          (revision e₁ e₂).total ≠ ⊤
  tensorDistributesLeft :
    ∀ e₁ e₂ e₃ : BinaryEvidence,
      (revision e₁ e₂) * e₃ = revision (e₁ * e₃) (e₂ * e₃)
  tensorDistributesRight :
    ∀ e₁ e₂ e₃ : BinaryEvidence,
      e₁ * (revision e₂ e₃) = revision (e₁ * e₂) (e₁ * e₃)

/-- Compact public handle for the finite binary-evidence Revision surface. -/
noncomputable def revisionRuleFamilyProfile : RevisionRuleFamilyProfile where
  binaryComm := revision_comm
  binaryAssoc := revision_assoc
  rightZero := revision_zero
  leftZero := zero_revision
  finitePair := revisionMany_pair
  finiteAppend := revisionMany_append
  finiteOrderInvariant := revisionMany_perm
  finiteTotal := revisionMany_total
  duplicatePositiveUnitDoubleCounts :=
    revisionMany_duplicate_positiveUnitEvidence_ne_singleton
  strengthWeightedAverage := revision_strength_weighted_avg
  totalAdd := revision_total
  finiteTotalNeTop := revision_total_ne_top
  tensorDistributesLeft := tensor_distrib_revision
  tensorDistributesRight := tensor_distrib_revision_right

end Mettapedia.PLN.RuleFamilies.FirstOrder.PLNRevision
