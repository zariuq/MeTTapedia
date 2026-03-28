import Mettapedia.Logic.UniversalPredictionApproximationWMBridge
import Mettapedia.Logic.WorldModelProfiles

/-!
# Universal-Mixture Conditional Queries as WM Queries

This file upgrades the raw prefix-event approximation bridge to a simple
**conditional query** API.

The key move is to package the conditional event `y` under context `x` as
binary evidence

`⟨ μ(x ++ y), μ(x) - μ(x ++ y) ⟩`.

Its WM strength is exactly `μ(y | x) = μ(x ++ y) / μ(x)`, so semimeasure
conditionals become first-class `BinaryWorldModel` queries.

Positive example:
- a continuation query `"next bits are y given current prefix x"`.

Negative example:
- this file does **not** claim conditional approximants are monotone in the
  approximation budget; only the exact WM interpretation is provided here.
-/

namespace Mettapedia.Logic.UniversalPrediction

open scoped Classical
open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.PLNWorldModelProfiles

/-- A conditional prefix query `target | context`. -/
structure ConditionalPrefixQuery where
  context : BinString
  target : BinString
  deriving DecidableEq

/-- Binary evidence carried by a semimeasure conditional query. -/
noncomputable def conditionalEvidence
    (μ : Semimeasure) (q : ConditionalPrefixQuery) : BinaryEvidence :=
  { pos := μ (q.context ++ q.target)
    neg := μ q.context - μ (q.context ++ q.target) }

theorem conditionalEvidence_total
    (μ : Semimeasure) (q : ConditionalPrefixQuery) :
    (conditionalEvidence μ q).total = μ q.context := by
  unfold conditionalEvidence BinaryEvidence.total
  have hle : μ (q.context ++ q.target) ≤ μ q.context := μ.mono_append q.context q.target
  exact add_tsub_cancel_of_le hle

/-- The extensional world-model profile induced by a semimeasure's conditional
queries. -/
abbrev ConditionalProfile := JointEvidenceProfile ConditionalPrefixQuery

/-- A semimeasure as a world-model evidence profile over conditional queries. -/
noncomputable def conditionalProfile (μ : Semimeasure) : ConditionalProfile :=
  fun q => conditionalEvidence μ q

/-- The WM strength of a conditional query is exactly the semimeasure
conditional. -/
theorem conditionalProfile_queryStrength_eq_conditionalENN
    (μ : Semimeasure) (q : ConditionalPrefixQuery) :
    BinaryWorldModel.queryStrength (conditionalProfile μ) q =
      conditionalENN μ q.target q.context := by
  change BinaryEvidence.toStrength (conditionalEvidence μ q) =
    conditionalENN μ q.target q.context
  by_cases hx : μ q.context = 0
  · rw [BinaryEvidence.toStrength, conditionalEvidence_total, hx, if_pos rfl]
    exact (conditionalENN_eq_zero_of_eq_zero μ q.context q.target hx).symm
  · rw [BinaryEvidence.toStrength, conditionalEvidence_total, if_neg hx]
    rfl

/-- Conditional-query profile for a finite-prefix universal-mixture
approximant. -/
noncomputable def approxConditionalProfile
    (ν : ℕ → Semimeasure) (w : ℕ → ENNReal)
    (hw : (∑' i, w i) ≤ 1) (n : ℕ) : ConditionalProfile :=
  conditionalProfile (xiApproxSemimeasure ν w hw n)

/-- Conditional-query profile for the full universal mixture. -/
noncomputable def fullConditionalProfile
    (ν : ℕ → Semimeasure) (w : ℕ → ENNReal)
    (hw : (∑' i, w i) ≤ 1) : ConditionalProfile :=
  conditionalProfile (xiSemimeasure ν w hw)

theorem approxConditionalQueryStrength_eq_conditionalENN
    (ν : ℕ → Semimeasure) (w : ℕ → ENNReal)
    (hw : (∑' i, w i) ≤ 1) (n : ℕ) (q : ConditionalPrefixQuery) :
    BinaryWorldModel.queryStrength (approxConditionalProfile ν w hw n) q =
      conditionalENN (xiApproxSemimeasure ν w hw n) q.target q.context := by
  simpa [approxConditionalProfile] using
    conditionalProfile_queryStrength_eq_conditionalENN (xiApproxSemimeasure ν w hw n) q

theorem fullConditionalQueryStrength_eq_conditionalENN
    (ν : ℕ → Semimeasure) (w : ℕ → ENNReal)
    (hw : (∑' i, w i) ≤ 1) (q : ConditionalPrefixQuery) :
    BinaryWorldModel.queryStrength (fullConditionalProfile ν w hw) q =
      conditionalENN (xiSemimeasure ν w hw) q.target q.context := by
  simpa [fullConditionalProfile] using
    conditionalProfile_queryStrength_eq_conditionalENN (xiSemimeasure ν w hw) q

/-- Conditional-query profile for the canonical geometric mixture. -/
noncomputable def geomConditionalProfile
    (ν : ℕ → Semimeasure) : ConditionalProfile :=
  fullConditionalProfile ν geometricWeight tsum_geometricWeight_le_one

/-- Conditional-query profile for a geometric finite-prefix approximant. -/
noncomputable def geomApproxConditionalProfile
    (ν : ℕ → Semimeasure) (n : ℕ) : ConditionalProfile :=
  approxConditionalProfile ν geometricWeight tsum_geometricWeight_le_one n

theorem geomConditionalQueryStrength_eq_conditionalENN
    (ν : ℕ → Semimeasure) (q : ConditionalPrefixQuery) :
    BinaryWorldModel.queryStrength (geomConditionalProfile ν) q =
      conditionalENN (xiGeomSemimeasure ν) q.target q.context := by
  simpa [geomConditionalProfile, xiGeomSemimeasure] using
    fullConditionalQueryStrength_eq_conditionalENN ν geometricWeight tsum_geometricWeight_le_one q

theorem geomApproxConditionalQueryStrength_eq_conditionalENN
    (ν : ℕ → Semimeasure) (n : ℕ) (q : ConditionalPrefixQuery) :
    BinaryWorldModel.queryStrength (geomApproxConditionalProfile ν n) q =
      conditionalENN (xiGeomApproxSemimeasure ν n) q.target q.context := by
  simpa [geomApproxConditionalProfile, xiGeomApproxSemimeasure] using
    approxConditionalQueryStrength_eq_conditionalENN ν geometricWeight tsum_geometricWeight_le_one n q

end Mettapedia.Logic.UniversalPrediction
