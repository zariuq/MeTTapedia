import Mettapedia.PLN.WorldModel.PLNWorldModelGeneric

/-!
# Generic WM Overlap Layer

Non-additive perimeter layer over the existing `WorldModel` interface:

- keep additive extraction as the canonical core;
- add overlap-aware merge semantics as extra structure;
- recover additive evidence when an explicit independence predicate holds.
-/

namespace Mettapedia.PLN.WorldModel.WorldModelOverlap

open Mettapedia.PLN.Evidence.EvidenceClass
open Mettapedia.PLN.WorldModel.PLNWorldModelGeneric

variable {State Query Ev Ov : Type*}
variable [EvidenceType State] [AddCommMonoid Ev] [AdditiveWorldModel State Query Ev]

/-- Overlap/correlation layer over a generic world model. -/
structure OverlapLayer (State Query Ev Ov : Type*)
    [EvidenceType State] [AddCommMonoid Ev] [AdditiveWorldModel State Query Ev] where
  merge : State → State → State
  overlap : State → State → Query → Ov
  combine : Ev → Ev → Ov → Ev
  independent : State → State → Query → Prop
  evidence_merge :
    ∀ W₁ W₂ q,
      AdditiveWorldModel.extract
        (State := State) (Query := Query) (Ev := Ev) (merge W₁ W₂) q =
      combine
        (AdditiveWorldModel.extract (State := State) (Query := Query) (Ev := Ev) W₁ q)
        (AdditiveWorldModel.extract (State := State) (Query := Query) (Ev := Ev) W₂ q)
        (overlap W₁ W₂ q)
  additive_of_independent :
    ∀ W₁ W₂ q, independent W₁ W₂ q →
      AdditiveWorldModel.extract
        (State := State) (Query := Query) (Ev := Ev) (merge W₁ W₂) q =
      AdditiveWorldModel.extract (State := State) (Query := Query) (Ev := Ev) W₁ q +
      AdditiveWorldModel.extract (State := State) (Query := Query) (Ev := Ev) W₂ q

namespace OverlapLayer

variable {State Query Ev Ov : Type*}
variable [EvidenceType State] [AddCommMonoid Ev] [AdditiveWorldModel State Query Ev]

theorem evidence_merge'
    (L : OverlapLayer State Query Ev Ov)
    (W₁ W₂ : State) (q : Query) :
    AdditiveWorldModel.extract
      (State := State) (Query := Query) (Ev := Ev) (L.merge W₁ W₂) q =
    L.combine
      (AdditiveWorldModel.extract (State := State) (Query := Query) (Ev := Ev) W₁ q)
      (AdditiveWorldModel.extract (State := State) (Query := Query) (Ev := Ev) W₂ q)
      (L.overlap W₁ W₂ q) :=
  L.evidence_merge W₁ W₂ q

theorem additive_of_independent'
    (L : OverlapLayer State Query Ev Ov)
    (W₁ W₂ : State) (q : Query)
    (hind : L.independent W₁ W₂ q) :
    AdditiveWorldModel.extract
      (State := State) (Query := Query) (Ev := Ev) (L.merge W₁ W₂) q =
    AdditiveWorldModel.extract (State := State) (Query := Query) (Ev := Ev) W₁ q +
    AdditiveWorldModel.extract (State := State) (Query := Query) (Ev := Ev) W₂ q :=
  L.additive_of_independent W₁ W₂ q hind

/-- When evidence combination with zero overlap equals addition,
    independence implies the combine operation recovers hplus. -/
theorem combine_eq_add_of_independent
    (L : OverlapLayer State Query Ev Ov)
    (W₁ W₂ : State) (q : Query) (hind : L.independent W₁ W₂ q) :
    L.combine
      (AdditiveWorldModel.extract (State := State) (Query := Query) (Ev := Ev) W₁ q)
      (AdditiveWorldModel.extract (State := State) (Query := Query) (Ev := Ev) W₂ q)
      (L.overlap W₁ W₂ q) =
    AdditiveWorldModel.extract (State := State) (Query := Query) (Ev := Ev) W₁ q +
    AdditiveWorldModel.extract (State := State) (Query := Query) (Ev := Ev) W₂ q := by
  rw [← L.evidence_merge W₁ W₂ q]
  exact L.additive_of_independent W₁ W₂ q hind

end OverlapLayer

/-! ## Overlap properties for specific evidence carriers

The inclusion-exclusion principle for evidence: when two states share
evidence, the naive sum over-counts by exactly the overlap. -/

/-- An overlap layer where the correction is subtractive (inclusion-exclusion).
    `combine e₁ e₂ ov = e₁ + e₂ - ov` when subtraction is available. -/
structure SubtractiveOverlapLayer (State Query Ev : Type*)
    [EvidenceType State] [AddCommMonoid Ev] [AdditiveWorldModel State Query Ev]
    [Sub Ev] extends OverlapLayer State Query Ev Ev where
  /-- The combine operation is inclusion-exclusion: e₁ + e₂ - overlap. -/
  combine_eq_sub : ∀ e₁ e₂ ov, combine e₁ e₂ ov = e₁ + e₂ - ov
  /-- Independence means zero overlap. -/
  independent_iff_zero_overlap : ∀ W₁ W₂ q,
    independent W₁ W₂ q ↔ overlap W₁ W₂ q = 0

namespace SubtractiveOverlapLayer

variable {State Query Ev : Type*}
variable [EvidenceType State] [AddCommMonoid Ev] [Sub Ev]
variable [AdditiveWorldModel State Query Ev]

/-- The inclusion-exclusion extraction law: extract from merged states equals
    the sum of individual extractions minus the overlap.

    This is the formal content of "what goes wrong when evidence shares a
    common cause": naive addition double-counts, and the overlap term is
    exactly the double-counted amount. -/
theorem inclusionExclusion
    (L : SubtractiveOverlapLayer State Query Ev)
    (W₁ W₂ : State) (q : Query) :
    AdditiveWorldModel.extract
      (State := State) (Query := Query) (Ev := Ev) (L.merge W₁ W₂) q =
    AdditiveWorldModel.extract (State := State) (Query := Query) (Ev := Ev) W₁ q +
    AdditiveWorldModel.extract (State := State) (Query := Query) (Ev := Ev) W₂ q -
    L.overlap W₁ W₂ q := by
  rw [L.evidence_merge W₁ W₂ q, L.combine_eq_sub]

/-- When overlap is zero, inclusion-exclusion recovers additive extraction. -/
theorem inclusionExclusion_of_zero_overlap
    (L : SubtractiveOverlapLayer State Query Ev)
    (W₁ W₂ : State) (q : Query) [AddRightCancelMonoid Ev]
    (hzero : L.overlap W₁ W₂ q = 0) :
    L.independent W₁ W₂ q :=
  L.independent_iff_zero_overlap W₁ W₂ q |>.mpr hzero

end SubtractiveOverlapLayer

end Mettapedia.PLN.WorldModel.WorldModelOverlap
