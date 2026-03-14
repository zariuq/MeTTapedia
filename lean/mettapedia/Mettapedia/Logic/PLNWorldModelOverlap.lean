import Mettapedia.Logic.PLNWorldModelGeneric

/-!
# Generic WM Overlap Layer

Non-additive perimeter layer over the existing `GenericWorldModel` interface:

- keep additive extraction as the canonical core;
- add overlap-aware merge semantics as extra structure;
- recover additive evidence when an explicit independence predicate holds.
-/

namespace Mettapedia.Logic

open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.PLNWorldModelGeneric

variable {State Query Ev Ov : Type*}
variable [EvidenceType State] [AddCommMonoid Ev] [GenericWorldModel State Query Ev]

/-- Overlap/correlation layer over a generic world model. -/
structure OverlapLayer (State Query Ev Ov : Type*)
    [EvidenceType State] [AddCommMonoid Ev] [GenericWorldModel State Query Ev] where
  merge : State → State → State
  overlap : State → State → Query → Ov
  combine : Ev → Ev → Ov → Ev
  independent : State → State → Query → Prop
  evidence_merge :
    ∀ W₁ W₂ q,
      GenericWorldModel.evidence
        (State := State) (Query := Query) (Ev := Ev) (merge W₁ W₂) q =
      combine
        (GenericWorldModel.evidence (State := State) (Query := Query) (Ev := Ev) W₁ q)
        (GenericWorldModel.evidence (State := State) (Query := Query) (Ev := Ev) W₂ q)
        (overlap W₁ W₂ q)
  additive_of_independent :
    ∀ W₁ W₂ q, independent W₁ W₂ q →
      GenericWorldModel.evidence
        (State := State) (Query := Query) (Ev := Ev) (merge W₁ W₂) q =
      GenericWorldModel.evidence (State := State) (Query := Query) (Ev := Ev) W₁ q +
      GenericWorldModel.evidence (State := State) (Query := Query) (Ev := Ev) W₂ q

namespace OverlapLayer

variable {State Query Ev Ov : Type*}
variable [EvidenceType State] [AddCommMonoid Ev] [GenericWorldModel State Query Ev]

theorem evidence_merge'
    (L : OverlapLayer State Query Ev Ov)
    (W₁ W₂ : State) (q : Query) :
    GenericWorldModel.evidence
      (State := State) (Query := Query) (Ev := Ev) (L.merge W₁ W₂) q =
    L.combine
      (GenericWorldModel.evidence (State := State) (Query := Query) (Ev := Ev) W₁ q)
      (GenericWorldModel.evidence (State := State) (Query := Query) (Ev := Ev) W₂ q)
      (L.overlap W₁ W₂ q) :=
  L.evidence_merge W₁ W₂ q

theorem additive_of_independent'
    (L : OverlapLayer State Query Ev Ov)
    (W₁ W₂ : State) (q : Query)
    (hind : L.independent W₁ W₂ q) :
    GenericWorldModel.evidence
      (State := State) (Query := Query) (Ev := Ev) (L.merge W₁ W₂) q =
    GenericWorldModel.evidence (State := State) (Query := Query) (Ev := Ev) W₁ q +
    GenericWorldModel.evidence (State := State) (Query := Query) (Ev := Ev) W₂ q :=
  L.additive_of_independent W₁ W₂ q hind

end OverlapLayer
end Mettapedia.Logic
