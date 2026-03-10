import Mettapedia.Logic.PLNWorldModelGeneric

/-!
# Generic World-Model Forgetting

This module adds an explicit forgetting/contraction layer on top of the generic
world-model interface.

The point is deliberately modest:

- forgetting is *not* default revision;
- it is a separate operation with its own laws;
- exact inverse forgetting is only possible for revisions whose evidence lies
  entirely inside the forgotten scope.

The last theorem is the precise no-go result proved here. Stronger inverse
forgetting principles would need richer provenance or support tracking.
-/

namespace Mettapedia.Logic

open scoped ENNReal
open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.ConjugateEvidenceSurface
open Mettapedia.Logic.PLNWorldModelGeneric

variable {State Query Ev : Type*}
variable [EvidenceType State] [AddCommMonoid Ev] [GenericWorldModel State Query Ev]

/-- A generic world model is zero-preserving when the empty/zero state extracts
zero evidence for every query. Additivity alone does not force this. -/
def GenericWorldModelZeroPreserving : Prop :=
  ∀ q,
    GenericWorldModel.evidence
      (State := State) (Query := Query) (Ev := Ev) (0 : State) q = 0

/-- A forgetting layer over a generic world model.

`inScope S q` means that query `q` lies inside the forgotten scope `S`. Outside
that scope, forgetting must leave the extracted evidence unchanged. -/
structure ForgettingLayer (State Scope Query Ev : Type*)
    [EvidenceType State] [AddCommMonoid Ev] [GenericWorldModel State Query Ev] where
  inScope : Scope → Query → Prop
  forget : Scope → State → State
  idempotent : ∀ S W, forget S (forget S W) = forget S W
  outsideInvariant :
    ∀ {S W q}, ¬ inScope S q →
      GenericWorldModel.evidence
        (State := State) (Query := Query) (Ev := Ev) (forget S W) q =
      GenericWorldModel.evidence
        (State := State) (Query := Query) (Ev := Ev) W q

namespace ForgettingLayer

variable {State Scope Query Ev : Type*}
variable [EvidenceType State] [AddCommMonoid Ev] [GenericWorldModel State Query Ev]

theorem idempotent' (F : ForgettingLayer State Scope Query Ev)
    (S : Scope) (W : State) :
    F.forget S (F.forget S W) = F.forget S W :=
  F.idempotent S W

theorem outsideInvariant'
    (F : ForgettingLayer State Scope Query Ev)
    {S : Scope} {W : State} {q : Query}
    (hout : ¬ F.inScope S q) :
    GenericWorldModel.evidence
      (State := State) (Query := Query) (Ev := Ev) (F.forget S W) q =
    GenericWorldModel.evidence
      (State := State) (Query := Query) (Ev := Ev) W q :=
  F.outsideInvariant hout

section Conjugate

variable [ConjugateEvidence Ev]

theorem outsideInvariant_queryObservationCount
    (F : ForgettingLayer State Scope Query Ev)
    {S : Scope} {W : State} {q : Query}
    (hout : ¬ F.inScope S q) :
    GenericWorldModel.queryObservationCount
      (State := State) (Query := Query) (Ev := Ev) (F.forget S W) q =
    GenericWorldModel.queryObservationCount
      (State := State) (Query := Query) (Ev := Ev) W q := by
  unfold GenericWorldModel.queryObservationCount
  simpa using congrArg ConjugateEvidence.observationCount (F.outsideInvariant hout)

theorem outsideInvariant_queryObservationConfidence
    (F : ForgettingLayer State Scope Query Ev)
    (κ : ℝ≥0∞)
    {S : Scope} {W : State} {q : Query}
    (hout : ¬ F.inScope S q) :
    GenericWorldModel.queryObservationConfidence
      (State := State) (Query := Query) (Ev := Ev) κ (F.forget S W) q =
    GenericWorldModel.queryObservationConfidence
      (State := State) (Query := Query) (Ev := Ev) κ W q := by
  unfold GenericWorldModel.queryObservationConfidence
  simpa using congrArg (observationConfidence κ) (F.outsideInvariant hout)

end Conjugate

/-- Exact inverse forgetting can only undo revisions whose evidence vanishes
outside the forgotten scope. -/
theorem exactInverse_revision_supported
    (F : ForgettingLayer State Scope Query Ev)
    (hzero : GenericWorldModelZeroPreserving (State := State) (Query := Query) (Ev := Ev))
    {S : Scope} {Δ : State}
    (hinv : ∀ W : State, F.forget S (W + Δ) = W) :
    ∀ q, ¬ F.inScope S q →
      GenericWorldModel.evidence
        (State := State) (Query := Query) (Ev := Ev) Δ q = 0 := by
  intro q hout
  have hOutside :=
    F.outsideInvariant (S := S) (W := (0 : State) + Δ) (q := q) hout
  have hInv0 : F.forget S ((0 : State) + Δ) = (0 : State) := by
    simpa using hinv (0 : State)
  calc
    GenericWorldModel.evidence
        (State := State) (Query := Query) (Ev := Ev) Δ q
      = GenericWorldModel.evidence
          (State := State) (Query := Query) (Ev := Ev) ((0 : State) + Δ) q := by
            simp
    _ = GenericWorldModel.evidence
          (State := State) (Query := Query) (Ev := Ev) (F.forget S ((0 : State) + Δ)) q := by
            symm
            exact hOutside
    _ = GenericWorldModel.evidence
          (State := State) (Query := Query) (Ev := Ev) (0 : State) q := by
            rw [hInv0]
    _ = 0 := hzero q

/-- No forgetting layer can be an exact inverse to a revision that changes a
query outside the forgotten scope. -/
theorem no_exactInverse_revision_of_nonzero_outside_scope
    (F : ForgettingLayer State Scope Query Ev)
    (hzero : GenericWorldModelZeroPreserving (State := State) (Query := Query) (Ev := Ev))
    {S : Scope} {Δ : State} {q : Query}
    (hout : ¬ F.inScope S q)
    (hne :
      GenericWorldModel.evidence
        (State := State) (Query := Query) (Ev := Ev) Δ q ≠ 0) :
    ¬ ∀ W : State, F.forget S (W + Δ) = W := by
  intro hinv
  exact hne (exactInverse_revision_supported
    (State := State) (Scope := Scope) (Query := Query) (Ev := Ev)
    F hzero hinv q hout)

end ForgettingLayer

end Mettapedia.Logic
