import Mathlib.Data.ENNReal.Basic
import Mettapedia.Logic.ConjugateEvidenceSurface
import Mettapedia.Logic.GenericWorldModelForgetting
import Mettapedia.Logic.PLNWorldModelOverlap
import Mettapedia.Logic.PLNWorldModelConservationPack
import Mettapedia.Logic.PLNWorldModelOrderCostBounds
import Mettapedia.Logic.PLNSemitopologyProvenanceBridge

/-!
# WM Audit Surface

Small audit-facing wrappers over the existing WM theorem surface:

- evidence-conservation checks (no hallucination / zero outside-scope leakage),
- non-commutative order-sensitivity signal (`SwapDefect`),
- overlap-separation criterion for safe additive recovery after overlap forgetting.
-/

namespace Mettapedia.Logic

open scoped ENNReal
open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.ConjugateEvidenceSurface
open Mettapedia.Logic.PLNWorldModelGeneric
open Mettapedia.Logic.LP

section Conservation

variable {State Scope Query Ev : Type*}
variable [EvidenceType State] [AddCommMonoid Ev] [AdditiveWorldModel State Query Ev]

/-- Audit predicate: revision `Δ` contributes no evidence outside forgotten scope `S`. -/
def NoHallucinationOutsideScope
    (F : ForgettingLayer State Scope Query Ev)
    (S : Scope) (Δ : State) : Prop :=
  ∀ q, ¬ F.inScope S q →
    AdditiveWorldModel.extract
      (State := State) (Query := Query) (Ev := Ev) Δ q = 0

theorem noHallucinationOutsideScope_of_exactInverse
    (F : ForgettingLayer State Scope Query Ev)
    (hzero : GenericWorldModelZeroPreserving (State := State) (Query := Query) (Ev := Ev))
    {S : Scope} {Δ : State}
    (hinv : ∀ W : State, F.forget S (W + Δ) = W) :
    NoHallucinationOutsideScope (State := State) (Scope := Scope) (Query := Query) (Ev := Ev)
      F S Δ := by
  intro q hout
  exact ForgettingLayer.exactInverse_revision_supported
    (State := State) (Scope := Scope) (Query := Query) (Ev := Ev)
    F hzero hinv q hout

end Conservation

section ConservationCount

variable {State Scope Query Ev : Type*}
variable [EvidenceType State] [ConjugateEvidence Ev] [AdditiveWorldModel State Query Ev]

theorem zeroLeakageOutsideScope_of_exactInverse
    (F : ForgettingLayer State Scope Query Ev)
    (hzero : GenericWorldModelZeroPreserving (State := State) (Query := Query) (Ev := Ev))
    {S : Scope} {Δ : State}
    (hinv : ∀ W : State, F.forget S (W + Δ) = W) :
    ∀ q, ¬ F.inScope S q →
      AdditiveWorldModel.queryObservationCount
        (State := State) (Query := Query) (Ev := Ev) Δ q = 0 := by
  intro q hout
  have hEv :
      AdditiveWorldModel.extract
        (State := State) (Query := Query) (Ev := Ev) Δ q = 0 :=
    ForgettingLayer.exactInverse_revision_supported
      (State := State) (Scope := Scope) (Query := Query) (Ev := Ev)
      F hzero hinv q hout
  unfold AdditiveWorldModel.queryObservationCount
  simpa [hEv] using (ConjugateEvidence.observationCount_zero (Ev := Ev))

end ConservationCount

section OrderCost

variable {State Query Ev Ov : Type*}
variable [EvidenceType State] [ConjugateEvidence Ev] [AdditiveWorldModel State Query Ev]

/-- Order-cost signal: evidence extracted from `merge W₁ W₂` differs from
`merge W₂ W₁` at query `q`. -/
def SwapDefect
    (L : OverlapLayer State Query Ev Ov)
    (W₁ W₂ : State) (q : Query) : Prop :=
  AdditiveWorldModel.extract
      (State := State) (Query := Query) (Ev := Ev) (L.merge W₁ W₂) q ≠
    AdditiveWorldModel.extract
      (State := State) (Query := Query) (Ev := Ev) (L.merge W₂ W₁) q

/-- Layer-level order sensitivity witness. -/
def OrderSensitive
    (L : OverlapLayer State Query Ev Ov) : Prop :=
  ∃ W₁ W₂ q, SwapDefect (State := State) (Query := Query) (Ev := Ev) (Ov := Ov) L W₁ W₂ q

theorem not_orderSensitive_of_commutativeMergeEvidence
    (L : OverlapLayer State Query Ev Ov)
    (hcomm :
      ∀ W₁ W₂ q,
        AdditiveWorldModel.extract
          (State := State) (Query := Query) (Ev := Ev) (L.merge W₁ W₂) q =
        AdditiveWorldModel.extract
          (State := State) (Query := Query) (Ev := Ev) (L.merge W₂ W₁) q) :
    ¬ OrderSensitive (State := State) (Query := Query) (Ev := Ev) (Ov := Ov) L := by
  intro hsens
  rcases hsens with ⟨W₁, W₂, q, hdef⟩
  exact hdef (hcomm W₁ W₂ q)

theorem swapAnomalyCount_zero_of_notSwapDefect
    (L : OverlapLayer State Query Ev Ov)
    (W₁ W₂ : State) (q : Query)
    (hdef : ¬ SwapDefect (State := State) (Query := Query) (Ev := Ev) (Ov := Ov) L W₁ W₂ q) :
    Mettapedia.Logic.SwapAnomalyCount
      (State := State) (Query := Query) (Ev := Ev) (Ov := Ov) L W₁ W₂ q = 0 := by
  have hEq :
      AdditiveWorldModel.extract
        (State := State) (Query := Query) (Ev := Ev) (L.merge W₁ W₂) q =
      AdditiveWorldModel.extract
        (State := State) (Query := Query) (Ev := Ev) (L.merge W₂ W₁) q :=
    not_ne_iff.mp hdef
  simpa using
    Mettapedia.Logic.swapAnomalyCount_zero_of_commutativeMergeEvidence
      (State := State) (Query := Query) (Ev := Ev) (Ov := Ov) L W₁ W₂ q hEq

theorem swapAnomalyBound_zero_of_notSwapDefect
    (L : OverlapLayer State Query Ev Ov)
    (W₁ W₂ : State) (q : Query)
    (hdef : ¬ SwapDefect (State := State) (Query := Query) (Ev := Ev) (Ov := Ov) L W₁ W₂ q) :
    Mettapedia.Logic.SwapAnomalyBound
      (State := State) (Query := Query) (Ev := Ev) (Ov := Ov) L W₁ W₂ q 0 := by
  simpa [Mettapedia.Logic.SwapAnomalyBound] using le_of_eq
    (swapAnomalyCount_zero_of_notSwapDefect
      (State := State) (Query := Query) (Ev := Ev) (Ov := Ov) L W₁ W₂ q hdef)

end OrderCost

section OverlapTopology

variable {σ : LPSignature} {n m : ℕ}

/-- Audit predicate encoding "safe overlap separation" used by the scoped
provenance/semitopology bridge. -/
def OverlapSeparatedAudit
    (T : Semitopology (Fin m))
    (W₁ W₂ : ScopedTrackedWhichState σ n m) (q : GroundAtom σ) : Prop :=
  ScopedSemitopologySeparatedByOverlap (σ := σ) (n := n) (m := m) T W₁ W₂ q

theorem semitopologyIndependent_of_overlapSeparatedAudit
    (T : Semitopology (Fin m))
    (W₁ W₂ : ScopedTrackedWhichState σ n m) (q : GroundAtom σ)
    (haudit : OverlapSeparatedAudit (σ := σ) (n := n) (m := m) T W₁ W₂ q) :
    Semitopology.SemitopologyIndependent
      T
      (scopedScopeSupportSet (σ := σ) (n := n) (m := m))
      (scopedRemainderLeft (σ := σ) (n := n) (m := m) W₁ W₂ q)
      (scopedRemainderRight (σ := σ) (n := n) (m := m) W₁ W₂ q)
      q :=
  semitopologyIndependent_scopedRemainders_after_forgetting_overlap
    (σ := σ) (n := n) (m := m) T W₁ W₂ q haudit

theorem additiveRecovery_of_overlapSeparatedAudit
    (T : Semitopology (Fin m))
    (W₁ W₂ : ScopedTrackedWhichState σ n m) (q : GroundAtom σ)
    (haudit : OverlapSeparatedAudit (σ := σ) (n := n) (m := m) T W₁ W₂ q) :
    AdditiveWorldModel.extract
      (State := ScopedTrackedWhichState σ n m) (Query := GroundAtom σ) (Ev := Which (Fin n))
      (forgetScopedByScope
        (scopedOverlapFootprint (σ := σ) (n := n) (m := m) W₁ W₂ q) (W₁ + W₂)) q =
    AdditiveWorldModel.extract
      (State := ScopedTrackedWhichState σ n m) (Query := GroundAtom σ) (Ev := Which (Fin n))
      (scopedRemainderLeft (σ := σ) (n := n) (m := m) W₁ W₂ q) q +
    AdditiveWorldModel.extract
      (State := ScopedTrackedWhichState σ n m) (Query := GroundAtom σ) (Ev := Which (Fin n))
      (scopedRemainderRight (σ := σ) (n := n) (m := m) W₁ W₂ q) q :=
  additive_recovery_after_forgetting_nonactionable_overlap
    (σ := σ) (n := n) (m := m) T W₁ W₂ q haudit

end OverlapTopology

end Mettapedia.Logic
