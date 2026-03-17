import Mettapedia.Logic.PLNSemitopology
import Mettapedia.Logic.PLNProvenanceTrackedState
import Mettapedia.Logic.PLNScopedTrackedWhichState

/-!
# Semitopology × Provenance Bridge

Bridge the semitopology / coalition layer to concrete `Which`-valued provenance
states.

This first non-additive slice stays honest:

- exact forgetting is available on the tracked provenance-history state;
- support-level forgetting is available on the plain `Which` K-relation surface;
- overlap forgetting recovers disjoint remainder supports, and actionable
  remainder supports then give semitopological independence.

We do **not** claim exact additive recovery on the raw `Which` evidence itself,
because `Which.wset ∅` and `0 = Which.wbot` are intentionally distinct.
-/

namespace Mettapedia.Logic

open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.PLNWorldModelGeneric
open Mettapedia.Logic.LP

variable {σ : LPSignature} {n : ℕ}
variable {m : ℕ}

/-- Query-indexed support forgetting on the plain `Which` provenance surface. -/
def forgetWhichSupportBy
    (S : GroundAtom σ → Finset (Fin n))
    (I : KRelation σ (Which (Fin n))) :
    KRelation σ (Which (Fin n)) :=
  fun q => I q - Which.wset (S q)

/-- Pointwise overlap footprint between two `Which` provenance states. -/
def whichOverlapSupport
    (I₁ I₂ : KRelation σ (Which (Fin n))) :
    GroundAtom σ → Finset (Fin n) :=
  fun q => whichSupport (σ := σ) (n := n) I₁ q ∩ whichSupport (σ := σ) (n := n) I₂ q

/-- Exact tracked-state forgetting by subtracting the tracked revision itself. -/
theorem tracked_exactInverse_of_trackedRevision
    (W Δ : TrackedWhichState σ n) :
    forgetTracked Δ (W + Δ) = W :=
  forgetTracked_add_right W Δ

theorem whichSupport_forgetWhichSupportBy
    (S : GroundAtom σ → Finset (Fin n))
    (I : KRelation σ (Which (Fin n))) (q : GroundAtom σ) :
    whichSupport (σ := σ) (n := n) (forgetWhichSupportBy S I) q =
      whichSupport (σ := σ) (n := n) I q \ S q := by
  unfold forgetWhichSupportBy whichSupport
  cases hI : I q with
  | wbot =>
      simp [hI]
  | wset s =>
      by_cases hs : s ⊆ S q
      · have hdif : s \ S q = ∅ := by
          ext i
          constructor
          · intro hi
            simp at hi
            exact (hi.2 (hs hi.1)).elim
          · intro hi
            simp at hi
        simp [(· - ·), Sub.sub, hI, hs, hdif]
      · ext i
        simp [(· - ·), Sub.sub, hI, hs]

theorem whichSupport_forgetWhichSupportBy_eq_empty_of_subset
    (S : GroundAtom σ → Finset (Fin n))
    (I : KRelation σ (Which (Fin n))) (q : GroundAtom σ)
    (hs : whichSupport (σ := σ) (n := n) I q ⊆ S q) :
    whichSupport (σ := σ) (n := n) (forgetWhichSupportBy S I) q = ∅ := by
  rw [whichSupport_forgetWhichSupportBy]
  ext i
  constructor
  · intro hi
    simp at hi
    exact (hi.2 (hs hi.1)).elim
  · intro hi
    simp at hi

theorem whichSupport_forgetWhichSupportBy_eq_self_of_disjoint
    (S : GroundAtom σ → Finset (Fin n))
    (I : KRelation σ (Which (Fin n))) (q : GroundAtom σ)
    (hdisj : Disjoint (whichSupport (σ := σ) (n := n) I q) (S q)) :
    whichSupport (σ := σ) (n := n) (forgetWhichSupportBy S I) q =
      whichSupport (σ := σ) (n := n) I q := by
  rw [whichSupport_forgetWhichSupportBy]
  ext i
  constructor
  · intro hi
    simp at hi
    exact hi.1
  · intro hi
    have hiS : i ∉ S q := by
      intro hiS
      exact (Finset.disjoint_left.mp hdisj) hi hiS
    simp [hi, hiS]

theorem whichSupport_forgetWhichOverlap_add
    (I₁ I₂ : KRelation σ (Which (Fin n))) (q : GroundAtom σ) :
    whichSupport (σ := σ) (n := n)
        (forgetWhichSupportBy (whichOverlapSupport (σ := σ) (n := n) I₁ I₂) (I₁ + I₂)) q =
      whichSupport (σ := σ) (n := n)
        (forgetWhichSupportBy (whichOverlapSupport (σ := σ) (n := n) I₁ I₂) I₁) q
        ∪
      whichSupport (σ := σ) (n := n)
        (forgetWhichSupportBy (whichOverlapSupport (σ := σ) (n := n) I₁ I₂) I₂) q := by
  rw [whichSupport_forgetWhichSupportBy, whichSupport_add_union]
  rw [whichSupport_forgetWhichSupportBy, whichSupport_forgetWhichSupportBy]
  ext i
  simp [whichOverlapSupport]
  tauto

theorem toTracked_evidence_forgetWhichSupportBy
    (S : GroundAtom σ → Finset (Fin n))
    (I : KRelation σ (Which (Fin n))) (q : GroundAtom σ) :
    AdditiveWorldModel.extract
      (State := TrackedWhichState σ n) (Query := GroundAtom σ) (Ev := Which (Fin n))
      (toTrackedWhichState (forgetWhichSupportBy S I)) q =
    forgetWhichSupportBy S I q := by
  exact toTracked_evidence_eq (σ := σ) (n := n) (I := forgetWhichSupportBy S I) q

theorem toTracked_exactInverse_of_supported_disjoint
    (W Δ : KRelation σ (Which (Fin n))) :
    forgetTracked (toTrackedWhichState Δ)
        (toTrackedWhichState W + toTrackedWhichState Δ) =
      toTrackedWhichState W := by
  simpa using toTracked_forget_exactInverse (σ := σ) (n := n) Δ (toTrackedWhichState W)

/-- Remainder supports after overlap forgetting on the two inputs. -/
def remainderSupportLeft
    (I₁ I₂ : KRelation σ (Which (Fin n))) (q : GroundAtom σ) : Finset (Fin n) :=
  whichSupport (σ := σ) (n := n)
    (forgetWhichSupportBy (whichOverlapSupport (σ := σ) (n := n) I₁ I₂) I₁) q

/-- Symmetric right remainder support. -/
def remainderSupportRight
    (I₁ I₂ : KRelation σ (Which (Fin n))) (q : GroundAtom σ) : Finset (Fin n) :=
  whichSupport (σ := σ) (n := n)
    (forgetWhichSupportBy (whichOverlapSupport (σ := σ) (n := n) I₁ I₂) I₂) q

theorem remainderSupports_disjoint_after_forgetting_overlap
    (I₁ I₂ : KRelation σ (Which (Fin n))) (q : GroundAtom σ) :
    Disjoint
      (remainderSupportLeft (σ := σ) (n := n) I₁ I₂ q)
      (remainderSupportRight (σ := σ) (n := n) I₁ I₂ q) := by
  unfold remainderSupportLeft remainderSupportRight
  rw [whichSupport_forgetWhichSupportBy, whichSupport_forgetWhichSupportBy]
  refine Finset.disjoint_left.2 ?_
  intro i hiL hiR
  simp [whichOverlapSupport] at hiL hiR
  exact hiL.2 hiR.1

theorem semitopologyIndependent_remainders_after_forgetting_overlap
    (T : Semitopology (Fin n))
    (I₁ I₂ : KRelation σ (Which (Fin n))) (q : GroundAtom σ)
    (hleft :
      T.actionable
        (↑(remainderSupportLeft (σ := σ) (n := n) I₁ I₂ q) : Set (Fin n)))
    (hright :
      T.actionable
        (↑(remainderSupportRight (σ := σ) (n := n) I₁ I₂ q) : Set (Fin n))) :
    Semitopology.SemitopologyIndependent
      T
      (fun I q => (whichSupport (σ := σ) (n := n) I q : Set (Fin n)))
      (forgetWhichSupportBy (whichOverlapSupport (σ := σ) (n := n) I₁ I₂) I₁)
      (forgetWhichSupportBy (whichOverlapSupport (σ := σ) (n := n) I₁ I₂) I₂)
      q := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [remainderSupportLeft] using hleft
  · simpa [remainderSupportRight] using hright
  · refine Set.disjoint_left.2 ?_
    intro i hiL hiR
    exact (Finset.disjoint_left.mp
      (remainderSupports_disjoint_after_forgetting_overlap (σ := σ) (n := n) I₁ I₂ q))
      hiL hiR

/-! ## Scope-labelled tracked provenance -/

/-- Shared scope-label footprint between two scoped tracked states. -/
def scopedOverlapFootprint
    (W₁ W₂ : ScopedTrackedWhichState σ n m) (q : GroundAtom σ) : Finset (Fin m) :=
  scopedTrackedScopeSupport W₁ q ∩ scopedTrackedScopeSupport W₂ q

/-- Left remainder after forgetting the shared scope-label footprint. -/
def scopedRemainderLeft
    (W₁ W₂ : ScopedTrackedWhichState σ n m) (q : GroundAtom σ) :
    ScopedTrackedWhichState σ n m :=
  forgetScopedByScope
    (scopedOverlapFootprint (σ := σ) (n := n) (m := m) W₁ W₂ q) W₁

/-- Right remainder after forgetting the shared scope-label footprint. -/
def scopedRemainderRight
    (W₁ W₂ : ScopedTrackedWhichState σ n m) (q : GroundAtom σ) :
    ScopedTrackedWhichState σ n m :=
  forgetScopedByScope
    (scopedOverlapFootprint (σ := σ) (n := n) (m := m) W₁ W₂ q) W₂

/-- Set-valued scope support for semitopological reasoning. -/
def scopedScopeSupportSet
    (W : ScopedTrackedWhichState σ n m) (q : GroundAtom σ) : Set (Fin m) :=
  ↑(scopedTrackedScopeSupport W q)

theorem scopedTrackedEvidence_after_forgetting_overlap_add
    (W₁ W₂ : ScopedTrackedWhichState σ n m) (q : GroundAtom σ) :
    AdditiveWorldModel.extract
      (State := ScopedTrackedWhichState σ n m) (Query := GroundAtom σ) (Ev := Which (Fin n))
      (forgetScopedByScope
        (scopedOverlapFootprint (σ := σ) (n := n) (m := m) W₁ W₂ q) (W₁ + W₂)) q =
    AdditiveWorldModel.extract
      (State := ScopedTrackedWhichState σ n m) (Query := GroundAtom σ) (Ev := Which (Fin n))
      (forgetScopedByScope
        (scopedOverlapFootprint (σ := σ) (n := n) (m := m) W₁ W₂ q) W₁) q +
    AdditiveWorldModel.extract
      (State := ScopedTrackedWhichState σ n m) (Query := GroundAtom σ) (Ev := Which (Fin n))
      (forgetScopedByScope
        (scopedOverlapFootprint (σ := σ) (n := n) (m := m) W₁ W₂ q) W₂) q := by
  rw [forgetScopedByScope_add, AdditiveWorldModel.extract_add']

theorem scopedRemainderScopeSupports_disjoint_after_forgetting_overlap
    (W₁ W₂ : ScopedTrackedWhichState σ n m) (q : GroundAtom σ) :
    Disjoint
      (scopedTrackedScopeSupport
        (scopedRemainderLeft (σ := σ) (n := n) (m := m) W₁ W₂ q) q)
      (scopedTrackedScopeSupport
        (scopedRemainderRight (σ := σ) (n := n) (m := m) W₁ W₂ q) q) := by
  unfold scopedRemainderLeft scopedRemainderRight
  refine Finset.disjoint_left.2 ?_
  intro i hiL hiR
  simp [scopedTrackedScopeSupport, forgetScopedByScope, scopedOverlapFootprint,
    Multiset.mem_toFinset] at hiL hiR
  rcases hiL.1 with ⟨x, hx⟩
  rcases hiR.1 with ⟨y, hy⟩
  exact hiL.2 x hx y hy

/-- Stronger semitopological separation criterion on the scoped tracked state:
the overlap footprint itself is non-actionable, while both remainders remain
actionable. -/
def ScopedSemitopologySeparatedByOverlap
    (T : Semitopology (Fin m))
    (W₁ W₂ : ScopedTrackedWhichState σ n m) (q : GroundAtom σ) : Prop :=
  T.actionable
      (scopedScopeSupportSet
        (scopedRemainderLeft (σ := σ) (n := n) (m := m) W₁ W₂ q) q) ∧
  T.actionable
      (scopedScopeSupportSet
        (scopedRemainderRight (σ := σ) (n := n) (m := m) W₁ W₂ q) q) ∧
  ¬ T.actionable
      (↑(scopedOverlapFootprint (σ := σ) (n := n) (m := m) W₁ W₂ q) : Set (Fin m))

theorem semitopologyIndependent_scopedRemainders_after_forgetting_overlap
    (T : Semitopology (Fin m))
    (W₁ W₂ : ScopedTrackedWhichState σ n m) (q : GroundAtom σ)
    (hsep : ScopedSemitopologySeparatedByOverlap (σ := σ) (n := n) (m := m) T W₁ W₂ q) :
    Semitopology.SemitopologyIndependent
      T
      (scopedScopeSupportSet (σ := σ) (n := n) (m := m))
      (scopedRemainderLeft (σ := σ) (n := n) (m := m) W₁ W₂ q)
      (scopedRemainderRight (σ := σ) (n := n) (m := m) W₁ W₂ q)
      q := by
  rcases hsep with ⟨hleft, hright, _hoverlap⟩
  refine ⟨hleft, hright, ?_⟩
  refine Set.disjoint_left.2 ?_
  intro i hiL hiR
  exact (Finset.disjoint_left.mp
    (scopedRemainderScopeSupports_disjoint_after_forgetting_overlap
      (σ := σ) (n := n) (m := m) W₁ W₂ q)) hiL hiR

theorem additive_recovery_after_forgetting_nonactionable_overlap
    (T : Semitopology (Fin m))
    (W₁ W₂ : ScopedTrackedWhichState σ n m) (q : GroundAtom σ)
    (hsep : ScopedSemitopologySeparatedByOverlap (σ := σ) (n := n) (m := m) T W₁ W₂ q) :
    AdditiveWorldModel.extract
      (State := ScopedTrackedWhichState σ n m) (Query := GroundAtom σ) (Ev := Which (Fin n))
      (forgetScopedByScope
        (scopedOverlapFootprint (σ := σ) (n := n) (m := m) W₁ W₂ q) (W₁ + W₂)) q =
    AdditiveWorldModel.extract
      (State := ScopedTrackedWhichState σ n m) (Query := GroundAtom σ) (Ev := Which (Fin n))
      (scopedRemainderLeft (σ := σ) (n := n) (m := m) W₁ W₂ q) q +
    AdditiveWorldModel.extract
      (State := ScopedTrackedWhichState σ n m) (Query := GroundAtom σ) (Ev := Which (Fin n))
      (scopedRemainderRight (σ := σ) (n := n) (m := m) W₁ W₂ q) q := by
  have _ :=
    semitopologyIndependent_scopedRemainders_after_forgetting_overlap
      (σ := σ) (n := n) (m := m) T W₁ W₂ q hsep
  exact scopedTrackedEvidence_after_forgetting_overlap_add (σ := σ) (n := n) (m := m) W₁ W₂ q

end Mettapedia.Logic
