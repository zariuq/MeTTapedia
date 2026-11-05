import Mettapedia.PLN.WorldModel.Provenance.PLNScopedTrackedWhichState
import Mettapedia.PLN.WorldModel.ForgettingEvidenceLaws

/-!
# Scope-labelled tracked provenance as a support-closed forgetting layer

Each query of a `ScopedTrackedWhichState` carries chunks labelled by the scope that contributed
them, and forgetting a set of labels removes their chunks (`forgetScopedByScope`).  With the labels
carried at a query as its support and a set of labels as its own footprint, this is a support-closed
forgetting layer (`scopedSupportClosedLayer`).  It commutes with revision, erases states supported
in the forgotten labels and fixes clean ones, so it undoes a supported revision of a clean base
exactly; its retained supports shrink and avoid the forgotten labels; and nonzero evidence carries a
label.  With lineage ordered by inclusion it is a retraction layer (`scopedRetractionLayer`): no
evidence grows, and a query whose labels avoid the forgotten ones keeps its evidence.  The
clean-base theorems of `PLNScopedTrackedWhichState` and `PLNProvenanceInference` are instances of
the interface laws.
-/

set_option autoImplicit false

namespace Mettapedia.PLN.WorldModel.ScopedTrackedRetraction

open Mettapedia.PLN.WorldModel.Provenance
open Mettapedia.PLN.WorldModel.ForgettingEvidenceLaws (SupportClosedForgettingLayer RetractionLayer)
open Mettapedia.Logic.LP

variable {σ : LPSignature} {n m : ℕ}

theorem mem_scopedTrackedScopeSupport {W : ScopedTrackedWhichState σ n m} {q : GroundAtom σ}
    {s : Fin m} :
    s ∈ scopedTrackedScopeSupport W q ↔ ∃ chunk ∈ W q, chunk.1 = s := by
  simp [scopedTrackedScopeSupport]

/-- **Forgetting scope labels is a support-closed forgetting layer.**  Every query may carry every
label, so the static scope of a forgetting is every query, and the content of the layer is in its
supports. -/
noncomputable def scopedSupportClosedLayer :
    SupportClosedForgettingLayer (ScopedTrackedWhichState σ n m) (Finset (Fin m)) (GroundAtom σ)
      (Which (Fin n)) (Fin m) where
  inScope _ _ := True
  forget := forgetScopedByScope
  idempotent := forgetScopedByScope_idempotent
  outsideInvariant hout := absurd trivial hout
  scopeFootprint S := S
  support W q := scopedTrackedScopeSupport W q
  forget_add := forgetScopedByScope_add
  forget_eq_zero_of_supported := by
    intro S Δ hsupp
    exact forgetScopedByScope_eq_zero_of_supportedInScope fun q chunk hchunk =>
      hsupp q (mem_scopedTrackedScopeSupport.mpr ⟨chunk, hchunk, rfl⟩)
  forget_eq_self_of_clean := by
    intro S W hclean
    exact forgetScopedByScope_eq_self_of_scopeClean fun q chunk hchunk =>
      Finset.disjoint_left.mp (hclean q) (mem_scopedTrackedScopeSupport.mpr ⟨chunk, hchunk, rfl⟩)
  support_nonempty_of_ne_zero := by
    intro W q hne
    have hunion : scopedTrackedUnionSupport W q ≠ ∅ := fun h =>
      hne ((scopedTrackedEvidence_eq_zero_iff_support_empty W q).mpr h)
    obtain ⟨i, hi⟩ := Finset.nonempty_of_ne_empty hunion
    simp only [scopedTrackedUnionSupport, Finset.mem_biUnion, Multiset.mem_toFinset] at hi
    obtain ⟨chunk, hchunk, -⟩ := hi
    exact ⟨chunk.1, mem_scopedTrackedScopeSupport.mpr ⟨chunk, hchunk, rfl⟩⟩
  retained_support_subset := by
    intro S W q s hs
    obtain ⟨chunk, hchunk, rfl⟩ := mem_scopedTrackedScopeSupport.mp hs
    simp only [forgetScopedByScope, Multiset.mem_filter] at hchunk
    exact mem_scopedTrackedScopeSupport.mpr ⟨chunk, hchunk.1, rfl⟩
  retained_support_disjoint := by
    intro S W q
    rw [Finset.disjoint_left]
    intro s hs hsS
    obtain ⟨chunk, hchunk, rfl⟩ := mem_scopedTrackedScopeSupport.mp hs
    simp only [forgetScopedByScope, Multiset.mem_filter] at hchunk
    exact hchunk.2 hsS

theorem scopedTrackedEvidence_congr {W W' : ScopedTrackedWhichState σ n m} {q : GroundAtom σ}
    (h : W' q = W q) : scopedTrackedEvidence W' q = scopedTrackedEvidence W q := by
  unfold scopedTrackedEvidence scopedTrackedPayloadSupport scopedTrackedUnionSupport
  rw [h]

theorem scopedTrackedUnionSupport_mono {W W' : ScopedTrackedWhichState σ n m} {q : GroundAtom σ}
    (le : W' q ≤ W q) : scopedTrackedUnionSupport W' q ⊆ scopedTrackedUnionSupport W q :=
  Finset.biUnion_subset_biUnion_of_subset_left _
    (Multiset.toFinset_subset.mpr (Multiset.subset_of_le le))

theorem scopedTrackedPayloadSupport_mono {W W' : ScopedTrackedWhichState σ n m} {q : GroundAtom σ}
    (le : W' q ≤ W q) : scopedTrackedPayloadSupport W' q ⊆ scopedTrackedPayloadSupport W q :=
  Finset.biUnion_subset_biUnion_of_subset_left _ (scopedTrackedUnionSupport_mono le)

/-- Fewer chunks never give more lineage. -/
theorem scopedTrackedEvidence_mono {W W' : ScopedTrackedWhichState σ n m} {q : GroundAtom σ}
    (le : W' q ≤ W q) : scopedTrackedEvidence W' q ≤ scopedTrackedEvidence W q := by
  unfold scopedTrackedEvidence
  by_cases h' : scopedTrackedUnionSupport W' q = ∅
  · simp only [h', dite_true]
    exact trivial
  · have h : scopedTrackedUnionSupport W q ≠ ∅ := fun hW =>
      h' (Finset.subset_empty.mp (hW ▸ scopedTrackedUnionSupport_mono le))
    simp only [h', h, dite_false]
    exact scopedTrackedPayloadSupport_mono le

/-- **Forgetting scope labels is a retraction layer**, with lineage ordered by inclusion: no
evidence grows, and a query whose labels avoid the forgotten ones keeps its evidence. -/
noncomputable def scopedRetractionLayer :
    RetractionLayer (ScopedTrackedWhichState σ n m) (Finset (Fin m)) (GroundAtom σ)
      (Which (Fin n)) (Fin m) :=
  { scopedSupportClosedLayer with
    forget_le := fun S W q => scopedTrackedEvidence_mono (Multiset.filter_le _ _)
    extract_forget_of_disjoint := by
      intro S W q avoids
      exact scopedTrackedEvidence_congr (Multiset.filter_eq_self.mpr fun chunk hchunk inS =>
        Finset.disjoint_left.mp avoids (mem_scopedTrackedScopeSupport.mpr ⟨chunk, hchunk, rfl⟩) inS) }

/-- The clean-base theorem of the scope-labelled state is the interface law. -/
theorem forgetScopedByScope_exactInverse_eq_interface {S : Finset (Fin m)}
    (W Δ : ScopedTrackedWhichState σ n m) (hclean : ScopeClean W S) (hsupp : SupportedInScope Δ S) :
    forgetScopedByScope S (W + Δ) = W :=
  (scopedSupportClosedLayer (σ := σ) (n := n) (m := m)).exactInverse_of_clean
    (fun q s hs => by
      obtain ⟨chunk, hchunk, rfl⟩ := mem_scopedTrackedScopeSupport.mp hs
      exact hsupp q chunk hchunk)
    (fun q => Finset.disjoint_left.mpr fun s hs hsS => by
      obtain ⟨chunk, hchunk, rfl⟩ := mem_scopedTrackedScopeSupport.mp hs
      exact hclean q chunk hchunk hsS)

end Mettapedia.PLN.WorldModel.ScopedTrackedRetraction

open Mettapedia.PLN.WorldModel.ScopedTrackedRetraction in
#print axioms scopedSupportClosedLayer
open Mettapedia.PLN.WorldModel.ScopedTrackedRetraction in
#print axioms scopedRetractionLayer
open Mettapedia.PLN.WorldModel.ScopedTrackedRetraction in
#print axioms forgetScopedByScope_exactInverse_eq_interface
