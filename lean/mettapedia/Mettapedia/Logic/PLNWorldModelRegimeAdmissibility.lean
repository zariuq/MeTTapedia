import Mettapedia.Logic.PLNWorldModelFixpointClosure
import Mettapedia.Hyperseed.Ultrainfinitism

/-!
# WM Regime Admissibility

This module bridges Route 2 Hyperseed regimes into the WM layer.

- `availableRegionAt` supplies state-conditioned accessibility/admissibility.
- `WorldModel.queryStrength` supplies the WM-side semantic threshold.
- `thresholdValid` packages threshold transport over arbitrary query sets.

The result is a small, theorem-friendly notion of regime-sensitive admissibility
for WM queries.
-/

namespace Mettapedia.Logic.PLNWorldModelRegimeAdmissibility

open Mettapedia.Logic
open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.PLNWorldModelFixpointClosure
open Mettapedia.Hyperseed
open scoped ENNReal

variable {State Query Signal Cost : Type*}
variable [EvidenceType State] [WorldModel State Query] [Preorder Cost]

/-- WM threshold region at state `W`: the queries whose extracted strength meets
threshold `τ`. -/
def wmThresholdRegion (W : State) (τ : ℝ≥0∞) : Set Query :=
  { q | τ ≤ WorldModel.queryStrength (State := State) (Query := Query) W q }

/-- Regime-sensitive WM admissibility at one state/query. -/
def wmAdmissibleAt
    (P : StatefulPerspective State Query Signal Cost)
    (W : State) (B : Cost) (guard : Set Query) (τ : ℝ≥0∞) (q : Query) : Prop :=
  q ∈ availableRegionAt P W B guard ∧
    τ ≤ WorldModel.queryStrength (State := State) (Query := Query) W q

/-- Set of WM queries admissible at one state under both a regime filter and a
semantic threshold. -/
def wmAdmissibleRegionAt
    (P : StatefulPerspective State Query Signal Cost)
    (W : State) (B : Cost) (guard : Set Query) (τ : ℝ≥0∞) : Set Query :=
  availableRegionAt P W B guard ∩ wmThresholdRegion (State := State) (Query := Query) W τ

theorem mem_wmThresholdRegion_iff
    (W : State) (τ : ℝ≥0∞) (q : Query) :
    q ∈ wmThresholdRegion (State := State) (Query := Query) W τ ↔
      τ ≤ WorldModel.queryStrength (State := State) (Query := Query) W q := by
  rfl

theorem wmAdmissibleAt_iff
    (P : StatefulPerspective State Query Signal Cost)
    (W : State) (B : Cost) (guard : Set Query) (τ : ℝ≥0∞) (q : Query) :
    wmAdmissibleAt (State := State) (Query := Query) P W B guard τ q ↔
      q ∈ availableRegionAt P W B guard ∧
        τ ≤ WorldModel.queryStrength (State := State) (Query := Query) W q := by
  rfl

theorem mem_wmAdmissibleRegionAt_iff
    (P : StatefulPerspective State Query Signal Cost)
    (W : State) (B : Cost) (guard : Set Query) (τ : ℝ≥0∞) (q : Query) :
    q ∈ wmAdmissibleRegionAt (State := State) (Query := Query) P W B guard τ ↔
      wmAdmissibleAt (State := State) (Query := Query) P W B guard τ q := by
  rfl

theorem thresholdValid_iff_subset_wmThresholdRegion
    (W : State) (τ : ℝ≥0∞) (S : Set Query) :
    thresholdValid (State := State) (Query := Query) W τ S ↔
      S ⊆ wmThresholdRegion (State := State) (Query := Query) W τ := by
  constructor
  · intro h q hq
    exact h q hq
  · intro h
    simpa [thresholdValid, wmThresholdRegion] using h

theorem wmAdmissibleRegionAt_subset_availableRegionAt
    (P : StatefulPerspective State Query Signal Cost)
    (W : State) (B : Cost) (guard : Set Query) (τ : ℝ≥0∞) :
    wmAdmissibleRegionAt (State := State) (Query := Query) P W B guard τ ⊆
      availableRegionAt P W B guard := by
  intro q hq
  exact hq.1

theorem wmAdmissibleRegionAt_subset_wmThresholdRegion
    (P : StatefulPerspective State Query Signal Cost)
    (W : State) (B : Cost) (guard : Set Query) (τ : ℝ≥0∞) :
    wmAdmissibleRegionAt (State := State) (Query := Query) P W B guard τ ⊆
      wmThresholdRegion (State := State) (Query := Query) W τ := by
  intro q hq
  exact hq.2

/-- Lower thresholds weakly enlarge the WM threshold region. -/
theorem wmThresholdRegion_mono
    (W : State) {τ₁ τ₂ : ℝ≥0∞} (hτ : τ₁ ≤ τ₂) :
    wmThresholdRegion (State := State) (Query := Query) W τ₂ ⊆
      wmThresholdRegion (State := State) (Query := Query) W τ₁ := by
  intro q hq
  exact le_trans hτ hq

theorem wmAdmissibleRegionAt_mono_budget
    (P : StatefulPerspective State Query Signal Cost)
    (W : State) {B₁ B₂ : Cost} (guard : Set Query) (τ : ℝ≥0∞)
    (hB : B₁ ≤ B₂) :
    wmAdmissibleRegionAt (State := State) (Query := Query) P W B₁ guard τ ⊆
      wmAdmissibleRegionAt (State := State) (Query := Query) P W B₂ guard τ := by
  intro q hq
  exact ⟨(availableRegionAt_mono_budget (P := P) (W := W) guard hB) hq.1, hq.2⟩

theorem wmAdmissibleRegionAt_mono_guard
    (P : StatefulPerspective State Query Signal Cost)
    (W : State) (B : Cost) {guard guard' : Set Query} (τ : ℝ≥0∞)
    (hguard : guard ⊆ guard') :
    wmAdmissibleRegionAt (State := State) (Query := Query) P W B guard τ ⊆
      wmAdmissibleRegionAt (State := State) (Query := Query) P W B guard' τ := by
  intro q hq
  exact ⟨(availableRegionAt_mono_guard (P := P) (W := W) (B := B) hguard) hq.1, hq.2⟩

theorem wmAdmissibleRegionAt_mono_threshold
    (P : StatefulPerspective State Query Signal Cost)
    (W : State) (B : Cost) (guard : Set Query) {τ₁ τ₂ : ℝ≥0∞}
    (hτ : τ₁ ≤ τ₂) :
    wmAdmissibleRegionAt (State := State) (Query := Query) P W B guard τ₂ ⊆
      wmAdmissibleRegionAt (State := State) (Query := Query) P W B guard τ₁ := by
  intro q hq
  exact ⟨hq.1, wmThresholdRegion_mono (State := State) (Query := Query) W hτ hq.2⟩

/-- If a threshold-valid set contains the whole available region, then every
available query becomes WM-admissible at that threshold. -/
theorem availableRegionAt_subset_wmAdmissibleRegionAt_of_thresholdValid
    (P : StatefulPerspective State Query Signal Cost)
    (W : State) (B : Cost) (guard S : Set Query) (τ : ℝ≥0∞)
    (hS : thresholdValid (State := State) (Query := Query) W τ S)
    (hAvail : availableRegionAt P W B guard ⊆ S) :
    availableRegionAt P W B guard ⊆
      wmAdmissibleRegionAt (State := State) (Query := Query) P W B guard τ := by
  intro q hq
  exact ⟨hq, hS q (hAvail hq)⟩

/-- Pointwise version of threshold transport into WM admissibility. -/
theorem wmAdmissibleAt_of_mem_availableRegionAt_of_thresholdValid
    (P : StatefulPerspective State Query Signal Cost)
    (W : State) (B : Cost) (guard S : Set Query) (τ : ℝ≥0∞) (q : Query)
    (hS : thresholdValid (State := State) (Query := Query) W τ S)
    (hAvail : availableRegionAt P W B guard ⊆ S)
    (hq : q ∈ availableRegionAt P W B guard) :
    wmAdmissibleAt (State := State) (Query := Query) P W B guard τ q := by
  exact ⟨hq, hS q (hAvail hq)⟩

/-- If the available region itself is threshold-valid, the WM-admissible region
collapses back to the available region. -/
theorem wmAdmissibleRegionAt_eq_availableRegionAt_of_thresholdValid
    (P : StatefulPerspective State Query Signal Cost)
    (W : State) (B : Cost) (guard : Set Query) (τ : ℝ≥0∞)
    (hAvail :
      thresholdValid (State := State) (Query := Query) W τ (availableRegionAt P W B guard)) :
    wmAdmissibleRegionAt (State := State) (Query := Query) P W B guard τ =
      availableRegionAt P W B guard := by
  apply Set.Subset.antisymm
  · exact wmAdmissibleRegionAt_subset_availableRegionAt (State := State) (Query := Query) P W B guard τ
  · exact
      availableRegionAt_subset_wmAdmissibleRegionAt_of_thresholdValid
        (State := State) (Query := Query) P W B guard (availableRegionAt P W B guard) τ hAvail
        Set.Subset.rfl

end Mettapedia.Logic.PLNWorldModelRegimeAdmissibility
