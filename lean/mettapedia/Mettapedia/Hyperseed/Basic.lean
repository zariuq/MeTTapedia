import Mettapedia.Logic.SufficientStatisticSurface
import Mettapedia.Logic.PLNWorldModelFixpointCascade
import Mettapedia.Logic.PLNWorldModelFixpointClosure
import Mettapedia.Hyperseed.Ultrainfinitism

/-!
# Hyperseed Basic

Hyperseed is a thin exploration and observation-ingestion layer above the
existing WM foundations. This file carries two compatible surfaces:

- a generic `HyperseedKernel` / trace-fold interface for external agents,
- trace-seeded closure helpers over sufficient-statistics world models.

It does not introduce a new semantics stack; it packages existing WM closure
machinery into forms that are convenient for OpenClaw-style observation flows.
-/

namespace Mettapedia.Hyperseed

open Mettapedia.Logic
open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.PLNWorldModelAdditive
open Mettapedia.Logic.PLNWorldModelFixpointClosure
open Mettapedia.Logic.PLNWorldModelFixpointCascade
open Mettapedia.Logic.SufficientStatisticSurface

/-! ## Observation envelope -/

/-- An observation tagged with source and timestamp metadata.
Generic over payload, source identifier, and time representation. -/
structure ObservationEnvelope (Obs Source Time : Type*) where
  source : Source
  time : Time
  payload : Obs

/-! ## Hyperseed kernel -/

/-- The Hyperseed exploration kernel: packages an ingestion function, a seed
query set, and a consequence rule pool over an existing WM state/query space.

- `ingest` folds a single observation into the WM state.
- `seedQueries` are the initial query obligations for closure.
- `rules` is the consequence rule pool.
-/
structure HyperseedKernel (Obs State Query : Type*)
    [EvidenceType State] [WorldModel State Query] where
  ingest : Obs → State → State
  seedQueries : Set Query
  rules : RuleSet State Query

variable {Obs Query : Type*}
variable {Signal Cost : Type*} [Preorder Cost]

/-- Queries directly suggested by an observation trace. -/
def traceSeed (frontier : Obs → Set Query) (σ : Multiset Obs) : Set Query :=
  { q | ∃ o, o ∈ σ ∧ q ∈ frontier o }

@[simp] theorem mem_traceSeed
    (frontier : Obs → Set Query) (σ : Multiset Obs) (q : Query) :
    q ∈ traceSeed frontier σ ↔ ∃ o, o ∈ σ ∧ q ∈ frontier o :=
  Iff.rfl

@[simp] theorem traceSeed_zero
    (frontier : Obs → Set Query) :
    traceSeed frontier (0 : Multiset Obs) = (∅ : Set Query) := by
  ext q
  simp [traceSeed]

@[simp] theorem traceSeed_singleton
    (frontier : Obs → Set Query) (o : Obs) (q : Query) :
    q ∈ traceSeed frontier ({o} : Multiset Obs) ↔ q ∈ frontier o := by
  simp [traceSeed]

/-- Rule pool for Hyperseed over the binary WM induced by a sufficient-statistics
surface. -/
abbrev RulePool
    (S : SufficientStatisticSurface Obs Query Evidence) :=
  letI : EvidenceType (Multiset Obs) := multisetEvidenceType Obs
  letI : WorldModel (Multiset Obs) Query := worldModelOfAtomicEvidence S.observe
  RuleSet (Multiset Obs) Query

/-- Hyperseed closure: observation-trace seeding plus WM fixpoint closure on the
binary evidence world model induced by a sufficient-statistics surface. -/
noncomputable def closureFromTrace
    (S : SufficientStatisticSurface Obs Query Evidence)
    (frontier : Obs → Set Query)
    (R : RulePool S)
    (σ : Multiset Obs) : Set Query :=
  letI : EvidenceType (Multiset Obs) := multisetEvidenceType Obs
  letI : WorldModel (Multiset Obs) Query := worldModelOfAtomicEvidence S.observe
  leastRuleClosure R σ (traceSeed frontier σ)

/-- Fair synchronous Hyperseed cascade from an observation trace. -/
def cascadeFromTrace
    (S : SufficientStatisticSurface Obs Query Evidence)
    (frontier : Obs → Set Query)
    (R : RulePool S)
    (σ : Multiset Obs) : ℕ → Set Query :=
  letI : EvidenceType (Multiset Obs) := multisetEvidenceType Obs
  letI : WorldModel (Multiset Obs) Query := worldModelOfAtomicEvidence S.observe
  immediateIter R σ (traceSeed frontier σ)

theorem seed_subset_closureFromTrace
    (S : SufficientStatisticSurface Obs Query Evidence)
    (frontier : Obs → Set Query)
    (R : RulePool S)
    (σ : Multiset Obs) :
    traceSeed frontier σ ⊆ closureFromTrace S frontier R σ := by
  letI : EvidenceType (Multiset Obs) := multisetEvidenceType Obs
  letI : WorldModel (Multiset Obs) Query := worldModelOfAtomicEvidence S.observe
  exact seed_subset_leastRuleClosure (R := R) (W := σ) (seed := traceSeed frontier σ)

theorem mem_closureFromTrace_iff_mem_cascade_card_of_finite
    [Fintype Query]
    (S : SufficientStatisticSurface Obs Query Evidence)
    (frontier : Obs → Set Query)
    (R : RulePool S)
    (σ : Multiset Obs) (q : Query) :
    q ∈ closureFromTrace S frontier R σ ↔
      q ∈ cascadeFromTrace S frontier R σ (Fintype.card Query) := by
  letI : EvidenceType (Multiset Obs) := multisetEvidenceType Obs
  letI : WorldModel (Multiset Obs) Query := worldModelOfAtomicEvidence S.observe
  exact
    mem_leastRuleClosure_iff_mem_immediateIter_card_of_finite
      (R := R) (W := σ) (seed := traceSeed frontier σ) q

theorem mem_closureFromTrace_implies_eventualDiscovery_of_finite
    [Fintype Query]
    (S : SufficientStatisticSurface Obs Query Evidence)
    (frontier : Obs → Set Query)
    (R : RulePool S)
    (σ : Multiset Obs)
    {q : Query}
    (hq : q ∈ closureFromTrace S frontier R σ) :
    ∃ N ≤ Fintype.card Query, q ∈ cascadeFromTrace S frontier R σ N := by
  letI : EvidenceType (Multiset Obs) := multisetEvidenceType Obs
  letI : WorldModel (Multiset Obs) Query := worldModelOfAtomicEvidence S.observe
  exact
    mem_leastRuleClosure_implies_eventual_discovery_of_finite
      (R := R) (W := σ) (seed := traceSeed frontier σ) hq

/-- Perspective-filtered Hyperseed closure. This keeps the existing closure
engine but exposes the observer-relative/bounded slice visible from one
perspective. -/
def availableClosureFromTrace
    (S : SufficientStatisticSurface Obs Query Evidence)
    (frontier : Obs → Set Query)
    (R : RulePool S)
    (σ : Multiset Obs)
    (P : Perspective Query Signal Cost)
    (B : Cost)
    (guard : Set Query) : Set Query :=
  closureFromTrace S frontier R σ ∩ availableRegion P B guard

/-- Perspective-filtered Hyperseed cascade. -/
def availableCascadeFromTrace
    (S : SufficientStatisticSurface Obs Query Evidence)
    (frontier : Obs → Set Query)
    (R : RulePool S)
    (σ : Multiset Obs)
    (P : Perspective Query Signal Cost)
    (B : Cost)
    (guard : Set Query) : ℕ → Set Query :=
  fun n => cascadeFromTrace S frontier R σ n ∩ availableRegion P B guard

/-- State-conditioned available closure: the admissible region itself may vary
with the current trace/state. This is the minimal Route 2 bridge from Hyperseed
into a regime-indexed WM semantics. -/
def stateAvailableClosureFromTrace
    (S : SufficientStatisticSurface Obs Query Evidence)
    (frontier : Obs → Set Query)
    (R : RulePool S)
    (σ : Multiset Obs)
    (P : StatefulPerspective (Multiset Obs) Query Signal Cost)
    (B : Cost)
    (guard : Set Query) : Set Query :=
  closureFromTrace S frontier R σ ∩ availableRegionAt P σ B guard

/-- State-conditioned available cascade. -/
def stateAvailableCascadeFromTrace
    (S : SufficientStatisticSurface Obs Query Evidence)
    (frontier : Obs → Set Query)
    (R : RulePool S)
    (σ : Multiset Obs)
    (P : StatefulPerspective (Multiset Obs) Query Signal Cost)
    (B : Cost)
    (guard : Set Query) : ℕ → Set Query :=
  fun n => cascadeFromTrace S frontier R σ n ∩ availableRegionAt P σ B guard

/-- Stage-filtered Hyperseed closure. -/
def stagedClosureFromTrace
    {Idx : Type*} [Preorder Idx]
    (S : SufficientStatisticSurface Obs Query Evidence)
    (frontier : Obs → Set Query)
    (R : RulePool S)
    (σ : Multiset Obs)
    (F : StagedView (World := Query) Idx)
    (i : Idx) : Set Query :=
  closureFromTrace S frontier R σ ∩ F.region i

/-- Stage-filtered Hyperseed cascade. -/
def stagedCascadeFromTrace
    {Idx : Type*} [Preorder Idx]
    (S : SufficientStatisticSurface Obs Query Evidence)
    (frontier : Obs → Set Query)
    (R : RulePool S)
    (σ : Multiset Obs)
    (F : StagedView (World := Query) Idx)
    (i : Idx) : ℕ → Set Query :=
  fun n => cascadeFromTrace S frontier R σ n ∩ F.region i

theorem mem_availableClosureFromTrace_iff
    (S : SufficientStatisticSurface Obs Query Evidence)
    (frontier : Obs → Set Query)
    (R : RulePool S)
    (σ : Multiset Obs)
    (P : Perspective Query Signal Cost)
    (B : Cost)
    (guard : Set Query)
    (q : Query) :
    q ∈ availableClosureFromTrace S frontier R σ P B guard ↔
      q ∈ closureFromTrace S frontier R σ ∧ q ∈ availableRegion P B guard := by
  rfl

theorem mem_stagedClosureFromTrace_iff
    {Idx : Type*} [Preorder Idx]
    (S : SufficientStatisticSurface Obs Query Evidence)
    (frontier : Obs → Set Query)
    (R : RulePool S)
    (σ : Multiset Obs)
    (F : StagedView (World := Query) Idx)
    (i : Idx)
    (q : Query) :
    q ∈ stagedClosureFromTrace S frontier R σ F i ↔
      q ∈ closureFromTrace S frontier R σ ∧ q ∈ F.region i := by
  rfl

theorem mem_stateAvailableClosureFromTrace_iff
    (S : SufficientStatisticSurface Obs Query Evidence)
    (frontier : Obs → Set Query)
    (R : RulePool S)
    (σ : Multiset Obs)
    (P : StatefulPerspective (Multiset Obs) Query Signal Cost)
    (B : Cost)
    (guard : Set Query)
    (q : Query) :
    q ∈ stateAvailableClosureFromTrace S frontier R σ P B guard ↔
      q ∈ closureFromTrace S frontier R σ ∧ q ∈ availableRegionAt P σ B guard := by
  rfl

theorem availableClosureFromTrace_subset_closureFromTrace
    (S : SufficientStatisticSurface Obs Query Evidence)
    (frontier : Obs → Set Query)
    (R : RulePool S)
    (σ : Multiset Obs)
    (P : Perspective Query Signal Cost)
    (B : Cost)
    (guard : Set Query) :
    availableClosureFromTrace S frontier R σ P B guard ⊆
      closureFromTrace S frontier R σ := by
  intro q hq
  exact hq.1

theorem availableClosureFromTrace_subset_availableRegion
    (S : SufficientStatisticSurface Obs Query Evidence)
    (frontier : Obs → Set Query)
    (R : RulePool S)
    (σ : Multiset Obs)
    (P : Perspective Query Signal Cost)
    (B : Cost)
    (guard : Set Query) :
    availableClosureFromTrace S frontier R σ P B guard ⊆
      availableRegion P B guard := by
  intro q hq
  exact hq.2

theorem availableCascadeFromTrace_subset_cascadeFromTrace
    (S : SufficientStatisticSurface Obs Query Evidence)
    (frontier : Obs → Set Query)
    (R : RulePool S)
    (σ : Multiset Obs)
    (P : Perspective Query Signal Cost)
    (B : Cost)
    (guard : Set Query)
    (n : ℕ) :
    availableCascadeFromTrace S frontier R σ P B guard n ⊆
      cascadeFromTrace S frontier R σ n := by
  intro q hq
  exact hq.1

theorem availableCascadeFromTrace_subset_availableRegion
    (S : SufficientStatisticSurface Obs Query Evidence)
    (frontier : Obs → Set Query)
    (R : RulePool S)
    (σ : Multiset Obs)
    (P : Perspective Query Signal Cost)
    (B : Cost)
    (guard : Set Query)
    (n : ℕ) :
    availableCascadeFromTrace S frontier R σ P B guard n ⊆
      availableRegion P B guard := by
  intro q hq
  exact hq.2

theorem stateAvailableClosureFromTrace_subset_closureFromTrace
    (S : SufficientStatisticSurface Obs Query Evidence)
    (frontier : Obs → Set Query)
    (R : RulePool S)
    (σ : Multiset Obs)
    (P : StatefulPerspective (Multiset Obs) Query Signal Cost)
    (B : Cost)
    (guard : Set Query) :
    stateAvailableClosureFromTrace S frontier R σ P B guard ⊆
      closureFromTrace S frontier R σ := by
  intro q hq
  exact hq.1

theorem stateAvailableClosureFromTrace_subset_availableRegionAt
    (S : SufficientStatisticSurface Obs Query Evidence)
    (frontier : Obs → Set Query)
    (R : RulePool S)
    (σ : Multiset Obs)
    (P : StatefulPerspective (Multiset Obs) Query Signal Cost)
    (B : Cost)
    (guard : Set Query) :
    stateAvailableClosureFromTrace S frontier R σ P B guard ⊆
      availableRegionAt P σ B guard := by
  intro q hq
  exact hq.2

theorem stateAvailableCascadeFromTrace_subset_cascadeFromTrace
    (S : SufficientStatisticSurface Obs Query Evidence)
    (frontier : Obs → Set Query)
    (R : RulePool S)
    (σ : Multiset Obs)
    (P : StatefulPerspective (Multiset Obs) Query Signal Cost)
    (B : Cost)
    (guard : Set Query)
    (n : ℕ) :
    stateAvailableCascadeFromTrace S frontier R σ P B guard n ⊆
      cascadeFromTrace S frontier R σ n := by
  intro q hq
  exact hq.1

theorem stateAvailableCascadeFromTrace_subset_availableRegionAt
    (S : SufficientStatisticSurface Obs Query Evidence)
    (frontier : Obs → Set Query)
    (R : RulePool S)
    (σ : Multiset Obs)
    (P : StatefulPerspective (Multiset Obs) Query Signal Cost)
    (B : Cost)
    (guard : Set Query)
    (n : ℕ) :
    stateAvailableCascadeFromTrace S frontier R σ P B guard n ⊆
      availableRegionAt P σ B guard := by
  intro q hq
  exact hq.2

theorem stagedClosureFromTrace_subset_closureFromTrace
    {Idx : Type*} [Preorder Idx]
    (S : SufficientStatisticSurface Obs Query Evidence)
    (frontier : Obs → Set Query)
    (R : RulePool S)
    (σ : Multiset Obs)
    (F : StagedView (World := Query) Idx)
    (i : Idx) :
    stagedClosureFromTrace S frontier R σ F i ⊆ closureFromTrace S frontier R σ := by
  intro q hq
  exact hq.1

theorem stagedClosureFromTrace_subset_region
    {Idx : Type*} [Preorder Idx]
    (S : SufficientStatisticSurface Obs Query Evidence)
    (frontier : Obs → Set Query)
    (R : RulePool S)
    (σ : Multiset Obs)
    (F : StagedView (World := Query) Idx)
    (i : Idx) :
    stagedClosureFromTrace S frontier R σ F i ⊆ F.region i := by
  intro q hq
  exact hq.2

theorem stagedCascadeFromTrace_subset_cascadeFromTrace
    {Idx : Type*} [Preorder Idx]
    (S : SufficientStatisticSurface Obs Query Evidence)
    (frontier : Obs → Set Query)
    (R : RulePool S)
    (σ : Multiset Obs)
    (F : StagedView (World := Query) Idx)
    (i : Idx)
    (n : ℕ) :
    stagedCascadeFromTrace S frontier R σ F i n ⊆ cascadeFromTrace S frontier R σ n := by
  intro q hq
  exact hq.1

theorem stagedCascadeFromTrace_subset_region
    {Idx : Type*} [Preorder Idx]
    (S : SufficientStatisticSurface Obs Query Evidence)
    (frontier : Obs → Set Query)
    (R : RulePool S)
    (σ : Multiset Obs)
    (F : StagedView (World := Query) Idx)
    (i : Idx)
    (n : ℕ) :
    stagedCascadeFromTrace S frontier R σ F i n ⊆ F.region i := by
  intro q hq
  exact hq.2

theorem availableClosureFromTrace_mono_budget
    (S : SufficientStatisticSurface Obs Query Evidence)
    (frontier : Obs → Set Query)
    (R : RulePool S)
    (σ : Multiset Obs)
    (P : Perspective Query Signal Cost)
    {B₁ B₂ : Cost}
    (guard : Set Query)
    (hB : B₁ ≤ B₂) :
    availableClosureFromTrace S frontier R σ P B₁ guard ⊆
      availableClosureFromTrace S frontier R σ P B₂ guard := by
  intro q hq
  exact ⟨hq.1, (availableRegion_mono_budget (P := P) (guard := guard) hB) hq.2⟩

theorem availableCascadeFromTrace_mono_budget
    (S : SufficientStatisticSurface Obs Query Evidence)
    (frontier : Obs → Set Query)
    (R : RulePool S)
    (σ : Multiset Obs)
    (P : Perspective Query Signal Cost)
    {B₁ B₂ : Cost}
    (guard : Set Query)
    (hB : B₁ ≤ B₂)
    (n : ℕ) :
    availableCascadeFromTrace S frontier R σ P B₁ guard n ⊆
      availableCascadeFromTrace S frontier R σ P B₂ guard n := by
  intro q hq
  exact ⟨hq.1, (availableRegion_mono_budget (P := P) (guard := guard) hB) hq.2⟩

theorem availableClosureFromTrace_mono_guard
    (S : SufficientStatisticSurface Obs Query Evidence)
    (frontier : Obs → Set Query)
    (R : RulePool S)
    (σ : Multiset Obs)
    (P : Perspective Query Signal Cost)
    (B : Cost)
    {guard guard' : Set Query}
    (hguard : guard ⊆ guard') :
    availableClosureFromTrace S frontier R σ P B guard ⊆
      availableClosureFromTrace S frontier R σ P B guard' := by
  intro q hq
  exact ⟨hq.1, (availableRegion_mono_guard (P := P) (B := B) hguard) hq.2⟩

theorem availableCascadeFromTrace_mono_guard
    (S : SufficientStatisticSurface Obs Query Evidence)
    (frontier : Obs → Set Query)
    (R : RulePool S)
    (σ : Multiset Obs)
    (P : Perspective Query Signal Cost)
    (B : Cost)
    {guard guard' : Set Query}
    (hguard : guard ⊆ guard')
    (n : ℕ) :
    availableCascadeFromTrace S frontier R σ P B guard n ⊆
      availableCascadeFromTrace S frontier R σ P B guard' n := by
  intro q hq
  exact ⟨hq.1, (availableRegion_mono_guard (P := P) (B := B) hguard) hq.2⟩

theorem stateAvailableClosureFromTrace_mono_budget
    (S : SufficientStatisticSurface Obs Query Evidence)
    (frontier : Obs → Set Query)
    (R : RulePool S)
    (σ : Multiset Obs)
    (P : StatefulPerspective (Multiset Obs) Query Signal Cost)
    {B₁ B₂ : Cost}
    (guard : Set Query)
    (hB : B₁ ≤ B₂) :
    stateAvailableClosureFromTrace S frontier R σ P B₁ guard ⊆
      stateAvailableClosureFromTrace S frontier R σ P B₂ guard := by
  intro q hq
  exact ⟨hq.1, (availableRegionAt_mono_budget (P := P) (W := σ) guard hB) hq.2⟩

theorem stateAvailableCascadeFromTrace_mono_budget
    (S : SufficientStatisticSurface Obs Query Evidence)
    (frontier : Obs → Set Query)
    (R : RulePool S)
    (σ : Multiset Obs)
    (P : StatefulPerspective (Multiset Obs) Query Signal Cost)
    {B₁ B₂ : Cost}
    (guard : Set Query)
    (hB : B₁ ≤ B₂)
    (n : ℕ) :
    stateAvailableCascadeFromTrace S frontier R σ P B₁ guard n ⊆
      stateAvailableCascadeFromTrace S frontier R σ P B₂ guard n := by
  intro q hq
  exact ⟨hq.1, (availableRegionAt_mono_budget (P := P) (W := σ) guard hB) hq.2⟩

theorem stateAvailableClosureFromTrace_mono_guard
    (S : SufficientStatisticSurface Obs Query Evidence)
    (frontier : Obs → Set Query)
    (R : RulePool S)
    (σ : Multiset Obs)
    (P : StatefulPerspective (Multiset Obs) Query Signal Cost)
    (B : Cost)
    {guard guard' : Set Query}
    (hguard : guard ⊆ guard') :
    stateAvailableClosureFromTrace S frontier R σ P B guard ⊆
      stateAvailableClosureFromTrace S frontier R σ P B guard' := by
  intro q hq
  exact ⟨hq.1, (availableRegionAt_mono_guard (P := P) (W := σ) (B := B) hguard) hq.2⟩

theorem stateAvailableCascadeFromTrace_mono_guard
    (S : SufficientStatisticSurface Obs Query Evidence)
    (frontier : Obs → Set Query)
    (R : RulePool S)
    (σ : Multiset Obs)
    (P : StatefulPerspective (Multiset Obs) Query Signal Cost)
    (B : Cost)
    {guard guard' : Set Query}
    (hguard : guard ⊆ guard')
    (n : ℕ) :
    stateAvailableCascadeFromTrace S frontier R σ P B guard n ⊆
      stateAvailableCascadeFromTrace S frontier R σ P B guard' n := by
  intro q hq
  exact ⟨hq.1, (availableRegionAt_mono_guard (P := P) (W := σ) (B := B) hguard) hq.2⟩

theorem stagedClosureFromTrace_mono
    {Idx : Type*} [Preorder Idx]
    (S : SufficientStatisticSurface Obs Query Evidence)
    (frontier : Obs → Set Query)
    (R : RulePool S)
    (σ : Multiset Obs)
    (F : StagedView (World := Query) Idx)
    {i j : Idx}
    (hij : i ≤ j) :
    stagedClosureFromTrace S frontier R σ F i ⊆
      stagedClosureFromTrace S frontier R σ F j := by
  intro q hq
  exact ⟨hq.1, (StagedView.region_mono F hij) hq.2⟩

theorem stagedCascadeFromTrace_mono
    {Idx : Type*} [Preorder Idx]
    (S : SufficientStatisticSurface Obs Query Evidence)
    (frontier : Obs → Set Query)
    (R : RulePool S)
    (σ : Multiset Obs)
    (F : StagedView (World := Query) Idx)
    {i j : Idx}
    (hij : i ≤ j)
    (n : ℕ) :
    stagedCascadeFromTrace S frontier R σ F i n ⊆
      stagedCascadeFromTrace S frontier R σ F j n := by
  intro q hq
  exact ⟨hq.1, (StagedView.region_mono F hij) hq.2⟩

theorem closureFromTrace_eq_availableClosureFromTrace_of_subset_availableRegion
    (S : SufficientStatisticSurface Obs Query Evidence)
    (frontier : Obs → Set Query)
    (R : RulePool S)
    (σ : Multiset Obs)
    (P : Perspective Query Signal Cost)
    (B : Cost)
    (guard : Set Query)
    (hClosure : closureFromTrace S frontier R σ ⊆ availableRegion P B guard) :
    closureFromTrace S frontier R σ =
      availableClosureFromTrace S frontier R σ P B guard := by
  apply Set.Subset.antisymm
  · intro q hq
    exact ⟨hq, hClosure hq⟩
  · exact availableClosureFromTrace_subset_closureFromTrace S frontier R σ P B guard

theorem cascadeFromTrace_eq_availableCascadeFromTrace_of_subset_availableRegion
    (S : SufficientStatisticSurface Obs Query Evidence)
    (frontier : Obs → Set Query)
    (R : RulePool S)
    (σ : Multiset Obs)
    (P : Perspective Query Signal Cost)
    (B : Cost)
    (guard : Set Query)
    (n : ℕ)
    (hCascade : cascadeFromTrace S frontier R σ n ⊆ availableRegion P B guard) :
    cascadeFromTrace S frontier R σ n =
      availableCascadeFromTrace S frontier R σ P B guard n := by
  apply Set.Subset.antisymm
  · intro q hq
    exact ⟨hq, hCascade hq⟩
  · exact availableCascadeFromTrace_subset_cascadeFromTrace S frontier R σ P B guard n

theorem stateAvailableClosureFromTrace_eq_availableClosureFromTrace_freezePerspective
    (S : SufficientStatisticSurface Obs Query Evidence)
    (frontier : Obs → Set Query)
    (R : RulePool S)
    (σ : Multiset Obs)
    (P : StatefulPerspective (Multiset Obs) Query Signal Cost)
    (B : Cost)
    (guard : Set Query) :
    stateAvailableClosureFromTrace S frontier R σ P B guard =
      availableClosureFromTrace S frontier R σ (freezePerspective P σ) B guard := by
  rfl

theorem stateAvailableCascadeFromTrace_eq_availableCascadeFromTrace_freezePerspective
    (S : SufficientStatisticSurface Obs Query Evidence)
    (frontier : Obs → Set Query)
    (R : RulePool S)
    (σ : Multiset Obs)
    (P : StatefulPerspective (Multiset Obs) Query Signal Cost)
    (B : Cost)
    (guard : Set Query)
    (n : ℕ) :
    stateAvailableCascadeFromTrace S frontier R σ P B guard n =
      availableCascadeFromTrace S frontier R σ (freezePerspective P σ) B guard n := by
  rfl

theorem closureFromTrace_eq_stateAvailableClosureFromTrace_of_subset_availableRegionAt
    (S : SufficientStatisticSurface Obs Query Evidence)
    (frontier : Obs → Set Query)
    (R : RulePool S)
    (σ : Multiset Obs)
    (P : StatefulPerspective (Multiset Obs) Query Signal Cost)
    (B : Cost)
    (guard : Set Query)
    (hClosure : closureFromTrace S frontier R σ ⊆ availableRegionAt P σ B guard) :
    closureFromTrace S frontier R σ =
      stateAvailableClosureFromTrace S frontier R σ P B guard := by
  apply Set.Subset.antisymm
  · intro q hq
    exact ⟨hq, hClosure hq⟩
  · exact stateAvailableClosureFromTrace_subset_closureFromTrace S frontier R σ P B guard

theorem cascadeFromTrace_eq_stateAvailableCascadeFromTrace_of_subset_availableRegionAt
    (S : SufficientStatisticSurface Obs Query Evidence)
    (frontier : Obs → Set Query)
    (R : RulePool S)
    (σ : Multiset Obs)
    (P : StatefulPerspective (Multiset Obs) Query Signal Cost)
    (B : Cost)
    (guard : Set Query)
    (n : ℕ)
    (hCascade : cascadeFromTrace S frontier R σ n ⊆ availableRegionAt P σ B guard) :
    cascadeFromTrace S frontier R σ n =
      stateAvailableCascadeFromTrace S frontier R σ P B guard n := by
  apply Set.Subset.antisymm
  · intro q hq
    exact ⟨hq, hCascade hq⟩
  · exact stateAvailableCascadeFromTrace_subset_cascadeFromTrace S frontier R σ P B guard n

theorem closureFromTrace_eq_stagedClosureFromTrace_of_subset_region
    {Idx : Type*} [Preorder Idx]
    (S : SufficientStatisticSurface Obs Query Evidence)
    (frontier : Obs → Set Query)
    (R : RulePool S)
    (σ : Multiset Obs)
    (F : StagedView (World := Query) Idx)
    (i : Idx)
    (hClosure : closureFromTrace S frontier R σ ⊆ F.region i) :
    closureFromTrace S frontier R σ =
      stagedClosureFromTrace S frontier R σ F i := by
  apply Set.Subset.antisymm
  · intro q hq
    exact ⟨hq, hClosure hq⟩
  · exact stagedClosureFromTrace_subset_closureFromTrace S frontier R σ F i

theorem cascadeFromTrace_eq_stagedCascadeFromTrace_of_subset_region
    {Idx : Type*} [Preorder Idx]
    (S : SufficientStatisticSurface Obs Query Evidence)
    (frontier : Obs → Set Query)
    (R : RulePool S)
    (σ : Multiset Obs)
    (F : StagedView (World := Query) Idx)
    (i : Idx)
    (n : ℕ)
    (hCascade : cascadeFromTrace S frontier R σ n ⊆ F.region i) :
    cascadeFromTrace S frontier R σ n =
      stagedCascadeFromTrace S frontier R σ F i n := by
  apply Set.Subset.antisymm
  · intro q hq
    exact ⟨hq, hCascade hq⟩
  · exact stagedCascadeFromTrace_subset_cascadeFromTrace S frontier R σ F i n

theorem mem_availableClosureFromTrace_iff_mem_availableCascade_card_of_finite
    [Fintype Query]
    (S : SufficientStatisticSurface Obs Query Evidence)
    (frontier : Obs → Set Query)
    (R : RulePool S)
    (σ : Multiset Obs)
    (P : Perspective Query Signal Cost)
    (B : Cost)
    (guard : Set Query)
    (q : Query) :
    q ∈ availableClosureFromTrace S frontier R σ P B guard ↔
      q ∈ availableCascadeFromTrace S frontier R σ P B guard (Fintype.card Query) := by
  constructor
  · intro hq
    exact
      ⟨(mem_closureFromTrace_iff_mem_cascade_card_of_finite S frontier R σ q).mp hq.1, hq.2⟩
  · intro hq
    exact
      ⟨(mem_closureFromTrace_iff_mem_cascade_card_of_finite S frontier R σ q).mpr hq.1, hq.2⟩

theorem mem_stagedClosureFromTrace_iff_mem_stagedCascade_card_of_finite
    [Fintype Query]
    {Idx : Type*} [Preorder Idx]
    (S : SufficientStatisticSurface Obs Query Evidence)
    (frontier : Obs → Set Query)
    (R : RulePool S)
    (σ : Multiset Obs)
    (F : StagedView (World := Query) Idx)
    (i : Idx)
    (q : Query) :
    q ∈ stagedClosureFromTrace S frontier R σ F i ↔
      q ∈ stagedCascadeFromTrace S frontier R σ F i (Fintype.card Query) := by
  constructor
  · intro hq
    exact
      ⟨(mem_closureFromTrace_iff_mem_cascade_card_of_finite S frontier R σ q).mp hq.1, hq.2⟩
  · intro hq
    exact
      ⟨(mem_closureFromTrace_iff_mem_cascade_card_of_finite S frontier R σ q).mpr hq.1, hq.2⟩

theorem mem_stateAvailableClosureFromTrace_iff_mem_stateAvailableCascade_card_of_finite
    [Fintype Query]
    (S : SufficientStatisticSurface Obs Query Evidence)
    (frontier : Obs → Set Query)
    (R : RulePool S)
    (σ : Multiset Obs)
    (P : StatefulPerspective (Multiset Obs) Query Signal Cost)
    (B : Cost)
    (guard : Set Query)
    (q : Query) :
    q ∈ stateAvailableClosureFromTrace S frontier R σ P B guard ↔
      q ∈ stateAvailableCascadeFromTrace S frontier R σ P B guard (Fintype.card Query) := by
  constructor
  · intro hq
    exact
      ⟨(mem_closureFromTrace_iff_mem_cascade_card_of_finite S frontier R σ q).mp hq.1, hq.2⟩
  · intro hq
    exact
      ⟨(mem_closureFromTrace_iff_mem_cascade_card_of_finite S frontier R σ q).mpr hq.1, hq.2⟩

/-- Budget-indexed available closure family for one fixed trace. -/
def availableClosureApproximationFromTrace
    (S : SufficientStatisticSurface Obs Query Evidence)
    (frontier : Obs → Set Query)
    (R : RulePool S)
    (σ : Multiset Obs)
    (P : Perspective Query Signal Cost)
    (guard : Set Query) :
    ClosureApproximation (World := Query) Cost PUnit where
  approx B _ := availableClosureFromTrace S frontier R σ P B guard
  mono := by
    intro B₁ B₂ _ hB
    exact availableClosureFromTrace_mono_budget S frontier R σ P guard hB

/-- Stage-indexed closure family for one fixed trace. -/
def stagedClosureApproximationFromTrace
    {Idx : Type*} [Preorder Idx]
    (S : SufficientStatisticSurface Obs Query Evidence)
    (frontier : Obs → Set Query)
    (R : RulePool S)
    (σ : Multiset Obs)
    (F : StagedView (World := Query) Idx) :
    ClosureApproximation (World := Query) Idx PUnit where
  approx i _ := stagedClosureFromTrace S frontier R σ F i
  mono := by
    intro i j _ hij
    exact stagedClosureFromTrace_mono S frontier R σ F hij

end Mettapedia.Hyperseed
