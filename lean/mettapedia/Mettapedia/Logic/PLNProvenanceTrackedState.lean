import Mettapedia.Logic.LP.Provenance
import Mettapedia.Logic.PLNWorldModelGeneric
import Mettapedia.Logic.PLNProvenanceWMSupportBridge
import Provenance.Semirings.Which
import Mathlib.Data.Multiset.AddSub
import Mathlib.Data.Finset.Lattice.Basic

/-!
# Tracked Provenance WM State

Concrete provenance-history state for `Which`-valued world-model experiments.

Each query carries a multiset of provenance chunks. BinaryEvidence unions the active
chunks, preserving the crucial `Which` distinction between:

- `wbot` via the empty multiset / empty union;
- `wset ∅` via a nonempty chunk carrying only the `none` witness;
- `wset s` via chunks carrying `some i` witnesses.

This gives an honest exact-forgetting theorem on the concrete tracked state:
subtracting a tracked revision from an additive merge removes exactly that
revision, with no approximation and no hidden sorries.
-/

namespace Mettapedia.Logic

open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.PLNWorldModelGeneric
open Mettapedia.Logic.LP

variable {σ : LPSignature} {n : ℕ}

/-- A tracked provenance chunk. `none` records nonzero empty-support evidence,
while `some i` records the ordinary provenance source `i`. -/
abbrev TrackedWhichChunk (n : ℕ) := Finset (Option (Fin n))

/-- A tracked provenance world-model state stores a multiset of chunks at each
query. -/
abbrev TrackedWhichState (σ : LPSignature) (n : ℕ) :=
  GroundAtom σ → Multiset (TrackedWhichChunk n)

noncomputable instance : EvidenceType (TrackedWhichState σ n) where
  toAddCommMonoid := inferInstance

/-- Union of all active tagged provenance witnesses at query `q`. -/
def trackedUnionSupport (W : TrackedWhichState σ n) (q : GroundAtom σ) :
    Finset (Option (Fin n)) :=
  (W q).toFinset.biUnion id

/-- Forget the `none` tag and recover the underlying `Which` support payload. -/
def trackedPayloadSupport (W : TrackedWhichState σ n) (q : GroundAtom σ) : Finset (Fin n) :=
  (trackedUnionSupport W q).biUnion fun oi =>
    match oi with
    | none => ∅
    | some i => {i}

/-- Query-local chunk support, retaining the query label so scopes can refer to
exact tracked contributions. -/
def trackedChunkSupport [DecidableEq (GroundAtom σ)]
    (W : TrackedWhichState σ n) (q : GroundAtom σ) :
    Finset (GroundAtom σ × TrackedWhichChunk n) :=
  ((W q).toFinset.image fun s => (q, s))

/-- Extract `Which` evidence from the tracked state. The empty union is mapped to
`0 = wbot`; any nonempty union yields `wset` of the payload support. -/
def trackedEvidence (W : TrackedWhichState σ n) (q : GroundAtom σ) : Which (Fin n) :=
  let s := trackedUnionSupport W q
  if _ : s = ∅ then 0 else Which.wset (trackedPayloadSupport W q)

theorem trackedEvidence_eq_zero_iff_support_empty
    (W : TrackedWhichState σ n) (q : GroundAtom σ) :
    trackedEvidence W q = 0 ↔ trackedUnionSupport W q = ∅ := by
  unfold trackedEvidence
  by_cases h : trackedUnionSupport W q = ∅ <;> simp [h]

theorem trackedEvidence_eq_wset_of_support_ne_empty
    (W : TrackedWhichState σ n) (q : GroundAtom σ)
    (hs : trackedUnionSupport W q ≠ ∅) :
    trackedEvidence W q = Which.wset (trackedPayloadSupport W q) := by
  unfold trackedEvidence
  simp [hs]

theorem trackedUnionSupport_add
    (W₁ W₂ : TrackedWhichState σ n) (q : GroundAtom σ) :
    trackedUnionSupport (W₁ + W₂) q =
      trackedUnionSupport W₁ q ∪ trackedUnionSupport W₂ q := by
  ext i
  simp [trackedUnionSupport, Finset.mem_biUnion, Multiset.mem_toFinset]
  constructor
  · intro h
    rcases h with ⟨a, ha, hi⟩
    rcases ha with ha | ha
    · exact Or.inl ⟨a, ha, hi⟩
    · exact Or.inr ⟨a, ha, hi⟩
  · intro h
    rcases h with h | h
    · rcases h with ⟨a, ha, hi⟩
      exact ⟨a, Or.inl ha, hi⟩
    · rcases h with ⟨a, ha, hi⟩
      exact ⟨a, Or.inr ha, hi⟩

theorem trackedPayloadSupport_add
    (W₁ W₂ : TrackedWhichState σ n) (q : GroundAtom σ) :
    trackedPayloadSupport (W₁ + W₂) q =
      trackedPayloadSupport W₁ q ∪ trackedPayloadSupport W₂ q := by
  ext i
  simp [trackedPayloadSupport, trackedUnionSupport_add, Finset.mem_biUnion]
  constructor
  · intro h
    rcases h with ⟨a, ha, hi⟩
    rcases ha with ha | ha
    · exact Or.inl ⟨a, ha, hi⟩
    · exact Or.inr ⟨a, ha, hi⟩
  · intro h
    rcases h with h | h
    · rcases h with ⟨a, ha, hi⟩
      exact ⟨a, Or.inl ha, hi⟩
    · rcases h with ⟨a, ha, hi⟩
      exact ⟨a, Or.inr ha, hi⟩

theorem trackedPayloadSupport_eq_empty_of_union_empty
    (W : TrackedWhichState σ n) (q : GroundAtom σ)
    (h : trackedUnionSupport W q = ∅) :
    trackedPayloadSupport W q = ∅ := by
  ext i
  simp [trackedPayloadSupport, h]

noncomputable instance : AdditiveWorldModel
    (TrackedWhichState σ n) (GroundAtom σ) (Which (Fin n)) where
  extract := trackedEvidence
  extract_add := by
    intro W₁ W₂ q
    by_cases h₁ : trackedUnionSupport W₁ q = ∅
    · by_cases h₂ : trackedUnionSupport W₂ q = ∅
      · simp [trackedEvidence, trackedUnionSupport_add, h₁, h₂]
      · rw [trackedEvidence_eq_wset_of_support_ne_empty _ _ h₂]
        have hE₁ : trackedEvidence W₁ q = 0 := by
          exact (trackedEvidence_eq_zero_iff_support_empty (W := W₁) (q := q)).2 h₁
        have hsum :
            trackedUnionSupport (W₁ + W₂) q = trackedUnionSupport W₂ q := by
          rw [trackedUnionSupport_add, h₁]
          simp
        have hsum_ne : trackedUnionSupport (W₁ + W₂) q ≠ ∅ := by
          simpa [hsum] using h₂
        rw [trackedEvidence_eq_wset_of_support_ne_empty _ _ hsum_ne, hE₁]
        have hpayload : trackedPayloadSupport (W₁ + W₂) q = trackedPayloadSupport W₂ q := by
          rw [trackedPayloadSupport_add, trackedPayloadSupport_eq_empty_of_union_empty _ _ h₁]
          simp
        simpa [(· + ·), Add.add] using congrArg Which.wset hpayload
    · by_cases h₂ : trackedUnionSupport W₂ q = ∅
      · rw [trackedEvidence_eq_wset_of_support_ne_empty _ _ h₁]
        have hE₂ : trackedEvidence W₂ q = 0 := by
          exact (trackedEvidence_eq_zero_iff_support_empty (W := W₂) (q := q)).2 h₂
        have hsum :
            trackedUnionSupport (W₁ + W₂) q = trackedUnionSupport W₁ q := by
          rw [trackedUnionSupport_add, h₂]
          simp
        have hsum_ne : trackedUnionSupport (W₁ + W₂) q ≠ ∅ := by
          simpa [hsum] using h₁
        rw [trackedEvidence_eq_wset_of_support_ne_empty _ _ hsum_ne, hE₂]
        have hpayload : trackedPayloadSupport (W₁ + W₂) q = trackedPayloadSupport W₁ q := by
          rw [trackedPayloadSupport_add, trackedPayloadSupport_eq_empty_of_union_empty _ _ h₂]
          simp
        simpa [(· + ·), Add.add] using congrArg Which.wset hpayload
      · have hsum :
          trackedUnionSupport (W₁ + W₂) q ≠ ∅ := by
          rw [trackedUnionSupport_add]
          simp [h₁, h₂]
        rw [trackedEvidence_eq_wset_of_support_ne_empty _ _ hsum,
          trackedEvidence_eq_wset_of_support_ne_empty _ _ h₁,
          trackedEvidence_eq_wset_of_support_ne_empty _ _ h₂,
          trackedPayloadSupport_add]
        simp [(· + ·), Add.add]

/-- Exact contribution-level forgetting by multiset subtraction. -/
def forgetTracked (S W : TrackedWhichState σ n) : TrackedWhichState σ n :=
  fun q => W q - S q

theorem forgetTracked_add_right
    (W Δ : TrackedWhichState σ n) :
    forgetTracked Δ (W + Δ) = W := by
  funext q
  rw [forgetTracked]
  exact Multiset.add_sub_cancel_right

/-- Embed a `Which`-valued K-relation as one tracked chunk per nonzero query. -/
def toTrackedWhichState (I : KRelation σ (Which (Fin n))) : TrackedWhichState σ n :=
  fun q =>
    match I q with
    | Which.wbot => 0
    | Which.wset s => {insert none (Finset.image some s)}

theorem toTracked_payloadSupport_eq_whichSupport
    (I : KRelation σ (Which (Fin n))) (q : GroundAtom σ) :
    trackedPayloadSupport (toTrackedWhichState I) q =
      whichSupport (σ := σ) (n := n) I q := by
  unfold toTrackedWhichState trackedPayloadSupport trackedUnionSupport whichSupport
  cases hI : I q with
  | wbot =>
      simp [hI]
  | wset s =>
      ext i
      simp [hI]

theorem toTracked_evidence_eq
    (I : KRelation σ (Which (Fin n))) (q : GroundAtom σ) :
    AdditiveWorldModel.extract
      (State := TrackedWhichState σ n) (Query := GroundAtom σ) (Ev := Which (Fin n))
      (toTrackedWhichState I) q = I q := by
  cases hI : I q with
  | wbot =>
      show trackedEvidence (toTrackedWhichState I) q = (0 : Which (Fin n))
      unfold trackedEvidence trackedUnionSupport toTrackedWhichState
      simp [hI]
  | wset s =>
      have hs : trackedUnionSupport (toTrackedWhichState I) q ≠ ∅ := by
        unfold trackedUnionSupport toTrackedWhichState
        simp [hI]
      show trackedEvidence (toTrackedWhichState I) q = Which.wset s
      rw [trackedEvidence_eq_wset_of_support_ne_empty _ _ hs]
      simp [toTracked_payloadSupport_eq_whichSupport, whichSupport, hI]

theorem toTracked_revision_preserves_add
    (I₁ I₂ : KRelation σ (Which (Fin n))) :
    ∀ q,
      AdditiveWorldModel.extract
        (State := TrackedWhichState σ n) (Query := GroundAtom σ) (Ev := Which (Fin n))
        (toTrackedWhichState (fun a => I₁ a + I₂ a)) q =
      AdditiveWorldModel.extract
        (State := TrackedWhichState σ n) (Query := GroundAtom σ) (Ev := Which (Fin n))
        (toTrackedWhichState I₁ + toTrackedWhichState I₂) q := by
  intro q
  rw [toTracked_evidence_eq, AdditiveWorldModel.extract_add',
    toTracked_evidence_eq, toTracked_evidence_eq]

theorem toTracked_forget_exactInverse
    (I : KRelation σ (Which (Fin n))) (W : TrackedWhichState σ n) :
    forgetTracked (toTrackedWhichState I) (W + toTrackedWhichState I) = W :=
  forgetTracked_add_right W (toTrackedWhichState I)

end Mettapedia.Logic
