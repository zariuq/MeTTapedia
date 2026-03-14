import Mettapedia.Logic.PLNProvenanceTrackedState
import Mathlib.Data.Multiset.Filter

/-!
# Scope-Labelled Tracked Provenance State

Concrete tracked provenance state with explicit scope labels.

Each query carries a multiset of pairs `(scope, chunk)`, where:
- `scope` tracks the coalition / forgetting region responsible for the chunk,
- `chunk` is the existing tracked `Which` payload.

This gives an honest non-empty-scope forgetting law:
if a revision is fully supported inside scope `S`, and the base state carries no
chunks in `S`, then forgetting `S` after revision exactly recovers the base
state.
-/

namespace Mettapedia.Logic

open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.PLNWorldModelGeneric
open Mettapedia.Logic.LP

variable {σ : LPSignature} {n m : ℕ}

/-- Scope-labelled tracked provenance state. -/
abbrev ScopedTrackedWhichState (σ : LPSignature) (n m : ℕ) :=
  GroundAtom σ → Multiset (Fin m × TrackedWhichChunk n)

noncomputable instance : EvidenceType (ScopedTrackedWhichState σ n m) where
  toAddCommMonoid := inferInstance

/-- Union of all payload witnesses at query `q`, forgetting the scope labels. -/
def scopedTrackedUnionSupport
    (W : ScopedTrackedWhichState σ n m) (q : GroundAtom σ) :
    Finset (Option (Fin n)) :=
  (W q).toFinset.biUnion Prod.snd

/-- Underlying `Which` payload support at query `q`. -/
def scopedTrackedPayloadSupport
    (W : ScopedTrackedWhichState σ n m) (q : GroundAtom σ) :
    Finset (Fin n) :=
  (scopedTrackedUnionSupport W q).biUnion fun oi =>
    match oi with
    | none => ∅
    | some i => {i}

/-- Scope-label footprint at query `q`. -/
def scopedTrackedScopeSupport
    (W : ScopedTrackedWhichState σ n m) (q : GroundAtom σ) :
    Finset (Fin m) :=
  (W q).toFinset.image Prod.fst

/-- Extract `Which` evidence by ignoring scope labels and unioning payload
chunks. -/
def scopedTrackedEvidence
    (W : ScopedTrackedWhichState σ n m) (q : GroundAtom σ) :
    Which (Fin n) :=
  let s := scopedTrackedUnionSupport W q
  if _ : s = ∅ then 0 else Which.wset (scopedTrackedPayloadSupport W q)

theorem scopedTrackedEvidence_eq_zero_iff_support_empty
    (W : ScopedTrackedWhichState σ n m) (q : GroundAtom σ) :
    scopedTrackedEvidence W q = 0 ↔ scopedTrackedUnionSupport W q = ∅ := by
  unfold scopedTrackedEvidence
  by_cases h : scopedTrackedUnionSupport W q = ∅ <;> simp [h]

theorem scopedTrackedEvidence_eq_wset_of_support_ne_empty
    (W : ScopedTrackedWhichState σ n m) (q : GroundAtom σ)
    (hs : scopedTrackedUnionSupport W q ≠ ∅) :
    scopedTrackedEvidence W q = Which.wset (scopedTrackedPayloadSupport W q) := by
  unfold scopedTrackedEvidence
  simp [hs]

theorem scopedTrackedUnionSupport_add
    (W₁ W₂ : ScopedTrackedWhichState σ n m) (q : GroundAtom σ) :
    scopedTrackedUnionSupport (W₁ + W₂) q =
      scopedTrackedUnionSupport W₁ q ∪ scopedTrackedUnionSupport W₂ q := by
  ext i
  simp [scopedTrackedUnionSupport, Finset.mem_biUnion, Multiset.mem_toFinset]
  constructor
  · intro h
    rcases h with ⟨a, b, hab, hi⟩
    rcases hab with hab | hab
    · exact Or.inl ⟨a, b, hab, hi⟩
    · exact Or.inr ⟨a, b, hab, hi⟩
  · intro h
    rcases h with h | h
    · rcases h with ⟨a, b, hab, hi⟩
      exact ⟨a, b, Or.inl hab, hi⟩
    · rcases h with ⟨a, b, hab, hi⟩
      exact ⟨a, b, Or.inr hab, hi⟩

theorem scopedTrackedPayloadSupport_add
    (W₁ W₂ : ScopedTrackedWhichState σ n m) (q : GroundAtom σ) :
    scopedTrackedPayloadSupport (W₁ + W₂) q =
      scopedTrackedPayloadSupport W₁ q ∪ scopedTrackedPayloadSupport W₂ q := by
  ext i
  simp [scopedTrackedPayloadSupport, scopedTrackedUnionSupport_add, Finset.mem_biUnion]
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

theorem scopedTrackedScopeSupport_add
    (W₁ W₂ : ScopedTrackedWhichState σ n m) (q : GroundAtom σ) :
    scopedTrackedScopeSupport (W₁ + W₂) q =
      scopedTrackedScopeSupport W₁ q ∪ scopedTrackedScopeSupport W₂ q := by
  ext s
  simp [scopedTrackedScopeSupport, Multiset.mem_toFinset]
  constructor
  · intro h
    rcases h with ⟨x, hx⟩
    rcases hx with hx | hx
    · exact Or.inl ⟨x, hx⟩
    · exact Or.inr ⟨x, hx⟩
  · intro h
    rcases h with h | h
    · rcases h with ⟨x, hx⟩
      exact ⟨x, Or.inl hx⟩
    · rcases h with ⟨x, hx⟩
      exact ⟨x, Or.inr hx⟩

theorem scopedTrackedPayloadSupport_eq_empty_of_union_empty
    (W : ScopedTrackedWhichState σ n m) (q : GroundAtom σ)
    (h : scopedTrackedUnionSupport W q = ∅) :
    scopedTrackedPayloadSupport W q = ∅ := by
  ext i
  simp [scopedTrackedPayloadSupport, h]

noncomputable instance : GenericWorldModel
    (ScopedTrackedWhichState σ n m) (GroundAtom σ) (Which (Fin n)) where
  evidence := scopedTrackedEvidence
  evidence_add := by
    intro W₁ W₂ q
    by_cases h₁ : scopedTrackedUnionSupport W₁ q = ∅
    · by_cases h₂ : scopedTrackedUnionSupport W₂ q = ∅
      · simp [scopedTrackedEvidence, scopedTrackedUnionSupport_add, h₁, h₂]
      · rw [scopedTrackedEvidence_eq_wset_of_support_ne_empty _ _ h₂]
        have hE₁ : scopedTrackedEvidence W₁ q = 0 := by
          exact (scopedTrackedEvidence_eq_zero_iff_support_empty (W := W₁) (q := q)).2 h₁
        have hsum :
            scopedTrackedUnionSupport (W₁ + W₂) q = scopedTrackedUnionSupport W₂ q := by
          rw [scopedTrackedUnionSupport_add, h₁]
          simp
        have hsum_ne : scopedTrackedUnionSupport (W₁ + W₂) q ≠ ∅ := by
          simpa [hsum] using h₂
        rw [scopedTrackedEvidence_eq_wset_of_support_ne_empty _ _ hsum_ne, hE₁]
        have hpayload :
            scopedTrackedPayloadSupport (W₁ + W₂) q = scopedTrackedPayloadSupport W₂ q := by
          rw [scopedTrackedPayloadSupport_add,
            scopedTrackedPayloadSupport_eq_empty_of_union_empty _ _ h₁]
          simp
        simpa [(· + ·), Add.add] using congrArg Which.wset hpayload
    · by_cases h₂ : scopedTrackedUnionSupport W₂ q = ∅
      · rw [scopedTrackedEvidence_eq_wset_of_support_ne_empty _ _ h₁]
        have hE₂ : scopedTrackedEvidence W₂ q = 0 := by
          exact (scopedTrackedEvidence_eq_zero_iff_support_empty (W := W₂) (q := q)).2 h₂
        have hsum :
            scopedTrackedUnionSupport (W₁ + W₂) q = scopedTrackedUnionSupport W₁ q := by
          rw [scopedTrackedUnionSupport_add, h₂]
          simp
        have hsum_ne : scopedTrackedUnionSupport (W₁ + W₂) q ≠ ∅ := by
          simpa [hsum] using h₁
        rw [scopedTrackedEvidence_eq_wset_of_support_ne_empty _ _ hsum_ne, hE₂]
        have hpayload :
            scopedTrackedPayloadSupport (W₁ + W₂) q = scopedTrackedPayloadSupport W₁ q := by
          rw [scopedTrackedPayloadSupport_add,
            scopedTrackedPayloadSupport_eq_empty_of_union_empty _ _ h₂]
          simp
        simpa [(· + ·), Add.add] using congrArg Which.wset hpayload
      · have hsum : scopedTrackedUnionSupport (W₁ + W₂) q ≠ ∅ := by
          rw [scopedTrackedUnionSupport_add]
          simp [h₁, h₂]
        rw [scopedTrackedEvidence_eq_wset_of_support_ne_empty _ _ hsum,
          scopedTrackedEvidence_eq_wset_of_support_ne_empty _ _ h₁,
          scopedTrackedEvidence_eq_wset_of_support_ne_empty _ _ h₂,
          scopedTrackedPayloadSupport_add]
        simp [(· + ·), Add.add]

/-- Forget every chunk whose scope label lies in `S`. -/
def forgetScopedByScope
    (S : Finset (Fin m)) (W : ScopedTrackedWhichState σ n m) :
    ScopedTrackedWhichState σ n m :=
  fun q => (W q).filter fun sc => sc.1 ∉ S

/-- Every chunk of `W` lies inside scope footprint `S`. -/
def SupportedInScope
    (W : ScopedTrackedWhichState σ n m) (S : Finset (Fin m)) : Prop :=
  ∀ q chunk, chunk ∈ W q → chunk.1 ∈ S

/-- `W` carries no chunks inside scope footprint `S`. -/
def ScopeClean
    (W : ScopedTrackedWhichState σ n m) (S : Finset (Fin m)) : Prop :=
  ∀ q chunk, chunk ∈ W q → chunk.1 ∉ S

theorem forgetScopedByScope_idempotent
    (S : Finset (Fin m)) (W : ScopedTrackedWhichState σ n m) :
    forgetScopedByScope S (forgetScopedByScope S W) = forgetScopedByScope S W := by
  funext q
  ext chunk
  simp [forgetScopedByScope]

theorem forgetScopedByScope_add
    (S : Finset (Fin m))
    (W₁ W₂ : ScopedTrackedWhichState σ n m) :
    forgetScopedByScope S (W₁ + W₂) =
      forgetScopedByScope S W₁ + forgetScopedByScope S W₂ := by
  funext q
  simp [forgetScopedByScope, Multiset.filter_add]

theorem forgetScopedByScope_eq_self_of_scopeClean
    {S : Finset (Fin m)} {W : ScopedTrackedWhichState σ n m}
    (hclean : ScopeClean W S) :
    forgetScopedByScope S W = W := by
  funext q
  apply Multiset.filter_eq_self.2
  intro chunk hchunk
  exact hclean q chunk hchunk

theorem forgetScopedByScope_eq_zero_of_supportedInScope
    {S : Finset (Fin m)} {W : ScopedTrackedWhichState σ n m}
    (hsupp : SupportedInScope W S) :
    forgetScopedByScope S W = 0 := by
  funext q
  apply Multiset.filter_eq_nil.2
  intro chunk hchunk
  simpa using hsupp q chunk hchunk

theorem forgetScopedByScope_exactInverse_of_supported_of_clean
    {S : Finset (Fin m)}
    (W Δ : ScopedTrackedWhichState σ n m)
    (hclean : ScopeClean W S)
    (hsupp : SupportedInScope Δ S) :
    forgetScopedByScope S (W + Δ) = W := by
  rw [forgetScopedByScope_add,
    forgetScopedByScope_eq_self_of_scopeClean hclean,
    forgetScopedByScope_eq_zero_of_supportedInScope hsupp,
    add_zero]

theorem forgetScopedByScope_scopeSupport_subset
    {S : Finset (Fin m)} {W : ScopedTrackedWhichState σ n m}
    (hsupp : SupportedInScope W S) :
    ∀ q, scopedTrackedScopeSupport W q ⊆ S := by
  intro q s hs
  have hs' : s ∈ (W q).toFinset.image Prod.fst := by
    simpa [scopedTrackedScopeSupport] using hs
  rcases Finset.mem_image.mp hs' with ⟨chunk, hchunk, hfst⟩
  exact hfst ▸ hsupp q chunk (Multiset.mem_toFinset.mp hchunk)

/-- Embed a plain `Which` K-relation as one scope-labelled tracked chunk per
nonzero query. -/
def toScopedTrackedWhichState
    (s : Fin m) (I : KRelation σ (Which (Fin n))) :
    ScopedTrackedWhichState σ n m :=
  fun q =>
    match I q with
    | Which.wbot => 0
    | Which.wset support => {(s, insert none (Finset.image some support))}

theorem toScopedTrackedWhichState_supportedInSingleton
    (s : Fin m) (I : KRelation σ (Which (Fin n))) :
    SupportedInScope (toScopedTrackedWhichState (σ := σ) (n := n) (m := m) s I) ({s} : Finset (Fin m)) := by
  intro q chunk hchunk
  unfold toScopedTrackedWhichState at hchunk
  cases hI : I q with
  | wbot =>
      simp [hI] at hchunk
  | wset support =>
      simp [hI] at hchunk
      rcases hchunk with rfl
      simp

theorem toScopedTrackedWhichState_scopeSupport_eq_singleton_of_nonzero
    (s : Fin m) (I : KRelation σ (Which (Fin n))) (q : GroundAtom σ)
    (hne : I q ≠ 0) :
    scopedTrackedScopeSupport
      (toScopedTrackedWhichState (σ := σ) (n := n) (m := m) s I) q = {s} := by
  unfold toScopedTrackedWhichState scopedTrackedScopeSupport
  cases hI : I q with
  | wbot =>
      exfalso
      apply hne
      rw [hI]
      rfl
  | wset support =>
      simp [hI]

theorem toScopedTrackedWhichState_forget_exactInverse_of_clean
    (s : Fin m) (I : KRelation σ (Which (Fin n))) (W : ScopedTrackedWhichState σ n m)
    (hclean : ScopeClean W ({s} : Finset (Fin m))) :
    forgetScopedByScope ({s} : Finset (Fin m))
        (W + toScopedTrackedWhichState (σ := σ) (n := n) (m := m) s I) = W := by
  exact forgetScopedByScope_exactInverse_of_supported_of_clean
    W (toScopedTrackedWhichState (σ := σ) (n := n) (m := m) s I)
    hclean
    (toScopedTrackedWhichState_supportedInSingleton (σ := σ) (n := n) (m := m) s I)

end Mettapedia.Logic
