import Mettapedia.Logic.MarkovDeFinettiCarrierTransport
import Mettapedia.Logic.MarkovDeFinettiEvidenceBasis
import Mettapedia.Logic.MarkovDeFinettiFortiniBridgeCrux

/-! LLM primer:
- This file bridges carrier transport → SuccessorMatrixPartialExchangeable.
- Path: multi-index carrier equiv → multi-index measure equality (level-3 lifting)
  → per-row joint perm invariance → SuccessorMatrixPE
- The level-3 lifting generalizes the singleton version at Core:1034-1114.
- Pattern: infinite event = ⋃_N finite-prefix event; carrier equiv gives per-N equality;
  monotone union gives infinite equality.

# Carrier Transport → Successor-Matrix Partial Exchangeability
-/

noncomputable section

namespace Mettapedia.Logic

open MarkovExchangeability
open MarkovDeFinettiHard
open MarkovDeFinettiRecurrence
open MarkovDeFinettiCarrierTransport
open CarrierTransportBridge
open Mettapedia.Logic.UniversalPrediction
open Mettapedia.Logic.UniversalPrediction.MarkovExchangeabilityBridge
open MeasureTheory

variable {k : ℕ}

/-! ## Per-row joint perm invariance from carrier transport

This file develops per-row and one-fiber invariance infrastructure that feeds
the actual bridge target `SuccessorMatrixPE_of_markovExchangeable_strongRecurrence`.
Per-row joint perm invariance is useful supporting data, but it is not by
itself the missing cross-row theorem.

The level-3 lifting pattern here is: infinite event = ⋃_N finite-prefix event,
carrier equiv gives per-N equality, monotone union gives infinite equality.
Generalized from singleton (Core:1034-1114) to multi-index. -/

namespace PerRowJointPE

open MarkovDeFinettiHard

/-! ### Finite selection maps

These package finitely many row-successor observables into a single measurable
tuple-valued map. Constant-anchor instances recover the existing per-row
preimage equalities, while mixed-anchor instances match the tuple form of
nonempty cylinder events. -/

/-- Finite tuple-valued map collecting row-successor values from possibly
different anchor rows and visit indices. -/
def multiRowSelectionMap
    {m : ℕ} (anchor : Fin m → Fin k) (idx : Fin m → ℕ) :
    (ℕ → Fin k) → Fin m → Fin k :=
  fun ω j => rowSuccessorVisitProcess (k := k) (anchor j) ω (idx j)

lemma measurable_multiRowSelectionMap
    {m : ℕ} (anchor : Fin m → Fin k) (idx : Fin m → ℕ) :
    Measurable (multiRowSelectionMap (k := k) anchor idx) := by
  refine measurable_pi_lambda _ ?_
  intro j
  simpa only [multiRowSelectionMap, Function.comp_def] using
    (measurable_pi_apply (idx j)).comp
      (measurable_rowSuccessorVisitProcess (k := k) (anchor j))

/-- The finite set of coordinates in a mixed selection map whose anchor row is
`i`. -/
def anchorFiber
    {m : ℕ} (anchor : Fin m → Fin k) (i : Fin k) : Finset (Fin m) :=
  Finset.univ.filter fun j => anchor j = i

/-- The ordered list of coordinates in a mixed selection map whose anchor row
is `i`. The order is inherited from `List.finRange m`. -/
def anchorFiberList
    {m : ℕ} (anchor : Fin m → Fin k) (i : Fin k) : List (Fin m) :=
  (List.finRange m).filter fun j => anchor j = i

lemma mem_anchorFiberList_iff
    {m : ℕ} (anchor : Fin m → Fin k) (i : Fin k) (j : Fin m) :
    j ∈ anchorFiberList (k := k) anchor i ↔ anchor j = i := by
  simp [anchorFiberList, List.mem_filter, List.mem_finRange]

lemma getElem_anchorFiberList_eq_anchor
    {m : ℕ} (anchor : Fin m → Fin k) (i : Fin k) {n : ℕ}
    (hn : n < (anchorFiberList (k := k) anchor i).length) :
    anchor ((anchorFiberList (k := k) anchor i)[n]) = i := by
  simp only [anchorFiberList]
  exact of_decide_eq_true
    (List.getElem_filter
      (xs := List.finRange m)
      (p := fun j : Fin m => anchor j = i)
      hn)

/-- The projection of a mixed selection map to the coordinates whose anchor row
is `i`, enumerated by `Fin (anchorFiber anchor i).card`. -/
def anchorFiberSelectionMap
    {m : ℕ} (anchor : Fin m → Fin k) (idx : Fin m → ℕ) (i : Fin k) :
    (ℕ → Fin k) → Fin (anchorFiber (k := k) anchor i).card → Fin k :=
  fun ω t => multiRowSelectionMap (k := k) anchor idx ω
    ((anchorFiber (k := k) anchor i).equivFin.symm t).1

/-- The projection of a mixed selection map to the coordinates whose anchor row
is `i`, enumerated in the ambient left-to-right order. -/
def anchorFiberSelectionMapList
    {m : ℕ} (anchor : Fin m → Fin k) (idx : Fin m → ℕ) (i : Fin k) :
    (ℕ → Fin k) → Fin (anchorFiberList (k := k) anchor i).length → Fin k :=
  fun ω t => multiRowSelectionMap (k := k) anchor idx ω
    ((anchorFiberList (k := k) anchor i)[t])

lemma measurable_anchorFiberSelectionMap
    {m : ℕ} (anchor : Fin m → Fin k) (idx : Fin m → ℕ) (i : Fin k) :
    Measurable (anchorFiberSelectionMap (k := k) anchor idx i) := by
  refine measurable_pi_lambda _ ?_
  intro t
  simpa only [anchorFiberSelectionMap, Function.comp_def] using
    (measurable_pi_apply
      (((anchorFiber (k := k) anchor i).equivFin.symm t).1)).comp
      (measurable_multiRowSelectionMap (k := k) anchor idx)

lemma measurable_anchorFiberSelectionMapList
    {m : ℕ} (anchor : Fin m → Fin k) (idx : Fin m → ℕ) (i : Fin k) :
    Measurable (anchorFiberSelectionMapList (k := k) anchor idx i) := by
  refine measurable_pi_lambda _ ?_
  intro t
  simpa only [anchorFiberSelectionMapList, Function.comp_def] using
    (measurable_pi_apply
      ((anchorFiberList (k := k) anchor i)[t])).comp
      (measurable_multiRowSelectionMap (k := k) anchor idx)

/-- The anchor-fiber projection is a constant-anchor selection map after
enumerating the chosen fiber. This is the cleanest currently proved "mixed map
with one anchor fiber permuted" interface. -/
lemma anchorFiberSelectionMap_eq_const
    {m : ℕ} (anchor : Fin m → Fin k) (idx : Fin m → ℕ) (i : Fin k) :
    anchorFiberSelectionMap (k := k) anchor idx i =
      multiRowSelectionMap (k := k)
        (fun _ : Fin (anchorFiber (k := k) anchor i).card => i)
        (fun t : Fin (anchorFiber (k := k) anchor i).card =>
          idx (((anchorFiber (k := k) anchor i).equivFin.symm t).1)) := by
  funext ω t
  have ht : anchor (((anchorFiber (k := k) anchor i).equivFin.symm t).1) = i := by
    have hmem : (((anchorFiber (k := k) anchor i).equivFin.symm t).1) ∈
        anchorFiber (k := k) anchor i :=
      ((anchorFiber (k := k) anchor i).equivFin.symm t).2
    exact (Finset.mem_filter.mp hmem).2
  simp [anchorFiberSelectionMap, multiRowSelectionMap, ht]

/-- The ordered anchor-fiber projection is a constant-anchor selection map
after enumerating the chosen fiber by `anchorFiberList`. -/
lemma anchorFiberSelectionMapList_eq_const
    {m : ℕ} (anchor : Fin m → Fin k) (idx : Fin m → ℕ) (i : Fin k) :
    anchorFiberSelectionMapList (k := k) anchor idx i =
      multiRowSelectionMap (k := k)
        (fun _ : Fin (anchorFiberList (k := k) anchor i).length => i)
        (fun t : Fin (anchorFiberList (k := k) anchor i).length =>
          idx ((anchorFiberList (k := k) anchor i)[t])) := by
  funext ω t
  have ht : anchor ((anchorFiberList (k := k) anchor i)[t]) = i := by
    exact getElem_anchorFiberList_eq_anchor (k := k) anchor i t.2
  rw [anchorFiberSelectionMapList, multiRowSelectionMap, ht, multiRowSelectionMap]

/-- Anchor function for a mixed finite selection map with a contiguous head block
in row `i` and an arbitrary fixed tail block. -/
def mixedHeadBlockAnchor
    {n' r : ℕ} (i : Fin k) (tailAnchor : Fin r → Fin k) :
    Fin (n' + r) → Fin k :=
  fun j =>
    if hj : (j : ℕ) < n' then i
    else tailAnchor
      (Fin.subNat n' (j.cast (Nat.add_comm n' r)) (Nat.le_of_not_lt hj))

/-- Visit-index function for a mixed finite selection map with a contiguous head
block and an arbitrary fixed tail block. -/
def mixedHeadBlockIdx
    {n' r : ℕ} (headIdx : Fin n' → ℕ) (tailIdx : Fin r → ℕ) :
    Fin (n' + r) → ℕ :=
  fun j =>
    if hj : (j : ℕ) < n' then headIdx ⟨j, hj⟩
    else tailIdx
      (Fin.subNat n' (j.cast (Nat.add_comm n' r)) (Nat.le_of_not_lt hj))

/-- Mixed finite selection map with a contiguous head block in row `i` and a
fixed tail block. Projecting to the head block recovers a constant-anchor
`multiRowSelectionMap`, which is the version currently supported by the
existing restricted-start invariance theorem. -/
def mixedHeadBlockSelectionMap
    {n' r : ℕ} (i : Fin k) (headIdx : Fin n' → ℕ)
    (tailAnchor : Fin r → Fin k) (tailIdx : Fin r → ℕ) :
    (ℕ → Fin k) → Fin (n' + r) → Fin k :=
  multiRowSelectionMap (k := k)
    (mixedHeadBlockAnchor (k := k) i tailAnchor)
    (mixedHeadBlockIdx headIdx tailIdx)

lemma measurable_mixedHeadBlockSelectionMap
    {n' r : ℕ} (i : Fin k) (headIdx : Fin n' → ℕ)
    (tailAnchor : Fin r → Fin k) (tailIdx : Fin r → ℕ) :
    Measurable
      (mixedHeadBlockSelectionMap (k := k) i headIdx tailAnchor tailIdx) :=
  measurable_multiRowSelectionMap (k := k)
    (mixedHeadBlockAnchor (k := k) i tailAnchor)
    (mixedHeadBlockIdx headIdx tailIdx)

/-- On the contiguous head block, `mixedHeadBlockSelectionMap` agrees with the
constant-anchor selection map determined by `headIdx`. -/
lemma mixedHeadBlockSelectionMap_castAdd
    {n' r : ℕ} (i : Fin k) (headIdx : Fin n' → ℕ)
    (tailAnchor : Fin r → Fin k) (tailIdx : Fin r → ℕ)
    (ω : ℕ → Fin k) (m : Fin n') :
    mixedHeadBlockSelectionMap (k := k) i headIdx tailAnchor tailIdx ω (Fin.castAdd r m) =
      rowSuccessorVisitProcess (k := k) i ω (headIdx m) := by
  simp [mixedHeadBlockSelectionMap, mixedHeadBlockAnchor, mixedHeadBlockIdx,
    multiRowSelectionMap, m.isLt]

/-- Projecting the mixed head-block selection map to its head block recovers
the corresponding constant-anchor `multiRowSelectionMap`. This is the honest
contiguous-block reduction step available from the current per-row machinery. -/
lemma mixedHeadBlockSelectionMap_comp_castAdd
    {n' r : ℕ} (i : Fin k) (headIdx : Fin n' → ℕ)
    (tailAnchor : Fin r → Fin k) (tailIdx : Fin r → ℕ) :
    (fun ω (m : Fin n') =>
      mixedHeadBlockSelectionMap (k := k) i headIdx tailAnchor tailIdx ω (Fin.castAdd r m)) =
      multiRowSelectionMap (k := k) (fun _ : Fin n' => i) headIdx := by
  funext ω m
  simpa [multiRowSelectionMap] using
    mixedHeadBlockSelectionMap_castAdd (k := k) i headIdx tailAnchor tailIdx ω m

/-! ### Joint row-successor event = monotone union of finite approximations

For a finite set S of visit indices and value function v,
the joint event ⋂_{n ∈ S} rowSuccessorValueEvent(i, n, v(n))
equals ⋃_N rowVisitCylinderEventUpTo(i, S, v, N).
The union is monotone in N. -/

/-- The joint row-successor event: all specified visit indices have
the specified successor values. -/
def jointRowSuccEvent (i : Fin k) (S : Finset ℕ) (v : ℕ → Fin k) :
    Set (ℕ → Fin k) :=
  ⋂ n ∈ S, rowSuccessorValueEvent (k := k) i n (v n)

/-- The joint event equals the monotone union of finite-prefix approximations.
Generalizes `rowSuccessorValueEvent_eq_iUnion_upTo_of_ne`. -/
theorem jointRowSuccEvent_eq_iUnion_upTo
    (i : Fin k) (S : Finset ℕ) (v : ℕ → Fin k)
    (hne : ∀ n ∈ S, v n ≠ i) :
    jointRowSuccEvent (k := k) i S v =
      ⋃ N : ℕ, rowVisitCylinderEventUpTo (k := k) i S v N := by
  ext ω
  simp only [jointRowSuccEvent, Set.mem_iInter, Set.mem_iUnion,
    rowVisitCylinderEventUpTo, rowSuccessorValueEvent, Set.mem_setOf_eq]
  constructor
  · -- (→) ω satisfies all constraints → find uniform horizon N
    intro hω
    -- For each n ∈ S, extract a visit-time witness.
    -- rowSuccessorAtNthVisit i n ω = v n with v n ≠ i means
    -- nthVisitTime ω i n = some t (cannot be none, since default = i ≠ v n)
    have hsome : ∀ n ∈ S, ∃ t, nthVisitTime (k := k) ω i n = some t ∧
        successorAt (k := k) ω t = v n := by
      intro n hn
      have hvn := hω n hn
      simp only [rowSuccessorAtNthVisit] at hvn
      split at hvn
      · exact ⟨_, ‹_›, hvn⟩
      · exact absurd hvn.symm (hne n hn)
    -- Use Finset.induction to find a uniform horizon
    induction S using Finset.induction with
    | empty => exact ⟨0, fun _ h => by simp at h⟩
    | @insert a S' ha ih =>
      have hne' : ∀ n ∈ S', v n ≠ i := fun n hn => hne n (Finset.mem_insert_of_mem hn)
      have hω' : ∀ n ∈ S', rowSuccessorAtNthVisit (k := k) i n ω = v n :=
        fun n hn => hω n (Finset.mem_insert_of_mem hn)
      have hsome' : ∀ n ∈ S', ∃ t, nthVisitTime (k := k) ω i n = some t ∧
          successorAt (k := k) ω t = v n :=
        fun n hn => hsome n (Finset.mem_insert_of_mem hn)
      rcases ih hne' hω' hsome' with ⟨N₁, hN₁⟩
      rcases hsome a (Finset.mem_insert_self a S') with ⟨t, ht_time, ht_succ⟩
      refine ⟨max N₁ (t + 1), fun n hn => ?_⟩
      rw [Finset.mem_insert] at hn
      rcases hn with rfl | hn
      · exact ⟨t, by omega, ht_time, ht_succ⟩
      · rcases hN₁ n hn with ⟨t', ht'N, ht'_time, ht'_succ⟩
        exact ⟨t', by omega, ht'_time, ht'_succ⟩
  · -- (←) Some finite approximation holds → all constraints hold
    intro ⟨N, hN⟩ n hnS
    rcases hN n hnS with ⟨t, htN, htime, hsucc⟩
    simp only [rowSuccessorAtNthVisit, htime, hsucc]

/-- Monotonicity: rowVisitCylinderEventUpTo is monotone in N.
Already proved at Core:1027 but restated here for convenience. -/
theorem rowVisitCylinderEventUpTo_mono' (i : Fin k) (S : Finset ℕ) (v : ℕ → Fin k) :
    Monotone (fun N => rowVisitCylinderEventUpTo (k := k) i S v N) :=
  rowVisitCylinderEventUpTo_mono (k := k) i S v

/-! ### Level-3 lifting: finite carrier equiv → infinite-event measure equality

The monotone union approach: carrier equivs at each N give per-N equality;
monotone union gives the infinite result. Two versions:
  1. Set-level (requires hne: v(n) ≠ i): `measure_start_inter_jointRowSuccEvent_eq`
  2. Measure-level with StrongRecurrence: planned for sorry D proof. -/

/-- Level-3 lifting with eventual carrier equivs (original version, requires hne).

Given carrier equivs for all N ≥ N₀, derive start-restricted measure equality
on the infinite joint row-successor event. The tail of a monotone ⨆ determines
the limit, so eventual equality suffices. -/
theorem measure_start_inter_jointRowSuccEvent_eq
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (P : Measure (ℕ → Fin k))
    (hExt : ∀ xs : List (Fin k), μ xs = P (MarkovDeFinettiRecurrence.cylinder (k := k) xs))
    (i : Fin k) (j : Fin k)
    (S₁ S₂ : Finset ℕ) (v₁ v₂ : ℕ → Fin k)
    (hne₁ : ∀ n ∈ S₁, v₁ n ≠ i)
    (hne₂ : ∀ n ∈ S₂, v₂ n ≠ i)
    -- Eventual equiv: for all N ≥ N₀, carrier equiv exists
    (N₀ : ℕ)
    (hEquiv : ∀ N : ℕ, N₀ ≤ N →
      ∃ e : ↥(rowVisitCylinderEventUpToPrefixCarrier (k := k) i S₁ v₁ N) ≃
            ↥(rowVisitCylinderEventUpToPrefixCarrier (k := k) i S₂ v₂ N),
        ∀ xs, evidenceOf (n := N) xs.1 = evidenceOf (n := N) (e xs).1) :
    P ({ω : ℕ → Fin k | ω 0 = j} ∩ jointRowSuccEvent (k := k) i S₁ v₁)
      =
    P ({ω : ℕ → Fin k | ω 0 = j} ∩ jointRowSuccEvent (k := k) i S₂ v₂) := by
  -- Rewrite as monotone union
  have hA := jointRowSuccEvent_eq_iUnion_upTo (k := k) i S₁ v₁ hne₁
  have hB := jointRowSuccEvent_eq_iUnion_upTo (k := k) i S₂ v₂ hne₂
  let S0 : Set (ℕ → Fin k) := {ω | ω 0 = j}
  let A := fun N => rowVisitCylinderEventUpTo (k := k) i S₁ v₁ N
  let B := fun N => rowVisitCylinderEventUpTo (k := k) i S₂ v₂ N
  have hintA : S0 ∩ jointRowSuccEvent (k := k) i S₁ v₁ = ⋃ N, S0 ∩ A N := by
    rw [hA, Set.inter_iUnion]
  have hintB : S0 ∩ jointRowSuccEvent (k := k) i S₂ v₂ = ⋃ N, S0 ∩ B N := by
    rw [hB, Set.inter_iUnion]
  have hmonoA : Monotone (fun N => S0 ∩ A N) := by
    intro N M hNM ω hω; exact ⟨hω.1, rowVisitCylinderEventUpTo_mono' i S₁ v₁ hNM hω.2⟩
  have hmonoB : Monotone (fun N => S0 ∩ B N) := by
    intro N M hNM ω hω; exact ⟨hω.1, rowVisitCylinderEventUpTo_mono' i S₂ v₂ hNM hω.2⟩
  -- Per-N equality for N ≥ N₀ from carrier equiv + Markov exchangeability
  have hNeq : ∀ N, N₀ ≤ N → P (S0 ∩ A N) = P (S0 ∩ B N) := by
    intro N hN
    rcases hEquiv N hN with ⟨e, he⟩
    exact measure_start_inter_rowVisitCylinderEventUpTo_eq_of_evidencePreservingEquiv_start
      (k := k) μ hμ P hExt i S₁ v₁ i S₂ v₂ N j e he
  -- The monotone ⨆ is determined by its tail (N ≥ N₀)
  have hSupA : ⨆ N, P (S0 ∩ A N) = ⨆ N, P (S0 ∩ A (N + N₀)) := by
    apply le_antisymm
    · exact iSup_le fun N => le_iSup_of_le N
        (measure_mono (hmonoA (by omega : N ≤ N + N₀)))
    · exact iSup_le fun N => le_iSup_of_le (N + N₀) le_rfl
  have hSupB : ⨆ N, P (S0 ∩ B N) = ⨆ N, P (S0 ∩ B (N + N₀)) := by
    apply le_antisymm
    · exact iSup_le fun N => le_iSup_of_le N
        (measure_mono (hmonoB (by omega : N ≤ N + N₀)))
    · exact iSup_le fun N => le_iSup_of_le (N + N₀) le_rfl
  calc P (S0 ∩ jointRowSuccEvent (k := k) i S₁ v₁)
      = P (⋃ N, S0 ∩ A N) := by rw [hintA]
    _ = ⨆ N, P (S0 ∩ A N) := hmonoA.measure_iUnion
    _ = ⨆ N, P (S0 ∩ A (N + N₀)) := hSupA
    _ = ⨆ N, P (S0 ∩ B (N + N₀)) := by
        congr 1; funext N; exact hNeq (N + N₀) (by omega)
    _ = ⨆ N, P (S0 ∩ B N) := hSupB.symm
    _ = P (⋃ N, S0 ∩ B N) := (hmonoB.measure_iUnion).symm
    _ = P (S0 ∩ jointRowSuccEvent (k := k) i S₂ v₂) := by rw [hintB]

/-! ### Level-3 lifting under StrongRecurrence (V/NV split)

When StrongRecurrence holds, we can lift ⋃upTo measure equality to JRE
measure equality via the V/NV decomposition, without needing hne.

Key insight (council quorum 95%): The `Exchangeable` definition uses
`Equiv.Perm (Fin n)` (not `Equiv.Perm ℕ`), so the test positions are
ALWAYS in `range(n)` — same S. The carrier transport handles same-S
value permutations without needing hne.

Proof route: prove `Exchangeable ρ X` directly (same-S carrier transport),
then get `FullyExchangeable` from `exchangeable_iff_fullyExchangeable`.
This avoids the different-S carrier equiv problem that blocked sorry D.

On V (visits i) ∩ AVE (all visits exist a.e.): JRE = ⋃upTo.
On NV (never visits i): rsp defaults to i, both sides agree.
Key Mathlib lemma: `measure_eq_measure_of_null_diff`. -/

/-- Row-specific recurrence suffices to lift `⋃upTo` equality to the full JRE ∩ V
piece. This is the exact recurrence input used downstream for a fixed row `i`. -/
theorem measure_JRE_inter_V_eq_upTo_of_rowRecurrence
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (i : Fin k)
    (hRowRec :
      ∀ᵐ ω ∂P, (∃ t, ω t = i) → ∀ n,
        nthVisitTimeExists (k := k) ω i n)
    (S0 : Set (ℕ → Fin k))
    (S : Finset ℕ) (v : ℕ → Fin k) (hS_ne : S.Nonempty) :
    P (S0 ∩ jointRowSuccEvent (k := k) i S v ∩ {ω | ∃ t, ω t = i}) =
    P (S0 ∩ ⋃ N, rowVisitCylinderEventUpTo (k := k) i S v N) := by
  apply Eq.symm
  apply measure_eq_measure_of_null_diff
  · -- ⋃upTo ⊆ JRE ∩ V
    intro ω ⟨hS0, hupTo⟩
    rcases Set.mem_iUnion.mp hupTo with ⟨N, hN⟩
    refine ⟨⟨hS0, Set.mem_iInter₂.mpr fun m hm => ?_⟩, ?_⟩
    · -- ω ∈ JRE at index m
      simp only [rowSuccessorValueEvent, Set.mem_setOf_eq]
      rcases (hN : ∀ n ∈ S, ∃ t < N, nthVisitTime (k := k) ω i n = some t ∧
        successorAt (k := k) ω t = v n) m hm with ⟨t, _, ht_time, ht_succ⟩
      simp only [rowSuccessorAtNthVisit, ht_time]; exact ht_succ
    · -- ω ∈ V
      rcases hS_ne with ⟨m₀, hm₀⟩
      rcases (hN : ∀ n ∈ S, _) m₀ hm₀ with ⟨t, _, ht_time, _⟩
      exact ⟨t, ((nthVisitTime_eq_some_iff (k := k) ω i m₀ t).mp ht_time).1⟩
  · -- (JRE ∩ V) \ ⋃upTo is null under the row-specific recurrence input
    have hSR : P {ω : ℕ → Fin k | ¬((∃ t, ω t = i) →
        ∀ n, nthVisitTimeExists (k := k) ω i n)} = 0 :=
      ae_iff.mp hRowRec
    apply measure_mono_null _ hSR
    intro ω ⟨⟨⟨hS0, hJRE⟩, hV⟩, hNotUpTo⟩
    simp only [Set.mem_setOf_eq, Classical.not_imp, not_forall]
    exact ⟨hV, by
      by_contra hAll; push_neg at hAll
      have hNotU : ω ∉ ⋃ N, rowVisitCylinderEventUpTo (k := k) i S v N :=
        fun h => hNotUpTo ⟨hS0, h⟩
      apply hNotU
      classical
      have hSome : ∀ m ∈ S, ∃ t, nthVisitTime (k := k) ω i m = some t := fun m _ =>
        ⟨_, (nthVisitTime_eq_some_iff (k := k) ω i m _).mpr (Nat.find_spec (hAll m))⟩
      choose! tFn htFn using hSome
      apply Set.mem_iUnion.mpr
      refine ⟨S.sup tFn + 1, fun m hm => ⟨tFn m, ?_, htFn m hm, ?_⟩⟩
      · exact Nat.lt_succ_of_le (Finset.le_sup (f := tFn) hm)
      · have hJm := Set.mem_iInter₂.mp hJRE m hm
        simp only [rowSuccessorValueEvent, Set.mem_setOf_eq,
          rowSuccessorAtNthVisit, htFn m hm] at hJm
        exact hJm⟩

/-- Under StrongRecurrence, `P(S0 ∩ JRE ∩ V) = P(S0 ∩ ⋃upTo)` where `V = {ω visits i}`.
Uses `measure_eq_measure_of_null_diff`: ⋃upTo ⊆ JRE ∩ V, and (JRE ∩ V) \ ⋃upTo is null. -/
theorem measure_JRE_inter_V_eq_upTo_of_strongRecurrence
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (hStrRec : MarkovDeFinettiHard.StrongRecurrence (k := k) P)
    (i : Fin k) (S0 : Set (ℕ → Fin k))
    (S : Finset ℕ) (v : ℕ → Fin k) (hS_ne : S.Nonempty) :
    P (S0 ∩ jointRowSuccEvent (k := k) i S v ∩ {ω | ∃ t, ω t = i}) =
    P (S0 ∩ ⋃ N, rowVisitCylinderEventUpTo (k := k) i S v N) := by
  exact
    measure_JRE_inter_V_eq_upTo_of_rowRecurrence
      (k := k) P i (hStrRec i) S0 S v hS_ne

/-! ### Instantiation: adjacent transposition → start-restricted multi-index equality

The multi-index carrier equiv for state i, adjacent visits n↔n+1,
gives: swapping the required values at visits n and n+1 preserves
start-restricted cylinder probabilities. This is the base case for
per-row exchangeability.

Key observation (council quorum 85%): swapping values at (n, n+1) in the
carrier specification IS the same as applying transposition (n, n+1) to
the visit indices. So the carrier equiv directly gives the permutation
invariance for adjacent transpositions. -/

/-- Adjacent transposition of a value function at positions n and n+1. -/
def swapValues (v : ℕ → Fin k) (n : ℕ) : ℕ → Fin k :=
  fun m => if m = n then v (n + 1) else if m = n + 1 then v n else v m

/-! ### Per-row joint perm invariance via carrier transport

The joint exchangeability of the row process for state i follows from:
1. Carrier transport: `rawSwap` + `segmentSwap_multiIndex_carrier_mem` give
   evidence-preserving bijections for adjacent value swaps when n+2 ∈ S (guard index).
2. Level-3 lifting: startRestricted_jointEvent_adjacent_swap lifts to infinite events.
3. Composition: adjacent swaps generate all permutations (swap_induction_on').
4. Marginalization: under strong recurrence, the guard index can be marginalized out.
5. measure_eq_of_fin_marginals_eq_prob: finite-dimensional agreement → full equality. -/

/-- Adjacent swap of a value function: swap values at positions a and a+1.
This is `swapValues` from PEBridge, re-expressed for the carrier equiv signature. -/
private def swapAt (v : ℕ → Fin k) (a : ℕ) : ℕ → Fin k :=
  fun m => if m = a then v (a + 1) else if m = a + 1 then v a else v m

/-- Multi-index carrier membership implies existence of the requested visit time. -/
private lemma carrier_mem_visit_exists_of_mem {N : ℕ}
    (i : Fin k) (S : Finset ℕ) (v : ℕ → Fin k)
    (xs : Fin (N + 1) → Fin k)
    (hxs : xs ∈ rowVisitCylinderEventUpToPrefixCarrier (k := k) i S v N)
    (m : ℕ) (hm : m ∈ S) :
    nthVisitTimeExists (k := k) (prefixExtend (k := k) N xs) i m := by
  have hmem : prefixExtend (k := k) N xs ∈
      rowVisitCylinderEventUpTo (k := k) i S v N := by
    simp only [rowVisitCylinderEventUpToPrefixCarrier, Finset.mem_filter, Finset.mem_univ,
      true_and] at hxs
    exact hxs
  rcases hmem m hm with ⟨t, _, htime, _⟩
  exact ⟨t, (nthVisitTime_eq_some_iff (k := k) _ i m t).mp htime⟩

/-- For multi-index carrier members, extracted visit times are within the horizon. -/
private lemma extractVisitTime_lt_of_carrier_mem_of_mem {N : ℕ}
    (i : Fin k) (S : Finset ℕ) (v : ℕ → Fin k)
    (xs : Fin (N + 1) → Fin k)
    (hxs : xs ∈ rowVisitCylinderEventUpToPrefixCarrier (k := k) i S v N)
    (m : ℕ) (hm : m ∈ S) :
    extractVisitTime xs i m (carrier_mem_visit_exists_of_mem (k := k) i S v xs hxs m hm) < N := by
  have hmem : prefixExtend (k := k) N xs ∈
      rowVisitCylinderEventUpTo (k := k) i S v N := by
    simp only [rowVisitCylinderEventUpToPrefixCarrier, Finset.mem_filter, Finset.mem_univ,
      true_and] at hxs
    exact hxs
  rcases hmem m hm with ⟨t, htN, htime, _⟩
  have hspec :
      isNthVisitTime (k := k) (prefixExtend (k := k) N xs) i m
        (extractVisitTime xs i m
          (carrier_mem_visit_exists_of_mem (k := k) i S v xs hxs m hm)) :=
    extractVisitTime_spec xs i m (carrier_mem_visit_exists_of_mem (k := k) i S v xs hxs m hm)
  have hspec_t : isNthVisitTime (k := k) (prefixExtend (k := k) N xs) i m t :=
    (nthVisitTime_eq_some_iff (k := k) _ i m t).mp htime
  have ht_eq := isNthVisitTime_unique (k := k) _ i m _ t hspec hspec_t
  rw [ht_eq]
  exact htN

/-- Consecutive extracted visit times are strictly ordered. -/
private lemma extractVisitTime_lt_succ {N : ℕ}
    (xs : Fin (N + 1) → Fin k) (i : Fin k) (n : ℕ)
    (hexN : nthVisitTimeExists (k := k) (prefixExtend (k := k) N xs) i n)
    (hexN1 : nthVisitTimeExists (k := k) (prefixExtend (k := k) N xs) i (n + 1)) :
    extractVisitTime xs i n hexN < extractVisitTime xs i (n + 1) hexN1 := by
  have hN := extractVisitTime_spec xs i n hexN
  have hN1 := extractVisitTime_spec xs i (n + 1) hexN1
  by_contra h
  push_neg at h
  have hmono := Finset.sum_le_sum_of_subset
    (f := fun s => if (prefixExtend (k := k) N xs) s = i then 1 else 0)
    (Finset.range_mono h)
  change visitCountBefore (k := k) (prefixExtend (k := k) N xs) i
      (extractVisitTime xs i (n + 1) hexN1) ≤
    visitCountBefore (k := k) (prefixExtend (k := k) N xs) i
      (extractVisitTime xs i n hexN) at hmono
  rw [hN.2, hN1.2] at hmono
  omega

/-- The carrier equiv for a SINGLE adjacent swap at position a, built from
`rawSwap` and `segmentSwap_multiIndex_carrier_mem`. Requires a, a+1, a+2 ∈ S. -/
private theorem carrier_equiv_adjacent {N : ℕ}
    (i : Fin k) (S : Finset ℕ) (v : ℕ → Fin k)
    (a : ℕ) (ha : a ∈ S) (ha1 : a + 1 ∈ S) (ha2 : a + 2 ∈ S) :
    ∃ e : ↥(rowVisitCylinderEventUpToPrefixCarrier (k := k) i S v N) ≃
          ↥(rowVisitCylinderEventUpToPrefixCarrier (k := k) i S (swapAt (k := k) v a) N),
      ∀ xs, evidenceOf (n := N) xs.1 = evidenceOf (n := N) (e xs).1 := by
  refine ⟨{
    toFun := fun ⟨xs, hxs⟩ => by
      let hex0 := carrier_mem_visit_exists_of_mem (k := k) i S v xs hxs a ha
      let hex1 := carrier_mem_visit_exists_of_mem (k := k) i S v xs hxs (a + 1) ha1
      let hex2 := carrier_mem_visit_exists_of_mem (k := k) i S v xs hxs (a + 2) ha2
      let hbd1 := extractVisitTime_lt_of_carrier_mem_of_mem
        (k := k) i S v xs hxs (a + 1) ha1
      let hbd2 := extractVisitTime_lt_of_carrier_mem_of_mem
        (k := k) i S v xs hxs (a + 2) ha2
      have h_t0 := extractVisitTime_spec xs i a hex0
      have h_t1 := extractVisitTime_spec xs i (a + 1) hex1
      have h_t2 := extractVisitTime_spec xs i (a + 2) hex2
      have ht01 : extractVisitTime xs i a hex0 < extractVisitTime xs i (a + 1) hex1 :=
        extractVisitTime_lt_succ (k := k) xs i a hex0 hex1
      have ht12 : extractVisitTime xs i (a + 1) hex1 < extractVisitTime xs i (a + 2) hex2 :=
        extractVisitTime_lt_succ (k := k) xs i (a + 1) hex1 hex2
      have h_aL1 : isNthVisitTime (k := k) (prefixExtend (k := k) N xs) i (a + 1)
          (extractVisitTime xs i a hex0
            + (extractVisitTime xs i (a + 1) hex1 - extractVisitTime xs i a hex0)) := by
        convert h_t1 using 1
        exact Nat.add_sub_cancel' (Nat.le_of_lt ht01)
      have h_aL1L2 : isNthVisitTime (k := k) (prefixExtend (k := k) N xs) i (a + 2)
          (extractVisitTime xs i a hex0
            + (extractVisitTime xs i (a + 1) hex1 - extractVisitTime xs i a hex0)
            + (extractVisitTime xs i (a + 2) hex2 - extractVisitTime xs i (a + 1) hex1)) := by
        convert h_t2 using 1
        rw [Nat.add_sub_cancel' (Nat.le_of_lt ht01), Nat.add_sub_cancel' (Nat.le_of_lt ht12)]
      refine ⟨rawSwap xs i a hex0 hex1 hex2 hbd1 hbd2, ?_⟩
      have hmem :=
        (segmentSwap_multiIndex_carrier_mem (k := k) i a
          (extractVisitTime xs i a hex0)
          (extractVisitTime xs i (a + 1) hex1 - extractVisitTime xs i a hex0)
          (extractVisitTime xs i (a + 2) hex2 - extractVisitTime xs i (a + 1) hex1)
          (Nat.sub_pos_of_lt ht01) (Nat.sub_pos_of_lt ht12)
          (by
            show extractVisitTime xs i a hex0
                + (extractVisitTime xs i (a + 1) hex1 - extractVisitTime xs i a hex0)
                + (extractVisitTime xs i (a + 2) hex2 - extractVisitTime xs i (a + 1) hex1) ≤ N
            calc
              _ = extractVisitTime xs i (a + 2) hex2 := by omega
              _ ≤ N := Nat.le_of_lt hbd2)
          S v ha ha1 xs hxs h_t0 h_aL1 h_aL1L2)
      exact hmem
    invFun := fun ⟨ys, hys⟩ => by
      let hex0 := carrier_mem_visit_exists_of_mem (k := k) i S (swapAt (k := k) v a) ys hys a ha
      let hex1 := carrier_mem_visit_exists_of_mem
        (k := k) i S (swapAt (k := k) v a) ys hys (a + 1) ha1
      let hex2 := carrier_mem_visit_exists_of_mem
        (k := k) i S (swapAt (k := k) v a) ys hys (a + 2) ha2
      let hbd1 := extractVisitTime_lt_of_carrier_mem_of_mem
        (k := k) i S (swapAt (k := k) v a) ys hys (a + 1) ha1
      let hbd2 := extractVisitTime_lt_of_carrier_mem_of_mem
        (k := k) i S (swapAt (k := k) v a) ys hys (a + 2) ha2
      have h_t0 := extractVisitTime_spec ys i a hex0
      have h_t1 := extractVisitTime_spec ys i (a + 1) hex1
      have h_t2 := extractVisitTime_spec ys i (a + 2) hex2
      have ht01 : extractVisitTime ys i a hex0 < extractVisitTime ys i (a + 1) hex1 :=
        extractVisitTime_lt_succ (k := k) ys i a hex0 hex1
      have ht12 : extractVisitTime ys i (a + 1) hex1 < extractVisitTime ys i (a + 2) hex2 :=
        extractVisitTime_lt_succ (k := k) ys i (a + 1) hex1 hex2
      have h_aL1 : isNthVisitTime (k := k) (prefixExtend (k := k) N ys) i (a + 1)
          (extractVisitTime ys i a hex0
            + (extractVisitTime ys i (a + 1) hex1 - extractVisitTime ys i a hex0)) := by
        convert h_t1 using 1
        exact Nat.add_sub_cancel' (Nat.le_of_lt ht01)
      have h_aL1L2 : isNthVisitTime (k := k) (prefixExtend (k := k) N ys) i (a + 2)
          (extractVisitTime ys i a hex0
            + (extractVisitTime ys i (a + 1) hex1 - extractVisitTime ys i a hex0)
            + (extractVisitTime ys i (a + 2) hex2 - extractVisitTime ys i (a + 1) hex1)) := by
        convert h_t2 using 1
        rw [Nat.add_sub_cancel' (Nat.le_of_lt ht01), Nat.add_sub_cancel' (Nat.le_of_lt ht12)]
      have hswap_twice :
          (fun m =>
            if m = a then (swapAt (k := k) v a) (a + 1)
            else if m = a + 1 then (swapAt (k := k) v a) a
            else (swapAt (k := k) v a) m) = v := by
        funext m
        by_cases hm : m = a
        · subst hm
          simp [swapAt]
        · by_cases hm1 : m = a + 1
          · subst hm1
            simp [swapAt]
          · simp [swapAt, hm, hm1]
      have hback_mem :
          segmentSwap ys (extractVisitTime ys i a hex0)
              (extractVisitTime ys i (a + 1) hex1 - extractVisitTime ys i a hex0)
              (extractVisitTime ys i (a + 2) hex2 - extractVisitTime ys i (a + 1) hex1)
              (Nat.sub_pos_of_lt ht01) (Nat.sub_pos_of_lt ht12)
              (by
                show extractVisitTime ys i a hex0
                    + (extractVisitTime ys i (a + 1) hex1 - extractVisitTime ys i a hex0)
                    + (extractVisitTime ys i (a + 2) hex2 - extractVisitTime ys i (a + 1) hex1) ≤ N
                calc
                  _ = extractVisitTime ys i (a + 2) hex2 := by omega
                  _ ≤ N := Nat.le_of_lt hbd2)
            ∈ rowVisitCylinderEventUpToPrefixCarrier (k := k) i S v N := by
        simpa [hswap_twice] using
          (segmentSwap_multiIndex_carrier_mem (k := k) i a
            (extractVisitTime ys i a hex0)
            (extractVisitTime ys i (a + 1) hex1 - extractVisitTime ys i a hex0)
            (extractVisitTime ys i (a + 2) hex2 - extractVisitTime ys i (a + 1) hex1)
            (Nat.sub_pos_of_lt ht01) (Nat.sub_pos_of_lt ht12)
            (by
              show extractVisitTime ys i a hex0
                  + (extractVisitTime ys i (a + 1) hex1 - extractVisitTime ys i a hex0)
                  + (extractVisitTime ys i (a + 2) hex2 - extractVisitTime ys i (a + 1) hex1) ≤ N
              calc
                _ = extractVisitTime ys i (a + 2) hex2 := by omega
                _ ≤ N := Nat.le_of_lt hbd2)
            S (swapAt (k := k) v a) ha ha1 ys hys h_t0 h_aL1 h_aL1L2)
      refine ⟨rawSwap ys i a hex0 hex1 hex2 hbd1 hbd2, ?_⟩
      simpa [rawSwap] using hback_mem
    left_inv := by
      intro ⟨xs, hxs⟩
      ext1
      let hex0 := carrier_mem_visit_exists_of_mem (k := k) i S v xs hxs a ha
      let hex1 := carrier_mem_visit_exists_of_mem (k := k) i S v xs hxs (a + 1) ha1
      let hex2 := carrier_mem_visit_exists_of_mem (k := k) i S v xs hxs (a + 2) ha2
      let hbd1 := extractVisitTime_lt_of_carrier_mem_of_mem
        (k := k) i S v xs hxs (a + 1) ha1
      let hbd2 := extractVisitTime_lt_of_carrier_mem_of_mem
        (k := k) i S v xs hxs (a + 2) ha2
      obtain ⟨_, _, _, _, _, heq⟩ := rawSwap_selfInverse xs i a hex0 hex1 hex2 hbd1 hbd2
      exact heq
    right_inv := by
      intro ⟨ys, hys⟩
      ext1
      let hex0 := carrier_mem_visit_exists_of_mem (k := k) i S (swapAt (k := k) v a) ys hys a ha
      let hex1 := carrier_mem_visit_exists_of_mem
        (k := k) i S (swapAt (k := k) v a) ys hys (a + 1) ha1
      let hex2 := carrier_mem_visit_exists_of_mem
        (k := k) i S (swapAt (k := k) v a) ys hys (a + 2) ha2
      let hbd1 := extractVisitTime_lt_of_carrier_mem_of_mem
        (k := k) i S (swapAt (k := k) v a) ys hys (a + 1) ha1
      let hbd2 := extractVisitTime_lt_of_carrier_mem_of_mem
        (k := k) i S (swapAt (k := k) v a) ys hys (a + 2) ha2
      obtain ⟨_, _, _, _, _, heq⟩ := rawSwap_selfInverse ys i a hex0 hex1 hex2 hbd1 hbd2
      exact heq
  }, ?_⟩
  intro ⟨xs, hxs⟩
  let hex0 := carrier_mem_visit_exists_of_mem (k := k) i S v xs hxs a ha
  let hex1 := carrier_mem_visit_exists_of_mem (k := k) i S v xs hxs (a + 1) ha1
  let hex2 := carrier_mem_visit_exists_of_mem (k := k) i S v xs hxs (a + 2) ha2
  let hbd1 := extractVisitTime_lt_of_carrier_mem_of_mem
    (k := k) i S v xs hxs (a + 1) ha1
  let hbd2 := extractVisitTime_lt_of_carrier_mem_of_mem
    (k := k) i S v xs hxs (a + 2) ha2
  exact (rawSwap_fwd_evid xs i a hex0 hex1 hex2 hbd1 hbd2).symm

/-- Start-restricted measure equality for adjacent transposition on a single row.
Permuting values at visits n↔n+1 for state i preserves the start-restricted
measure of the joint event. Requires n, n+1, n+2 ∈ S so the carrier equiv
has sufficient visit data (derived from carrier membership, not CarrierSuffHyp).

This combines adjacent carrier equiv (`carrier_equiv_adjacent`) with
`measure_start_inter_jointRowSuccEvent_eq` (level-3 lifting). -/
theorem startRestricted_jointEvent_adjacent_swap
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (P : Measure (ℕ → Fin k))
    (hExt : ∀ xs : List (Fin k), μ xs = P (MarkovDeFinettiRecurrence.cylinder (k := k) xs))
    (i j : Fin k) (n : ℕ) (S : Finset ℕ) (v : ℕ → Fin k)
    (hn : n ∈ S) (hn1 : n + 1 ∈ S) (hn2 : n + 2 ∈ S)
    (hne : ∀ m ∈ S, v m ≠ i) :
    P ({ω : ℕ → Fin k | ω 0 = j} ∩ jointRowSuccEvent (k := k) i S v)
      =
    P ({ω : ℕ → Fin k | ω 0 = j} ∩
      jointRowSuccEvent (k := k) i S (swapValues (k := k) v n)) := by
  have hne' : ∀ m ∈ S, swapValues (k := k) v n m ≠ i := by
    intro m hm
    simp only [swapValues]
    split_ifs with h1 h2
    · exact hne (n + 1) hn1
    · exact hne n hn
    · exact hne m hm
  exact measure_start_inter_jointRowSuccEvent_eq (k := k) μ hμ P hExt i j S S v
    (swapValues (k := k) v n) hne hne' 0
    (fun N _ => by
      rcases carrier_equiv_adjacent (N := N) i S v n hn hn1 hn2 with ⟨e, he⟩
      refine ⟨e, ?_⟩
      intro xs
      exact he xs)

/-- Carrier equiv for swapping values at positions a and b (not necessarily adjacent),
with a < b and all intermediate positions + guard in S.
Proof: compose adjacent swaps using the three-swap identity
  swap(a,b) = adj(a) ∘ adj(a+1) ∘ ... ∘ adj(b-1) ∘ adj(b-2) ∘ ... ∘ adj(a).
By induction on b - a. -/
private theorem carrier_equiv_swap {N : ℕ}
    (i : Fin k) (S : Finset ℕ) (v : ℕ → Fin k)
    (a b : ℕ) (hab : a < b)
    -- All positions a through b+1 are in S (ensures guards for all adjacent swaps)
    (hrange : ∀ m, a ≤ m → m ≤ b + 1 → m ∈ S) :
    ∃ e : ↥(rowVisitCylinderEventUpToPrefixCarrier (k := k) i S v N) ≃
          ↥(rowVisitCylinderEventUpToPrefixCarrier (k := k) i S
            (fun m => if m = a then v b else if m = b then v a else v m) N),
      ∀ xs, evidenceOf (n := N) xs.1 = evidenceOf (n := N) (e xs).1 := by
  -- Induction on d = b - a - 1 (distance minus 1), generalizing over a and v.
  obtain ⟨d, hd⟩ : ∃ d, b = a + d + 1 := ⟨b - a - 1, by omega⟩
  subst hd; clear hab
  induction d generalizing a v with
  | zero =>
    -- Base case: b = a + 1, adjacent swap
    simp only [Nat.add_zero]
    exact carrier_equiv_adjacent i S v a (hrange a le_rfl (by omega))
      (hrange (a + 1) (by omega) (by omega)) (hrange (a + 2) (by omega) (by omega))
  | succ d ih =>
    -- Step: swap(a, a+d+2) via three-swap identity:
    -- adj(a) ∘ swap(a+1, a+d+2) ∘ adj(a) = swap(a, a+d+2)
    -- Step 1: adj(a) on v gives v' = swapAt v a
    let v₁ := swapAt (k := k) v a
    rcases carrier_equiv_adjacent (N := N) i S v a (hrange a le_rfl (by omega))
      (hrange (a + 1) (by omega) (by omega))
      (hrange (a + 2) (by omega) (by omega)) with ⟨e₁, he₁⟩
    -- Step 2: swap(a+1, a+d+2) on v₁ gives v₂ (by ih at position a+1)
    have hrange' : ∀ m, a + 1 ≤ m → m ≤ a + 1 + d + 1 + 1 → m ∈ S :=
      fun m hm1 hm2 => hrange m (by omega) (by omega)
    rcases ih v₁ (a + 1) hrange' with ⟨e₂, he₂⟩
    -- Step 3: adj(a) on v₂ gives v₃ (final result)
    -- Use a + 1 + d + 1 to match ih output (definitional equality with e₂'s codomain)
    let v₂ := fun m => if m = a + 1 then v₁ (a + 1 + d + 1)
                        else if m = a + 1 + d + 1 then v₁ (a + 1)
                        else v₁ m
    rcases carrier_equiv_adjacent (N := N) i S v₂ a (hrange a le_rfl (by omega))
      (hrange (a + 1) (by omega) (by omega))
      (hrange (a + 2) (by omega) (by omega)) with ⟨e₃, he₃⟩
    -- Three-swap value function identity: swapAt(v₂, a) = target swap(a, a+d+2)
    have h_vf : (fun m => if m = a then v (a + (d + 1) + 1)
        else if m = a + (d + 1) + 1 then v a else v m) = swapAt (k := k) v₂ a := by
      funext m; simp only [swapAt, v₂, v₁]
      split_ifs <;> first | rfl | exact congr_arg v (by omega)
    rw [h_vf]
    exact ⟨(e₁.trans e₂).trans e₃, fun xs =>
      (he₁ xs).trans ((he₂ (e₁ xs)).trans (he₃ (e₂ (e₁ xs))))⟩

/-- Carrier equiv for arbitrary value function permutation within S.
Given v, w related by a permutation π (fixing complement of S),
with all values ≠ i and S contiguous with guards, there exists an
evidence-preserving carrier bijection.
Proved by `swap_induction_on'` composing `carrier_equiv_swap`. -/
theorem carrier_equiv_of_value_perm {N : ℕ}
    (i : Fin k) (S : Finset ℕ) (v w : ℕ → Fin k)
    (hS_range : ∀ a b, a ∈ S → b ∈ S → a < b → ∀ m, a ≤ m → m ≤ b + 1 → m ∈ S)
    (hout : ∀ m, m ∉ S → v m = w m)
    (hperm : ∃ π : Equiv.Perm ℕ, (∀ m ∈ S, w m = v (π m)) ∧
        (∀ m, m ∉ S → π m = m)) :
    ∃ e : ↥(rowVisitCylinderEventUpToPrefixCarrier (k := k) i S v N) ≃
          ↥(rowVisitCylinderEventUpToPrefixCarrier (k := k) i S w N),
      ∀ xs, evidenceOf (n := N) xs.1 = evidenceOf (n := N) (e xs).1 := by
  rcases hperm with ⟨π, hπval, hπfix⟩
  -- Perm fixing outside S maps S to S
  have perm_maps_S : ∀ (σ : Equiv.Perm ℕ), (∀ m, m ∉ S → σ m = m) →
      ∀ x, x ∈ S → σ x ∈ S := by
    intro σ hfix x hx; by_contra h
    exact h (show σ x ∈ S by rwa [show σ x = x from σ.injective (hfix _ h)])
  -- Restrict π to the finite subtype
  haveI : Finite ↥(↑S : Set ℕ) := S.finite_toSet.to_subtype
  have hπ_iff : ∀ x, (π x ∈ (↑S : Set ℕ)) ↔ (x ∈ (↑S : Set ℕ)) := by
    intro x; constructor
    · intro h; by_contra hx
      rw [hπfix x (by simpa using hx)] at h; exact hx h
    · intro hx; exact perm_maps_S π hπfix x (by simpa using hx)
  let π_sub : Equiv.Perm ↥(↑S : Set ℕ) := π.subtypePerm hπ_iff
  -- Motive: for σ on ↥S, carrier equiv from v to val_of(σ)
  let val_of (σ : Equiv.Perm ↥(↑S : Set ℕ)) : ℕ → Fin k :=
    fun m => if h : (m ∈ S) then v ((σ ⟨m, h⟩ : ↥(↑S : Set ℕ)).1) else v m
  -- val_of(1) = v
  have hval_1 : val_of 1 = v := by funext m; simp [val_of]
  -- val_of(π_sub) = w (connecting the subtype perm to the target function)
  -- val_of(π_sub) = w
  have hval_π : val_of π_sub = w := by
    funext m; simp only [val_of]; split
    · next h => simp [π_sub]; exact (hπval m h).symm
    · next h => exact hout m h
  -- Suffices to prove the motive for all σ
  suffices hmot : ∀ σ : Equiv.Perm ↥(↑S : Set ℕ),
      ∃ e : ↥(rowVisitCylinderEventUpToPrefixCarrier (k := k) i S v N) ≃
            ↥(rowVisitCylinderEventUpToPrefixCarrier (k := k) i S (val_of σ) N),
        ∀ xs, evidenceOf (n := N) xs.1 = evidenceOf (n := N) (e xs).1 by
    rcases hmot π_sub with ⟨e, he⟩; rw [← hval_π]; exact ⟨e, he⟩
  -- Prove motive by swap_induction_on'
  intro σ
  refine σ.swap_induction_on' ?_ ?_
  · -- Base: σ = 1
    rw [hval_1]; exact ⟨Equiv.refl _, fun _ => rfl⟩
  · -- Step: given equiv for τ, extend to τ * swap(x,y)
    intro τ x y hxy ⟨e_τ, he_τ⟩
    have hx_mem : x.val ∈ S := by simp
    have hy_mem : y.val ∈ S := by simp
    have hxy_val : x.val ≠ y.val := Subtype.val_injective.ne hxy
    -- val_of(τ * swap(x,y)) swaps values at x.val, y.val in val_of(τ)
    -- Use carrier_equiv_swap to bridge carrier(val_of τ) ≃ carrier(val_of(τ*swap(x,y)))
    rcases Nat.lt_or_gt_of_ne hxy_val with hab | hab
    · -- x.val < y.val
      rcases carrier_equiv_swap (N := N) i S (val_of τ) x.val y.val hab
        (hS_range x.val y.val hx_mem hy_mem hab) with ⟨e_sw, he_sw⟩
      -- The swap target = val_of(τ * swap(x,y))
      -- Value function identity: swap at (x.val, y.val) = val_of(τ * swap(x,y))
      have htarget : (fun m => if m = x.val then (val_of τ) y.val
            else if m = y.val then (val_of τ) x.val else (val_of τ) m) =
          val_of (τ * Equiv.swap x y) := by
        funext m; simp only [val_of, Equiv.Perm.mul_apply]
        by_cases hm : m ∈ S
        · simp only [dif_pos hm]
          by_cases hxm : m = x.val
          · subst hxm; simp [Equiv.swap_apply_left, show (⟨m, hm⟩ : ↥(↑S : Set ℕ)) = x from Subtype.ext rfl,
              show (⟨y.val, hy_mem⟩ : ↥(↑S : Set ℕ)) = y from Subtype.ext rfl]
          · by_cases hym : m = y.val
            · subst hym; simp [hxm, Equiv.swap_apply_right, show (⟨m, hm⟩ : ↥(↑S : Set ℕ)) = y from Subtype.ext rfl,
                show (⟨x.val, hx_mem⟩ : ↥(↑S : Set ℕ)) = x from Subtype.ext rfl]
            · have hne_x : (⟨m, hm⟩ : ↥(↑S : Set ℕ)) ≠ x := fun h => hxm (congr_arg Subtype.val h)
              have hne_y : (⟨m, hm⟩ : ↥(↑S : Set ℕ)) ≠ y := fun h => hym (congr_arg Subtype.val h)
              simp only [hxm, ite_false, hym, Equiv.swap_apply_of_ne_of_ne hne_x hne_y]
        · simp only [dif_neg hm]
          have hxm : m ≠ x.val := fun h => hm (h ▸ hx_mem)
          have hym : m ≠ y.val := fun h => hm (h ▸ hy_mem)
          simp only [hxm, ite_false, hym]
      suffices ∃ e : ↥(rowVisitCylinderEventUpToPrefixCarrier (k := k) i S v N) ≃
            ↥(rowVisitCylinderEventUpToPrefixCarrier (k := k) i S
              (fun m => if m = x.val then (val_of τ) y.val
                else if m = y.val then (val_of τ) x.val else (val_of τ) m) N),
          ∀ xs, evidenceOf (n := N) xs.1 = evidenceOf (n := N) (e xs).1 by rwa [htarget] at this
      exact ⟨e_τ.trans e_sw, fun xs => (he_τ xs).trans (he_sw (e_τ xs))⟩
    · -- y.val < x.val: use symmetry of swap
      rcases carrier_equiv_swap (N := N) i S (val_of τ) y.val x.val hab
        (hS_range y.val x.val hy_mem hx_mem hab) with ⟨e_sw, he_sw⟩
      have htarget : (fun m => if m = y.val then (val_of τ) x.val
            else if m = x.val then (val_of τ) y.val else (val_of τ) m) =
          val_of (τ * Equiv.swap x y) := by
        funext m; simp only [val_of, Equiv.Perm.mul_apply]
        by_cases hm : m ∈ S
        · simp only [dif_pos hm]
          by_cases hym : m = y.val
          · subst hym; simp [Equiv.swap_apply_right, show (⟨m, hm⟩ : ↥(↑S : Set ℕ)) = y from Subtype.ext rfl,
                show (⟨x.val, hx_mem⟩ : ↥(↑S : Set ℕ)) = x from Subtype.ext rfl]
          · by_cases hxm : m = x.val
            · subst hxm; simp [hym, Equiv.swap_apply_left, show (⟨m, hm⟩ : ↥(↑S : Set ℕ)) = x from Subtype.ext rfl,
                show (⟨y.val, hy_mem⟩ : ↥(↑S : Set ℕ)) = y from Subtype.ext rfl]
            · have hne_x : (⟨m, hm⟩ : ↥(↑S : Set ℕ)) ≠ x := fun h => hxm (congr_arg Subtype.val h)
              have hne_y : (⟨m, hm⟩ : ↥(↑S : Set ℕ)) ≠ y := fun h => hym (congr_arg Subtype.val h)
              simp only [hxm, hym, ite_false, Equiv.swap_apply_of_ne_of_ne hne_x hne_y]
        · simp only [dif_neg hm]
          have hxm : m ≠ x.val := fun h => hm (h ▸ hx_mem)
          have hym : m ≠ y.val := fun h => hm (h ▸ hy_mem)
          simp only [hxm, hym, ite_false]
      suffices ∃ e : ↥(rowVisitCylinderEventUpToPrefixCarrier (k := k) i S v N) ≃
            ↥(rowVisitCylinderEventUpToPrefixCarrier (k := k) i S
              (fun m => if m = y.val then (val_of τ) x.val
                else if m = x.val then (val_of τ) y.val else (val_of τ) m) N),
          ∀ xs, evidenceOf (n := N) xs.1 = evidenceOf (n := N) (e xs).1 by rwa [htarget] at this
      exact ⟨e_τ.trans e_sw, fun xs => (he_τ xs).trans (he_sw (e_τ xs))⟩

/-- Carrier equiv for Fin n' permutation on S = range(n'+2).
Swap induction on Perm (Fin n') guarantees all transpositions (x,y) satisfy
x.val, y.val < n', so y.val+1 ≤ n' < n'+2, ensuring hrange for carrier_equiv_swap.
This avoids the boundary bug in carrier_equiv_of_value_perm. -/
private theorem carrier_equiv_of_fin_perm {N n' : ℕ}
    (i : Fin k) (v : ℕ → Fin k) (σ' : Equiv.Perm (Fin n')) :
    let val_of (τ : Equiv.Perm (Fin n')) : ℕ → Fin k :=
      fun m => if h : m < n' then v (↑(τ ⟨m, h⟩)) else v m
    ∃ e : ↥(rowVisitCylinderEventUpToPrefixCarrier (k := k) i
              (Finset.range (n' + 2)) v N) ≃
          ↥(rowVisitCylinderEventUpToPrefixCarrier (k := k) i
              (Finset.range (n' + 2)) (val_of σ') N),
      ∀ xs, evidenceOf (n := N) xs.1 = evidenceOf (n := N) (e xs).1 := by
  intro val_of
  suffices ∀ τ : Equiv.Perm (Fin n'),
      ∃ e : ↥(rowVisitCylinderEventUpToPrefixCarrier (k := k) i
                (Finset.range (n' + 2)) v N) ≃
            ↥(rowVisitCylinderEventUpToPrefixCarrier (k := k) i
                (Finset.range (n' + 2)) (val_of τ) N),
        ∀ xs, evidenceOf (n := N) xs.1 = evidenceOf (n := N) (e xs).1 from this σ'
  intro τ; refine τ.swap_induction_on' ?_ ?_
  · have h1 : val_of 1 = v := by funext m; simp [val_of]
    rw [h1]; exact ⟨Equiv.refl _, fun _ => rfl⟩
  · intro τ₀ x y hxy ⟨e₀, he₀⟩
    -- val_of(τ₀ * swap x y) = swap(val_of τ₀, min, max)
    -- carrier_equiv_swap for each orientation
    have htarget_eq : ∀ (a b : Fin n'), a.val < b.val →
        (fun m => if m = a.val then (val_of τ₀) b.val
          else if m = b.val then (val_of τ₀) a.val
          else (val_of τ₀) m) = val_of (τ₀ * Equiv.swap a b) := by
      intro a b _; funext m; simp only [val_of, Equiv.Perm.mul_apply]
      by_cases hm : m < n'
      · simp only [dif_pos hm]
        by_cases ham : m = a.val
        · subst ham; simp [Equiv.swap_apply_left,
            show (⟨m, hm⟩ : Fin n') = a from Fin.ext rfl]
        · by_cases hbm : m = b.val
          · subst hbm; simp [ham, Equiv.swap_apply_right,
              show (⟨m, hm⟩ : Fin n') = b from Fin.ext rfl]
          · simp only [ham, ite_false, hbm, Equiv.swap_apply_of_ne_of_ne
              (show (⟨m, hm⟩ : Fin n') ≠ a from fun h => ham (congr_arg Fin.val h))
              (show (⟨m, hm⟩ : Fin n') ≠ b from fun h => hbm (congr_arg Fin.val h))]
      · simp only [dif_neg hm]; simp [show m ≠ a.val from fun h => hm (h ▸ a.isLt),
          show m ≠ b.val from fun h => hm (h ▸ b.isLt)]
    rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hxy) with hab | hab
    · rcases carrier_equiv_swap (N := N) i (Finset.range (n' + 2)) (val_of τ₀)
          x.val y.val hab (fun m hm1 hm2 => Finset.mem_range.mpr (by omega))
        with ⟨e_sw, he_sw⟩
      rw [← htarget_eq x y hab]
      exact ⟨e₀.trans e_sw, fun xs => (he₀ xs).trans (he_sw (e₀ xs))⟩
    · rcases carrier_equiv_swap (N := N) i (Finset.range (n' + 2)) (val_of τ₀)
          y.val x.val hab (fun m hm1 hm2 => Finset.mem_range.mpr (by omega))
        with ⟨e_sw, he_sw⟩
      rw [show Equiv.swap x y = Equiv.swap y x from Equiv.swap_comm x y,
          ← htarget_eq y x hab]
      exact ⟨e₀.trans e_sw, fun xs => (he₀ xs).trans (he_sw (e₀ xs))⟩

/-- Per-start-state equality for the row process preimage under permutation,
assuming only the row-specific recurrence needed for the fixed row `i`. -/
theorem measure_start_inter_rsp_preimage_eq_of_rowRecurrence
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (hExt : ∀ xs : List (Fin k), μ xs = P (MarkovDeFinettiRecurrence.cylinder (k := k) xs))
    (i : Fin k)
    (hRowRec :
      ∀ᵐ ω ∂P, (∃ t, ω t = i) → ∀ n,
        nthVisitTimeExists (k := k) ω i n)
    (n' : ℕ) (σ' : Equiv.Perm (Fin n')) (c : Fin n' → Fin k)
    (j : Fin k) :
    P ({ω | ω 0 = j} ∩
        (fun ω (m : Fin n') => rowSuccessorVisitProcess (k := k) i ω ↑(σ' m)) ⁻¹' {c}) =
    P ({ω | ω 0 = j} ∩
        (fun ω (m : Fin n') => rowSuccessorVisitProcess (k := k) i ω ↑m) ⁻¹' {c}) := by
  -- Guard-extended value functions
  let ext₁ : Fin k → Fin k → ℕ → Fin k := fun a b m =>
    if h : m < n' then c (σ'.symm ⟨m, h⟩)
    else if m = n' then a else if m = n' + 1 then b else i
  let ext₂ : Fin k → Fin k → ℕ → Fin k := fun a b m =>
    if h : m < n' then c ⟨m, h⟩
    else if m = n' then a else if m = n' + 1 then b else i
  -- carrier_equiv_of_fin_perm with ext₁ and σ' gives ext₂
  have hval_eq : ∀ a b : Fin k,
      (fun m => if h : m < n' then (ext₁ a b) (↑(σ' ⟨m, h⟩)) else (ext₁ a b) m) =
      ext₂ a b := by
    intro a b; funext m; simp only [ext₁, ext₂]
    by_cases hm : m < n'
    · simp only [dif_pos hm, dif_pos (σ' ⟨m, hm⟩).isLt,
        show ¬(↑(σ' ⟨m, hm⟩) = n') from by omega,
        show ¬(↑(σ' ⟨m, hm⟩) = n' + 1) from by omega, ite_false]
      simp [Equiv.symm_apply_apply]
    · simp [dif_neg hm]
  let S0 : Set (ℕ → Fin k) := {ω | ω 0 = j}
  let V : Set (ℕ → Fin k) := {ω | ∃ t, ω t = i}
  let S := Finset.range (n' + 2)
  -- Per-(a,b) V-piece equality: ⋃upTo equality from carrier equivs.
  have hPerN : ∀ (a b : Fin k) (N : ℕ),
      P (S0 ∩ rowVisitCylinderEventUpTo (k := k) i S (ext₁ a b) N) =
      P (S0 ∩ rowVisitCylinderEventUpTo (k := k) i S (ext₂ a b) N) := by
    intro a b N
    rcases carrier_equiv_of_fin_perm (k := k) (N := N) i (ext₁ a b) σ' with ⟨e₀, he₀⟩
    dsimp only [] at e₀ he₀
    rw [show ext₂ a b = (fun m => if h : m < n' then (ext₁ a b) ↑(σ' ⟨m, h⟩)
        else (ext₁ a b) m) from (hval_eq a b).symm]
    exact measure_start_inter_rowVisitCylinderEventUpTo_eq_of_evidencePreservingEquiv_start
      (k := k) μ hμ P hExt i S (ext₁ a b) i S _ N j e₀ he₀
  -- V-piece ⋃upTo equality (per a, b)
  have hUpTo : ∀ a b : Fin k,
      P (S0 ∩ ⋃ N, rowVisitCylinderEventUpTo (k := k) i S (ext₁ a b) N) =
      P (S0 ∩ ⋃ N, rowVisitCylinderEventUpTo (k := k) i S (ext₂ a b) N) := by
    intro a b
    have hmono₁ : Monotone (fun N => S0 ∩ rowVisitCylinderEventUpTo (k := k) i S (ext₁ a b) N) :=
      fun N M h ω ⟨h1, h2⟩ => ⟨h1, rowVisitCylinderEventUpTo_mono' i S (ext₁ a b) h h2⟩
    have hmono₂ : Monotone (fun N => S0 ∩ rowVisitCylinderEventUpTo (k := k) i S (ext₂ a b) N) :=
      fun N M h ω ⟨h1, h2⟩ => ⟨h1, rowVisitCylinderEventUpTo_mono' i S (ext₂ a b) h h2⟩
    rw [Set.inter_iUnion, Set.inter_iUnion]
    rw [hmono₁.measure_iUnion, hmono₂.measure_iUnion]
    exact iSup_congr (hPerN a b)
  -- V-piece JRE equality (per a, b) via measure_JRE_inter_V_eq_upTo
  have hS_ne : S.Nonempty := ⟨0, Finset.mem_range.mpr (by omega)⟩
  have hV_eq : ∀ a b : Fin k,
      P (S0 ∩ jointRowSuccEvent (k := k) i S (ext₁ a b) ∩ V) =
      P (S0 ∩ jointRowSuccEvent (k := k) i S (ext₂ a b) ∩ V) := by
    intro a b
    rw [measure_JRE_inter_V_eq_upTo_of_rowRecurrence P i hRowRec S0 S (ext₁ a b) hS_ne,
        measure_JRE_inter_V_eq_upTo_of_rowRecurrence P i hRowRec S0 S (ext₂ a b) hS_ne]
    exact hUpTo a b
  -- NV-piece JRE equality (per a, b): on NV, rsp defaults to i, so both sides equal
  have hNV_eq : ∀ a b : Fin k,
      P (S0 ∩ jointRowSuccEvent (k := k) i S (ext₁ a b) ∩ Vᶜ) =
      P (S0 ∩ jointRowSuccEvent (k := k) i S (ext₂ a b) ∩ Vᶜ) := by
    intro a b; congr 1; ext ω
    -- Helper: on NV, all rsp values are i
    have hall_i : ω ∈ Vᶜ → ∀ n, rowSuccessorAtNthVisit (k := k) i n ω = i := by
      intro hNV n; simp only [rowSuccessorAtNthVisit]
      cases hn : nthVisitTime (k := k) ω i n with
      | none => rfl
      | some t => exact absurd ⟨t, ((nthVisitTime_eq_some_iff (k := k) ω i n t).mp hn).1⟩ hNV
    -- Helper: on NV, JRE membership forces the value function to be constant i on S
    have hJRE_forces : ∀ (v : ℕ → Fin k),
        ω ∈ Vᶜ → ω ∈ jointRowSuccEvent (k := k) i S v → ∀ m' ∈ S, v m' = i := by
      intro v hNV hJRE m' hm'
      have hmem := Set.mem_iInter₂.mp hJRE m' hm'
      simp only [rowSuccessorValueEvent, Set.mem_setOf_eq] at hmem
      rw [hall_i hNV m'] at hmem; exact hmem.symm
    -- Helper: if all c values are i, then both ext₁ and ext₂ are i on S
    have hc_all_i_imp : (∀ q : Fin n', c q = i) → ∀ (a' b' : Fin k),
        a' = i → b' = i → ∀ m' ∈ S, ext₁ a' b' m' = i ∧ ext₂ a' b' m' = i := by
      intro hc a' b' ha hb m' hm'
      simp only [ext₁, ext₂]
      constructor
      · by_cases hm'1 : m' < n'
        · simp [dif_pos hm'1, hc]
        · simp only [dif_neg hm'1]; split_ifs with h1 h2 <;> first | exact ha | exact hb | rfl
      · by_cases hm'1 : m' < n'
        · simp [dif_pos hm'1, hc]
        · simp only [dif_neg hm'1]; split_ifs with h1 h2 <;> first | exact ha | exact hb | rfl
    constructor
    · -- mp: ext₁ membership → ext₂ membership
      intro ⟨⟨hS0, hJRE⟩, hNV⟩
      refine ⟨⟨hS0, Set.mem_iInter₂.mpr fun m hm => ?_⟩, hNV⟩
      simp only [rowSuccessorValueEvent, Set.mem_setOf_eq]
      rw [hall_i hNV m]
      -- ext₁ forced to i on S; derive c is constant i; then ext₂ is i
      have hf1 := hJRE_forces (ext₁ a b) hNV hJRE
      have hc_i : ∀ q : Fin n', c q = i := by
        intro q
        have hσqS : (σ' q : ℕ) ∈ S := Finset.mem_range.mpr (by omega)
        have h1 := hf1 (σ' q) hσqS
        simp only [ext₁, dif_pos (σ' q).isLt] at h1
        have : (⟨(σ' q).val, (σ' q).isLt⟩ : Fin n') = σ' q := Fin.ext rfl
        rw [this, Equiv.symm_apply_apply] at h1
        exact h1
      exact ((hc_all_i_imp hc_i a b
        (by have := hf1 n' (Finset.mem_range.mpr (by omega)); simp only [ext₁, dif_neg (lt_irrefl n'), ite_true] at this; exact this)
        (by have := hf1 (n' + 1) (Finset.mem_range.mpr (by omega)); simp only [ext₁, dif_neg (by omega : ¬(n' + 1 < n')), show ¬(n' + 1 = n') from by omega, ite_false, ite_true] at this; exact this)
        m hm).2).symm
    · -- mpr: ext₂ membership → ext₁ membership
      intro ⟨⟨hS0, hJRE⟩, hNV⟩
      refine ⟨⟨hS0, Set.mem_iInter₂.mpr fun m hm => ?_⟩, hNV⟩
      simp only [rowSuccessorValueEvent, Set.mem_setOf_eq]
      rw [hall_i hNV m]
      have hf2 := hJRE_forces (ext₂ a b) hNV hJRE
      have hc_i : ∀ q : Fin n', c q = i := by
        intro q
        have hqS : (q : ℕ) ∈ S := Finset.mem_range.mpr (by omega)
        have := hf2 q hqS
        simp only [ext₂, dif_pos q.isLt] at this
        exact this
      exact ((hc_all_i_imp hc_i a b
        (by have := hf2 n' (Finset.mem_range.mpr (by omega)); simp only [ext₂, dif_neg (lt_irrefl n'), ite_true] at this; exact this)
        (by have := hf2 (n' + 1) (Finset.mem_range.mpr (by omega)); simp only [ext₂, dif_neg (by omega : ¬(n' + 1 < n')), show ¬(n' + 1 = n') from by omega, ite_false, ite_true] at this; exact this)
        m hm).1).symm
  -- Assembly: combine V-piece + NV-piece via guard marginalization.
  set E₁ := (fun ω (j : Fin n') => rowSuccessorVisitProcess (k := k) i ω ↑(σ' j)) ⁻¹' {c}
  set E₂ := (fun ω (j : Fin n') => rowSuccessorVisitProcess (k := k) i ω ↑j) ⁻¹' {c}
  -- Key: on NV, both preimages reduce to {ω | ∀ j, i = c j}, so E₁ ∩ Vᶜ = E₂ ∩ Vᶜ
  have hNV_preimage : S0 ∩ E₁ ∩ Vᶜ = S0 ∩ E₂ ∩ Vᶜ := by
    ext ω; constructor <;> intro ⟨⟨hS0, hE⟩, hNV⟩ <;> refine ⟨⟨hS0, ?_⟩, hNV⟩
    all_goals {
      simp only [E₁, E₂, Set.mem_preimage, Set.mem_singleton_iff, rowSuccessorVisitProcess] at hE ⊢
      ext q
      have hall_i : ∀ n, rowSuccessorAtNthVisit (k := k) i n ω = i := by
        intro n; simp only [rowSuccessorAtNthVisit]
        cases hn : nthVisitTime (k := k) ω i n with
        | none => rfl
        | some t => exact absurd ⟨t, ((nthVisitTime_eq_some_iff (k := k) ω i n t).mp hn).1⟩ hNV
      -- Both preimages force rsvp = i at all indices, so c q = i for all q
      have : ∀ (q : Fin n'), c q = i := by
        intro q
        have hq := congr_fun hE q
        simp only [hall_i] at hq; exact hq.symm
      simp [hall_i, this q] }
  -- Key: on V, use guard marginalization to reduce to hV_eq
  have hE₁_guard : E₁ = ⋃ a : Fin k, ⋃ b : Fin k, jointRowSuccEvent (k := k) i S (ext₁ a b) := by
    ext ω
    simp only [E₁, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iUnion,
      jointRowSuccEvent, Set.mem_iInter, rowSuccessorValueEvent, Set.mem_setOf_eq,
      rowSuccessorVisitProcess]
    constructor
    · intro hE
      refine ⟨rowSuccessorAtNthVisit (k := k) i n' ω,
              rowSuccessorAtNthVisit (k := k) i (n' + 1) ω,
              fun m hm => ?_⟩
      have hmS := Finset.mem_range.mp hm
      by_cases hm1 : m < n'
      · simp only [ext₁, dif_pos hm1]
        have := congr_fun hE (σ'.symm ⟨m, hm1⟩)
        simp only [Equiv.apply_symm_apply] at this; exact this
      · simp only [ext₁, dif_neg hm1]
        by_cases hm2 : m = n'
        · subst hm2; simp
        · by_cases hm3 : m = n' + 1
          · subst hm3; simp
          · omega
    · intro ⟨a', b', hJRE⟩
      show (fun j => rowSuccessorAtNthVisit (k := k) i (↑(σ' j)) ω) = c
      funext q
      have := hJRE (↑(σ' q)) (Finset.mem_range.mpr (by omega))
      simp only [ext₁, dif_pos (σ' q).isLt] at this
      have hfin : (⟨(σ' q).val, (σ' q).isLt⟩ : Fin n') = σ' q := Fin.ext rfl
      rw [hfin, Equiv.symm_apply_apply] at this; exact this
  have hE₂_guard : E₂ = ⋃ a : Fin k, ⋃ b : Fin k, jointRowSuccEvent (k := k) i S (ext₂ a b) := by
    ext ω
    simp only [E₂, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iUnion,
      jointRowSuccEvent, Set.mem_iInter, rowSuccessorValueEvent, Set.mem_setOf_eq,
      rowSuccessorVisitProcess]
    constructor
    · intro hE
      refine ⟨rowSuccessorAtNthVisit (k := k) i n' ω,
              rowSuccessorAtNthVisit (k := k) i (n' + 1) ω,
              fun m hm => ?_⟩
      have hmS := Finset.mem_range.mp hm
      by_cases hm1 : m < n'
      · simp only [ext₂, dif_pos hm1]; exact congr_fun hE ⟨m, hm1⟩
      · simp only [ext₂, dif_neg hm1]
        by_cases hm2 : m = n'
        · subst hm2; simp
        · by_cases hm3 : m = n' + 1
          · subst hm3; simp
          · omega
    · intro ⟨a', b', hJRE⟩
      ext ⟨q, hq⟩
      exact hJRE q (Finset.mem_range.mpr (by omega)) |>.symm ▸ by
        simp only [ext₂, dif_pos hq]
  -- Per-term full equality via V/NV decomposition
  have hV_meas : MeasurableSet V := by
    show MeasurableSet {ω : ℕ → Fin k | ∃ t, ω t = i}
    rw [show {ω : ℕ → Fin k | ∃ t, ω t = i} =
        ⋃ t, (fun (f : ℕ → Fin k) => f t) ⁻¹' {i} from by ext ω; simp]
    exact MeasurableSet.iUnion fun t => measurable_pi_apply t (measurableSet_singleton i)
  have hPerTerm : ∀ a b : Fin k,
      P (S0 ∩ jointRowSuccEvent (k := k) i S (ext₁ a b)) =
      P (S0 ∩ jointRowSuccEvent (k := k) i S (ext₂ a b)) := by
    intro a b
    have h1 := @measure_inter_add_diff _ _ P V (S0 ∩ jointRowSuccEvent (k := k) i S (ext₁ a b)) hV_meas
    have h2 := @measure_inter_add_diff _ _ P V (S0 ∩ jointRowSuccEvent (k := k) i S (ext₂ a b)) hV_meas
    rw [Set.diff_eq] at h1 h2
    rw [← h1, ← h2, hV_eq a b, hNV_eq a b]
  -- Guard marginalization: the JRE(S, ext a b) for different a are disjoint
  have hJRE_disj : ∀ (ext : Fin k → Fin k → ℕ → Fin k),
      (∀ (a : Fin k) (b : Fin k), ext a b n' = a) →
      Pairwise (Function.onFun Disjoint fun a =>
        S0 ∩ ⋃ b, jointRowSuccEvent (k := k) i S (ext a b)) := by
    intro ext hext a₁ a₂ ha₁₂
    rw [Function.onFun, Set.disjoint_left]
    intro ω ⟨_, h1⟩ ⟨_, h2⟩
    rw [Set.mem_iUnion] at h1 h2
    rcases h1 with ⟨b₁, hb₁⟩; rcases h2 with ⟨b₂, hb₂⟩
    have hmem₁ := Set.mem_iInter₂.mp hb₁ n' (Finset.mem_range.mpr (by omega))
    have hmem₂ := Set.mem_iInter₂.mp hb₂ n' (Finset.mem_range.mpr (by omega))
    simp only [rowSuccessorValueEvent, Set.mem_setOf_eq] at hmem₁ hmem₂
    rw [hext a₁ b₁] at hmem₁; rw [hext a₂ b₂] at hmem₂
    exact ha₁₂ (hmem₁ ▸ hmem₂)
  have hext₁_n' : ∀ a b : Fin k, ext₁ a b n' = a := by
    intro a b; simp [ext₁]
  have hext₂_n' : ∀ a b : Fin k, ext₂ a b n' = a := by
    intro a b; simp [ext₂]
  -- Measurability of JRE terms
  have hJRE_meas : ∀ (ext : Fin k → Fin k → ℕ → Fin k) (a : Fin k),
      MeasurableSet (S0 ∩ ⋃ b, jointRowSuccEvent (k := k) i S (ext a b)) := by
    intro ext a
    apply MeasurableSet.inter
    · change MeasurableSet {ω : ℕ → Fin k | ω 0 = j}
      rw [show {ω : ℕ → Fin k | ω 0 = j} = (fun f : ℕ → Fin k => f 0) ⁻¹' {j} from by
        ext ω; simp]
      exact measurable_pi_apply 0 (measurableSet_singleton j)
    · exact MeasurableSet.iUnion fun b => MeasurableSet.biInter (Finset.countable_toSet S) fun n _ =>
          measurableSet_rowSuccessorValueEvent (k := k) i n (ext a b n)
  rw [hE₁_guard, hE₂_guard, Set.inter_iUnion, Set.inter_iUnion]
  rw [measure_iUnion (hJRE_disj ext₁ hext₁_n') (hJRE_meas ext₁),
      measure_iUnion (hJRE_disj ext₂ hext₂_n') (hJRE_meas ext₂)]
  congr 1; ext a
  -- For inner union over b: also disjoint (different b at index n'+1)
  have hJRE_disj_b : ∀ (ext : Fin k → Fin k → ℕ → Fin k) (a : Fin k),
      (∀ b : Fin k, ext a b (n' + 1) = b) →
      Pairwise (Function.onFun Disjoint fun b =>
        S0 ∩ jointRowSuccEvent (k := k) i S (ext a b)) := by
    intro ext a hext b₁ b₂ hb₁₂
    rw [Function.onFun, Set.disjoint_left]
    intro ω ⟨_, hb₁⟩ ⟨_, hb₂⟩
    have hmem₁ := Set.mem_iInter₂.mp hb₁ (n' + 1) (Finset.mem_range.mpr (by omega))
    have hmem₂ := Set.mem_iInter₂.mp hb₂ (n' + 1) (Finset.mem_range.mpr (by omega))
    simp only [rowSuccessorValueEvent, Set.mem_setOf_eq] at hmem₁ hmem₂
    rw [hext b₁] at hmem₁; rw [hext b₂] at hmem₂
    exact hb₁₂ (hmem₁ ▸ hmem₂)
  have hext₁_n1 : ∀ a b : Fin k, ext₁ a b (n' + 1) = b := by
    intro a b; simp [ext₁, show ¬(n' + 1 < n') from by omega]
  have hext₂_n1 : ∀ a b : Fin k, ext₂ a b (n' + 1) = b := by
    intro a b; simp [ext₂, show ¬(n' + 1 < n') from by omega]
  have hJRE_meas_b : ∀ (ext : Fin k → Fin k → ℕ → Fin k) (a b : Fin k),
      MeasurableSet (S0 ∩ jointRowSuccEvent (k := k) i S (ext a b)) := by
    intro ext a b
    apply MeasurableSet.inter
    · change MeasurableSet {ω : ℕ → Fin k | ω 0 = j}
      rw [show {ω : ℕ → Fin k | ω 0 = j} = (fun f : ℕ → Fin k => f 0) ⁻¹' {j} from by
        ext ω; simp]
      exact measurable_pi_apply 0 (measurableSet_singleton j)
    · exact MeasurableSet.biInter (Finset.countable_toSet S) fun n _ =>
          measurableSet_rowSuccessorValueEvent (k := k) i n (ext a b n)
  rw [show S0 ∩ ⋃ b, jointRowSuccEvent (k := k) i S (ext₁ a b) =
        ⋃ b, S0 ∩ jointRowSuccEvent (k := k) i S (ext₁ a b) from Set.inter_iUnion _ _,
      show S0 ∩ ⋃ b, jointRowSuccEvent (k := k) i S (ext₂ a b) =
        ⋃ b, S0 ∩ jointRowSuccEvent (k := k) i S (ext₂ a b) from Set.inter_iUnion _ _,
      measure_iUnion (hJRE_disj_b ext₁ a (hext₁_n1 a)) (fun b => hJRE_meas_b ext₁ a b),
      measure_iUnion (hJRE_disj_b ext₂ a (hext₂_n1 a)) (fun b => hJRE_meas_b ext₂ a b)]
  congr 1; ext b
  exact hPerTerm a b

/-- Per-start-state equality for the row process preimage under permutation.
For each start state `j`, the measure of `{ω₀=j} ∩ f⁻¹'{c}` is the same
whether `f` permutes visit indices via `σ'` or uses identity indexing.

This is the core per-`j` step in `exchangeable_rowProcess`, extracted as a
reusable lemma for the restricted version `exchangeable_rowProcess_restrict`. -/
theorem measure_start_inter_rsp_preimage_eq
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (hExt : ∀ xs : List (Fin k), μ xs = P (MarkovDeFinettiRecurrence.cylinder (k := k) xs))
    (hStrRec : MarkovDeFinettiHard.StrongRecurrence (k := k) P)
    (i : Fin k) (n' : ℕ) (σ' : Equiv.Perm (Fin n')) (c : Fin n' → Fin k)
    (j : Fin k) :
    P ({ω | ω 0 = j} ∩
        (fun ω (m : Fin n') => rowSuccessorVisitProcess (k := k) i ω ↑(σ' m)) ⁻¹' {c}) =
    P ({ω | ω 0 = j} ∩
        (fun ω (m : Fin n') => rowSuccessorVisitProcess (k := k) i ω ↑m) ⁻¹' {c}) := by
  exact
    measure_start_inter_rsp_preimage_eq_of_rowRecurrence
      (k := k) μ hμ P hExt i (hStrRec i) n' σ' c j

/-- Constant-anchor specialization of `measure_start_inter_rsp_preimage_eq`
rephrased through `multiRowSelectionMap`.

This is the first bridge theorem toward finite multi-row selection events:
it upgrades the existing per-row statement to the new tuple-valued interface
without yet attempting mixed anchors. -/
theorem measure_start_inter_multiRowSelectionMap_const_preimage_eq
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (hExt : ∀ xs : List (Fin k), μ xs = P (MarkovDeFinettiRecurrence.cylinder (k := k) xs))
    (hStrRec : MarkovDeFinettiHard.StrongRecurrence (k := k) P)
    (i : Fin k) (n' : ℕ) (σ' : Equiv.Perm (Fin n')) (c : Fin n' → Fin k)
    (j : Fin k) :
    P ({ω | ω 0 = j} ∩
        (multiRowSelectionMap (k := k) (fun _ : Fin n' => i)
          (fun m : Fin n' => ↑(σ' m))) ⁻¹' {c}) =
    P ({ω | ω 0 = j} ∩
        (multiRowSelectionMap (k := k) (fun _ : Fin n' => i)
          (fun m : Fin n' => ↑m)) ⁻¹' {c}) := by
  exact measure_start_inter_rsp_preimage_eq (k := k) μ hμ P hExt hStrRec i n' σ' c j

/-- One-fiber restricted-start invariance for mixed finite selection maps,
assuming the selected fiber is already enumerated by visit indices `0, ..., n-1`.

Positive example: this applies to word-level successor tuples once we prove the
corresponding anchor-fiber enumeration lemma.
Negative example: without `hidx`, the theorem is false as stated from the
current per-row infrastructure alone. -/
theorem measure_start_inter_anchorFiberSelectionMap_perm_eq_of_idx_eq_enum
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (hExt : ∀ xs : List (Fin k), μ xs = P (MarkovDeFinettiRecurrence.cylinder (k := k) xs))
    (hStrRec : MarkovDeFinettiHard.StrongRecurrence (k := k) P)
    {m : ℕ} (anchor : Fin m → Fin k) (idx : Fin m → ℕ) (i : Fin k)
    (hidx :
      ∀ t : Fin (anchorFiber (k := k) anchor i).card,
        idx (((anchorFiber (k := k) anchor i).equivFin.symm t).1) = t)
    (σ' : Equiv.Perm (Fin (anchorFiber (k := k) anchor i).card))
    (c : Fin (anchorFiber (k := k) anchor i).card → Fin k)
    (j : Fin k) :
    P ({ω | ω 0 = j} ∩
        (fun ω (t : Fin (anchorFiber (k := k) anchor i).card) =>
          anchorFiberSelectionMap (k := k) anchor idx i ω (σ' t)) ⁻¹' {c}) =
    P ({ω | ω 0 = j} ∩
        (fun ω (t : Fin (anchorFiber (k := k) anchor i).card) =>
          anchorFiberSelectionMap (k := k) anchor idx i ω t) ⁻¹' {c}) := by
  rw [anchorFiberSelectionMap_eq_const (k := k) anchor idx i]
  simp only [hidx]
  exact
    measure_start_inter_multiRowSelectionMap_const_preimage_eq
      (k := k) μ hμ P hExt hStrRec i
      (anchorFiber (k := k) anchor i).card σ' c j

/-- Ordered-fiber restricted-start invariance for mixed finite selection maps,
assuming the selected fiber is enumerated by visit indices `0, ..., n-1` in the
ambient left-to-right order.

Positive example: this is the exact interface needed for word-level successor
tuples.
Negative example: without `hidx`, permuting arbitrary ordered coordinates in a
fiber is not justified by the current per-row infrastructure. -/
theorem measure_start_inter_anchorFiberSelectionMapList_perm_eq_of_idx_eq_enum
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (hExt : ∀ xs : List (Fin k), μ xs = P (MarkovDeFinettiRecurrence.cylinder (k := k) xs))
    (hStrRec : MarkovDeFinettiHard.StrongRecurrence (k := k) P)
    {m : ℕ} (anchor : Fin m → Fin k) (idx : Fin m → ℕ) (i : Fin k)
    (hidx :
      ∀ t : Fin (anchorFiberList (k := k) anchor i).length,
        idx ((anchorFiberList (k := k) anchor i)[t]) = t)
    (σ' : Equiv.Perm (Fin (anchorFiberList (k := k) anchor i).length))
    (c : Fin (anchorFiberList (k := k) anchor i).length → Fin k)
    (j : Fin k) :
    P ({ω | ω 0 = j} ∩
        (fun ω (t : Fin (anchorFiberList (k := k) anchor i).length) =>
          anchorFiberSelectionMapList (k := k) anchor idx i ω (σ' t)) ⁻¹' {c}) =
    P ({ω | ω 0 = j} ∩
        (fun ω (t : Fin (anchorFiberList (k := k) anchor i).length) =>
          anchorFiberSelectionMapList (k := k) anchor idx i ω t) ⁻¹' {c}) := by
  have hconst :
      multiRowSelectionMap (k := k)
          (fun _ : Fin (anchorFiberList (k := k) anchor i).length => i)
          (fun t : Fin (anchorFiberList (k := k) anchor i).length =>
            idx ((anchorFiberList (k := k) anchor i)[t])) =
        multiRowSelectionMap (k := k)
          (fun _ : Fin (anchorFiberList (k := k) anchor i).length => i)
          (fun t : Fin (anchorFiberList (k := k) anchor i).length => ↑t) := by
    funext ω t
    simp only [multiRowSelectionMap, hidx]
  rw [anchorFiberSelectionMapList_eq_const (k := k) anchor idx i, hconst]
  exact
    measure_start_inter_multiRowSelectionMap_const_preimage_eq
      (k := k) μ hμ P hExt hStrRec i
      (anchorFiberList (k := k) anchor i).length σ' c j

/-- Contiguous-head-block specialization:
inside a mixed finite selection map, permuting the indices of a single head
block in row `i` and then projecting back to that block gives the same
start-restricted preimage measure as the identity order. This is the strongest
mixed-block statement that currently reduces directly to the per-row theorem
`measure_start_inter_multiRowSelectionMap_const_preimage_eq`. -/
theorem measure_start_inter_mixedHeadBlockSelectionMap_head_preimage_eq
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (hExt : ∀ xs : List (Fin k), μ xs = P (MarkovDeFinettiRecurrence.cylinder (k := k) xs))
    (hStrRec : MarkovDeFinettiHard.StrongRecurrence (k := k) P)
    (i : Fin k) (n' r : ℕ) (σ' : Equiv.Perm (Fin n'))
    (tailAnchor : Fin r → Fin k) (tailIdx : Fin r → ℕ)
    (c : Fin n' → Fin k) (j : Fin k) :
    P ({ω | ω 0 = j} ∩
        (fun ω (m : Fin n') =>
          mixedHeadBlockSelectionMap (k := k) i (fun t : Fin n' => ↑(σ' t))
            tailAnchor tailIdx ω (Fin.castAdd r m)) ⁻¹' {c}) =
    P ({ω | ω 0 = j} ∩
        (fun ω (m : Fin n') =>
          mixedHeadBlockSelectionMap (k := k) i (fun t : Fin n' => ↑t)
            tailAnchor tailIdx ω (Fin.castAdd r m)) ⁻¹' {c}) := by
  simpa [mixedHeadBlockSelectionMap_comp_castAdd] using
    measure_start_inter_multiRowSelectionMap_const_preimage_eq
      (k := k) μ hμ P hExt hStrRec i n' σ' c j

/-- `wordSuccessorTupleMap` is a concrete mixed-anchor instance of
`multiRowSelectionMap`. -/
lemma wordSuccessorTupleMap_eq_multiRowSelectionMap
    (a : Fin k) (ys : List (Fin k)) :
    wordSuccessorTupleMap (k := k) a ys =
      multiRowSelectionMap (k := k)
        (fun j : Fin ys.length => (a :: ys).getD j.1 a)
        (fun j : Fin ys.length => wordVisitIndex (k := k) (a :: ys) a j.1) := by
  funext ω j
  simp [wordSuccessorTupleMap, multiRowSelectionMap, rowSuccessorVisitProcess]

lemma wordAnchorFiberList_eq_anchorFiberList
    (a : Fin k) (ys : List (Fin k)) (i : Fin k) :
    wordAnchorFiberList (k := k) a ys i =
      anchorFiberList (k := k)
        (fun j : Fin ys.length => (a :: ys).getD j.1 a) i := rfl

lemma wordSuccessorTupleMap_eq_anchorFiberSelectionMapList
    (a : Fin k) (ys : List (Fin k)) (i : Fin k)
    (ω : ℕ → Fin k)
    (t : Fin (wordAnchorFiberList (k := k) a ys i).length) :
    anchorFiberSelectionMapList (k := k)
      (fun j : Fin ys.length => (a :: ys).getD j.1 a)
      (fun j : Fin ys.length => wordVisitIndex (k := k) (a :: ys) a j.1)
      i ω t =
      wordSuccessorTupleMap (k := k) a ys ω
        ((wordAnchorFiberList (k := k) a ys i)[t]) := by
  rw [wordSuccessorTupleMap_eq_multiRowSelectionMap (k := k) a ys]
  rfl

/-- First honest word-fiber permutation invariance result:
within a fixed anchor row `i`, permuting the ordered coordinates of
`wordSuccessorTupleMap` preserves the corresponding start-restricted singleton
preimage measure. -/
theorem measure_start_inter_wordSuccessorTupleMap_wordAnchorFiber_perm_eq
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (hExt : ∀ xs : List (Fin k), μ xs = P (MarkovDeFinettiRecurrence.cylinder (k := k) xs))
    (hStrRec : MarkovDeFinettiHard.StrongRecurrence (k := k) P)
    (a : Fin k) (ys : List (Fin k)) (i : Fin k)
    (σ' : Equiv.Perm (Fin (wordAnchorFiberList (k := k) a ys i).length))
    (c : Fin (wordAnchorFiberList (k := k) a ys i).length → Fin k)
    (j : Fin k) :
    P ({ω | ω 0 = j} ∩
        (fun ω (t : Fin (wordAnchorFiberList (k := k) a ys i).length) =>
          wordSuccessorTupleMap (k := k) a ys ω
            ((wordAnchorFiberList (k := k) a ys i)[σ' t])) ⁻¹' {c}) =
    P ({ω | ω 0 = j} ∩
        (fun ω (t : Fin (wordAnchorFiberList (k := k) a ys i).length) =>
          wordSuccessorTupleMap (k := k) a ys ω
            ((wordAnchorFiberList (k := k) a ys i)[t])) ⁻¹' {c}) := by
  exact
    measure_start_inter_anchorFiberSelectionMapList_perm_eq_of_idx_eq_enum
      (k := k) μ hμ P hExt hStrRec
      (anchor := fun j : Fin ys.length => (a :: ys).getD j.1 a)
      (idx := fun j : Fin ys.length => wordVisitIndex (k := k) (a :: ys) a j.1)
      i
      (hidx := Mettapedia.Logic.MarkovDeFinettiHard.wordVisitIndex_getElem_wordAnchorFiberList
        (k := k) a ys i)
      σ' c j

/-- The target tuple obtained by restricting the full word successor tuple to
the ordered anchor fiber for row `i`. -/
def wordAnchorFiberTarget
    (a : Fin k) (ys : List (Fin k)) (i : Fin k) :
    Fin (wordAnchorFiberList (k := k) a ys i).length → Fin k :=
  fun t => wordSuccessorTuple (k := k) a ys
    ((wordAnchorFiberList (k := k) a ys i)[t])

/-- Projected word-fiber invariance specialized to the cylinder word's own
target tuple. This is the first honest "projected cylinder" measure identity. -/
theorem measure_start_inter_wordAnchorFiberTarget_perm_eq
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (hExt : ∀ xs : List (Fin k), μ xs = P (MarkovDeFinettiRecurrence.cylinder (k := k) xs))
    (hStrRec : MarkovDeFinettiHard.StrongRecurrence (k := k) P)
    (a : Fin k) (ys : List (Fin k)) (i : Fin k)
    (σ' : Equiv.Perm (Fin (wordAnchorFiberList (k := k) a ys i).length))
    (j : Fin k) :
    P ({ω | ω 0 = j} ∩
        (fun ω (t : Fin (wordAnchorFiberList (k := k) a ys i).length) =>
          wordSuccessorTupleMap (k := k) a ys ω
            ((wordAnchorFiberList (k := k) a ys i)[σ' t])) ⁻¹'
          ({wordAnchorFiberTarget (k := k) a ys i} :
            Set (Fin (wordAnchorFiberList (k := k) a ys i).length → Fin k))) =
    P ({ω | ω 0 = j} ∩
        (fun ω (t : Fin (wordAnchorFiberList (k := k) a ys i).length) =>
          wordSuccessorTupleMap (k := k) a ys ω
            ((wordAnchorFiberList (k := k) a ys i)[t])) ⁻¹'
          ({wordAnchorFiberTarget (k := k) a ys i} :
            Set (Fin (wordAnchorFiberList (k := k) a ys i).length → Fin k))) := by
  simpa [wordAnchorFiberTarget] using
    measure_start_inter_wordSuccessorTupleMap_wordAnchorFiber_perm_eq
      (k := k) μ hμ P hExt hStrRec a ys i σ'
      (wordAnchorFiberTarget (k := k) a ys i) j

/-- The full-tuple event where the selected anchor fiber is constrained by `c`
and all complementary coordinates are fixed to the original word tuple.

This isolates the exact next theorem target after projected-fiber invariance:
show start-restricted invariance of the preimage of this set under permutations
of the selected fiber data. -/
def wordTupleFixedComplementSet
    (a : Fin k) (ys : List (Fin k)) (i : Fin k)
    (c : Fin (wordAnchorFiberList (k := k) a ys i).length → Fin k) :
    Set (Fin ys.length → Fin k) :=
  {u |
    (∀ t : Fin (wordAnchorFiberList (k := k) a ys i).length,
      u ((wordAnchorFiberList (k := k) a ys i)[t]) = c t) ∧
    ∀ j : Fin ys.length,
      (a :: ys).getD j.1 a ≠ i → u j = wordSuccessorTuple (k := k) a ys j}

/-- The finite trajectory determined by the word `a :: ys`. -/
def wordTraj
    (a : Fin k) (ys : List (Fin k)) :
    Traj k ys.length :=
  fun j => (a :: ys).getD j.1 a

/-- Prefix-level version of `wordSuccessorTupleMap`, obtained by evaluating the
mixed-row word query on the canonical infinite extension of a finite prefix. -/
def wordSuccessorTuplePrefixMap
    (a : Fin k) (ys : List (Fin k)) :
    Traj k ys.length → Fin ys.length → Fin k :=
  fun xs => wordSuccessorTupleMap (k := k) a ys (prefixExtend (k := k) ys.length xs)

/-- The finite set of length-`ys.length + 1` trajectories whose canonical
extension satisfies the mixed-row fixed-complement event. -/
def wordTupleFixedComplementTrajSet
    (a : Fin k) (ys : List (Fin k)) (i : Fin k)
    (c : Fin (wordAnchorFiberList (k := k) a ys i).length → Fin k) :
    Finset (Traj k ys.length) :=
  by
    classical
    exact (trajFinset k ys.length).filter fun xs =>
      wordSuccessorTuplePrefixMap (k := k) a ys xs ∈
        wordTupleFixedComplementSet (k := k) a ys i c

/-- The portion of a fixed evidence fiber corresponding to the mixed-row
fixed-complement event. This is the finite Route C object counted inside an
evidence class. -/
def wordTupleFixedComplementFiberSubset
    (a : Fin k) (ys : List (Fin k)) (i : Fin k)
    (c : Fin (wordAnchorFiberList (k := k) a ys i).length → Fin k)
    (eN : MarkovState k) :
    Finset (Traj k ys.length) :=
  by
    classical
    exact (fiber k ys.length eN).filter fun xs =>
      wordSuccessorTuplePrefixMap (k := k) a ys xs ∈
        wordTupleFixedComplementSet (k := k) a ys i c

lemma wordTupleFixedComplementFiberSubset_subset_fiber
    (a : Fin k) (ys : List (Fin k)) (i : Fin k)
    (c : Fin (wordAnchorFiberList (k := k) a ys i).length → Fin k)
    (eN : MarkovState k) :
    wordTupleFixedComplementFiberSubset (k := k) a ys i c eN ⊆ fiber k ys.length eN := by
  classical
  intro xs hxs
  exact (Finset.mem_filter.1 hxs).1

lemma mem_wordTupleFixedComplementTrajSet_iff
    (a : Fin k) (ys : List (Fin k)) (i : Fin k)
    (c : Fin (wordAnchorFiberList (k := k) a ys i).length → Fin k)
    (xs : Traj k ys.length) :
    xs ∈ wordTupleFixedComplementTrajSet (k := k) a ys i c ↔
      wordSuccessorTuplePrefixMap (k := k) a ys xs ∈
        wordTupleFixedComplementSet (k := k) a ys i c := by
  classical
  simp [wordTupleFixedComplementTrajSet, trajFinset]

lemma mem_wordTupleFixedComplementFiberSubset_iff
    (a : Fin k) (ys : List (Fin k)) (i : Fin k)
    (c : Fin (wordAnchorFiberList (k := k) a ys i).length → Fin k)
    (eN : MarkovState k) (xs : Traj k ys.length) :
    xs ∈ wordTupleFixedComplementFiberSubset (k := k) a ys i c eN ↔
      xs ∈ fiber k ys.length eN ∧
      wordSuccessorTuplePrefixMap (k := k) a ys xs ∈
        wordTupleFixedComplementSet (k := k) a ys i c := by
  classical
  simp [wordTupleFixedComplementFiberSubset]

/-- On a fixed evidence fiber, a Markov-exchangeable prefix measure is constant
on the mixed-row fixed-complement subset, so the total mass is cardinality
times the mass of any representative in that subset. -/
lemma sum_mu_wordTupleFixedComplementFiberSubset_eq_card_mul
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (a : Fin k) (ys : List (Fin k)) (i : Fin k)
    (c : Fin (wordAnchorFiberList (k := k) a ys i).length → Fin k)
    (eN : MarkovState k) {xs0 : Traj k ys.length}
    (hxs0 : xs0 ∈ wordTupleFixedComplementFiberSubset (k := k) a ys i c eN) :
    (∑ xs ∈ wordTupleFixedComplementFiberSubset (k := k) a ys i c eN,
      μ (trajToList (k := k) xs)) =
      ((wordTupleFixedComplementFiberSubset (k := k) a ys i c eN).card : ENNReal) *
        μ (trajToList (k := k) xs0) := by
  exact
    sum_mu_eq_card_mul_of_subset_fiber (k := k) (μ := μ) hμ
      (hA := wordTupleFixedComplementFiberSubset_subset_fiber (k := k) a ys i c eN)
      (hxs0 := hxs0)

lemma measurableSet_wordTupleFixedComplementSet
    (a : Fin k) (ys : List (Fin k)) (i : Fin k)
    (c : Fin (wordAnchorFiberList (k := k) a ys i).length → Fin k) :
    MeasurableSet (wordTupleFixedComplementSet (k := k) a ys i c) := by
  exact (Set.toFinite _).measurableSet

lemma wordSuccessorTuple_mem_wordTupleFixedComplementSet_wordAnchorFiberTarget
    (a : Fin k) (ys : List (Fin k)) (i : Fin k) :
    wordSuccessorTuple (k := k) a ys ∈
      wordTupleFixedComplementSet (k := k) a ys i
        (wordAnchorFiberTarget (k := k) a ys i) := by
  refine ⟨?_, ?_⟩
  · intro t
    rfl
  · intro j hj
    rfl

/-- The fixed-complement set at the word's own fiber target IS the singleton
{wordSuccessorTuple}. The fiber constraint pins fiber coords to their word
values; the complement constraint pins the rest. Together, all coords are
pinned. -/
lemma wordTupleFixedComplementSet_wordAnchorFiberTarget_eq_singleton
    (a : Fin k) (ys : List (Fin k)) (i : Fin k) :
    wordTupleFixedComplementSet (k := k) a ys i
        (wordAnchorFiberTarget (k := k) a ys i) =
      {wordSuccessorTuple (k := k) a ys} := by
  ext u
  simp only [Set.mem_singleton_iff, wordTupleFixedComplementSet, Set.mem_setOf_eq]
  constructor
  · intro ⟨hfiber, hcomp⟩
    funext j
    by_cases hj : (a :: ys).getD j.1 a = i
    · -- j is in the anchor fiber for i
      have hmem : j ∈ wordAnchorFiberList (k := k) a ys i :=
        (mem_wordAnchorFiberList_iff (k := k) a ys i j).mpr hj
      obtain ⟨t, ht_val⟩ := List.mem_iff_get.mp hmem
      have hcoord := hfiber t
      rw [wordAnchorFiberTarget] at hcoord
      -- hcoord uses l[t] (Fin-indexed), ht_val uses l.get t; these are defeq
      have hj_eq : (wordAnchorFiberList (k := k) a ys i)[t] = j := ht_val
      rw [hj_eq] at hcoord
      exact hcoord
    · exact hcomp j hj
  · intro h
    subst h
    exact wordSuccessorTuple_mem_wordTupleFixedComplementSet_wordAnchorFiberTarget
      (k := k) a ys i

/-! ### The bridge gap: restricted successor-matrix partial exchangeability

The fixed-complement invariance theorem below takes `hPE_restrict` as a hypothesis.
This hypothesis says: for each start state `j`, `P.restrict {ω₀=j}` satisfies
`SuccessorMatrixPartialExchangeable` (independent per-row visit-index permutations
preserve the joint law of cross-row selections under the restricted measure).

**What's needed to prove `hPE_restrict`**: The existing per-row carrier transport
(`measure_start_inter_rsp_preimage_eq`, line 759) proves the single-row case.
The missing bridge theorem is genuinely multi-row. Plausible routes are:
(a) a counting / Euler-trail argument on evidence fibers, or
(b) a sound multi-row carrier equivalence that moves all relevant rows together.

Either route should be aimed at `SuccessorMatrixPartialExchangeable` itself,
rather than iterating the one-fiber theorem below. This local theorem is a
supporting invariant, not the final cross-row bridge.

See `SuccessorMatrixPE_of_markovExchangeable_strongRecurrence` (Crux:2408) for the
corresponding Prop interface in the composition theorem. -/

/-- Full fixed-complement invariance at the correct abstraction layer:
under successor-matrix partial exchangeability on each start-restricted law,
permuting one ordered anchor fiber leaves the corresponding start-restricted
full-tuple event invariant, with all complementary coordinates held fixed.

**Limitation**: This theorem permutes ONE fiber (one row `i`) while pinning
all non-`i` coordinates to `wordSuccessorTuple` values. It CANNOT be iterated
across multiple fibers because pinning non-`i` coordinates forces other rows
back to their original values, preventing independent multi-row permutation.
For the full cross-row product formula, a multi-fiber variant or a direct
application of `SuccessorMatrixPartialExchangeable` on the full tuple is needed. -/
theorem measure_start_inter_preimage_wordTupleFixedComplementSet_perm_eq
    (P : Measure (ℕ → Fin k))
    (hPE_restrict :
      ∀ j : Fin k,
        SuccessorMatrixPartialExchangeable (k := k)
          (P.restrict {ω : ℕ → Fin k | ω 0 = j}))
    (a : Fin k) (ys : List (Fin k)) (i : Fin k)
    (σ' : Equiv.Perm (Fin (wordAnchorFiberList (k := k) a ys i).length))
    (c : Fin (wordAnchorFiberList (k := k) a ys i).length → Fin k)
    (j : Fin k) :
    P ({ω : ℕ → Fin k | ω 0 = j} ∩
        (wordSuccessorTupleMap (k := k) a ys) ⁻¹'
          wordTupleFixedComplementSet (k := k) a ys i (fun t => c (σ' t))) =
    P ({ω : ℕ → Fin k | ω 0 = j} ∩
        (wordSuccessorTupleMap (k := k) a ys) ⁻¹'
          wordTupleFixedComplementSet (k := k) a ys i c) := by
  let s : Set (ℕ → Fin k) := {ω : ℕ → Fin k | ω 0 = j}
  let anchor : Fin ys.length → Fin k := fun u : Fin ys.length => (a :: ys).getD u.1 a
  let idx : Fin ys.length → ℕ := fun u : Fin ys.length =>
    wordVisitIndex (k := k) (a :: ys) a u.1
  let σNat : Equiv.Perm ℕ := {
    toFun := fun n =>
      if h : n < (wordAnchorFiberList (k := k) a ys i).length then
        (σ'.symm ⟨n, h⟩).1
      else n
    invFun := fun n =>
      if h : n < (wordAnchorFiberList (k := k) a ys i).length then
        (σ' ⟨n, h⟩).1
      else n
    left_inv n := by
      by_cases h : n < (wordAnchorFiberList (k := k) a ys i).length <;>
        simp [h, Fin.eta, Equiv.apply_symm_apply]
    right_inv n := by
      by_cases h : n < (wordAnchorFiberList (k := k) a ys i).length <;>
        simp [h, Fin.eta, Equiv.symm_apply_apply] }
  let σrow : Fin k → Equiv.Perm ℕ := fun u => if u = i then σNat else Equiv.refl ℕ
  let f : (ℕ → Fin k) → Fin ys.length → Fin k :=
    fun ω u =>
      rowSuccessorVisitProcess (k := k) (anchor u) ω ((σrow (anchor u)) (idx u))
  let g : (ℕ → Fin k) → Fin ys.length → Fin k :=
    wordSuccessorTupleMap (k := k) a ys
  have hmap :
      Measure.map f (P.restrict s) = Measure.map g (P.restrict s) := by
    simp only [f, g, s, anchor, idx, σrow, σNat,
      wordSuccessorTupleMap_eq_multiRowSelectionMap (k := k) a ys]
    exact hPE_restrict j ys.length anchor idx σrow
  have hf : Measurable f := by
    refine measurable_pi_lambda _ ?_
    intro u
    exact (measurable_pi_apply ((σrow (anchor u)) (idx u))).comp
      (measurable_rowSuccessorVisitProcess (k := k) (anchor u))
  have hg : Measurable g := by
    simpa [g] using measurable_wordSuccessorTupleMap (k := k) a ys
  have hfixed_meas :
      MeasurableSet (wordTupleFixedComplementSet (k := k) a ys i c) :=
    measurableSet_wordTupleFixedComplementSet (k := k) a ys i c
  have hfixed_perm_meas :
      MeasurableSet
        (wordTupleFixedComplementSet (k := k) a ys i (fun t => c (σ' t))) :=
    measurableSet_wordTupleFixedComplementSet (k := k) a ys i (fun t => c (σ' t))
  have hs_meas : MeasurableSet s := by
    change MeasurableSet ((fun ω : ℕ → Fin k => ω 0) ⁻¹' {j})
    exact measurable_pi_apply 0 (measurableSet_singleton j)
  have hcoord_perm :
      ∀ (ω : ℕ → Fin k) (t : Fin (wordAnchorFiberList (k := k) a ys i).length),
        f ω ((wordAnchorFiberList (k := k) a ys i)[σ' t]) =
          g ω ((wordAnchorFiberList (k := k) a ys i)[t]) := by
    intro ω t
    have hidx_left :
        idx ((wordAnchorFiberList (k := k) a ys i)[σ' t]) = σ' t :=
      Mettapedia.Logic.MarkovDeFinettiHard.wordVisitIndex_getElem_wordAnchorFiberList
        (k := k) a ys i (σ' t)
    have hidx_right :
        idx ((wordAnchorFiberList (k := k) a ys i)[t]) = t :=
      Mettapedia.Logic.MarkovDeFinettiHard.wordVisitIndex_getElem_wordAnchorFiberList
        (k := k) a ys i t
    have hanchor_left :
        anchor ((wordAnchorFiberList (k := k) a ys i)[σ' t]) = i := by
      exact getElem_wordAnchorFiberList_eq_anchor (k := k) a ys i (σ' t).2
    have hanchor_right :
        anchor ((wordAnchorFiberList (k := k) a ys i)[t]) = i := by
      exact getElem_wordAnchorFiberList_eq_anchor (k := k) a ys i t.2
    change
      rowSuccessorVisitProcess (k := k)
        (anchor ((wordAnchorFiberList (k := k) a ys i)[σ' t])) ω
        ((if anchor ((wordAnchorFiberList (k := k) a ys i)[σ' t]) = i then σNat else Equiv.refl ℕ)
          (idx ((wordAnchorFiberList (k := k) a ys i)[σ' t]))) =
      rowSuccessorVisitProcess (k := k)
        (anchor ((wordAnchorFiberList (k := k) a ys i)[t])) ω
        (idx ((wordAnchorFiberList (k := k) a ys i)[t]))
    rw [hanchor_left, hanchor_right, if_pos rfl, hidx_left, hidx_right]
    have hσ : σNat (σ' t) = t := by
      simp [σNat]
    simp [hσ]
  have hcoord_fix :
      ∀ (ω : ℕ → Fin k) (u : Fin ys.length), anchor u ≠ i → f ω u = g ω u := by
    intro ω u hu
    change
      rowSuccessorVisitProcess (k := k) (anchor u) ω
        ((if anchor u = i then σNat else Equiv.refl ℕ) (idx u)) =
      rowSuccessorVisitProcess (k := k) (anchor u) ω (idx u)
    rw [if_neg hu]
    rfl
  have hpre :
      f ⁻¹' wordTupleFixedComplementSet (k := k) a ys i c =
        g ⁻¹' wordTupleFixedComplementSet (k := k) a ys i (fun t => c (σ' t)) := by
    ext ω
    constructor
    · intro hω
      rcases hω with ⟨hfiber, hcomp⟩
      refine ⟨?_, ?_⟩
      · intro t
        have h := hfiber (σ' t)
        exact (hcoord_perm ω t).symm.trans h
      · intro u hu
        have h := hcomp u hu
        exact (hcoord_fix ω u hu).symm.trans h
    · intro hω
      rcases hω with ⟨hfiber, hcomp⟩
      refine ⟨?_, ?_⟩
      · intro t
        have h := hfiber (σ'.symm t)
        simpa using (hcoord_perm ω (σ'.symm t)).trans (by simpa using h)
      · intro u hu
        have h := hcomp u hu
        exact (hcoord_fix ω u hu).trans h
  have hmap_eval :
      (P.restrict s) (f ⁻¹' wordTupleFixedComplementSet (k := k) a ys i c) =
        (P.restrict s) (g ⁻¹' wordTupleFixedComplementSet (k := k) a ys i c) := by
    have h :=
      congrArg (fun M =>
        M (wordTupleFixedComplementSet (k := k) a ys i c)) hmap
    simpa [Measure.map_apply hf hfixed_meas, Measure.map_apply hg hfixed_meas]
      using h
  calc
    P (s ∩ g ⁻¹' wordTupleFixedComplementSet (k := k) a ys i (fun t => c (σ' t))) =
        (P.restrict s) (g ⁻¹' wordTupleFixedComplementSet (k := k) a ys i (fun t => c (σ' t))) := by
          simpa [Set.inter_comm] using
            (MeasureTheory.Measure.restrict_apply' (μ := P) (s := s)
              (t := g ⁻¹' wordTupleFixedComplementSet (k := k) a ys i (fun t => c (σ' t)))
              hs_meas).symm
    _ = (P.restrict s) (f ⁻¹' wordTupleFixedComplementSet (k := k) a ys i c) := by
          rw [hpre]
    _ = (P.restrict s) (g ⁻¹' wordTupleFixedComplementSet (k := k) a ys i c) := hmap_eval
    _ = P (s ∩ g ⁻¹' wordTupleFixedComplementSet (k := k) a ys i c) := by
          simpa [Set.inter_comm] using
            (MeasureTheory.Measure.restrict_apply' (μ := P) (s := s)
              (t := g ⁻¹' wordTupleFixedComplementSet (k := k) a ys i c)
              hs_meas)

/-- The cylinder event EQUALS the corresponding full fixed-complement event
at the word's own fiber target, for every choice of anchor row i. -/
lemma cylinder_cons_eq_start_inter_wordTupleFixedComplementSet_wordAnchorFiberTarget_preimage
    (a : Fin k) (ys : List (Fin k)) (i : Fin k) :
    cylinder (k := k) (a :: ys) =
      {ω : ℕ → Fin k | ω 0 = a} ∩
        (wordSuccessorTupleMap (k := k) a ys) ⁻¹'
          wordTupleFixedComplementSet (k := k) a ys i
            (wordAnchorFiberTarget (k := k) a ys i) := by
  rw [cylinder_cons_eq_start_inter_preimage_wordSuccessorTuple (k := k) a ys,
      wordTupleFixedComplementSet_wordAnchorFiberTarget_eq_singleton (k := k) a ys i]

/-- Cylinder-level fixed-complement equality under start-restricted
successor-matrix PE: the cylinder measure EQUALS the fixed-complement event
with any permutation of the selected anchor fiber. -/
theorem measure_cylinder_cons_eq_start_inter_preimage_wordTupleFixedComplementSet_wordAnchorFiberTarget_perm
    (P : Measure (ℕ → Fin k))
    (hPE_restrict :
      ∀ j : Fin k,
        SuccessorMatrixPartialExchangeable (k := k)
          (P.restrict {ω : ℕ → Fin k | ω 0 = j}))
    (a : Fin k) (ys : List (Fin k)) (i : Fin k)
    (σ' : Equiv.Perm (Fin (wordAnchorFiberList (k := k) a ys i).length)) :
    P (cylinder (k := k) (a :: ys)) =
      P ({ω : ℕ → Fin k | ω 0 = a} ∩
          (wordSuccessorTupleMap (k := k) a ys) ⁻¹'
            wordTupleFixedComplementSet (k := k) a ys i
              (fun t => wordAnchorFiberTarget (k := k) a ys i (σ' t))) := by
  calc
    P (cylinder (k := k) (a :: ys)) =
        P ({ω : ℕ → Fin k | ω 0 = a} ∩
            (wordSuccessorTupleMap (k := k) a ys) ⁻¹'
              wordTupleFixedComplementSet (k := k) a ys i
                (wordAnchorFiberTarget (k := k) a ys i)) := by
          rw [cylinder_cons_eq_start_inter_wordTupleFixedComplementSet_wordAnchorFiberTarget_preimage
              (k := k) a ys i]
    _ =
        P ({ω : ℕ → Fin k | ω 0 = a} ∩
            (wordSuccessorTupleMap (k := k) a ys) ⁻¹'
              wordTupleFixedComplementSet (k := k) a ys i
                (fun t => wordAnchorFiberTarget (k := k) a ys i (σ' t))) := by
          symm
          exact measure_start_inter_preimage_wordTupleFixedComplementSet_perm_eq
            (k := k) P hPE_restrict a ys i σ'
            (wordAnchorFiberTarget (k := k) a ys i) a

/-- Every cylinder event implies its corresponding projected anchor-fiber event.
This is the set-theoretic "projected cylinder" corollary extracted from the
full tuple representation. -/
lemma cylinder_cons_subset_start_inter_wordAnchorFiberTarget_preimage
    (a : Fin k) (ys : List (Fin k)) (i : Fin k) :
    cylinder (k := k) (a :: ys) ⊆
      {ω : ℕ → Fin k | ω 0 = a} ∩
        (fun ω (t : Fin (wordAnchorFiberList (k := k) a ys i).length) =>
          wordSuccessorTupleMap (k := k) a ys ω
            ((wordAnchorFiberList (k := k) a ys i)[t])) ⁻¹'
          ({wordAnchorFiberTarget (k := k) a ys i} :
            Set (Fin (wordAnchorFiberList (k := k) a ys i).length → Fin k)) := by
  rw [cylinder_cons_eq_start_inter_preimage_wordSuccessorTuple (k := k) a ys]
  intro ω hω
  rcases hω with ⟨hstart, htuple⟩
  refine ⟨hstart, ?_⟩
  ext t
  have hcoord := congrFun htuple ((wordAnchorFiberList (k := k) a ys i)[t])
  simpa [wordAnchorFiberTarget] using congrArg Fin.val hcoord

/-- Measure-theoretic projected-cylinder corollary:
the nonempty cylinder is bounded above by the projected anchor-fiber event, and
the latter is invariant under permutations of the selected fiber. -/
theorem measure_cylinder_cons_le_start_inter_wordAnchorFiberTarget_perm_preimage
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (hExt : ∀ xs : List (Fin k), μ xs = P (MarkovDeFinettiRecurrence.cylinder (k := k) xs))
    (hStrRec : MarkovDeFinettiHard.StrongRecurrence (k := k) P)
    (a : Fin k) (ys : List (Fin k)) (i : Fin k)
    (σ' : Equiv.Perm (Fin (wordAnchorFiberList (k := k) a ys i).length)) :
    P (cylinder (k := k) (a :: ys)) ≤
      P ({ω : ℕ → Fin k | ω 0 = a} ∩
          (fun ω (t : Fin (wordAnchorFiberList (k := k) a ys i).length) =>
            wordSuccessorTupleMap (k := k) a ys ω
              ((wordAnchorFiberList (k := k) a ys i)[σ' t])) ⁻¹'
            ({wordAnchorFiberTarget (k := k) a ys i} :
              Set (Fin (wordAnchorFiberList (k := k) a ys i).length → Fin k))) := by
  calc
    P (cylinder (k := k) (a :: ys)) ≤
        P ({ω : ℕ → Fin k | ω 0 = a} ∩
            (fun ω (t : Fin (wordAnchorFiberList (k := k) a ys i).length) =>
              wordSuccessorTupleMap (k := k) a ys ω
                ((wordAnchorFiberList (k := k) a ys i)[t])) ⁻¹'
              ({wordAnchorFiberTarget (k := k) a ys i} :
                Set (Fin (wordAnchorFiberList (k := k) a ys i).length → Fin k))) := by
          exact measure_mono
            (cylinder_cons_subset_start_inter_wordAnchorFiberTarget_preimage
              (k := k) a ys i)
    _ =
        P ({ω : ℕ → Fin k | ω 0 = a} ∩
            (fun ω (t : Fin (wordAnchorFiberList (k := k) a ys i).length) =>
              wordSuccessorTupleMap (k := k) a ys ω
                ((wordAnchorFiberList (k := k) a ys i)[σ' t])) ⁻¹'
              ({wordAnchorFiberTarget (k := k) a ys i} :
                Set (Fin (wordAnchorFiberList (k := k) a ys i).length → Fin k))) := by
          symm
          exact measure_start_inter_wordAnchorFiberTarget_perm_eq
            (k := k) μ hμ P hExt hStrRec a ys i σ' a

/-- The ordered coordinates of `wordAnchorFiberList` mapped into the
`anchorFiber` enumeration used by `anchorFiberSelectionMap`. -/
def wordAnchorFiberIndexMap
    (a : Fin k) (ys : List (Fin k)) (i : Fin k) :
    Fin (wordAnchorFiberList (k := k) a ys i).length →
      Fin (anchorFiber (k := k) (fun j : Fin ys.length => (a :: ys).getD j.1 a) i).card :=
  fun t =>
    (anchorFiber (k := k) (fun j : Fin ys.length => (a :: ys).getD j.1 a) i).equivFin
      ⟨(wordAnchorFiberList (k := k) a ys i)[t], by
        refine Finset.mem_filter.mpr ?_
        refine ⟨Finset.mem_univ _, ?_⟩
        exact getElem_wordAnchorFiberList_eq_anchor (k := k) a ys i t.2⟩

lemma wordAnchorFiberIndexMap_symm_apply
    (a : Fin k) (ys : List (Fin k)) (i : Fin k)
    (t : Fin (wordAnchorFiberList (k := k) a ys i).length) :
    ((anchorFiber (k := k) (fun j : Fin ys.length => (a :: ys).getD j.1 a) i).equivFin.symm
      (wordAnchorFiberIndexMap (k := k) a ys i t)).1 =
      (wordAnchorFiberList (k := k) a ys i)[t] := by
  simp [wordAnchorFiberIndexMap]

lemma anchorFiberSelectionMap_comp_wordAnchorFiberIndexMap
    (a : Fin k) (ys : List (Fin k)) (i : Fin k)
    (idx : Fin ys.length → ℕ) (ω : ℕ → Fin k)
    (t : Fin (wordAnchorFiberList (k := k) a ys i).length) :
    anchorFiberSelectionMap (k := k)
      (fun j : Fin ys.length => (a :: ys).getD j.1 a) idx i ω
      (wordAnchorFiberIndexMap (k := k) a ys i t) =
      multiRowSelectionMap (k := k)
        (fun j : Fin ys.length => (a :: ys).getD j.1 a) idx ω
        ((wordAnchorFiberList (k := k) a ys i)[t]) := by
  simp [anchorFiberSelectionMap, wordAnchorFiberIndexMap]

lemma wordSuccessorTupleMap_eq_anchorFiberSelectionMap_wordAnchorFiberIndexMap
    (a : Fin k) (ys : List (Fin k)) (i : Fin k)
    (ω : ℕ → Fin k)
    (t : Fin (wordAnchorFiberList (k := k) a ys i).length) :
    anchorFiberSelectionMap (k := k)
      (fun j : Fin ys.length => (a :: ys).getD j.1 a)
      (fun j : Fin ys.length => wordVisitIndex (k := k) (a :: ys) a j.1)
      i ω (wordAnchorFiberIndexMap (k := k) a ys i t) =
      wordSuccessorTupleMap (k := k) a ys ω
        ((wordAnchorFiberList (k := k) a ys i)[t]) := by
  rw [wordSuccessorTupleMap_eq_multiRowSelectionMap (k := k) a ys]
  exact anchorFiberSelectionMap_comp_wordAnchorFiberIndexMap (k := k) a ys i
    (fun j : Fin ys.length => wordVisitIndex (k := k) (a :: ys) a j.1) ω t

/-- Cylinder constraints for a nonempty word, restated through
`multiRowSelectionMap`. This gives the new abstraction a concrete downstream
consumer in the Fortini assembly. -/
lemma cylinder_cons_eq_start_inter_preimage_multiRowSelectionMap
    (a : Fin k) (ys : List (Fin k)) :
    cylinder (k := k) (a :: ys) =
      {ω : ℕ → Fin k | ω 0 = a} ∩
        (multiRowSelectionMap (k := k)
          (fun j : Fin ys.length => (a :: ys).getD j.1 a)
          (fun j : Fin ys.length => wordVisitIndex (k := k) (a :: ys) a j.1)) ⁻¹'
          ({wordSuccessorTuple (k := k) a ys} : Set (Fin ys.length → Fin k)) := by
  simpa [wordSuccessorTupleMap_eq_multiRowSelectionMap (k := k) a ys] using
    (cylinder_cons_eq_start_inter_preimage_wordSuccessorTuple (k := k) a ys)

/-- Strong recurrence in a class gives the exact row-specific recurrence
predicate used by the PE bridge for any row index `i ∈ C`. -/
lemma ae_rowRecurrence_of_StrongRecurrenceInClass
    (C : Set (Fin k))
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (hStrRecC : MarkovDeFinettiRecurrence.StrongRecurrenceInClass (k := k) C P)
    (i : Fin k) (hi : i ∈ C) :
    ∀ᵐ ω ∂P, (∃ t, ω t = i) → ∀ n,
      nthVisitTimeExists (k := k) ω i n := by
  have hAllN :
      ∀ n : ℕ,
        ∀ᵐ ω ∂P, (∃ t : ℕ, ω t ∈ C) → nthVisitTimeExists (k := k) ω i n := by
    intro n
    exact
      nthVisitTimeExists_of_StrongRecurrenceInClass
        (k := k) C P inferInstance hStrRecC i hi n
  have hAll :
      ∀ᵐ ω ∂P, ∀ n : ℕ, (∃ t : ℕ, ω t ∈ C) →
        nthVisitTimeExists (k := k) ω i n := by
    rw [ae_all_iff]
    intro n
    exact hAllN n
  filter_upwards [hAll] with ω hω hvisit n
  refine hω n ?_
  rcases hvisit with ⟨t, ht⟩
  exact ⟨t, by simpa [ht] using hi⟩

/-- Exchangeability of the row process only needs the row-specific recurrence
input for the fixed state `i`. -/
theorem exchangeable_rowProcess_of_rowRecurrence
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (hExt : ∀ xs : List (Fin k), μ xs = P (MarkovDeFinettiRecurrence.cylinder (k := k) xs))
    (i : Fin k)
    (hRowRec :
      ∀ᵐ ω ∂P, (∃ t, ω t = i) → ∀ n,
        nthVisitTimeExists (k := k) ω i n) :
    Exchangeability.Exchangeable P
      (fun n (ω : ℕ → Fin k) =>
        MarkovDeFinettiHard.rowSuccessorVisitProcess (k := k) i ω n) := by
  intro n' σ'
  show Measure.map (fun ω (j : Fin n') =>
      MarkovDeFinettiHard.rowSuccessorVisitProcess (k := k) i ω (↑(σ' j))) P =
    Measure.map (fun ω (j : Fin n') =>
      MarkovDeFinettiHard.rowSuccessorVisitProcess (k := k) i ω ↑j) P
  have hmeas_rsp := MarkovDeFinettiHard.measurable_rowSuccessorVisitProcess (k := k) i
  have hf : Measurable (fun ω : ℕ → Fin k => fun j : Fin n' =>
      MarkovDeFinettiHard.rowSuccessorVisitProcess (k := k) i ω (↑(σ' j))) := by
    apply measurable_pi_lambda
    intro j
    show Measurable (fun ω : ℕ → Fin k =>
      MarkovDeFinettiHard.rowSuccessorVisitProcess (k := k) i ω (↑(σ' j)))
    exact (measurable_pi_apply (↑(σ' j))).comp hmeas_rsp
  have hg : Measurable (fun ω : ℕ → Fin k => fun j : Fin n' =>
      MarkovDeFinettiHard.rowSuccessorVisitProcess (k := k) i ω ↑j) := by
    apply measurable_pi_lambda
    intro j
    show Measurable (fun ω : ℕ → Fin k =>
      MarkovDeFinettiHard.rowSuccessorVisitProcess (k := k) i ω ↑j)
    exact (measurable_pi_apply ↑j).comp hmeas_rsp
  apply MeasureTheory.Measure.ext_of_singleton
  intro c
  rw [Measure.map_apply hf (measurableSet_singleton c),
      Measure.map_apply hg (measurableSet_singleton c)]
  have hpartition : ∀ E : Set (ℕ → Fin k), MeasurableSet E →
      P E = ∑ j : Fin k, P ({ω | ω 0 = j} ∩ E) := by
    intro E hE
    let fiber : Fin k → Set (ℕ → Fin k) :=
      fun j => (fun ω : ℕ → Fin k => ω 0) ⁻¹' {j} ∩ E
    have hcover : E = ⋃ j : Fin k, fiber j := by
      ext ω
      simp only [fiber, Set.mem_iUnion, Set.mem_inter_iff,
        Set.mem_preimage, Set.mem_singleton_iff]
      exact ⟨fun h => ⟨ω 0, rfl, h⟩, fun ⟨_, _, h⟩ => h⟩
    have hdisj : Pairwise (Function.onFun Disjoint fiber) := by
      intro a b hab
      exact Set.disjoint_left.mpr fun ω ⟨ha, _⟩ ⟨hb, _⟩ =>
        hab (by simp only [Set.mem_preimage, Set.mem_singleton_iff] at ha hb; exact ha ▸ hb)
    have hmeas : ∀ j, MeasurableSet (fiber j) :=
      fun j => (measurable_pi_apply 0 (measurableSet_singleton j)).inter hE
    have hfiber_eq : ∀ j, P (fiber j) = P ({ω | ω 0 = j} ∩ E) := by
      intro j
      congr 1
    rw [hcover, measure_iUnion hdisj hmeas]
    simp_rw [hfiber_eq, ← hcover]
    exact tsum_fintype _
  rw [hpartition _ (hf (measurableSet_singleton c)),
      hpartition _ (hg (measurableSet_singleton c))]
  congr 1
  ext j
  exact
    measure_start_inter_rsp_preimage_eq_of_rowRecurrence
      (k := k) μ hμ P hExt i hRowRec n' σ' c j

/-- The row process for each state i is Exchangeable under P.
Uses guard marginalization (S = range(n'+2)) + V/NV decomposition +
carrier_equiv_of_fin_perm to avoid the different-S and boundary bugs.

Council quorum 87%: Exchangeable uses Perm(Fin n') → same S always.
Guard positions n', n'+1 absorb the boundary; swap_induction restricted
to Fin n' never touches guards. -/
theorem exchangeable_rowProcess
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (hExt : ∀ xs : List (Fin k), μ xs = P (MarkovDeFinettiRecurrence.cylinder (k := k) xs))
    (hStrRec : MarkovDeFinettiHard.StrongRecurrence (k := k) P) (i : Fin k) :
    Exchangeability.Exchangeable P
      (fun n (ω : ℕ → Fin k) =>
        MarkovDeFinettiHard.rowSuccessorVisitProcess (k := k) i ω n) := by
  exact
    exchangeable_rowProcess_of_rowRecurrence
      (k := k) μ hμ P hExt i (hStrRec i)

/-- Per-row joint perm invariance for a single row.
The row process for each state i is invariant under arbitrary permutation
of visit indices. Uses Exchangeable → FullyExchangeable → rowPermute equality.

The proof route: carrier equiv → level-3 lifting → adjacent swap equality
→ composition of swaps → guard index marginalization → pushforward equality. -/
theorem rowProcessLaw_permInvariant_of_markovExchangeability_rowRecurrence
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (hExt : ∀ xs : List (Fin k), μ xs = P (MarkovDeFinettiRecurrence.cylinder (k := k) xs))
    (i : Fin k)
    (hRowRec :
      ∀ᵐ ω ∂P, (∃ t, ω t = i) → ∀ n,
        nthVisitTimeExists (k := k) ω i n) :
    ∀ (σ : Equiv.Perm ℕ), IsFiniteMeasure P →
      Measure.map (MarkovDeFinettiHard.rowPermute (k := k) σ)
        (MarkovDeFinettiHard.rowProcessLaw (k := k) P i) =
      MarkovDeFinettiHard.rowProcessLaw (k := k) P i := by
  intro σ _
  have hmeas_rowPermute : Measurable (MarkovDeFinettiHard.rowPermute (k := k) σ) :=
    measurable_pi_lambda _ (fun n => measurable_pi_apply (σ n))
  have hExch :=
    exchangeable_rowProcess_of_rowRecurrence (k := k) μ hμ P hExt i hRowRec
  have hFull := (Exchangeability.exchangeable_iff_fullyExchangeable
      (fun m => (measurable_pi_apply m).comp
        (MarkovDeFinettiHard.measurable_rowSuccessorVisitProcess (k := k) i))).mp hExch
  have hσ := hFull σ
  show Measure.map (MarkovDeFinettiHard.rowPermute (k := k) σ)
      (Measure.map (MarkovDeFinettiHard.rowSuccessorVisitProcess (k := k) i) P) =
    Measure.map (MarkovDeFinettiHard.rowSuccessorVisitProcess (k := k) i) P
  rw [Measure.map_map hmeas_rowPermute
      (MarkovDeFinettiHard.measurable_rowSuccessorVisitProcess (k := k) i)]
  exact hσ

/-- Per-row joint perm invariance for a single class-local row. -/
theorem rowProcessLaw_permInvariant_of_markovExchangeability_strongRecurrenceInClass
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (hExt : ∀ xs : List (Fin k), μ xs = P (MarkovDeFinettiRecurrence.cylinder (k := k) xs))
    (C : Set (Fin k))
    (hStrRecC : MarkovDeFinettiRecurrence.StrongRecurrenceInClass (k := k) C P)
    (i : Fin k) (hi : i ∈ C) :
    ∀ (σ : Equiv.Perm ℕ), IsFiniteMeasure P →
      Measure.map (MarkovDeFinettiHard.rowPermute (k := k) σ)
        (MarkovDeFinettiHard.rowProcessLaw (k := k) P i) =
      MarkovDeFinettiHard.rowProcessLaw (k := k) P i := by
  exact
    rowProcessLaw_permInvariant_of_markovExchangeability_rowRecurrence
      (k := k) μ hμ P hExt i
      (ae_rowRecurrence_of_StrongRecurrenceInClass
        (k := k) C P hStrRecC i hi)

/-- Per-row joint perm invariance for a single row.
The row process for each state i is invariant under arbitrary permutation
of visit indices. Uses Exchangeable → FullyExchangeable → rowPermute equality.

The proof route: carrier equiv → level-3 lifting → adjacent swap equality
→ composition of swaps → guard index marginalization → pushforward equality. -/
theorem rowProcessLaw_permInvariant_of_markovExchangeability
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (hExt : ∀ xs : List (Fin k), μ xs = P (MarkovDeFinettiRecurrence.cylinder (k := k) xs))
    (hStrRec : MarkovDeFinettiHard.StrongRecurrence (k := k) P) :
    ∀ (i : Fin k) (σ : Equiv.Perm ℕ), IsFiniteMeasure P →
      Measure.map (MarkovDeFinettiHard.rowPermute (k := k) σ)
        (MarkovDeFinettiHard.rowProcessLaw (k := k) P i) =
      MarkovDeFinettiHard.rowProcessLaw (k := k) P i := by
  intro i σ hfin
  exact
    rowProcessLaw_permInvariant_of_markovExchangeability_rowRecurrence
      (k := k) μ hμ P hExt i (hStrRec i) σ hfin

/-- The row process under `P.restrict {ω₀ = a}` is exchangeable as soon as the
fixed row `i` satisfies the row-specific recurrence hypothesis. -/
theorem exchangeable_rowProcess_restrict_of_rowRecurrence
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (hExt : ∀ xs : List (Fin k), μ xs = P (MarkovDeFinettiRecurrence.cylinder (k := k) xs))
    (i a : Fin k)
    (hRowRec :
      ∀ᵐ ω ∂P, (∃ t, ω t = i) → ∀ n,
        nthVisitTimeExists (k := k) ω i n) :
    Exchangeability.Exchangeable (P.restrict {ω : ℕ → Fin k | ω 0 = a})
      (fun n (ω : ℕ → Fin k) =>
        MarkovDeFinettiHard.rowSuccessorVisitProcess (k := k) i ω n) := by
  intro n' σ'
  show Measure.map (fun ω (j : Fin n') =>
      MarkovDeFinettiHard.rowSuccessorVisitProcess (k := k) i ω (↑(σ' j)))
        (P.restrict {ω | ω 0 = a}) =
    Measure.map (fun ω (j : Fin n') =>
      MarkovDeFinettiHard.rowSuccessorVisitProcess (k := k) i ω ↑j)
        (P.restrict {ω | ω 0 = a})
  have hmeas_rsp := MarkovDeFinettiHard.measurable_rowSuccessorVisitProcess (k := k) i
  have hf : Measurable (fun ω : ℕ → Fin k => fun j : Fin n' =>
      MarkovDeFinettiHard.rowSuccessorVisitProcess (k := k) i ω (↑(σ' j))) := by
    apply measurable_pi_lambda; intro j
    exact (measurable_pi_apply (↑(σ' j))).comp hmeas_rsp
  have hg : Measurable (fun ω : ℕ → Fin k => fun j : Fin n' =>
      MarkovDeFinettiHard.rowSuccessorVisitProcess (k := k) i ω ↑j) := by
    apply measurable_pi_lambda; intro j
    exact (measurable_pi_apply ↑j).comp hmeas_rsp
  have hS_meas : MeasurableSet {ω : ℕ → Fin k | ω 0 = a} := by
    rw [show {ω : ℕ → Fin k | ω 0 = a} = (fun f : ℕ → Fin k => f 0) ⁻¹' {a} from by ext ω; simp]
    exact measurable_pi_apply 0 (measurableSet_singleton a)
  apply MeasureTheory.Measure.ext_of_singleton; intro c
  rw [Measure.map_apply hf (measurableSet_singleton c),
      Measure.map_apply hg (measurableSet_singleton c)]
  rw [Measure.restrict_apply' hS_meas, Measure.restrict_apply' hS_meas]
  have := measure_start_inter_rsp_preimage_eq_of_rowRecurrence
    (k := k) μ hμ P hExt i hRowRec n' σ' c a
  rwa [Set.inter_comm, Set.inter_comm ({ω : ℕ → Fin k | ω 0 = a}
    : Set (ℕ → Fin k))] at this

/-- The row process for each state `i` is Exchangeable under `P.restrict {ω₀ = a}`.
Uses `Measure.restrict_apply` to convert the restricted measure to
`P({ω₀=a} ∩ ...)`, then applies `measure_start_inter_rsp_preimage_eq`. -/
theorem exchangeable_rowProcess_restrict
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (hExt : ∀ xs : List (Fin k), μ xs = P (MarkovDeFinettiRecurrence.cylinder (k := k) xs))
    (hStrRec : MarkovDeFinettiHard.StrongRecurrence (k := k) P) (i a : Fin k) :
    Exchangeability.Exchangeable (P.restrict {ω : ℕ → Fin k | ω 0 = a})
      (fun n (ω : ℕ → Fin k) =>
        MarkovDeFinettiHard.rowSuccessorVisitProcess (k := k) i ω n) := by
  exact
    exchangeable_rowProcess_restrict_of_rowRecurrence
      (k := k) μ hμ P hExt i a (hStrRec i)

/-- The row process for each state `i` is Exchangeable under
`P.restrict {ω₀ ∈ C}`.
This finite-class version reduces to the per-start theorem by partitioning the
class event into singleton start fibers. -/
theorem exchangeable_rowProcess_restrict_class_of_rowRecurrence
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (hExt : ∀ xs : List (Fin k), μ xs = P (MarkovDeFinettiRecurrence.cylinder (k := k) xs))
    (C : Set (Fin k)) (i : Fin k)
    (hRowRec :
      ∀ᵐ ω ∂P, (∃ t, ω t = i) → ∀ n,
        nthVisitTimeExists (k := k) ω i n) :
    Exchangeability.Exchangeable (P.restrict {ω : ℕ → Fin k | ω 0 ∈ C})
      (fun n (ω : ℕ → Fin k) =>
        MarkovDeFinettiHard.rowSuccessorVisitProcess (k := k) i ω n) := by
  intro n' σ'
  show Measure.map (fun ω (j : Fin n') =>
      MarkovDeFinettiHard.rowSuccessorVisitProcess (k := k) i ω (↑(σ' j)))
        (P.restrict {ω | ω 0 ∈ C}) =
    Measure.map (fun ω (j : Fin n') =>
      MarkovDeFinettiHard.rowSuccessorVisitProcess (k := k) i ω ↑j)
        (P.restrict {ω | ω 0 ∈ C})
  have hmeas_rsp := MarkovDeFinettiHard.measurable_rowSuccessorVisitProcess (k := k) i
  have hf : Measurable (fun ω : ℕ → Fin k => fun j : Fin n' =>
      MarkovDeFinettiHard.rowSuccessorVisitProcess (k := k) i ω (↑(σ' j))) := by
    apply measurable_pi_lambda; intro j
    exact (measurable_pi_apply (↑(σ' j))).comp hmeas_rsp
  have hg : Measurable (fun ω : ℕ → Fin k => fun j : Fin n' =>
      MarkovDeFinettiHard.rowSuccessorVisitProcess (k := k) i ω ↑j) := by
    apply measurable_pi_lambda; intro j
    exact (measurable_pi_apply ↑j).comp hmeas_rsp
  have hC_meas : MeasurableSet {ω : ℕ → Fin k | ω 0 ∈ C} := by
    show MeasurableSet ((fun f : ℕ → Fin k => f 0) ⁻¹' C)
    exact measurable_pi_apply 0 (Set.Finite.measurableSet (Set.toFinite C))
  apply MeasureTheory.Measure.ext_of_singleton
  intro c
  rw [Measure.map_apply hf (measurableSet_singleton c),
      Measure.map_apply hg (measurableSet_singleton c)]
  rw [Measure.restrict_apply' hC_meas, Measure.restrict_apply' hC_meas]
  let Eσ : Set (ℕ → Fin k) :=
    (fun ω (j : Fin n') =>
      MarkovDeFinettiHard.rowSuccessorVisitProcess (k := k) i ω (↑(σ' j))) ⁻¹' {c}
  let En : Set (ℕ → Fin k) :=
    (fun ω (j : Fin n') =>
      MarkovDeFinettiHard.rowSuccessorVisitProcess (k := k) i ω ↑j) ⁻¹' {c}
  have hleft := sum_start_inter_eq_measure (k := k) P (Eσ ∩ {ω : ℕ → Fin k | ω 0 ∈ C})
  have hright := sum_start_inter_eq_measure (k := k) P (En ∩ {ω : ℕ → Fin k | ω 0 ∈ C})
  rw [← hleft, ← hright]
  congr 1
  ext a
  by_cases ha : a ∈ C
  · have hEσ :
        {ω : ℕ → Fin k | ω 0 = a} ∩ (Eσ ∩ {ω : ℕ → Fin k | ω 0 ∈ C}) =
          {ω : ℕ → Fin k | ω 0 = a} ∩ Eσ := by
      ext ω
      constructor
      · intro hω
        exact ⟨hω.1, hω.2.1⟩
      · intro hω
        have hstart : ω 0 = a := by
          simpa using hω.1
        refine ⟨hω.1, hω.2, ?_⟩
        show ω 0 ∈ C
        simpa [hstart] using ha
    have hEn :
        {ω : ℕ → Fin k | ω 0 = a} ∩ (En ∩ {ω : ℕ → Fin k | ω 0 ∈ C}) =
          {ω : ℕ → Fin k | ω 0 = a} ∩ En := by
      ext ω
      constructor
      · intro hω
        exact ⟨hω.1, hω.2.1⟩
      · intro hω
        have hstart : ω 0 = a := by
          simpa using hω.1
        refine ⟨hω.1, hω.2, ?_⟩
        show ω 0 ∈ C
        simpa [hstart] using ha
    rw [hEσ, hEn]
    exact
      measure_start_inter_rsp_preimage_eq_of_rowRecurrence
        (k := k) μ hμ P hExt i hRowRec n' σ' c a
  · have hEσ_empty :
        {ω : ℕ → Fin k | ω 0 = a} ∩ (Eσ ∩ {ω : ℕ → Fin k | ω 0 ∈ C}) = ∅ := by
      ext ω
      constructor
      · intro hω
        have hstart : ω 0 = a := by
          simpa using hω.1
        have hmem : ω 0 ∈ C := by
          simpa using hω.2.2
        exact (ha (hstart ▸ hmem)).elim
      · intro hω
        cases hω
    have hEn_empty :
        {ω : ℕ → Fin k | ω 0 = a} ∩ (En ∩ {ω : ℕ → Fin k | ω 0 ∈ C}) = ∅ := by
      ext ω
      constructor
      · intro hω
        have hstart : ω 0 = a := by
          simpa using hω.1
        have hmem : ω 0 ∈ C := by
          simpa using hω.2.2
        exact (ha (hstart ▸ hmem)).elim
      · intro hω
        cases hω
    simp [hEσ_empty, hEn_empty]

/-- The row process for each state `i` is Exchangeable under
`P.restrict {ω₀ ∈ C}`.
This finite-class version reduces to the per-start theorem by partitioning the
class event into singleton start fibers. -/
theorem exchangeable_rowProcess_restrict_class
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (hExt : ∀ xs : List (Fin k), μ xs = P (MarkovDeFinettiRecurrence.cylinder (k := k) xs))
    (hStrRec : MarkovDeFinettiHard.StrongRecurrence (k := k) P)
    (C : Set (Fin k)) (i : Fin k) :
    Exchangeability.Exchangeable (P.restrict {ω : ℕ → Fin k | ω 0 ∈ C})
      (fun n (ω : ℕ → Fin k) =>
        MarkovDeFinettiHard.rowSuccessorVisitProcess (k := k) i ω n) := by
  exact
    exchangeable_rowProcess_restrict_class_of_rowRecurrence
      (k := k) μ hμ P hExt C i (hStrRec i)

/-- Class recurrence suffices for row-process exchangeability on any row
whose anchor state lies inside the recurrent class. -/
theorem exchangeable_rowProcess_of_markovExchangeability_strongRecurrenceInClass
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (hExt : ∀ xs : List (Fin k), μ xs = P (MarkovDeFinettiRecurrence.cylinder (k := k) xs))
    (C : Set (Fin k))
    (hStrRecC : MarkovDeFinettiRecurrence.StrongRecurrenceInClass (k := k) C P)
    (i : Fin k) (hi : i ∈ C) :
    Exchangeability.Exchangeable P
      (fun n (ω : ℕ → Fin k) =>
        MarkovDeFinettiHard.rowSuccessorVisitProcess (k := k) i ω n) := by
  exact
    exchangeable_rowProcess_of_rowRecurrence
      (k := k) μ hμ P hExt i
      (ae_rowRecurrence_of_StrongRecurrenceInClass
        (k := k) C P hStrRecC i hi)

/-- Singleton-start class-local exchangeability under class recurrence. -/
theorem exchangeable_rowProcess_restrict_of_markovExchangeability_strongRecurrenceInClass
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (hExt : ∀ xs : List (Fin k), μ xs = P (MarkovDeFinettiRecurrence.cylinder (k := k) xs))
    (C : Set (Fin k))
    (hStrRecC : MarkovDeFinettiRecurrence.StrongRecurrenceInClass (k := k) C P)
    (i a : Fin k) (hi : i ∈ C) :
    Exchangeability.Exchangeable (P.restrict {ω : ℕ → Fin k | ω 0 = a})
      (fun n (ω : ℕ → Fin k) =>
        MarkovDeFinettiHard.rowSuccessorVisitProcess (k := k) i ω n) := by
  exact
    exchangeable_rowProcess_restrict_of_rowRecurrence
      (k := k) μ hμ P hExt i a
      (ae_rowRecurrence_of_StrongRecurrenceInClass
        (k := k) C P hStrRecC i hi)

/-- Class-restricted exchangeability under class recurrence for rows indexed by
states inside the recurrent class. -/
theorem exchangeable_rowProcess_restrict_class_of_markovExchangeability_strongRecurrenceInClass
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (hExt : ∀ xs : List (Fin k), μ xs = P (MarkovDeFinettiRecurrence.cylinder (k := k) xs))
    (C : Set (Fin k))
    (hStrRecC : MarkovDeFinettiRecurrence.StrongRecurrenceInClass (k := k) C P)
    (i : Fin k) (hi : i ∈ C) :
    Exchangeability.Exchangeable (P.restrict {ω : ℕ → Fin k | ω 0 ∈ C})
      (fun n (ω : ℕ → Fin k) =>
        MarkovDeFinettiHard.rowSuccessorVisitProcess (k := k) i ω n) := by
  exact
    exchangeable_rowProcess_restrict_class_of_rowRecurrence
      (k := k) μ hμ P hExt C i
      (ae_rowRecurrence_of_StrongRecurrenceInClass
        (k := k) C P hStrRecC i hi)

/-- Per-row joint perm invariance for a single row under the restricted measure
`P.restrict {ω₀ = a}`. The row process law restricted to paths starting at `a`
is invariant under arbitrary permutation of visit indices.

When `P({ω₀=a}) = 0` both sides are trivially zero. Otherwise we scale
to a probability measure, apply `exchangeable_iff_fullyExchangeable`, and scale back. -/
theorem rowProcessLaw_restrict_permInvariant
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (hExt : ∀ xs : List (Fin k), μ xs = P (MarkovDeFinettiRecurrence.cylinder (k := k) xs))
    (hStrRec : MarkovDeFinettiHard.StrongRecurrence (k := k) P) (i a : Fin k)
    (σ : Equiv.Perm ℕ) :
    Measure.map (MarkovDeFinettiHard.rowPermute (k := k) σ)
      (MarkovDeFinettiHard.rowProcessLaw (k := k)
        (P.restrict {ω : ℕ → Fin k | ω 0 = a}) i) =
    MarkovDeFinettiHard.rowProcessLaw (k := k)
      (P.restrict {ω : ℕ → Fin k | ω 0 = a}) i := by
  let Pa := P.restrict {ω : ℕ → Fin k | ω 0 = a}
  have hmeas_rsp := MarkovDeFinettiHard.measurable_rowSuccessorVisitProcess (k := k) i
  have hmeas_rowPermute : Measurable (MarkovDeFinettiHard.rowPermute (k := k) σ) :=
    measurable_pi_lambda _ (fun n => measurable_pi_apply (σ n))
  -- Show as map_map
  show Measure.map (MarkovDeFinettiHard.rowPermute (k := k) σ)
      (Measure.map (MarkovDeFinettiHard.rowSuccessorVisitProcess (k := k) i) Pa) =
    Measure.map (MarkovDeFinettiHard.rowSuccessorVisitProcess (k := k) i) Pa
  rw [Measure.map_map hmeas_rowPermute hmeas_rsp]
  -- Goal: map (fun ω n => rsp i ω (σ n)) Pa = map (fun ω n => rsp i ω n) Pa
  have hExch := exchangeable_rowProcess_restrict (k := k) μ hμ P hExt hStrRec i a
  have hX_meas : ∀ m, Measurable (fun ω : ℕ → Fin k =>
      MarkovDeFinettiHard.rowSuccessorVisitProcess (k := k) i ω m) :=
    fun m => (measurable_pi_apply m).comp hmeas_rsp
  -- Case split: Pa = 0 or Pa ≠ 0
  by_cases hPa_zero : Pa = 0
  · simp [hPa_zero, Measure.map_zero]
  · -- Pa ≠ 0, so w := Pa(Ω) > 0 and w ≤ 1 < ⊤.
    -- Scale Pa by w⁻¹ to get a probability measure Qa.
    set w := Pa Set.univ with hw_def
    have hw_pos : 0 < w := by
      rw [pos_iff_ne_zero]; intro h; exact hPa_zero (Measure.measure_univ_eq_zero.mp h)
    have hw_ne_top : w ≠ ⊤ := by
      have : Pa Set.univ ≤ P Set.univ := by
        rw [show Pa = P.restrict {ω | ω 0 = a} from rfl,
            Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
        exact measure_mono (Set.subset_univ _)
      exact ne_top_of_le_ne_top (by simp [measure_univ]) this
    have hw_inv_ne_zero : w⁻¹ ≠ (0 : ENNReal) := ENNReal.inv_ne_zero.mpr hw_ne_top
    have hw_inv_ne_top : w⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr hw_pos.ne'
    set Qa := w⁻¹ • Pa with hQa_def
    have hQa_prob : Qa Set.univ = 1 := by
      rw [hQa_def, Measure.smul_apply, smul_eq_mul,
          ENNReal.inv_mul_cancel hw_pos.ne' hw_ne_top]
    haveI : IsProbabilityMeasure Qa := ⟨hQa_prob⟩
    -- Exchangeable Pa X implies Exchangeable Qa X (scaling preserves measure equality)
    have hExch_Qa : Exchangeability.Exchangeable Qa
        (fun n (ω : ℕ → Fin k) =>
          MarkovDeFinettiHard.rowSuccessorVisitProcess (k := k) i ω n) := by
      intro n' σ'
      simp only [hQa_def, Measure.map_smul]
      exact congr_arg (w⁻¹ • ·) (hExch n' σ')
    -- FullyExchangeable Qa X via exchangeable_iff_fullyExchangeable
    have hFull_Qa := (Exchangeability.exchangeable_iff_fullyExchangeable hX_meas).mp hExch_Qa
    -- FullyExchangeable Qa X for σ gives map equality for Qa
    have hσ_Qa := hFull_Qa σ
    -- Scale back: map f (w⁻¹ • Pa) = w⁻¹ • map f Pa, so w⁻¹ • LHS = w⁻¹ • RHS
    simp only [hQa_def, Measure.map_smul] at hσ_Qa
    -- hσ_Qa : w⁻¹ • map (... σ ...) Pa = w⁻¹ • map (...) Pa
    -- Cancel w⁻¹ using Measure.ext + ENNReal.mul_right_inj
    ext s hs
    have := congr_arg (· s) hσ_Qa
    simp only [Measure.smul_apply, smul_eq_mul] at this
    exact (ENNReal.mul_right_inj hw_inv_ne_zero hw_inv_ne_top).mp this

/-- The row process under P.restrict{ω₀=a} is ConditionallyIID (with some kernel).
Normalizes the restricted measure, applies de Finetti, then un-normalizes.
The kernel existence is the key output; kernel IDENTITY with the unrestricted
kernel requires separate uniqueness infrastructure. -/
theorem conditionallyIID_rowProcessLaw_restrict
    (hk : 0 < k)
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (hExt : ∀ xs : List (Fin k), μ xs = P (MarkovDeFinettiRecurrence.cylinder (k := k) xs))
    (hStrRec : MarkovDeFinettiHard.StrongRecurrence (k := k) P) (i a : Fin k) :
    Exchangeability.ConditionallyIID
      (MarkovDeFinettiHard.rowProcessLaw (k := k) (P.restrict {ω : ℕ → Fin k | ω 0 = a}) i)
      (fun n (r : ℕ → Fin k) => r n) := by
  set Pa := P.restrict {ω : ℕ → Fin k | ω 0 = a} with hPa_def
  have hmeas_rsp := MarkovDeFinettiHard.measurable_rowSuccessorVisitProcess (k := k) i
  by_cases hPa_zero : Pa = 0
  · -- Pa = 0: row process law is zero, ConditionallyIID holds vacuously
    simp only [hPa_zero, MarkovDeFinettiHard.rowProcessLaw, Measure.map_zero]
    haveI : Inhabited (Fin k) := ⟨⟨0, hk⟩⟩
    refine ⟨fun _ => Measure.dirac default, fun _ => inferInstance,
      fun B _hB => measurable_const, fun m sel _hsel => ?_⟩
    simp [Measure.map_zero, Measure.bind]
  · -- Pa ≠ 0: normalize, apply de Finetti, un-normalize
    set w := Pa Set.univ with hw_def
    have hw_pos : 0 < w := by
      rw [pos_iff_ne_zero]; intro h; exact hPa_zero (Measure.measure_univ_eq_zero.mp h)
    have hw_ne_top : w ≠ ⊤ :=
      ne_top_of_le_ne_top (by simp)
        (Measure.restrict_apply_univ _ ▸ measure_mono (Set.subset_univ _))
    set Qa := w⁻¹ • Pa with hQa_def
    haveI : IsProbabilityMeasure Qa := ⟨by
      rw [hQa_def, Measure.smul_apply, smul_eq_mul,
          ENNReal.inv_mul_cancel hw_pos.ne' hw_ne_top]⟩
    -- Perm invariance for Qa's row process law
    have hperm_Qa : ∀ σ : Equiv.Perm ℕ,
        Measure.map (MarkovDeFinettiHard.rowPermute (k := k) σ)
          (MarkovDeFinettiHard.rowProcessLaw (k := k) Qa i) =
        MarkovDeFinettiHard.rowProcessLaw (k := k) Qa i := by
      intro σ
      -- rowProcessLaw Qa = rowProcessLaw (w⁻¹ • Pa) = w⁻¹ • rowProcessLaw Pa
      simp only [MarkovDeFinettiHard.rowProcessLaw, hQa_def, Measure.map_smul]
      have hPa_perm := rowProcessLaw_restrict_permInvariant (k := k) μ hμ P hExt hStrRec i a σ
      -- hPa_perm : map(rowPermute σ)(rowProcessLaw Pa i) = rowProcessLaw Pa i
      -- Unfold rowProcessLaw in hPa_perm and use map_map
      show w⁻¹ • Measure.map (MarkovDeFinettiHard.rowPermute (k := k) σ)
          (Measure.map (MarkovDeFinettiHard.rowSuccessorVisitProcess (k := k) i) Pa) =
        w⁻¹ • Measure.map (MarkovDeFinettiHard.rowSuccessorVisitProcess (k := k) i) Pa
      exact congr_arg (w⁻¹ • ·) hPa_perm
    -- Apply de Finetti to Qa
    obtain ⟨ν, hν_prob, hν_meas, hν_eq⟩ :=
      MarkovDeFinettiHard.rowProcessLaw_conditionallyIID_of_perm_invariant
        (k := k) hk Qa i hperm_Qa
    -- ν is the ConditionallyIID kernel for (rowProcessLaw Qa i).
    -- rowProcessLaw Qa i = w⁻¹ • rowProcessLaw Pa i.
    -- Un-normalize: the bind identity scales linearly.
    refine ⟨ν, hν_prob, hν_meas, fun m sel hsel => ?_⟩
    have h_Qa := hν_eq m sel hsel
    -- h_Qa : map(proj_sel)(rowProcessLaw Qa i) = (rowProcessLaw Qa i).bind(pi(ν))
    -- rowProcessLaw Qa i = w⁻¹ • rowProcessLaw Pa i
    have hρ_scale : MarkovDeFinettiHard.rowProcessLaw (k := k) Qa i =
        w⁻¹ • MarkovDeFinettiHard.rowProcessLaw (k := k) Pa i := by
      simp [MarkovDeFinettiHard.rowProcessLaw, hQa_def, Measure.map_smul]
    rw [hρ_scale] at h_Qa
    -- h_Qa : map(proj_sel)(w⁻¹ • ρ) = (w⁻¹ • ρ).bind(pi(ν))
    -- LHS: map(f)(c • μ) = c • map(f)(μ)
    rw [Measure.map_smul] at h_Qa
    -- RHS: (c • μ).bind(g) = c • μ.bind(g)
    rw [show (w⁻¹ • MarkovDeFinettiHard.rowProcessLaw (k := k) Pa i).bind
        (fun r => Measure.pi fun _ : Fin m => ν r) =
      w⁻¹ • (MarkovDeFinettiHard.rowProcessLaw (k := k) Pa i).bind
        (fun r => Measure.pi fun _ : Fin m => ν r) from by
      simp [Measure.bind, Measure.map_smul, Measure.join_smul]] at h_Qa
    -- h_Qa : w⁻¹ • map(proj)(ρ) = w⁻¹ • ρ.bind(pi(ν))
    -- Cancel w⁻¹
    have hw_inv_ne_zero : w⁻¹ ≠ (0 : ENNReal) := ENNReal.inv_ne_zero.mpr hw_ne_top
    have hw_inv_ne_top : w⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr hw_pos.ne'
    ext s hs
    have := congr_arg (· s) h_Qa
    simp only [Measure.smul_apply, smul_eq_mul] at this
    exact (ENNReal.mul_right_inj hw_inv_ne_zero hw_inv_ne_top).mp this

end PerRowJointPE

end Mettapedia.Logic
