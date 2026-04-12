import Mettapedia.Logic.MarkovExchangeability

/-! LLM primer:
- `segmentSwap xs a L1 L2` transposes segments [a+1..a+L2] and [a+L2+1..a+L1+L2]
  in a trajectory xs : Fin (N+1) → Fin k.
- Boundary values xs(a), xs(a+L1), xs(a+L1+L2) must all be equal for transCount
  preservation (they're all visits to the anchor state i).
- Involutive: swap(a,L2,L1) ∘ swap(a,L1,L2) = id.
- Evidence preservation = start preservation + transCount preservation.

# Carrier Transport Core: Segment Swap Infrastructure

Ported from `_archive/MarkovDeFinetti/Logic/MarkovDeFinettiHardExcursionBridge.lean`
(1,206 lines, 0 sorry) into the active framework. This file focuses on the
core segment-swap definitions and properties. The finite evidence/fiber layer
now lives separately in `Mettapedia.Logic.MarkovDeFinettiEvidenceBasis`.

## Archived files referenced but not imported

- `_archive/.../MarkovDeFinettiHardExcursionBridge.lean` — source of segmentSwap
- `_archive/.../MarkovDeFinettiHardCopyPerm.lean` — edge-copy permutations (fiber counting)
- `_archive/.../MarkovDeFinettiHardEulerTrails.lean` — Euler trail ↔ trajectory
- `_archive/.../MarkovDeFinettiHardEulerTrailFiber.lean` — canonical edge labeling
- `_archive/.../MarkovDeFinettiHardBESTCore.lean` — EulerGraph, edgeTok, graphOfState

The Euler trail chain (3,265 lines, all 0 sorry) establishes that trajectories with
identical transition counts correspond to Euler trails on the same multigraph, related
by copy-index permutations. The segment swap is the constructive counterpart: it
explicitly builds the evidence-preserving bijection via excursion transposition.
-/

noncomputable section

namespace Mettapedia.Logic.MarkovDeFinettiCarrierTransport

open Mettapedia.Logic.MarkovExchangeability
open scoped BigOperators

variable {k : ℕ}

/-! ## Section 1: segmentSwap definition

Ported verbatim from `ExcursionBridge.lean:39-47`.
`Traj k N` in the archive is `Fin (N+1) → Fin k`, the same type used here. -/

/-- Swap two contiguous segments of lengths L1 and L2 in a trajectory,
starting after position `a`. The segment [a+1, a+L2] is replaced by
what was at [a+L1+1, a+L1+L2], and vice versa.

Uses dependent `if h :` so branch conditions are available in proofs. -/
def segmentSwap {N : ℕ} (xs : Fin (N + 1) → Fin k) (a L1 L2 : ℕ)
    (_hL1 : 0 < L1) (_hL2 : 0 < L2) (hcN : a + L1 + L2 ≤ N) :
    Fin (N + 1) → Fin k :=
  fun ⟨t, ht⟩ =>
    if _h1 : t ≤ a then xs ⟨t, ht⟩
    else if _h2 : t ≤ a + L2 then
      xs ⟨t + L1, by omega⟩
    else if _h3 : t ≤ a + L1 + L2 then
      xs ⟨t - L2, by omega⟩
    else xs ⟨t, ht⟩

/-! ## Section 2: Position remap and basic properties

Ported from `ExcursionBridge.lean:51-82, 200-298`. -/

/-- Position-level remapping underlying segmentSwap.
Maps [0,a] to itself, [a+1,a+L2] to [a+L1+1,a+L1+L2],
[a+L2+1,a+L1+L2] to [a+1,a+L1], and the rest to itself. -/
def swapRemap (a L1 L2 : ℕ) (t : ℕ) : ℕ :=
  if t < a then t
  else if t < a + L2 then t + L1
  else if t < a + L1 + L2 then t - L2
  else t

lemma swapRemap_lt {N : ℕ} (a L1 L2 : ℕ)
    (_hL1 : 0 < L1) (_hL2 : 0 < L2) (hcN : a + L1 + L2 ≤ N)
    (t : ℕ) (ht : t < N) : swapRemap a L1 L2 t < N := by
  simp only [swapRemap]; split_ifs <;> omega

/-- The position remap as a Fin-level function. -/
def swapPermFin {N : ℕ} (a L1 L2 : ℕ)
    (hL1 : 0 < L1) (hL2 : 0 < L2) (hcN : a + L1 + L2 ≤ N) :
    Fin N → Fin N :=
  fun ⟨t, ht⟩ => ⟨swapRemap a L1 L2 t, swapRemap_lt a L1 L2 hL1 hL2 hcN t ht⟩

lemma swapPermFin_injective {N : ℕ} (a L1 L2 : ℕ)
    (hL1 : 0 < L1) (hL2 : 0 < L2) (hcN : a + L1 + L2 ≤ N) :
    Function.Injective (swapPermFin (N := N) a L1 L2 hL1 hL2 hcN) := by
  intro ⟨t₁, ht₁⟩ ⟨t₂, ht₂⟩ h
  have h' : swapRemap a L1 L2 t₁ = swapRemap a L1 L2 t₂ := by
    simp only [swapPermFin, Fin.mk.injEq] at h; exact h
  apply Fin.ext; show t₁ = t₂
  simp only [swapRemap] at h'
  split_ifs at h' with h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  all_goals omega

lemma swapPermFin_bijective {N : ℕ} (a L1 L2 : ℕ)
    (hL1 : 0 < L1) (hL2 : 0 < L2) (hcN : a + L1 + L2 ≤ N) :
    Function.Bijective (swapPermFin (N := N) a L1 L2 hL1 hL2 hcN) := by
  rw [Fintype.bijective_iff_injective_and_card]
  exact ⟨swapPermFin_injective a L1 L2 hL1 hL2 hcN, by simp⟩

/-! ## Section 3: Transition pair correspondence and transCount preservation

Ported from `ExcursionBridge.lean:86-145`.
GENERALIZED: boundary condition uses `xs(a) = xs(a+L1) = xs(a+L1+L2)`
(not necessarily `= xs 0`). The original archive required `= xs 0`. -/

/-- Each transition pair in the swapped trajectory corresponds to a
remapped transition pair in the original. -/
theorem segmentSwap_transition_pair {N : ℕ} (xs : Fin (N + 1) → Fin k) (a L1 L2 : ℕ)
    (hL1 : 0 < L1) (hL2 : 0 < L2) (hcN : a + L1 + L2 ≤ N)
    (ha_val : xs ⟨a, by omega⟩ = xs ⟨a + L1, by omega⟩)
    (hb_val : xs ⟨a + L1, by omega⟩ = xs ⟨a + L1 + L2, by omega⟩)
    (j : Fin N) :
    let σj := swapPermFin a L1 L2 hL1 hL2 hcN j
    (segmentSwap xs a L1 L2 hL1 hL2 hcN (Fin.castSucc j),
     segmentSwap xs a L1 L2 hL1 hL2 hcN (Fin.succ j)) =
    (xs (Fin.castSucc σj), xs (Fin.succ σj)) := by
  rcases j with ⟨t, ht⟩
  simp only [swapPermFin, swapRemap]
  rw [Prod.mk.injEq]
  simp only [segmentSwap, Fin.castSucc_mk, Fin.succ_mk]
  -- Helper: positions at boundaries a, a+L1, a+L1+L2 all give the same value
  have to_anchor : ∀ (i : Fin (N + 1)),
      i.val = a ∨ i.val = a + L1 ∨ i.val = a + L1 + L2 →
        xs i = xs ⟨a + L1, by omega⟩ := by
    intro i h
    rcases h with h | h | h
    · exact (congrArg xs (Fin.ext h)).trans ha_val
    · exact congrArg xs (Fin.ext h)
    · exact (congrArg xs (Fin.ext h)).trans hb_val.symm
  constructor <;> split_ifs <;>
    first
    | rfl
    | (congr 1; ext; simp; omega)
    | omega
    | (refine (to_anchor _ ?_).trans (to_anchor _ ?_).symm <;> simp <;> omega)

/-- Transition counts are preserved by segmentSwap when all three boundary
positions map to the same state.

Generalized from the archive: the boundary condition is
`xs(a) = xs(a+L1) = xs(a+L1+L2)` (arbitrary common value, not necessarily xs 0). -/
theorem segmentSwap_transCount {N : ℕ} (xs : Fin (N + 1) → Fin k) (a L1 L2 : ℕ)
    (hL1 : 0 < L1) (hL2 : 0 < L2) (hcN : a + L1 + L2 ≤ N)
    (ha_val : xs ⟨a, by omega⟩ = xs ⟨a + L1, by omega⟩)
    (hb_val : xs ⟨a + L1, by omega⟩ = xs ⟨a + L1 + L2, by omega⟩)
    (α β : Fin k) :
    transCount (n := N) (segmentSwap xs a L1 L2 hL1 hL2 hcN) α β =
      transCount (n := N) xs α β := by
  simp only [transCount]
  let σ := swapPermFin (N := N) a L1 L2 hL1 hL2 hcN
  have hσ := swapPermFin_bijective (N := N) a L1 L2 hL1 hL2 hcN
  have hfilt_eq : (Finset.univ.filter (fun j : Fin N =>
      segmentSwap xs a L1 L2 hL1 hL2 hcN (Fin.castSucc j) = α ∧
      segmentSwap xs a L1 L2 hL1 hL2 hcN (Fin.succ j) = β)) =
    (Finset.univ.filter (fun j : Fin N =>
      xs (Fin.castSucc (σ j)) = α ∧ xs (Fin.succ (σ j)) = β)) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have h := segmentSwap_transition_pair xs a L1 L2 hL1 hL2 hcN ha_val hb_val j
    simp only at h; rw [Prod.mk.injEq] at h; rw [h.1, h.2]
  rw [hfilt_eq]
  apply Finset.card_bij (fun j _ => σ j)
  · intro j hj; simpa using hj
  · intro j₁ _ j₂ _ h; exact hσ.1 h
  · intro j hj
    obtain ⟨j', rfl⟩ := hσ.2 j
    exact ⟨j', by simpa using hj, rfl⟩

/-! ## Section 4: Start, last, and evidence preservation -/

/-- segmentSwap preserves the start state (position 0 is always ≤ a since a ≥ 0). -/
lemma segmentSwap_start {N : ℕ} (xs : Fin (N + 1) → Fin k) (a L1 L2 : ℕ)
    (hL1 : 0 < L1) (hL2 : 0 < L2) (hcN : a + L1 + L2 ≤ N) :
    segmentSwap xs a L1 L2 hL1 hL2 hcN 0 = xs 0 := by
  simp [segmentSwap]

/-- segmentSwap preserves the last element when boundary returns hold. -/
lemma segmentSwap_last {N : ℕ} (xs : Fin (N + 1) → Fin k) (a L1 L2 : ℕ)
    (hL1 : 0 < L1) (hL2 : 0 < L2) (hcN : a + L1 + L2 ≤ N)
    (_ha_val : xs ⟨a, by omega⟩ = xs ⟨a + L1, by omega⟩)
    (hb_val : xs ⟨a + L1, by omega⟩ = xs ⟨a + L1 + L2, by omega⟩) :
    segmentSwap xs a L1 L2 hL1 hL2 hcN (Fin.last N) = xs (Fin.last N) := by
  simp only [segmentSwap, Fin.last]
  split_ifs with h1 h2 h3
  · omega
  · omega
  · -- N ≤ a + L1 + L2: boundary case
    -- The goal is: xs ⟨N - L2, _⟩ = xs ⟨N, _⟩
    -- We know h3 : N ≤ a + L1 + L2, and hcN : a + L1 + L2 ≤ N, so N = a + L1 + L2
    -- xs(N - L2) = xs(a + L1), and xs(N) = xs(a + L1 + L2) = xs(a + L1) by hb_val
    have hN_eq : N = a + L1 + L2 := by omega
    have h_nml2 : N - L2 = a + L1 := by omega
    have : (⟨N - L2, by omega⟩ : Fin (N + 1)).val = (⟨a + L1, by omega⟩ : Fin (N + 1)).val := by
      simp [h_nml2]
    have heq1 : xs ⟨N - L2, by omega⟩ = xs ⟨a + L1, by omega⟩ := by
      congr 1; exact Fin.ext this
    have hNeq : (⟨N, by omega⟩ : Fin (N + 1)).val = (⟨a + L1 + L2, by omega⟩ : Fin (N + 1)).val := by
      simp [hN_eq]
    have heq2 : xs ⟨N, by omega⟩ = xs ⟨a + L1 + L2, by omega⟩ := by
      congr 1; exact Fin.ext hNeq
    rw [heq1, heq2]
    exact hb_val
  · rfl

/-- **NEW**: segmentSwap preserves MarkovEvidence (start + transition counts).
This is the key property for carrier transport. -/
theorem segmentSwap_evidenceOf {N : ℕ} (xs : Fin (N + 1) → Fin k) (a L1 L2 : ℕ)
    (hL1 : 0 < L1) (hL2 : 0 < L2) (hcN : a + L1 + L2 ≤ N)
    (ha_val : xs ⟨a, by omega⟩ = xs ⟨a + L1, by omega⟩)
    (hb_val : xs ⟨a + L1, by omega⟩ = xs ⟨a + L1 + L2, by omega⟩) :
    evidenceOf (n := N) (segmentSwap xs a L1 L2 hL1 hL2 hcN) =
      evidenceOf (n := N) xs := by
  refine MarkovEvidence.ext ?_ ?_
  · -- start field
    exact segmentSwap_start xs a L1 L2 hL1 hL2 hcN
  · -- trans field
    funext α β
    exact segmentSwap_transCount xs a L1 L2 hL1 hL2 hcN ha_val hb_val α β

/-! ## Section 5: Involutivity and Equiv packaging -/

/-- segmentSwap is an involution: swapping with (a, L2, L1) undoes (a, L1, L2). -/
theorem segmentSwap_involutive {N : ℕ} (xs : Fin (N + 1) → Fin k) (a L1 L2 : ℕ)
    (hL1 : 0 < L1) (hL2 : 0 < L2) (hcN : a + L1 + L2 ≤ N) :
    segmentSwap (segmentSwap xs a L1 L2 hL1 hL2 hcN) a L2 L1 hL2 hL1
      (by omega) = xs := by
  funext ⟨t, ht⟩
  simp only [segmentSwap]
  split_ifs <;> first | rfl | (congr 1; ext; dsimp only; omega)

/-- segmentSwap packaged as a permutation (self-inverse bijection). -/
def segmentSwapEquiv {N : ℕ} (a L1 L2 : ℕ)
    (hL1 : 0 < L1) (hL2 : 0 < L2) (hcN : a + L1 + L2 ≤ N) :
    Equiv.Perm (Fin (N + 1) → Fin k) where
  toFun xs := segmentSwap xs a L1 L2 hL1 hL2 hcN
  invFun xs := segmentSwap xs a L2 L1 hL2 hL1 (by omega)
  left_inv xs := segmentSwap_involutive xs a L1 L2 hL1 hL2 hcN
  right_inv xs := segmentSwap_involutive xs a L2 L1 hL2 hL1 (by omega)

/-! ## Section 6: Prefix/suffix invariance -/

/-- segmentSwap is the identity on positions ≤ a. -/
lemma segmentSwap_eq_of_le {N : ℕ} (xs : Fin (N + 1) → Fin k) (a L1 L2 : ℕ)
    (hL1 : 0 < L1) (hL2 : 0 < L2) (hcN : a + L1 + L2 ≤ N)
    (i : Fin (N + 1)) (hi : (i : ℕ) ≤ a) :
    segmentSwap xs a L1 L2 hL1 hL2 hcN i = xs i := by
  simp [segmentSwap, hi]

/-- segmentSwap is the identity on positions > a + L1 + L2. -/
lemma segmentSwap_eq_of_gt {N : ℕ} (xs : Fin (N + 1) → Fin k) (a L1 L2 : ℕ)
    (hL1 : 0 < L1) (hL2 : 0 < L2) (hcN : a + L1 + L2 ≤ N)
    (i : Fin (N + 1)) (hi : a + L1 + L2 < (i : ℕ)) :
    segmentSwap xs a L1 L2 hL1 hL2 hcN i = xs i := by
  have h1 : ¬((i : ℕ) ≤ a) := by omega
  have h2 : ¬((i : ℕ) ≤ a + L2) := by omega
  have h3 : ¬((i : ℕ) ≤ a + L1 + L2) := by omega
  simp [segmentSwap, h1, h2, h3]

/-- segmentSwap at position a gives the original value (boundary case). -/
lemma segmentSwap_at_a {N : ℕ} (xs : Fin (N + 1) → Fin k) (a L1 L2 : ℕ)
    (hL1 : 0 < L1) (hL2 : 0 < L2) (hcN : a + L1 + L2 ≤ N) :
    segmentSwap xs a L1 L2 hL1 hL2 hcN ⟨a, by omega⟩ = xs ⟨a, by omega⟩ := by
  simp [segmentSwap]

/-- segmentSwap at position a + L1 + L2 gives xs(a + L1) (the mid-boundary). -/
lemma segmentSwap_at_end {N : ℕ} (xs : Fin (N + 1) → Fin k) (a L1 L2 : ℕ)
    (hL1 : 0 < L1) (hL2 : 0 < L2) (hcN : a + L1 + L2 ≤ N) :
    segmentSwap xs a L1 L2 hL1 hL2 hcN ⟨a + L1 + L2, by omega⟩ =
      xs ⟨a + L1, by omega⟩ := by
  simp only [segmentSwap]
  split_ifs with h1 h2 h3
  · omega
  · omega
  · show xs ⟨a + L1 + L2 - L2, _⟩ = xs ⟨a + L1, _⟩
    congr 1; ext; show a + L1 + L2 - L2 = a + L1; omega
  · omega

/-- segmentSwap at position a + L2 gives xs(a + L1 + L2) (the other boundary). -/
lemma segmentSwap_at_mid {N : ℕ} (xs : Fin (N + 1) → Fin k) (a L1 L2 : ℕ)
    (hL1 : 0 < L1) (hL2 : 0 < L2) (hcN : a + L1 + L2 ≤ N) :
    segmentSwap xs a L1 L2 hL1 hL2 hcN ⟨a + L2, by omega⟩ =
      xs ⟨a + L1 + L2, by omega⟩ := by
  simp only [segmentSwap]
  split_ifs with h1 h2 h3
  · omega
  · congr 1; ext; simp; omega
  · omega
  · omega

/-- segmentSwap at position a + 1 gives xs(a + L1 + 1): the first position of the
second excursion maps to the first position of the first excursion. -/
lemma segmentSwap_successor_at_a {N : ℕ} (xs : Fin (N + 1) → Fin k) (a L1 L2 : ℕ)
    (hL1 : 0 < L1) (hL2 : 0 < L2) (hcN : a + L1 + L2 ≤ N) :
    segmentSwap xs a L1 L2 hL1 hL2 hcN ⟨a + 1, by omega⟩ =
      xs ⟨a + L1 + 1, by omega⟩ := by
  simp only [segmentSwap]
  split_ifs with h1 h2 h3
  · omega
  · congr 1; ext; simp; omega
  · omega
  · omega

/-- segmentSwap at position a + L2 + 1 gives xs(a + 1): the successor at the
(n+1)-th visit maps to the successor at the n-th visit. -/
lemma segmentSwap_successor_at_mid {N : ℕ} (xs : Fin (N + 1) → Fin k) (a L1 L2 : ℕ)
    (hL1 : 0 < L1) (hL2 : 0 < L2) (hcN : a + L1 + L2 ≤ N) :
    segmentSwap xs a L1 L2 hL1 hL2 hcN ⟨a + L2 + 1, by omega⟩ =
      xs ⟨a + 1, by omega⟩ := by
  simp only [segmentSwap]
  split_ifs with h1 h2 h3
  · omega
  · omega
  · congr 1; ext; simp; omega
  · omega

/-! ## Section 7: segmentSwap is identity on positions outside [a+1, a+L1+L2]

This gives the queue transposition property: segmentSwap at the n-th and (n+1)-th
visits to state i only affects the successors at those two visits. All other
successor values are unchanged (their times are outside the swap region). -/

/-- segmentSwap preserves the value at any position t with t+1 ≤ a (successor before swap). -/
lemma segmentSwap_successor_preserved_before {N : ℕ} (xs : Fin (N + 1) → Fin k) (a L1 L2 : ℕ)
    (hL1 : 0 < L1) (hL2 : 0 < L2) (hcN : a + L1 + L2 ≤ N)
    (t : ℕ) (ht : t + 1 ≤ a) (htN : t + 1 ≤ N) :
    segmentSwap xs a L1 L2 hL1 hL2 hcN ⟨t + 1, by omega⟩ =
      xs ⟨t + 1, by omega⟩ :=
  segmentSwap_eq_of_le xs a L1 L2 hL1 hL2 hcN ⟨t + 1, by omega⟩ (by omega)

/-- segmentSwap preserves the value at any position t+1 with t ≥ a+L1+L2. -/
lemma segmentSwap_successor_preserved_after {N : ℕ} (xs : Fin (N + 1) → Fin k) (a L1 L2 : ℕ)
    (hL1 : 0 < L1) (hL2 : 0 < L2) (hcN : a + L1 + L2 ≤ N)
    (t : ℕ) (ht : a + L1 + L2 ≤ t) (htN : t + 1 ≤ N) :
    segmentSwap xs a L1 L2 hL1 hL2 hcN ⟨t + 1, by omega⟩ =
      xs ⟨t + 1, by omega⟩ :=
  segmentSwap_eq_of_gt xs a L1 L2 hL1 hL2 hcN ⟨t + 1, by omega⟩ (by simp; omega)

end Mettapedia.Logic.MarkovDeFinettiCarrierTransport
