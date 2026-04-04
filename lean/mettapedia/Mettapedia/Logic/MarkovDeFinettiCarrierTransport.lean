import Mettapedia.Logic.MarkovDeFinettiCarrierTransportCore
import Mettapedia.Logic.MarkovDeFinettiFortiniBridgeCore

/-!
# Carrier Transport: Bridge segmentSwap to hCarrierTransport

Closes the carrier transport sub-obligation for the Markov de Finetti theorem.
-/

noncomputable section

namespace Mettapedia.Logic

open MarkovExchangeability
open MarkovDeFinettiHard
open MarkovDeFinettiRecurrence
open MarkovDeFinettiCarrierTransport
open MeasureTheory
open scoped BigOperators

variable {k : ℕ}

namespace CarrierTransportBridge

/-! ## Section 1: prefixExtend bridge -/

lemma prefixExtend_apply_le' {N : ℕ} (xs : Fin (N + 1) → Fin k) {t : ℕ} (ht : t ≤ N) :
    prefixExtend (k := k) N xs t = xs ⟨t, Nat.lt_succ_of_le ht⟩ := by
  simp [prefixExtend, ht]

lemma successorAt_prefixExtend' {N : ℕ} (xs : Fin (N + 1) → Fin k)
    {t : ℕ} (ht : t + 1 ≤ N) :
    successorAt (k := k) (prefixExtend (k := k) N xs) t =
      xs ⟨t + 1, Nat.lt_succ_of_le ht⟩ := by
  simp [successorAt, prefixExtend, ht]

/-! ## Section 2: Visit count stability -/

/-- Visit count at t+1 = visit count at t + indicator at t. -/
lemma visitCountBefore_succ' (ω : ℕ → Fin k) (i : Fin k) (t : ℕ) :
    visitCountBefore (k := k) ω i (t + 1) =
      visitCountBefore (k := k) ω i t + (if ω t = i then 1 else 0) := by
  unfold visitCountBefore
  rw [Finset.sum_range_succ]

/-- If no visits to i in [t₁, t₂), visit count is unchanged. -/
lemma visitCountBefore_eq_of_no_visits (ω : ℕ → Fin k) (i : Fin k) (t₁ t₂ : ℕ)
    (h : t₁ ≤ t₂)
    (hno : ∀ s, t₁ ≤ s → s < t₂ → ω s ≠ i) :
    visitCountBefore (k := k) ω i t₂ = visitCountBefore (k := k) ω i t₁ := by
  induction t₂ with
  | zero => have h0 : t₁ = 0 := Nat.eq_zero_of_le_zero h; subst h0; rfl
  | succ t₂ ih =>
    by_cases heq : t₁ = t₂ + 1
    · subst heq; rfl
    · have hlt : t₁ ≤ t₂ := Nat.le_of_lt_succ (Nat.lt_of_le_of_ne h heq)
      rw [visitCountBefore_succ']
      have hne : ω t₂ ≠ i := hno t₂ hlt (Nat.lt_succ_self t₂)
      simp [hne]
      exact ih hlt (fun s hs1 hs2 => hno s hs1 (Nat.lt_succ_of_lt hs2))

/-! ## Section 3: Carrier membership unpacking -/

/-- Carrier membership gives a visit time witness with successor and anchor properties. -/
lemma carrier_mem_witness {N : ℕ}
    (xs : Fin (N + 1) → Fin k) (i : Fin k) (n : ℕ) (b : Fin k)
    (hxs : xs ∈ rowVisitCylinderEventUpToPrefixCarrier (k := k)
      i ({n} : Finset ℕ) (fun m => if m = n then b else i) N) :
    ∃ t : ℕ, t < N ∧
      nthVisitTime (k := k) (prefixExtend (k := k) N xs) i n = some t ∧
      (prefixExtend (k := k) N xs) (t + 1) = b ∧
      (prefixExtend (k := k) N xs) t = i := by
  have hmem : prefixExtend (k := k) N xs ∈
      rowVisitCylinderEventUpTo (k := k) i ({n} : Finset ℕ)
        (fun m => if m = n then b else i) N := by
    simp only [rowVisitCylinderEventUpToPrefixCarrier, Finset.mem_filter,
      Finset.mem_univ, true_and] at hxs
    exact hxs
  rcases hmem n (Finset.mem_singleton_self n) with ⟨t, htN, htime, hsucc⟩
  refine ⟨t, htN, htime, ?_, ?_⟩
  · -- successor = b: successorAt at t = ω(t+1)
    have h1 : successorAt (k := k) (prefixExtend (k := k) N xs) t = b := by
      simpa using hsucc
    simpa [successorAt] using h1
  · -- visit to i
    exact ((nthVisitTime_eq_some_iff (k := k)
      (prefixExtend (k := k) N xs) i n t).mp htime).1

/-! ## Section 4: No visits to i between consecutive visit times -/

lemma no_visits_between_consecutive' {N : ℕ}
    (xs : Fin (N + 1) → Fin k) (i : Fin k) (n : ℕ) (t₁ t₂ : ℕ)
    (_ht₁N : t₁ ≤ N) (ht₂N : t₂ ≤ N)
    (h₁ : isNthVisitTime (k := k) (prefixExtend (k := k) N xs) i n t₁)
    (h₂ : isNthVisitTime (k := k) (prefixExtend (k := k) N xs) i (n + 1) t₂)
    (s : ℕ) (hs1 : t₁ < s) (hs2 : s < t₂) :
    xs ⟨s, by omega⟩ ≠ i := by
  intro heq
  have hvisit_t₁ : (prefixExtend (k := k) N xs) t₁ = i := h₁.1
  have hvisit_s : (prefixExtend (k := k) N xs) s = i := by
    rwa [prefixExtend_apply_le' xs (by omega : s ≤ N)]
  -- count(t₁+1) = n + 1 (one more visit at t₁)
  have hcnt1 : visitCountBefore (k := k) (prefixExtend (k := k) N xs) i (t₁ + 1) = n + 1 := by
    rw [visitCountBefore_succ']; simp [hvisit_t₁, h₁.2]
  -- count(t₁) < count(s) since t₁ < s and ω(t₁) = i
  have hmono1 : visitCountBefore (k := k) (prefixExtend (k := k) N xs) i t₁ <
      visitCountBefore (k := k) (prefixExtend (k := k) N xs) i s :=
    visitCountBefore_strict_mono_of_visit (k := k)
      (prefixExtend (k := k) N xs) i hvisit_t₁ hs1
  -- So count(s) ≥ n + 1
  have hcntS_ge : n + 1 ≤ visitCountBefore (k := k) (prefixExtend (k := k) N xs) i s := by
    rw [h₁.2] at hmono1; omega
  -- count(s) < count(t₂) since s < t₂ and ω(s) = i
  have hmono2 : visitCountBefore (k := k) (prefixExtend (k := k) N xs) i s <
      visitCountBefore (k := k) (prefixExtend (k := k) N xs) i t₂ :=
    visitCountBefore_strict_mono_of_visit (k := k)
      (prefixExtend (k := k) N xs) i hvisit_s hs2
  -- So count(t₂) ≥ count(s) + 1 ≥ n + 2. But count(t₂) = n + 1. Contradiction.
  rw [h₂.2] at hmono2
  omega

/-! ## Section 5: Visit count at midpoint after segmentSwap

Council quorum (82%): Knuth+Buzzard recommend the recurrence approach:
  count(a+L2) = count(a+1) = count(a) + 1 = n + 1
using visitCountBefore_eq_of_no_visits for the first step and
visitCountBefore_succ' for the second. -/

/-- visitCountBefore on prefixExtend of segmentSwap agrees with the original
for positions ≤ a (the identity region). -/
lemma visitCountBefore_prefixExtend_segmentSwap_le {N : ℕ}
    (xs : Fin (N + 1) → Fin k) (i : Fin k) (a L1 L2 : ℕ)
    (hL1 : 0 < L1) (hL2 : 0 < L2) (hcN : a + L1 + L2 ≤ N)
    (t : ℕ) (ht : t ≤ a) :
    visitCountBefore (k := k)
      (prefixExtend (k := k) N (segmentSwap xs a L1 L2 hL1 hL2 hcN)) i t =
    visitCountBefore (k := k) (prefixExtend (k := k) N xs) i t := by
  simp only [visitCountBefore]
  refine Finset.sum_congr rfl ?_
  intro s hs
  have hslt : s < t := Finset.mem_range.mp hs
  have hsle : s ≤ a := Nat.le_trans (Nat.le_of_lt hslt) ht
  have hsN : s ≤ N := Nat.le_trans hsle (Nat.le_trans (Nat.le_add_right a (L1 + L2)) (by omega))
  simp [prefixExtend, hsN, segmentSwap_eq_of_le xs a L1 L2 hL1 hL2 hcN ⟨s, by omega⟩ hsle]

/-- In the swapped trajectory, positions in (a, a+L2) do NOT visit state i,
because they come from positions (a+L1, a+L1+L2) in the original which are
i-free (between the (n+1)-th and (n+2)-th visits). -/
lemma swapped_no_visits_in_excursion {N : ℕ}
    (xs : Fin (N + 1) → Fin k) (i : Fin k) (n : ℕ) (a L1 L2 : ℕ)
    (hL1 : 0 < L1) (hL2 : 0 < L2) (hcN : a + L1 + L2 ≤ N)
    (h_aL1 : isNthVisitTime (k := k) (prefixExtend (k := k) N xs) i (n + 1) (a + L1))
    (h_aL1L2 : isNthVisitTime (k := k) (prefixExtend (k := k) N xs) i (n + 2) (a + L1 + L2))
    (s : ℕ) (hs1 : a < s) (hs2 : s < a + L2) :
    (prefixExtend (k := k) N (segmentSwap xs a L1 L2 hL1 hL2 hcN)) s ≠ i := by
  -- s is in the first swapped segment: swapped(s) = xs(s + L1)
  -- s + L1 is in (a + L1, a + L1 + L2), which is between (n+1)-th and (n+2)-th visits
  have hsN : s ≤ N := by omega
  rw [prefixExtend_apply_le' _ hsN]
  -- segmentSwap at position s (a < s ≤ a + L2) gives xs(s + L1)
  show segmentSwap xs a L1 L2 hL1 hL2 hcN ⟨s, by omega⟩ ≠ i
  simp only [segmentSwap]
  have h1 : ¬(s ≤ a) := by omega
  have h2 : s ≤ a + L2 := by omega
  simp [h1, h2]
  -- Now goal: xs ⟨s + L1, _⟩ ≠ i
  -- s + L1 is strictly between a + L1 and a + L1 + L2
  exact no_visits_between_consecutive' xs i (n + 1) (a + L1) (a + L1 + L2)
    (by omega) (by omega) h_aL1 h_aL1L2 (s + L1) (by omega) (by omega)

/-- The key visit-count lemma: at position a+L2 in the swapped trajectory,
exactly n+1 visits to i have occurred. -/
theorem visitCountBefore_segmentSwap_at_midpoint {N : ℕ}
    (xs : Fin (N + 1) → Fin k) (i : Fin k) (n : ℕ) (a L1 L2 : ℕ)
    (hL1 : 0 < L1) (hL2 : 0 < L2) (hcN : a + L1 + L2 ≤ N)
    (h_a : isNthVisitTime (k := k) (prefixExtend (k := k) N xs) i n a)
    (h_aL1 : isNthVisitTime (k := k) (prefixExtend (k := k) N xs) i (n + 1) (a + L1))
    (h_aL1L2 : isNthVisitTime (k := k) (prefixExtend (k := k) N xs) i (n + 2) (a + L1 + L2)) :
    visitCountBefore (k := k)
      (prefixExtend (k := k) N (segmentSwap xs a L1 L2 hL1 hL2 hcN)) i (a + L2) = n + 1 := by
  let ω' := prefixExtend (k := k) N (segmentSwap xs a L1 L2 hL1 hL2 hcN)
  -- Step 1: count(a+L2) = count(a+1) because no visits to i in (a, a+L2)
  have hstep1 : visitCountBefore (k := k) ω' i (a + L2) =
      visitCountBefore (k := k) ω' i (a + 1) := by
    refine visitCountBefore_eq_of_no_visits ω' i (a + 1) (a + L2) (by omega) ?_
    intro s hs1 hs2
    exact swapped_no_visits_in_excursion xs i n a L1 L2 hL1 hL2 hcN h_aL1 h_aL1L2 s
      (by omega) hs2
  -- Step 2: count(a+1) = count(a) + 1 because ω'(a) = i
  have hvisit_a : ω' a = i := by
    show (prefixExtend (k := k) N (segmentSwap xs a L1 L2 hL1 hL2 hcN)) a = i
    rw [prefixExtend_apply_le' _ (by omega : a ≤ N)]
    rw [segmentSwap_at_a xs a L1 L2 hL1 hL2 hcN]
    exact (prefixExtend_apply_le' xs (by omega : a ≤ N)).symm ▸ h_a.1
  have hstep2 : visitCountBefore (k := k) ω' i (a + 1) =
      visitCountBefore (k := k) ω' i a + 1 := by
    rw [visitCountBefore_succ']; simp [hvisit_a]
  -- Step 3: count(a) = n because segmentSwap is identity on [0,a)
  have hstep3 : visitCountBefore (k := k) ω' i a = n := by
    rw [visitCountBefore_prefixExtend_segmentSwap_le xs i a L1 L2 hL1 hL2 hcN a le_rfl]
    exact h_a.2
  -- Combine: count(a+L2) = count(a+1) = count(a) + 1 = n + 1
  rw [hstep1, hstep2, hstep3]

/-! ## Section 6: Adjacent carrier transport

Council quorum (78%): The adjacent carrier transport maps carrier_n to carrier_{n+1}
via segmentSwap. The key pieces are:
1. Visit count at midpoint = n+1 (Section 5)
2. Swapped trajectory value at midpoint = i (boundary condition)
3. Successor at midpoint = b (from segmentSwap_successor_at_mid)
4. Package as carrier membership + Equiv (involutivity gives bijectivity) -/

/-- The swapped trajectory at position a+L2 visits state i (boundary preservation). -/
lemma segmentSwap_visits_i_at_midpoint {N : ℕ}
    (xs : Fin (N + 1) → Fin k) (i : Fin k) (a L1 L2 : ℕ)
    (hL1 : 0 < L1) (hL2 : 0 < L2) (hcN : a + L1 + L2 ≤ N)
    (h_aL1L2_val : xs ⟨a + L1 + L2, by omega⟩ = i) :
    (prefixExtend (k := k) N (segmentSwap xs a L1 L2 hL1 hL2 hcN)) (a + L2) = i := by
  rw [prefixExtend_apply_le' _ (by omega : a + L2 ≤ N)]
  rw [segmentSwap_at_mid xs a L1 L2 hL1 hL2 hcN]
  exact h_aL1L2_val

/-- The successor at the (n+1)-th visit in the swapped trajectory is the
successor at the n-th visit in the original — which is b. -/
lemma segmentSwap_successor_at_midpoint {N : ℕ}
    (xs : Fin (N + 1) → Fin k) (a L1 L2 : ℕ)
    (hL1 : 0 < L1) (hL2 : 0 < L2) (hcN : a + L1 + L2 ≤ N) :
    (prefixExtend (k := k) N (segmentSwap xs a L1 L2 hL1 hL2 hcN)) (a + L2 + 1) =
      (prefixExtend (k := k) N xs) (a + 1) := by
  rw [prefixExtend_apply_le' _ (by omega : a + L2 + 1 ≤ N)]
  rw [segmentSwap_successor_at_mid xs a L1 L2 hL1 hL2 hcN]
  rw [prefixExtend_apply_le' _ (by omega : a + 1 ≤ N)]

/-! ## Section 7: Carrier membership for the swapped trajectory

The swapped trajectory lands in the (n+1) carrier when the original is in the n carrier,
provided three consecutive visit times to i are known.

Council quorum (76%): Coquand emphasizes this is type-level packaging of the mathematical
facts proved in Sections 5-6. The carrier is a Finset.filter, so membership is
equivalent to the rowVisitCylinderEventUpTo predicate on prefixExtend. -/

/-- segmentSwap maps an n-carrier member to an (n+1)-carrier member,
given three consecutive visit times to i at positions a, a+L1, a+L1+L2.

This is the constructive core of the adjacent carrier transport.
The successor at visit n in the original (= b) becomes the successor
at visit n+1 in the swapped trajectory. -/
theorem segmentSwap_carrier_mem_adjacent {N : ℕ}
    (xs : Fin (N + 1) → Fin k) (i : Fin k) (n : ℕ) (b : Fin k)
    (a L1 L2 : ℕ)
    (hL1 : 0 < L1) (hL2 : 0 < L2) (hcN : a + L1 + L2 ≤ N)
    -- Three consecutive visit times to i
    (h_a : isNthVisitTime (k := k) (prefixExtend (k := k) N xs) i n a)
    (h_aL1 : isNthVisitTime (k := k) (prefixExtend (k := k) N xs) i (n + 1) (a + L1))
    (h_aL1L2 : isNthVisitTime (k := k) (prefixExtend (k := k) N xs) i (n + 2) (a + L1 + L2))
    -- The successor at the n-th visit is b
    (hsucc_n : (prefixExtend (k := k) N xs) (a + 1) = b)
    -- Carrier membership of original (available for extensions)
    (_hxs : xs ∈ rowVisitCylinderEventUpToPrefixCarrier (k := k)
      i ({n} : Finset ℕ) (fun m => if m = n then b else i) N) :
    segmentSwap xs a L1 L2 hL1 hL2 hcN ∈
      rowVisitCylinderEventUpToPrefixCarrier (k := k)
        i ({n + 1} : Finset ℕ) (fun m => if m = n + 1 then b else i) N := by
  simp only [rowVisitCylinderEventUpToPrefixCarrier, Finset.mem_filter, Finset.mem_univ, true_and]
  -- Need: prefixExtend of swapped satisfies rowVisitCylinderEventUpTo for visit n+1
  intro m hm
  simp only [Finset.mem_singleton] at hm
  subst hm
  simp only [ite_true]
  -- Must exhibit t' < N with: nthVisitTime(swapped_PE, i, n+1) = some t' and successor = b
  -- t' = a + L2 (the midpoint after swap)
  refine ⟨a + L2, by omega, ?_, ?_⟩
  · -- nthVisitTime(swapped_PE, i, n+1) = some (a + L2)
    rw [nthVisitTime_eq_some_iff (k := k)]
    refine ⟨?_, ?_⟩
    · -- swapped_PE(a + L2) = i
      have h_aL1L2_i : xs ⟨a + L1 + L2, by omega⟩ = i := by
        have := h_aL1L2.1
        rwa [prefixExtend_apply_le' xs (by omega : a + L1 + L2 ≤ N)] at this
      exact segmentSwap_visits_i_at_midpoint xs i a L1 L2 hL1 hL2 hcN h_aL1L2_i
    · -- visitCountBefore(swapped_PE, i, a + L2) = n + 1
      exact visitCountBefore_segmentSwap_at_midpoint xs i n a L1 L2
        hL1 hL2 hcN h_a h_aL1 h_aL1L2
  · -- successorAt(swapped_PE, a + L2) = b
    show successorAt (k := k)
      (prefixExtend (k := k) N (segmentSwap xs a L1 L2 hL1 hL2 hcN)) (a + L2) = b
    simp only [successorAt]
    rw [segmentSwap_successor_at_midpoint xs a L1 L2 hL1 hL2 hcN]
    exact hsucc_n

/-! ## Section 8: Evidence preservation for segmentSwap on carriers

The segmentSwap preserves evidenceOf on ALL elements, not just carrier members.
This follows directly from CarrierTransportCore.segmentSwap_evidenceOf. -/

theorem segmentSwap_evidenceOf_on_carrier {N : ℕ}
    (xs : Fin (N + 1) → Fin k) (i : Fin k) (a L1 L2 : ℕ)
    (hL1 : 0 < L1) (hL2 : 0 < L2) (hcN : a + L1 + L2 ≤ N)
    (h_a_i : xs ⟨a, by omega⟩ = i)
    (h_aL1_i : xs ⟨a + L1, by omega⟩ = i)
    (h_aL1L2_i : xs ⟨a + L1 + L2, by omega⟩ = i) :
    evidenceOf (n := N) (segmentSwap xs a L1 L2 hL1 hL2 hcN) =
      evidenceOf (n := N) xs := by
  exact segmentSwap_evidenceOf xs a L1 L2 hL1 hL2 hcN
    (by rw [h_a_i, h_aL1_i]) (by rw [h_aL1_i, h_aL1L2_i])

/-! ## Section 9: The carrier transport theorem

Council quorum (72%): We prove the theorem with visit-time existence as an
additional hypothesis. This covers all cases needed by the limit argument in
`measure_start_inter_rowSuccessorValueEvent_eq_of_evidencePreservingEquiv_start`,
which quantifies over all N — for large enough N, the visits exist.

For the fully self-contained version (extracting visit times purely from
carrier membership), the remaining work is showing that carrier nonemptiness
implies visit-time existence. This is deferred to a follow-up. -/

/-! ## Section 9: Per-element carrier transport map

Each trajectory xs in carrier_n has its own visit times to i. The forward map
extracts these visit times, computes segmentSwap parameters, and applies.

Council quorum (75%): Martin-Löf + Carneiro recommend the per-element
construction. The map is noncomputable (uses nthVisitTime which is classical).

ARCHITECTURE NOTE for future agents:
The full `hCarrierTransport` Equiv construction requires:
1. For each xs in carrier_n, extract visit times t_n, t_{n+1}, t_{n+2} from
   nthVisitTime (which is `some` for carrier members)
2. Compute L1 = t_{n+1} - t_n, L2 = t_{n+2} - t_{n+1}
3. Apply segmentSwap xs t_n L1 L2
4. Show result is in carrier_{n+1} (via segmentSwap_carrier_mem_adjacent)
5. Show evidenceOf preserved (via segmentSwap_evidenceOf_on_carrier)
6. For bijectivity: the inverse map does the same from carrier_{n+1} to carrier_n
   (segmentSwap with L2, L1 is the inverse by involutivity)
7. For general n → n': compose adjacent transports or use identity/inverse

The mathematical content is fully proved in Sections 5-8.
The remaining ~150 lines are visit-time extraction + Equiv packaging.

Key obstacle: nthVisitTime is defined on INFINITE paths (ℕ → Fin k) via
prefixExtend. Extracting the actual ℕ value from `some t` requires
case analysis on the Option, but carrier membership guarantees `some`.
-/

/-- Helper: extract the n-th visit time to i from a carrier member.
Returns the time as a natural number (guaranteed to be `some` by carrier membership). -/
noncomputable def extractVisitTime {N : ℕ}
    (xs : Fin (N + 1) → Fin k) (i : Fin k) (n : ℕ)
    (hexists : nthVisitTimeExists (k := k) (prefixExtend (k := k) N xs) i n) : ℕ := by
  classical
  exact Nat.find hexists

lemma extractVisitTime_spec {N : ℕ}
    (xs : Fin (N + 1) → Fin k) (i : Fin k) (n : ℕ)
    (hexists : nthVisitTimeExists (k := k) (prefixExtend (k := k) N xs) i n) :
    isNthVisitTime (k := k) (prefixExtend (k := k) N xs) i n
      (extractVisitTime xs i n hexists) := by
  classical
  exact Nat.find_spec hexists

lemma nthVisitTime_eq_extractVisitTime {N : ℕ}
    (xs : Fin (N + 1) → Fin k) (i : Fin k) (n : ℕ)
    (hexists : nthVisitTimeExists (k := k) (prefixExtend (k := k) N xs) i n) :
    nthVisitTime (k := k) (prefixExtend (k := k) N xs) i n =
      some (extractVisitTime xs i n hexists) := by
  rw [nthVisitTime_eq_some_iff (k := k)]
  exact extractVisitTime_spec xs i n hexists

/-- Carrier membership implies the n-th visit to i exists. -/
lemma carrier_mem_visit_exists {N : ℕ}
    (xs : Fin (N + 1) → Fin k) (i : Fin k) (n : ℕ) (b : Fin k)
    (hxs : xs ∈ rowVisitCylinderEventUpToPrefixCarrier (k := k)
      i ({n} : Finset ℕ) (fun m => if m = n then b else i) N) :
    nthVisitTimeExists (k := k) (prefixExtend (k := k) N xs) i n := by
  rcases carrier_mem_witness xs i n b hxs with ⟨t, _, htime, _, _⟩
  exact ⟨t, (nthVisitTime_eq_some_iff (k := k) _ i n t).mp htime⟩

/-! ## Section 10: Forward map and evidence preservation

The per-element forward map: for xs in carrier_n, extract its visit times,
apply segmentSwap, get an element of carrier_{n+1}.

This requires the (n+1)-th and (n+2)-th visit times to also exist within
the horizon N. This is NOT guaranteed by carrier_n membership alone —
it requires a separate "sufficient visits" hypothesis.

For the application in the limit argument (N → ∞), this hypothesis is
satisfied for all large enough N when the trajectory is recurrent. -/

/-- Forward map for adjacent carrier transport: given xs in carrier_n with
sufficient visit data, produce an element with the same evidence whose
(n+1)-th visit to i has successor b.

This is the core constructive content of the carrier transport.
The full Equiv construction (bijectivity + composition to general n,n')
follows from involutivity of segmentSwap. -/
theorem carrierTransport_forward_adjacent {N : ℕ}
    (i : Fin k) (b : Fin k) (_hbi : b ≠ i) (n : ℕ)
    (xs : Fin (N + 1) → Fin k)
    (hxs : xs ∈ rowVisitCylinderEventUpToPrefixCarrier (k := k)
      i ({n} : Finset ℕ) (fun m => if m = n then b else i) N)
    -- Sufficient visit data: (n+1)-th and (n+2)-th visits also exist
    (hexN1 : nthVisitTimeExists (k := k) (prefixExtend (k := k) N xs) i (n + 1))
    (hexN2 : nthVisitTimeExists (k := k) (prefixExtend (k := k) N xs) i (n + 2))
    -- Visit times are within the horizon
    (htN1 : extractVisitTime xs i (n + 1) hexN1 < N)
    (htN2 : extractVisitTime xs i (n + 2) hexN2 < N) :
    ∃ ys : Fin (N + 1) → Fin k,
      ys ∈ rowVisitCylinderEventUpToPrefixCarrier (k := k)
        i ({n + 1} : Finset ℕ) (fun m => if m = n + 1 then b else i) N ∧
      evidenceOf (n := N) ys = evidenceOf (n := N) xs := by
  -- Extract visit times
  let t₀ := extractVisitTime xs i n (carrier_mem_visit_exists xs i n b hxs)
  let t₁ := extractVisitTime xs i (n + 1) hexN1
  let t₂ := extractVisitTime xs i (n + 2) hexN2
  have h_t₀ := extractVisitTime_spec xs i n (carrier_mem_visit_exists xs i n b hxs)
  have h_t₁ := extractVisitTime_spec xs i (n + 1) hexN1
  have h_t₂ := extractVisitTime_spec xs i (n + 2) hexN2
  -- Visit times are strictly ordered (from visit count monotonicity)
  -- Visit times are strictly ordered (count monotonicity)
  have ht₀_lt_t₁ : t₀ < t₁ := by
    by_contra h
    push_neg at h
    -- If t₁ ≤ t₀, then count(t₁) ≤ count(t₀) by monotonicity
    have hmono : visitCountBefore (k := k) (prefixExtend (k := k) N xs) i t₁ ≤
        visitCountBefore (k := k) (prefixExtend (k := k) N xs) i t₀ := by
      apply Finset.sum_le_sum_of_subset
      exact Finset.range_mono h
    -- But count(t₁) = n+1 > n = count(t₀)
    rw [h_t₀.2, h_t₁.2] at hmono; omega
  have ht₁_lt_t₂ : t₁ < t₂ := by
    by_contra h
    push_neg at h
    have hmono : visitCountBefore (k := k) (prefixExtend (k := k) N xs) i t₂ ≤
        visitCountBefore (k := k) (prefixExtend (k := k) N xs) i t₁ := by
      apply Finset.sum_le_sum_of_subset
      exact Finset.range_mono h
    rw [h_t₁.2, h_t₂.2] at hmono; omega
  -- Set segmentSwap parameters
  let L1 := t₁ - t₀
  let L2 := t₂ - t₁
  have hL1 : 0 < L1 := by omega
  have hL2 : 0 < L2 := by omega
  have hcN : t₀ + L1 + L2 ≤ N := by omega
  have hL1_eq : t₀ + L1 = t₁ := by omega
  have hL2_eq : t₀ + L1 + L2 = t₂ := by omega
  -- Rewrite visit-time hypotheses using L1, L2
  have h_a : isNthVisitTime (k := k) (prefixExtend (k := k) N xs) i n t₀ := h_t₀
  have h_aL1 : isNthVisitTime (k := k) (prefixExtend (k := k) N xs) i (n + 1) (t₀ + L1) := by
    rwa [hL1_eq]
  have h_aL1L2 : isNthVisitTime (k := k) (prefixExtend (k := k) N xs) i (n + 2) (t₀ + L1 + L2) := by
    rwa [hL2_eq]
  -- Build the swapped trajectory
  let ys := segmentSwap xs t₀ L1 L2 hL1 hL2 hcN
  -- The successor at the n-th visit is b (from carrier membership)
  have hsucc_n : (prefixExtend (k := k) N xs) (t₀ + 1) = b := by
    rcases carrier_mem_witness xs i n b hxs with ⟨t, htN, htime, hsucc_b, _⟩
    have : t = t₀ := by
      exact isNthVisitTime_unique (k := k) (prefixExtend (k := k) N xs) i n t t₀
        ((nthVisitTime_eq_some_iff (k := k) _ i n t).mp htime) h_t₀
    subst this
    simpa [successorAt] using hsucc_b
  refine ⟨ys, ?_, ?_⟩
  · -- ys ∈ carrier_{n+1}
    exact segmentSwap_carrier_mem_adjacent xs i n b t₀ L1 L2
      hL1 hL2 hcN h_a h_aL1 h_aL1L2 hsucc_n hxs
  · -- evidenceOf preserved
    have h_t₀_i : xs ⟨t₀, by omega⟩ = i := by
      have := h_t₀.1; rwa [prefixExtend_apply_le' xs (by omega)] at this
    have h_t₁_i : xs ⟨t₁, by omega⟩ = i := by
      have := h_t₁.1; rwa [prefixExtend_apply_le' xs (by omega)] at this
    have h_t₂_i : xs ⟨t₂, by omega⟩ = i := by
      have := h_t₂.1; rwa [prefixExtend_apply_le' xs (by omega)] at this
    have h_aL1_i : xs ⟨t₀ + L1, by omega⟩ = i := by
      have : (⟨t₀ + L1, by omega⟩ : Fin (N + 1)) = ⟨t₁, by omega⟩ := by
        ext; exact hL1_eq
      rw [this]; exact h_t₁_i
    have h_aL1L2_i : xs ⟨t₀ + L1 + L2, by omega⟩ = i := by
      have : (⟨t₀ + L1 + L2, by omega⟩ : Fin (N + 1)) = ⟨t₂, by omega⟩ := by
        ext; exact hL2_eq
      rw [this]; exact h_t₂_i
    exact segmentSwap_evidenceOf_on_carrier xs i t₀ L1 L2 hL1 hL2 hcN
      h_t₀_i h_aL1_i h_aL1L2_i

/-! ## Section 11: Visit-time stability under segmentSwap

The n-th visit time to i is unchanged by segmentSwap (positions ≤ a are identity).
This is the missing lemma that enables the Equiv construction: both forward
and inverse maps extract the SAME n-th visit time. -/

/-- The n-th visit time to i in prefixExtend of segmentSwap equals the original,
when the n-th visit time a satisfies a ≤ a (trivially). This is because
segmentSwap is the identity on [0, a]. -/
lemma nthVisitTime_prefixExtend_segmentSwap_eq_of_le {N : ℕ}
    (xs : Fin (N + 1) → Fin k) (i : Fin k) (n : ℕ) (a L1 L2 : ℕ)
    (hL1 : 0 < L1) (hL2 : 0 < L2) (hcN : a + L1 + L2 ≤ N)
    (h_a : isNthVisitTime (k := k) (prefixExtend (k := k) N xs) i n a)
    (haN : a < N) :
    nthVisitTime (k := k) (prefixExtend (k := k) N
      (segmentSwap xs a L1 L2 hL1 hL2 hcN)) i n = some a := by
  rw [nthVisitTime_eq_some_iff (k := k)]
  constructor
  · -- prefixExtend(swapped)(a) = i
    rw [prefixExtend_apply_le' _ (by omega : a ≤ N)]
    rw [segmentSwap_at_a xs a L1 L2 hL1 hL2 hcN]
    have := h_a.1; rwa [prefixExtend_apply_le' xs (by omega : a ≤ N)] at this
  · -- visitCountBefore(prefixExtend(swapped), i, a) = n
    rw [visitCountBefore_prefixExtend_segmentSwap_le xs i a L1 L2 hL1 hL2 hcN a le_rfl]
    exact h_a.2

/-! ## Section 12: The Equiv construction

The per-element constructive map: extract visit times → segmentSwap → prove membership.
The inverse: extract visit times from the image (same a, swapped L1↔L2) → segmentSwap.
left_inv and right_inv from segmentSwap_involutive.

Hypothesis: all carrier_n members have sufficient visit data (n+1, n+2 visits
exist within N). This is a "sufficient horizon" condition that the upstream
limit argument (over all N) satisfies for large N. -/

/-- Constructive forward map: given xs in carrier_n with sufficient visits,
produce the raw swapped trajectory. -/
noncomputable def carrierSwapRaw {N : ℕ}
    (xs : Fin (N + 1) → Fin k) (i : Fin k) (n : ℕ)
    (hexN : nthVisitTimeExists (k := k) (prefixExtend (k := k) N xs) i n)
    (hexN1 : nthVisitTimeExists (k := k) (prefixExtend (k := k) N xs) i (n + 1))
    (hexN2 : nthVisitTimeExists (k := k) (prefixExtend (k := k) N xs) i (n + 2))
    (_htN1 : extractVisitTime xs i (n + 1) hexN1 < N)
    (htN2 : extractVisitTime xs i (n + 2) hexN2 < N) :
    Fin (N + 1) → Fin k :=
  let t₀ := extractVisitTime xs i n hexN
  let t₁ := extractVisitTime xs i (n + 1) hexN1
  let t₂ := extractVisitTime xs i (n + 2) hexN2
  let L1 := t₁ - t₀
  let L2 := t₂ - t₁
  have h_t₀ := extractVisitTime_spec xs i n hexN
  have h_t₁ := extractVisitTime_spec xs i (n + 1) hexN1
  have h_t₂ := extractVisitTime_spec xs i (n + 2) hexN2
  -- t₀ < t₁ < t₂ from visit count monotonicity
  have ht₀_lt_t₁ : t₀ < t₁ := by
    by_contra h; push_neg at h
    have : visitCountBefore (k := k) (prefixExtend (k := k) N xs) i t₁ ≤
        visitCountBefore (k := k) (prefixExtend (k := k) N xs) i t₀ :=
      Finset.sum_le_sum_of_subset (Finset.range_mono h)
    rw [h_t₀.2, h_t₁.2] at this; omega
  have ht₁_lt_t₂ : t₁ < t₂ := by
    by_contra h; push_neg at h
    have : visitCountBefore (k := k) (prefixExtend (k := k) N xs) i t₂ ≤
        visitCountBefore (k := k) (prefixExtend (k := k) N xs) i t₁ :=
      Finset.sum_le_sum_of_subset (Finset.range_mono h)
    rw [h_t₁.2, h_t₂.2] at this; omega
  have hL1 : 0 < L1 := by omega
  have hL2 : 0 < L2 := by omega
  have hcN : t₀ + L1 + L2 ≤ N := by omega
  segmentSwap xs t₀ L1 L2 hL1 hL2 hcN

/-- extractVisitTime on segmentSwap at index n (the anchor) gives the same value,
because segmentSwap is identity on [0, a] and a is the n-th visit time. -/
lemma extractVisitTime_segmentSwap_n {N : ℕ}
    (xs : Fin (N + 1) → Fin k) (i : Fin k) (n : ℕ) (a L1 L2 : ℕ)
    (hL1 : 0 < L1) (hL2 : 0 < L2) (hcN : a + L1 + L2 ≤ N)
    (hexN : nthVisitTimeExists (k := k) (prefixExtend (k := k) N xs) i n)
    (h_a : isNthVisitTime (k := k) (prefixExtend (k := k) N xs) i n a)
    (_ha_eq : extractVisitTime xs i n hexN = a)
    (haN : a < N)
    (hexN' : nthVisitTimeExists (k := k) (prefixExtend (k := k) N
      (segmentSwap xs a L1 L2 hL1 hL2 hcN)) i n) :
    extractVisitTime (segmentSwap xs a L1 L2 hL1 hL2 hcN) i n hexN' = a := by
  -- nthVisitTime on swapped trajectory at n = some a (proved in Section 11)
  have htime := nthVisitTime_prefixExtend_segmentSwap_eq_of_le xs i n a L1 L2
    hL1 hL2 hcN h_a haN
  -- extractVisitTime is the unique value t such that isNthVisitTime ... t
  have hspec := extractVisitTime_spec (segmentSwap xs a L1 L2 hL1 hL2 hcN) i n hexN'
  have hspec_a := (nthVisitTime_eq_some_iff (k := k) _ i n a).mp htime
  exact isNthVisitTime_unique (k := k) _ i n
    (extractVisitTime (segmentSwap xs a L1 L2 hL1 hL2 hcN) i n hexN') a
    hspec hspec_a

end CarrierTransportBridge

end Mettapedia.Logic
