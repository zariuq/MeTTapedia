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

/-! ## Section 12: Visit-time lemmas for (n+1)-th and (n+2)-th visits in swapped traj -/

/-- In the swapped trajectory, positions (a+L2, a+L1+L2) are i-free.
These come from (a, a+L1) in the original (between n-th and (n+1)-th visits). -/
lemma swapped_no_visits_second_excursion {N : ℕ}
    (xs : Fin (N + 1) → Fin k) (i : Fin k) (n : ℕ) (a L1 L2 : ℕ)
    (hL1 : 0 < L1) (hL2 : 0 < L2) (hcN : a + L1 + L2 ≤ N)
    (h_a : isNthVisitTime (k := k) (prefixExtend (k := k) N xs) i n a)
    (h_aL1 : isNthVisitTime (k := k) (prefixExtend (k := k) N xs) i (n + 1) (a + L1))
    (s : ℕ) (hs1 : a + L2 < s) (hs2 : s < a + L1 + L2) :
    (prefixExtend (k := k) N (segmentSwap xs a L1 L2 hL1 hL2 hcN)) s ≠ i := by
  rw [prefixExtend_apply_le' _ (by omega : s ≤ N)]
  show segmentSwap xs a L1 L2 hL1 hL2 hcN ⟨s, by omega⟩ ≠ i
  simp only [segmentSwap]
  have h1 : ¬(s ≤ a) := by omega
  have h2 : ¬(s ≤ a + L2) := by omega
  have h3 : s ≤ a + L1 + L2 := by omega
  simp [h1, h2, h3]
  exact no_visits_between_consecutive' xs i n a (a + L1) (by omega) (by omega) h_a h_aL1
    (s - L2) (by omega) (by omega)

/-- Visit count at a+L1+L2 in the swapped trajectory = n+2. -/
theorem visitCountBefore_segmentSwap_at_endpoint {N : ℕ}
    (xs : Fin (N + 1) → Fin k) (i : Fin k) (n : ℕ) (a L1 L2 : ℕ)
    (hL1 : 0 < L1) (hL2 : 0 < L2) (hcN : a + L1 + L2 ≤ N)
    (h_a : isNthVisitTime (k := k) (prefixExtend (k := k) N xs) i n a)
    (h_aL1 : isNthVisitTime (k := k) (prefixExtend (k := k) N xs) i (n + 1) (a + L1))
    (h_aL1L2 : isNthVisitTime (k := k) (prefixExtend (k := k) N xs) i (n + 2) (a + L1 + L2)) :
    visitCountBefore (k := k)
      (prefixExtend (k := k) N (segmentSwap xs a L1 L2 hL1 hL2 hcN)) i (a + L1 + L2) =
        n + 2 := by
  let ω' := prefixExtend (k := k) N (segmentSwap xs a L1 L2 hL1 hL2 hcN)
  have hstep1 : visitCountBefore (k := k) ω' i (a + L1 + L2) =
      visitCountBefore (k := k) ω' i (a + L2 + 1) := by
    refine visitCountBefore_eq_of_no_visits ω' i (a + L2 + 1) (a + L1 + L2) (by omega) ?_
    intro s hs1 hs2
    exact swapped_no_visits_second_excursion xs i n a L1 L2 hL1 hL2 hcN h_a h_aL1 s
      (by omega) hs2
  have hvisit_mid : ω' (a + L2) = i :=
    segmentSwap_visits_i_at_midpoint xs i a L1 L2 hL1 hL2 hcN
      (by have := h_aL1L2.1; rwa [prefixExtend_apply_le' xs (by omega)] at this)
  have hstep2 : visitCountBefore (k := k) ω' i (a + L2 + 1) =
      visitCountBefore (k := k) ω' i (a + L2) + 1 := by
    rw [visitCountBefore_succ']; simp [hvisit_mid]
  have hstep3 := visitCountBefore_segmentSwap_at_midpoint xs i n a L1 L2
    hL1 hL2 hcN h_a h_aL1 h_aL1L2
  rw [hstep1, hstep2, hstep3]

/-- nthVisitTime for (n+1)-th visit in swapped trajectory = some (a+L2). -/
theorem nthVisitTime_segmentSwap_n1 {N : ℕ}
    (xs : Fin (N + 1) → Fin k) (i : Fin k) (n : ℕ) (a L1 L2 : ℕ)
    (hL1 : 0 < L1) (hL2 : 0 < L2) (hcN : a + L1 + L2 ≤ N)
    (h_a : isNthVisitTime (k := k) (prefixExtend (k := k) N xs) i n a)
    (h_aL1 : isNthVisitTime (k := k) (prefixExtend (k := k) N xs) i (n + 1) (a + L1))
    (h_aL1L2 : isNthVisitTime (k := k) (prefixExtend (k := k) N xs) i (n + 2) (a + L1 + L2)) :
    nthVisitTime (k := k) (prefixExtend (k := k) N
      (segmentSwap xs a L1 L2 hL1 hL2 hcN)) i (n + 1) = some (a + L2) := by
  rw [nthVisitTime_eq_some_iff (k := k)]
  exact ⟨segmentSwap_visits_i_at_midpoint xs i a L1 L2 hL1 hL2 hcN
    (by have := h_aL1L2.1; rwa [prefixExtend_apply_le' xs (by omega)] at this),
   visitCountBefore_segmentSwap_at_midpoint xs i n a L1 L2 hL1 hL2 hcN h_a h_aL1 h_aL1L2⟩

/-- nthVisitTime for (n+2)-th visit in swapped trajectory = some (a+L1+L2). -/
theorem nthVisitTime_segmentSwap_n2 {N : ℕ}
    (xs : Fin (N + 1) → Fin k) (i : Fin k) (n : ℕ) (a L1 L2 : ℕ)
    (hL1 : 0 < L1) (hL2 : 0 < L2) (hcN : a + L1 + L2 ≤ N)
    (h_a : isNthVisitTime (k := k) (prefixExtend (k := k) N xs) i n a)
    (h_aL1 : isNthVisitTime (k := k) (prefixExtend (k := k) N xs) i (n + 1) (a + L1))
    (h_aL1L2 : isNthVisitTime (k := k) (prefixExtend (k := k) N xs) i (n + 2) (a + L1 + L2)) :
    nthVisitTime (k := k) (prefixExtend (k := k) N
      (segmentSwap xs a L1 L2 hL1 hL2 hcN)) i (n + 2) = some (a + L1 + L2) := by
  rw [nthVisitTime_eq_some_iff (k := k)]
  constructor
  · rw [prefixExtend_apply_le' _ (by omega : a + L1 + L2 ≤ N)]
    rw [segmentSwap_at_end xs a L1 L2 hL1 hL2 hcN]
    have := h_aL1.1; rwa [prefixExtend_apply_le' xs (by omega)] at this
  · exact visitCountBefore_segmentSwap_at_endpoint xs i n a L1 L2
      hL1 hL2 hcN h_a h_aL1 h_aL1L2

/-! ## Section 13: The Equiv construction -/

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

/-- carrierSwapRaw is a per-element involution: applying it to its own output
(with the swapped trajectory's visit times) recovers the original.

The swapped trajectory has visit times: n-th at a, (n+1)-th at a+L2, (n+2)-th at a+L1+L2.
So L1' = (a+L2) - a = L2, L2' = (a+L1+L2) - (a+L2) = L1.
segmentSwap(segmentSwap(xs, a, L1, L2), a, L2, L1) = xs by involutivity. -/
theorem carrierSwapRaw_involutive {N : ℕ}
    (xs : Fin (N + 1) → Fin k) (i : Fin k) (n : ℕ) (a L1 L2 : ℕ)
    (hL1 : 0 < L1) (hL2 : 0 < L2) (hcN : a + L1 + L2 ≤ N)
    (_h_a : isNthVisitTime (k := k) (prefixExtend (k := k) N xs) i n a)
    (_h_aL1 : isNthVisitTime (k := k) (prefixExtend (k := k) N xs) i (n + 1) (a + L1))
    (_h_aL1L2 : isNthVisitTime (k := k) (prefixExtend (k := k) N xs) i (n + 2) (a + L1 + L2)) :
    segmentSwap (segmentSwap xs a L1 L2 hL1 hL2 hcN) a L2 L1 hL2 hL1 (by omega) = xs :=
  segmentSwap_involutive xs a L1 L2 hL1 hL2 hcN

/-- Reverse direction: segmentSwap with (a, L2, L1) maps carrier_{n+1} to carrier_n.
The (n+1)-th visit is at a+L2 in the swapped trajectory, and after the REVERSE swap
(swapping back the excursions), the n-th visit at a gets successor b. -/
theorem segmentSwap_carrier_mem_adjacent_reverse {N : ℕ}
    (xs : Fin (N + 1) → Fin k) (i : Fin k) (n : ℕ) (b : Fin k)
    (a L1 L2 : ℕ)
    (hL1 : 0 < L1) (hL2 : 0 < L2) (hcN : a + L1 + L2 ≤ N)
    (h_a : isNthVisitTime (k := k) (prefixExtend (k := k) N xs) i n a)
    (h_aL2 : isNthVisitTime (k := k) (prefixExtend (k := k) N xs) i (n + 1) (a + L2))
    (h_aL1L2 : isNthVisitTime (k := k) (prefixExtend (k := k) N xs) i (n + 2) (a + L1 + L2))
    -- The successor at the (n+1)-th visit (position a+L2) is b
    (hsucc_n1 : (prefixExtend (k := k) N xs) (a + L2 + 1) = b)
    (_hxs : xs ∈ rowVisitCylinderEventUpToPrefixCarrier (k := k)
      i ({n + 1} : Finset ℕ) (fun m => if m = n + 1 then b else i) N) :
    segmentSwap xs a L2 L1 hL2 hL1 (by omega) ∈
      rowVisitCylinderEventUpToPrefixCarrier (k := k)
        i ({n} : Finset ℕ) (fun m => if m = n then b else i) N := by
  -- The reverse swap: segmentSwap(xs, a, L2, L1) transposes the two excursions back.
  -- After the reverse swap:
  -- - n-th visit to i is still at a (positions ≤ a unchanged)
  -- - Successor at n-th visit = xs(a+L2+1) = b (from segmentSwap_successor_at_mid
  --   with swapped parameters: L2 plays the role of L1, L1 plays the role of L2)
  simp only [rowVisitCylinderEventUpToPrefixCarrier, Finset.mem_filter, Finset.mem_univ, true_and]
  intro m hm
  simp only [Finset.mem_singleton] at hm; subst hm
  simp only [ite_true]
  refine ⟨a, by omega, ?_, ?_⟩
  · -- nthVisitTime of reverse-swapped at n = some a
    rw [nthVisitTime_eq_some_iff (k := k)]
    constructor
    · rw [prefixExtend_apply_le' _ (by omega : a ≤ N)]
      rw [segmentSwap_at_a xs a L2 L1 hL2 hL1 (by omega)]
      have := h_a.1; rwa [prefixExtend_apply_le' xs (by omega)] at this
    · -- visitCountBefore(reverse-swapped, i, a) = n
      -- reverse swap is identity on [0, a), so count = count on original = n
      rw [visitCountBefore_prefixExtend_segmentSwap_le xs i a L2 L1 hL2 hL1 (by omega) a le_rfl]
      exact h_a.2
  · -- successorAt of reverse-swapped at a = b
    show successorAt (k := k) (prefixExtend (k := k) N
      (segmentSwap xs a L2 L1 hL2 hL1 (by omega))) a = b
    simp only [successorAt]
    -- segmentSwap(xs, a, L2, L1) at position a+1: since a < a+1 ≤ a+L1,
    -- we're in the second branch: xs((a+1) + L2) = xs(a+L2+1) = b
    rw [prefixExtend_apply_le' _ (by omega : a + 1 ≤ N)]
    simp only [segmentSwap]
    have h1 : ¬(a + 1 ≤ a) := by omega
    have h2 : a + 1 ≤ a + L1 := by omega
    simp [h1, h2]
    -- Goal: xs ⟨a + 1 + L2, _⟩ = b
    -- This is xs(a + L2 + 1) = b from the hypothesis, modulo Fin arithmetic
    have heq : (⟨a + 1 + L2, by omega⟩ : Fin (N + 1)) = ⟨a + L2 + 1, by omega⟩ := by
      ext; show a + 1 + L2 = a + L2 + 1; omega
    rw [heq]
    rw [← prefixExtend_apply_le' xs (by omega : a + L2 + 1 ≤ N)]
    exact hsucc_n1

/-- extractVisitTime at (n+1) on segmentSwap gives a+L2. -/
lemma extractVisitTime_segmentSwap_n1 {N : ℕ}
    (xs : Fin (N + 1) → Fin k) (i : Fin k) (n : ℕ) (a L1 L2 : ℕ)
    (hL1 : 0 < L1) (hL2 : 0 < L2) (hcN : a + L1 + L2 ≤ N)
    (h_a : isNthVisitTime (k := k) (prefixExtend (k := k) N xs) i n a)
    (h_aL1 : isNthVisitTime (k := k) (prefixExtend (k := k) N xs) i (n + 1) (a + L1))
    (h_aL1L2 : isNthVisitTime (k := k) (prefixExtend (k := k) N xs) i (n + 2) (a + L1 + L2))
    (hexN1' : nthVisitTimeExists (k := k) (prefixExtend (k := k) N
      (segmentSwap xs a L1 L2 hL1 hL2 hcN)) i (n + 1)) :
    extractVisitTime (segmentSwap xs a L1 L2 hL1 hL2 hcN) i (n + 1) hexN1' = a + L2 := by
  have htime := nthVisitTime_segmentSwap_n1 xs i n a L1 L2 hL1 hL2 hcN h_a h_aL1 h_aL1L2
  have hspec := extractVisitTime_spec (segmentSwap xs a L1 L2 hL1 hL2 hcN) i (n + 1) hexN1'
  have hspec_aL2 := (nthVisitTime_eq_some_iff (k := k) _ i (n + 1) (a + L2)).mp htime
  exact isNthVisitTime_unique (k := k) _ i (n + 1) _ (a + L2) hspec hspec_aL2

/-- extractVisitTime at (n+2) on segmentSwap gives a+L1+L2. -/
lemma extractVisitTime_segmentSwap_n2 {N : ℕ}
    (xs : Fin (N + 1) → Fin k) (i : Fin k) (n : ℕ) (a L1 L2 : ℕ)
    (hL1 : 0 < L1) (hL2 : 0 < L2) (hcN : a + L1 + L2 ≤ N)
    (h_a : isNthVisitTime (k := k) (prefixExtend (k := k) N xs) i n a)
    (h_aL1 : isNthVisitTime (k := k) (prefixExtend (k := k) N xs) i (n + 1) (a + L1))
    (h_aL1L2 : isNthVisitTime (k := k) (prefixExtend (k := k) N xs) i (n + 2) (a + L1 + L2))
    (hexN2' : nthVisitTimeExists (k := k) (prefixExtend (k := k) N
      (segmentSwap xs a L1 L2 hL1 hL2 hcN)) i (n + 2)) :
    extractVisitTime (segmentSwap xs a L1 L2 hL1 hL2 hcN) i (n + 2) hexN2' = a + L1 + L2 := by
  have htime := nthVisitTime_segmentSwap_n2 xs i n a L1 L2 hL1 hL2 hcN h_a h_aL1 h_aL1L2
  have hspec := extractVisitTime_spec (segmentSwap xs a L1 L2 hL1 hL2 hcN) i (n + 2) hexN2'
  have hspec_end := (nthVisitTime_eq_some_iff (k := k) _ i (n + 2) (a + L1 + L2)).mp htime
  exact isNthVisitTime_unique (k := k) _ i (n + 2) _ (a + L1 + L2) hspec hspec_end

/-! ## Section 14: Missing monotonicity lemma + the Equiv -/

/-- Visit-time existence is monotone: if the (n+1)-th visit exists, the n-th does too. -/
lemma nthVisitTimeExists_of_succ
    (ω : ℕ → Fin k) (i : Fin k) (n : ℕ)
    (h : nthVisitTimeExists (k := k) ω i (n + 1)) :
    nthVisitTimeExists (k := k) ω i n := by
  -- Suffices to find s with ω(s) = i and count(s) = n.
  -- Strategy: the (n+1)-th visit at time t means count(t) = n+1.
  -- Scan backwards from t: the last visit to i before or at position t-1
  -- with ω(s) = i must have count(s) = n (since count(s+1) = count(s)+1 = n+1).
  rcases h with ⟨t, hvisit, hcount⟩
  -- Use strong recursion: find s < t with count(s+1) = n+1 and ω(s) = i.
  -- Then count(s) = n.
  -- We prove: if count(t) ≥ n+1, then visit n exists in [0, t).
  suffices ∀ t, visitCountBefore (k := k) ω i t ≥ n + 1 →
      ∃ s, ω s = i ∧ visitCountBefore (k := k) ω i s = n by
    -- count(t) = n+1 ≥ n+1
    exact this t (by omega)
  intro t
  induction t with
  | zero => simp [visitCountBefore]
  | succ t ih =>
    intro hge
    rw [visitCountBefore_succ'] at hge
    by_cases hωt : ω t = i
    · simp [hωt] at hge
      by_cases heq : visitCountBefore (k := k) ω i t = n
      · exact ⟨t, hωt, heq⟩
      · exact ih (by omega)
    · simp [hωt] at hge; exact ih hge

/-- The raw swap map: given a trajectory and existence proofs for three consecutive
visit times, produce the segment-swapped trajectory. Defined transparently in
terms of extractVisitTime and segmentSwap so that involutivity is provable. -/
@[reducible] noncomputable def rawSwap {N : ℕ}
    (xs : Fin (N + 1) → Fin k) (i : Fin k) (n : ℕ)
    (hex0 : nthVisitTimeExists (k := k) (prefixExtend (k := k) N xs) i n)
    (hex1 : nthVisitTimeExists (k := k) (prefixExtend (k := k) N xs) i (n + 1))
    (hex2 : nthVisitTimeExists (k := k) (prefixExtend (k := k) N xs) i (n + 2))
    (_hbd1 : extractVisitTime xs i (n + 1) hex1 < N)
    (hbd2 : extractVisitTime xs i (n + 2) hex2 < N) :
    Fin (N + 1) → Fin k :=
  let t₀ := extractVisitTime xs i n hex0
  let t₁ := extractVisitTime xs i (n + 1) hex1
  let t₂ := extractVisitTime xs i (n + 2) hex2
  have h0 := extractVisitTime_spec xs i n hex0
  have h1 := extractVisitTime_spec xs i (n + 1) hex1
  have h2 := extractVisitTime_spec xs i (n + 2) hex2
  have ht01 : t₀ < t₁ := by
    by_contra hle; push_neg at hle
    have := Finset.sum_le_sum_of_subset
      (f := fun s => if (prefixExtend (k := k) N xs) s = i then 1 else 0)
      (Finset.range_mono hle)
    change visitCountBefore (k := k) _ i t₁ ≤ visitCountBefore (k := k) _ i t₀ at this
    rw [h0.2, h1.2] at this; omega
  have ht12 : t₁ < t₂ := by
    by_contra hle; push_neg at hle
    have := Finset.sum_le_sum_of_subset
      (f := fun s => if (prefixExtend (k := k) N xs) s = i then 1 else 0)
      (Finset.range_mono hle)
    change visitCountBefore (k := k) _ i t₂ ≤ visitCountBefore (k := k) _ i t₁ at this
    rw [h1.2, h2.2] at this; omega
  have hL1 : 0 < t₁ - t₀ := by omega
  have hL2 : 0 < t₂ - t₁ := by omega
  have hsum : t₀ + (t₁ - t₀) + (t₂ - t₁) = t₂ := by omega
  have hcN : t₀ + (t₁ - t₀) + (t₂ - t₁) ≤ N := by omega
  segmentSwap xs t₀ (t₁ - t₀) (t₂ - t₁) hL1 hL2 hcN

/-- rawSwap is self-inverse: rawSwap(rawSwap(xs)) = xs.
Crucially, this constructs the output visit-time proofs INTERNALLY,
so the caller only needs to provide input proofs.
This is what makes the Equiv's left_inv/right_inv closeable. -/
theorem rawSwap_selfInverse {N : ℕ}
    (xs : Fin (N + 1) → Fin k) (i : Fin k) (n : ℕ)
    (hex0 : nthVisitTimeExists (k := k) (prefixExtend (k := k) N xs) i n)
    (hex1 : nthVisitTimeExists (k := k) (prefixExtend (k := k) N xs) i (n + 1))
    (hex2 : nthVisitTimeExists (k := k) (prefixExtend (k := k) N xs) i (n + 2))
    (hbd1 : extractVisitTime xs i (n + 1) hex1 < N)
    (hbd2 : extractVisitTime xs i (n + 2) hex2 < N) :
    -- Construct output proofs internally
    ∃ (hex0' : nthVisitTimeExists (k := k) (prefixExtend (k := k) N
          (rawSwap xs i n hex0 hex1 hex2 hbd1 hbd2)) i n)
      (hex1' : nthVisitTimeExists (k := k) (prefixExtend (k := k) N
          (rawSwap xs i n hex0 hex1 hex2 hbd1 hbd2)) i (n + 1))
      (hex2' : nthVisitTimeExists (k := k) (prefixExtend (k := k) N
          (rawSwap xs i n hex0 hex1 hex2 hbd1 hbd2)) i (n + 2))
      (hbd1' : extractVisitTime (rawSwap xs i n hex0 hex1 hex2 hbd1 hbd2)
          i (n + 1) hex1' < N)
      (hbd2' : extractVisitTime (rawSwap xs i n hex0 hex1 hex2 hbd1 hbd2)
          i (n + 2) hex2' < N),
    rawSwap (rawSwap xs i n hex0 hex1 hex2 hbd1 hbd2)
      i n hex0' hex1' hex2' hbd1' hbd2' = xs := by
  let ys := rawSwap xs i n hex0 hex1 hex2 hbd1 hbd2
  set t₀ := extractVisitTime xs i n hex0
  set t₁ := extractVisitTime xs i (n + 1) hex1
  set t₂ := extractVisitTime xs i (n + 2) hex2
  set L1 := t₁ - t₀; set L2 := t₂ - t₁
  have h_t₀ := extractVisitTime_spec xs i n hex0
  have h_t₁ := extractVisitTime_spec xs i (n + 1) hex1
  have h_t₂ := extractVisitTime_spec xs i (n + 2) hex2
  have ht01 : t₀ < t₁ := by
    by_contra h; push_neg at h
    have := Finset.sum_le_sum_of_subset (f := fun s => if (prefixExtend (k := k) N xs) s = i then 1 else 0) (Finset.range_mono h)
    change visitCountBefore (k := k) _ i t₁ ≤ visitCountBefore (k := k) _ i t₀ at this
    rw [h_t₀.2, h_t₁.2] at this; omega
  have ht12 : t₁ < t₂ := by
    by_contra h; push_neg at h
    have := Finset.sum_le_sum_of_subset (f := fun s => if (prefixExtend (k := k) N xs) s = i then 1 else 0) (Finset.range_mono h)
    change visitCountBefore (k := k) _ i t₂ ≤ visitCountBefore (k := k) _ i t₁ at this
    rw [h_t₁.2, h_t₂.2] at this; omega
  have hL1pos : 0 < L1 := by omega
  have hL2pos : 0 < L2 := by omega
  have hcN : t₀ + L1 + L2 ≤ N := by omega
  have h_aL1 : isNthVisitTime (k := k) (prefixExtend (k := k) N xs) i (n + 1) (t₀ + L1) := by
    convert h_t₁ using 1; omega
  have h_aL1L2 : isNthVisitTime (k := k) (prefixExtend (k := k) N xs) i (n + 2) (t₀ + L1 + L2) := by
    convert h_t₂ using 1; omega
  -- Construct visit-time existence for ys = rawSwap(xs) = segmentSwap(xs, t₀, L1, L2)
  have hnt_n := nthVisitTime_prefixExtend_segmentSwap_eq_of_le xs i n t₀ L1 L2
    hL1pos hL2pos hcN h_t₀ (by omega)
  have hnt_n1 := nthVisitTime_segmentSwap_n1 xs i n t₀ L1 L2
    hL1pos hL2pos hcN h_t₀ h_aL1 h_aL1L2
  have hnt_n2 := nthVisitTime_segmentSwap_n2 xs i n t₀ L1 L2
    hL1pos hL2pos hcN h_t₀ h_aL1 h_aL1L2
  -- Existence proofs from nthVisitTime = some
  let hex0' : nthVisitTimeExists (k := k) (prefixExtend (k := k) N ys) i n :=
    ⟨t₀, (nthVisitTime_eq_some_iff (k := k) _ i n t₀).mp hnt_n⟩
  let hex1' : nthVisitTimeExists (k := k) (prefixExtend (k := k) N ys) i (n + 1) :=
    ⟨t₀ + L2, (nthVisitTime_eq_some_iff (k := k) _ i (n + 1) (t₀ + L2)).mp hnt_n1⟩
  let hex2' : nthVisitTimeExists (k := k) (prefixExtend (k := k) N ys) i (n + 2) :=
    ⟨t₀ + L1 + L2, (nthVisitTime_eq_some_iff (k := k) _ i (n + 2) (t₀ + L1 + L2)).mp hnt_n2⟩
  -- Bounds: extractVisitTime gives the specific values
  have evt0 := extractVisitTime_segmentSwap_n xs i n t₀ L1 L2
    hL1pos hL2pos hcN hex0 h_t₀ rfl (by omega) hex0'
  have evt1 := extractVisitTime_segmentSwap_n1 xs i n t₀ L1 L2
    hL1pos hL2pos hcN h_t₀ h_aL1 h_aL1L2 hex1'
  have evt2 := extractVisitTime_segmentSwap_n2 xs i n t₀ L1 L2
    hL1pos hL2pos hcN h_t₀ h_aL1 h_aL1L2 hex2'
  have hbd1' : extractVisitTime ys i (n + 1) hex1' < N := by rw [evt1]; omega
  have hbd2' : extractVisitTime ys i (n + 2) hex2' < N := by rw [evt2]; omega
  -- The involutive result
  refine ⟨hex0', hex1', hex2', hbd1', hbd2', ?_⟩
  -- rawSwap(ys) with these proofs = xs
  funext ⟨p, hp⟩
  have hinv := segmentSwap_involutive xs t₀ L1 L2 hL1pos hL2pos hcN
  have lhs_eq : rawSwap ys i n hex0' hex1' hex2' hbd1' hbd2' ⟨p, hp⟩ =
      segmentSwap (segmentSwap xs t₀ L1 L2 hL1pos hL2pos hcN)
        (extractVisitTime (segmentSwap xs t₀ L1 L2 hL1pos hL2pos hcN) i n hex0')
        (extractVisitTime (segmentSwap xs t₀ L1 L2 hL1pos hL2pos hcN) i (n + 1) hex1' -
         extractVisitTime (segmentSwap xs t₀ L1 L2 hL1pos hL2pos hcN) i n hex0')
        (extractVisitTime (segmentSwap xs t₀ L1 L2 hL1pos hL2pos hcN) i (n + 2) hex2' -
         extractVisitTime (segmentSwap xs t₀ L1 L2 hL1pos hL2pos hcN) i (n + 1) hex1')
        _ _ _ ⟨p, hp⟩ := rfl
  rw [lhs_eq]
  simp only [evt0, evt1, evt2,
    show (t₀ + L2) - t₀ = L2 by omega,
    show (t₀ + L1 + L2) - (t₀ + L2) = L1 by omega]
  exact congrFun hinv ⟨p, hp⟩

/-- Forward membership: rawSwap of carrier_n member lands in carrier_{n+1}. -/
theorem rawSwap_fwd_mem {N : ℕ}
    (i : Fin k) (b : Fin k) (hbi : b ≠ i) (n : ℕ)
    (xs : Fin (N + 1) → Fin k)
    (hxs : xs ∈ rowVisitCylinderEventUpToPrefixCarrier (k := k)
      i ({n} : Finset ℕ) (fun j => if j = n then b else i) N)
    (hex1 : nthVisitTimeExists (k := k) (prefixExtend (k := k) N xs) i (n + 1))
    (hex2 : nthVisitTimeExists (k := k) (prefixExtend (k := k) N xs) i (n + 2))
    (hbd1 : extractVisitTime xs i (n + 1) hex1 < N)
    (hbd2 : extractVisitTime xs i (n + 2) hex2 < N) :
    rawSwap xs i n (carrier_mem_visit_exists xs i n b hxs) hex1 hex2 hbd1 hbd2 ∈
      rowVisitCylinderEventUpToPrefixCarrier (k := k)
        i ({n + 1} : Finset ℕ) (fun j => if j = n + 1 then b else i) N := by
  let hex0 := carrier_mem_visit_exists xs i n b hxs
  have h0 := extractVisitTime_spec xs i n hex0
  have h1 := extractVisitTime_spec xs i (n + 1) hex1
  have h2 := extractVisitTime_spec xs i (n + 2) hex2
  have ht01 : extractVisitTime xs i n hex0 < extractVisitTime xs i (n + 1) hex1 := by
    by_contra h; push_neg at h
    have := Finset.sum_le_sum_of_subset (f := fun s => if (prefixExtend (k := k) N xs) s = i then 1 else 0) (Finset.range_mono h)
    change visitCountBefore (k := k) _ i _ ≤ visitCountBefore (k := k) _ i _ at this
    rw [h0.2, h1.2] at this; omega
  have ht12 : extractVisitTime xs i (n + 1) hex1 < extractVisitTime xs i (n + 2) hex2 := by
    by_contra h; push_neg at h
    have := Finset.sum_le_sum_of_subset (f := fun s => if (prefixExtend (k := k) N xs) s = i then 1 else 0) (Finset.range_mono h)
    change visitCountBefore (k := k) _ i _ ≤ visitCountBefore (k := k) _ i _ at this
    rw [h1.2, h2.2] at this; omega
  have h_aL1 : isNthVisitTime (k := k) (prefixExtend (k := k) N xs) i (n + 1)
      (extractVisitTime xs i n hex0 + (extractVisitTime xs i (n + 1) hex1 - extractVisitTime xs i n hex0)) := by
    convert h1 using 1; exact Nat.add_sub_cancel' (Nat.le_of_lt ht01)
  have h_aL1L2 : isNthVisitTime (k := k) (prefixExtend (k := k) N xs) i (n + 2)
      (extractVisitTime xs i n hex0 + (extractVisitTime xs i (n + 1) hex1 - extractVisitTime xs i n hex0) +
        (extractVisitTime xs i (n + 2) hex2 - extractVisitTime xs i (n + 1) hex1)) := by
    convert h2 using 1
    rw [Nat.add_sub_cancel' (Nat.le_of_lt ht01), Nat.add_sub_cancel' (Nat.le_of_lt ht12)]
  have hsucc : (prefixExtend (k := k) N xs) (extractVisitTime xs i n hex0 + 1) = b := by
    rcases carrier_mem_witness xs i n b hxs with ⟨t, _, htime, hb, _⟩
    have := isNthVisitTime_unique (k := k) _ i n t _ ((nthVisitTime_eq_some_iff (k := k) _ i n t).mp htime) h0
    subst this; simpa [successorAt] using hb
  exact segmentSwap_carrier_mem_adjacent xs i n b _ _ _
    (Nat.sub_pos_of_lt ht01) (Nat.sub_pos_of_lt ht12)
    (by rw [Nat.add_sub_cancel' (Nat.le_of_lt ht01), Nat.add_sub_cancel' (Nat.le_of_lt ht12)]; exact Nat.le_of_lt hbd2)
    h0 h_aL1 h_aL1L2 hsucc hxs

/-- Reverse membership: rawSwap of carrier_{n+1} member lands in carrier_n. -/
theorem rawSwap_bwd_mem {N : ℕ}
    (i : Fin k) (b : Fin k) (hbi : b ≠ i) (n : ℕ)
    (ys : Fin (N + 1) → Fin k)
    (hys : ys ∈ rowVisitCylinderEventUpToPrefixCarrier (k := k)
      i ({n + 1} : Finset ℕ) (fun j => if j = n + 1 then b else i) N)
    (hex0 : nthVisitTimeExists (k := k) (prefixExtend (k := k) N ys) i n)
    (hex1 : nthVisitTimeExists (k := k) (prefixExtend (k := k) N ys) i (n + 1))
    (hex2 : nthVisitTimeExists (k := k) (prefixExtend (k := k) N ys) i (n + 2))
    (hbd1 : extractVisitTime ys i (n + 1) hex1 < N)
    (hbd2 : extractVisitTime ys i (n + 2) hex2 < N) :
    rawSwap ys i n hex0 hex1 hex2 hbd1 hbd2 ∈
      rowVisitCylinderEventUpToPrefixCarrier (k := k)
        i ({n} : Finset ℕ) (fun j => if j = n then b else i) N := by
  have h0 := extractVisitTime_spec ys i n hex0
  have h1 := extractVisitTime_spec ys i (n + 1) hex1
  have h2 := extractVisitTime_spec ys i (n + 2) hex2
  have ht01 : extractVisitTime ys i n hex0 < extractVisitTime ys i (n + 1) hex1 := by
    by_contra h; push_neg at h
    have := Finset.sum_le_sum_of_subset (f := fun s => if (prefixExtend (k := k) N ys) s = i then 1 else 0) (Finset.range_mono h)
    change visitCountBefore (k := k) _ i _ ≤ visitCountBefore (k := k) _ i _ at this
    rw [h0.2, h1.2] at this; omega
  have ht12 : extractVisitTime ys i (n + 1) hex1 < extractVisitTime ys i (n + 2) hex2 := by
    by_contra h; push_neg at h
    have := Finset.sum_le_sum_of_subset (f := fun s => if (prefixExtend (k := k) N ys) s = i then 1 else 0) (Finset.range_mono h)
    change visitCountBefore (k := k) _ i _ ≤ visitCountBefore (k := k) _ i _ at this
    rw [h1.2, h2.2] at this; omega
  have h_aL2 : isNthVisitTime (k := k) (prefixExtend (k := k) N ys) i (n + 1)
      (extractVisitTime ys i n hex0 + (extractVisitTime ys i (n + 1) hex1 - extractVisitTime ys i n hex0)) := by
    convert h1 using 1; exact Nat.add_sub_cancel' (Nat.le_of_lt ht01)
  have h_aL1L2 : isNthVisitTime (k := k) (prefixExtend (k := k) N ys) i (n + 2)
      (extractVisitTime ys i n hex0 + (extractVisitTime ys i (n + 2) hex2 - extractVisitTime ys i (n + 1) hex1) +
        (extractVisitTime ys i (n + 1) hex1 - extractVisitTime ys i n hex0)) := by
    convert h2 using 1; show _ = extractVisitTime ys i (n + 2) hex2
    calc extractVisitTime ys i n hex0 + (extractVisitTime ys i (n + 2) hex2 - extractVisitTime ys i (n + 1) hex1) + (extractVisitTime ys i (n + 1) hex1 - extractVisitTime ys i n hex0)
        = extractVisitTime ys i n hex0 + (extractVisitTime ys i (n + 1) hex1 - extractVisitTime ys i n hex0) + (extractVisitTime ys i (n + 2) hex2 - extractVisitTime ys i (n + 1) hex1) := by omega
      _ = extractVisitTime ys i (n + 1) hex1 + (extractVisitTime ys i (n + 2) hex2 - extractVisitTime ys i (n + 1) hex1) := by rw [Nat.add_sub_cancel' (Nat.le_of_lt ht01)]
      _ = extractVisitTime ys i (n + 2) hex2 := Nat.add_sub_cancel' (Nat.le_of_lt ht12)
  have hsucc : (prefixExtend (k := k) N ys)
      (extractVisitTime ys i n hex0 + (extractVisitTime ys i (n + 1) hex1 - extractVisitTime ys i n hex0) + 1) = b := by
    rcases carrier_mem_witness ys i (n + 1) b hys with ⟨t, _, htime, hb, _⟩
    have := isNthVisitTime_unique (k := k) _ i (n + 1) t _ ((nthVisitTime_eq_some_iff (k := k) _ i (n + 1) t).mp htime) h_aL2
    subst this; simpa [successorAt] using hb
  exact segmentSwap_carrier_mem_adjacent_reverse ys i n b
    (extractVisitTime ys i n hex0)
    (extractVisitTime ys i (n + 2) hex2 - extractVisitTime ys i (n + 1) hex1)
    (extractVisitTime ys i (n + 1) hex1 - extractVisitTime ys i n hex0)
    (Nat.sub_pos_of_lt ht12) (Nat.sub_pos_of_lt ht01)
    (by show extractVisitTime ys i n hex0 + (extractVisitTime ys i (n + 2) hex2 - extractVisitTime ys i (n + 1) hex1) + (extractVisitTime ys i (n + 1) hex1 - extractVisitTime ys i n hex0) ≤ N
        calc _ = extractVisitTime ys i (n + 2) hex2 := by omega
          _ ≤ N := Nat.le_of_lt hbd2)
    h0 h_aL2 h_aL1L2 hsucc hys

/-- Forward evidence preservation. -/
theorem rawSwap_fwd_evid {N : ℕ}
    (xs : Fin (N + 1) → Fin k) (i : Fin k) (n : ℕ)
    (hex0 : nthVisitTimeExists (k := k) (prefixExtend (k := k) N xs) i n)
    (hex1 : nthVisitTimeExists (k := k) (prefixExtend (k := k) N xs) i (n + 1))
    (hex2 : nthVisitTimeExists (k := k) (prefixExtend (k := k) N xs) i (n + 2))
    (hbd1 : extractVisitTime xs i (n + 1) hex1 < N)
    (hbd2 : extractVisitTime xs i (n + 2) hex2 < N) :
    evidenceOf (n := N) (rawSwap xs i n hex0 hex1 hex2 hbd1 hbd2) = evidenceOf (n := N) xs := by
  have h0 := extractVisitTime_spec xs i n hex0
  have h1 := extractVisitTime_spec xs i (n + 1) hex1
  have h2 := extractVisitTime_spec xs i (n + 2) hex2
  have ht01 : extractVisitTime xs i n hex0 < extractVisitTime xs i (n + 1) hex1 := by
    by_contra h; push_neg at h
    have := Finset.sum_le_sum_of_subset (f := fun s => if (prefixExtend (k := k) N xs) s = i then 1 else 0) (Finset.range_mono h)
    change visitCountBefore (k := k) _ i _ ≤ visitCountBefore (k := k) _ i _ at this
    rw [h0.2, h1.2] at this; omega
  have ht12 : extractVisitTime xs i (n + 1) hex1 < extractVisitTime xs i (n + 2) hex2 := by
    by_contra h; push_neg at h
    have := Finset.sum_le_sum_of_subset (f := fun s => if (prefixExtend (k := k) N xs) s = i then 1 else 0) (Finset.range_mono h)
    change visitCountBefore (k := k) _ i _ ≤ visitCountBefore (k := k) _ i _ at this
    rw [h1.2, h2.2] at this; omega
  have val0 : xs ⟨extractVisitTime xs i n hex0, by omega⟩ = i := by
    have := h0.1; rwa [prefixExtend_apply_le' xs (Nat.le_of_lt (Nat.lt_trans ht01 hbd1))] at this
  have val1_fin : (⟨extractVisitTime xs i n hex0 + (extractVisitTime xs i (n + 1) hex1 - extractVisitTime xs i n hex0), by omega⟩ : Fin (N + 1)) = ⟨extractVisitTime xs i (n + 1) hex1, by omega⟩ :=
    Fin.ext (Nat.add_sub_cancel' (Nat.le_of_lt ht01))
  have val2_fin : (⟨extractVisitTime xs i n hex0 + (extractVisitTime xs i (n + 1) hex1 - extractVisitTime xs i n hex0) + (extractVisitTime xs i (n + 2) hex2 - extractVisitTime xs i (n + 1) hex1), by omega⟩ : Fin (N + 1)) = ⟨extractVisitTime xs i (n + 2) hex2, by omega⟩ := by
    apply Fin.ext; show _ = extractVisitTime xs i (n + 2) hex2
    have heq1 : extractVisitTime xs i n hex0 + (extractVisitTime xs i (n + 1) hex1 - extractVisitTime xs i n hex0) = extractVisitTime xs i (n + 1) hex1 := Nat.add_sub_cancel' (Nat.le_of_lt ht01)
    have heq2 : extractVisitTime xs i (n + 1) hex1 + (extractVisitTime xs i (n + 2) hex2 - extractVisitTime xs i (n + 1) hex1) = extractVisitTime xs i (n + 2) hex2 := Nat.add_sub_cancel' (Nat.le_of_lt ht12)
    simp only [Fin.val_mk]; omega
  have val1 : xs ⟨extractVisitTime xs i (n + 1) hex1, by omega⟩ = i := by
    have := h1.1; rwa [prefixExtend_apply_le' xs (Nat.le_of_lt hbd1)] at this
  have val2 : xs ⟨extractVisitTime xs i (n + 2) hex2, by omega⟩ = i := by
    have := h2.1; rwa [prefixExtend_apply_le' xs (Nat.le_of_lt hbd2)] at this
  exact segmentSwap_evidenceOf xs _ _ _
    (Nat.sub_pos_of_lt ht01) (Nat.sub_pos_of_lt ht12)
    (by rw [Nat.add_sub_cancel' (Nat.le_of_lt ht01), Nat.add_sub_cancel' (Nat.le_of_lt ht12)]; exact Nat.le_of_lt hbd2)
    (by rw [val0]; rw [show xs ⟨extractVisitTime xs i n hex0 + (extractVisitTime xs i (n + 1) hex1 - extractVisitTime xs i n hex0), _⟩ = xs ⟨extractVisitTime xs i (n + 1) hex1, _⟩ from congrArg xs val1_fin]; rw [val1])
    (by rw [show xs ⟨extractVisitTime xs i n hex0 + (extractVisitTime xs i (n + 1) hex1 - extractVisitTime xs i n hex0), _⟩ = xs ⟨extractVisitTime xs i (n + 1) hex1, _⟩ from congrArg xs val1_fin]; rw [val1]; rw [show xs ⟨extractVisitTime xs i n hex0 + (extractVisitTime xs i (n + 1) hex1 - extractVisitTime xs i n hex0) + (extractVisitTime xs i (n + 2) hex2 - extractVisitTime xs i (n + 1) hex1), _⟩ = xs ⟨extractVisitTime xs i (n + 2) hex2, _⟩ from congrArg xs val2_fin]; rw [val2])

/-- **THE CARRIER TRANSPORT EQUIV.** -/
theorem carrierTransportEquivAdjacent {N : ℕ}
    (i : Fin k) (b : Fin k) (hbi : b ≠ i) (n : ℕ)
    (hSuff : ∀ (m : ℕ) (xs : Fin (N + 1) → Fin k),
      xs ∈ rowVisitCylinderEventUpToPrefixCarrier (k := k)
        i ({m} : Finset ℕ) (fun j => if j = m then b else i) N →
      nthVisitTimeExists (k := k) (prefixExtend (k := k) N xs) i (m + 1) ∧
      nthVisitTimeExists (k := k) (prefixExtend (k := k) N xs) i (m + 2) ∧
      (∀ (h1 : nthVisitTimeExists (k := k) (prefixExtend (k := k) N xs) i (m + 1))
         (h2 : nthVisitTimeExists (k := k) (prefixExtend (k := k) N xs) i (m + 2)),
        extractVisitTime xs i (m + 1) h1 < N ∧ extractVisitTime xs i (m + 2) h2 < N)) :
    ∃ e :
      ↥(rowVisitCylinderEventUpToPrefixCarrier (k := k) i ({n} : Finset ℕ)
          (fun m => if m = n then b else i) N) ≃
      ↥(rowVisitCylinderEventUpToPrefixCarrier (k := k) i ({n + 1} : Finset ℕ)
          (fun m => if m = n + 1 then b else i) N),
      ∀ xs, evidenceOf (n := N) xs.1 = evidenceOf (n := N) (e xs).1 := by
  -- Abbreviations for hSuff extraction
  let S := fun m xs (hxs : xs ∈ rowVisitCylinderEventUpToPrefixCarrier (k := k)
      i ({m} : Finset ℕ) (fun j => if j = m then b else i) N) => hSuff m xs hxs
  refine ⟨{
    toFun := fun ⟨xs, hxs⟩ =>
      ⟨rawSwap xs i n (carrier_mem_visit_exists xs i n b hxs) (S n xs hxs).1 (S n xs hxs).2.1
        ((S n xs hxs).2.2 (S n xs hxs).1 (S n xs hxs).2.1).1
        ((S n xs hxs).2.2 (S n xs hxs).1 (S n xs hxs).2.1).2,
       rawSwap_fwd_mem i b hbi n xs hxs (S n xs hxs).1 (S n xs hxs).2.1
        ((S n xs hxs).2.2 (S n xs hxs).1 (S n xs hxs).2.1).1
        ((S n xs hxs).2.2 (S n xs hxs).1 (S n xs hxs).2.1).2⟩
    invFun := fun ⟨ys, hys⟩ =>
      let hex1 := carrier_mem_visit_exists ys i (n + 1) b hys
      let hex0 := nthVisitTimeExists_of_succ _ i n hex1
      let hex2 := (S (n + 1) ys hys).1
      have hbd1 : extractVisitTime ys i (n + 1) hex1 < N := by
        rcases carrier_mem_witness ys i (n + 1) b hys with ⟨t, htN, htime, _, _⟩
        have := isNthVisitTime_unique (k := k) _ i (n + 1) _ t
          (extractVisitTime_spec ys i (n + 1) hex1)
          ((nthVisitTime_eq_some_iff (k := k) _ i (n + 1) t).mp htime); omega
      have hbd2 : extractVisitTime ys i (n + 2) hex2 < N :=
        ((S (n + 1) ys hys).2.2 (S (n + 1) ys hys).1 (S (n + 1) ys hys).2.1).1
      have hmem := rawSwap_bwd_mem i b hbi n ys hys hex0 hex1 hex2 hbd1 hbd2
      Subtype.mk (rawSwap ys i n hex0 hex1 hex2 hbd1 hbd2) hmem
    left_inv := by
      intro ⟨xs, hxs⟩; ext1
      obtain ⟨_, _, _, _, _, heq⟩ := rawSwap_selfInverse xs i n
        (carrier_mem_visit_exists xs i n b hxs) (S n xs hxs).1 (S n xs hxs).2.1
        ((S n xs hxs).2.2 (S n xs hxs).1 (S n xs hxs).2.1).1
        ((S n xs hxs).2.2 (S n xs hxs).1 (S n xs hxs).2.1).2
      exact heq
    right_inv := by
      intro ⟨ys, hys⟩; ext1
      let hex1 := carrier_mem_visit_exists ys i (n + 1) b hys
      let hex0 := nthVisitTimeExists_of_succ _ i n hex1
      let hex2 := (S (n + 1) ys hys).1
      have hbd1 : extractVisitTime ys i (n + 1) hex1 < N := by
        rcases carrier_mem_witness ys i (n + 1) b hys with ⟨t, htN, htime, _, _⟩
        have := isNthVisitTime_unique (k := k) _ i (n + 1) _ t
          (extractVisitTime_spec ys i (n + 1) hex1)
          ((nthVisitTime_eq_some_iff (k := k) _ i (n + 1) t).mp htime); omega
      have hbd2 : extractVisitTime ys i (n + 2) hex2 < N :=
        ((S (n + 1) ys hys).2.2 (S (n + 1) ys hys).1 (S (n + 1) ys hys).2.1).1
      obtain ⟨_, _, _, _, _, heq⟩ := rawSwap_selfInverse ys i n hex0 hex1 hex2 hbd1 hbd2
      exact heq
  }, fun ⟨xs, hxs⟩ => (rawSwap_fwd_evid xs i n
    (carrier_mem_visit_exists xs i n b hxs) (S n xs hxs).1 (S n xs hxs).2.1
    ((S n xs hxs).2.2 (S n xs hxs).1 (S n xs hxs).2.1).1
    ((S n xs hxs).2.2 (S n xs hxs).1 (S n xs hxs).2.1).2).symm⟩

/-! ## Section 15: General carrier transport via composition -/

/-- Abbreviation for the hSuff hypothesis type used throughout carrier transport. -/
abbrev CarrierSuffHyp (i : Fin k) (b : Fin k) (N : ℕ) : Prop :=
  ∀ (m : ℕ) (xs : Fin (N + 1) → Fin k),
    xs ∈ rowVisitCylinderEventUpToPrefixCarrier (k := k)
      i ({m} : Finset ℕ) (fun j => if j = m then b else i) N →
    nthVisitTimeExists (k := k) (prefixExtend (k := k) N xs) i (m + 1) ∧
    nthVisitTimeExists (k := k) (prefixExtend (k := k) N xs) i (m + 2) ∧
    (∀ (h1 : nthVisitTimeExists (k := k) (prefixExtend (k := k) N xs) i (m + 1))
       (h2 : nthVisitTimeExists (k := k) (prefixExtend (k := k) N xs) i (m + 2)),
      extractVisitTime xs i (m + 1) h1 < N ∧ extractVisitTime xs i (m + 2) h2 < N)

/-- Compose `d` adjacent carrier transport Equivs to build carrier(n) ≃ carrier(n+d).
Uses `n + 0 = n` and `n + (d+1) = (n+d) + 1` definitionally. -/
@[reducible] noncomputable def carrierTransportEquivAscendingChain {N : ℕ}
    (i : Fin k) (b : Fin k) (hbi : b ≠ i) (n : ℕ)
    (hSuff : CarrierSuffHyp (k := k) i b N) :
    (d : ℕ) →
      ↥(rowVisitCylinderEventUpToPrefixCarrier (k := k) i ({n} : Finset ℕ)
          (fun m => if m = n then b else i) N) ≃
      ↥(rowVisitCylinderEventUpToPrefixCarrier (k := k) i ({n + d} : Finset ℕ)
          (fun m => if m = n + d then b else i) N)
  | 0 => Equiv.refl _
  | d + 1 =>
    (carrierTransportEquivAscendingChain i b hbi n hSuff d).trans
      (carrierTransportEquivAdjacent i b hbi (n + d) hSuff).choose

/-- Evidence preservation for the ascending chain, by induction on `d`. -/
lemma carrierTransportEquivAscendingChain_evidence {N : ℕ}
    (i : Fin k) (b : Fin k) (hbi : b ≠ i) (n : ℕ)
    (hSuff : CarrierSuffHyp (k := k) i b N) :
    ∀ (d : ℕ) (xs : ↥(rowVisitCylinderEventUpToPrefixCarrier (k := k) i ({n} : Finset ℕ)
        (fun m => if m = n then b else i) N)),
      evidenceOf (n := N) xs.1 =
        evidenceOf (n := N) (carrierTransportEquivAscendingChain i b hbi n hSuff d xs).1
  | 0, _ => rfl
  | d + 1, xs => by
    simp only [carrierTransportEquivAscendingChain, Equiv.trans_apply]
    exact (carrierTransportEquivAscendingChain_evidence i b hbi n hSuff d xs).trans
      ((carrierTransportEquivAdjacent i b hbi (n + d) hSuff).choose_spec
        (carrierTransportEquivAscendingChain i b hbi n hSuff d xs))

/-- **GENERAL CARRIER TRANSPORT EQUIV**: for arbitrary visit indices n, n'.
Composes adjacent Equivs via Nat induction; uses `.symm` for the descending case. -/
theorem carrierTransportEquivGeneral {N : ℕ}
    (i : Fin k) (b : Fin k) (hbi : b ≠ i) (n n' : ℕ)
    (hSuff : CarrierSuffHyp (k := k) i b N) :
    ∃ e :
      ↥(rowVisitCylinderEventUpToPrefixCarrier (k := k) i ({n} : Finset ℕ)
          (fun m => if m = n then b else i) N) ≃
      ↥(rowVisitCylinderEventUpToPrefixCarrier (k := k) i ({n'} : Finset ℕ)
          (fun m => if m = n' then b else i) N),
      ∀ xs :
        ↥(rowVisitCylinderEventUpToPrefixCarrier (k := k) i ({n} : Finset ℕ)
            (fun m => if m = n then b else i) N),
        evidenceOf (n := N) xs.1 = evidenceOf (n := N) (e xs).1 := by
  by_cases h : n ≤ n'
  · -- Case n ≤ n': ascending chain of length (n' - n)
    obtain ⟨d, rfl⟩ : ∃ d, n' = n + d := ⟨n' - n, (Nat.add_sub_cancel' h).symm⟩
    exact ⟨carrierTransportEquivAscendingChain i b hbi n hSuff d,
           carrierTransportEquivAscendingChain_evidence i b hbi n hSuff d⟩
  · -- Case n' < n: ascending chain from n' to n, then .symm
    push_neg at h
    obtain ⟨d, rfl⟩ : ∃ d, n = n' + d + 1 := ⟨n - n' - 1, by omega⟩
    let chain := carrierTransportEquivAscendingChain i b hbi n' hSuff (d + 1)
    refine ⟨chain.symm, fun xs => ?_⟩
    have hev := carrierTransportEquivAscendingChain_evidence i b hbi n' hSuff (d + 1)
      (chain.symm xs)
    rw [chain.apply_symm_apply] at hev
    exact hev.symm

/-! ## Section 16: Multi-index carrier transport for single state

The Level 2 infrastructure (`measure_start_inter_rowVisitCylinderEventUpTo_eq_...`)
takes an Equiv between carriers with ARBITRARY S (Finset of visit indices).
For per-row PE, we need: given S containing both n and n+1, an evidence-preserving
Equiv between carrier(i, S, v, N) and carrier(i, S, v ∘ swap(n, n+1), N).

This is built from rawSwap: the adjacent carrier transport transposes
queue entries n ↔ n+1 and leaves others unchanged, so it maps the multi-index
carrier with value function v to the carrier with v ∘ swap(n, n+1). -/

/-- Adjacent value swap for multi-index carrier via segmentSwap (not rawSwap!):
segmentSwap maps carrier(i, S, v, N) → carrier(i, S, v', N) where v' swaps at n, n+1.
Uses segmentSwap DIRECTLY with external parameters — no rawSwap indirection. -/
theorem segmentSwap_multiIndex_carrier_mem {N : ℕ}
    (i : Fin k) (n : ℕ) (a L1 L2 : ℕ)
    (hL1 : 0 < L1) (hL2 : 0 < L2) (hcN : a + L1 + L2 ≤ N)
    (S : Finset ℕ) (v : ℕ → Fin k)
    (hn : n ∈ S) (hn1 : n + 1 ∈ S)
    (xs : Fin (N + 1) → Fin k)
    (hxs : xs ∈ rowVisitCylinderEventUpToPrefixCarrier (k := k) i S v N)
    -- Visit-time data: a is the n-th visit time, a+L1 is (n+1)-th, a+L1+L2 is (n+2)-th
    (h_a : isNthVisitTime (k := k) (prefixExtend (k := k) N xs) i n a)
    (h_aL1 : isNthVisitTime (k := k) (prefixExtend (k := k) N xs) i (n + 1) (a + L1))
    (h_aL1L2 : isNthVisitTime (k := k) (prefixExtend (k := k) N xs) i (n + 2) (a + L1 + L2)) :
    segmentSwap xs a L1 L2 hL1 hL2 hcN ∈
      rowVisitCylinderEventUpToPrefixCarrier (k := k) i S
        (fun m => if m = n then v (n + 1)
                  else if m = n + 1 then v n
                  else v m) N := by
  -- Unfold carrier membership
  simp only [rowVisitCylinderEventUpToPrefixCarrier, Finset.mem_filter, Finset.mem_univ,
    true_and] at hxs ⊢
  -- Visit-time lemmas for the swapped trajectory
  have hnt_n := nthVisitTime_prefixExtend_segmentSwap_eq_of_le
    xs i n a L1 L2 hL1 hL2 hcN h_a (by omega : a < N)
  have hnt_n1 := nthVisitTime_segmentSwap_n1 xs i n a L1 L2
    hL1 hL2 hcN h_a h_aL1 h_aL1L2
  -- Original successor witnesses
  rcases hxs n hn with ⟨tn, htnN, htimen, hsuccn⟩
  rcases hxs (n + 1) hn1 with ⟨tn1, htn1N, htimen1, hsuccn1⟩
  have htn_eq : tn = a := isNthVisitTime_unique (k := k) _ i n tn a
    ((nthVisitTime_eq_some_iff (k := k) _ i n tn).mp htimen) h_a
  have htn1_eq : tn1 = a + L1 := isNthVisitTime_unique (k := k) _ i (n + 1) tn1 (a + L1)
    ((nthVisitTime_eq_some_iff (k := k) _ i (n + 1) tn1).mp htimen1) h_aL1
  rw [htn_eq] at hsuccn; rw [htn1_eq] at hsuccn1
  -- For each m ∈ S, produce the witness
  intro m hmS
  by_cases hmn : m = n
  · -- m = n: successor at visit n becomes v(n+1) (by segmentSwap_successor_at_a)
    simp only [hmn, ite_true]
    refine ⟨a, by omega, hmn ▸ hnt_n, ?_⟩
    simp only [successorAt, prefixExtend_apply_le' _ (by omega : a + 1 ≤ N)]
    rw [segmentSwap_successor_at_a xs a L1 L2 hL1 hL2 hcN]
    have := hsuccn1; simp only [successorAt] at this
    rwa [prefixExtend_apply_le' xs (by omega : a + L1 + 1 ≤ N)] at this
  · by_cases hmn1 : m = n + 1
    · -- m = n+1: successor at visit n+1 becomes v(n) (by segmentSwap_successor_at_mid)
      have hne : n + 1 ≠ n := by omega
      simp only [hmn1, hne, ite_true, ite_false]
      refine ⟨a + L2, by omega, hmn1 ▸ hnt_n1, ?_⟩
      simp only [successorAt, prefixExtend_apply_le' _ (by omega : a + L2 + 1 ≤ N)]
      rw [segmentSwap_successor_at_mid xs a L1 L2 hL1 hL2 hcN]
      have := hsuccn; simp only [successorAt] at this
      rw [prefixExtend_apply_le' xs (by omega : a + 1 ≤ N)] at this; exact this
    · -- m ∉ {n, n+1}: visit time outside swap region → identity
      simp only [hmn, hmn1, ite_false]
      rcases hxs m hmS with ⟨t, htN, htime, hsucc⟩
      have hm_time := (nthVisitTime_eq_some_iff (k := k) _ i m t).mp htime
      -- Case split: m < n (visit before swap) or m > n+1 (visit after swap)
      by_cases hm_lt : m < n
      · -- m < n: visit time t < a → all positions ≤ t+1 are ≤ a → identity
        have ht_lt : t < a := by
          by_contra hge; push_neg at hge
          have := Finset.sum_le_sum_of_subset
            (f := fun s => if (prefixExtend (k := k) N xs) s = i then 1 else 0)
            (Finset.range_mono hge)
          change visitCountBefore (k := k) _ i _ ≤ visitCountBefore (k := k) _ i _ at this
          rw [hm_time.2, h_a.2] at this; omega
        refine ⟨t, htN, ?_, ?_⟩
        · rw [nthVisitTime_eq_some_iff (k := k)]; constructor
          · rw [prefixExtend_apply_le' _ (by omega),
                segmentSwap_eq_of_le xs a L1 L2 hL1 hL2 hcN ⟨t, by omega⟩ (by simp; omega)]
            have := hm_time.1; rwa [prefixExtend_apply_le' xs (by omega)] at this
          · -- visitCountBefore: all positions < t have same trajectory value
            change visitCountBefore (k := k)
              (prefixExtend (k := k) N (segmentSwap xs a L1 L2 hL1 hL2 hcN)) i t = m
            rw [← hm_time.2]; simp only [visitCountBefore]
            apply Finset.sum_congr rfl
            intro s hs; simp only [Finset.mem_range] at hs
            congr 1
            rw [prefixExtend_apply_le' _ (by omega),
                segmentSwap_eq_of_le xs a L1 L2 hL1 hL2 hcN ⟨s, by omega⟩ (by simp; omega),
                prefixExtend_apply_le' xs (by omega)]
        · simp only [successorAt]
          rw [prefixExtend_apply_le' _ (by omega),
              segmentSwap_eq_of_le xs a L1 L2 hL1 hL2 hcN ⟨t + 1, by omega⟩ (by simp; omega)]
          have := hsucc; simp only [successorAt] at this
          rwa [prefixExtend_apply_le' xs (by omega)] at this
      · -- m > n+1: visit time t ≥ a+L1+L2 → positions t, t+1 are > a+L1+L2 → identity
        have hm_ge : m ≥ n + 2 := by omega
        have ht_ge : t ≥ a + L1 + L2 := by
          by_contra hlt; push_neg at hlt
          have := Finset.sum_le_sum_of_subset
            (f := fun s => if (prefixExtend (k := k) N xs) s = i then 1 else 0)
            (Finset.range_mono (by omega : t ≤ a + L1 + L2))
          change visitCountBefore (k := k) _ i _ ≤ visitCountBefore (k := k) _ i _ at this
          rw [hm_time.2, h_aL1L2.2] at this
          have hmeq : m = n + 2 := by omega
          rw [hmeq] at hm_time
          exact absurd (isNthVisitTime_unique (k := k) _ i (n + 2) t (a + L1 + L2)
            hm_time h_aL1L2) (by omega)
        refine ⟨t, htN, ?_, ?_⟩
        · rw [nthVisitTime_eq_some_iff (k := k)]; constructor
          · rw [prefixExtend_apply_le' _ (by omega)]
            by_cases ht_eq : t = a + L1 + L2
            · -- t exactly at the boundary: use segmentSwap_at_end
              rw [show (⟨t, _⟩ : Fin (N + 1)) = ⟨a + L1 + L2, by omega⟩ from Fin.ext (by simp [ht_eq])]
              rw [segmentSwap_at_end xs a L1 L2 hL1 hL2 hcN]
              have := h_aL1.1; rwa [prefixExtend_apply_le' xs (by omega)] at this
            · -- t strictly past the boundary
              rw [segmentSwap_eq_of_gt xs a L1 L2 hL1 hL2 hcN ⟨t, by omega⟩ (by simp; omega)]
              have := hm_time.1; rwa [prefixExtend_apply_le' xs (by omega)] at this
          · -- visitCountBefore at t: positions < a+L1+L2 have same count (by swap symmetry),
            -- positions ≥ a+L1+L2 are identity.
            -- The key: visitCountBefore_segmentSwap_at_endpoint gives equality at a+L1+L2,
            -- and identity after that gives equality at t.
            have hvc_end := visitCountBefore_segmentSwap_at_endpoint xs i n a L1 L2
              hL1 hL2 hcN h_a h_aL1 h_aL1L2
            -- visitCountBefore(swapped, t) = visitCountBefore(original, t)
            -- Split at cutpoint a+L1+L2 using additive decomposition
            change visitCountBefore (k := k) (prefixExtend (k := k) N
              (segmentSwap xs a L1 L2 hL1 hL2 hcN)) i t = m
            rw [← hm_time.2]
            -- Both sides split as: sum over [0, a+L1+L2) + sum over [a+L1+L2, t)
            -- First parts agree by hvc_end/h_aL1L2.2
            -- Second parts agree by identity after swap region
            simp only [visitCountBefore]
            rw [← Finset.sum_filter_add_sum_filter_not (Finset.range t)
              (fun s => s < a + L1 + L2)]
            rw [← Finset.sum_filter_add_sum_filter_not (Finset.range t)
              (fun s => s < a + L1 + L2)]
            congr 1
            · -- [0, a+L1+L2) part: totals agree
              have : (Finset.range t).filter (fun s => s < a + L1 + L2) =
                  Finset.range (a + L1 + L2) := by
                ext s; simp [Finset.mem_filter, Finset.mem_range]; omega
              rw [this]
              -- Both = n + 2
              rw [show (∑ x ∈ Finset.range (a + L1 + L2),
                if prefixExtend (k := k) N (segmentSwap xs a L1 L2 hL1 hL2 hcN) x = i then 1 else 0)
                = n + 2 from hvc_end,
                show (∑ x ∈ Finset.range (a + L1 + L2),
                if prefixExtend (k := k) N xs x = i then 1 else 0)
                = n + 2 from h_aL1L2.2]
            · -- [a+L1+L2, t) part: identity region
              apply Finset.sum_congr rfl; intro s hs
              simp only [Finset.mem_filter, Finset.mem_range, not_lt] at hs
              -- hs : s < t ∧ ¬(s < a + L1 + L2), i.e. s ≥ a + L1 + L2
              congr 1
              rw [prefixExtend_apply_le' _ (by omega)]
              by_cases hseq : s = a + L1 + L2
              · subst hseq
                -- Both sides: segmentSwap at a+L1+L2 gives xs(a+L1) = i,
                -- prefixExtend xs at a+L1+L2 gives xs(a+L1+L2) = i. Both = i.
                simp only [segmentSwap_at_end xs a L1 L2 hL1 hL2 hcN,
                  prefixExtend_apply_le' xs (by omega)]
                have hlhs : xs ⟨a + L1, by omega⟩ = i := by
                  have := h_aL1.1; rwa [prefixExtend_apply_le' xs (by omega)] at this
                have hrhs : xs ⟨a + L1 + L2, by omega⟩ = i := by
                  have := h_aL1L2.1; rwa [prefixExtend_apply_le' xs (by omega)] at this
                simp [hlhs, hrhs]
              · congr 1
                rw [segmentSwap_eq_of_gt xs a L1 L2 hL1 hL2 hcN ⟨s, by omega⟩ (by simp; omega),
                    prefixExtend_apply_le' xs (by omega)]
        · simp only [successorAt]
          rw [prefixExtend_apply_le' _ (by omega),
              segmentSwap_eq_of_gt xs a L1 L2 hL1 hL2 hcN ⟨t + 1, by omega⟩ (by simp; omega)]
          have := hsucc; simp only [successorAt] at this
          rwa [prefixExtend_apply_le' xs (by omega)] at this

end CarrierTransportBridge

end Mettapedia.Logic
