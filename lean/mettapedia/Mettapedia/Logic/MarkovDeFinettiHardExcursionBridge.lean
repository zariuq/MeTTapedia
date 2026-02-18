import Mettapedia.Logic.MarkovDeFinettiHardExcursionModel
import Mettapedia.Logic.MarkovDeFinettiHardCopyPerm

/-! LLM primer:
- Traj k N = Fin (N+1) → Fin k
- Parameterized by (a, L1, L2) where b = a + L1, c = a + L1 + L2
- segmentSwap uses dependent `if h :` so branch conditions are available to omega
- swapRemap uses < boundaries matching transition index semantics

# Excursion Bridge (Phase B, Step 4)
-/

noncomputable section

namespace Mettapedia.Logic

open scoped Classical BigOperators

namespace MarkovDeFinettiHardExcursionBridge

open Finset
open MarkovDeFinettiHardExcursions
open MarkovDeFinettiHardExcursionModel
open MarkovDeFinettiHardBESTCore
open MarkovDeFinettiHardEulerTrails
open MarkovDeFinettiHardEulerTrailFiber
open MarkovDeFinettiHardCopyPerm
open MarkovExchangeability
open UniversalPrediction.FiniteAlphabet
open UniversalPrediction.MarkovExchangeabilityBridge
open MarkovDeFinettiHard

variable {k : ℕ}

/-! ## Segment swap -/

/-- Swap segments of lengths L1 and L2 starting after position a.
Uses dependent `if h :` so branch conditions are available in proofs. -/
def segmentSwap {N : ℕ} (xs : Traj k N) (a L1 L2 : ℕ)
    (_hL1 : 0 < L1) (hL2 : 0 < L2) (hcN : a + L1 + L2 ≤ N) : Traj k N :=
  fun ⟨t, ht⟩ =>
    if _h1 : t ≤ a then xs ⟨t, ht⟩
    else if _h2 : t ≤ a + L2 then
      xs ⟨t + L1, by omega⟩
    else if _h3 : t ≤ a + L1 + L2 then
      xs ⟨t - L2, by omega⟩
    else xs ⟨t, ht⟩

/-! ## Position remap -/

def swapRemap (a L1 L2 : ℕ) (t : ℕ) : ℕ :=
  if t < a then t
  else if t < a + L2 then t + L1
  else if t < a + L1 + L2 then t - L2
  else t

lemma swapRemap_lt {N : ℕ} (a L1 L2 : ℕ)
    (_hL1 : 0 < L1) (_hL2 : 0 < L2) (hcN : a + L1 + L2 ≤ N)
    (t : ℕ) (ht : t < N) : swapRemap a L1 L2 t < N := by
  simp only [swapRemap]; split_ifs <;> omega

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

/-! ## Transition pair correspondence -/

theorem segmentSwap_transition_pair {N : ℕ} (xs : Traj k N) (a L1 L2 : ℕ)
    (hL1 : 0 < L1) (hL2 : 0 < L2) (hcN : a + L1 + L2 ≤ N)
    (ha_ret : xs ⟨a, by omega⟩ = xs 0)
    (hb_ret : xs ⟨a + L1, by omega⟩ = xs 0)
    (hc_ret : xs ⟨a + L1 + L2, by omega⟩ = xs 0)
    (j : Fin N) :
    let σj := swapPermFin a L1 L2 hL1 hL2 hcN j
    (segmentSwap xs a L1 L2 hL1 hL2 hcN (Fin.castSucc j),
     segmentSwap xs a L1 L2 hL1 hL2 hcN (Fin.succ j)) =
    (xs (Fin.castSucc σj), xs (Fin.succ σj)) := by
  rcases j with ⟨t, ht⟩
  simp only [swapPermFin, swapRemap]
  rw [Prod.mk.injEq]
  simp only [segmentSwap, Fin.castSucc_mk, Fin.succ_mk]
  -- After simp, both source and target are nested dite/ite expressions.
  -- split_ifs resolves all branching; boundary cases need return conditions.
  -- Helper: any Fin position whose val equals a return position index gives xs 0
  have to_xs0 : ∀ (i : Fin (N + 1)),
      i.val = a ∨ i.val = a + L1 ∨ i.val = a + L1 + L2 → xs i = xs 0 := by
    intro i h
    rcases h with h | h | h
    · exact (congrArg xs (Fin.ext h)).trans ha_ret
    · exact (congrArg xs (Fin.ext h)).trans hb_ret
    · exact (congrArg xs (Fin.ext h)).trans hc_ret
  constructor <;> split_ifs <;>
    first
    | rfl
    | (congr 1; ext; simp; omega)
    | omega
    | (refine (to_xs0 _ ?_).trans (to_xs0 _ ?_).symm <;> simp <;> omega)

/-! ## Transition count preservation -/

theorem segmentSwap_transCount {N : ℕ} (xs : Traj k N) (a L1 L2 : ℕ)
    (hL1 : 0 < L1) (hL2 : 0 < L2) (hcN : a + L1 + L2 ≤ N)
    (ha_ret : xs ⟨a, by omega⟩ = xs 0)
    (hb_ret : xs ⟨a + L1, by omega⟩ = xs 0)
    (hc_ret : xs ⟨a + L1 + L2, by omega⟩ = xs 0)
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
    have h := segmentSwap_transition_pair xs a L1 L2 hL1 hL2 hcN ha_ret hb_ret hc_ret j
    simp only at h; rw [Prod.mk.injEq] at h; rw [h.1, h.2]
  rw [hfilt_eq]
  apply Finset.card_bij (fun j _ => σ j)
  · intro j hj; simpa using hj
  · intro j₁ _ j₂ _ h; exact hσ.1 h
  · intro j hj
    obtain ⟨j', rfl⟩ := hσ.2 j
    exact ⟨j', by simpa using hj, rfl⟩

/-! ## Derived properties -/

lemma segmentSwap_start {N : ℕ} (xs : Traj k N) (a L1 L2 : ℕ)
    (hL1 : 0 < L1) (hL2 : 0 < L2) (hcN : a + L1 + L2 ≤ N) :
    segmentSwap xs a L1 L2 hL1 hL2 hcN 0 = xs 0 := by
  simp [segmentSwap]

lemma segmentSwap_last {N : ℕ} (xs : Traj k N) (a L1 L2 : ℕ)
    (hL1 : 0 < L1) (hL2 : 0 < L2) (hcN : a + L1 + L2 ≤ N)
    (hb_ret : xs ⟨a + L1, by omega⟩ = xs 0)
    (hc_ret : xs ⟨a + L1 + L2, by omega⟩ = xs 0) :
    segmentSwap xs a L1 L2 hL1 hL2 hcN (Fin.last N) = xs (Fin.last N) := by
  simp only [segmentSwap, Fin.last]
  split_ifs with h1 h2 h3
  · -- N ≤ a: impossible
    omega
  · -- N ≤ a + L2: impossible (since a + L1 + L2 ≤ N and L1 > 0)
    omega
  · -- N ≤ a + L1 + L2: boundary case, xs(N - L2) = xs(N) via returns
    have : xs ⟨N - L2, by omega⟩ = xs ⟨a + L1, by omega⟩ := by
      congr 1; ext; simp; omega
    rw [this, hb_ret, ← hc_ret]; congr 1; ext; simp; omega
  · -- N > a + L1 + L2: suffix, identity
    rfl

theorem segmentSwap_stateOfTraj {N : ℕ} (xs : Traj k N) (a L1 L2 : ℕ)
    (hL1 : 0 < L1) (hL2 : 0 < L2) (hcN : a + L1 + L2 ≤ N)
    (ha_ret : xs ⟨a, by omega⟩ = xs 0)
    (hb_ret : xs ⟨a + L1, by omega⟩ = xs 0)
    (hc_ret : xs ⟨a + L1 + L2, by omega⟩ = xs 0) :
    stateOfTraj (k := k) (segmentSwap xs a L1 L2 hL1 hL2 hcN) =
      stateOfTraj (k := k) xs := by
  refine MarkovState.ext ?_ ?_ ?_
  · simp [stateOfTraj, segmentSwap_start]
  · ext α β
    simp only [stateOfTraj, countsOfFn_apply]
    exact segmentSwap_transCount xs a L1 L2 hL1 hL2 hcN ha_ret hb_ret hc_ret α β
  · simp [stateOfTraj, segmentSwap_last xs a L1 L2 hL1 hL2 hcN hb_ret hc_ret]

theorem segmentSwap_mem_fiber {N : ℕ} (s : MarkovState k)
    (xs : Traj k N) (hxs : xs ∈ fiber k N s)
    (a L1 L2 : ℕ) (hL1 : 0 < L1) (hL2 : 0 < L2) (hcN : a + L1 + L2 ≤ N)
    (ha_ret : xs ⟨a, by omega⟩ = xs 0)
    (hb_ret : xs ⟨a + L1, by omega⟩ = xs 0)
    (hc_ret : xs ⟨a + L1 + L2, by omega⟩ = xs 0) :
    segmentSwap xs a L1 L2 hL1 hL2 hcN ∈ fiber k N s := by
  rw [fiber, Finset.mem_filter]
  exact ⟨Finset.mem_univ _,
    (segmentSwap_stateOfTraj xs a L1 L2 hL1 hL2 hcN ha_ret hb_ret hc_ret).trans
      (Finset.mem_filter.1 hxs).2⟩

/-! ## Prefix/suffix invariance -/

lemma segmentSwap_eq_of_le_a {N : ℕ} (xs : Traj k N) (a L1 L2 : ℕ)
    (hL1 : 0 < L1) (hL2 : 0 < L2) (hcN : a + L1 + L2 ≤ N)
    (i : Fin (N + 1)) (hi : (i : ℕ) ≤ a) :
    segmentSwap xs a L1 L2 hL1 hL2 hcN i = xs i := by
  have h1 : (i : ℕ) ≤ a := hi
  simp [segmentSwap, h1]

/-- Variant of `segmentSwap_eq_of_le_a` with plain ℕ position argument. -/
lemma segmentSwap_eq_of_le_a' {N : ℕ} (xs : Traj k N) (a L1 L2 : ℕ)
    (hL1 : 0 < L1) (hL2 : 0 < L2) (hcN : a + L1 + L2 ≤ N)
    (p : ℕ) (hp : p < N + 1) (hle : p ≤ a) :
    segmentSwap xs a L1 L2 hL1 hL2 hcN ⟨p, hp⟩ = xs ⟨p, hp⟩ :=
  segmentSwap_eq_of_le_a xs a L1 L2 hL1 hL2 hcN ⟨p, hp⟩ hle

lemma segmentSwap_eq_of_gt_range {N : ℕ} (xs : Traj k N) (a L1 L2 : ℕ)
    (hL1 : 0 < L1) (hL2 : 0 < L2) (hcN : a + L1 + L2 ≤ N)
    (i : Fin (N + 1)) (hi : a + L1 + L2 < (i : ℕ)) :
    segmentSwap xs a L1 L2 hL1 hL2 hcN i = xs i := by
  have h1 : ¬((i : ℕ) ≤ a) := by omega
  have h2 : ¬((i : ℕ) ≤ a + L2) := by omega
  have h3 : ¬((i : ℕ) ≤ a + L1 + L2) := by omega
  simp [segmentSwap, h1, h2, h3]

/-- Variant of `segmentSwap_eq_of_gt_range` with plain ℕ position argument
(avoids Fin coercion opacity in omega). -/
lemma segmentSwap_eq_of_gt_range' {N : ℕ} (xs : Traj k N) (a L1 L2 : ℕ)
    (hL1 : 0 < L1) (hL2 : 0 < L2) (hcN : a + L1 + L2 ≤ N)
    (p : ℕ) (hp : p < N + 1) (hgt : a + L1 + L2 < p) :
    segmentSwap xs a L1 L2 hL1 hL2 hcN ⟨p, hp⟩ = xs ⟨p, hp⟩ :=
  segmentSwap_eq_of_gt_range xs a L1 L2 hL1 hL2 hcN ⟨p, hp⟩ hgt

lemma trajPrefix_segmentSwap_eq_of_prefix_before_swap
    {n N : ℕ} (h : n ≤ N)
    (xs : Traj k N) (a L1 L2 : ℕ) (hna : n ≤ a)
    (hL1 : 0 < L1) (hL2 : 0 < L2) (hcN : a + L1 + L2 ≤ N) :
    trajPrefix (k := k) h (segmentSwap xs a L1 L2 hL1 hL2 hcN) =
      trajPrefix (k := k) h xs := by
  funext i
  dsimp [trajPrefix]
  have hi_le_a : ((Fin.castLE (Nat.succ_le_succ h) i : Fin (N + 1)) : ℕ) ≤ a := by
    have hi_le_n : (i : ℕ) ≤ n := Nat.lt_succ_iff.mp i.is_lt
    have hi_cast_eq : ((Fin.castLE (Nat.succ_le_succ h) i : Fin (N + 1)) : ℕ) = (i : ℕ) := rfl
    exact hi_cast_eq ▸ le_trans hi_le_n hna
  exact segmentSwap_eq_of_le_a xs a L1 L2 hL1 hL2 hcN
    (Fin.castLE (Nat.succ_le_succ h) i) hi_le_a

/-- If the swap window lies entirely inside the prefix horizon, taking prefix
after swap is definitionally the same as swapping inside the prefixed
trajectory. -/
lemma trajPrefix_segmentSwap_eq_segmentSwap_prefix
    {n N : ℕ} (h : n ≤ N)
    (xs : Traj k N) (a L1 L2 : ℕ)
    (hL1 : 0 < L1) (hL2 : 0 < L2)
    (hcShort : a + L1 + L2 ≤ n) :
    trajPrefix (k := k) h
      (segmentSwap xs a L1 L2 hL1 hL2 (le_trans hcShort h)) =
      segmentSwap (trajPrefix (k := k) h xs) a L1 L2 hL1 hL2 hcShort := by
  funext i
  rfl

lemma prefixState_segmentSwap_eq_of_prefix_before_swap
    {n N : ℕ} (h : n ≤ N)
    (xs : Traj k N) (a L1 L2 : ℕ) (hna : n ≤ a)
    (hL1 : 0 < L1) (hL2 : 0 < L2) (hcN : a + L1 + L2 ≤ N) :
    prefixState (k := k) h (segmentSwap xs a L1 L2 hL1 hL2 hcN) =
      prefixState (k := k) h xs := by
  simp [prefixState, trajPrefix_segmentSwap_eq_of_prefix_before_swap (k := k) h xs a L1 L2 hna hL1 hL2 hcN]

lemma segmentSwap_mem_prefixFiber_of_prefix_before_swap
    {n N : ℕ} (h : n ≤ N)
    (e eN : MarkovState k) (xs : Traj k N)
    (a L1 L2 : ℕ) (hna : n ≤ a)
    (hL1 : 0 < L1) (hL2 : 0 < L2) (hcN : a + L1 + L2 ≤ N)
    (ha_ret : xs ⟨a, by omega⟩ = xs 0)
    (hb_ret : xs ⟨a + L1, by omega⟩ = xs 0)
    (hc_ret : xs ⟨a + L1 + L2, by omega⟩ = xs 0)
    (hxs : xs ∈ prefixFiber (k := k) h e eN) :
    segmentSwap xs a L1 L2 hL1 hL2 hcN ∈ prefixFiber (k := k) h e eN := by
  have hxsFiber : xs ∈ fiber k N eN := (Finset.mem_filter.1 hxs).1
  have hmemFiber :
      segmentSwap xs a L1 L2 hL1 hL2 hcN ∈ fiber k N eN :=
    segmentSwap_mem_fiber eN xs hxsFiber a L1 L2 hL1 hL2 hcN ha_ret hb_ret hc_ret
  refine Finset.mem_filter.2 ?_
  refine ⟨hmemFiber, ?_⟩
  have hprefix : prefixState (k := k) h xs = e := (Finset.mem_filter.1 hxs).2
  simpa [hprefix] using
    prefixState_segmentSwap_eq_of_prefix_before_swap (k := k) h xs a L1 L2 hna hL1 hL2 hcN

/-! ## Segment swap involutivity

Swapping with `(a, L2, L1)` undoes a swap with `(a, L1, L2)`. -/

theorem segmentSwap_involutive {N : ℕ} (xs : Traj k N) (a L1 L2 : ℕ)
    (hL1 : 0 < L1) (hL2 : 0 < L2) (hcN : a + L1 + L2 ≤ N) :
    segmentSwap (segmentSwap xs a L1 L2 hL1 hL2 hcN) a L2 L1 hL2 hL1
      (by omega) = xs := by
  funext ⟨t, ht⟩
  simp only [segmentSwap]
  split_ifs <;> first | rfl | (congr 1; ext; dsimp only; omega)

/-! ## Segment swap is injective on trajectories -/

theorem segmentSwap_injective {N : ℕ} (a L1 L2 : ℕ)
    (hL1 : 0 < L1) (hL2 : 0 < L2) (hcN : a + L1 + L2 ≤ N)
    {xs ys : Traj k N}
    (h : segmentSwap xs a L1 L2 hL1 hL2 hcN =
         segmentSwap ys a L1 L2 hL1 hL2 hcN) :
    xs = ys := by
  rw [← segmentSwap_involutive xs a L1 L2 hL1 hL2 hcN,
      ← segmentSwap_involutive ys a L1 L2 hL1 hL2 hcN, h]

/-! ## Equicardinality of prefixFiber under segment swap

The segment swap is a bijection from `prefixFiber(h, e, s)` to itself
(when the swap happens after the prefix horizon). This is the key to
the excursion ordering uniformity argument. -/

/-- The segment swap is a self-inverse bijection on `Traj k N`. -/
def segmentSwapEquiv {N : ℕ} (a L1 L2 : ℕ)
    (hL1 : 0 < L1) (hL2 : 0 < L2) (hcN : a + L1 + L2 ≤ N) :
    Equiv.Perm (Traj k N) where
  toFun xs := segmentSwap xs a L1 L2 hL1 hL2 hcN
  invFun xs := segmentSwap xs a L2 L1 hL2 hL1 (by omega)
  left_inv xs := segmentSwap_involutive xs a L1 L2 hL1 hL2 hcN
  right_inv xs := segmentSwap_involutive xs a L2 L1 hL2 hL1 (by omega)

/-! ## Return position characterization under segment swap

When the swap region `[a, a+L1+L2]` bounds two excursions (no intermediate
returns), the return positions of `segmentSwap xs` are obtained from those
of `xs` by replacing the midpoint `a+L1` with `a+L2`. -/

/-- In the identity prefix (i ≤ a), segmentSwap preserves return status. -/
lemma segmentSwap_return_prefix {N : ℕ} (xs : Traj k N) (a L1 L2 : ℕ)
    (hL1 : 0 < L1) (hL2 : 0 < L2) (hcN : a + L1 + L2 ≤ N)
    (i : Fin (N + 1)) (hi : (i : ℕ) ≤ a) :
    segmentSwap xs a L1 L2 hL1 hL2 hcN i = xs 0 ↔ xs i = xs 0 := by
  rw [segmentSwap_eq_of_le_a xs a L1 L2 hL1 hL2 hcN i hi]

/-- In the identity suffix (i > a+L1+L2), segmentSwap preserves return status. -/
lemma segmentSwap_return_suffix {N : ℕ} (xs : Traj k N) (a L1 L2 : ℕ)
    (hL1 : 0 < L1) (hL2 : 0 < L2) (hcN : a + L1 + L2 ≤ N)
    (i : Fin (N + 1)) (hi : a + L1 + L2 < (i : ℕ)) :
    segmentSwap xs a L1 L2 hL1 hL2 hcN i = xs 0 ↔ xs i = xs 0 := by
  simp only [segmentSwap]
  split_ifs with h1 h2 h3
  · exact absurd hi (by omega)
  · exact absurd hi (by omega)
  · exact absurd hi (by omega)
  · exact Iff.rfl

/-- Full return position characterization: within the excursion swap range,
the return positions are exactly `{a, a+L2, a+L1+L2}` (replacing old `{a, a+L1, a+L1+L2}`). -/
theorem segmentSwap_return_in_range {N : ℕ} (xs : Traj k N) (a L1 L2 : ℕ)
    (hL1 : 0 < L1) (hL2 : 0 < L2) (hcN : a + L1 + L2 ≤ N)
    (_ha_ret : xs ⟨a, by omega⟩ = xs 0)
    (hb_ret : xs ⟨a + L1, by omega⟩ = xs 0)
    (hc_ret : xs ⟨a + L1 + L2, by omega⟩ = xs 0)
    -- No returns in excursion interiors (quantified over Fin to avoid omega-in-∀ issue)
    (hnoret1 : ∀ (j : Fin (N + 1)), a < j.val → j.val < a + L1 → xs j ≠ xs 0)
    (hnoret2 : ∀ (j : Fin (N + 1)), a + L1 < j.val → j.val < a + L1 + L2 → xs j ≠ xs 0)
    (i : Fin (N + 1)) (hi_lo : a < (i : ℕ)) (hi_hi : (i : ℕ) ≤ a + L1 + L2) :
    segmentSwap xs a L1 L2 hL1 hL2 hcN i = xs 0 ↔
      ((i : ℕ) = a + L2 ∨ (i : ℕ) = a + L1 + L2) := by
  constructor
  · -- Forward: if swapped position returns, must be at a+L2 or a+L1+L2
    intro hret
    simp only [segmentSwap] at hret
    split_ifs at hret with h1 h2
    · omega
    · -- i ≤ a+L2: maps to xs(i+L1). If xs(i+L1) = xs 0, i+L1 must be a return.
      -- No returns in (a+L1, a+L1+L2), so i+L1 = a+L1+L2, giving i = a+L2.
      left
      by_contra hne
      exact hnoret2 ⟨↑i + L1, by omega⟩ (by simp; omega) (by simp; omega)
        (by rwa [show (⟨↑i + L1, _⟩ : Fin (N + 1)) = ⟨↑i + L1, by omega⟩ from rfl])
    · -- a+L2 < i ≤ a+L1+L2: maps to xs(i-L2). i-L2 must be a return.
      -- No returns in (a, a+L1), so i-L2 = a+L1, giving i = a+L1+L2.
      right
      by_contra hne
      exact hnoret1 ⟨↑i - L2, by omega⟩ (by simp; omega) (by simp; omega)
        (by rwa [show (⟨↑i - L2, _⟩ : Fin (N + 1)) = ⟨↑i - L2, by omega⟩ from rfl])
  · -- Backward: if i = a+L2 or i = a+L1+L2, show return
    intro h
    simp only [segmentSwap]
    rcases h with hi_eq | hi_eq
    · -- i.val = a + L2
      split_ifs with h1 h2
      · omega
      · -- maps to xs(i+L1) = xs(a+L1+L2)
        rw [show (⟨↑i + L1, _⟩ : Fin (N + 1)) = ⟨a + L1 + L2, by omega⟩ from
              Fin.ext (by simp; omega)]
        exact hc_ret
      · omega
    · -- i.val = a + L1 + L2
      split_ifs with h1 h2
      · omega
      · omega
      · -- maps to xs(i-L2) = xs(a+L1)
        rw [show (⟨↑i - L2, _⟩ : Fin (N + 1)) = ⟨a + L1, by omega⟩ from
              Fin.ext (by simp; omega)]
        exact hb_ret

/-! ## Segment value correspondence under swap

When segmentSwap is applied at adjacent excursion boundaries (a, a+L1, a+L1+L2),
the segment [a, a+L2] of the swapped trajectory reproduces the values of
the original segment [a+L1, a+L1+L2], and vice versa. -/

/-- In the second block (a < t ≤ a + L2), segmentSwap maps to xs(t + L1). -/
lemma segmentSwap_val_second_block {N : ℕ} (xs : Traj k N) (a L1 L2 : ℕ)
    (hL1 : 0 < L1) (hL2 : 0 < L2) (hcN : a + L1 + L2 ≤ N)
    (t : ℕ) (ht : t < N + 1) (ht_lo : a < t) (ht_hi : t ≤ a + L2) :
    segmentSwap xs a L1 L2 hL1 hL2 hcN ⟨t, ht⟩ = xs ⟨t + L1, by omega⟩ := by
  simp only [segmentSwap]
  split_ifs <;> omega

/-- In the third block (a + L2 < t ≤ a + L1 + L2), segmentSwap maps to xs(t - L2). -/
lemma segmentSwap_val_third_block {N : ℕ} (xs : Traj k N) (a L1 L2 : ℕ)
    (hL1 : 0 < L1) (hL2 : 0 < L2) (hcN : a + L1 + L2 ≤ N)
    (t : ℕ) (ht : t < N + 1) (ht_lo : a + L2 < t) (ht_hi : t ≤ a + L1 + L2) :
    segmentSwap xs a L1 L2 hL1 hL2 hcN ⟨t, ht⟩ = xs ⟨t - L2, by omega⟩ := by
  simp only [segmentSwap]
  split_ifs <;> omega

/-- The swapped trajectory segment [a, a+L2] pointwise matches the original
segment [a+L1, a+L1+L2] (adjacent excursion transposition, forward direction). -/
theorem segmentSwap_excursion_transpose_fwd {N : ℕ} (xs : Traj k N) (a L1 L2 : ℕ)
    (hL1 : 0 < L1) (hL2 : 0 < L2) (hcN : a + L1 + L2 ≤ N)
    (ha_ret : xs ⟨a, by omega⟩ = xs 0)
    (hb_ret : xs ⟨a + L1, by omega⟩ = xs 0)
    (j : ℕ) (hj : j ≤ L2) :
    segmentSwap xs a L1 L2 hL1 hL2 hcN ⟨a + j, by omega⟩ =
      xs ⟨a + L1 + j, by omega⟩ := by
  rcases Nat.eq_zero_or_pos j with rfl | hj_pos
  · -- j = 0: both sides are xs 0 (return positions)
    show segmentSwap xs a L1 L2 hL1 hL2 hcN ⟨a, by omega⟩ = xs ⟨a + L1, by omega⟩
    rw [segmentSwap_eq_of_le_a xs a L1 L2 hL1 hL2 hcN ⟨a, by omega⟩ (by simp)]
    rw [ha_ret, hb_ret]
  · -- j > 0: second block
    rw [segmentSwap_val_second_block xs a L1 L2 hL1 hL2 hcN (a + j) (by omega)
        (by omega) (by omega)]
    congr 1; ext; dsimp only; omega

/-- The swapped trajectory segment [a+L2, a+L1+L2] pointwise matches the original
segment [a, a+L1] (adjacent excursion transposition, backward direction). -/
theorem segmentSwap_excursion_transpose_bwd {N : ℕ} (xs : Traj k N) (a L1 L2 : ℕ)
    (hL1 : 0 < L1) (hL2 : 0 < L2) (hcN : a + L1 + L2 ≤ N)
    (ha_ret : xs ⟨a, by omega⟩ = xs 0)
    (hc_ret : xs ⟨a + L1 + L2, by omega⟩ = xs 0)
    (j : ℕ) (hj : j ≤ L1) :
    segmentSwap xs a L1 L2 hL1 hL2 hcN ⟨a + L2 + j, by omega⟩ =
      xs ⟨a + j, by omega⟩ := by
  rcases Nat.eq_zero_or_pos j with rfl | hj_pos
  · -- j = 0: boundary point (a+L2 is in second block boundary)
    -- segmentSwap(xs, a+L2) = xs(a+L2+L1) = xs(a+L1+L2) = xs 0 = xs(a)
    show segmentSwap xs a L1 L2 hL1 hL2 hcN ⟨a + L2, by omega⟩ = xs ⟨a, by omega⟩
    rw [segmentSwap_val_second_block xs a L1 L2 hL1 hL2 hcN (a + L2) (by omega)
        (by omega) (by omega)]
    have : (⟨a + L2 + L1, by omega⟩ : Fin (N + 1)) = ⟨a + L1 + L2, by omega⟩ :=
      Fin.ext (by dsimp only; omega)
    rw [this, hc_ret, ha_ret]
  · -- j > 0: third block
    rw [segmentSwap_val_third_block xs a L1 L2 hL1 hL2 hcN (a + L2 + j) (by omega)
        (by omega) (by omega)]
    congr 1; ext; dsimp only; omega

/-! ## Return position set under segment swap

The return positions (as a Finset) of the swapped trajectory are obtained from
those of the original by replacing `a + L1` with `a + L2`, preserving cardinality. -/

/-- Full return-position characterization for segmentSwap: `i` is a return position
of `segmentSwap xs` iff `i` is in the "adjusted" return set. -/
theorem segmentSwap_isReturn_iff {N : ℕ} (xs : Traj k N) (a L1 L2 : ℕ)
    (hL1 : 0 < L1) (hL2 : 0 < L2) (hcN : a + L1 + L2 ≤ N)
    (ha_ret : xs ⟨a, by omega⟩ = xs 0)
    (hb_ret : xs ⟨a + L1, by omega⟩ = xs 0)
    (hc_ret : xs ⟨a + L1 + L2, by omega⟩ = xs 0)
    (hnoret1 : ∀ (j : Fin (N + 1)), a < j.val → j.val < a + L1 → xs j ≠ xs 0)
    (hnoret2 : ∀ (j : Fin (N + 1)), a + L1 < j.val → j.val < a + L1 + L2 → xs j ≠ xs 0)
    (i : Fin (N + 1)) :
    segmentSwap xs a L1 L2 hL1 hL2 hcN i = xs 0 ↔
      (((i : ℕ) ≤ a ∧ xs i = xs 0) ∨
       ((i : ℕ) = a + L2) ∨
       ((i : ℕ) = a + L1 + L2) ∨
       (a + L1 + L2 < (i : ℕ) ∧ xs i = xs 0)) := by
  by_cases hi_le : (i : ℕ) ≤ a
  · -- prefix: identity
    rw [segmentSwap_return_prefix xs a L1 L2 hL1 hL2 hcN i hi_le]
    constructor
    · intro h; exact Or.inl ⟨hi_le, h⟩
    · intro h; rcases h with ⟨_, h⟩ | h | h | ⟨h, _⟩ <;> [exact h; omega; omega; omega]
  · by_cases hi_le2 : (i : ℕ) ≤ a + L1 + L2
    · -- swap range: use segmentSwap_return_in_range
      rw [segmentSwap_return_in_range xs a L1 L2 hL1 hL2 hcN
          ha_ret hb_ret hc_ret hnoret1 hnoret2 i (by omega) hi_le2]
      constructor
      · intro h; rcases h with h | h <;> [exact Or.inr (Or.inl h); exact Or.inr (Or.inr (Or.inl h))]
      · intro h
        rcases h with ⟨h, _⟩ | h | h | ⟨h, _⟩ <;> [omega; exact Or.inl h; exact Or.inr h; omega]
    · -- suffix: identity
      rw [segmentSwap_return_suffix xs a L1 L2 hL1 hL2 hcN i (by omega)]
      constructor
      · intro h; exact Or.inr (Or.inr (Or.inr ⟨by omega, h⟩))
      · intro h; rcases h with ⟨h, _⟩ | h | h | ⟨_, h⟩ <;> [omega; omega; omega; exact h]

/-- The return-position Finset cardinality is preserved by segmentSwap
(because the bijection replaces exactly one return position with another). -/
theorem returnPositions_segmentSwap_card {N : ℕ} (xs : Traj k N) (a L1 L2 : ℕ)
    (hL1 : 0 < L1) (hL2 : 0 < L2) (hcN : a + L1 + L2 ≤ N)
    (ha_ret : xs ⟨a, by omega⟩ = xs 0)
    (hb_ret : xs ⟨a + L1, by omega⟩ = xs 0)
    (hc_ret : xs ⟨a + L1 + L2, by omega⟩ = xs 0) :
    (returnPositions (k := k) (segmentSwap xs a L1 L2 hL1 hL2 hcN)).card =
      (returnPositions (k := k) xs).card := by
  -- stateOfTraj determines returnsToStart, which determines return position count
  have hstate := segmentSwap_stateOfTraj xs a L1 L2 hL1 hL2 hcN ha_ret hb_ret hc_ret
  rw [card_returnPositions_eq_returnsToStart_add_one,
      card_returnPositions_eq_returnsToStart_add_one, hstate]

/-- numExcursions is preserved by segmentSwap. -/
theorem numExcursions_segmentSwap {N : ℕ} (xs : Traj k N) (a L1 L2 : ℕ)
    (hL1 : 0 < L1) (hL2 : 0 < L2) (hcN : a + L1 + L2 ≤ N)
    (ha_ret : xs ⟨a, by omega⟩ = xs 0)
    (hb_ret : xs ⟨a + L1, by omega⟩ = xs 0)
    (hc_ret : xs ⟨a + L1 + L2, by omega⟩ = xs 0) :
    numExcursions (k := k) (segmentSwap xs a L1 L2 hL1 hL2 hcN) =
      numExcursions (k := k) xs := by
  unfold numExcursions
  rw [returnPositions_segmentSwap_card xs a L1 L2 hL1 hL2 hcN ha_ret hb_ret hc_ret]

/-! ## trajSegment pointwise characterization

All lemmas use plain ℕ positions to avoid Fin coercion opacity in omega. -/

/-- `trajSegment xs ⟨p, _⟩ ⟨q, _⟩` has length `q - p + 1` when `p ≤ q`. -/
lemma trajSegment_length {N : ℕ} (xs : Traj k N)
    (p q : ℕ) (hp : p < N + 1) (hq : q < N + 1) (hpq : p ≤ q) :
    (trajSegment (k := k) xs ⟨p, hp⟩ ⟨q, hq⟩).length = q - p + 1 := by
  simp only [trajSegment, Nat.min_eq_left hpq, Nat.max_eq_right hpq, trajToList]
  rw [List.length_take, List.length_drop, List.length_ofFn]
  omega

/-- The `t`-th element of `trajSegment xs ⟨p, _⟩ ⟨q, _⟩` (for `p ≤ q`) is `xs(p + t)`. -/
lemma trajSegment_getElem {N : ℕ} (xs : Traj k N)
    (p q : ℕ) (hp : p < N + 1) (hq : q < N + 1) (hpq : p ≤ q) (t : ℕ)
    (ht : t < (trajSegment (k := k) xs ⟨p, hp⟩ ⟨q, hq⟩).length) :
    (trajSegment (k := k) xs ⟨p, hp⟩ ⟨q, hq⟩)[t] = xs ⟨p + t, by
      have := trajSegment_length (k := k) xs p q hp hq hpq; omega⟩ := by
  simp only [trajSegment, Nat.min_eq_left hpq, Nat.max_eq_right hpq, trajToList]
  rw [List.getElem_take, List.getElem_drop, List.getElem_ofFn]

/-- Two `trajSegment`s of the same length are equal iff they agree pointwise. -/
lemma trajSegment_ext {N : ℕ} (xs ys : Traj k N)
    (p₁ q₁ p₂ q₂ : ℕ) (hp₁ : p₁ < N + 1) (hq₁ : q₁ < N + 1)
    (hp₂ : p₂ < N + 1) (hq₂ : q₂ < N + 1)
    (h₁ : p₁ ≤ q₁) (h₂ : p₂ ≤ q₂)
    (hlen : q₁ - p₁ = q₂ - p₂)
    (hpw : ∀ (t : ℕ) (_ht : t ≤ q₁ - p₁),
      xs ⟨p₁ + t, by omega⟩ = ys ⟨p₂ + t, by omega⟩) :
    trajSegment (k := k) xs ⟨p₁, hp₁⟩ ⟨q₁, hq₁⟩ =
      trajSegment (k := k) ys ⟨p₂, hp₂⟩ ⟨q₂, hq₂⟩ := by
  apply List.ext_getElem
  · rw [trajSegment_length _ _ _ _ _ h₁, trajSegment_length _ _ _ _ _ h₂, hlen]
  · intro t ht₁ ht₂
    rw [trajSegment_getElem _ _ _ _ _ h₁, trajSegment_getElem _ _ _ _ _ h₂]
    exact hpw t (by rw [trajSegment_length _ _ _ _ _ h₁] at ht₁; omega)

/-- The forward excursion transposition: segment `[a, a+L2]` of the swapped
trajectory matches segment `[a+L1, a+L1+L2]` of the original. -/
theorem trajSegment_segmentSwap_fwd {N : ℕ} (xs : Traj k N) (a L1 L2 : ℕ)
    (hL1 : 0 < L1) (hL2 : 0 < L2) (hcN : a + L1 + L2 ≤ N)
    (ha_ret : xs ⟨a, by omega⟩ = xs 0)
    (hb_ret : xs ⟨a + L1, by omega⟩ = xs 0) :
    trajSegment (k := k)
      (segmentSwap xs a L1 L2 hL1 hL2 hcN) ⟨a, by omega⟩ ⟨a + L2, by omega⟩ =
    trajSegment (k := k) xs ⟨a + L1, by omega⟩ ⟨a + L1 + L2, by omega⟩ := by
  exact trajSegment_ext _ _ a (a + L2) (a + L1) (a + L1 + L2)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (fun t ht => segmentSwap_excursion_transpose_fwd xs a L1 L2 hL1 hL2 hcN
      ha_ret hb_ret t (by omega))

/-- The backward excursion transposition: segment `[a+L2, a+L1+L2]` of the swapped
trajectory matches segment `[a, a+L1]` of the original. -/
theorem trajSegment_segmentSwap_bwd {N : ℕ} (xs : Traj k N) (a L1 L2 : ℕ)
    (hL1 : 0 < L1) (hL2 : 0 < L2) (hcN : a + L1 + L2 ≤ N)
    (ha_ret : xs ⟨a, by omega⟩ = xs 0)
    (hc_ret : xs ⟨a + L1 + L2, by omega⟩ = xs 0) :
    trajSegment (k := k)
      (segmentSwap xs a L1 L2 hL1 hL2 hcN) ⟨a + L2, by omega⟩ ⟨a + L1 + L2, by omega⟩ =
    trajSegment (k := k) xs ⟨a, by omega⟩ ⟨a + L1, by omega⟩ := by
  exact trajSegment_ext _ _ (a + L2) (a + L1 + L2) a (a + L1)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (fun t ht => segmentSwap_excursion_transpose_bwd xs a L1 L2 hL1 hL2 hcN
      ha_ret hc_ret t (by omega))

/-- Segments outside the swap range are unchanged. -/
theorem trajSegment_segmentSwap_outside {N : ℕ} (xs : Traj k N) (a L1 L2 : ℕ)
    (hL1 : 0 < L1) (hL2 : 0 < L2) (hcN : a + L1 + L2 ≤ N)
    (i j : Fin (N + 1)) (hij : i.val ≤ j.val)
    (hout : j.val ≤ a ∨ a + L1 + L2 < i.val) :
    trajSegment (k := k) (segmentSwap xs a L1 L2 hL1 hL2 hcN) i j =
      trajSegment (k := k) xs i j := by
  exact trajSegment_ext _ _ i.val j.val i.val j.val i.isLt j.isLt i.isLt j.isLt
    hij hij rfl (fun t ht => by
      rcases hout with hle | hge
      · exact segmentSwap_eq_of_le_a' xs a L1 L2 hL1 hL2 hcN (i.val + t) (by omega) (by omega)
      · exact segmentSwap_eq_of_gt_range' xs a L1 L2 hL1 hL2 hcN (i.val + t) (by omega) (by omega))

/-! ## Return position Finset equality under segmentSwap

The return positions of `segmentSwap xs` differ from those of `xs` by
replacing `a + L1` with `a + L2` (when L1 ≠ L2). -/

/-- Characterization: `i` is a return of the swapped trajectory iff
it satisfies the adjusted condition. Wraps `segmentSwap_isReturn_iff`
as a Finset membership statement. -/
theorem mem_returnPositions_segmentSwap {N : ℕ} (xs : Traj k N) (a L1 L2 : ℕ)
    (hL1 : 0 < L1) (hL2 : 0 < L2) (hcN : a + L1 + L2 ≤ N)
    (ha_ret : xs ⟨a, by omega⟩ = xs 0)
    (hb_ret : xs ⟨a + L1, by omega⟩ = xs 0)
    (hc_ret : xs ⟨a + L1 + L2, by omega⟩ = xs 0)
    (hnoret1 : ∀ (j : Fin (N + 1)), a < j.val → j.val < a + L1 → xs j ≠ xs 0)
    (hnoret2 : ∀ (j : Fin (N + 1)), a + L1 < j.val → j.val < a + L1 + L2 → xs j ≠ xs 0)
    (i : Fin (N + 1)) :
    i ∈ returnPositions (k := k) (segmentSwap xs a L1 L2 hL1 hL2 hcN) ↔
      ((i.val ≤ a ∧ xs i = xs 0) ∨
       i.val = a + L2 ∨
       i.val = a + L1 + L2 ∨
       (a + L1 + L2 < i.val ∧ xs i = xs 0)) := by
  simp only [returnPositions, Finset.mem_filter, Finset.mem_univ, true_and]
  have := segmentSwap_isReturn_iff xs a L1 L2 hL1 hL2 hcN
    ha_ret hb_ret hc_ret hnoret1 hnoret2 i
  -- segmentSwap_isReturn_iff uses `segmentSwap ... i = xs 0`
  -- but returnPositions uses `(segmentSwap ...) i = (segmentSwap ...) 0`
  -- Since 0 ≤ a, segmentSwap at 0 = xs 0
  have h0 : segmentSwap xs a L1 L2 hL1 hL2 hcN 0 = xs 0 :=
    segmentSwap_eq_of_le_a' xs a L1 L2 hL1 hL2 hcN 0 (by omega) (by omega)
  rw [h0]
  exact this

/-- The return positions of the swapped trajectory, expressed as a Finset
in terms of the original return positions. Under the excursion swap that
replaces `a + L1` with `a + L2`, the Finset changes by exactly this
one-element replacement. -/
theorem returnPositions_segmentSwap_eq {N : ℕ} (xs : Traj k N) (a L1 L2 : ℕ)
    (hL1 : 0 < L1) (hL2 : 0 < L2) (hcN : a + L1 + L2 ≤ N)
    (ha_ret : xs ⟨a, by omega⟩ = xs 0)
    (hb_ret : xs ⟨a + L1, by omega⟩ = xs 0)
    (hc_ret : xs ⟨a + L1 + L2, by omega⟩ = xs 0)
    (hnoret1 : ∀ (j : Fin (N + 1)), a < j.val → j.val < a + L1 → xs j ≠ xs 0)
    (hnoret2 : ∀ (j : Fin (N + 1)), a + L1 < j.val → j.val < a + L1 + L2 → xs j ≠ xs 0) :
    returnPositions (k := k) (segmentSwap xs a L1 L2 hL1 hL2 hcN) =
      ((returnPositions (k := k) xs).erase ⟨a + L1, by omega⟩) ∪
        {⟨a + L2, by omega⟩} := by
  ext i
  rw [mem_returnPositions_segmentSwap xs a L1 L2 hL1 hL2 hcN
    ha_ret hb_ret hc_ret hnoret1 hnoret2]
  simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton,
    returnPositions, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · -- forward: swapped return → erased ∪ singleton
    intro h
    rcases h with ⟨hle, hret⟩ | hval | hval | ⟨hgt, hret⟩
    · -- prefix case
      left
      refine ⟨?_, hret⟩
      intro heq
      rw [Fin.ext_iff] at heq
      simp at heq
      omega
    · -- i = a + L2
      right
      exact Fin.ext (by simp; exact hval)
    · -- i = a + L1 + L2
      left
      refine ⟨?_, hc_ret ▸ (by congr 1; exact Fin.ext (by simp; exact hval))⟩
      intro heq
      rw [Fin.ext_iff] at heq
      simp at heq
      omega
    · -- suffix case
      left
      refine ⟨?_, hret⟩
      intro heq
      rw [Fin.ext_iff] at heq
      simp at heq
      omega
  · -- backward: erased ∪ singleton → swapped return
    intro h
    rcases h with ⟨hne, hret⟩ | heq
    · -- i ∈ erase: i is an original return, i ≠ a + L1
      have hne_val : i.val ≠ a + L1 := by
        intro h; apply hne; exact Fin.ext (by simp; exact h)
      by_cases h1 : i.val ≤ a
      · exact Or.inl ⟨h1, hret⟩
      · by_cases h2 : i.val < a + L1
        · -- a < i < a + L1: original return → contradiction with hnoret1
          exact absurd hret (hnoret1 i (by omega) h2)
        · by_cases h3 : i.val = a + L1 + L2
          · exact Or.inr (Or.inr (Or.inl h3))
          · by_cases h4 : i.val < a + L1 + L2
            · -- a + L1 < i < a + L1 + L2: contradiction with hnoret2
              exact absurd hret (hnoret2 i (by omega) h4)
            · exact Or.inr (Or.inr (Or.inr ⟨by omega, hret⟩))
    · -- i = ⟨a + L2, _⟩
      have : i.val = a + L2 := by
        rw [heq]
      exact Or.inr (Or.inl this)

/-! ## Consecutive pair characterization

A pair `(a, b)` in a Finset is **consecutive** if `a < b` and no Finset element
lies strictly between them.  This characterizes excursion boundaries without
needing `Finset.sort`. -/

/-- `a` and `b` are consecutive in `S` if `a < b` and no element of `S` lies
strictly between them. -/
def IsConsecutivePair (S : Finset (Fin (N + 1))) (a b : Fin (N + 1)) : Prop :=
  a ∈ S ∧ b ∈ S ∧ a < b ∧ ∀ c ∈ S, ¬(a < c ∧ c < b)

/-- Consecutive return positions appear as adjacent entries in `excursionPairs`. -/
lemma mem_excursionPairs_of_IsConsecutivePair {N : ℕ} (xs : Traj k N)
    {a b : Fin (N + 1)}
    (h : IsConsecutivePair (returnPositions (k := k) xs) a b) :
    (a, b) ∈ excursionPairs (k := k) xs := by
  rcases h with ⟨ha, hb, hab, hgap⟩
  exact mem_excursionPairs_of_return_consecutive (k := k) xs a b ha hb hab hgap

/-- Converse: if `(a, b)` appears in `excursionPairs`, then `a` and `b` are
consecutive in the return positions. -/
lemma IsConsecutivePair_of_mem_excursionPairs {N : ℕ} (xs : Traj k N)
    {a b : Fin (N + 1)}
    (h : (a, b) ∈ excursionPairs (k := k) xs) :
    IsConsecutivePair (returnPositions (k := k) xs) a b := by
  classical
  let l : List (Fin (N + 1)) := returnPositionsList (k := k) xs
  have hs : l.SortedLT := by
    simpa [l, returnPositionsList] using
      (Finset.sortedLT_sort (returnPositions (k := k) xs))
  have hzip : excursionPairs (k := k) xs = l.zip l.tail := by
    simp [excursionPairs, l]
  rw [hzip] at h
  -- Get the index `i` such that `(l[i], l[i+1]) = (a, b)`
  rcases (List.mem_iff_getElem.mp h) with ⟨i, hi_lt, hi_eq⟩
  have hi_zip_len : i < (l.zip l.tail).length := hi_lt
  have hl_len : i + 1 < l.length := by
    have : (l.zip l.tail).length = l.length - 1 := by
      simp [List.length_zip, List.length_tail]
    omega
  have hi_lt_l : i < l.length := by omega
  have ha_eq : a = l[i] := by
    have := congrArg Prod.fst hi_eq
    simp [List.getElem_zip, List.getElem_tail] at this
    exact this.symm
  have hb_eq : b = l[i + 1] := by
    have := congrArg Prod.snd hi_eq
    simp [List.getElem_zip, List.getElem_tail] at this
    exact this.symm
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- a ∈ returnPositions
    rw [ha_eq]
    have haL : l[i] ∈ l := List.getElem_mem hi_lt_l
    simpa [l, returnPositionsList] using
      (Finset.mem_sort (s := returnPositions (k := k) xs) (r := (· ≤ ·))).1 haL
  · -- b ∈ returnPositions
    rw [hb_eq]
    have hbL : l[i + 1] ∈ l := List.getElem_mem hl_len
    simpa [l, returnPositionsList] using
      (Finset.mem_sort (s := returnPositions (k := k) xs) (r := (· ≤ ·))).1 hbL
  · -- a < b
    rw [ha_eq, hb_eq]
    exact (List.SortedLT.getElem_lt_getElem_iff
      (l := l) hs (i := i) (j := i + 1) (hi := hi_lt_l) (hj := hl_len)).2 (by omega)
  · -- No element strictly between a and b
    intro c hc ⟨hac, hcb⟩
    rw [ha_eq] at hac
    rw [hb_eq] at hcb
    have hcL : c ∈ l := by
      simpa [l, returnPositionsList] using
        (Finset.mem_sort (s := returnPositions (k := k) xs) (r := (· ≤ ·))).2 hc
    rcases (List.mem_iff_getElem.mp hcL) with ⟨j, hj_lt, hj_eq⟩
    -- c = l[j], and l[i] < l[j] < l[i+1], so i < j < i+1, contradiction
    have hij : i < j := by
      rw [← hj_eq] at hac
      exact (List.SortedLT.getElem_lt_getElem_iff
        (l := l) hs (i := i) (j := j) (hi := hi_lt_l) (hj := hj_lt)).1 hac
    have hji1 : j < i + 1 := by
      rw [← hj_eq] at hcb
      exact (List.SortedLT.getElem_lt_getElem_iff
        (l := l) hs (i := j) (j := i + 1) (hi := hj_lt) (hj := hl_len)).1 hcb
    omega

/-- No-return hypotheses exactly say that `(a, a+L1)` and `(a+L1, a+L1+L2)` are
consecutive pairs in the return positions. -/
lemma isConsecutivePair_of_excursion_boundary {N : ℕ} (xs : Traj k N) (a L1 L2 : ℕ)
    (hL1 : 0 < L1) (hL2 : 0 < L2) (hcN : a + L1 + L2 ≤ N)
    (ha_ret : xs ⟨a, by omega⟩ = xs 0)
    (hb_ret : xs ⟨a + L1, by omega⟩ = xs 0)
    (hc_ret : xs ⟨a + L1 + L2, by omega⟩ = xs 0)
    (hnoret1 : ∀ (j : Fin (N + 1)), a < j.val → j.val < a + L1 → xs j ≠ xs 0)
    (hnoret2 : ∀ (j : Fin (N + 1)), a + L1 < j.val → j.val < a + L1 + L2 → xs j ≠ xs 0) :
    IsConsecutivePair (returnPositions (k := k) xs)
      ⟨a, by omega⟩ ⟨a + L1, by omega⟩ ∧
    IsConsecutivePair (returnPositions (k := k) xs)
      ⟨a + L1, by omega⟩ ⟨a + L1 + L2, by omega⟩ := by
  constructor
  · refine ⟨?_, ?_, ?_, ?_⟩
    · simp [returnPositions, ha_ret]
    · simp [returnPositions, hb_ret]
    · simp only [Fin.lt_def]; omega
    · intro c hc ⟨hac, hcb⟩
      simp [returnPositions] at hc
      have := hnoret1 c (by exact_mod_cast hac) (by exact_mod_cast hcb)
      exact this hc
  · refine ⟨?_, ?_, ?_, ?_⟩
    · simp [returnPositions, hb_ret]
    · simp [returnPositions, hc_ret]
    · simp only [Fin.lt_def]; omega
    · intro c hc ⟨hbc, hcc⟩
      simp [returnPositions] at hc
      have := hnoret2 c (by exact_mod_cast hbc) (by exact_mod_cast hcc)
      exact this hc

/-- Segment boundaries for an excursion decomposition are members of `excursionPairs`. -/
lemma mem_excursionPairs_of_excursion_boundary {N : ℕ} (xs : Traj k N) (a L1 L2 : ℕ)
    (hL1 : 0 < L1) (hL2 : 0 < L2) (hcN : a + L1 + L2 ≤ N)
    (ha_ret : xs ⟨a, by omega⟩ = xs 0)
    (hb_ret : xs ⟨a + L1, by omega⟩ = xs 0)
    (hc_ret : xs ⟨a + L1 + L2, by omega⟩ = xs 0)
    (hnoret1 : ∀ (j : Fin (N + 1)), a < j.val → j.val < a + L1 → xs j ≠ xs 0)
    (hnoret2 : ∀ (j : Fin (N + 1)), a + L1 < j.val → j.val < a + L1 + L2 → xs j ≠ xs 0) :
    (⟨a, by omega⟩, ⟨a + L1, by omega⟩) ∈ excursionPairs (k := k) xs ∧
    (⟨a + L1, by omega⟩, ⟨a + L1 + L2, by omega⟩) ∈ excursionPairs (k := k) xs := by
  rcases isConsecutivePair_of_excursion_boundary (k := k) xs a L1 L2 hL1 hL2 hcN
      ha_ret hb_ret hc_ret hnoret1 hnoret2 with ⟨h1, h2⟩
  exact ⟨mem_excursionPairs_of_IsConsecutivePair (k := k) xs h1,
    mem_excursionPairs_of_IsConsecutivePair (k := k) xs h2⟩

/-- After segment swap, `(a, a+L2)` and `(a+L2, a+L1+L2)` are consecutive in the
new return positions. -/
lemma isConsecutivePair_swap {N : ℕ} (xs : Traj k N) (a L1 L2 : ℕ)
    (hL1 : 0 < L1) (hL2 : 0 < L2) (hcN : a + L1 + L2 ≤ N)
    (ha_ret : xs ⟨a, by omega⟩ = xs 0)
    (hb_ret : xs ⟨a + L1, by omega⟩ = xs 0)
    (hc_ret : xs ⟨a + L1 + L2, by omega⟩ = xs 0)
    (hnoret1 : ∀ (j : Fin (N + 1)), a < j.val → j.val < a + L1 → xs j ≠ xs 0)
    (hnoret2 : ∀ (j : Fin (N + 1)), a + L1 < j.val → j.val < a + L1 + L2 → xs j ≠ xs 0) :
    let xs' := segmentSwap xs a L1 L2 hL1 hL2 hcN
    IsConsecutivePair (returnPositions (k := k) xs')
      ⟨a, by omega⟩ ⟨a + L2, by omega⟩ ∧
    IsConsecutivePair (returnPositions (k := k) xs')
      ⟨a + L2, by omega⟩ ⟨a + L1 + L2, by omega⟩ := by
  intro xs'
  -- Membership characterization for return positions of the swapped trajectory
  have hmem : ∀ i, i ∈ returnPositions (k := k) xs' ↔
      ((i.val ≤ a ∧ xs i = xs 0) ∨
       i.val = a + L2 ∨
       i.val = a + L1 + L2 ∨
       (a + L1 + L2 < i.val ∧ xs i = xs 0)) :=
    mem_returnPositions_segmentSwap xs a L1 L2 hL1 hL2 hcN
      ha_ret hb_ret hc_ret hnoret1 hnoret2
  constructor
  · refine ⟨?_, ?_, ?_, ?_⟩
    · -- a ∈ returnPositions xs'
      exact (hmem _).mpr (Or.inl ⟨Nat.le_refl a, ha_ret⟩)
    · -- a+L2 ∈ returnPositions xs'
      exact (hmem _).mpr (Or.inr (Or.inl rfl))
    · -- a < a+L2
      simp only [Fin.lt_def]; omega
    · -- No return of xs' strictly between a and a+L2
      intro c hc ⟨hac, hcL2⟩
      have hac' : a < c.val := by exact_mod_cast hac
      have hcL2' : c.val < a + L2 := by exact_mod_cast hcL2
      rcases (hmem c).mp hc with ⟨hle, _⟩ | heq | heq | ⟨hgt, _⟩ <;> omega
  · refine ⟨?_, ?_, ?_, ?_⟩
    · -- a+L2 ∈ returnPositions xs'
      exact (hmem _).mpr (Or.inr (Or.inl rfl))
    · -- a+L1+L2 ∈ returnPositions xs'
      exact (hmem _).mpr (Or.inr (Or.inr (Or.inl rfl)))
    · -- a+L2 < a+L1+L2
      simp only [Fin.lt_def]; omega
    · -- No return of xs' strictly between a+L2 and a+L1+L2
      intro c hc ⟨hL2c, hcC⟩
      have hL2c' : a + L2 < c.val := by exact_mod_cast hL2c
      have hcC' : c.val < a + L1 + L2 := by exact_mod_cast hcC
      rcases (hmem c).mp hc with ⟨hle, _⟩ | heq | heq | ⟨hgt, _⟩ <;> omega

/-- Swapped segment boundaries are members of `excursionPairs` for the swapped trajectory. -/
lemma mem_excursionPairs_swap {N : ℕ} (xs : Traj k N) (a L1 L2 : ℕ)
    (hL1 : 0 < L1) (hL2 : 0 < L2) (hcN : a + L1 + L2 ≤ N)
    (ha_ret : xs ⟨a, by omega⟩ = xs 0)
    (hb_ret : xs ⟨a + L1, by omega⟩ = xs 0)
    (hc_ret : xs ⟨a + L1 + L2, by omega⟩ = xs 0)
    (hnoret1 : ∀ (j : Fin (N + 1)), a < j.val → j.val < a + L1 → xs j ≠ xs 0)
    (hnoret2 : ∀ (j : Fin (N + 1)), a + L1 < j.val → j.val < a + L1 + L2 → xs j ≠ xs 0) :
    let xs' := segmentSwap xs a L1 L2 hL1 hL2 hcN
    (⟨a, by omega⟩, ⟨a + L2, by omega⟩) ∈ excursionPairs (k := k) xs' ∧
    (⟨a + L2, by omega⟩, ⟨a + L1 + L2, by omega⟩) ∈ excursionPairs (k := k) xs' := by
  intro xs'
  rcases isConsecutivePair_swap (k := k) xs a L1 L2 hL1 hL2 hcN
      ha_ret hb_ret hc_ret hnoret1 hnoret2 with ⟨h1, h2⟩
  exact ⟨mem_excursionPairs_of_IsConsecutivePair (k := k) xs' h1,
    mem_excursionPairs_of_IsConsecutivePair (k := k) xs' h2⟩

-- The following generic list lemmas and the main excursionPairs transformation
-- lemma are placed in MarkovDeFinettiHardBEST.lean (which imports this file)
-- to avoid the Finset.cons namespace interference with List.cons.inj.
lemma mem_excursionsOfTraj_of_mem_excursionPairs {N : ℕ} (xs : Traj k N)
    {p : Fin (N + 1) × Fin (N + 1)} (hp : p ∈ excursionPairs (k := k) xs) :
    trajSegment (k := k) xs p.1 p.2 ∈ excursionsOfTraj (k := k) xs := by
  unfold excursionsOfTraj
  exact List.mem_map.mpr ⟨p, hp, rfl⟩

lemma swapped_middle_excursions_mem_excursionsOfTraj {N : ℕ}
    (xs : Traj k N) (a L1 L2 : ℕ)
    (hL1 : 0 < L1) (hL2 : 0 < L2) (hcN : a + L1 + L2 ≤ N)
    (ha_ret : xs ⟨a, by omega⟩ = xs 0)
    (hb_ret : xs ⟨a + L1, by omega⟩ = xs 0)
    (hc_ret : xs ⟨a + L1 + L2, by omega⟩ = xs 0)
    (hnoret1 : ∀ (j : Fin (N + 1)), a < j.val → j.val < a + L1 → xs j ≠ xs 0)
    (hnoret2 : ∀ (j : Fin (N + 1)), a + L1 < j.val → j.val < a + L1 + L2 → xs j ≠ xs 0) :
    let xs' := segmentSwap xs a L1 L2 hL1 hL2 hcN
    trajSegment (k := k) xs ⟨a + L1, by omega⟩ ⟨a + L1 + L2, by omega⟩ ∈
      excursionsOfTraj (k := k) xs' ∧
    trajSegment (k := k) xs ⟨a, by omega⟩ ⟨a + L1, by omega⟩ ∈
      excursionsOfTraj (k := k) xs' := by
  intro xs'
  rcases mem_excursionPairs_swap (k := k) xs a L1 L2 hL1 hL2 hcN
      ha_ret hb_ret hc_ret hnoret1 hnoret2 with ⟨hpair1, hpair2⟩
  constructor
  · have hmem :
      trajSegment (k := k) xs' ⟨a, by omega⟩ ⟨a + L2, by omega⟩ ∈
        excursionsOfTraj (k := k) xs' :=
      mem_excursionsOfTraj_of_mem_excursionPairs (k := k) xs' hpair1
    have hseg :
        trajSegment (k := k) xs' ⟨a, by omega⟩ ⟨a + L2, by omega⟩ =
          trajSegment (k := k) xs ⟨a + L1, by omega⟩ ⟨a + L1 + L2, by omega⟩ :=
      trajSegment_segmentSwap_fwd (k := k) xs a L1 L2 hL1 hL2 hcN ha_ret hb_ret
    exact hseg ▸ hmem
  · have hmem :
      trajSegment (k := k) xs' ⟨a + L2, by omega⟩ ⟨a + L1 + L2, by omega⟩ ∈
        excursionsOfTraj (k := k) xs' :=
      mem_excursionsOfTraj_of_mem_excursionPairs (k := k) xs' hpair2
    have hseg :
        trajSegment (k := k) xs' ⟨a + L2, by omega⟩ ⟨a + L1 + L2, by omega⟩ =
          trajSegment (k := k) xs ⟨a, by omega⟩ ⟨a + L1, by omega⟩ :=
      trajSegment_segmentSwap_bwd (k := k) xs a L1 L2 hL1 hL2 hcN ha_ret hc_ret
    exact hseg ▸ hmem

/-! ## Ordered-list adjacent-transposition bridge (decomposition form)

These lemmas provide an exact ordered-list statement for `excursionListOfTraj`
once the corresponding `excursionPairs` decomposition is available.
-/

/-- If `excursionPairs` of the swapped trajectory has the same prefix/suffix pair
blocks with the middle pair transposed, and mapped prefix/suffix segments are
preserved, then `excursionListOfTraj` is exactly the same transposition on the
middle two excursions. -/
lemma excursionListOfTraj_segmentSwap_eq_of_excursionPairs_decomp
    {N : ℕ} (xs : Traj k N) (a L1 L2 : ℕ)
    (hL1 : 0 < L1) (hL2 : 0 < L2) (hcN : a + L1 + L2 ≤ N)
    (pre suf : List (Fin (N + 1) × Fin (N + 1)))
    (hPairsNew :
      excursionPairs (k := k) (segmentSwap xs a L1 L2 hL1 hL2 hcN) =
        pre ++
          [(⟨a, by omega⟩, ⟨a + L2, by omega⟩),
           (⟨a + L2, by omega⟩, ⟨a + L1 + L2, by omega⟩)] ++
          suf)
    (hPre :
      pre.map
          (fun p =>
            trajSegment (k := k)
              (segmentSwap xs a L1 L2 hL1 hL2 hcN) p.1 p.2) =
        pre.map (fun p => trajSegment (k := k) xs p.1 p.2))
    (hSuf :
      suf.map
          (fun p =>
            trajSegment (k := k)
              (segmentSwap xs a L1 L2 hL1 hL2 hcN) p.1 p.2) =
        suf.map (fun p => trajSegment (k := k) xs p.1 p.2))
    (ha_ret : xs ⟨a, by omega⟩ = xs 0)
    (hb_ret : xs ⟨a + L1, by omega⟩ = xs 0)
    (hc_ret : xs ⟨a + L1 + L2, by omega⟩ = xs 0) :
    excursionListOfTraj (k := k) (segmentSwap xs a L1 L2 hL1 hL2 hcN) =
      pre.map (fun p => trajSegment (k := k) xs p.1 p.2) ++
        [trajSegment (k := k) xs ⟨a + L1, by omega⟩ ⟨a + L1 + L2, by omega⟩,
         trajSegment (k := k) xs ⟨a, by omega⟩ ⟨a + L1, by omega⟩] ++
        suf.map (fun p => trajSegment (k := k) xs p.1 p.2) := by
  unfold excursionListOfTraj excursionsOfTraj
  rw [hPairsNew, List.map_append, List.map_append]
  simp only [List.map_cons, List.map_nil]
  rw [hPre, hSuf]
  simp only [List.append_assoc]
  have hmid1 :
      trajSegment (k := k) (segmentSwap xs a L1 L2 hL1 hL2 hcN)
          ⟨a, by omega⟩ ⟨a + L2, by omega⟩ =
        trajSegment (k := k) xs
          ⟨a + L1, by omega⟩ ⟨a + L1 + L2, by omega⟩ :=
    trajSegment_segmentSwap_fwd (k := k) xs a L1 L2 hL1 hL2 hcN ha_ret hb_ret
  have hmid2 :
      trajSegment (k := k) (segmentSwap xs a L1 L2 hL1 hL2 hcN)
          ⟨a + L2, by omega⟩ ⟨a + L1 + L2, by omega⟩ =
        trajSegment (k := k) xs
          ⟨a, by omega⟩ ⟨a + L1, by omega⟩ :=
    trajSegment_segmentSwap_bwd (k := k) xs a L1 L2 hL1 hL2 hcN ha_ret hc_ret
  simp [hmid1, hmid2]

/-- Adjacent-transposition form relative to the original excursion list.

Assuming `excursionPairs xs = pre ++ [(a,a+L1),(a+L1,a+L1+L2)] ++ suf` and the
corresponding swapped-pairs decomposition for `segmentSwap xs`, this yields an
exact ordered-list transposition in `excursionListOfTraj`. -/
lemma excursionListOfTraj_segmentSwap_eq_swap_middle_of_excursionPairs_decomp
    {N : ℕ} (xs : Traj k N) (a L1 L2 : ℕ)
    (hL1 : 0 < L1) (hL2 : 0 < L2) (hcN : a + L1 + L2 ≤ N)
    (pre suf : List (Fin (N + 1) × Fin (N + 1)))
    (_hPairsOld :
      excursionPairs (k := k) xs =
        pre ++
          [(⟨a, by omega⟩, ⟨a + L1, by omega⟩),
           (⟨a + L1, by omega⟩, ⟨a + L1 + L2, by omega⟩)] ++
          suf)
    (hPairsNew :
      excursionPairs (k := k) (segmentSwap xs a L1 L2 hL1 hL2 hcN) =
        pre ++
          [(⟨a, by omega⟩, ⟨a + L2, by omega⟩),
           (⟨a + L2, by omega⟩, ⟨a + L1 + L2, by omega⟩)] ++
          suf)
    (hPre :
      pre.map
          (fun p =>
            trajSegment (k := k)
              (segmentSwap xs a L1 L2 hL1 hL2 hcN) p.1 p.2) =
        pre.map (fun p => trajSegment (k := k) xs p.1 p.2))
    (hSuf :
      suf.map
          (fun p =>
            trajSegment (k := k)
              (segmentSwap xs a L1 L2 hL1 hL2 hcN) p.1 p.2) =
        suf.map (fun p => trajSegment (k := k) xs p.1 p.2))
    (ha_ret : xs ⟨a, by omega⟩ = xs 0)
    (hb_ret : xs ⟨a + L1, by omega⟩ = xs 0)
    (hc_ret : xs ⟨a + L1 + L2, by omega⟩ = xs 0) :
    excursionListOfTraj (k := k) (segmentSwap xs a L1 L2 hL1 hL2 hcN) =
      let e1 := trajSegment (k := k) xs ⟨a, by omega⟩ ⟨a + L1, by omega⟩
      let e2 := trajSegment (k := k) xs ⟨a + L1, by omega⟩ ⟨a + L1 + L2, by omega⟩
      (pre.map (fun p => trajSegment (k := k) xs p.1 p.2)) ++ [e2, e1] ++
        (suf.map (fun p => trajSegment (k := k) xs p.1 p.2)) := by
  have hnew :=
    excursionListOfTraj_segmentSwap_eq_of_excursionPairs_decomp
      (k := k) (xs := xs) (a := a) (L1 := L1) (L2 := L2)
      hL1 hL2 hcN pre suf hPairsNew hPre hSuf ha_ret hb_ret hc_ret
  simpa [List.append_assoc] using hnew

/-- Stronger ordered-list adjacent-swap bridge.

This variant exposes the result directly as a swap in a caller-provided
excursion-list decomposition `preSeg ++ [e1, e2] ++ sufSeg`.
-/
lemma excursionListOfTraj_segmentSwap_eq_swap_middle_of_excursionPairs_decomp_strong
    {N : ℕ} (xs : Traj k N) (a L1 L2 : ℕ)
    (hL1 : 0 < L1) (hL2 : 0 < L2) (hcN : a + L1 + L2 ≤ N)
    (pre suf : List (Fin (N + 1) × Fin (N + 1)))
    (preSeg sufSeg : ExcursionList k) (e1 e2 : ExcursionType k)
    (hPairsOld :
      excursionPairs (k := k) xs =
        pre ++
          [(⟨a, by omega⟩, ⟨a + L1, by omega⟩),
           (⟨a + L1, by omega⟩, ⟨a + L1 + L2, by omega⟩)] ++
          suf)
    (hPairsNew :
      excursionPairs (k := k) (segmentSwap xs a L1 L2 hL1 hL2 hcN) =
        pre ++
          [(⟨a, by omega⟩, ⟨a + L2, by omega⟩),
           (⟨a + L2, by omega⟩, ⟨a + L1 + L2, by omega⟩)] ++
          suf)
    (hPre :
      pre.map
          (fun p =>
            trajSegment (k := k)
              (segmentSwap xs a L1 L2 hL1 hL2 hcN) p.1 p.2) =
        pre.map (fun p => trajSegment (k := k) xs p.1 p.2))
    (hSuf :
      suf.map
          (fun p =>
            trajSegment (k := k)
              (segmentSwap xs a L1 L2 hL1 hL2 hcN) p.1 p.2) =
        suf.map (fun p => trajSegment (k := k) xs p.1 p.2))
    (ha_ret : xs ⟨a, by omega⟩ = xs 0)
    (hb_ret : xs ⟨a + L1, by omega⟩ = xs 0)
    (hc_ret : xs ⟨a + L1 + L2, by omega⟩ = xs 0)
    (hOld :
      excursionListOfTraj (k := k) xs = preSeg ++ [e1, e2] ++ sufSeg)
    (hPreSeg :
      preSeg = pre.map (fun p => trajSegment (k := k) xs p.1 p.2))
    (hSufSeg :
      sufSeg = suf.map (fun p => trajSegment (k := k) xs p.1 p.2))
    (hE1 :
      e1 = trajSegment (k := k) xs ⟨a, by omega⟩ ⟨a + L1, by omega⟩)
    (hE2 :
      e2 = trajSegment (k := k) xs ⟨a + L1, by omega⟩ ⟨a + L1 + L2, by omega⟩) :
    excursionListOfTraj (k := k) (segmentSwap xs a L1 L2 hL1 hL2 hcN) =
      preSeg ++ [e2, e1] ++ sufSeg := by
  have hswap :=
    excursionListOfTraj_segmentSwap_eq_swap_middle_of_excursionPairs_decomp
      (k := k) (xs := xs) (a := a) (L1 := L1) (L2 := L2)
      hL1 hL2 hcN pre suf hPairsOld hPairsNew hPre hSuf ha_ret hb_ret hc_ret
  have hswap' :
      excursionListOfTraj (k := k) (segmentSwap xs a L1 L2 hL1 hL2 hcN) =
        (pre.map (fun p => trajSegment (k := k) xs p.1 p.2)) ++
          [trajSegment (k := k) xs ⟨a + L1, by omega⟩ ⟨a + L1 + L2, by omega⟩,
           trajSegment (k := k) xs ⟨a, by omega⟩ ⟨a + L1, by omega⟩] ++
          (suf.map (fun p => trajSegment (k := k) xs p.1 p.2)) := by
    simpa [List.append_assoc] using hswap
  -- rewrite to caller's names
  have _hOld_use := hOld
  simpa [hOld, hPreSeg, hSufSeg, hE1, hE2, List.append_assoc] using hswap'

/-- Under the adjacent-excursion transposition decomposition hypotheses, the
excursion multiset is preserved by `segmentSwap`. -/
lemma excursionMultiset_segmentSwap_eq_swap_middle_of_excursionPairs_decomp_strong
    {N : ℕ} (xs : Traj k N) (a L1 L2 : ℕ)
    (hL1 : 0 < L1) (hL2 : 0 < L2) (hcN : a + L1 + L2 ≤ N)
    (pre suf : List (Fin (N + 1) × Fin (N + 1)))
    (preSeg sufSeg : ExcursionList k) (e1 e2 : ExcursionType k)
    (hPairsOld :
      excursionPairs (k := k) xs =
        pre ++
          [(⟨a, by omega⟩, ⟨a + L1, by omega⟩),
           (⟨a + L1, by omega⟩, ⟨a + L1 + L2, by omega⟩)] ++
          suf)
    (hPairsNew :
      excursionPairs (k := k) (segmentSwap xs a L1 L2 hL1 hL2 hcN) =
        pre ++
          [(⟨a, by omega⟩, ⟨a + L2, by omega⟩),
           (⟨a + L2, by omega⟩, ⟨a + L1 + L2, by omega⟩)] ++
          suf)
    (hPre :
      pre.map
          (fun p =>
            trajSegment (k := k)
              (segmentSwap xs a L1 L2 hL1 hL2 hcN) p.1 p.2) =
        pre.map (fun p => trajSegment (k := k) xs p.1 p.2))
    (hSuf :
      suf.map
          (fun p =>
            trajSegment (k := k)
              (segmentSwap xs a L1 L2 hL1 hL2 hcN) p.1 p.2) =
        suf.map (fun p => trajSegment (k := k) xs p.1 p.2))
    (ha_ret : xs ⟨a, by omega⟩ = xs 0)
    (hb_ret : xs ⟨a + L1, by omega⟩ = xs 0)
    (hc_ret : xs ⟨a + L1 + L2, by omega⟩ = xs 0)
    (hOld :
      excursionListOfTraj (k := k) xs = preSeg ++ [e1, e2] ++ sufSeg)
    (hPreSeg :
      preSeg = pre.map (fun p => trajSegment (k := k) xs p.1 p.2))
    (hSufSeg :
      sufSeg = suf.map (fun p => trajSegment (k := k) xs p.1 p.2))
    (hE1 :
      e1 = trajSegment (k := k) xs ⟨a, by omega⟩ ⟨a + L1, by omega⟩)
    (hE2 :
      e2 = trajSegment (k := k) xs ⟨a + L1, by omega⟩ ⟨a + L1 + L2, by omega⟩) :
    excursionMultiset (k := k)
        (excursionListOfTraj (k := k) (segmentSwap xs a L1 L2 hL1 hL2 hcN)) =
      excursionMultiset (k := k) (excursionListOfTraj (k := k) xs) := by
  have hswap :
      excursionListOfTraj (k := k) (segmentSwap xs a L1 L2 hL1 hL2 hcN) =
        preSeg ++ [e2, e1] ++ sufSeg :=
    excursionListOfTraj_segmentSwap_eq_swap_middle_of_excursionPairs_decomp_strong
      (k := k) (xs := xs) (a := a) (L1 := L1) (L2 := L2)
      hL1 hL2 hcN pre suf preSeg sufSeg e1 e2
      hPairsOld hPairsNew hPre hSuf ha_ret hb_ret hc_ret
      hOld hPreSeg hSufSeg hE1 hE2
  rw [hswap, hOld]
  have hmid : [e2, e1].Perm [e1, e2] := by
    simpa using (List.Perm.swap e2 e1 []).symm
  have hperm :
      (preSeg ++ [e2, e1] ++ sufSeg).Perm (preSeg ++ [e1, e2] ++ sufSeg) := by
    exact (List.Perm.append_left _ hmid).append_right _
  simpa [excursionMultiset] using hperm

/-! ## Ordered-list bridge lemmas -/

/-- If the segment swap starts strictly after the prefix horizon, the prefix
excursion list is unchanged. This is the ordered-list form used to build
`prefixPatternFiber` transport maps. -/
lemma excursionListOfTraj_prefix_segmentSwap_eq_of_prefix_before_swap
    {n N : ℕ} (hN : Nat.succ n ≤ N)
    (xs : Traj k N) (a L1 L2 : ℕ) (hna : Nat.succ n ≤ a)
    (hL1 : 0 < L1) (hL2 : 0 < L2) (hcN : a + L1 + L2 ≤ N) :
    excursionListOfTraj (k := k)
      (trajPrefix (k := k) hN (segmentSwap xs a L1 L2 hL1 hL2 hcN)) =
    excursionListOfTraj (k := k) (trajPrefix (k := k) hN xs) := by
  have hprefix :
      trajPrefix (k := k) hN (segmentSwap xs a L1 L2 hL1 hL2 hcN) =
        trajPrefix (k := k) hN xs :=
    trajPrefix_segmentSwap_eq_of_prefix_before_swap
      (k := k) (h := hN) (xs := xs) (a := a) (L1 := L1) (L2 := L2)
      (hna := hna) (hL1 := hL1) (hL2 := hL2) (hcN := hcN)
  simp [hprefix]

end MarkovDeFinettiHardExcursionBridge

end Mettapedia.Logic
