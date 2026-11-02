import Mathlib

/-!
# Indexes bought on demand: rent or buy

A store answers a run of queries over a relation either by scanning it, at a
cost of `r` a query, or by building an index once, at a cost of `B`, after which
a query costs nothing more.  How many queries will come is not known in advance.
The policy that scans `k` times and builds before the next query costs `q * r`
over a run of `q ≤ k` queries and `k * r + B` over a longer one, while the
cheapest choice made in hindsight costs `min (q * r) B`.

* `rentOrBuy_le_opt_add` : the policy exceeds the hindsight optimum by at most
  `max (k * r) B`, whatever its allowance `k`;
* `rentOrBuy_le_two_mul_opt` : when the allowance matches the build,
  `k * r ≤ B ≤ (k + 1) * r`, it costs at most twice the hindsight optimum,
  however many queries come;
* `two_mul_opt_le_rentOrBuy_add` : no allowance does better by more than one
  scan: the run that stops at the first query after the build makes any such
  policy pay twice the optimum, less one scan.

Scans need not cost the same: a lookup through an index reads the rows its
key's posting holds, which vary with the key.  The policy then builds once the
rows its lookups have paid reach the build:

* `rentOrBuyVar_le_two_mul_opt_add` : it costs at most twice the hindsight
  optimum, plus the one scan that carried its payments past the build.
-/

namespace Mettapedia.InformationTheory.RelationStoreFloors

/-- The cost of scanning `k` times and then building, over a run of `q`
queries. -/
def rentOrBuy (r B k q : ℕ) : ℕ := if q ≤ k then q * r else k * r + B

/-- The hindsight optimum over a run of `q` queries: scan every one, or build
before the first. -/
def rentOrBuyOpt (r B q : ℕ) : ℕ := min (q * r) B

/-- Whatever its allowance, the policy exceeds the hindsight optimum by at most
the larger of its scans and the build. -/
theorem rentOrBuy_le_opt_add (r B k q : ℕ) :
    rentOrBuy r B k q ≤ rentOrBuyOpt r B q + max (k * r) B := by
  unfold rentOrBuy rentOrBuyOpt
  have hscans := le_max_left (k * r) B
  have hbuild := le_max_right (k * r) B
  split_ifs with hq
  · have h : q * r ≤ k * r := Nat.mul_le_mul_right r hq
    rcases le_total (q * r) B with hqB | hqB
    · rw [min_eq_left hqB]
      omega
    · rw [min_eq_right hqB]
      omega
  · have h : k * r ≤ q * r := Nat.mul_le_mul_right r (Nat.le_of_lt (not_le.mp hq))
    rcases le_total (q * r) B with hqB | hqB
    · rw [min_eq_left hqB]
      omega
    · rw [min_eq_right hqB]
      omega

/-- With an allowance that matches the build, `k * r ≤ B ≤ (k + 1) * r`, the
policy costs at most twice the hindsight optimum, however many queries come. -/
theorem rentOrBuy_le_two_mul_opt {r B k : ℕ} (hlow : k * r ≤ B)
    (hhigh : B ≤ (k + 1) * r) (q : ℕ) :
    rentOrBuy r B k q ≤ 2 * rentOrBuyOpt r B q := by
  unfold rentOrBuy rentOrBuyOpt
  split_ifs with hq
  · have h : q * r ≤ k * r := Nat.mul_le_mul_right r hq
    rw [min_eq_left (h.trans hlow)]
    omega
  · have h : (k + 1) * r ≤ q * r := Nat.mul_le_mul_right r (not_le.mp hq)
    rw [min_eq_right (hhigh.trans h)]
    omega

/-- The run that stops at the first query after the build makes any allowance
`j` pay twice the hindsight optimum, less one scan. -/
theorem two_mul_opt_le_rentOrBuy_add (r B j : ℕ) :
    2 * rentOrBuyOpt r B (j + 1) ≤ rentOrBuy r B j (j + 1) + r := by
  unfold rentOrBuy rentOrBuyOpt
  rw [if_neg (by omega)]
  have hscan := min_le_left ((j + 1) * r) B
  have hbuild := min_le_right ((j + 1) * r) B
  have hexpand : (j + 1) * r = j * r + r := by ring
  omega

/-- Four scans, then a build costing four scans: at the fifth query the policy
has paid twice the optimum. -/
example : rentOrBuy 1 4 4 5 = 8 ∧ rentOrBuyOpt 1 4 5 = 4 := by decide

/-! ### Scans of varying cost -/

/-- The rows the first `t` lookups read, the `i`-th reading `c i`. -/
def paid (c : ℕ → ℕ) (t : ℕ) : ℕ := ∑ i ∈ Finset.range t, c i

/-- The cost over a run of `q` lookups of building once the rows paid reach the
build `B`: the lookups up to the one whose rows reach it, and the build; or
every lookup, when their rows never reach it. -/
def rentOrBuyVar (c : ℕ → ℕ) (B q : ℕ) : ℕ :=
  if h : B ≤ paid c q then paid c (Nat.find (⟨q, h⟩ : ∃ t, B ≤ paid c t)) + B
  else paid c q

/-- Building once the rows paid reach the build costs at most twice the
hindsight optimum, `min (paid c q) B`, plus the largest single scan: the one
that carried the payments past the build. -/
theorem rentOrBuyVar_le_two_mul_opt_add (c : ℕ → ℕ) (B q m : ℕ)
    (hm : ∀ i < q, c i ≤ m) :
    rentOrBuyVar c B q ≤ 2 * min (paid c q) B + m := by
  unfold rentOrBuyVar
  split_ifs with h
  · have hspec : B ≤ paid c (Nat.find (⟨q, h⟩ : ∃ t, B ≤ paid c t)) :=
      Nat.find_spec (⟨q, h⟩ : ∃ t, B ≤ paid c t)
    have hle : Nat.find (⟨q, h⟩ : ∃ t, B ≤ paid c t) ≤ q :=
      Nat.find_min' (⟨q, h⟩ : ∃ t, B ≤ paid c t) h
    rw [min_eq_right h]
    rcases Nat.eq_zero_or_pos (Nat.find (⟨q, h⟩ : ∃ t, B ≤ paid c t)) with h0 | hpos
    · rw [h0] at hspec ⊢
      simp [paid] at hspec ⊢
      omega
    · obtain ⟨s, hs⟩ : ∃ s, Nat.find (⟨q, h⟩ : ∃ t, B ≤ paid c t) = s + 1 :=
        ⟨_ - 1, (Nat.succ_pred_eq_of_pos hpos).symm⟩
      have hlt : ¬ B ≤ paid c s :=
        Nat.find_min (⟨q, h⟩ : ∃ t, B ≤ paid c t) (by omega)
      have hstep : paid c (s + 1) = paid c s + c s := Finset.sum_range_succ _ _
      have hcs : c s ≤ m := hm s (by omega)
      rw [hs, hstep]
      omega
  · rw [min_eq_left (by omega)]
    omega

/-- Scans of one row and a build of four: the fourth lookup's row reaches the
build, and the run of six lookups pays eight against an optimum of four. -/
example : rentOrBuyVar (fun _ => 1) 4 6 = 8 ∧ min (paid (fun _ => 1) 6) 4 = 4 := by
  have hp : ∀ t, paid (fun _ => 1) t = t := fun t => by simp [paid]
  refine ⟨?_, by rw [hp]; rfl⟩
  have h : 4 ≤ paid (fun _ => 1) 6 := by rw [hp]; norm_num
  rw [rentOrBuyVar, dif_pos h]
  have hfind : Nat.find (⟨6, h⟩ : ∃ t, 4 ≤ paid (fun _ => 1) t) = 4 := by
    rw [Nat.find_eq_iff]
    exact ⟨by rw [hp], fun n hn => by rw [hp]; omega⟩
  rw [hfind, hp]

end Mettapedia.InformationTheory.RelationStoreFloors
