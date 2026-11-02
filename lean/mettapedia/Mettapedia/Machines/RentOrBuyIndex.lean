import Mathlib.Tactic

/-!
# Reverse probes of a relation kept by its first column: rent, then buy

A binary relation kept by its first column (one row of second-column numbers per
first-column number) answers a probe that binds only the second column by reading
every row: a *rent* of `rent` steps per probe.  An index by the second column
answers such a probe in `use` steps (its answers), at most a row scan, but
building it costs `buy` steps once, and keeping it costs memory.

Always scanning costs `k * rent` for `k` probes, which leaves the best choice
behind without bound as `k` grows.  The rule here rents while the rents paid stay
below the price of the index, then buys: the deterministic rule for renting or
buying, which pays at most twice the best choice made knowing `k` in advance,
plus one rent.  A program that rarely probes this way never pays for the index.

This file models the rule as the procedure it is, a state of rents paid and
whether the index was bought, and proves:
* `run_cost`: its cost is `k * rent` while `k` is at most the rentals `m` it
  makes, and `m * rent + buy + (k - m) * use` after;
* `run_competitive`: that is at most `2 * min (k * rent) (buy + k * use) + rent`,
  where `min (k * rent) (buy + k * use)` is the best cost of any choice of
  when to buy;
* `best_le` and `scanAlways_gap`: no choice costs less than that minimum, and
  always scanning costs `k * (rent - use) - buy` more than buying first.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.RentOrBuyIndex

/-- The prices: a scanning probe costs `rent` (at least one step), building the
index costs `buy`, a probe through the index costs `use`, at most a scan. -/
structure Prices where
  rent : Nat
  buy : Nat
  use : Nat
  rent_pos : 0 < rent
  use_le : use ≤ rent

/-- The rule's state: rents paid so far, and whether the index is bought. -/
structure St where
  spent : Nat
  bought : Bool

/-- One probe: through the index once bought; buying first once the rents paid
reach the price; scanning otherwise. -/
def step (p : Prices) (s : St) : St × Nat :=
  if s.bought then (s, p.use)
  else if p.buy ≤ s.spent then (⟨s.spent, true⟩, p.buy + p.use)
  else (⟨s.spent + p.rent, false⟩, p.rent)

/-- `k` probes from the start: the state and the cost. -/
def run (p : Prices) : Nat → St × Nat
  | 0 => (⟨0, false⟩, 0)
  | k + 1 =>
    let r := run p k
    let s := step p r.1
    (s.1, r.2 + s.2)

/-- The rentals the rule makes: the fewest whose rents reach the price. -/
def rentals (p : Prices) : Nat :=
  Nat.find (⟨p.buy, by nlinarith [p.rent_pos]⟩ : ∃ m, p.buy ≤ m * p.rent)

theorem rentals_spec (p : Prices) : p.buy ≤ rentals p * p.rent :=
  Nat.find_spec (⟨p.buy, by nlinarith [p.rent_pos]⟩ : ∃ m, p.buy ≤ m * p.rent)

theorem rentals_min (p : Prices) : rentals p * p.rent < p.buy + p.rent := by
  rcases Nat.eq_zero_or_pos (rentals p) with h | h
  · rw [h]; simp; exact Or.inr p.rent_pos
  · have hlt : rentals p - 1 < rentals p := by omega
    have hnot := Nat.find_min
      (⟨p.buy, by nlinarith [p.rent_pos]⟩ : ∃ m, p.buy ≤ m * p.rent) hlt
    push Not at hnot
    have heq : rentals p * p.rent = (rentals p - 1) * p.rent + p.rent := by
      rw [← Nat.succ_mul]; congr 1; unfold rentals at h ⊢; omega
    unfold rentals at heq hnot ⊢
    omega

/-- The rule's states and cost, probe by probe. -/
theorem run_state (p : Prices) (k : Nat) :
    (k ≤ rentals p → (run p k).1 = ⟨k * p.rent, false⟩ ∧ (run p k).2 = k * p.rent) ∧
      (rentals p < k → (run p k).1.bought = true ∧
        (run p k).2 = rentals p * p.rent + p.buy + (k - rentals p) * p.use) := by
  induction k with
  | zero => exact ⟨fun _ => ⟨by simp [run], by simp [run]⟩, fun h => absurd h (by omega)⟩
  | succ k ih =>
    obtain ⟨ih1, ih2⟩ := ih
    refine ⟨fun hk => ?_, fun hk => ?_⟩
    · -- Still renting: before the rentals are done, the rents paid stay below the price.
      obtain ⟨hs, hc⟩ := ih1 (by omega)
      have hbelow : ¬ p.buy ≤ k * p.rent := by
        intro hle
        have := Nat.find_min'
          (⟨p.buy, by nlinarith [p.rent_pos]⟩ : ∃ m, p.buy ≤ m * p.rent) hle
        unfold rentals at hk; omega
      simp only [run, hs, hc, step, Bool.false_eq_true, if_false, if_neg hbelow]
      constructor
      · simp [Nat.succ_mul]
      · simp [Nat.succ_mul]
    · rcases Nat.lt_or_ge (rentals p) k with hlt | hge
      · -- Bought already.
        obtain ⟨hb, hc⟩ := ih2 hlt
        simp only [run, step, hb, if_true]
        refine ⟨trivial, ?_⟩
        rw [hc]
        have : k + 1 - rentals p = (k - rentals p) + 1 := by omega
        rw [this, Nat.add_mul, one_mul]; ring
      · -- This probe buys: the rents paid have just reached the price.
        have hk' : k = rentals p := by omega
        obtain ⟨hs, hc⟩ := ih1 (by omega)
        have hreach : p.buy ≤ k * p.rent := hk' ▸ rentals_spec p
        simp only [run, hs, hc, step, Bool.false_eq_true, if_false, if_pos hreach]
        refine ⟨trivial, ?_⟩
        rw [hk']
        have : rentals p + 1 - rentals p = 1 := by omega
        rw [this]; ring

theorem run_cost (p : Prices) (k : Nat) :
    (run p k).2 = if k ≤ rentals p then k * p.rent
      else rentals p * p.rent + p.buy + (k - rentals p) * p.use := by
  split
  · exact ((run_state p k).1 ‹_›).2
  · exact ((run_state p k).2 (by omega)).2

/-- Buying before probe `j` (or never, `j = k`): `j` rents, then the price and
`k - j` uses. -/
def buyAt (p : Prices) (k j : Nat) : Nat :=
  if j < k then j * p.rent + p.buy + (k - j) * p.use else k * p.rent

/-- No choice of when to buy costs less than `min (k * rent) (buy + k * use)`. -/
theorem best_le (p : Prices) (k j : Nat) :
    min (k * p.rent) (p.buy + k * p.use) ≤ buyAt p k j := by
  unfold buyAt
  split
  · rename_i hj
    have h1 : j * p.use ≤ j * p.rent := Nat.mul_le_mul_left j p.use_le
    have h2 : k * p.use = j * p.use + (k - j) * p.use := by
      rw [← Nat.add_mul]; congr 1; omega
    refine le_trans (min_le_right _ _) ?_
    omega
  · exact min_le_left _ _

/-- The rule pays at most twice the best choice, plus one rent. -/
theorem run_competitive (p : Prices) (k : Nat) :
    (run p k).2 ≤ 2 * min (k * p.rent) (p.buy + k * p.use) + p.rent := by
  rw [run_cost]
  have hspec := rentals_spec p
  have hmin := rentals_min p
  set m := rentals p
  split
  · rename_i hk
    have hkm : k * p.rent ≤ m * p.rent := Nat.mul_le_mul_right p.rent hk
    rcases le_total (k * p.rent) (p.buy + k * p.use) with h | h
    · rw [min_eq_left h]; omega
    · rw [min_eq_right h]; omega
  · rename_i hk
    have hk' : m ≤ k := by omega
    have hu : (k - m) * p.use ≤ (k - m) * p.rent := Nat.mul_le_mul_left _ p.use_le
    have hsplit : k * p.rent = m * p.rent + (k - m) * p.rent := by
      rw [← Nat.add_mul]; congr 1; omega
    have hsplit' : k * p.use = m * p.use + (k - m) * p.use := by
      rw [← Nat.add_mul]; congr 1; omega
    rcases le_total (k * p.rent) (p.buy + k * p.use) with h | h
    · rw [min_eq_left h]; omega
    · rw [min_eq_right h]; omega

/-- Always scanning. -/
def scanAlways (p : Prices) (k : Nat) : Nat := k * p.rent

/-- Always scanning costs `k * (rent - use)` more than buying first, less the
price: a gap that grows without bound with the probes. -/
theorem scanAlways_gap (p : Prices) (k : Nat) :
    scanAlways p k + p.buy = (p.buy + k * p.use) + k * (p.rent - p.use) := by
  unfold scanAlways
  have : k * p.rent = k * p.use + k * (p.rent - p.use) := by
    rw [← Nat.mul_add]; congr 1; have := p.use_le; omega
  omega

end Mettapedia.Machines.RentOrBuyIndex
