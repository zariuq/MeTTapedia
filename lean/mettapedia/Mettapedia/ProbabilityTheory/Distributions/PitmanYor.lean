import Mettapedia.ProbabilityTheory.Distributions.BetaBernoulliHorizon

/-!
# The two-parameter Chinese restaurant process

Customers arrive one at a time. When `n` customers sit at `K` tables of sizes `s₁, …, s_K`, the
next one joins table `j` with probability `(s_j - d) / (n + θ)` and opens a new table with
probability `(θ + K d) / (n + θ)`; the first customer opens a table. For `0 ≤ d ≤ 1` and `-d < θ`
this is a probability distribution on the next customer's choices.

A seating sequence that leaves `K` tables of sizes `s₁, …, s_K`, `n` customers in all, has
probability `∏_{k=1}^{K-1} (θ + k d) / (θ + 1)^(n-1 rising) · ∏_j (1 - d)^(s_j - 1 rising)`
(`seatProb_eq`), the exchangeable partition probability function of Pitman (1995). It depends on
the multiset of table sizes only (`seatProb_eq_eppf`): seating sequences that leave the same table
sizes, in any order, have the same probability (`seatProb_eq_of_tables`). Seating one more customer
multiplies it by the probability of that customer's choice (`eppf_seat_new`, `eppf_seat_join`), and
summing over the choices gives it back (`eppf_seat_new_add_sum_join`). These identities hold for
all real `d` and `θ`.

With dishes on the tables, drawn from a base distribution, the probability that the next draw is a
given dish is a martingale (`DishState.pred_martingale`), so the dish's expected number of draws
among the next `M` is `M` times that probability (`DishState.expectedUses_eq`).
-/

namespace Mettapedia.ProbabilityTheory
namespace PitmanYor

open BetaBernoulliPrior (rising)

private theorem rising_zero (x : ℝ) : rising x 0 = 1 := Finset.prod_range_zero _

private theorem rising_succ_right (x : ℝ) (n : ℕ) : rising x (n + 1) = rising x n * (x + n) :=
  Finset.prod_range_succ _ _

/-- Changing one entry of a list multiplies the product of an image of the list by `a` when it
multiplies the image of that entry by `a`. -/
@[to_additive /-- Changing one entry of a list adds `a` to the sum of an image of the list when it
adds `a` to the image of that entry. -/]
theorem prod_map_modify {α M : Type*} [CommMonoid M] (g : α → M) (f : α → α) {s : List α}
    {j : ℕ} (hj : j < s.length) {a : M} (h : g (f s[j]) = g s[j] * a) :
    ((s.modify j f).map g).prod = (s.map g).prod * a := by
  conv_rhs => rw [← List.take_append_drop j s, List.drop_eq_getElem_cons hj]
  rw [List.modify_eq_take_cons_drop hj]
  simp only [List.map_append, List.map_cons, List.prod_append, List.prod_cons, h]
  rw [mul_right_comm (g s[j]), ← mul_assoc]

/-- Joining a table adds one customer. -/
theorem sum_modify_add_one {s : List ℕ} {j : ℕ} (hj : j < s.length) :
    (s.modify j (· + 1)).sum = s.sum + 1 := by
  simpa using sum_map_modify id (· + 1) hj (a := 1) rfl

/-! ## The seating process -/

/-- A customer's choice: open a new table, or join the open table with index `j`, counting from `0`
in the order the tables were opened. -/
inductive Seat
  | new
  | join (j : ℕ)
  deriving DecidableEq

/-- The table sizes after one more customer is seated. -/
def seat (s : List ℕ) : Seat → List ℕ
  | .new => s ++ [1]
  | .join j => s.modify j (· + 1)

/-- The table sizes after customers making the choices `l` arrive at tables of sizes `s`. -/
def tablesFrom (s : List ℕ) (l : List Seat) : List ℕ := l.foldl seat s

/-- The table sizes a seating sequence leaves, in the order the tables were opened. -/
def tables (l : List Seat) : List ℕ := tablesFrom [] l

@[simp] theorem tablesFrom_nil (s : List ℕ) : tablesFrom s [] = s := rfl

@[simp] theorem tablesFrom_cons (s : List ℕ) (c : Seat) (l : List Seat) :
    tablesFrom s (c :: l) = tablesFrom (seat s c) l := rfl

/-- The choices `l`, made by customers arriving at tables of sizes `s`, join only open tables:
a customer who joins table `j` finds more than `j` tables open. -/
def ValidFrom (s : List ℕ) (l : List Seat) : Prop :=
  ∀ l₁ j l₂, l = l₁ ++ .join j :: l₂ → j < (tablesFrom s l₁).length

/-- A seating sequence: every customer who joins a table joins one already open. -/
def Valid (l : List Seat) : Prop := ValidFrom [] l

@[simp] theorem validFrom_nil (s : List ℕ) : ValidFrom s [] := by
  intro l₁ j l₂ h
  simp at h

@[simp] theorem validFrom_new {s : List ℕ} {l : List Seat} :
    ValidFrom s (.new :: l) ↔ ValidFrom (s ++ [1]) l := by
  constructor
  · intro h l₁ j l₂ hl
    simpa [seat] using h (.new :: l₁) j l₂ (by simp [hl])
  · intro h l₁ j l₂ hl
    cases l₁ with
    | nil => simp at hl
    | cons c l₁ =>
      simp only [List.cons_append, List.cons.injEq] at hl
      obtain ⟨rfl, rfl⟩ := hl
      simpa [seat] using h l₁ j l₂ rfl

@[simp] theorem validFrom_join {s : List ℕ} {j : ℕ} {l : List Seat} :
    ValidFrom s (.join j :: l) ↔ j < s.length ∧ ValidFrom (s.modify j (· + 1)) l := by
  constructor
  · intro h
    refine ⟨by simpa using h [] j l rfl, fun l₁ i l₂ hl => ?_⟩
    simpa [seat] using h (.join j :: l₁) i l₂ (by simp [hl])
  · rintro ⟨hj, h⟩ l₁ i l₂ hl
    cases l₁ with
    | nil =>
      simp only [List.nil_append, List.cons.injEq, Seat.join.injEq] at hl
      obtain ⟨rfl, -⟩ := hl
      simpa using hj
    | cons c l₁ =>
      simp only [List.cons_append, List.cons.injEq] at hl
      obtain ⟨rfl, rfl⟩ := hl
      simpa [seat] using h l₁ i l₂ rfl

/-- Every open table has a customer. -/
theorem pos_of_mem_seat {s : List ℕ} (hs : ∀ m ∈ s, 0 < m) (c : Seat) :
    ∀ m ∈ seat s c, 0 < m := by
  intro m hm
  cases c with
  | new =>
    rcases List.mem_append.1 hm with h | h
    · exact hs m h
    · rw [List.mem_singleton.1 h]
      exact Nat.one_pos
  | join j =>
    simp only [seat, List.modify_eq_set] at hm
    rcases List.mem_or_eq_of_mem_set hm with h | rfl
    · exact hs m h
    · omega

/-- The probability of the next customer's choice at tables of sizes `s`, `n` customers at `K`
tables: join table `j` with probability `(s_j - d) / (n + θ)`, open a new table with probability
`(θ + K d) / (n + θ)`. The first customer opens a table; no customer joins a table not open. -/
noncomputable def predictive (d θ : ℝ) (s : List ℕ) : Seat → ℝ
  | .new => if s = [] then 1 else (θ + s.length * d) / (s.sum + θ)
  | .join j => if h : j < s.length then (s[j] - d) / (s.sum + θ) else 0

/-- The probability that customers arriving at tables of sizes `s` make the choices `l`, each
choice drawn from the predictive given the customers before. -/
noncomputable def seatProbFrom (d θ : ℝ) : List ℕ → List Seat → ℝ
  | _, [] => 1
  | s, c :: l => predictive d θ s c * seatProbFrom d θ (seat s c) l

/-- The probability of a seating sequence: the product of the probabilities of its choices, each
given the customers before. -/
noncomputable def seatProb (d θ : ℝ) (l : List Seat) : ℝ := seatProbFrom d θ [] l

/-! ## The exchangeable partition probability function -/

/-- The exchangeable partition probability function at the multiset `s` of table sizes, `K`
tables and `n` customers:
`∏_{k=1}^{K-1} (θ + k d) / (θ + 1)^(n-1 rising) · ∏_j (1 - d)^(s_j - 1 rising)`. -/
noncomputable def eppf (d θ : ℝ) (s : Multiset ℕ) : ℝ :=
  (∏ k ∈ Finset.Ico 1 (Multiset.card s), (θ + k * d)) / rising (θ + 1) (s.sum - 1) *
    (s.map fun m => rising (1 - d) (m - 1)).prod

variable {d θ : ℝ}

theorem eppf_coe (s : List ℕ) :
    eppf d θ s = (∏ k ∈ Finset.Ico 1 s.length, (θ + k * d)) / rising (θ + 1) (s.sum - 1) *
      (s.map fun m => rising (1 - d) (m - 1)).prod := by
  simp only [eppf, Multiset.coe_card, Multiset.sum_coe, Multiset.map_coe, Multiset.prod_coe]

theorem eppf_zero : eppf d θ 0 = 1 := by
  simp [eppf, rising_zero]

/-- Opening a new table multiplies the EPPF by the probability of opening it. -/
theorem eppf_seat_new {s : List ℕ} (hs : ∀ m ∈ s, 0 < m) :
    eppf d θ (seat s .new) = eppf d θ s * predictive d θ s .new := by
  rw [eppf_coe, eppf_coe]
  rcases s with _ | ⟨x, s⟩
  · simp [seat, predictive, rising_zero]
  · obtain ⟨n, hn⟩ : ∃ n, (x :: s).sum = n + 1 :=
      ⟨(x :: s).sum - 1, by have := hs x List.mem_cons_self; simp only [List.sum_cons]; omega⟩
    simp only [seat, predictive, List.length_append, List.length_singleton, List.sum_append,
      List.sum_singleton, hn, List.map_append, List.map_singleton, List.prod_append,
      List.prod_singleton, reduceCtorEq, if_false, Nat.add_sub_cancel, Nat.sub_self, rising_zero,
      mul_one]
    rw [Finset.prod_Ico_succ_top (by simp), rising_succ_right]
    push_cast
    simp only [div_eq_mul_inv, mul_inv]
    ring

/-- Joining an open table multiplies the EPPF by the probability of joining it. -/
theorem eppf_seat_join {s : List ℕ} (hs : ∀ m ∈ s, 0 < m) {j : ℕ} (hj : j < s.length) :
    eppf d θ (seat s (.join j)) = eppf d θ s * predictive d θ s (.join j) := by
  have hmem : s[j] ∈ s := List.getElem_mem hj
  obtain ⟨t, ht⟩ : ∃ t, s[j] = t + 1 := ⟨s[j] - 1, by have := hs _ hmem; omega⟩
  obtain ⟨n, hn⟩ : ∃ n, s.sum = n + 1 :=
    ⟨s.sum - 1, by have := hs _ hmem; have := List.le_sum_of_mem hmem; omega⟩
  have hprod : ((s.modify j (· + 1)).map fun m => rising (1 - d) (m - 1)).prod =
      (s.map fun m => rising (1 - d) (m - 1)).prod * (s[j] - d) := by
    apply prod_map_modify _ _ hj
    simp only [ht, Nat.add_sub_cancel, rising_succ_right]
    push_cast
    ring
  rw [eppf_coe, eppf_coe]
  simp only [seat, predictive, dif_pos hj, List.length_modify, sum_modify_add_one hj, hprod, hn,
    Nat.add_sub_cancel, rising_succ_right]
  push_cast
  simp only [div_eq_mul_inv, mul_inv]
  ring

/-- Customers arriving at tables of sizes `s` multiply the EPPF by the probability of their
choices. -/
theorem eppf_tablesFrom {s : List ℕ} (hs : ∀ m ∈ s, 0 < m) {l : List Seat}
    (hl : ValidFrom s l) :
    eppf d θ (tablesFrom s l) = eppf d θ s * seatProbFrom d θ s l := by
  induction l generalizing s with
  | nil => simp [seatProbFrom]
  | cons c l ih =>
    cases c with
    | new =>
      rw [validFrom_new] at hl
      rw [tablesFrom_cons, ih (pos_of_mem_seat hs .new) hl, eppf_seat_new hs, seatProbFrom,
        mul_assoc]
    | join j =>
      rw [validFrom_join] at hl
      rw [tablesFrom_cons, ih (pos_of_mem_seat hs (.join j)) hl.2, eppf_seat_join hs hl.1,
        seatProbFrom, mul_assoc]

/-- The probability of a seating sequence is the EPPF of the table sizes it leaves: it depends on
the multiset of table sizes only. -/
theorem seatProb_eq_eppf {l : List Seat} (hl : Valid l) :
    seatProb d θ l = eppf d θ (tables l) := by
  rw [tables, eppf_tablesFrom (by simp) hl, Multiset.coe_nil, eppf_zero, one_mul, seatProb]

/-- **Closed form** (Pitman 1995). A seating sequence that leaves `K` tables of sizes
`s₁, …, s_K`, `n` customers in all, has probability
`∏_{k=1}^{K-1} (θ + k d) / (θ + 1)^(n-1 rising) · ∏_j (1 - d)^(s_j - 1 rising)`. -/
theorem seatProb_eq {l : List Seat} (hl : Valid l) :
    seatProb d θ l =
      (∏ k ∈ Finset.Ico 1 (tables l).length, (θ + k * d)) / rising (θ + 1) ((tables l).sum - 1) *
        ((tables l).map fun m => rising (1 - d) (m - 1)).prod := by
  rw [seatProb_eq_eppf hl, eppf_coe]

/-- **Exchangeability.** Two seating sequences that leave the same multiset of table sizes, whatever
the order of the tables, have the same probability. -/
theorem seatProb_eq_of_tables {l₁ l₂ : List Seat} (h₁ : Valid l₁) (h₂ : Valid l₂)
    (h : (tables l₁ : Multiset ℕ) = tables l₂) : seatProb d θ l₁ = seatProb d θ l₂ := by
  rw [seatProb_eq_eppf h₁, seatProb_eq_eppf h₂, h]

/-- A sequence in which some customer joins a table not open has probability zero. -/
theorem seatProbFrom_eq_zero {s : List ℕ} {l : List Seat} (hl : ¬ ValidFrom s l) :
    seatProbFrom d θ s l = 0 := by
  induction l generalizing s with
  | nil => exact absurd (validFrom_nil s) hl
  | cons c l ih =>
    cases c with
    | new =>
      rw [validFrom_new] at hl
      rw [seatProbFrom, ih (s := seat s .new) hl, mul_zero]
    | join j =>
      rw [validFrom_join, not_and_or] at hl
      rw [seatProbFrom]
      rcases hl with hj | hl
      · rw [predictive, dif_neg hj, zero_mul]
      · rw [ih (s := seat s (.join j)) hl, mul_zero]

theorem seatProb_eq_zero {l : List Seat} (hl : ¬ Valid l) : seatProb d θ l = 0 :=
  seatProbFrom_eq_zero hl

/-! ## The predictive is a probability distribution -/

/-- The probabilities of opening a table and of joining each open table sum to one. -/
theorem predictive_new_add_sum_join {s : List ℕ} (h : s ≠ [] → (s.sum : ℝ) + θ ≠ 0) :
    predictive d θ s .new + ∑ j : Fin s.length, predictive d θ s (.join j) = 1 := by
  rcases eq_or_ne s [] with rfl | hs
  · simp [predictive]
  · have hsum : ∑ j : Fin s.length, (s[j.1] : ℝ) = s.sum := by
      rw [Fin.sum_univ_fun_getElem s (fun m : ℕ => (m : ℝ)), Nat.cast_list_sum]
    simp only [predictive, if_neg hs, Fin.is_lt, dif_pos]
    rw [← Finset.sum_div, ← add_div, div_eq_one_iff_eq (h hs), Finset.sum_sub_distrib,
      hsum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring

/-- For `0 ≤ d ≤ 1` and `-d < θ`, every choice has nonnegative probability. -/
theorem predictive_nonneg (hd₀ : 0 ≤ d) (hd₁ : d ≤ 1) (hθ : -d < θ) {s : List ℕ}
    (hs : ∀ m ∈ s, 0 < m) (c : Seat) : 0 ≤ predictive d θ s c := by
  rcases eq_or_ne s [] with rfl | hne
  · cases c <;> simp [predictive]
  · obtain ⟨x, s', rfl⟩ := List.exists_cons_of_ne_nil hne
    have hx : (1 : ℝ) ≤ x := by exact_mod_cast hs x List.mem_cons_self
    have hden : 0 < ((x :: s').sum : ℝ) + θ := by
      have : (x : ℝ) ≤ ((x :: s').sum : ℝ) := by
        exact_mod_cast List.le_sum_of_mem List.mem_cons_self
      linarith
    cases c with
    | new =>
      simp only [predictive, if_neg hne]
      refine div_nonneg ?_ hden.le
      have : (1 : ℝ) ≤ ((x :: s').length : ℝ) := by simp
      nlinarith
    | join j =>
      simp only [predictive]
      split_ifs with hj
      · refine div_nonneg ?_ hden.le
        have : (1 : ℝ) ≤ (x :: s')[j] := by exact_mod_cast hs _ (List.getElem_mem hj)
        linarith
      · exact le_rfl

/-- **Addition rule.** Summed over the choices of one more customer, the EPPF gives back the EPPF
before that customer arrives. -/
theorem eppf_seat_new_add_sum_join {s : List ℕ} (hs : ∀ m ∈ s, 0 < m)
    (h : s ≠ [] → (s.sum : ℝ) + θ ≠ 0) :
    eppf d θ (seat s .new) + ∑ j : Fin s.length, eppf d θ (seat s (.join j)) = eppf d θ s := by
  rw [eppf_seat_new hs, Finset.sum_congr rfl fun j _ => eppf_seat_join hs j.isLt,
    ← Finset.mul_sum, ← mul_add, predictive_new_add_sum_join h, mul_one]

/-! ## Examples -/


/-! ## One dish over a horizon

Tables carry dishes: a new table's dish is drawn from a base distribution that gives the dish `F`
probability `p`. Toward `F`, the restaurant is the mass `a = n_F - d t_F` of `F`'s tables, the mass
`b` of the other tables, and the number of tables `T`; the next draw is `F` with probability
`(a + (θ + d T) p) / (a + b + θ + d T)` (`DishState.pred`). Each of a draw's four outcomes (join a
table of `F`, open one, join another table, open another) adds one to the denominator, and the
probability that the next draw is `F` is a martingale (`DishState.pred_martingale`), so the expected
number of draws of `F` among the next `M` is `M` times it (`DishState.expectedUses_eq`). -/

/-- One dish against the rest of the restaurant. -/
structure DishState where
  /-- the mass of the dish's tables, `n_F - d t_F` -/
  a : ℝ
  /-- the mass of the other tables -/
  b : ℝ
  /-- the number of tables -/
  T : ℕ

namespace DishState

/-- The outcomes of a draw: join a table of the dish, open a table of it, join another table, open
a table of another dish. -/
inductive Draw
  | joinDish
  | newDish
  | joinOther
  | newOther

variable (d θ p : ℝ)

/-- The weight of a new table, `θ + d T`. -/
def newWeight (s : DishState) : ℝ := θ + d * s.T

/-- The normalizer, `n + θ`. -/
def total (s : DishState) : ℝ := s.a + s.b + newWeight d θ s

/-- The probability that the next draw is the dish. -/
noncomputable def pred (s : DishState) : ℝ := (s.a + newWeight d θ s * p) / total d θ s

/-- The weight of each outcome. -/
def weight (s : DishState) : Draw → ℝ
  | .joinDish => s.a
  | .newDish => newWeight d θ s * p
  | .joinOther => s.b
  | .newOther => newWeight d θ s * (1 - p)

/-- The state after each outcome. -/
def next (s : DishState) : Draw → DishState
  | .joinDish => ⟨s.a + 1, s.b, s.T⟩
  | .newDish => ⟨s.a + 1 - d, s.b, s.T + 1⟩
  | .joinOther => ⟨s.a, s.b + 1, s.T⟩
  | .newOther => ⟨s.a, s.b + 1 - d, s.T + 1⟩

/-- `1` for a draw of the dish, `0` otherwise. -/
def isDish : Draw → ℝ
  | .joinDish => 1
  | .newDish => 1
  | .joinOther => 0
  | .newOther => 0

/-- The expectation of a function of the next draw's outcome. -/
noncomputable def expect (s : DishState) (f : Draw → ℝ) : ℝ :=
  (weight d θ p s .joinDish * f .joinDish + weight d θ p s .newDish * f .newDish +
    weight d θ p s .joinOther * f .joinOther + weight d θ p s .newOther * f .newOther) /
    total d θ s

/-- The expected number of draws of the dish among the next `M`. -/
noncomputable def expectedUses : ℕ → DishState → ℝ
  | 0, _ => 0
  | M + 1, s => expect d θ p s fun k => isDish k + expectedUses M (next d s k)

/-- Every outcome adds one to the normalizer. -/
theorem total_next (s : DishState) (k : Draw) : total d θ (next d s k) = total d θ s + 1 := by
  cases k <;> simp only [total, next, newWeight] <;> push_cast <;> ring

/-- The outcome's probabilities add up to one. -/
theorem expect_one (s : DishState) (h : total d θ s ≠ 0) : expect d θ p s (fun _ => 1) = 1 := by
  rw [expect, div_eq_one_iff_eq h]
  simp only [weight, total, newWeight]
  ring

/-- The expectation is linear. -/
theorem expect_add_mul (s : DishState) (f g : Draw → ℝ) (c : ℝ) :
    expect d θ p s (fun k => f k + c * g k) = expect d θ p s f + c * expect d θ p s g := by
  simp only [expect]
  ring

/-- The probability that the next draw is the dish is the expectation of `isDish`. -/
theorem expect_isDish (s : DishState) : expect d θ p s isDish = pred d θ p s := by
  simp only [expect, isDish, weight, pred]
  ring

/-- The probability that the next draw is the dish is a martingale: its expectation after the
draw is its value before. -/
theorem pred_martingale (s : DishState) (h : total d θ s ≠ 0) (h1 : total d θ s + 1 ≠ 0) :
    expect d θ p s (fun k => pred d θ p (next d s k)) = pred d θ p s := by
  have hn : ∀ k, pred d θ p (next d s k) =
      ((next d s k).a + newWeight d θ (next d s k) * p) / (total d θ s + 1) := fun k => by
    rw [pred, total_next]
  simp only [expect, hn]
  rw [pred, div_eq_div_iff h h]
  field_simp
  simp only [weight, next, newWeight, total]
  push_cast
  ring

/-- The expected number of draws of the dish among the next `M` is `M` times the probability that
the next draw is the dish. -/
theorem expectedUses_eq (M : ℕ) (s : DishState) (h : 0 < total d θ s) :
    expectedUses d θ p M s = M * pred d θ p s := by
  induction M generalizing s with
  | zero => simp [expectedUses]
  | succ M ih =>
    have hn : ∀ k, expectedUses d θ p M (next d s k) = M * pred d θ p (next d s k) := fun k =>
      ih _ (by rw [total_next]; linarith)
    simp only [expectedUses, hn]
    rw [expect_add_mul, expect_isDish, pred_martingale d θ p s h.ne' (by linarith)]
    push_cast
    ring

/-- With `d = 1/2`, `θ = 1` and a dish the base gives probability `1/2`, at one table of mass `1`
against mass `1` elsewhere and two tables: the next draw is the dish with probability `1/2`, and
two draws contain it once on average, computed from the outcomes themselves. -/
example : pred (1 / 2) 1 (1 / 2) ⟨1, 1, 2⟩ = 1 / 2 ∧
    expectedUses (1 / 2) 1 (1 / 2) 2 ⟨1, 1, 2⟩ = 1 := by
  refine ⟨?_, ?_⟩ <;>
    norm_num [pred, expectedUses, expect, weight, next, isDish, total, newWeight]

/-- Counting only the dish's tables misses the draws of it from new tables: `a / (n + θ)` is `1/4`
where the probability is `1/2`. -/
example : (1 : ℝ) / total (1 / 2) 1 ⟨1, 1, 2⟩ ≠ pred (1 / 2) 1 (1 / 2) ⟨1, 1, 2⟩ := by
  norm_num [pred, total, newWeight]

end DishState

/-- Three customers: open a table, join it, open a second; or open two tables and join the
second. Both leave a table of two and a table of one. -/
example : tables [.new, .join 0, .new] = [2, 1] ∧ tables [.new, .new, .join 1] = [1, 2] :=
  ⟨rfl, rfl⟩

/-- With `d = 1/2` and `θ = 1` both have probability `1/8`, the closed form at sizes `{2, 1}`. -/
example : seatProb (1 / 2) 1 [.new, .join 0, .new] = 1 / 8 ∧
    seatProb (1 / 2) 1 [.new, .new, .join 1] = 1 / 8 ∧ eppf (1 / 2) 1 {2, 1} = 1 / 8 := by
  refine ⟨?_, ?_, ?_⟩
  · norm_num [seatProb, seatProbFrom, predictive, seat]
  · norm_num [seatProb, seatProbFrom, predictive, seat]
  · norm_num [eppf, rising, Finset.prod_range_succ]

/-- The same equality for all `d` and `θ`, from exchangeability. -/
example (d θ : ℝ) : seatProb d θ [.new, .join 0, .new] = seatProb d θ [.new, .new, .join 1] :=
  seatProb_eq_of_tables (by simp [Valid]) (by simp [Valid]) (by decide)

/-- Not all seatings are equally likely: with `d = 1/2` and `θ = 1`, three tables of one have
probability `1/2`, not `1/8`. -/
example : seatProb (1 / 2) 1 [.new, .new, .new] = 1 / 2 ∧
    seatProb (1 / 2) 1 [.new, .new, .new] ≠ seatProb (1 / 2) 1 [.new, .join 0, .new] := by
  refine ⟨?_, ?_⟩ <;> simp [seatProb, seatProbFrom, predictive, seat] <;> norm_num

/-- With `d = 0` and `θ = 1`, one table of three has probability `1/3`, a table of two and a table
of one `1/6`. -/
example : seatProb 0 1 [.new, .join 0, .join 0] = 1 / 3 ∧
    seatProb 0 1 [.new, .join 0, .new] = 1 / 6 := by
  refine ⟨?_, ?_⟩ <;> norm_num [seatProb, seatProbFrom, predictive, seat]

/-- Equal probability does not mean equal table sizes: with `d = 1/2` and `θ = 1` one table of
three also has probability `1/8`. -/
example : seatProb (1 / 2) 1 [.new, .join 0, .join 0] =
      seatProb (1 / 2) 1 [.new, .join 0, .new] ∧
    (tables [.new, .join 0, .join 0] : Multiset ℕ) ≠ tables [.new, .join 0, .new] := by
  refine ⟨?_, by decide⟩
  norm_num [seatProb, seatProbFrom, predictive, seat]

/-- One table of three and two tables of sizes two and one are equally likely exactly when `d = 1`
or `θ = 2 (1 - d)`, as at `d = 1/2`, `θ = 1`, and not at `d = 0`, `θ = 1`. -/
example {d θ : ℝ} (hθ : -1 < θ) :
    seatProb d θ [.new, .join 0, .join 0] = seatProb d θ [.new, .join 0, .new] ↔
      d = 1 ∨ θ = 2 * (1 - d) := by
  have h₁ : (1 : ℝ) + θ ≠ 0 := by linarith
  have h₂ : (2 : ℝ) + θ ≠ 0 := by linarith
  have key : seatProb d θ [.new, .join 0, .join 0] - seatProb d θ [.new, .join 0, .new] =
      (1 - d) * (2 * (1 - d) - θ) / ((1 + θ) * (2 + θ)) := by
    simp [seatProb, seatProbFrom, predictive, seat]
    field_simp
    ring
  rw [← sub_eq_zero, key, div_eq_zero_iff, or_iff_left (mul_ne_zero h₁ h₂), mul_eq_zero,
    sub_eq_zero, sub_eq_zero, eq_comm (a := (1 : ℝ)), eq_comm (a := 2 * (1 - d))]

/-- A customer cannot join a table that is not open. -/
example (d θ : ℝ) : ¬ Valid [.join 0] ∧ seatProb d θ [.join 0] = 0 := by
  refine ⟨by simp [Valid], ?_⟩
  simp [seatProb, seatProbFrom, predictive]

/-- Exchangeability needs valid sequences: `[new, join 1, join 0]` and `[new, join 0]` both leave
one table of two, with probabilities `0` and `1/4`. -/
example : tables [.new, .join 1, .join 0] = tables [.new, .join 0] ∧
    seatProb (1 / 2) 1 [.new, .join 1, .join 0] = 0 ∧
    seatProb (1 / 2) 1 [.new, .join 0] = 1 / 4 := by
  refine ⟨rfl, ?_, ?_⟩ <;> norm_num [seatProb, seatProbFrom, predictive, seat]

end PitmanYor
end Mettapedia.ProbabilityTheory
