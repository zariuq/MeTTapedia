import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.CausalHistories

/-!
# Controls for the race identity

## Positive control: two independent races (`Coins`)

Two races with weights `1, 3` and `2, 2`. The causal history "the first lands tails, the second
heads" has two linearizations, each of likelihood `3/16` under the jump chain of the composition,
and their sum is the product `3/4 · 1/2` of the two races' own likelihoods (`history_product`),
as the race identity says (`history_by_identity`).

## Negative control: a confused contention set (`Board`)

Two receivers `r1, r2` and two messages `m1, m2`: four candidates `ij` joining `ri` with `mj`, with
weight `2` for `11` and `1` for the others. All four form one contention set (each shares a receiver
or a message with two others), yet `11` and `22` share nothing: the set is not a cell. The causal
history in which `11` and `22` both fire has two linearizations.

* Normalizing the firing candidate inside its contention set, along each linearization, gives `2/5`
  for `11` then `22` and `1/5` for `22` then `11` (`confusion_representatives`): the likelihood is
  not invariant under the interleaving quotient.
* Normalizing maximal matchings by the products of their weights gives `2/3` (`matchingShare`).
* The jump chain gives the history `2/5 + 1/5 = 3/5` (`confusion_history`), which neither local
  reading produces (`confusion_control`).

## Negative control: transparency needs the quotient (`Tick`)

A deterministic side (one candidate, weight `w`) beside a fair race. The likelihood of the schedule
"the deterministic candidate first, then heads" depends on `w`: `1/6` at `w = 1`, `1/4` at `w = 2`
(`schedule_sees_weight`). The causal history's likelihood is `1/2` for every positive `w`
(`history_blind_to_weight`).
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.CausalHistories.Controls

open Mettapedia.GSLT.GradedSupport (IsNormal)

/-! ## Two independent races -/

/-- A race with two outcomes. -/
inductive Coin where
  | start
  | heads
  | tails
  deriving DecidableEq

/-- The first race: heads with weight `1`, tails with weight `3`. -/
def coinA : Coin → List (Coin × ℝ)
  | .start => [(.heads, 1), (.tails, 3)]
  | _ => []

/-- The second race: heads and tails with weight `2` each. -/
def coinB : Coin → List (Coin × ℝ)
  | .start => [(.heads, 2), (.tails, 2)]
  | _ => []

theorem coinA_positive : Positive coinA := by
  intro s p member
  cases s <;> simp only [coinA, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> norm_num

theorem coinB_positive : Positive coinB := by
  intro s p member
  cases s <;> simp only [coinB, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> norm_num

theorem coinA_maximal : Maximal coinA .start [(.tails, 3)] :=
  ⟨.cons (by simp [coinA]) (.nil _), fun p member => by simp [endState, coinA] at member⟩

theorem coinB_maximal : Maximal coinB .start [(.heads, 2)] :=
  ⟨.cons (by simp [coinB]) (.nil _), fun p member => by simp [endState, coinB] at member⟩

/-- **The two linearizations, each `3/16`, and their sum, the product `3/4 · 1/2`.** -/
theorem history_product :
    schedProb coinA coinB .start .start [.inl (.tails, 3), .inr (.heads, 2)] = 3 / 16 ∧
      schedProb coinA coinB .start .start [.inr (.heads, 2), .inl (.tails, 3)] = 3 / 16 ∧
      ((shuffles [((.tails : Coin), (3 : ℝ))] [((.heads : Coin), (2 : ℝ))]).map
          (schedProb coinA coinB .start .start)).sum = 3 / 8 ∧
      pathProb coinA .start [(.tails, 3)] = 3 / 4 ∧ pathProb coinB .start [(.heads, 2)] = 1 / 2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num [schedProb, pathProb, shuffles, total, coinA, coinB]

/-- **The same sum, by the race identity.** -/
theorem history_by_identity :
    ((shuffles [((.tails : Coin), (3 : ℝ))] [((.heads : Coin), (2 : ℝ))]).map
        (schedProb coinA coinB .start .start)).sum =
      pathProb coinA .start [(.tails, 3)] * pathProb coinB .start [(.heads, 2)] :=
  sum_shuffles coinA coinB coinA_positive coinB_positive _ _ _ _ coinA_maximal.1 coinB_maximal.1
    coinA_maximal.2 coinB_maximal.2

/-! ## A confused contention set -/

/-- The 2×2 race, by what is left after the first firing: firing `11` leaves only `22`, firing `12`
leaves only `21`, and so on. -/
inductive Board where
  | full
  | left11
  | left12
  | left21
  | left22
  | done
  deriving DecidableEq

/-- The candidates of the 2×2 race: `11` has weight `2`, the others `1`. -/
def board : Board → List (Board × ℝ)
  | .full => [(.left22, 2), (.left21, 1), (.left12, 1), (.left11, 1)]
  | .left22 => [(.done, 1)]
  | .left21 => [(.done, 1)]
  | .left12 => [(.done, 1)]
  | .left11 => [(.done, 2)]
  | .done => []

/-- `11`, then `22`. -/
def elevenFirst : List (Board × ℝ) := [(.left22, 2), (.done, 1)]

/-- `22`, then `11`. -/
def twentyTwoFirst : List (Board × ℝ) := [(.left11, 1), (.done, 2)]

theorem elevenFirst_maximal : Maximal board .full elevenFirst :=
  ⟨.cons (by simp [board]) (.cons (by simp [board]) (.nil _)),
    fun p member => by simp [endState, elevenFirst, board] at member⟩

theorem twentyTwoFirst_maximal : Maximal board .full twentyTwoFirst :=
  ⟨.cons (by simp [board]) (.cons (by simp [board]) (.nil _)),
    fun p member => by simp [endState, twentyTwoFirst, board] at member⟩

/-- **Normalization of maximal matchings**: the matching `{11, 22}` against `{12, 21}`, each
weighted by the product of its candidates' weights. -/
def matchingShare (w₁₁ w₁₂ w₂₁ w₂₂ : ℝ) : ℝ := w₁₁ * w₂₂ / (w₁₁ * w₂₂ + w₁₂ * w₂₁)

/-- **Along each linearization**, normalizing the firing candidate inside its contention set (here
the whole race, then the one candidate left) gives `2/5` and `1/5`. -/
theorem confusion_representatives :
    pathProb board .full elevenFirst = 2 / 5 ∧ pathProb board .full twentyTwoFirst = 1 / 5 := by
  constructor <;> norm_num [pathProb, total, board, elevenFirst, twentyTwoFirst]

/-- **The jump chain's likelihood of the history**: the sum over its two linearizations. -/
theorem confusion_history :
    pathProb board .full elevenFirst + pathProb board .full twentyTwoFirst = 3 / 5 := by
  rw [confusion_representatives.1, confusion_representatives.2]
  norm_num

/-- **The confused control**: the two representatives disagree, the matching reading gives `2/3`,
and the jump chain gives `3/5`. -/
theorem confusion_control :
    pathProb board .full elevenFirst ≠ pathProb board .full twentyTwoFirst ∧
      matchingShare 2 1 1 1 = 2 / 3 ∧
      pathProb board .full elevenFirst + pathProb board .full twentyTwoFirst ≠
        matchingShare 2 1 1 1 := by
  rw [confusion_history, confusion_representatives.1, confusion_representatives.2]
  refine ⟨by norm_num, by norm_num [matchingShare], by norm_num [matchingShare]⟩

/-! ## Transparency needs the quotient -/

/-- A deterministic side: one candidate of weight `w`. -/
def tick (w : ℝ) : Coin → List (Coin × ℝ)
  | .start => [(.heads, w)]
  | _ => []

/-- A fair race. -/
def fair : Coin → List (Coin × ℝ)
  | .start => [(.heads, 1), (.tails, 1)]
  | _ => []

theorem tick_positive {w : ℝ} (hw : 0 < w) : Positive (tick w) := by
  intro s p member
  cases s <;> simp only [tick, List.mem_cons, List.not_mem_nil, or_false] at member
  subst member
  exact hw

theorem fair_positive : Positive fair := by
  intro s p member
  cases s <;> simp only [fair, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> norm_num

/-- **A schedule sees the weight of a deterministic candidate.** -/
theorem schedule_sees_weight :
    schedProb (tick 1) fair .start .start [.inl (.heads, 1), .inr (.heads, 1)] = 1 / 6 ∧
      schedProb (tick 2) fair .start .start [.inl (.heads, 2), .inr (.heads, 1)] = 1 / 4 := by
  constructor <;> norm_num [schedProb, total, tick, fair]

/-- **The causal history does not**: for every positive weight it has the fair race's `1/2`. -/
theorem history_blind_to_weight {w : ℝ} (hw : 0 < w) :
    ((shuffles [((.heads : Coin), w)] [((.heads : Coin), (1 : ℝ))]).map fun σ =>
        pathProb (par (tick w) fair) (.start, .start) (realize .start .start σ)).sum = 1 / 2 := by
  rw [deterministic_transparent (tick w) fair (tick_positive hw) fair_positive
    ⟨.cons (by simp [tick]) (.nil _), fun p member => by simp [endState, tick] at member⟩
    (.cons (by simp [tick]) (.nil _))
    ⟨.cons (by simp [fair]) (.nil _), fun p member => by simp [endState, fair] at member⟩]
  norm_num [pathProb, total, fair]

#print axioms coinA_positive
#print axioms history_product
#print axioms history_by_identity
#print axioms confusion_representatives
#print axioms confusion_history
#print axioms confusion_control
#print axioms schedule_sees_weight
#print axioms history_blind_to_weight

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.CausalHistories.Controls

end
