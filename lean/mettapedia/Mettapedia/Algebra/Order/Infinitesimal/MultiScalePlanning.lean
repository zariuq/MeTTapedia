import Mettapedia.Algebra.Order.Infinitesimal.LevelSeries

/-!
# Priorities at different scales, decided by ordinary arithmetic

A planner often has objectives that are not commensurable: a hard constraint
that must never be traded away, an ordinary reward, and a tie-break that should
matter only when everything else is level.  The usual answers are to invent a
penalty weight big enough, or to compare tuples lexicographically.  Both have a
cost.  A weight has to be guessed and can always be outbid
(`finite_weight_is_outbid`); a tuple order is not a number, so scores of
independent subproblems cannot be added.

Scoring into the level field does both jobs with one comparison.  A hard
constraint sits at level `-1`, ordinary reward at level `0`, the tie-break at
level `1`, and the ordinary order of the field decides.  The scores remain
*numbers*: they add, subtract and multiply, so independent subproblems compose.

The three facts that make this work are proved here in general, not shown on an
example:

* `reward_never_compensates_violation` — **no** reward and **no** tie-break
  ever outweighs a violation, for every rational value of each;
* `finite_weight_is_outbid` — for **every** finite penalty weight there is a
  reward that overturns it, which is exactly what the level does not permit;
* `tie_break_never_overturns_reward` — an infinitesimal tie-break never
  reverses a strict difference in reward, however large the tie-break.
-/

set_option autoImplicit false

namespace Mettapedia.Algebra.Order.Infinitesimal

open HahnSeries LevelSeries

namespace MultiScale

/-! ## The comparison lemma the applications rest on -/

/-- **Two series whose lowest level is the same are ordered by the coefficient
there.**  Everything below that level is absent from both, so the first
difference is at the head. -/
theorem toLevelField_lt_of_head_lt {i : ℤ} {a b : ℚ} {p q : LevelSeries}
    (hp : Sorted ((i, a) :: p)) (hq : Sorted ((i, b) :: q)) (hab : a < b) :
    toLevelField ((i, a) :: p) < toLevelField ((i, b) :: q) := by
  rw [toLevelField, toLevelField, lt_iff]
  refine ⟨i, fun j hj => ?_, ?_⟩
  · rw [ofLex_toLex, ofLex_toLex, coeff_toHahn_lt_head hp hj, coeff_toHahn_lt_head hq hj]
  · rw [ofLex_toLex, ofLex_toLex, coeff_toHahn_head hp, coeff_toHahn_head hq]
    exact hab

/-! ## Scoring a plan -/

/-- A plan's score: how badly it breaks the hard constraint, what it earns, and
how it breaks ties. -/
structure Score where
  /-- Violation of the hard constraint; positive means the plan breaks it. -/
  violation : ℚ
  /-- Ordinary reward. -/
  reward : ℚ
  /-- Tie-break, to be consulted only when the rest is level. -/
  tieBreak : ℚ
  deriving DecidableEq, Repr

/-- The score as a level series: violation at level `-1`, reward at level `0`,
tie-break at level `1`. -/
def Score.toSeries (s : Score) : LevelSeries :=
  [(-1, -s.violation), (0, s.reward), (1, s.tieBreak)]

theorem sorted_toSeries (s : Score) : Sorted s.toSeries := by
  refine ⟨?_, ⟨?_, ⟨by simp, trivial⟩⟩⟩ <;> intro u hu <;>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu <;>
    rcases hu with rfl | rfl <;> norm_num

/-- Comparison of plans, executable. -/
def Score.better (s t : Score) : Bool := LevelSeries.cmp t.toSeries s.toSeries = .lt

/-! ## A violation is never worth it -/

/-- **No reward and no tie-break ever compensates a violation.**  For every
reward and every tie-break, a plan that breaks the hard constraint scores below
a plan that keeps it with nothing at all. -/
theorem reward_never_compensates_violation
    {v reward tieBreak : ℚ} (hv : 0 < v) :
    toLevelField (Score.mk v reward tieBreak).toSeries <
      toLevelField (Score.mk 0 0 0).toSeries := by
  refine toLevelField_lt_of_head_lt (sorted_toSeries _) (sorted_toSeries _) ?_
  show -v < -0
  simpa using hv

/-- The same, comparing two plans that both earn and break ties however they
like: only the violation is consulted. -/
theorem violation_decides
    {v w r r' t t' : ℚ} (h : w < v) :
    toLevelField (Score.mk v r t).toSeries <
      toLevelField (Score.mk w r' t').toSeries := by
  refine toLevelField_lt_of_head_lt (sorted_toSeries _) (sorted_toSeries _) ?_
  show -v < -w
  exact neg_lt_neg h

/-! ## Why a finite weight cannot do this -/

/-- **Every finite penalty weight is outbid.**  Choosing a weight `M` for the
hard constraint means some reward makes breaking it profitable — and the
witness is explicit. -/
theorem finite_weight_is_outbid (M : ℚ) :
    ∃ reward : ℚ, 0 < -M + reward :=
  ⟨M + 1, by ring_nf; norm_num⟩

/-- Stated against the level scoring, the contrast is exact: there the
violation term is below **every** rational, so no reward is large enough. -/
theorem violation_below_every_reward (reward : ℚ) : ofRat reward < Om :=
  ofRat_lt_Om reward

/-! ## The tie-break stays a tie-break

When two scores agree at a level, that level contributes the same amount to
both and cancels: the comparison drops to what is left. -/

theorem toLevelField_cons (t : Term) (l : LevelSeries) :
    toLevelField (t :: l) = toLex (single t.1 t.2) + toLevelField l := rfl

/-- **Agreeing heads cancel.** -/
theorem toLevelField_lt_cons {t : Term} {p q : LevelSeries}
    (h : toLevelField p < toLevelField q) :
    toLevelField (t :: p) < toLevelField (t :: q) := by
  rw [toLevelField_cons, toLevelField_cons]
  exact add_lt_add_of_le_of_lt le_rfl h

theorem sorted_singleton (t : Term) : Sorted [t] := ⟨by simp, trivial⟩

theorem sorted_pair {i j : ℤ} {a b : ℚ} (h : i < j) : Sorted [(i, a), (j, b)] :=
  ⟨by
    intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl
    exact h, sorted_singleton _⟩

/-- **An infinitesimal tie-break never overturns a difference in reward**,
however large the tie-break: the violation levels agree and cancel, and the
reward level decides before the tie-break is ever consulted. -/
theorem tie_break_never_overturns_reward {r r' t t' : ℚ} (h : r < r') :
    toLevelField (Score.mk 0 r t).toSeries <
      toLevelField (Score.mk 0 r' t').toSeries :=
  toLevelField_lt_cons
    (toLevelField_lt_of_head_lt (sorted_pair (by norm_num)) (sorted_pair (by norm_num)) h)

/-- **And it decides when the reward is level.** -/
theorem tie_break_decides {r t t' : ℚ} (h : t < t') :
    toLevelField (Score.mk 0 r t).toSeries <
      toLevelField (Score.mk 0 r t').toSeries :=
  toLevelField_lt_cons (toLevelField_lt_cons
    (toLevelField_lt_of_head_lt (sorted_singleton _) (sorted_singleton _) h))

/-! ## A worked choice, executable

Three plans.  The first breaks the hard constraint but earns a great deal; the
second keeps it and earns little; the third keeps it, earns the same little,
and wins on the tie-break. -/

namespace Worked

/-- Breaks the constraint, earns a fortune. -/
def greedy : Score := ⟨1, 1000000, 0⟩

/-- Keeps the constraint, earns little. -/
def safe : Score := ⟨0, 1, 0⟩

/-- Keeps the constraint, earns the same, better on the tie-break. -/
def polished : Score := ⟨0, 1, 5⟩

/-- Pick the best of a nonempty list. -/
def best : Score → List Score → Score
  | s, [] => s
  | s, t :: rest => best (if t.better s then t else s) rest

/-- **The greedy plan loses to the safe one**, despite earning a million,
because the comparison is at a level the million cannot reach. -/
theorem greedy_loses :
    toLevelField greedy.toSeries < toLevelField safe.toSeries :=
  violation_decides (by norm_num)

/-- **And the tie-break settles the remaining pair.** -/
theorem polished_wins :
    toLevelField safe.toSeries < toLevelField polished.toSeries :=
  tie_break_decides (by norm_num)

end Worked

end MultiScale

end Mettapedia.Algebra.Order.Infinitesimal

#print axioms Mettapedia.Algebra.Order.Infinitesimal.MultiScale.toLevelField_lt_of_head_lt
#print axioms Mettapedia.Algebra.Order.Infinitesimal.MultiScale.reward_never_compensates_violation
#print axioms Mettapedia.Algebra.Order.Infinitesimal.MultiScale.violation_decides
#print axioms Mettapedia.Algebra.Order.Infinitesimal.MultiScale.finite_weight_is_outbid
#print axioms Mettapedia.Algebra.Order.Infinitesimal.MultiScale.tie_break_never_overturns_reward
#print axioms Mettapedia.Algebra.Order.Infinitesimal.MultiScale.tie_break_decides
#print axioms Mettapedia.Algebra.Order.Infinitesimal.MultiScale.Worked.greedy_loses
#print axioms Mettapedia.Algebra.Order.Infinitesimal.MultiScale.Worked.polished_wins
