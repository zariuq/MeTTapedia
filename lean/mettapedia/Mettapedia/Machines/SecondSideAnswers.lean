import Mathlib.Tactic

/-!
# The second side of a relation kept by its first column: same answers, linear runs

A binary relation kept as rows by its first column answers a probe that binds
only the second column by scanning every first-column row for the bit, `rows`
steps per probe whatever its answers: on a graph's triangles, a probe per
vertex, the square of the rows.  The second side keeps, for each second-column
value, the first-column values paired with it.  `RentOrBuyIndex` proves the rule
that builds it (rent while the rents stay below its price, then buy) within
twice the best choice of when to build, for probes of uniform cost.

This file adds what that rule needs besides its price:
* `buildSide_eq_answers`: the side, built by one pass over the pairs, answers
  every probe exactly as the scan does, in the relation's order;
* `scanCost_eq` and `scan_quadratic`: the scan costs `rows` steps per probe,
  the square of the rows for one probe per row;
* `rentBuy_le` and `rentBuy_linear`: counting each probe's own answers, the
  run that rents and then buys costs at most `2 * (pairs + rows) + rows` steps
  besides each probe's answers and one step for each probe, and so at most
  `3 * pairs + 4 * rows` for one probe per row.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.SecondSideAnswers

/-- A relation of pairs `(a, b)`. -/
abbrev Rel := List (Nat × Nat)

/-- The answers of a probe binding the second column to `b`: each `a` with
`(a, b)` held, in the relation's order. -/
def answers (rel : Rel) (b : Nat) : List Nat :=
  (rel.filter (fun p => p.2 == b)).map Prod.fst

/-- The second side, built by one pass over the pairs: each pair puts its
first value on the list of its second. -/
def buildSide (rel : Rel) : Nat → List Nat :=
  rel.foldr (fun p side => fun b => if p.2 = b then p.1 :: side b else side b)
    (fun _ => [])

/-- The side answers each probe as the scan does. -/
theorem buildSide_eq_answers (rel : Rel) (b : Nat) :
    buildSide rel b = answers rel b := by
  induction rel with
  | nil => simp [buildSide, answers]
  | cons p rest ih =>
    simp only [buildSide, List.foldr_cons] at ih ⊢
    rw [ih]
    by_cases h : p.2 = b <;> simp [answers, h]

/-- Without the side, a probe reads every first-column row. -/
def scanCost (rows : Nat) (probes : List Nat) : Nat :=
  (probes.map (fun _ => rows)).sum

theorem scanCost_eq (rows : Nat) (probes : List Nat) :
    scanCost rows probes = rows * probes.length := by
  induction probes with
  | nil => simp [scanCost]
  | cons p rest ih =>
    simp only [scanCost, List.map_cons, List.sum_cons, List.length_cons] at ih ⊢
    rw [ih]
    ring

/-- One probe for each row, as a triangle search probes each vertex: the scan
costs the square of the rows. -/
theorem scan_quadratic (rows : Nat) (probes : List Nat)
    (h : probes.length = rows) : scanCost rows probes = rows * rows := by
  rw [scanCost_eq, h]

/-- The run once the side is built: each probe reads its answers and finds
its list in one step. -/
def builtCost (answerCounts : List Nat) : Nat :=
  (answerCounts.map (· + 1)).sum

/-- Rent, then buy.  `rent` is what the probes before paid.  A probe without
the side reads every row; when the rents then reach the side's price,
`pairs + rows`, the side is built at that price, and the probes after it run
as `builtCost` says. -/
def rentBuyCost (rows pairs : Nat) : Nat → List Nat → Nat
  | _, [] => 0
  | rent, _ :: rest =>
      if pairs + rows ≤ rent + rows then
        rows + (pairs + rows) + builtCost rest
      else
        rows + rentBuyCost rows pairs (rent + rows) rest

/-- What the rent phase has left to pay before the side is bought: no more than
its price less what is paid, plus one probe's rent. -/
theorem rentBuyCost_le_aux (rows pairs : Nat) (answerCounts : List Nat) :
    ∀ rent : Nat, rent < pairs + rows →
      rentBuyCost rows pairs rent answerCounts ≤
        (pairs + rows - rent) + rows + (pairs + rows) + builtCost answerCounts := by
  induction answerCounts with
  | nil =>
    intro rent _
    simp [rentBuyCost]
  | cons n rest ih =>
    intro rent hrent
    simp only [rentBuyCost]
    split_ifs with hbuy
    · have hb : builtCost rest ≤ builtCost (n :: rest) := by
        simp [builtCost]
      omega
    · have hnext : rent + rows < pairs + rows := by omega
      have := ih (rent + rows) hnext
      have hb : builtCost rest ≤ builtCost (n :: rest) := by
        simp [builtCost]
      omega

/-- The whole run: at most twice the side's price, one probe's rent more, and
each probe's answers and its one step. -/
theorem rentBuy_le (rows pairs : Nat) (answerCounts : List Nat)
    (hprice : 0 < pairs + rows) :
    rentBuyCost rows pairs 0 answerCounts ≤
      2 * (pairs + rows) + rows + builtCost answerCounts := by
  have := rentBuyCost_le_aux rows pairs answerCounts 0 hprice
  omega

/-- Each probe's answers, summed over a probe for every second-column value,
are the pairs: with one probe per row and as many rows as values, the run is
linear where the scan is quadratic. -/
theorem builtCost_eq (answerCounts : List Nat) :
    builtCost answerCounts = answerCounts.sum + answerCounts.length := by
  induction answerCounts with
  | nil => simp [builtCost]
  | cons n rest ih =>
    simp only [builtCost, List.map_cons, List.sum_cons, List.length_cons] at ih ⊢
    rw [ih]
    ring

theorem rentBuy_linear (rows pairs : Nat) (answerCounts : List Nat)
    (hprice : 0 < pairs + rows) (hsum : answerCounts.sum = pairs)
    (hlen : answerCounts.length = rows) :
    rentBuyCost rows pairs 0 answerCounts ≤ 3 * pairs + 4 * rows := by
  have h := rentBuy_le rows pairs answerCounts hprice
  rw [builtCost_eq, hsum, hlen] at h
  omega

end Mettapedia.Machines.SecondSideAnswers
