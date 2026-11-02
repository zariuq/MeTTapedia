import Mettapedia.GSLT.Dynamics.RegionPortfolio
import Mettapedia.GSLT.Dynamics.JoinAggregation

/-!
# A count observer chooses between three concrete join realizations

The source enumerates ordered row pairs. One worker materializes this source;
the other two independently count matching right rows or build a grouped
count function. Existing variable-elimination proofs connect their results.
Duplicate rows remain duplicate occurrences throughout.

The estimates used by the selector are not asserted to be machine costs.
In particular the functional group table is not certified constant-time
native storage. This instance tests semantic selection, not a speed claim.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.ObservationQualified.JoinCounts

open RegionObservations PartialRegionPlan JoinAggregation

universe u

variable {Row : Type u}

def appendedLength : Family (List Row) where
  Question := List Row
  Answer _ := Nat
  read suffix rows := (rows ++ suffix).length

theorem length_exact : (appendedLength (Row := Row)).Exact List.length := by
  intro left right
  constructor
  · intro same
    change ∀ suffix : List Row, (left ++ suffix).length = (right ++ suffix).length
    intro suffix
    simp [same]
  · intro same
    change ∀ suffix : List Row, (left ++ suffix).length = (right ++ suffix).length at same
    simpa using same []

abbrev Rows := List (Nat × Nat)
abbrev Input := Rows × Rows
abbrev AnswerRows := List (Nat × Nat × Nat)

def boundary : Boundary Input AnswerRows Nat where
  source input := join input.1 input.2
  summarize := List.length
  future := appendedLength
  sufficient left right := (length_exact left right).mp

inductive Regime where
  | materialized | streamed | grouped
  deriving DecidableEq

def materialized : CertifiedRegion boundary Regime where
  regime := .materialized
  Artifact := AnswerRows
  attempt input := .committed (join input.1 input.2)
  decode := List.length
  restores _ _ impossible := by cases impossible
  exact _ _ committed := by cases committed; rfl

def streamCount (input : Input) : Nat :=
  (input.1.map fun row => input.2.countP fun other => other.1 = row.2).sum

theorem streamCount_exact (input : Input) :
    streamCount input = (join input.1 input.2).length :=
  (length_join_eq_sum_countP input.1 input.2).symm

def streamed : CertifiedRegion boundary Regime where
  regime := .streamed
  Artifact := Nat
  attempt input := .committed (streamCount input)
  decode := id
  restores _ _ impossible := by cases impossible
  exact input _ committed := by
    cases committed
    exact streamCount_exact input

abbrev Grouped := Rows × (Nat → Nat)

def buildGroups (input : Input) : Grouped :=
  (input.1, groupTable Prod.fst (fun _ : Nat × Nat => (1 : Nat)) input.2)

def readGroups (groups : Grouped) : Nat :=
  (groups.1.map fun row => groups.2 row.2).sum

theorem groups_exact (input : Input) : readGroups (buildGroups input) =
    (join input.1 input.2).length := by
  have agrees := sum_join_eq_route input.1 input.2 (fun _ => (1 : Nat)) (fun _ => 1)
  simpa [readGroups, buildGroups] using agrees.symm

def grouped : CertifiedRegion boundary Regime where
  regime := .grouped
  Artifact := Grouped
  attempt input := .committed (buildGroups input)
  decode := readGroups
  restores _ _ impossible := by cases impossible
  exact input _ committed := by
    cases committed
    exact groups_exact input

/-- The registry position is explicit; estimates can be supplied by a model,
a profiler or a learner without granting semantic admission. -/
def candidate (region : CertifiedRegion boundary Regime) (ordinal : Nat)
    (estimate : Input → Estimate) : Candidate boundary Regime :=
  ⟨region, estimate, ordinal⟩

def portfolio (prices : Regime → Input → Estimate) : List (Candidate boundary Regime) :=
  [candidate materialized 0 (prices .materialized),
    candidate streamed 1 (prices .streamed), candidate grouped 2 (prices .grouped)]

theorem every_price_model_keeps_count (prices : Regime → Input → Estimate) (input : Input) :
    RegionPortfolio.execute input (portfolio prices) = (join input.1 input.2).length :=
  RegionPortfolio.execute_exact input _

theorem reorder_keeps_count (prices : Regime → Input → Estimate) (input : Input) :
    RegionPortfolio.execute input (portfolio prices).reverse =
      RegionPortfolio.execute input (portfolio prices) :=
  RegionPortfolio.selection_independent input _ _

namespace Controls

def repeated : Input := ([(1, 7), (1, 7), (2, 8)], [(7, 3), (7, 3), (8, 4)])

theorem independent_workers_count_five :
    (join repeated.1 repeated.2).length = 5 ∧
      streamCount repeated = 5 ∧ readGroups (buildGroups repeated) = 5 := by decide

theorem set_quotient_loses_three_occurrences :
    streamCount (repeated.1.dedup, repeated.2.dedup) = 2 ∧ streamCount repeated = 5 := by decide

def preferGrouped : Regime → Input → Estimate
  | .grouped, _ => ⟨1, 2⟩
  | _, _ => ⟨9, 0⟩

theorem chooses_grouped :
    ((RegionPortfolio.select repeated (portfolio preferGrouped)).map
      (fun picked => picked.region.regime)) = some .grouped := by decide

theorem chosen_independent_worker_runs :
    RegionPortfolio.execute repeated (portfolio preferGrouped) = 5 := by decide

theorem all_rejected_still_counts :
    RegionPortfolio.execute repeated
      (RegionPortfolio.gather ([none, none] : List (Option (Candidate boundary Regime)))) = 5 := by
  decide

theorem no_capacity_keeps_the_full_input :
    (grouped.restrict (fun _ => false)).attempt repeated = .declined repeated ∧
      (grouped.restrict (fun _ => false)).execute repeated = 5 := by
  constructor <;> rfl

/-- A scalar count cannot justify replacing an ordered or value-sensitive
observer with a count observer. -/
theorem equal_count_does_not_preserve_first :
    ([1, 2] : List Nat).length = ([2, 1] : List Nat).length ∧
      ([1, 2] : List Nat).head? ≠ ([2, 1] : List Nat).head? := by decide

end Controls

#print axioms length_exact
#print axioms groups_exact
#print axioms every_price_model_keeps_count
#print axioms Controls.chosen_independent_worker_runs

end Mettapedia.GSLT.Dynamics.ObservationQualified.JoinCounts
