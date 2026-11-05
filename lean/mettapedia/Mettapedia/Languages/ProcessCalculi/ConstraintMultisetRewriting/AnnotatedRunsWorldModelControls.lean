import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunsWorldModel

/-!
# The raven ledger as a run

Two observers share one sighting. The first sights `o1`, `o2` and `o3`, three black birds. The
second sights `o4`, a bird that is not black, and `o5`, another black bird. Each then submits the
observations it vouches for: the first `{o1, o2, o3}`, the second `{o3, o4, o5}`, sharing `o3`.

Every step is a firing of the candidate step. Sightings make observation occurrences into the
evidence space; submissions read the observations they cite and make a submission record outside
it. The run is executable (`run_executable`), and confidence uses prior weight one.

| Combination | Evidence | Strength, confidence | Lean |
|---|---|---|---|
| revise only disjoint submissions, else keep the first | (3, 0) | (1, 3/4) | `stamp_row` |
| add the evidence of the two submissions | (5, 1) | (5/6, 6/7) | `additive_row` |
| the ledger at the end of the run | (4, 1) | (4/5, 5/6) | `ledger_row` |

* The stamp rule is safe but drops the new sightings; the additive readout counts `o3` twice; the
  ledger is exact (`ledger_eq_union`).
* **A repeated submission changes nothing** in the ledger (`resubmission_keeps_ledger`,
  `resubmission_keeps_row`), while the additive readout grows to (7, 2), that is
  (7/9, 9/10) (`resubmission_additive_row`).
* **Interleavings.** The two sightings are independent, so the run with them in the other order is
  the same trace (`orders_one_trace`). Summed over the two orders the readout is (8, 2); the merged
  ledger gives (4, 1) once (`interleavings_double_count`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns

namespace WorldModelRuns

namespace RavenControls

open Mettapedia.Logic.LP
open ConstraintMultisetRewriting.Controls (signature A)
open AnnotatedRuns.Controls (Run)
open Mettapedia.PLN.WorldModel.EvidenceSpaces
open Mettapedia.PLN.WorldModel.EvidenceContracts
open MeTTaCalculus.OccurrenceCommits (TraceIndependent)
open Mettapedia.GSLT.Distinction.CausalGluing (TraceEquiv Swap)

/-- Labels: black sightings `1`, `2`, `3`, `5`; the sighting `4` is not black; submission records
`11`, `12`, `13`; `20` carries the row of the counts `(4, 1)`, made by a revision firing. -/
def label : Nat → Term signature
  | 1 => .const 1
  | 2 => .const 1
  | 3 => .const 1
  | 4 => .const 0
  | 5 => .const 1
  | 11 => .const 7
  | 12 => .const 7
  | 13 => .const 7
  | 20 => ConstraintMultisetRewriting.Controls.f (.const (Nat.pair 4 1))
  | _ => .const 2

/-- The evidence space: sightings, black or not. -/
def space : Term signature → Bool
  | .const 0 => true
  | .const 1 => true
  | _ => false

/-- What a sighting records: whether the bird is black. -/
def black : Term signature → Bool
  | .const 1 => true
  | _ => false

/-- The query of outcomes: "the bird is black". -/
def isBlack : Bool → Bool := id

def empty : Configuration (Term signature) Nat := ⟨[], ∅⟩

/-- The first observer sights `o1`, `o2`, `o3`. -/
def sightFirst : Run := ⟨⟨[], [], [], [], [.const 1, .const 1, .const 1]⟩, [], ⟨[], [], [1, 2, 3]⟩⟩

/-- The second observer sights `o4` and `o5`. -/
def sightSecond : Run := ⟨⟨[], [], [], [], [.const 0, .const 1]⟩, [], ⟨[], [], [4, 5]⟩⟩

/-- The first observer submits `{o1, o2, o3}`. -/
def submitFirst : Run :=
  ⟨⟨[], [.const 1, .const 1, .const 1], [], [], [.const 7]⟩, [], ⟨[], [1, 2, 3], [11]⟩⟩

/-- The second observer submits `{o3, o4, o5}`. -/
def submitSecond : Run :=
  ⟨⟨[], [.const 1, .const 0, .const 1], [], [], [.const 7]⟩, [], ⟨[], [3, 4, 5], [12]⟩⟩

/-- The second observer submits `{o3, o4, o5}` again. -/
def resubmitSecond : Run :=
  ⟨⟨[], [.const 1, .const 0, .const 1], [], [], [.const 7]⟩, [], ⟨[], [3, 4, 5], [13]⟩⟩

def ravenRun : List Run := [sightFirst, sightSecond, submitFirst, submitSecond]

theorem sightFirst_valid : sightFirst.Valid A label empty := by
  refine ⟨⟨by decide, by decide, rfl, rfl, rfl, by decide, ⟨Subst.id signature, ?_⟩,
    by simp [sightFirst]⟩, by simp [sightFirst]⟩
  intro equation member
  simp [Selection.problem, Selection.equations, empty, sightFirst] at member

theorem sightSecond_valid : sightSecond.Valid A label (sightFirst.result label empty) := by
  refine ⟨⟨by decide, by decide, rfl, rfl, rfl, by decide, ⟨Subst.id signature, ?_⟩,
    by simp [sightSecond]⟩, by simp [sightSecond]⟩
  intro equation member
  simp [Selection.problem, Selection.equations, Selection.result, Firing.result, empty,
    sightFirst, sightSecond] at member

theorem submitFirst_valid :
    submitFirst.Valid A label (sightSecond.result label (sightFirst.result label empty)) := by
  refine ⟨⟨by decide, by decide, rfl, rfl, rfl, by decide, ⟨Subst.id signature, ?_⟩,
    by simp [submitFirst]⟩, by simp [submitFirst]⟩
  intro equation member
  simp [Selection.problem, Selection.equations, Selection.result, Firing.result, empty,
    sightFirst, sightSecond, submitFirst, label] at member
  subst member
  rfl

theorem submitSecond_valid :
    submitSecond.Valid A label
      (submitFirst.result label (sightSecond.result label (sightFirst.result label empty))) := by
  refine ⟨⟨by decide, by decide, rfl, rfl, rfl, by decide, ⟨Subst.id signature, ?_⟩,
    by simp [submitSecond]⟩, by simp [submitSecond]⟩
  intro equation member
  simp [Selection.problem, Selection.equations, Selection.result, Firing.result, empty,
    sightFirst, sightSecond, submitFirst, submitSecond, label] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem resubmitSecond_valid :
    resubmitSecond.Valid A label (follow label empty ravenRun) := by
  refine ⟨⟨by decide, by decide, rfl, rfl, rfl, by decide, ⟨Subst.id signature, ?_⟩,
    by simp [resubmitSecond]⟩, by simp [resubmitSecond]⟩
  intro equation member
  simp [follow, ravenRun, Selection.problem, Selection.equations, Selection.result, Firing.result,
    empty, sightFirst, sightSecond, submitFirst, submitSecond, resubmitSecond, label] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- **The raven run runs.** -/
theorem run_executable : Executable A label empty ravenRun :=
  ⟨sightFirst_valid, sightSecond_valid, submitFirst_valid, submitSecond_valid,
    submitSecond_valid.firing.consistent⟩

/-- The run with the repeated submission runs. -/
theorem rerun_executable : Executable A label empty (ravenRun ++ [resubmitSecond]) :=
  ⟨sightFirst_valid, sightSecond_valid, submitFirst_valid, submitSecond_valid,
    resubmitSecond_valid, resubmitSecond_valid.firing.consistent⟩

/-- The first submission. -/
theorem cited_first : cited label space submitFirst = {1, 2, 3} := by decide

/-- The second submission, sharing `o3`. -/
theorem cited_second : cited label space submitSecond = {3, 4, 5} := by decide

/-- **The ledger at the end of the run** holds the five sightings once each. -/
theorem final_ledger : ledger label space (follow label empty ravenRun) = {1, 2, 3, 4, 5} := by
  decide

theorem ledger_eq_union :
    ledger label space (follow label empty ravenRun) =
      cited label space submitFirst ∪ cited label space submitSecond := by
  rw [final_ledger, cited_first, cited_second]
  decide

/-- Revise disjoint submissions; otherwise keep the first. -/
def stampRevise (first second : Finset Nat) : Finset Nat :=
  if Disjoint first second then first ∪ second else first

theorem first_evidence :
    ledgerEvidence (recorded label black) isBlack {1, 2, 3} = ⟨3, 0⟩ := by
  ext <;> decide

theorem second_evidence :
    ledgerEvidence (recorded label black) isBlack {3, 4, 5} = ⟨2, 1⟩ := by
  ext <;> decide

theorem union_evidence :
    ledgerEvidence (recorded label black) isBlack {1, 2, 3, 4, 5} = ⟨4, 1⟩ := by
  ext <;> decide

/-- **The stamp rule**: the submissions overlap, so the first is kept and the new sightings are
dropped: (1, 3/4). -/
theorem stamp_row :
    truthValue 1 (ledgerEvidence (recorded label black) isBlack
      (stampRevise (cited label space submitFirst) (cited label space submitSecond))) =
      (1, 3 / 4) := by
  have overlap : ¬ Disjoint (({1, 2, 3} : Finset Nat)) {3, 4, 5} := by decide
  rw [cited_first, cited_second, stampRevise, if_neg overlap, first_evidence]
  norm_num [truthValue, strengthQ, confidenceQ, Evidence.strength, Evidence.total]

/-- **Additive revision** counts `o3` twice: (5/6, 6/7). It is the additive readout of the run
word. -/
theorem additive_row :
    citedSum label space black isBlack ravenRun = ⟨5, 1⟩ ∧
      truthValue 1 (citedSum label space black isBlack ravenRun) = (5 / 6, 6 / 7) := by
  have sum : citedSum label space black isBlack ravenRun = ⟨5, 1⟩ := by
    simp only [ravenRun, citedSum]
    ext <;> decide
  refine ⟨sum, ?_⟩
  rw [sum]
  norm_num [truthValue, strengthQ, confidenceQ, Evidence.strength, Evidence.total]

/-- **The ledger** gives the exact row: (4/5, 5/6). -/
theorem ledger_row :
    readout label space black isBlack (follow label empty ravenRun) = ⟨4, 1⟩ ∧
      truthAt label space black 1 isBlack (follow label empty ravenRun) = (4 / 5, 5 / 6) := by
  have counts : readout label space black isBlack (follow label empty ravenRun) = ⟨4, 1⟩ := by
    unfold readout
    rw [final_ledger, union_evidence]
  refine ⟨counts, ?_⟩
  unfold truthAt
  rw [counts]
  norm_num [truthValue, strengthQ, confidenceQ, Evidence.strength, Evidence.total]

/-- The additive readout is not exact: the submissions are not disjoint. -/
theorem additive_not_exact :
    citedSum label space black isBlack ravenRun ≠
      ledgerEvidence (recorded label black) isBlack (citedLedger label space ravenRun) := by
  rw [Ne, citedSum_eq_iff_pairwise_disjoint]
  intro apart
  have pair := List.pairwise_iff_get.mp apart ⟨2, by decide⟩ ⟨3, by decide⟩ (by decide)
  change Disjoint (cited label space submitFirst) (cited label space submitSecond) at pair
  rw [cited_first, cited_second] at pair
  revert pair
  decide

/-- **A repeated submission changes nothing in the ledger.** -/
theorem resubmission_keeps_ledger :
    ledger label space (follow label empty (ravenRun ++ [resubmitSecond])) =
      ledger label space (follow label empty ravenRun) := by
  decide

theorem resubmission_keeps_row :
    truthAt label space black 1 isBlack (follow label empty (ravenRun ++ [resubmitSecond])) =
      (4 / 5, 5 / 6) := by
  rw [← ledger_row.2]
  exact truthAt_eq_of_ledger_eq label space black 1 isBlack resubmission_keeps_ledger

/-- The cited ledger keeps its value too. -/
theorem resubmission_keeps_cited :
    citedLedger label space (ravenRun ++ [resubmitSecond]) = citedLedger label space ravenRun :=
  citedLedger_append_of_subset label space (by decide)

/-- **The additive readout grows on a repeated submission**: (7, 2), that is (7/9, 9/10). -/
theorem resubmission_additive_row :
    citedSum label space black isBlack (ravenRun ++ [resubmitSecond]) = ⟨7, 2⟩ ∧
      truthValue 1 (citedSum label space black isBlack (ravenRun ++ [resubmitSecond])) =
        (7 / 9, 9 / 10) := by
  have sum : citedSum label space black isBlack (ravenRun ++ [resubmitSecond]) = ⟨7, 2⟩ := by
    rw [citedSum_append, additive_row.1]
    ext <;> decide
  refine ⟨sum, ?_⟩
  rw [sum]
  norm_num [truthValue, strengthQ, confidenceQ, Evidence.strength, Evidence.total]

/-! ### Interleavings of the sightings -/

/-- The run with the two sightings in the other order. -/
def swappedRun : List Run := [sightSecond, sightFirst, submitFirst, submitSecond]

/-- The two sightings are statically independent. -/
theorem sightings_independent : StaticIndependent label sightFirst sightSecond := by
  refine ⟨⟨rfl, by simp [Firing.StaticQueries, sightFirst]⟩,
    ⟨rfl, by simp [Firing.StaticQueries, sightSecond]⟩, fun _ => ?_⟩
  unfold TraceIndependent MeTTaCalculus.OccurrenceCommits.Independent
    MeTTaCalculus.OccurrenceCommits.Clash MeTTaCalculus.OccurrenceCommits.Spoils
    MeTTaCalculus.OccurrenceCommits.WritesInto MeTTaCalculus.OccurrenceCommits.Commit.uses
  simp only [Firing.footprintAt_taken, Firing.footprintAt_kept, Firing.footprintAt_made,
    Firing.footprintAt_queries, sightFirst, sightSecond, List.map_nil]
  decide

/-- **The two orders are one trace.** -/
theorem orders_one_trace : RoundEquiv A label empty ravenRun swappedRun := by
  refine traceEquiv_roundEquiv A label ?_ empty run_executable
  change TraceEquiv (StaticIndependent label) [sightFirst, sightSecond, submitFirst, submitSecond]
    [sightSecond, sightFirst, submitFirst, submitSecond]
  exact .rel _ _ (by simpa using Swap.swap [] [submitFirst, submitSecond] sightings_independent)

/-- **The interleaving sum counts the ledger twice; the merge counts it once.** -/
theorem interleavings_double_count :
    ([ravenRun, swappedRun].map fun w =>
        readout label space black isBlack (follow label empty w)).sum =
        ⟨8, 2⟩ ∧
      readout label space black isBlack (follow label empty ravenRun) +
          readout label space black isBlack (follow label empty swappedRun) ≠
        ledgerEvidence (recorded label black) isBlack
          (ledger label space (follow label empty ravenRun) ∪
            ledger label space (follow label empty swappedRun)) := by
  have routes : ∀ w' ∈ [ravenRun, swappedRun], RoundEquiv A label empty ravenRun w' := by
    intro w' member
    rcases List.mem_pair.mp member with rfl | rfl
    · exact Relation.EqvGen.refl _
    · exact orders_one_trace
  constructor
  · rw [interleavings_sum A label space black isBlack [ravenRun, swappedRun] routes, ledger_row.1]
    ext <;> rfl
  · intro same
    have empty' :=
      (interleaving_sum_eq_merge_iff A label space black isBlack orders_one_trace).mp same
    rw [final_ledger] at empty'
    exact absurd empty' (by decide)

end RavenControls

end WorldModelRuns

open WorldModelRuns

#print axioms RavenControls.run_executable
#print axioms RavenControls.rerun_executable
#print axioms RavenControls.final_ledger
#print axioms RavenControls.ledger_eq_union
#print axioms RavenControls.stamp_row
#print axioms RavenControls.additive_row
#print axioms RavenControls.ledger_row
#print axioms RavenControls.additive_not_exact
#print axioms RavenControls.resubmission_keeps_ledger
#print axioms RavenControls.resubmission_keeps_row
#print axioms RavenControls.resubmission_keeps_cited
#print axioms RavenControls.resubmission_additive_row
#print axioms RavenControls.sightings_independent
#print axioms RavenControls.orders_one_trace
#print axioms RavenControls.interleavings_double_count

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns
