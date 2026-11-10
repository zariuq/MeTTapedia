import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DistinctionMachine
import Mettapedia.GSLT.Distinction.HistoryGrammar

/-!
# The d-calc history grammar interpreted by transform

Evolution, fork, merge and erasure run on finite multisets of live nodes;
the space of such configurations is not required to be finite. Each event
is interpreted by one state-token firing. Forward and backward correspondence
preserve the complete event word, including fork versus erase distinctions.

This serial interpreter preserves labelled histories. It does not claim to
preserve true concurrency: its shared state token serializes events. A
distributed representation needs a separate independence-preserving lowering.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DistinctionHistory
open Mettapedia.Cybernetics.DistinctionCalculus.History
open Mettapedia.GSLT.Distinction.HistoryGrammar
open DistinctionFinite

universe uV uR
variable {V : Type uV} [DecidableEq V] {R : Type uR}
  (G : Grammar V) (read : Multiset V → R)

def machine : Machine (Multiset V) (Event V) R :=
  ⟨read, fun live event => (step G event live).toList⟩

theorem next_iff (live target : Multiset V) (event : Event V) :
    target ∈ (machine G read).next live event ↔ Fires G event live target := by
  rw [← step_eq_some_iff]
  change target ∈ (step G event live).toList ↔ step G event live = some target
  cases step G event live <;> simp [eq_comm]

theorem moves_iff (s t : Nat × Multiset V) (event : Event V) :
    Race.Generic.Moves (machine G read).step.toStep Machine.offers s event t ↔
      t.1 = s.1 + 1 ∧ Fires G event s.2 t.2 := by
  rw [Machine.moves_iff, next_iff]

def events {s : Nat × Multiset V} (run : (machine G read).step.Run s) : List (Event V) :=
  run.word.map fun entry => entry.2.1

/-- Every interpreted run reflects to the original event grammar, with no extra history. -/
theorem reflects_run {s : Nat × Multiset V} (run : (machine G read).step.Run s) :
    LabelledPath G s.2 (events G read run) run.last.2 := by
  induction run with
  | nil s => exact .nil s.2
  | @cons s f admitted rest ih =>
      exact .cons ((next_iff G read s.2 f.2 f.1).mp admitted) ih

/-- Every source history lifts, at any fresh clock, keeping its event word and final nodes. -/
theorem lifts_path {live target : Multiset V} {word : List (Event V)}
    (path : LabelledPath G live word target) :
    ∀ clock, ∃ run : (machine G read).step.Run (clock, live),
      run.last.2 = target ∧ events G read run = word := by
  induction path with
  | nil live =>
      intro clock
      exact ⟨.nil (clock, live), rfl, rfl⟩
  | @cons live middle target event word fired rest ih =>
      intro clock
      obtain ⟨tail, last, labels⟩ := ih (clock + 1)
      let admitted := (next_iff G read live middle event).mpr fired
      refine ⟨.cons (event, middle) admitted tail, last, ?_⟩
      change event :: events G read tail = event :: word
      exact congrArg (List.cons event) labels

/-- Source execution and transform interpretation agree in both directions. -/
theorem run_iff (word : List (Event V)) (live target : Multiset V) (clock : Nat) :
    run G word live = some target ↔
      ∃ execution : (machine G read).step.Run (clock, live),
        execution.last.2 = target ∧ events G read execution = word := by
  rw [run_eq_some_iff]
  constructor
  · intro path
    exact lifts_path G read path clock
  · rintro ⟨execution, last, labels⟩
    have path := reflects_run G read execution
    simpa only [last, labels] using path

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DistinctionHistory

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DistinctionHistory.Controls
open Mettapedia.Cybernetics.DistinctionCalculus.History
open Mettapedia.GSLT.Distinction.HistoryGrammar

def grammar : Grammar Bool := ⟨Bool.not, fun x y => x && y⟩
def program : List (Event Bool) := [.fork false, .evolve false, .merge false true, .erase false]

theorem four_events_run : run grammar program {false} = some 0 := by decide

theorem four_events_on_transform :
    ∃ execution : (machine grammar Multiset.card).step.Run (0, {false}),
      execution.last.2 = 0 ∧ events grammar Multiset.card execution = program :=
  (run_iff grammar Multiset.card program {false} 0 0).mp four_events_run

theorem merge_needs_two_occurrences : step grammar (.merge false false) {false} = none := by decide

theorem no_double_consumption (target : Nat × Multiset Bool) :
    ¬ Race.Generic.Moves (machine grammar Multiset.card).step.toStep DistinctionFinite.Machine.offers
      (0, {false}) (.merge false false) target := by
  intro moved
  have source := (moves_iff grammar Multiset.card _ _ _).mp moved |>.2
  have ran := (step_eq_some_iff grammar _ _ _).mpr source
  rw [merge_needs_two_occurrences] at ran
  cases ran

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DistinctionHistory.Controls
