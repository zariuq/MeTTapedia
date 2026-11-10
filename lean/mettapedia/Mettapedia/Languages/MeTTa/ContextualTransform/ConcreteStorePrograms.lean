import Mettapedia.Languages.MeTTa.ContextualTransform.AdaptiveStorePrograms
import Mettapedia.Data.List.FreshOccurrenceAllocation

/-!
# Executable occurrence allocation and connected store-program controls

These clients execute the actual ordered transform step through the existing
adaptive interpreter. Their source expectations are computed independently.
The allocation profile is fresh against current live identities. It is a
value-observer model, not a policy for retained historical cursors or receipts.
The generic interpretation permits a stronger supply when those observers exist.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.ContextualTransform.ConcreteStorePrograms

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open Interface
open Mettapedia.Machines
open ReadOnlyQuery (Program)
open Mettapedia.Data.List.OrderedOccurrenceCursor (Occurrence)
open AdaptiveStorePrograms

abbrev Id := Occurrence Atom

def label : Id → Atom := Occurrence.value

def allocation : Allocation label where
  make := Mettapedia.Data.List.FreshOccurrenceAllocation.allocate
  values := Mettapedia.Data.List.FreshOccurrenceAllocation.allocate_values
  distinct := Mettapedia.Data.List.FreshOccurrenceAllocation.allocate_nodup
  fresh := Mettapedia.Data.List.FreshOccurrenceAllocation.fresh

/-- A nonempty ambient equation store remains meaningful throughout the run. -/
def knowledge : EquationStore Atom := [(.var "ambient", .symbol "protected")]

theorem consistent : PeTTaStoreSelection.atomFrames.Solvable (a := PUnit.unit) knowledge := by
  refine ⟨PUnit.unit, SubstitutionAlgebra.Insertion.single "ambient" (.symbol "protected"), ?_⟩
  intro equation member
  have same : equation = (.var "ambient", .symbol "protected") := List.mem_singleton.mp member
  subst equation
  simp [Frames.Solves, PeTTaStoreSelection.atomFrames, Frames.ofSubstitution,
    MetaMeTTaComparison.atomAction, SubstitutionAlgebra.Insertion.single,
    SubstitutionAlgebra.subst]

def initial : State Id := ⟨[], List.nodup_nil⟩

def firstValue : Reply → Atom
  | .rows (value :: _) => value
  | _ => .symbol "no-first-value"

/-- The removal predicate depends on the preceding query reply. -/
def adaptive : Program Command Reply (List Reply) :=
  .read (.append [.symbol "a", .symbol "b", .symbol "a"]) fun written =>
    .read (.query (fun _ => true)) fun observed =>
      .read (.remove (fun value => value == firstValue observed)) fun removed =>
        .read (.query (fun _ => true)) fun remaining =>
          .pure [written, observed, removed, remaining]

def expected : List Reply :=
  [.count 3, .rows [.symbol "a", .symbol "b", .symbol "a"],
    .changed true, .rows [.symbol "b"]]

theorem independent_source_answers : (QueryState.run source adaptive []).answer = expected := by
  decide +kernel

theorem target_answers :
    (QueryState.run (target label knowledge consistent allocation) adaptive initial).answer = expected := by
  have agreement := adaptive_exact label knowledge consistent allocation adaptive initial
  have answers := congrArg QueryState.Observation.answer agreement
  exact answers.symm.trans independent_source_answers

theorem target_final_store :
    decode label (QueryState.run (target label knowledge consistent allocation) adaptive initial).state =
      [.symbol "b"] := by
  have agreement := adaptive_exact label knowledge consistent allocation adaptive initial
  have worlds := congrArg QueryState.Observation.state agreement
  exact worlds.symm.trans (by decide +kernel)

theorem actual_run_keeps_ambient_knowledge :
    (realization label knowledge consistent allocation adaptive initial).last.1 = knowledge := by
  rw [realization_last]

theorem actual_run_has_four_events :
    (realization label knowledge consistent allocation adaptive initial).word.length = 4 := by
  rw [realization_length]
  have agreement := adaptive_exact label knowledge consistent allocation adaptive initial
  have history := congrArg (fun observation => observation.reads.length) agreement
  exact history.symm.trans (by decide +kernel)

/-- Treating the source as a set would lose one observed answer occurrence. -/
theorem deduplicated_observation_is_wrong :
    (QueryState.run source adaptive []).answer ≠
      [.count 3, .rows [.symbol "a", .symbol "b"], .changed true, .rows [.symbol "b"]] := by
  decide +kernel

/-- Publication is required; replacing removal by an identity update would
leave three rows, not the actual target's single surviving row. -/
theorem skipping_removal_is_wrong :
    decode label (QueryState.run (target label knowledge consistent allocation) adaptive initial).state ≠
      [.symbol "a", .symbol "b", .symbol "a"] := by
  rw [target_final_store]
  decide

end Mettapedia.Languages.MeTTa.ContextualTransform.ConcreteStorePrograms
