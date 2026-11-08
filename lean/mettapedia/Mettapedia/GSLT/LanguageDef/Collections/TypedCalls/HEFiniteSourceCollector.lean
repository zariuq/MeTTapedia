import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEFiniteSuperposeSquare
import Mettapedia.Languages.MeTTa.HE.CeTTaRuntimeContracts

/-!
# A source-earned typed producer in the retained collapse collector

The reached collector receives its held source operand. Its child is the
existing checked scoped worker, with only its final configuration relabelled
as a completed service reply. The child configuration, resource requests and
ordered publications remain present throughout execution.

For every finite integer list, the child starts from the actual unevaluated
sq(superpose(...)) expression and is proved to finish. No finished child
array or whole-expression equality is an admission premise. Empty completion
is distinguished from suspension, then omitted by the existing collector.

This closes the retained collector boundary. The standard-library collapse
macro's context-space/chain/fold lowering and native frame/array realization
are separate obligations. The source uses an empty root record and pure
mathematical integer multiplication; it is not a native overflow theorem.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEFiniteSourceCollector

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE.RecursiveTasks
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open TypedSquareCollection HEFiniteSuperposeSource HEFiniteSuperposeSquare

open CeTTaRuntimeContracts.InstructionControl

structure Request where
  operand : Atom
  deriving DecidableEq, Repr

def readRequest : Atom → Option Request
  | .expression [.symbol "collapse", operand] => some ⟨operand⟩
  | _ => none

def Request.source (request : Request) : Atom := apply "collapse" [request.operand]

def request (inputs : List Int) : Request := ⟨squareSuperpose inputs⟩

theorem read_source (inputs : List Int) : readRequest (surface inputs) = some (request inputs) := rfl

theorem read_request_sound {source : Atom} {selected : Request}
    (read : readRequest source = some selected) : source = selected.source := by
  unfold readRequest at read
  split at read
  · cases read
    rfl
  · cases read

def load (request : Request) : Configuration :=
  Configuration.initial space (.atom request.operand Atom.undefinedType Bindings.empty 22 [])

def callerBindings (_request : Request) : Bindings := Bindings.empty

def materialized (results : ResultSet) : List Collapse.MaterializedOutcome :=
  results.map fun result => ⟨some result.1, result.2⟩

def completed (inputs : List Int) : Collapse.Completed Unit := ⟨(), materialized (sourceResults inputs)⟩

def finish (state : Configuration) : Reply (Collapse.Completed Unit) Empty :=
  .returned ⟨(), materialized state.emitted⟩

def child := worker.relabel id finish id

def collector (services : Spec.Eval.Minimal.Services) :=
  Collapse.handled services callerBindings child load

def active (input : Request) := Collapse.active (World := Unit) (Failure := Empty) input (load input)

def start (input : Request) : HandledState (Collapse.Parent Request Unit Empty) Configuration Request :=
  .running (.enter input)

/-- Only a real worker completion constructs the child reply. Relabelling
does not turn a pending resource request or exhausted prefix into completion. -/
theorem child_finishes (inputs : List Int) :
    child.run (sourceBudget inputs) (load (request inputs)) =
      (sourceResults inputs, .finished (.returned (completed inputs))) := by
  change child.run (sourceBudget inputs) (initial inputs) = _
  rw [child, worker.run_relabel, finite_source_finishes]
  simp [Outcome.relabel, finish, completed]

theorem completed_rows_exact (inputs : List Int) :
    Collapse.results (completed inputs).rows = inputs.map squareResult := by
  cases inputs with
  | nil => rfl
  | cons first rest =>
      simp [completed, sourceResults, materialized, Collapse.results, List.filterMap_map,
        Collapse.MaterializedOutcome.kept, squareResult, num, Atom.empty, Function.comp_def]

theorem completed_pack_exact (services : Spec.Eval.Minimal.Services) (inputs : List Int) :
    Collapse.pack services (completed inputs).rows = Spec.Eval.Minimal.encodeResults services (inputs.map squareResult) := by
  rw [Collapse.pack_exact, completed_rows_exact]

/-- The existing collector handles the actual source-derived child, and
closes only after its full return and the collector's own closing step. -/
theorem collector_finishes_active (services : Spec.Eval.Minimal.Services) (inputs : List Int) :
    ∃ used ≤ sourceBudget inputs + 1,
      (collector services).run used (active (request inputs)) =
        ((sourceResults inputs).map Collapse.Event.child ++ [Collapse.Event.replied (.returned (completed inputs))],
          .finished (.aggregate (request inputs) ()
            (Spec.Eval.Minimal.encodeResults services (inputs.map squareResult), Bindings.empty))) := by
  obtain ⟨used, bound, ran⟩ := Collapse.complete_after_child services callerBindings child load
    (sourceBudget inputs) (request inputs) (load (request inputs))
    (sourceResults inputs) (completed inputs) (child_finishes inputs)
  refine ⟨used, bound, ?_⟩
  rw [completed_pack_exact] at ran
  simpa only [collector, active, callerBindings, completed] using ran

theorem collector_enters (services : Spec.Eval.Minimal.Services) (input : Request) :
    (collector services).step (start input) =
      some (.publish [Collapse.Event.entered input] (active input)) := rfl

/-- The loader begins from the held operand, and the full handled run earns
the aggregate. Ordered child publications remain visible in the trace. -/
theorem collector_finishes (services : Spec.Eval.Minimal.Services) (inputs : List Int) :
    ∃ used ≤ sourceBudget inputs + 2,
      (collector services).run used (start (request inputs)) =
        ([Collapse.Event.entered (request inputs)] ++
          (sourceResults inputs).map Collapse.Event.child ++ [Collapse.Event.replied (.returned (completed inputs))],
          .finished (.aggregate (request inputs) ()
            (Spec.Eval.Minimal.encodeResults services (inputs.map squareResult), Bindings.empty))) := by
  obtain ⟨used, bound, ran⟩ := collector_finishes_active services inputs
  refine ⟨used + 1, by omega, ?_⟩
  rw [(collector services).run_succ_publish (collector_enters services (request inputs)), ran]
  simp only [List.append_assoc]

/-- A suspended source execution remains the retained child of this same
collector. Its already published prefix is neither discarded nor replayed. -/
theorem collector_paused (services : Spec.Eval.Minimal.Services) (inputs : List Int)
    (fuel : Nat) (published : ResultSet) (saved : Configuration)
    (paused : worker.run fuel (initial inputs) = (published, .exhausted saved)) :
    (collector services).run fuel (active (request inputs)) =
      (published.map Collapse.Event.child,
        .exhausted (Collapse.active (World := Unit) (Failure := Empty) (request inputs) saved)) := by
  have childPaused : child.run fuel (load (request inputs)) = (published, .exhausted saved) := by
    change child.run fuel (initial inputs) = _
    rw [child, worker.run_relabel, paused]
    simp [Outcome.relabel]
  exact Collapse.paused_child_exact services callerBindings child load fuel (request inputs)
    (load (request inputs)) saved published childPaused

theorem returned_frontier_not_aggregate (services : Spec.Eval.Minimal.Services)
    (first : Int) (rest : List Int) :
    (collector services).run (97 * (first :: rest).length + 59) (active (request (first :: rest))) =
      ([], .exhausted (Collapse.active (World := Unit) (Failure := Empty) (request (first :: rest))
        ⟨space, .returning ((first :: rest).map squareResult), [], []⟩)) :=
  collector_paused services (first :: rest) _ [] _ (source_returns first rest)

/-- Ground numeric outputs are unchanged by the binding application that
the standard-library collapse readback performs on each collected pair.
This is a readback law, not a proof of that whole macro's execution. -/
theorem surface_values_readback (inputs : List Int) (depth : Nat) :
    (Collapse.results (completed inputs).rows).map (fun result => result.2.applyFull result.1 depth) =
      inputs.map (fun n => num (n * n)) := by
  rw [completed_rows_exact, List.map_map]
  apply List.map_congr_left
  intro n _
  exact CompletedDelivery.applyFull_ground (squareBindings n) depth (num (n * n)) rfl

namespace Controls

def diagnostic : Atom := Atom.error (.symbol "source-call") (.symbol "failure")

/-- Collector readback omits Empty but retains both errors and successful
values, with their original records. It is not another priority selector. -/
theorem three_class_readback (bindings : Bindings) :
    Collapse.results (materialized
      [(Atom.empty, bindings), (diagnostic, bindings), (num 4, bindings)]) =
      [(diagnostic, bindings), (num 4, bindings)] := rfl

/-- A collector cannot recover an error discarded by an earlier binary
selector. The numeric source profile's earned clean frontiers are essential. -/
theorem earlier_binary_selection_not_repaired (bindings : Bindings) :
    HEInvocationFrontier.normalize (HEReturns.keep [(Atom.empty, bindings), (diagnostic, bindings)]) =
      [(Atom.empty, bindings)] ∧
    HEInvocationFrontier.normalize [(Atom.empty, bindings), (diagnostic, bindings)] =
      [(diagnostic, bindings)] := by constructor <;> rfl

theorem empty_completed_is_empty_collection (services : Spec.Eval.Minimal.Services) :
    Collapse.pack services (completed []).rows = .expression [] := rfl

theorem duplicate_occurrences_and_records (services : Spec.Eval.Minimal.Services) :
    Collapse.pack services (completed [2, -2, 2]).rows =
      Spec.Eval.Minimal.encodeResults services [squareResult 2, squareResult (-2), squareResult 2] :=
  completed_pack_exact services [2, -2, 2]

theorem equal_values_different_snapshots (services : Spec.Eval.Minimal.Services)
    (laws : Spec.Eval.Minimal.ServiceLaws services) :
    Spec.Eval.Minimal.encodeResult services (squareResult 2) ≠
      Spec.Eval.Minimal.encodeResult services (squareResult (-2)) := by
  intro same
  have records := congrArg Prod.snd (Collapse.encodeResult_injective services laws same)
  exact TypedSquareCollection.Controls.equal_values_distinct_records.2 records

theorem malformed_surface_declined :
    readRequest (apply "collapse" []) = none ∧
      readRequest (apply "collapse" [.symbol "one", .symbol "two"]) = none := by decide

theorem cancelled_no_aggregate (services : Spec.Eval.Minimal.Services) (input : Request) :
    (Collapse.parent (World := Unit) (Receipt := ResultPair) (Failure := Empty) services callerBindings).step
      (.returned input .cancelled) = some (.finish (.cancelled input)) := rfl

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEFiniteSourceCollector
