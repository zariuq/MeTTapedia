import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DistinctionObserver
import Mettapedia.GSLT.Dynamics.ObservationDiscipline
import Mettapedia.GSLT.Core.ObservationControlContract

/-!
# Witness-preserving, independently failing observation axes

Transform runs feed the existing observation-discipline and evaluator-control
interfaces. Indexed observations collect every axis on the same event word,
retaining each axis's success or failure separately. A failing axis does not
erase another axis's value or witnesses. The full event word is available as
a retained discipline; changing its value readout does not rerun effects.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DistinctionWitnesses
open Interface
open Mettapedia.GSLT.Dynamics
open Mettapedia.GSLT.Core
open ObservationDemandControl

universe uE uI uC uV uOb uT uH uO uS uF uG

/-- Each axis's optional witness is retained, even if another axis rejects the history. -/
def indexed {Event : Type uE} {Index : Type uI}
    (axes : Index → ObservationDiscipline.{uE, uC, uV} Event) : ObservationDiscipline Event where
  collection := {
    Container := (i : Index) → Option (axes i).collection.Container
    collect events := some (fun i => (axes i).collection.collect events) }
  Value := (i : Index) → Option (axes i).Value
  readout witnesses i := (witnesses i).map (axes i).readout

theorem indexed_observe {Event : Type uE} {Index : Type uI}
    (axes : Index → ObservationDiscipline.{uE, uC, uV} Event) (events : List Event) :
    (indexed axes).observe events = some (fun i => (axes i).observe events) := rfl

/-- Combined equality is exactly independent equality of all the optional readings. -/
theorem indexed_eq_iff {Event : Type uE} {Index : Type uI}
    (axes : Index → ObservationDiscipline.{uE, uC, uV} Event) (xs ys : List Event) :
    (indexed axes).observe xs = (indexed axes).observe ys ↔
      ∀ i, (axes i).observe xs = (axes i).observe ys := by
  constructor
  · intro same
    exact congrFun (Option.some.inj same)
  · intro same
    exact congrArg some (funext same)

/-- A discipline retaining the actual event word before a chosen readout. -/
def retained {Event : Type uE} {Value : Type uV} (read : List Event → Value) :
    ObservationDiscipline Event where
  collection := { Container := List Event, collect := some }
  Value := Value
  readout := read

theorem retained_witness_injective {Event : Type uE} {Value : Type uV}
    (read : List Event → Value) : Function.Injective (retained read).collection.collect :=
  fun _ _ same => Option.some.inj same

/-- Observation re-reading operates on the retained history, not on a new execution. -/
theorem retained_reread {Event : Type uE} {Value : Type uV} (read : List Event → Value)
    (events : List Event) : (retained read).observe events = some (read events) := rfl

section Runs
variable {Obj : Type uOb} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uO} [DecidableEq O] {State : Type uS}
  {Fir : State → Type uF} (P : Interface.Step X O State Fir)

abbrev Event := (s : State) × Fir s

def onRun (discipline : ObservationDiscipline (Event (Fir := Fir))) {s : State} (run : P.Run s) :
    Option discipline.Value := discipline.observe run.word

/-- History alone does not determine endpoints, especially for an empty run. -/
def onRunWithEndpoints (discipline : ObservationDiscipline (Event (Fir := Fir)))
    {s : State} (run : P.Run s) : State × Option discipline.Value × State :=
  (s, onRun P discipline run, run.last)

theorem endpoints_retained (discipline : ObservationDiscipline (Event (Fir := Fir)))
    {s t : State} (first : P.Run s) (second : P.Run t)
    (same : onRunWithEndpoints P discipline first = onRunWithEndpoints P discipline second) :
    s = t ∧ onRun P discipline first = onRun P discipline second ∧ first.last = second.last :=
  ⟨congrArg Prod.fst same, congrArg (fun x => x.2.1) same, congrArg (fun x => x.2.2) same⟩

theorem onRun_mapValue (discipline : ObservationDiscipline (Event (Fir := Fir)))
    {Value : Type*} (summarize : discipline.Value → Value) {s : State} (run : P.Run s) :
    onRun P (discipline.mapValue summarize) run = (onRun P discipline run).map summarize :=
  discipline.mapValue_observe summarize run.word

/-- Reuse the evaluator's contract; there is no second pruning-authority mechanism. -/
def controlContract {Guard : Type uG} (discipline : ObservationDiscipline (Event (Fir := Fir)))
    (demand : ObservationDemand Guard) :
    ObservationControlContract.Contract (Event (Fir := Fir)) Guard (Option discipline.Value) where
  observer := ⟨discipline.observe⟩
  demand := demand

theorem control_preserves_runs {Guard : Type uG} {Receipt : Type*}
    (discipline : ObservationDiscipline (Event (Fir := Fir))) (demand : ObservationDemand Guard)
    (change : ObservationIndexedPruning.Change (Event (Fir := Fir)) Receipt)
    (licensed : (controlContract discipline demand).Preserves change)
    {s t : State} (first : P.Run s) (second : P.Run t)
    (before : change.source = first.word) (after : change.target = second.word) :
    onRun P discipline first = onRun P discipline second := by
  simpa only [ObservationControlContract.Contract.Preserves,
    ObservationIndexedPruning.LawfulAt, controlContract, before, after, onRun] using licensed

end Runs

namespace Controls

def success : ObservationDiscipline Nat := retained List.length
def failure : ObservationDiscipline Nat where
  collection := { Container := Unit, collect := fun _ => none }
  Value := Nat
  readout _ := 0

def axes : Bool → ObservationDiscipline Nat := fun i => if i then success else failure

/-- A strict product masks success when the other axis fails; indexed collection retains it. -/
theorem independent_failure :
    (success.prod failure).observe [1, 2] = none ∧
      ((indexed axes).observe [1, 2]).map (fun readings => readings true) = some (some (2 : Nat)) ∧
      ((indexed axes).observe [1, 2]).map (fun readings => readings false) = some none :=
  ⟨rfl, rfl, rfl⟩

theorem equal_scores_different_witnesses :
    success.observe [1, 2] = success.observe [2, 1] ∧
      success.collection.collect [1, 2] ≠ success.collection.collect [2, 1] := by
  constructor
  · rfl
  · change some ([1, 2] : List Nat) ≠ some [2, 1]
    decide

end Controls
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DistinctionWitnesses
