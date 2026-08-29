import Mettapedia.GSLT.Core.ObservationControlContract
import Mettapedia.GSLT.Dynamics.ObservationDiscipline

/-!
# Observation-control contracts as GSLT observation disciplines

An observation-control contract over transition occurrences induces the
standard observation discipline which retains one complete occurrence history
and applies the contract's declared observer to it.  This is the semantic
attachment point to a GSLT: the transition system remains the sole source of
steps, while the contract determines the client view and completion demand.

Multiple observation axes share the same retained history.  They are not run
as independent computations and then paired.  This matters for values,
coverage, faults, and provenance, whose coordinates must describe one run.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.ObservationControlDiscipline

open Mettapedia.Cybernetics
open Mettapedia.GSLT
open Mettapedia.GSLT.Core.ObservationControlContract

universe uEvent uGuard uView uOtherView uTerm

variable {OtherView : Type uOtherView}

/-- The total collector retaining one event history exactly. -/
def fullHistoryCollector (Event : Type uEvent) : WitnessCollector Event where
  Container := List Event
  collect := some

@[simp] theorem fullHistoryCollector_collect
    {Event : Type uEvent} (events : List Event) :
    (fullHistoryCollector Event).collect events = some events :=
  rfl

theorem fullHistoryCollector_total (Event : Type uEvent) :
    (fullHistoryCollector Event).Total := by
  intro events
  exact ⟨events, rfl⟩

/-- Interpret a contract as the canonical one-history observation discipline.
The completion demand remains in the contract and is not confused with event
collection. -/
def ofContract {Event : Type uEvent} {Guard : Type uGuard}
    {View : Type uView} (contract : Contract Event Guard View) :
    ObservationDiscipline Event where
  collection := fullHistoryCollector Event
  Value := View
  readout := contract.observer.observe

@[simp] theorem ofContract_observe
    {Event : Type uEvent} {Guard : Type uGuard} {View : Type uView}
    (contract : Contract Event Guard View) (events : List Event) :
    (ofContract contract).observe events =
      some (contract.observer.observe events) :=
  rfl

/-- Forgetting an observation coordinate commutes exactly with the existing
value-map operation on observation disciplines. -/
theorem ofContract_postcompose
    {Event : Type uEvent} {Guard : Type uGuard} {View : Type uView}
    (contract : Contract Event Guard View) (summarize : View -> OtherView) :
    ofContract (contract.postcompose summarize) =
      (ofContract contract).mapValue summarize :=
  rfl

/-- Adding an axis observes both coordinates from the same retained event
history. -/
@[simp] theorem ofContract_addAxis_observe
    {Event : Type uEvent} {Guard : Type uGuard} {View : Type uView}
    (contract : Contract Event Guard View)
    (axis : Observer (List Event) OtherView) (events : List Event) :
    (ofContract (contract.addAxis axis)).observe events =
      some (contract.observer.observe events, axis.observe events) :=
  rfl

/-- An observation-control contract whose items are the proof-relevant
one-step occurrences of a GSLT. -/
abbrev GSLTContract (system : GSLT.{uTerm})
    (Guard : Type uGuard) (View : Type uView) :=
  Contract system.LabeledStep Guard View

/-- The canonical GSLT observation supplied by a contract. -/
def ofGSLTContract {system : GSLT.{uTerm}} {Guard : Type uGuard}
    {View : Type uView} (contract : GSLTContract system Guard View) :
    GSLTObservation system :=
  ofContract contract

@[simp] theorem ofGSLTContract_observe
    {system : GSLT.{uTerm}} {Guard : Type uGuard} {View : Type uView}
    (contract : GSLTContract system Guard View)
    (events : List system.LabeledStep) :
    (ofGSLTContract contract).observe events =
      some (contract.observer.observe events) :=
  rfl

/-! ## One-run positive and negative controls -/

namespace Canary

inductive Event where
  | answer (value : Bool)
  | fault
deriving DecidableEq, Repr

def values : Observer (List Event) (List Bool) where
  observe := List.filterMap fun event =>
    match event with
    | .answer value => some value
    | .fault => none

def faults : Observer (List Event) Nat where
  observe := fun events => events.count .fault

def valueContract : Contract Event Unit (List Bool) where
  observer := values
  demand := { completion := .completeBag }

def valueAndFaultContract : Contract Event Unit (List Bool × Nat) :=
  valueContract.addAxis faults

/-- Both coordinates are read from one event history. -/
theorem values_and_faults_share_run :
    (ofContract valueAndFaultContract).observe
        [.answer true, .fault, .answer false] =
      some ([true, false], 1) :=
  rfl

/-- Pairing coordinates from different histories can produce a report that
the one-history discipline did not observe. -/
theorem separate_histories_can_manufacture_report :
    (values.observe [.answer true], faults.observe [.fault]) = ([true], 1) /\
      (ofContract valueAndFaultContract).observe [.answer true] ≠
        some ([true], 1) /\
      (ofContract valueAndFaultContract).observe [.fault] ≠
        some ([true], 1) := by
  simp [ofContract, valueAndFaultContract, valueContract, values, faults,
    fullHistoryCollector, ObservationDiscipline.observe,
    Contract.addAxis]

end Canary

#print axioms fullHistoryCollector_total
#print axioms ofContract_postcompose
#print axioms ofContract_addAxis_observe
#print axioms ofGSLTContract_observe
#print axioms Canary.values_and_faults_share_run
#print axioms Canary.separate_histories_can_manufacture_report

end Mettapedia.GSLT.Dynamics.ObservationControlDiscipline
