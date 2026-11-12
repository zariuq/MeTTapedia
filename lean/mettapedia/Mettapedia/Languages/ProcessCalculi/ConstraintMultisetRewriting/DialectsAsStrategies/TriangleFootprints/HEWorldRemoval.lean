import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.HEOnTheStep.NamedDifferences

/-!
# HE's one-occurrence removal on HE's own machine

H1's removal control (`HEOnTheStep.NamedDifferences.removal`) compared PeTTa's machine with HE's
space operation `HE.Space.remove`, not with HE's machine. Here the removal runs on HE's world
machine (`HEOnTheStep.heWorldMachine`) through a concrete world service.

* `removalService`: a world service whose native `remove-atom` takes one occurrence of its
  argument from the world (`HE.Space.remove`) and answers `()`; its world is HE's space.
* `he_removes_one_occurrence`: on a space holding `(p a)` twice, HE's world machine steps by the
  native call `(call-native remove-atom space (p a))` to the space holding `(p a)` once.
* `removal_outcome_unique`: every native outcome of this service on that space leaves one `(p a)`.
* `removal_on_the_step`: from every store representing that configuration the step fires (a writing
  rule, taking the world occurrence and making the new one) to a store whose world holds `(p a)`
  once.
* `removal_difference_on_machines`: **the removal difference on both machines**: HE's machine
  leaves one `(p a)`, PeTTa's request takes both rows and leaves none.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints

namespace WorldRemoval

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Mettapedia.Languages.MeTTa.HE (Space)
open Mettapedia.Languages.MeTTa.HE.RecursiveMachine.Contextual (WorldLocalStepWith)
open Mettapedia.Languages.MeTTa.HE.RecursiveTasks.Contextual (Control Continuation)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed (Policy Result CastLookup WorldServices)
open HEOnTheStep (heWorldMachine he_world_local machine_to_store worldsOf worldsOf_encode Store
  Represents StoreStep)
open MeTTaCalculus.OccurrenceCommits (labels)

/-- `(p a)`. -/
def pa : Atom := .expression [.symbol "p", .symbol "a"]

/-- `()`, the answer of a removal. -/
def unitValue : Entry.Value := .expression .active []

/-- **A world service with one-occurrence removal**: the native call `remove-atom` takes one
occurrence of its argument from the space (`HE.Space.remove`) and answers `()`. -/
def removalService : WorldServices Unit Space where
  contextPayload _ := .custom "Space" "self"
  nativeCall _ world name _ argument frame results after :=
    name = .symbol "remove-atom" ∧ after = world.remove argument ∧
      results = [(unitValue, frame)]

/-- The world is the space itself, at the one context. -/
def view : Space → Unit → Space := fun world _ => world

/-- `(call-native remove-atom space (p a))` as pending minimal work. -/
def removeCall (live : List Atom) (scope : List String) (caller : Option Atom)
    (readiness : Entry.Status)
    (activation : Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed.Frame) : Control Unit :=
  .work (.minimal live scope caller
    (.expression readiness [.symbol "call-native", .symbol "remove-atom", .symbol "space",
      .expression .active [.symbol "p", .symbol "a"]]) activation)

variable {dispatch : Mettapedia.Languages.MeTTa.HE.Spec.Eval.GroundedDispatch} {lookup : CastLookup}
  {policy : Policy}

/-- **HE's machine removes one occurrence.** On a space holding `(p a)` twice, HE's world machine
steps by the native removal to the space holding `(p a)` once. -/
theorem he_removes_one_occurrence (live : List Atom) (scope : List String) (caller : Option Atom)
    (readiness : Entry.Status)
    (activation : Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed.Frame) :
    (heWorldMachine view removalService dispatch lookup policy ()).Step
      ⟨Space.ofList [pa, pa], removeCall live scope caller readiness activation, [], []⟩
      ⟨Space.ofList [pa], .returning [(unitValue, activation)], [], []⟩ :=
  .internal (WorldLocalStepWith.native ⟨by simp [Entry.Value.erase],
    by simp [Entry.Value.erase, Space.remove, Space.ofList, pa], rfl⟩)

/-- **Every native outcome of the service on that space leaves one `(p a)`.** -/
theorem removal_outcome_unique {function : Atom}
    {activation : Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed.Frame} {results : List Result}
    {after : Space}
    (outcome : removalService.nativeCall () (Space.ofList [pa, pa]) (.symbol "remove-atom") function
      pa activation results after) :
    after = Space.ofList [pa] ∧ results = [(unitValue, activation)] := by
  obtain ⟨_, removed, answered⟩ := outcome
  exact ⟨removed.trans (by decide +kernel), answered⟩

/-- **The removal on the step.** From every store representing the configuration, the step under
the rules of HE's world machine fires to a store whose world holds `(p a)` once. -/
theorem removal_on_the_step (live : List Atom) (scope : List String) (caller : Option Atom)
    (readiness : Entry.Status) (activation : Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed.Frame)
    {S : Store Space (Control Unit) Continuation Result}
    (represented : Represents S
      ⟨Space.ofList [pa, pa], removeCall live scope caller readiness activation, [], []⟩) :
    ∃ S', StoreStep (heWorldMachine view removalService dispatch lookup policy ()) S S' ∧
      worldsOf (labels Prod.fst S'.present) = {Space.ofList [pa]} := by
  obtain ⟨S', fires, here⟩ := machine_to_store (he_world_local ()) represented
    (he_removes_one_occurrence (dispatch := dispatch) (lookup := lookup) (policy := policy)
      live scope caller readiness activation)
  exact ⟨S', fires, by rw [here.2, worldsOf_encode]⟩

open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.PeTTa.RunsAsFirings

/-- **The removal difference on both machines.** On `(p a)` stored twice, HE's world machine with
one-occurrence removal leaves one `(p a)`; PeTTa's `remove-atom` is one request taking both rows,
and its store is left empty. -/
theorem removal_difference_on_machines (live : List Atom) (scope : List String)
    (caller : Option Atom) (readiness : Entry.Status)
    (activation : Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed.Frame) :
    (heWorldMachine view removalService dispatch lookup policy ()).Step
        ⟨Space.ofList [pa, pa], removeCall live scope caller readiness activation, [], []⟩
        ⟨Space.ofList [pa], .returning [(unitValue, activation)], [], []⟩ ∧
      (requests rowSupply HEOnTheStep.NamedDifferences.noProgram 30
          (Streaming.enter { state := HEOnTheStep.NamedDifferences.dupStore }
            HEOnTheStep.NamedDifferences.removePa)
          (Row.load 0 HEOnTheStep.NamedDifferences.dupAtoms)).map RunsAsFirings.Controls.shape =
        [([⟨0, .self, pa⟩, ⟨1, .self, pa⟩], [], [])] ∧
      (Streaming.advance HEOnTheStep.NamedDifferences.noProgram 30
        (Streaming.enter { state := HEOnTheStep.NamedDifferences.dupStore }
          HEOnTheStep.NamedDifferences.removePa)).world.state.core = [] :=
  ⟨he_removes_one_occurrence live scope caller readiness activation,
    HEOnTheStep.NamedDifferences.removal.2.1, HEOnTheStep.NamedDifferences.removal.2.2⟩

end WorldRemoval

#print axioms WorldRemoval.he_removes_one_occurrence
#print axioms WorldRemoval.removal_outcome_unique
#print axioms WorldRemoval.removal_on_the_step
#print axioms WorldRemoval.removal_difference_on_machines

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints
