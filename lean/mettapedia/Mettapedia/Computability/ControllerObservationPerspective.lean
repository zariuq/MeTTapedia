import Mettapedia.Computability.FragmentwiseComputationalTrinity
import Mettapedia.GSLT.Core.BranchCaptureAlgebra
import Mettapedia.GSLT.Core.OpenTotalityObservation

/-!
# Controller switching at an observation perspective

A controller chooses which authorized occurrence to expand; an observation
perspective chooses which distinctions in the resulting history remain
visible.  These are different axes.  This module gives their smallest common
boundary.

An observation perspective is a view of an exact occurrence stream.  A map of
perspectives explicitly forgets information, such as stream order when moving
to an occurrence bag.  Controller state can change at a live snapshot without
changing the underlying occurrence frontier.  If the resulting hybrid run
completes, the additive occurrence bag is unchanged.  At a bounded prefix,
however, switching controllers may change even the observed answer bag.

The theorem is semantic admission, not a physical zero-cost claim.  A runtime
still needs capture authority for the branch state and may have to build a
deque or scoring index.  `BranchCaptureAlgebra` keeps that storage obligation
separate from the observation theorem proved here.
-/

namespace Mettapedia.Computability.ControllerObservationPerspective

open Mettapedia.GSLT.Core.BranchingTemporal
open Mettapedia.GSLT.Core.InferenceControl

universe uOccurrence uView

/-- A declared observation of an exact finite occurrence stream. -/
structure Perspective (Occurrence : Type uOccurrence) where
  View : Type uView
  observe : List Occurrence → View

/-- An explicit information-forgetting map between two perspectives on the
same occurrence history. -/
structure PerspectiveMap {Occurrence : Type uOccurrence}
    (source : Perspective.{uOccurrence, uView} Occurrence)
    (target : Perspective.{uOccurrence, uView} Occurrence) where
  project : source.View → target.View
  commutes : ∀ occurrences,
    project (source.observe occurrences) = target.observe occurrences

namespace Perspective

variable {Node Answer : Type*}

/-- Preserve the exact ordered answer stream while forgetting producer nodes. -/
def answerStream : Perspective (Emission Node Answer) where
  View := List Answer
  observe occurrences := occurrences.map Emission.value

/-- Forget order but retain every answer occurrence. -/
def answerBag : Perspective (Emission Node Answer) where
  View := Multiset Answer
  observe := eventBag

/-- Forgetting order is a declared map of observation perspectives. -/
def streamToBag : PerspectiveMap
    (answerStream (Node := Node) (Answer := Answer))
    (answerBag (Node := Node) (Answer := Answer)) where
  project := fun answers : List Answer => (answers : Multiset Answer)
  commutes := by
    intro occurrences
    rfl

end Perspective

/-! ## Completion-stable perspectives

An arbitrary observation of a prefix need not be controller invariant.  The
positive capability needed for controller switching is more specific: the
observation must factor through the completed occurrence bag.  This is a
property of the declared perspective, not a property of a controller name.
-/

/-- A perspective is insensitive to controller order at completion when it
is a readout of the exact occurrence bag.  The factorization retains the
readout explicitly; no quotient is installed as definitional equality. -/
structure FactorsThroughAnswerBag {Node Answer : Type*}
    (perspective : Perspective (Emission Node Answer)) where
  project : Multiset Answer → perspective.View
  factors : ∀ occurrences,
    perspective.observe occurrences = project (eventBag occurrences)

namespace Perspective

/-- The exact occurrence-bag perspective factors through itself. -/
def answerBagFactors {Node Answer : Type*} :
    FactorsThroughAnswerBag
      (answerBag (Node := Node) (Answer := Answer)) where
  project := id
  factors := by
    intro occurrences
    rfl

end Perspective

/-- A typed authorization for changing controller over a completed-bag
perspective.  Observation invariance and physical storage admission are
separate fields: neither can manufacture the other. -/
structure CompletionSwitchAuthority {Node Answer : Type*}
    (perspective : Perspective (Emission Node Answer))
    (available : Mettapedia.GSLT.Core.BranchCaptureAlgebra.CaptureCapacity)
    (requested : Mettapedia.GSLT.Core.BranchCaptureAlgebra.StorageMode) where
  observation : FactorsThroughAnswerBag perspective
  storage : Mettapedia.GSLT.Core.BranchCaptureAlgebra.Admitted available requested

/-- Optional evidence for advertising fair unbounded enumeration at a
completed-bag perspective.  This is not controller admission: every lawful
occurrence-preserving DFS, learned, or adversarial controller may execute
without this certificate.  The certificate is required only for the stronger
claim that every occurrence which remains reachable will eventually be
selected.

The controller itself need not be intrinsically fair.  A schedule may combine
an arbitrary learned, KBO, valuation, or depth-biased lane with a sufficiently
recurrent age lane and prove fairness for the composite clock. -/
structure FairUnboundedFrontierCertificate {Node Answer Memory : Type*}
    (system : BranchingSystem Node Answer)
    (controller : Controller Node Answer Memory)
    (roots : List Node)
    (perspective : Perspective (Emission Node Answer))
    (available : Mettapedia.GSLT.Core.BranchCaptureAlgebra.CaptureCapacity)
    (requested : Mettapedia.GSLT.Core.BranchCaptureAlgebra.StorageMode) where
  completion : CompletionSwitchAuthority perspective available requested
  fairness :
    Mettapedia.GSLT.Core.InferenceControl.Snapshot.FairFrom
      system controller roots

/-! ## Controller changes over one occurrence state -/

/-- Before a genuine choice exists, every lawful scheduler selects the same
sole occurrence.  This is the representation-minimal deterministic case; it
must not be described as depth-first search.  DFS, FIFO, weight, and learned
selection become distinct policies only once more than one occurrence is
live. -/
theorem scheduler_selected_singleton {Node : Type*}
    (scheduler : Scheduler Node) (node : Node) :
    Mettapedia.GSLT.Core.BranchingTemporal.selected scheduler [node] = some node := by
  unfold Mettapedia.GSLT.Core.BranchingTemporal.selected
  cases h : scheduler.reorder [node] with
  | nil =>
      have permutation := scheduler.reorder_complete [node]
      rw [h] at permutation
      simp at permutation
  | cons selected pending =>
      have selected_mem : selected ∈ [node] :=
        (scheduler.reorder_complete [node]).mem_iff.mp (by simp [h])
      have selected_eq : selected = node := by simpa using selected_mem
      simp [selected_eq]

/-- Attach controller memory to an existing controller-neutral search
snapshot.  No occurrence, event, or frontier element is copied or changed by
this semantic operation. -/
def withControllerMemory {Node Answer Memory : Type*}
    (search : Mettapedia.GSLT.Core.BranchingTemporal.Snapshot Node Answer)
    (memory : Memory) :
    Mettapedia.GSLT.Core.InferenceControl.Snapshot Node Answer Memory where
  search := search
  memory := memory

@[simp] theorem withControllerMemory_search
    {Node Answer Memory : Type*}
    (search : Mettapedia.GSLT.Core.BranchingTemporal.Snapshot Node Answer)
    (memory : Memory) :
    (withControllerMemory search memory).search = search :=
  rfl

/-- Switching controller and memory at a live occurrence snapshot preserves
the completed additive answer bag.  The first controller may run for any
finite prefix; the second may start with arbitrary valid private memory.  The
only semantic premise added at the switch is that the hybrid run eventually
closes its frontier. -/
theorem completed_bag_after_controller_switch
    {Node Answer FirstMemory SecondMemory : Type*}
    (system : BranchingSystem Node Answer)
    (first : Controller Node Answer FirstMemory)
    (second : Controller Node Answer SecondMemory)
    (denotation : AdditiveDenotation system)
    (roots : List Node) (firstFuel secondFuel : Nat)
    (secondMemory : SecondMemory)
    (complete :
      (Mettapedia.GSLT.Core.InferenceControl.Snapshot.run system second
        secondFuel
        (withControllerMemory
          (Mettapedia.GSLT.Core.InferenceControl.Snapshot.run system first
            firstFuel
            (Mettapedia.GSLT.Core.InferenceControl.Snapshot.initial first roots)
          ).search secondMemory)).search.frontier = []) :
    eventBag
        (Mettapedia.GSLT.Core.InferenceControl.Snapshot.run system second
          secondFuel
          (withControllerMemory
            (Mettapedia.GSLT.Core.InferenceControl.Snapshot.run system first
              firstFuel
              (Mettapedia.GSLT.Core.InferenceControl.Snapshot.initial first roots)
            ).search secondMemory)).search.events =
      foldValues denotation.value roots := by
  let initial :=
    Mettapedia.GSLT.Core.InferenceControl.Snapshot.initial first roots
  let firstResult :=
    Mettapedia.GSLT.Core.InferenceControl.Snapshot.run system first firstFuel
      initial
  let switched := withControllerMemory firstResult.search secondMemory
  let finished :=
    Mettapedia.GSLT.Core.InferenceControl.Snapshot.run system second secondFuel
      switched
  have firstPreserved :=
    Mettapedia.GSLT.Core.InferenceControl.Snapshot.account_run system first
      denotation firstFuel initial
  have secondPreserved :=
    Mettapedia.GSLT.Core.InferenceControl.Snapshot.account_run system second
      denotation secondFuel switched
  have preserved : account denotation finished.search = account denotation initial.search :=
    secondPreserved.trans firstPreserved
  have finishedComplete : finished.search.frontier = [] := complete
  unfold account at preserved
  rw [finishedComplete] at preserved
  simpa [finished, switched, firstResult, initial,
    Mettapedia.GSLT.Core.InferenceControl.Snapshot.initial,
    Mettapedia.GSLT.Core.BranchingTemporal.initial, foldValues, eventBag]
    using preserved

/-- Every perspective explicitly factored through the occurrence bag inherits
the hybrid-controller completion theorem.  The type theory can therefore
require this capability at a scope boundary and erase the proof after
admission; the runtime still owes the requested physical capture. -/
theorem completed_factored_observation_after_controller_switch
    {Node Answer FirstMemory SecondMemory : Type*}
    (system : BranchingSystem Node Answer)
    (first : Controller Node Answer FirstMemory)
    (second : Controller Node Answer SecondMemory)
    (denotation : AdditiveDenotation system)
    (perspective : Perspective (Emission Node Answer))
    (factored : FactorsThroughAnswerBag perspective)
    (roots : List Node) (firstFuel secondFuel : Nat)
    (secondMemory : SecondMemory)
    (complete :
      (Mettapedia.GSLT.Core.InferenceControl.Snapshot.run system second
        secondFuel
        (withControllerMemory
          (Mettapedia.GSLT.Core.InferenceControl.Snapshot.run system first
            firstFuel
            (Mettapedia.GSLT.Core.InferenceControl.Snapshot.initial first roots)
          ).search secondMemory)).search.frontier = []) :
    perspective.observe
        (Mettapedia.GSLT.Core.InferenceControl.Snapshot.run system second
          secondFuel
          (withControllerMemory
            (Mettapedia.GSLT.Core.InferenceControl.Snapshot.run system first
              firstFuel
              (Mettapedia.GSLT.Core.InferenceControl.Snapshot.initial first roots)
            ).search secondMemory)).search.events =
      factored.project (foldValues denotation.value roots) := by
  rw [factored.factors]
  exact congrArg factored.project
    (completed_bag_after_controller_switch system first second denotation roots
      firstFuel secondFuel secondMemory complete)

/-- A prepared multi-view portfolio has the same completion law.  Its queue
views may spend memory to make FIFO, LIFO, KBO, valuation, or learned
selection cheap, but every view is a complete permutation of one live
occurrence store.  The semantic result therefore depends only on the declared
bag-factored perspective; representation cost remains an independent receipt. -/
theorem completed_factored_portfolio_observation
    {Node Answer : Type*} {count : Nat}
    [NeZero count] [DecidableEq Node]
    (system : BranchingSystem Node Answer)
    (disciplines : Fin count →
      Mettapedia.GSLT.Core.WeightedOccurrenceControl.QueueDiscipline Node)
    (denotation : AdditiveDenotation system)
    (perspective : Perspective (Emission Node Answer))
    (factored : FactorsThroughAnswerBag perspective)
    (roots : List Node) (start : Fin count) (fuel : Nat)
    (complete :
      (Mettapedia.GSLT.Core.WeightedOccurrenceControl.PortfolioSnapshot.run
        system disciplines fuel
        (Mettapedia.GSLT.Core.WeightedOccurrenceControl.PortfolioSnapshot.initial
          disciplines roots start)).frontier.live = []) :
    perspective.observe
        (Mettapedia.GSLT.Core.WeightedOccurrenceControl.PortfolioSnapshot.run
          system disciplines fuel
          (Mettapedia.GSLT.Core.WeightedOccurrenceControl.PortfolioSnapshot.initial
            disciplines roots start)).events =
      factored.project (foldValues denotation.value roots) := by
  rw [factored.factors]
  exact congrArg factored.project
    (Mettapedia.GSLT.Core.WeightedOccurrenceControl.PortfolioSnapshot.completed_run_denotation
      system disciplines denotation roots start fuel complete)

/-! ## Executable discrimination: completion versus bounded prefixes -/

namespace Canary

open Mettapedia.GSLT.Core.BranchingTemporal.FiniteSearch

/-- The left answer needs one additional expansion; the right answer is
immediately available. -/
def root : FiniteSearch Bool :=
  .choice (.delay (.answer false)) (.answer true)

def fifo : Controller (FiniteSearch Bool) Bool Unit :=
  Controller.fixed Scheduler.breadthFirst

def dfs : Controller (FiniteSearch Bool) Bool Unit :=
  Controller.fixed Scheduler.depthFirst

/-- Two exact streams with the same occurrence bag but opposite answer order. -/
def orderedLeft : List (Emission Unit Bool) :=
  [⟨(), false⟩, ⟨(), true⟩]

def orderedRight : List (Emission Unit Bool) :=
  [⟨(), true⟩, ⟨(), false⟩]

theorem ordered_streams_same_bag_but_distinct :
    eventBag orderedLeft = eventBag orderedRight ∧
      (Perspective.answerStream.observe orderedLeft ≠
        Perspective.answerStream.observe orderedRight) := by
  constructor
  · change (↑[false, true] : Multiset Bool) = ↑[true, false]
    exact Quot.sound (List.Perm.swap true false [])
  · simp [orderedLeft, orderedRight, Perspective.answerStream]

/-- Exact answer order cannot be reconstructed from the occurrence bag.  A
completed-bag switch authority is therefore unavailable for this ordered
perspective, rather than silently changing its meaning. -/
theorem answerStream_bool_not_factored :
    ¬ Nonempty
      (FactorsThroughAnswerBag
        (Perspective.answerStream (Node := Unit) (Answer := Bool))) := by
  rintro ⟨factored⟩
  apply ordered_streams_same_bag_but_distinct.2
  rw [factored.factors, factored.factors,
    ordered_streams_same_bag_but_distinct.1]

/-- Multi-shot storage and a completed occurrence-bag readout jointly admit
controller switching. -/
def bagMultiShotAuthority :
    CompletionSwitchAuthority
      (Perspective.answerBag (Node := Unit) (Answer := Bool))
      .multiShot .ownedMultiShot where
  observation := Perspective.answerBagFactors
  storage := by decide

/-- Strict FIFO is one witness of the abstract unbounded-frontier contract for
this finite search, not the definition of the contract or the universal
default. -/
def fifoFairUnboundedCertificate :
    FairUnboundedFrontierCertificate system fifo [root]
      (Perspective.answerBag (Node := FiniteSearch Bool) (Answer := Bool))
      .multiShot .ownedMultiShot where
  completion := {
    observation := Perspective.answerBagFactors
    storage := by decide }
  fairness :=
    (Mettapedia.GSLT.Core.InferenceControl.Snapshot.fixed_fair_iff
      system Scheduler.breadthFirst [root]).2
      (breadthFirst_fair system [root])

/-- A one-shot state cannot acquire owned-frontier authority merely because
its observation is bag-valued. -/
theorem oneShot_cannot_authorize_owned_bag_switch :
    ¬ Nonempty
      (CompletionSwitchAuthority
        (Perspective.answerBag (Node := Unit) (Answer := Bool))
        .oneShot .ownedMultiShot) := by
  rintro ⟨authority⟩
  exact
    Mettapedia.GSLT.Core.BranchCaptureAlgebra.oneShot_rejects_ownedMultiShot
      authority.storage

/-- Lawful DFS scheduling remains executable, but it cannot advertise fair
unbounded enumeration on the starvation witness.  The failed claim is the
optional liveness certificate, not controller admission. -/
theorem starvationDFS_has_no_fair_unbounded_certificate :
    ¬ Nonempty
      (FairUnboundedFrontierCertificate
        Mettapedia.GSLT.Core.BranchingTemporal.Starvation.system
        (Controller.fixed Scheduler.depthFirst)
        Mettapedia.GSLT.Core.BranchingTemporal.Starvation.roots
        (Perspective.answerBag
          (Node := Mettapedia.GSLT.Core.BranchingTemporal.Starvation.Node)
          (Answer := Nat))
        .multiShot .ownedMultiShot) := by
  rintro ⟨authority⟩
  exact Mettapedia.GSLT.Core.BranchingTemporal.Starvation.depthFirst_not_fair
    ((Mettapedia.GSLT.Core.InferenceControl.Snapshot.fixed_fair_iff _ _ _).mp
      authority.fairness)

/-- One common prefix exposes the same live occurrences to both subsequent
controllers. -/
def commonPrefix :
    Mettapedia.GSLT.Core.InferenceControl.Snapshot
      (FiniteSearch Bool) Bool Unit :=
  Mettapedia.GSLT.Core.InferenceControl.Snapshot.run system fifo 1
    (Mettapedia.GSLT.Core.InferenceControl.Snapshot.initial fifo [root])

def continueFIFO :
    Mettapedia.GSLT.Core.InferenceControl.Snapshot
      (FiniteSearch Bool) Bool Unit :=
  Mettapedia.GSLT.Core.InferenceControl.Snapshot.run system fifo 2
    (withControllerMemory commonPrefix.search ())

def continueDFS :
    Mettapedia.GSLT.Core.InferenceControl.Snapshot
      (FiniteSearch Bool) Bool Unit :=
  Mettapedia.GSLT.Core.InferenceControl.Snapshot.run system dfs 2
    (withControllerMemory commonPrefix.search ())

/-- From the identical live occurrence state, FIFO and DFS expose different
bounded streams and different bounded bags.  A prefix perspective therefore
does not authorize a silent controller switch. -/
theorem same_frontier_switch_changes_bounded_observation :
    continueFIFO.search.events.map Emission.value = [true] ∧
      continueDFS.search.events.map Emission.value = [false] ∧
      eventBag continueFIFO.search.events ≠
        eventBag continueDFS.search.events ∧
      continueFIFO.search.frontier ≠ [] ∧
      continueDFS.search.frontier ≠ [] := by
  decide

/-- Once the hybrid run completes, switching from FIFO to DFS retains the
exact denotational bag. -/
theorem completed_switch_recovers_denotation :
    let firstResult :=
      Mettapedia.GSLT.Core.InferenceControl.Snapshot.run system fifo 1
        (Mettapedia.GSLT.Core.InferenceControl.Snapshot.initial fifo [root])
    let finished :=
      Mettapedia.GSLT.Core.InferenceControl.Snapshot.run system dfs 4
        (withControllerMemory firstResult.search ())
    eventBag finished.search.events = FiniteSearch.denote root := by
  apply completed_bag_after_controller_switch system fifo dfs
    FiniteSearch.additiveDenotation [root] 1 4 ()
  decide

end Canary

#print axioms Perspective.streamToBag
#print axioms Perspective.answerBagFactors
#print axioms scheduler_selected_singleton
#print axioms Canary.fifoFairUnboundedCertificate
#print axioms completed_bag_after_controller_switch
#print axioms completed_factored_observation_after_controller_switch
#print axioms completed_factored_portfolio_observation
#print axioms Canary.ordered_streams_same_bag_but_distinct
#print axioms Canary.answerStream_bool_not_factored
#print axioms Canary.oneShot_cannot_authorize_owned_bag_switch
#print axioms Canary.starvationDFS_has_no_fair_unbounded_certificate
#print axioms Canary.same_frontier_switch_changes_bounded_observation
#print axioms Canary.completed_switch_recovers_denotation

end Mettapedia.Computability.ControllerObservationPerspective
