import Mettapedia.Cybernetics.Stigmergy
import Mettapedia.Languages.MeTTa.MeTTaRevisionedQueryBindEval

/-!
# Revisioned MeTTa spaces as a stigmergic medium

The existing revisioned named-space semantics is an instance of the general
stigmergic interface.  Publishing an atom leaves an occurrence-bearing trace;
a later revision can still expose that occurrence; and the trace can stimulate
an action by another agent.  The proof uses the existing persistent emission
receipt and the actual multiset contents of the later space.

This is a semantic instance, not a claim that every use of a MeTTa space is
stigmergic.  It verifies that the persistent publication protocol has the
required action, agent, medium, trace, and coordination structure.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.StigmergicSpace

open Mettapedia.Cybernetics.Stigmergy
open Mettapedia.Languages.MeTTa.MeTTaRevisionedQueryBindEval
open Mettapedia.OSLF.MeTTaIL.Syntax

universe uSpace

/-- A publication and the later reaction that it can stimulate. -/
inductive SpaceAction (SpaceName : Type uSpace) where
  | publish (actor : Bool) (space : SpaceName) (atom : Pattern)
  | react (actor : Bool) (space : SpaceName) (atom : Pattern)

namespace SpaceAction

def actor {SpaceName : Type uSpace} : SpaceAction SpaceName -> Bool
  | .publish agent _ _ => agent
  | .react agent _ _ => agent

end SpaceAction

/-- The persistent trace identifies the named space, exact atom occurrence
kind, and revision at which it was deposited. -/
structure PublishedTrace (SpaceName : Type uSpace) where
  space : SpaceName
  atom : Pattern
  depositedRevision : Nat

/-- An agent performs exactly the actions carrying that agent identifier. -/
abbrev Performs {SpaceName : Type uSpace}
    (agent : Bool) (action : SpaceAction SpaceName) : Type uSpace :=
  ULift.{uSpace} (PLift (agent = action.actor))

/-- Monotone evolution of a revisioned space retains every earlier atom
occurrence count. -/
structure SpaceEvolution {SpaceName : Type uSpace} [DecidableEq SpaceName]
    (before after : RevisionedSpaces SpaceName) : Type where
  revision_mono : before.revision <= after.revision
  occurrence_mono : forall space atom,
    Multiset.count atom (before.contents space) <=
      Multiset.count atom (after.contents space)

/-- Every publication step is a monotone space evolution. -/
def addEvolution {SpaceName : Type uSpace} [DecidableEq SpaceName]
    (world : RevisionedSpaces SpaceName) (written : SpaceName)
    (newAtom : Pattern) :
    SpaceEvolution world (addAtomWorld world written newAtom) where
  revision_mono := by
    simp [addAtomWorld]
  occurrence_mono := by
    intro read atom
    by_cases same : read = written
    · subst read
      rw [addAtomWorld_contents_same]
      by_cases sameAtom : atom = newAtom
      · subst atom
        simp
      · simp [sameAtom]
    · simp [addAtomWorld, same]

/-- Publication leaves a trace through the existing proof-relevant emission
receipt. -/
inductive SpaceLeaves {SpaceName : Type uSpace} [DecidableEq SpaceName] :
    Nat -> Bool -> SpaceAction SpaceName ->
      RevisionedSpaces SpaceName -> RevisionedSpaces SpaceName ->
      PublishedTrace SpaceName -> Type (max uSpace 0) where
  | publish (producer : Bool) (before after : RevisionedSpaces SpaceName)
      (space : SpaceName) (atom : Pattern)
      (receipt : PersistentEmitReceipt before after space atom) :
      SpaceLeaves after.revision producer (.publish producer space atom)
        before after ⟨space, atom, after.revision⟩

/-- A later space exposes a trace when its revision is current, no earlier
than the deposit, and the exact atom occurrence is still present. -/
structure SpaceExposure {SpaceName : Type uSpace} [DecidableEq SpaceName]
    (time : Nat) (world : RevisionedSpaces SpaceName)
    (trace : PublishedTrace SpaceName) : Type (max uSpace 0) where
  currentRevision : time = world.revision
  afterDeposit : trace.depositedRevision <= time
  occurrencePresent : trace.atom ∈ world.contents trace.space

/-- A published trace stimulates the matching reaction action. -/
abbrev SpaceStimulates {SpaceName : Type uSpace}
    (trace : PublishedTrace SpaceName) (consumer : Bool)
    (action : SpaceAction SpaceName) : Type uSpace :=
  ULift.{uSpace} (PLift (action = .react consumer trace.space trace.atom))

/-- Coordination records the exact publish/react pairing. -/
inductive SpaceCoordination {SpaceName : Type uSpace} :
    SpaceAction SpaceName -> SpaceAction SpaceName -> Type (max uSpace 0) where
  | publishReact (producer consumer : Bool) (space : SpaceName) (atom : Pattern) :
      SpaceCoordination (.publish producer space atom) (.react consumer space atom)

/-- Revisioned named spaces instantiate the abstract stigmergic medium. -/
def medium (SpaceName : Type uSpace) [DecidableEq SpaceName] :
    Medium.{0, uSpace, uSpace, uSpace, 0, uSpace} where
  Agent := Bool
  Action := SpaceAction SpaceName
  MediumState := RevisionedSpaces SpaceName
  Trace := PublishedTrace SpaceName
  Time := Nat
  before := (.<.)
  performs := Performs
  evolves := fun before after => ULift.{uSpace} (SpaceEvolution before after)
  leaves := SpaceLeaves
  exposes := SpaceExposure
  stimulates := SpaceStimulates
  Coordination := SpaceCoordination

/-- Every complete delayed publication/exposure episode yields the exact
publish/react coordination witness. -/
theorem medium_mediates (SpaceName : Type uSpace) [DecidableEq SpaceName] :
    (medium SpaceName).Mediates := by
  rintro ⟨producer, consumer, firstAction, laterAction, beforeState,
    depositedState, observedState, trace, depositedAt, observedAt, delayed,
    producerPerforms, consumerPerforms, leavesTrace, stateEvolves,
    exposesTrace, traceStimulates⟩
  cases leavesTrace with
  | publish producer before after space atom receipt =>
      have laterActionEq := traceStimulates.down.down
      cases laterActionEq
      exact ⟨SpaceCoordination.publishReact producer consumer space atom⟩

/-! ## A real delayed-space episode -/

def afterDeposit {SpaceName : Type uSpace} [DecidableEq SpaceName]
    (before : RevisionedSpaces SpaceName) (space : SpaceName) (atom : Pattern) :
    RevisionedSpaces SpaceName :=
  addAtomWorld before space atom

def afterDelay {SpaceName : Type uSpace} [DecidableEq SpaceName]
    (before : RevisionedSpaces SpaceName) (space : SpaceName)
    (atom laterAtom : Pattern) : RevisionedSpaces SpaceName :=
  addAtomWorld (afterDeposit before space atom) space laterAtom

def depositedTrace {SpaceName : Type uSpace} [DecidableEq SpaceName]
    (before : RevisionedSpaces SpaceName) (space : SpaceName) (atom : Pattern) :
    PublishedTrace SpaceName :=
  ⟨space, atom, (afterDeposit before space atom).revision⟩

/-- A second publication advances time while preserving exposure of the first
published atom. -/
def delayedPublicationEpisode {SpaceName : Type uSpace} [DecidableEq SpaceName]
    (before : RevisionedSpaces SpaceName) (space : SpaceName)
    (atom laterAtom : Pattern) : DelayedEpisode (medium SpaceName) where
  producer := false
  consumer := true
  firstAction := .publish false space atom
  laterAction := .react true space atom
  beforeState := before
  depositedState := afterDeposit before space atom
  observedState := afterDelay before space atom laterAtom
  trace := depositedTrace before space atom
  depositedAt := (afterDeposit before space atom).revision
  observedAt := (afterDelay before space atom laterAtom).revision
  delayed := by
    change before.revision + 1 < before.revision + 1 + 1
    omega
  producerPerforms := ⟨⟨rfl⟩⟩
  consumerPerforms := ⟨⟨rfl⟩⟩
  leavesTrace := by
    exact SpaceLeaves.publish false before (afterDeposit before space atom)
      space atom ⟨rfl⟩
  stateEvolves :=
    ⟨addEvolution (afterDeposit before space atom) space laterAtom⟩
  exposesTrace := by
    refine ⟨rfl, ?_, ?_⟩
    · simp [depositedTrace, afterDeposit, afterDelay, addAtomWorld]
    · simp [depositedTrace, afterDeposit, afterDelay, addAtomWorld]
  traceStimulates := ⟨⟨rfl⟩⟩

/-- The persistent named space mediates delayed coordination through the
retained first publication, not merely through endpoint equality. -/
theorem delayed_publication_coordinates
    {SpaceName : Type uSpace} [DecidableEq SpaceName]
    (before : RevisionedSpaces SpaceName) (space : SpaceName)
    (atom laterAtom : Pattern) :
    Nonempty ((medium SpaceName).Coordination
      (.publish false space atom) (.react true space atom)) :=
  (medium SpaceName).trace_mediated_coordination
    (medium_mediates SpaceName)
    (delayedPublicationEpisode before space atom laterAtom)

end Mettapedia.Languages.MeTTa.StigmergicSpace

#print axioms Mettapedia.Languages.MeTTa.StigmergicSpace.addEvolution
#print axioms Mettapedia.Languages.MeTTa.StigmergicSpace.medium_mediates
#print axioms Mettapedia.Languages.MeTTa.StigmergicSpace.delayed_publication_coordinates
