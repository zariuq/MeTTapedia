import Mettapedia.TypeTheory.CertificateGSLTSearchProfileRevision
import Mettapedia.GSLT.Dynamics.ProvenanceInterpretation

/-!
# Consumer-indexed provenance readouts of certificate search

An operational search trace is not itself a probability, a count, or a
Boolean reachability fact.  This module maps each emitted origin to a stable
cause and compares three lawful consumers of the resulting derivation list:

* symbolic semiring provenance retains alternative occurrences and shared
  cause identities;
* counting interprets every observed cause as one;
* Boolean world semantics asks whether at least one observed cause holds in a
  separately supplied world.

The profile-revision discriminator then proves that prefix restart and
certified delta reopening have equal raw event counts but different symbolic
provenance.  Replaying one root is invisible to every Boolean reachability
world, whereas adding a distinct checked child is visible in a world that
separates the two causes.

No probabilistic-independence conclusion is drawn.  Turning cause identities
into random events remains a separate semantic authority.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.CertificateGSLTSearchProvenanceReadout

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.Core.BranchingTemporal
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.CalculusAsLanguage
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.Dynamics.ProvenanceInterpretation
open Mettapedia.TypeTheory.CertificateGSLTScheduledHistory
open Mettapedia.TypeTheory.CertificateGSLTFiniteSearchAcceleration
open Mettapedia.TypeTheory.CertificateGSLTFiniteSearchAcceleration.ScheduledSearchProfile
open Mettapedia.TypeTheory.CertificateGSLTSearchProfileRevision

noncomputable section

/-! ## One trace, several consumers -/

/-- Regard every emitted origin as a one-cause alternative derivation.  The
answer payload is intentionally not used to invent cause identity. -/
def eventCauseDerivations {Node Answer : Type}
    (events : List (Emission Node Answer)) :
    List (Mettapedia.GSLT.Dynamics.ProvenanceInterpretation.Derivation Node) :=
  events.map fun event => [event.origin]

@[simp] theorem eventCauseDerivations_nil {Node Answer : Type} :
    eventCauseDerivations ([] : List (Emission Node Answer)) = [] :=
  rfl

@[simp] theorem eventCauseDerivations_cons {Node Answer : Type}
    (event : Emission Node Answer) (events : List (Emission Node Answer)) :
    eventCauseDerivations (event :: events) =
      [event.origin] :: eventCauseDerivations events :=
  rfl

theorem eventCauseDerivations_append {Node Answer : Type}
    (first second : List (Emission Node Answer)) :
    eventCauseDerivations (first ++ second) =
      eventCauseDerivations first ++ eventCauseDerivations second := by
  simp [eventCauseDerivations]

/-- The universal symbolic provenance of an operational event trace. -/
def traceProvenance {Node Answer : Type}
    (events : List (Emission Node Answer)) : MvPolynomial Node Nat :=
  provenance (eventCauseDerivations events)

/-- Counting is one interpretation of the symbolic trace: every cause is
assigned one and alternatives add. -/
def traceCount {Node Answer : Type}
    (events : List (Emission Node Answer)) : Nat :=
  interpSet (fun _ : Node => (1 : Nat)) (eventCauseDerivations events)

/-- A selected world's Boolean reachability observation of the trace. -/
def traceEvent {Node Answer : Type}
    (events : List (Emission Node Answer)) (world : World Node) : Bool :=
  eventOf (eventCauseDerivations events) world

/-- The characteristic valuation of one selected cause. -/
noncomputable def causeIndicator {Node : Type}
    (selectedCause cause : Node) : Nat := by
  classical
  exact if cause = selectedCause then 1 else 0

@[simp] theorem causeIndicator_self {Node : Type} (cause : Node) :
    causeIndicator cause cause = 1 := by
  classical
  simp [causeIndicator]

theorem causeIndicator_of_ne {Node : Type} {selectedCause cause : Node}
    (different : cause ≠ selectedCause) :
    causeIndicator selectedCause cause = 0 := by
  classical
  simp [causeIndicator, different]

/-- Multiplicity of one selected cause in the alternative event trace. -/
noncomputable def traceMultiplicity {Node Answer : Type}
    (selectedCause : Node) (events : List (Emission Node Answer)) : Nat :=
  interpSet (causeIndicator selectedCause)
    (eventCauseDerivations events)

/-- Appending chronological traces adds their symbolic alternatives. -/
theorem traceProvenance_append {Node Answer : Type}
    (first second : List (Emission Node Answer)) :
    traceProvenance (first ++ second) =
      traceProvenance first + traceProvenance second := by
  simp [traceProvenance, eventCauseDerivations_append,
    provenance_alternatives]

/-- The counting interpretation is exactly the number of emitted
occurrences. -/
theorem traceCount_eq_length {Node Answer : Type}
    (events : List (Emission Node Answer)) :
    traceCount events = events.length := by
  induction events with
  | nil => simp [traceCount, interpSet]
  | cons event events inductionHypothesis =>
      calc
        traceCount (event :: events) = 1 + traceCount events := by
          simp [traceCount, interpSet, interpDeriv]
        _ = 1 + events.length := by rw [inductionHypothesis]
        _ = (event :: events).length := by simp [Nat.add_comm]

/-- The universal provenance polynomial evaluates to the direct counting
readout. -/
theorem eval_traceProvenance_eq_traceCount {Node Answer : Type}
    (events : List (Emission Node Answer)) :
    MvPolynomial.eval₂ (Nat.castRingHom Nat) (fun _ : Node => (1 : Nat))
        (traceProvenance events) = traceCount events := by
  exact interp_provenance (fun _ : Node => (1 : Nat))
    (eventCauseDerivations events)

/-- The same universal polynomial evaluates to the selected-cause
multiplicity readout. -/
theorem eval_traceProvenance_eq_traceMultiplicity {Node Answer : Type}
    (selectedCause : Node) (events : List (Emission Node Answer)) :
    MvPolynomial.eval₂ (Nat.castRingHom Nat)
        (causeIndicator selectedCause)
        (traceProvenance events) = traceMultiplicity selectedCause events := by
  exact interp_provenance (causeIndicator selectedCause)
    (eventCauseDerivations events)

/-- Concatenating traces is Boolean disjunction at every supplied world. -/
theorem traceEvent_append {Node Answer : Type}
    (first second : List (Emission Node Answer)) (world : World Node) :
    traceEvent (first ++ second) world =
      (traceEvent first world || traceEvent second world) := by
  simp [traceEvent, eventCauseDerivations_append, eventOf]

/-! ## Generic replay boundary -/

/-- Counting sees two emissions of the same cause. -/
theorem duplicate_single_cause_counts_twice {Cause : Type} (cause : Cause) :
    interpSet (fun _ : Cause => (1 : Nat)) [[cause], [cause]] = 2 := by
  simp [interpSet, interpDeriv]

/-- Boolean reachability is idempotent under exact replay of one cause. -/
theorem duplicate_single_cause_event_invariant {Cause : Type}
    (cause : Cause) (world : World Cause) :
    eventOf [[cause], [cause]] world = eventOf [[cause]] world := by
  simp [eventOf, holds]

/-- Therefore no unindexed collapse of replay can serve both the counting
consumer and the Boolean reachability consumer. -/
theorem replay_is_consumer_sensitive {Cause : Type} (cause : Cause) :
    interpSet (fun _ : Cause => (1 : Nat)) [[cause], [cause]] ≠
        interpSet (fun _ : Cause => (1 : Nat)) [[cause]] ∧
      (∀ world : World Cause,
        eventOf [[cause], [cause]] world = eventOf [[cause]] world) := by
  constructor
  · simp [interpSet, interpDeriv]
  · exact duplicate_single_cause_event_invariant cause

/-! ## Search-profile revision discriminator -/

namespace Canary

variable {definition : ValidatedCalculusLanguageDef}
variable {goal : Pattern} {ruleInstance : RuleInstance}

abbrev rootNode : ScheduledSearchNode definition [goal] :=
  initialNode definition [goal]

def addedChild
    (application : RuleApplication definition ruleInstance [] goal) :
    ScheduledSearchNode definition [goal] :=
  rootNode.extend
    (ScheduledCandidate.mk []
      (CertificateGSLTScheduledHistory.Canary.sole application))

/-- The profile delta introduces a genuinely new retained history node, even
though its empty obligation state alone would not remember how it arose. -/
theorem addedChild_ne_rootNode
    (application : RuleApplication definition ruleInstance [] goal) :
    addedChild application ≠ rootNode := by
  exact ScheduledSearchNode.extend_ne_self rootNode
    (ScheduledCandidate.mk []
      (CertificateGSLTScheduledHistory.Canary.sole application))

abbrev oldEvents (definition : ValidatedCalculusLanguageDef) (goal : Pattern) :=
  (CertificateGSLTSearchProfileRevision.Canary.oldClosedSnapshot
    definition goal).events

abbrev restartedEvents
    (application : RuleApplication definition ruleInstance [] goal) :=
  (run
    (branchingSystem
      (CertificateGSLTSearchProfileRevision.Canary.revisedProfile application)
      [goal])
    Scheduler.breadthFirst 1
    (prefixPreservingRestart
      (CertificateGSLTSearchProfileRevision.Canary.oldClosedSnapshot
        definition goal))).events

abbrev deltaEvents
    (application : RuleApplication definition ruleInstance [] goal) :=
  (run
    (branchingSystem
      (CertificateGSLTSearchProfileRevision.Canary.revisedProfile application)
      [goal])
    Scheduler.breadthFirst 1
    (reopenWithDelta
      (CertificateGSLTSearchProfileRevision.Canary.soleBatch
        application))).events

theorem oldEvents_eq
    (definition : ValidatedCalculusLanguageDef) (goal : Pattern) :
    oldEvents definition goal =
      [CertificateGSLTSearchProfileRevision.Canary.rootEvent] :=
  rfl

/-- Restart has two emissions because it replays the retained root. -/
theorem restartedEvents_eq
    (application : RuleApplication definition ruleInstance [] goal) :
    restartedEvents application =
      [CertificateGSLTSearchProfileRevision.Canary.rootEvent,
       CertificateGSLTSearchProfileRevision.Canary.rootEvent] :=
  CertificateGSLTSearchProfileRevision.Canary.prefix_restart_duplicates_root
    application

/-- Delta migration also has two emissions, but its second cause is the new
checked child rather than a replayed root. -/
theorem deltaEvents_eq
    (application : RuleApplication definition ruleInstance [] goal) :
    deltaEvents application =
      [CertificateGSLTSearchProfileRevision.Canary.rootEvent,
       ⟨addedChild application, addedChild application⟩] := by
  simpa [addedChild] using
    CertificateGSLTSearchProfileRevision.Canary.delta_reopen_first_tick_events
      application

theorem old_traceCount_eq_one
    (definition : ValidatedCalculusLanguageDef) (goal : Pattern) :
    traceCount (oldEvents definition goal) = 1 := by
  rw [traceCount_eq_length, oldEvents_eq]
  rfl

theorem restart_traceCount_eq_two
    (application : RuleApplication definition ruleInstance [] goal) :
    traceCount (restartedEvents application) = 2 := by
  rw [traceCount_eq_length, restartedEvents_eq]
  rfl

theorem delta_traceCount_eq_two
    (application : RuleApplication definition ruleInstance [] goal) :
    traceCount (deltaEvents application) = 2 := by
  rw [traceCount_eq_length, deltaEvents_eq]
  rfl

/-- Raw occurrence count cannot tell replay from a genuinely added cause. -/
theorem restart_delta_count_collision
    (application : RuleApplication definition ruleInstance [] goal) :
    traceCount (restartedEvents application) =
      traceCount (deltaEvents application) := by
  rw [restart_traceCount_eq_two, delta_traceCount_eq_two]

/-- The root occurs twice after restart. -/
theorem restart_rootMultiplicity_eq_two
    (application : RuleApplication definition ruleInstance [] goal) :
    traceMultiplicity (rootNode : ScheduledSearchNode definition [goal])
      (restartedEvents application) = 2 := by
  rw [restartedEvents_eq]
  simp [traceMultiplicity, eventCauseDerivations, interpSet, interpDeriv]

/-- The root occurs only once after delta reopening; the second event has a
different proof history. -/
theorem delta_rootMultiplicity_eq_one
    (application : RuleApplication definition ruleInstance [] goal) :
    traceMultiplicity (rootNode : ScheduledSearchNode definition [goal])
      (deltaEvents application) = 1 := by
  rw [deltaEvents_eq]
  simp [traceMultiplicity, eventCauseDerivations, interpSet, interpDeriv,
    causeIndicator_of_ne (addedChild_ne_rootNode application)]

/-- Universal semiring provenance distinguishes replay from genuine delta
addition, although raw trace length does not. -/
theorem restart_delta_provenance_ne
    (application : RuleApplication definition ruleInstance [] goal) :
    traceProvenance (restartedEvents application) ≠
      traceProvenance (deltaEvents application) := by
  intro equal
  have evaluated := congrArg
    (MvPolynomial.eval₂ (Nat.castRingHom Nat)
      (causeIndicator
        (rootNode : ScheduledSearchNode definition [goal]))) equal
  rw [eval_traceProvenance_eq_traceMultiplicity,
    eval_traceProvenance_eq_traceMultiplicity,
    restart_rootMultiplicity_eq_two,
    delta_rootMultiplicity_eq_one] at evaluated
  omega

/-- Boolean reachability cannot observe an exact restart replay, for any
interpretation of search nodes as causes. -/
theorem restart_traceEvent_eq_old
    (application : RuleApplication definition ruleInstance [] goal)
    (world : World (ScheduledSearchNode definition [goal])) :
    traceEvent (restartedEvents application) world =
      traceEvent (oldEvents definition goal) world := by
  rw [restartedEvents_eq, oldEvents_eq]
  simp [traceEvent, eventCauseDerivations, eventOf, holds]

/-- A world that treats only the added child as true separates the genuine
delta from the old trace. -/
noncomputable def addedChildWorld
    (application : RuleApplication definition ruleInstance [] goal) :
    World (ScheduledSearchNode definition [goal]) := by
  classical
  exact fun node => if node = addedChild application then true else false

@[simp] theorem addedChildWorld_child
    (application : RuleApplication definition ruleInstance [] goal) :
    addedChildWorld application (addedChild application) = true := by
  classical
  simp [addedChildWorld]

@[simp] theorem addedChildWorld_root
    (application : RuleApplication definition ruleInstance [] goal) :
    addedChildWorld application rootNode = false := by
  classical
  simp [addedChildWorld, (addedChild_ne_rootNode application).symm]

theorem old_traceEvent_addedChildWorld_false
    (application : RuleApplication definition ruleInstance [] goal) :
    traceEvent (oldEvents definition goal) (addedChildWorld application) =
      false := by
  rw [oldEvents_eq]
  simp [traceEvent, eventCauseDerivations, eventOf, holds]

theorem delta_traceEvent_addedChildWorld_true
    (application : RuleApplication definition ruleInstance [] goal) :
    traceEvent (deltaEvents application) (addedChildWorld application) =
      true := by
  rw [deltaEvents_eq]
  simp [traceEvent, eventCauseDerivations, eventOf, holds]

/-- Positive discriminator: unlike replay, a certified delta is observable in
some lawful Boolean cause interpretation. -/
theorem exists_world_distinguishing_delta_from_old
    (application : RuleApplication definition ruleInstance [] goal) :
    ∃ world : World (ScheduledSearchNode definition [goal]),
      traceEvent (deltaEvents application) world ≠
        traceEvent (oldEvents definition goal) world := by
  refine ⟨addedChildWorld application, ?_⟩
  rw [delta_traceEvent_addedChildWorld_true,
    old_traceEvent_addedChildWorld_false]
  decide

/-- The three readouts together expose the exact observer boundary. -/
theorem revision_readout_trichotomy
    (application : RuleApplication definition ruleInstance [] goal) :
    traceCount (restartedEvents application) =
        traceCount (deltaEvents application) ∧
      traceProvenance (restartedEvents application) ≠
        traceProvenance (deltaEvents application) ∧
      (∀ world : World (ScheduledSearchNode definition [goal]),
        traceEvent (restartedEvents application) world =
          traceEvent (oldEvents definition goal) world) ∧
      (∃ world : World (ScheduledSearchNode definition [goal]),
        traceEvent (deltaEvents application) world ≠
          traceEvent (oldEvents definition goal) world) :=
  ⟨restart_delta_count_collision application,
    restart_delta_provenance_ne application,
    restart_traceEvent_eq_old application,
    exists_world_distinguishing_delta_from_old application⟩

end Canary

/-! ## Audited theorem crowns -/

#print axioms traceProvenance_append
#print axioms traceCount_eq_length
#print axioms eval_traceProvenance_eq_traceCount
#print axioms traceEvent_append
#print axioms replay_is_consumer_sensitive
#print axioms Canary.addedChild_ne_rootNode
#print axioms Canary.restart_delta_count_collision
#print axioms Canary.restart_delta_provenance_ne
#print axioms Canary.restart_traceEvent_eq_old
#print axioms Canary.exists_world_distinguishing_delta_from_old
#print axioms Canary.revision_readout_trichotomy

end


end Mettapedia.TypeTheory.CertificateGSLTSearchProvenanceReadout
