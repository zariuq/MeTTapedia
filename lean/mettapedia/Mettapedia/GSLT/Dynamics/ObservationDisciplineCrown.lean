import Mettapedia.GSLT.Dynamics.CompositeObservationPolicy
import Mettapedia.GSLT.Dynamics.ObservationSchedulerSufficiency
import Mettapedia.GSLT.Dynamics.ObservationTransport
import Mettapedia.GSLT.LanguageDef.GradedObservationDiscipline

/-!
# Capability-indexed observation-discipline crown

An observation discipline has four semantically distinct layers:

* the execution system and its proof-relevant events;
* the witness container populated by an event history;
* a declared value readout from retained witnesses;
* a downstream policy that may use only distinctions retained by that readout.

This module closes two remaining seams in that factorization.

First, chronological and certified-independent composition are indexed
capabilities of a collector.  They are not fields required of every observer,
and one capability does not determine the other.

Second, operational policy support is characterized on the exact image of the
collector.  The earlier global policy criterion remains useful when every
abstract container value is part of the public contract, but an unreachable
container must not invalidate a policy that is exact on every executable
history.  The two notions are separated by a checked counterexample.
-/

namespace Mettapedia.GSLT.Dynamics

open Mettapedia.Algebra

universe uEvent uSourceEvent uContainer uValue uDecision

/-! ## Capability-indexed collection algebra -/

/-- Algebraic operations that may be requested of a witness collector.
Chronological composition follows history concatenation.  Independent
parallel composition is used only after the operational layer supplies an
independence certificate. -/
inductive CollectionCapabilityKind where
  | chronological
  | independentParallel
  deriving DecidableEq, Repr

namespace WitnessCollector

/-- The dependent family selected by a collection-capability request. -/
def Capability {Event : Type uEvent}
    (collector : WitnessCollector.{uEvent, uContainer} Event) :
    CollectionCapabilityKind → Type uContainer
  | .chronological => ChronologicalCapability collector
  | .independentParallel => IndependentParallelCapability collector

/-- A container is operationally reachable when some accepted finite event
history collects to it. -/
def Reachable {Event : Type uEvent}
    (collector : WitnessCollector.{uEvent, uContainer} Event)
    (container : collector.Container) : Prop :=
  ∃ events, collector.collect events = some container

end WitnessCollector

namespace ObservationDiscipline

/-- Collection capabilities of a discipline are inherited from its retained
witness collector, not from its value readout. -/
abbrev CollectionCapability {Event : Type uEvent}
    (discipline : ObservationDiscipline.{uEvent, uContainer, uValue} Event)
    (kind : CollectionCapabilityKind) : Type uContainer :=
  discipline.collection.Capability kind

/-- Changing only the value dial retains every collection capability
definitionally. -/
def mapValueCollectionCapability {Event : Type uEvent}
    (discipline : ObservationDiscipline.{uEvent, uContainer, uValue} Event)
    (translate : discipline.Value → OtherValue)
    {kind : CollectionCapabilityKind}
    (capability : discipline.CollectionCapability kind) :
    (discipline.mapValue translate).CollectionCapability kind :=
  capability

/-- Pullback along an event map preserves whichever collection capability was
actually supplied. -/
def pullbackCollectionCapability
    (eventMap : SourceEvent → Event)
    (discipline : ObservationDiscipline.{uEvent, uContainer, uValue} Event) :
    ∀ kind : CollectionCapabilityKind,
      discipline.CollectionCapability kind →
        (ObservationTransport.ObservationDiscipline.pullback eventMap discipline
          ).CollectionCapability kind
  | .chronological, capability =>
      ObservationTransport.WitnessCollector.pullbackChronological
        eventMap discipline.collection capability
  | .independentParallel, capability =>
      ObservationTransport.WitnessCollector.pullbackIndependentParallel
        eventMap discipline.collection capability

/-! ## Exact policy factorization on executable witness states -/

/-- A policy is operationally supported when a policy on the declared value
readout agrees with it on every witness container that can actually be
collected.  No condition is imposed on unreachable abstract containers. -/
def SupportsReachablePolicy {Event : Type uEvent}
    (discipline : ObservationDiscipline.{uEvent, uContainer, uValue} Event)
    (policy : discipline.collection.Container → Decision) : Prop :=
  ∃ observedPolicy : discipline.Value → Decision,
    ∀ {container}, discipline.collection.Reachable container →
      observedPolicy (discipline.readout container) = policy container

/-- The exact operational candidate domain: retained witness states that are
produced by at least one accepted event history. -/
abbrev ReachableContainer {Event : Type uEvent}
    (discipline : ObservationDiscipline.{uEvent, uContainer, uValue} Event) :=
  { container : discipline.collection.Container //
      discipline.collection.Reachable container }

/-- Maximum-score selection restricted to operationally reachable witness
states.  The bag selector receives the proof-relevant reachable subtype, so
unreachable abstract carrier values cannot influence its specification. -/
def SupportsReachableMaxSelection {Event : Type uEvent}
    (discipline : ObservationDiscipline.{uEvent, uContainer, uValue} Event)
    (score : discipline.collection.Container → Nat) : Prop :=
  Mettapedia.GSLT.Core.ObservationSupportsMaxSelection
    (fun container : discipline.ReachableContainer =>
      discipline.readout container.1)
    (fun container => score container.1)

/-- The intrinsic information criterion for operational policy support:
equal readouts must induce equal decisions whenever both witness states are
reachable. -/
def PolicyConstantOnReachableReadoutFibers {Event : Type uEvent}
    (discipline : ObservationDiscipline.{uEvent, uContainer, uValue} Event)
    (policy : discipline.collection.Container → Decision) : Prop :=
  ∀ {first second},
    discipline.collection.Reachable first →
    discipline.collection.Reachable second →
    discipline.readout first = discipline.readout second →
    policy first = policy second

/-- **Exact reachable-image policy criterion.**  For an inhabited decision
type, operational policy support is equivalent to constancy on reachable
readout fibres.  Values outside the reachable readout image receive an
arbitrary default, which no execution can observe. -/
theorem supportsReachablePolicy_iff_constantOnReachableReadoutFibers
    {Event : Type uEvent} [Nonempty Decision]
    (discipline : ObservationDiscipline.{uEvent, uContainer, uValue} Event)
    (policy : discipline.collection.Container → Decision) :
    discipline.SupportsReachablePolicy policy ↔
      discipline.PolicyConstantOnReachableReadoutFibers policy := by
  constructor
  · rintro ⟨observedPolicy, agrees⟩ first second firstReachable
      secondReachable sameReadout
    rw [← agrees firstReachable, ← agrees secondReachable, sameReadout]
  · intro constant
    classical
    let fallback : Decision := Classical.choice inferInstance
    let observedPolicy : discipline.Value → Decision := fun value =>
      if reachable : ∃ container,
          discipline.collection.Reachable container ∧
            discipline.readout container = value then
        policy (Classical.choose reachable)
      else
        fallback
    refine ⟨observedPolicy, ?_⟩
    intro container containerReachable
    simp only [observedPolicy]
    split
    · rename_i reachable
      exact constant
        (Classical.choose_spec reachable).1 containerReachable
        (Classical.choose_spec reachable).2
    · rename_i unreachable
      exact False.elim
        (unreachable ⟨container, containerReachable, rfl⟩)

/-- **Exact reachable scheduler criterion.**  A readout can implement
maximum-score selection over executable witness states precisely when the
score is constant on its reachable readout fibres. -/
theorem supportsReachableMaxSelection_iff
    {Event : Type uEvent}
    (discipline : ObservationDiscipline.{uEvent, uContainer, uValue} Event)
    (score : discipline.collection.Container → Nat) :
    discipline.SupportsReachableMaxSelection score ↔
      discipline.PolicyConstantOnReachableReadoutFibers score := by
  unfold SupportsReachableMaxSelection
  rw [Mettapedia.GSLT.Core.observationSupportsMaxSelection_iff]
  constructor
  · intro constant first second firstReachable secondReachable sameReadout
    exact constant
      (first := ⟨first, firstReachable⟩)
      (second := ⟨second, secondReachable⟩)
      sameReadout
  · intro constant first second sameReadout
    exact constant first.property second.property sameReadout

/-- Maximum-selection support and ordinary score-policy support have the
same information criterion on the executable image. -/
theorem supportsReachableMaxSelection_iff_supportsReachableScorePolicy
    {Event : Type uEvent}
    (discipline : ObservationDiscipline.{uEvent, uContainer, uValue} Event)
    (score : discipline.collection.Container → Nat) :
    discipline.SupportsReachableMaxSelection score ↔
      discipline.SupportsReachablePolicy score := by
  rw [supportsReachableMaxSelection_iff,
    supportsReachablePolicy_iff_constantOnReachableReadoutFibers]

/-- A globally supported policy is operationally supported.  The converse is
false when the collector's carrier contains unreachable states. -/
theorem supportsReachablePolicy_of_supportsPolicy {Event : Type uEvent}
    (discipline : ObservationDiscipline.{uEvent, uContainer, uValue} Event)
    (policy : discipline.collection.Container → Decision)
    (supported : discipline.SupportsPolicy policy) :
    discipline.SupportsReachablePolicy policy := by
  obtain ⟨observedPolicy, agrees⟩ := supported
  exact ⟨observedPolicy, fun _ => agrees _⟩

/-- One collision between two reachable witness states with different
decisions refutes operational support. -/
theorem not_supportsReachablePolicy_of_collision {Event : Type uEvent}
    (discipline : ObservationDiscipline.{uEvent, uContainer, uValue} Event)
    (policy : discipline.collection.Container → Decision)
    {first second : discipline.collection.Container}
    (firstReachable : discipline.collection.Reachable first)
    (secondReachable : discipline.collection.Reachable second)
    (sameReadout : discipline.readout first = discipline.readout second)
    (differentDecision : policy first ≠ policy second) :
    ¬ discipline.SupportsReachablePolicy policy := by
  rintro ⟨observedPolicy, agrees⟩
  exact differentDecision
    ((agrees firstReachable).symm.trans
      ((congrArg observedPolicy sameReadout).trans
        (agrees secondReachable)))

end ObservationDiscipline

/-! ## Positive and negative controls -/

namespace CapabilityCanary

def unitWork : Unit → WorkSpan := fun _ => ⟨1, 1⟩

/-- Work/span supplies both indexed collection capabilities, with distinct
algebras for chronological and independently parallel composition. -/
def workSpanCapability :
    ∀ kind : CollectionCapabilityKind,
      (WorkSpanObservation.discipline unitWork).CollectionCapability kind
  | .chronological => WorkSpanObservation.chronological unitWork
  | .independentParallel => WorkSpanObservation.independentParallel unitWork

/-- The capability index is semantically relevant: the same two retained
unit costs have different span under the two selected operations. -/
theorem chronological_ne_independentParallel :
    (workSpanCapability .chronological).algebra.op
        ⟨1, 1⟩ ⟨1, 1⟩ ≠
      (workSpanCapability .independentParallel).algebra.op
        ⟨1, 1⟩ ⟨1, 1⟩ := by
  intro equal
  have values : (⟨2, 2⟩ : WorkSpan) = ⟨2, 1⟩ :=
    Option.some.inj equal
  have spans := congrArg WorkSpan.span values
  norm_num at spans

/-- A valid observation discipline whose collector rejects every history. -/
def nowhere : ObservationDiscipline Unit where
  collection :=
    { Container := Unit
      collect := fun _ => none }
  Value := Unit
  readout := id

/-- Observation does not imply chronological compositionality.  Capabilities
must be supplied, never inferred from the existence of a readout. -/
theorem nowhere_has_no_chronological_capability :
    IsEmpty (nowhere.CollectionCapability .chronological) :=
  ⟨by
    intro capability
    have impossible :
        nowhere.collection.collect [] = some capability.algebra.unit :=
      capability.collect_nil
    simp [nowhere] at impossible⟩

end CapabilityCanary

namespace ReachablePolicyCanary

/-- Only `false` is produced; `true` is an abstract but unreachable container
state. -/
def collector : WitnessCollector Unit where
  Container := Bool
  collect := fun _ => some false

def discipline : ObservationDiscipline Unit where
  collection := collector
  Value := Unit
  readout := fun _ => ()

def policy : Bool → Bool := id

/-- The policy is exactly implementable on every executable witness state. -/
theorem supportsReachablePolicy :
    discipline.SupportsReachablePolicy policy := by
  refine ⟨fun _ => false, ?_⟩
  intro container reachable
  obtain ⟨events, equation⟩ := reachable
  change some false = some container at equation
  cases equation
  rfl

/-- The stronger global contract rejects the same policy because it also
asks the constant readout to distinguish the unreachable `true` state. -/
theorem not_supportsGlobalPolicy :
    ¬ discipline.SupportsPolicy policy := by
  apply ObservationDiscipline.not_supportsPolicy_of_collision discipline policy
      (first := false) (second := true)
  · rfl
  · decide

/-- Operational and global factorization are therefore genuinely distinct. -/
theorem reachable_support_does_not_imply_global_support :
    discipline.SupportsReachablePolicy policy ∧
      ¬ discipline.SupportsPolicy policy :=
  ⟨supportsReachablePolicy, not_supportsGlobalPolicy⟩

end ReachablePolicyCanary

#print axioms ObservationDiscipline.supportsReachablePolicy_iff_constantOnReachableReadoutFibers
#print axioms ObservationDiscipline.supportsReachableMaxSelection_iff
#print axioms ObservationDiscipline.supportsReachableMaxSelection_iff_supportsReachableScorePolicy
#print axioms ObservationDiscipline.supportsReachablePolicy_of_supportsPolicy
#print axioms ObservationDiscipline.not_supportsReachablePolicy_of_collision
#print axioms CapabilityCanary.chronological_ne_independentParallel
#print axioms CapabilityCanary.nowhere_has_no_chronological_capability
#print axioms ReachablePolicyCanary.reachable_support_does_not_imply_global_support

end Mettapedia.GSLT.Dynamics
