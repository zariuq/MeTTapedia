import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NeedMachineProjection
import Mettapedia.OSLF.NativeTypes.Semantics.ModalSimulation

/-!
# Behavioral observation of actual controlled copying

The state map forgets control rows while retaining the actual heap occurrences
and heap equations. Events on both sides are ordinary transform firings.
Projection and lifting supply a span map with outgoing endpoint coverage;
the existing native modal semantics then transports every future-only formula
with positive fixed-point bodies, including nested least and greatest fixed
points. This is a comparison of the copying subsystem and heap observations.
It is not a whole-machine, spatial, authority or runtime-cost equivalence.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NeedCopyObservation

open Mettapedia.Machines.BranchLocalNeed.CallTimeChoice (Suspension)
open Mettapedia.OSLF.Framework.DerivedModalities
open Mettapedia.GSLT.ObservationSpans
open Mettapedia.OSLF.NativeTypes.Semantics.ModalFormula
open Mettapedia.Logic.ModalMuCalculus
open Mettapedia.GSLT.LanguageDef.CertificateGSLT.MuCalculusBoundary

structure Protocol where
  job : Nat
  source : Nat
  input : NeedControl.Control Nat
  reads : List (SnapshotCopy.Row Suspension)
  operation : NeedStoreOperations.Operation
  resume : NeedControl.Resume

def Protocol.plan (protocol : Protocol) : NeedControl.Plan :=
  ⟨protocol.input,protocol.reads,.edit protocol.source protocol.operation protocol.resume⟩

abbrev Controlled (protocol : Protocol) :=
  {world : NeedMachine.World // NeedMachine.action.Consistent world.equations ∧
    NeedMachine.Has world.present (.waiting protocol.job protocol.plan)}

structure HeapEdge (protocol : Protocol) where
  before : SnapshotCopy.World Suspension
  after : SnapshotCopy.World Suspension
  event : SnapshotCopy.Event Suspension
  firing : Step SnapshotCopy.action SnapshotCopy.label
    (event.rule protocol.job protocol.source protocol.job) before after

structure ControlledEdge (protocol : Protocol) where
  before : Controlled protocol
  after : Controlled protocol
  event : SnapshotCopy.Event Suspension
  firing : Step NeedMachine.action NeedMachine.label
    (NeedMachine.copyRule protocol.job protocol.input protocol.reads protocol.source
      protocol.operation protocol.resume event) before.val after.val

def heapSpan (protocol : Protocol) : ReductionSpan (SnapshotCopy.World Suspension) where
  Edge := HeapEdge protocol
  source := HeapEdge.before
  target := HeapEdge.after

def controlledSpan (protocol : Protocol) : ReductionSpan (Controlled protocol) where
  Edge := ControlledEdge protocol
  source := ControlledEdge.before
  target := ControlledEdge.after

/-- The event component projects the actual firing; neither transition
system is defined by pulling back the other system's relation. -/
def projection (protocol : Protocol) : SpanMap (controlledSpan protocol) (heapSpan protocol) where
  states world := NeedMachine.heapWorld world.val
  events edge := ⟨NeedMachine.heapWorld edge.before.val,NeedMachine.heapWorld edge.after.val,edge.event,
    NeedMachine.copy_projects protocol.job protocol.input protocol.reads protocol.source
      protocol.operation protocol.resume edge.event edge.firing⟩
  source_comm _ := rfl
  target_comm _ := rfl

/-- Every heap event starting at the projected world has a genuine
controlled firing, including its original absence check and equation history. -/
theorem projection_source_lifts (protocol : Protocol) : (projection protocol).SourceLifts := by
  intro before event starts
  have heapStep := event.firing
  change event.before = NeedMachine.heapWorld before.val at starts
  rw [starts] at heapStep
  obtain ⟨after,firing,projected⟩ := NeedMachine.copy_lifts protocol.job protocol.input protocol.reads
    protocol.source protocol.operation protocol.resume event.event before.property.1 before.property.2 heapStep
  let controlledAfter : Controlled protocol := ⟨after,firing.consistent,
    NeedMachine.copy_keeps_waiting protocol.job protocol.input protocol.reads protocol.source
      protocol.operation protocol.resume event.event firing⟩
  exact ⟨⟨before,controlledAfter,event.event,firing⟩,rfl,projected⟩

/-- The generic OSLF diamond law now applies to this concrete transform
projection, with every heap predicate admitted as an observation. -/
theorem possibility_iff (protocol : Protocol) (predicate : SnapshotCopy.World Suspension → Prop)
    (world : Controlled protocol) :
    derivedDiamond (heapSpan protocol) predicate (NeedMachine.heapWorld world.val) ↔
      derivedDiamond (controlledSpan protocol) (fun state => predicate (NeedMachine.heapWorld state.val)) world :=
  (projection protocol).diamond_pullback (projection_source_lifts protocol) predicate world

/-- Formula restriction recording the direction of every modality.
In particular, a future box is not OSLF's predecessor-universal box. -/
def FutureOnly : {n : Nat} → Formula Traversal n → Prop
  | _, .tt | _, .ff | _, .var _ => True
  | _, .neg inner | _, .mu inner | _, .nu inner => FutureOnly inner
  | _, .conj left right | _, .disj left right => FutureOnly left ∧ FutureOnly right
  | _, .diamond direction inner | _, .box direction inner => direction = .future ∧ FutureOnly inner

theorem future_coverage_of_lifts {X Y : Type*} {A : ReductionSpan X} {B : ReductionSpan Y}
    (observation : SpanMap A B) (lifts : observation.SourceLifts) {n : Nat} (formula : Formula Traversal n)
    (future : FutureOnly formula) : CoversFormula observation formula := by
  induction formula with
  | tt | ff | var _ => trivial
  | neg inner ih | mu inner ih | nu inner ih => exact ih future
  | conj left right il ir | disj left right il ir => exact ⟨il future.1,ir future.2⟩
  | diamond direction inner ih | box direction inner ih =>
      obtain ⟨rfl,only⟩ := future
      exact ⟨lifts,ih only⟩

theorem future_coverage (protocol : Protocol) {n : Nat} (formula : Formula Traversal n)
    (future : FutureOnly formula) : CoversFormula (projection protocol) formula :=
  future_coverage_of_lifts (projection protocol) (projection_source_lifts protocol) formula future

/-- Exact future behavioral observation, using the independently owned
modal fixed-point semantics and its genuine endpoint-lifting theorem. -/
theorem future_formula_iff (protocol : Protocol) {n : Nat} (formula : Formula Traversal n)
    (future : FutureOnly formula) (positive : fixedPointsPositive formula = true)
    (environment : Env (SnapshotCopy.World Suspension) n) (world : Controlled protocol) :
    satisfies (transitionSystem (heapSpan protocol)) environment formula (NeedMachine.heapWorld world.val) ↔
      satisfies (transitionSystem (controlledSpan protocol))
        (pullEnvironment (projection protocol).states environment) formula world :=
  satisfies_pullback (projection protocol) formula (future_coverage protocol formula future) positive environment world

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NeedCopyObservation
