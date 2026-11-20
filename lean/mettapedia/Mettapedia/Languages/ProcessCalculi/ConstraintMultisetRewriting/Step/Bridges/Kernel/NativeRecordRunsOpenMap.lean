import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Kernel.NativeRecordRunsCorrespondence
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.TransitionMaps

/-!
# Future lifting for the pointed native-record observation

Each step consumes one pending request. The checked operational
correspondence therefore lifts one source step to one actual pointed step.
The observation is an open map of successor systems. This statement concerns
the named pointed queue profile; it does not make the raw forget projection
open, identify a native cost, or establish contextual equivalence.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.NativeRecordRunsOpenMap

open NativeFieldSchema InterpretedFrames NativeRecordRuns NativeRecordRunsCorrespondence
open Mettapedia.GSLT Mettapedia.GSLT.IndexedOperational Mettapedia.GSLT.Ultrainfinite
open Mettapedia.OSLF.Framework.DerivedModalities
open FragmentsOfTheStep.TransitionMaps

universe u v w

theorem queue_step_pending {Observation : Type v} {Event : Type u}
    {edge : Observation → Event → Observation → Prop} {before after : QueueState Observation Event}
    (stepped : QueueStep edge before after) : after.pending.length + 1 = before.pending.length := by
  obtain ⟨event, remaining, beforeEq, _, afterEq, _⟩ := stepped
  rw [beforeEq, afterEq, List.length_cons]

theorem pointed_step_pending {Cell : Field → Type u} {Record : Type u} {Effect : Frame.{u}} {Index : Type v}
    (clauses : Index → QueueClause Cell Record Effect)
    {before after : NativeRecordRunsCorrespondence.Configuration Cell (Record × Effect.Carrier)}
    (event : PointedEvent clauses before after) : after.pending.length + 1 = before.pending.length := by
  cases event with
  | fire start actual admitted finish restriction =>
      have oldView := start.view
      rw [← restriction] at oldView
      obtain ⟨move⟩ := invert_move clauses _ actual admitted finish.environment finish.view.solved
        start.layout start.fields _ _ oldView
      have samePending := (view_observables move.result finish.view).2.2
      have beforeLength := congrArg List.length move.input.pendingSame
      have afterLength := congrArg List.length samePending
      simp only [List.length_cons] at beforeLength
      dsimp only
      omega

theorem target_step_pending {Cell : Field → Type u} {Record : Type u} {Effect : Frame.{u}} {Index : Type v}
    (clauses : Index → QueueClause Cell Record Effect)
    {before after : NativeRecordRunsCorrespondence.Configuration Cell (Record × Effect.Carrier)}
    (stepped : (targetTheory clauses).Step before after) : after.pending.length + 1 = before.pending.length := by
  obtain ⟨event⟩ := stepped
  exact pointed_step_pending clauses event

theorem target_path_pending {Cell : Field → Type u} {Record : Type u} {Effect : Frame.{u}} {Index : Type v}
    (clauses : Index → QueueClause Cell Record Effect)
    {before after : NativeRecordRunsCorrespondence.Configuration Cell (Record × Effect.Carrier)}
    (path : ExecutionPath (targetTheory clauses) before after) :
    path.length + after.pending.length = before.pending.length := by
  induction path with
  | refl state => exact Nat.zero_add _
  | @cons first middle last step rest ih =>
      have firstDrop := target_step_pending clauses step.down
      change rest.length + 1 + last.pending.length = first.pending.length
      omega

theorem target_step_of_path_one {Cell : Field → Type u} {Record : Type u} {Effect : Frame.{u}} {Index : Type v}
    (clauses : Index → QueueClause Cell Record Effect)
    {before after : NativeRecordRunsCorrespondence.Configuration Cell (Record × Effect.Carrier)}
    (path : ExecutionPath (targetTheory clauses) before after) (one : path.length = 1) :
    (targetTheory clauses).Step before after := by
  cases path with
  | refl => cases one
  | cons step rest =>
      cases rest with
      | refl => exact step.down
      | cons next tail =>
          change tail.length + 1 + 1 = 1 at one
          omega

/-- The forward path supplied by the existing correspondence has exactly
one step because both queue endpoints differ by exactly one request. -/
theorem functional_bisimulation {Cell : Field → Type u} {Record : Type u} {Effect : Frame.{u}} {Index : Type v}
    {Observation : Type w} (clauses : Index → QueueClause Cell Record Effect)
    (read : ((name : Field) → Cell name) → Observation)
    (edge : Observation → (Record × Effect.Carrier) → Observation → Prop)
    (comparison : OperationalCorrespondence (sourceTheory edge) (targetTheory clauses))
    (graph : ∀ source current, comparison.related source current ↔ observe read current = source) :
    FunctionalBisimulation (targetTheory clauses).Step (sourceTheory edge).Step (observe read) := by
  constructor
  · intro before after stepped
    have related := (graph (observe read before) before).mpr rfl
    rcases comparison.readStep related stepped with unchanged | ⟨sourceAfter, sourceStep, relatedAfter⟩
    · have same := (graph (observe read before) after).mp unchanged
      have equalLength := congrArg (fun source => source.pending.length) same
      have dropped := target_step_pending clauses stepped
      change after.pending.length = before.pending.length at equalLength
      omega
    · have same := (graph sourceAfter after).mp relatedAfter
      exact same.symm ▸ sourceStep
  · intro before sourceAfter sourceStep
    have related := (graph (observe read before) before).mpr rfl
    obtain ⟨after, ⟨path⟩, relatedAfter⟩ := comparison.forward related sourceStep
    have same := (graph sourceAfter after).mp relatedAfter
    have pathDrop := target_path_pending clauses path
    have sourceDrop := queue_step_pending sourceStep
    have sameLength := congrArg (fun source => source.pending.length) same
    change after.pending.length = sourceAfter.pending.length at sameLength
    change sourceAfter.pending.length + 1 = before.pending.length at sourceDrop
    have one : path.length = 1 := by omega
    exact ⟨after, target_step_of_path_one clauses path one, same⟩

/-- Every finite source future lifts from every pointed state over its start. -/
theorem observation_future_lift {Cell : Field → Type u} {Record : Type u} {Effect : Frame.{u}} {Index : Type v}
    {Observation : Type w} (clauses : Index → QueueClause Cell Record Effect)
    (read : ((name : Field) → Cell name) → Observation)
    (edge : Observation → (Record × Effect.Carrier) → Observation → Prop)
    (comparison : OperationalCorrespondence (sourceTheory edge) (targetTheory clauses))
    (graph : ∀ source current, comparison.related source current ↔ observe read current = source)
    {first : NativeRecordRunsCorrespondence.Configuration Cell (Record × Effect.Carrier)}
    {last : QueueState Observation (Record × Effect.Carrier)}
    (path : Relation.ReflTransGen (sourceTheory edge).Step (observe read first) last) :
    ∃ finish, Relation.ReflTransGen (targetTheory clauses).Step first finish ∧ observe read finish = last :=
  Zag.path (functional_bisimulation clauses read edge comparison graph).zag path first rfl

theorem observation_diamond {Cell : Field → Type u} {Record : Type u} {Effect : Frame.{u}} {Index : Type v}
    {Observation : Type w} (clauses : Index → QueueClause Cell Record Effect)
    (read : ((name : Field) → Cell name) → Observation)
    (edge : Observation → (Record × Effect.Carrier) → Observation → Prop)
    (comparison : OperationalCorrespondence (sourceTheory edge) (targetTheory clauses))
    (graph : ∀ source current, comparison.related source current ↔ observe read current = source)
    (predicate : QueueState Observation (Record × Effect.Carrier) → Prop) :
    pb (observe read) (derivedDiamond (span (sourceTheory edge).Step) predicate) =
      derivedDiamond (span (targetTheory clauses).Step) (pb (observe read) predicate) :=
  pb_diamond (functional_bisimulation clauses read edge comparison graph) predicate

theorem observation_forwardBox {Cell : Field → Type u} {Record : Type u} {Effect : Frame.{u}} {Index : Type v}
    {Observation : Type w} (clauses : Index → QueueClause Cell Record Effect)
    (read : ((name : Field) → Cell name) → Observation)
    (edge : Observation → (Record × Effect.Carrier) → Observation → Prop)
    (comparison : OperationalCorrespondence (sourceTheory edge) (targetTheory clauses))
    (graph : ∀ source current, comparison.related source current ↔ observe read current = source)
    (predicate : QueueState Observation (Record × Effect.Carrier) → Prop) :
    pb (observe read) (derivedForwardBox (span (sourceTheory edge).Step) predicate) =
      derivedForwardBox (span (targetTheory clauses).Step) (pb (observe read) predicate) :=
  pb_forwardBox (functional_bisimulation clauses read edge comparison graph) predicate

theorem observation_bisimilar_iff {Cell : Field → Type u} {Record : Type u} {Effect : Frame.{u}} {Index : Type v}
    {Observation : Type (u+1)} (clauses : Index → QueueClause Cell Record Effect)
    (read : ((name : Field) → Cell name) → Observation)
    (edge : Observation → (Record × Effect.Carrier) → Observation → Prop)
    (comparison : OperationalCorrespondence (sourceTheory edge) (targetTheory clauses))
    (graph : ∀ source current, comparison.related source current ↔ observe read current = source)
    {first second : NativeRecordRunsCorrespondence.Configuration Cell (Record × Effect.Carrier)} :
    (targetTheory clauses).Bisimilar first second ↔
      (sourceTheory edge).Bisimilar (observe read first) (observe read second) :=
  bisimilar_iff_map (functional_bisimulation clauses read edge comparison graph)

section Native

open Mettapedia.Logic Mettapedia.Languages.OpenTheory Mettapedia.Languages.HOLLight
open NativeClauseData ProofExecution TypeFamilySemantics

attribute [local irreducible] NativeClauseData.signature

variable {ops : Operations} (table : Fin 29 → Syntax ops)
    (contract : NativeInstanceReadback.Signature (signature ops))
    {received : Registered.State} (profile : SourceProfileModels.ProfileFrame.{w} received)
    (logical : NativeFieldMeaning.LogicalOperations ops)
    (casesReading : NativeClauseReadback.Reading (signature ops) (NativeFieldMeaning.clauses table) received)
    (instanceReading : NativeInstanceReadback.Reading contract received)
    (products : NativeFieldPacking.Readings ops received)
    (other : OperatorFamilies.{w}) (assignment : Assignment.{w})

include logical casesReading instanceReading products in
theorem native_functional_bisimulation (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol)
    (domains : model.InhabitedDomains) (sameModel : model = profile.frame.model other assignment)
    (allow : NativeInstanceReadback.Signature.Allow (native := signature ops) model) :
    FunctionalBisimulation (targetTheory (nativeClause table model domains contract allow)).Step
      (sourceTheory (fun source (event : Event ops model) target =>
        contract.instanceValue model allow source event.1 event.2 target)).Step
      (observe (NativeFieldPacking.semanticPack ops model)) :=
  functional_bisimulation (nativeClause table model domains contract allow) (NativeFieldPacking.semanticPack ops model)
    (fun source event target => contract.instanceValue model allow source event.1 event.2 target)
    (nativeCorrespondence table contract profile logical casesReading instanceReading products other assignment
      model domains sameModel allow) (by intro source current; rfl)

include logical casesReading instanceReading products in
abbrev received_functional_bisimulation :=
  native_functional_bisimulation table contract profile logical casesReading instanceReading products other assignment
    (profile.frame.model other assignment) (NativeFieldExecution.sourceDomains profile.frame other assignment) rfl

include logical casesReading instanceReading products in
theorem native_future_lift (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol)
    (domains : model.InhabitedDomains) (sameModel : model = profile.frame.model other assignment)
    (allow : NativeInstanceReadback.Signature.Allow (native := signature ops) model)
    {first : NativeRecordRunsCorrespondence.Configuration
      (fun name => HOL.Ty.denote.{0,w+1} model.Carrier (name.type ops)) (Event ops model)}
    {last : QueueState ((signature ops).State model) (Event ops model)}
    (path : Relation.ReflTransGen
      (sourceTheory (fun source (event : Event ops model) target =>
        contract.instanceValue model allow source event.1 event.2 target)).Step
      (observe (NativeFieldPacking.semanticPack ops model) first) last) :
    ∃ finish, Relation.ReflTransGen (targetTheory (nativeClause table model domains contract allow)).Step first finish ∧
      observe (NativeFieldPacking.semanticPack ops model) finish = last :=
  Zag.path (native_functional_bisimulation table contract profile logical casesReading instanceReading products other assignment
    model domains sameModel allow).zag path first rfl

include logical casesReading instanceReading products in
abbrev received_future_lift :=
  native_future_lift table contract profile logical casesReading instanceReading products other assignment
    (profile.frame.model other assignment) (NativeFieldExecution.sourceDomains profile.frame other assignment) rfl

include logical casesReading instanceReading products in
theorem native_diamond (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol)
    (domains : model.InhabitedDomains) (sameModel : model = profile.frame.model other assignment)
    (allow : NativeInstanceReadback.Signature.Allow (native := signature ops) model)
    (predicate : QueueState ((signature ops).State model) (Event ops model) → Prop) :
    pb (observe (NativeFieldPacking.semanticPack ops model))
        (derivedDiamond (span (sourceTheory (fun source (event : Event ops model) target =>
          contract.instanceValue model allow source event.1 event.2 target)).Step) predicate) =
      derivedDiamond (span (targetTheory (nativeClause table model domains contract allow)).Step)
        (pb (observe (NativeFieldPacking.semanticPack ops model)) predicate) :=
  pb_diamond (native_functional_bisimulation table contract profile logical casesReading instanceReading products
    other assignment model domains sameModel allow) predicate

include logical casesReading instanceReading products in
theorem native_forwardBox (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol)
    (domains : model.InhabitedDomains) (sameModel : model = profile.frame.model other assignment)
    (allow : NativeInstanceReadback.Signature.Allow (native := signature ops) model)
    (predicate : QueueState ((signature ops).State model) (Event ops model) → Prop) :
    pb (observe (NativeFieldPacking.semanticPack ops model))
        (derivedForwardBox (span (sourceTheory (fun source (event : Event ops model) target =>
          contract.instanceValue model allow source event.1 event.2 target)).Step) predicate) =
      derivedForwardBox (span (targetTheory (nativeClause table model domains contract allow)).Step)
        (pb (observe (NativeFieldPacking.semanticPack ops model)) predicate) :=
  pb_forwardBox (native_functional_bisimulation table contract profile logical casesReading instanceReading products
    other assignment model domains sameModel allow) predicate

end Native

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.NativeRecordRunsOpenMap
