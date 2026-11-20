import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Kernel.NativeRecordRunsRealization
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Execution

/-!
# Solution-indexed operational readback of native record runs

A configuration retains an actual queue state and one satisfying point of
its knowledge, with the exact live layout. All such points are retained in
the carrier. A lifted event is an actual admitted firing whose result point
restricts to its starting point; it contains no source-transition premise.

The ordinary successor theory forgets firing identities. A separate event
projection below retains the actual firing and its occurrence in the path.
The interpretation is the named constrained-information queue: store bag;
commit one match; guards after the firing's own tells; rules fixed; one store.
It does not choose a primitive policy for other step constructions.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.NativeRecordRunsCorrespondence

open Mettapedia.Logic Mettapedia.Languages.OpenTheory Mettapedia.Languages.HOLLight
open NativeFieldSchema InterpretedFrames NativeRecordRuns
open Mettapedia.GSLT Mettapedia.GSLT.IndexedOperational Mettapedia.GSLT.Ultrainfinite
open FragmentsOfTheStep.TransitionMaps

universe u v w

theorem view_observables {Cell : Field → Type u} {Event : Type u}
    {state : StoreData Cell Event} {environment : state.frame.Carrier}
    {firstLayout secondLayout : Layout} {firstFields secondFields : (name : Field) → Cell name}
    {firstCursor secondCursor : Nat} {firstPending secondPending : List Event}
    (first : ViewData state firstLayout environment firstFields firstCursor firstPending)
    (second : ViewData state secondLayout environment secondFields secondCursor secondPending) :
    firstFields = secondFields ∧ firstCursor = secondCursor ∧ firstPending = secondPending := by
  have requestPresent : secondLayout.request ∈ state.present := by
    rw [second.exact]
    exact Finset.mem_insert_self _ _
  obtain ⟨_request, cursor, pending⟩ := first.pending_slot requestPresent _ _ second.request.symm
  refine ⟨?_, cursor.symm, pending.symm⟩
  funext name
  have fieldPresent : secondLayout.field name ∈ state.present := by
    rw [second.exact]
    exact field_in_support secondLayout name
  have sameSlot := first.field_slot fieldPresent name (secondFields name) (second.field name).symm
  apply atom_field_injective name
  rw [← first.field name, ← second.field name, sameSlot]

@[ext] structure QueueState (Observation : Type v) (Event : Type u) where
  value : Observation
  cursor : Nat
  pending : List Event

def QueueStep {Observation : Type v} {Event : Type u}
    (edge : Observation → Event → Observation → Prop)
    (before after : QueueState Observation Event) : Prop :=
  ∃ event remaining, before.pending = event :: remaining ∧
    after.cursor = before.cursor+1 ∧ after.pending = remaining ∧ edge before.value event after.value

structure Configuration (Cell : Field → Type u) (Event : Type u) where
  state : StoreData Cell Event
  cursor : Nat
  pending : List Event
  point : PointData state cursor pending

def observe {Cell : Field → Type u} {Event : Type u} {Observation : Type v}
    (read : ((name : Field) → Cell name) → Observation)
    (configuration : Configuration Cell Event) : QueueState Observation Event :=
  ⟨read configuration.point.fields, configuration.cursor, configuration.pending⟩

inductive PointedEvent {Cell : Field → Type u} {Record : Type u} {Effect : Frame.{u}} {Index : Type v}
    (clauses : Index → QueueClause Cell Record Effect) :
    Configuration Cell (Record × Effect.Carrier) → Configuration Cell (Record × Effect.Carrier) →
      Type (max (u+1) v) where
  | fire {state : StoreData Cell (Record × Effect.Carrier)} {cursor : Nat}
      {pending : List (Record × Effect.Carrier)}
      (before : PointData state cursor pending)
      (actual : RuleSyntax.Firing Occurrence extensions (familyProgram clauses) state.frame)
      (admitted : (RuleSyntax.step (frames (AtomData Cell (Record × Effect.Carrier)))
        Occurrence extensions (familyProgram clauses)).Admits (s := state) actual)
      {nextCursor : Nat} {nextPending : List (Record × Effect.Carrier)}
      (after : PointData (actual.result (frames (AtomData Cell (Record × Effect.Carrier))) state)
        nextCursor nextPending)
      (restriction : after.environment.1 = before.environment) :
      PointedEvent clauses ⟨state, cursor, pending, before⟩
        ⟨actual.result (frames (AtomData Cell (Record × Effect.Carrier))) state,
          nextCursor, nextPending, after⟩

abbrev rawStep {Cell : Field → Type u} {Record : Type u} {Effect : Frame.{u}} {Index : Type v}
    (clauses : Index → QueueClause Cell Record Effect) :=
  (RuleSyntax.step (frames (AtomData Cell (Record × Effect.Carrier))) Occurrence extensions
    (familyProgram clauses)).toStep

def targetTheory {Cell : Field → Type u} {Record : Type u} {Effect : Frame.{u}} {Index : Type v}
    (clauses : Index → QueueClause Cell Record Effect) : GSLT :=
  theoryOf (Configuration Cell (Record × Effect.Carrier)) (fun before after =>
    Nonempty (PointedEvent clauses before after))

def sourceTheory {Observation : Type v} {Event : Type u}
    (edge : Observation → Event → Observation → Prop) : GSLT :=
  theoryOf (QueueState Observation Event) (QueueStep edge)

theorem event_reads_step {Cell : Field → Type u} {Record : Type u} {Effect : Frame.{u}} {Index : Type v}
    {Observation : Type w} (clauses : Index → QueueClause Cell Record Effect)
    (read : ((name : Field) → Cell name) → Observation)
    (edge : Observation → (Record × Effect.Carrier) → Observation → Prop)
    (caseMeaning : ∀ index values effect, (clauses index).guard values effect →
      edge (read (fun name => (clauses index).before name values))
        ((clauses index).record values, effect) (read (fun name => (clauses index).after name values)))
    {before after : Configuration Cell (Record × Effect.Carrier)}
    (event : PointedEvent clauses before after) : QueueStep edge (observe read before) (observe read after) := by
  cases event with
  | fire start actual admitted finish restriction =>
      have oldView := start.view
      rw [← restriction] at oldView
      obtain ⟨move⟩ := invert_move clauses _ actual admitted finish.environment finish.view.solved
        start.layout start.fields _ _ oldView
      obtain ⟨fieldsSame, cursorSame, pendingSame⟩ := view_observables move.result finish.view
      refine ⟨((clauses move.index).record move.locals.values, move.locals.effect),
        move.locals.tail, move.input.pendingSame, cursorSame.symm, pendingSame.symm, ?_⟩
      have firstSame : start.fields = fun name => (clauses move.index).before name move.locals.values :=
        funext move.input.fieldsSame
      have source := caseMeaning move.index move.locals.values move.locals.effect move.valid
      rw [← firstSame, fieldsSame] at source
      exact source

def observationTranslation {Cell : Field → Type u} {Record : Type u} {Effect : Frame.{u}} {Index : Type v}
    {Observation : Type w} (clauses : Index → QueueClause Cell Record Effect)
    (read : ((name : Field) → Cell name) → Observation)
    (edge : Observation → (Record × Effect.Carrier) → Observation → Prop)
    (caseMeaning : ∀ index values effect, (clauses index).guard values effect →
      edge (read (fun name => (clauses index).before name values))
        ((clauses index).record values, effect) (read (fun name => (clauses index).after name values))) :
    OperationalTranslation (targetTheory clauses) (sourceTheory edge) where
  mapTerm := observe read
  mapEquiv := fun same => congrArg (observe read) same
  mapStep := by
    rintro before after ⟨event⟩
    exact event_reads_step clauses read edge caseMeaning event

def readback {Cell : Field → Type u} {Record : Type u} {Effect : Frame.{u}} {Index : Type v}
    {Observation : Type w} (clauses : Index → QueueClause Cell Record Effect)
    (read : ((name : Field) → Cell name) → Observation)
    (edge : Observation → (Record × Effect.Carrier) → Observation → Prop)
    (caseMeaning : ∀ index values effect, (clauses index).guard values effect →
      edge (read (fun name => (clauses index).before name values))
        ((clauses index).record values, effect) (read (fun name => (clauses index).after name values))) :
    OperationalReadback (sourceTheory edge) (targetTheory clauses) where
  related source target := observe read target = source
  readStep := by
    rintro source current next same ⟨event⟩
    exact .inr ⟨observe read next,
      same ▸ event_reads_step clauses read edge caseMeaning event, rfl⟩

def forgetTranslation {Cell : Field → Type u} {Record : Type u} {Effect : Frame.{u}} {Index : Type v}
    (clauses : Index → QueueClause Cell Record Effect) :
    OperationalTranslation (targetTheory clauses) (Execution.theory (rawStep clauses)) where
  mapTerm := Configuration.state
  mapEquiv := fun same => congrArg Configuration.state same
  mapStep := by
    rintro before after ⟨event⟩
    cases event with
    | fire start actual admitted finish restriction => exact ⟨actual, admitted, rfl⟩

def forgetEvent {Cell : Field → Type u} {Record : Type u} {Effect : Frame.{u}} {Index : Type v}
    {clauses : Index → QueueClause Cell Record Effect}
    {before after : Configuration Cell (Record × Effect.Carrier)} (event : PointedEvent clauses before after) :
    (rawStep clauses).toEffectCore.Event (rawStep clauses).eventAdmission before.state after.state := by
  cases event with
  | fire start actual admitted finish restriction => exact (rawStep clauses).event actual admitted

def forgetPath {Cell : Field → Type u} {Record : Type u} {Effect : Frame.{u}} {Index : Type v}
    {clauses : Index → QueueClause Cell Record Effect} :
    {before after : Configuration Cell (Record × Effect.Carrier)} →
    Route (PointedEvent clauses) before after → Execution.EventPath (rawStep clauses) before.state after.state
  | _, _, .refl _ => .refl _
  | _, _, .cons event rest => .cons (forgetEvent event) (forgetPath rest)

theorem forgetPath_length {Cell : Field → Type u} {Record : Type u} {Effect : Frame.{u}} {Index : Type v}
    {clauses : Index → QueueClause Cell Record Effect}
    {before after : Configuration Cell (Record × Effect.Carrier)}
    (path : Route (PointedEvent clauses) before after) : (forgetPath path).length = path.length := by
  induction path with
  | refl => rfl
  | cons event rest ih => exact congrArg (fun count => count+1) ih

def firingWord {Cell : Field → Type u} {Record : Type u} {Effect : Frame.{u}} {Index : Type v}
    {clauses : Index → QueueClause Cell Record Effect} :
    {before after : Configuration Cell (Record × Effect.Carrier)} →
    Route (PointedEvent clauses) before after →
      List ((state : StoreData Cell (Record × Effect.Carrier)) ×
        RuleSyntax.Firing Occurrence extensions (familyProgram clauses) state.frame)
  | _, _, .refl _ => []
  | before, _, .cons event rest =>
      ⟨before.state, (forgetEvent event).firing⟩ :: firingWord rest

theorem forgetPath_firings {Cell : Field → Type u} {Record : Type u} {Effect : Frame.{u}} {Index : Type v}
    {clauses : Index → QueueClause Cell Record Effect}
    {before after : Configuration Cell (Record × Effect.Carrier)}
    (path : Route (PointedEvent clauses) before after) :
    Execution.eventWord (rawStep clauses) (forgetPath path) = firingWord path := by
  induction path with
  | refl => rfl
  | cons event rest ih => exact congrArg (List.cons _) ih

theorem firingWord_length {Cell : Field → Type u} {Record : Type u} {Effect : Frame.{u}} {Index : Type v}
    {clauses : Index → QueueClause Cell Record Effect}
    {before after : Configuration Cell (Record × Effect.Carrier)}
    (path : Route (PointedEvent clauses) before after) : (firingWord path).length = path.length := by
  induction path with
  | refl => rfl
  | cons event rest ih => exact congrArg (fun count => count+1) ih

/-- A lift of the supplied raw execution, including its actual firing word.
No new raw execution or final solution is substituted for either input. -/
structure RunLiftData {Cell : Field → Type u} {Record : Type u} {Effect : Frame.{u}} {Index : Type v}
    (clauses : Index → QueueClause Cell Record Effect)
    {state : StoreData Cell (Record × Effect.Carrier)} {cursor : Nat}
    {pending : List (Record × Effect.Carrier)} (start : PointData state cursor pending)
    (run : (rawStep clauses).Run state) (environment : run.last.frame.Carrier) where
  finalCursor : Nat
  remaining : List (Record × Effect.Carrier)
  point : PointData run.last finalCursor remaining
  environmentSame : point.environment = environment
  path : Route (PointedEvent clauses) ⟨state, cursor, pending, start⟩
    ⟨run.last, finalCursor, remaining, point⟩
  projected : forgetPath path = Execution.toEvents (rawStep clauses) run

/-- Every actual finite run, at every supplied satisfying final point, has
a pointed lift that retains the same firings. This coverage law is separate
from the source observation law. -/
theorem lift_run {Cell : Field → Type u} {Record : Type u} {Effect : Frame.{u}} {Index : Type v}
    (clauses : Index → QueueClause Cell Record Effect)
    {state : StoreData Cell (Record × Effect.Carrier)} (run : (rawStep clauses).Run state) :
    ∀ (environment : run.last.frame.Carrier) (_satisfies : Satisfies run.last.knowledge environment)
      {cursor : Nat} {pending : List (Record × Effect.Carrier)} (start : PointData state cursor pending),
      run.toLast environment = start.environment → Nonempty (RunLiftData clauses start run environment) := by
  induction run with
  | nil state =>
      intro environment _satisfies cursor pending start restriction
      exact ⟨{
        finalCursor := cursor
        remaining := pending
        point := start
        environmentSame := restriction.symm
        path := .refl _
        projected := rfl }⟩
  | @cons state actual admitted rest ih =>
      intro environment satisfies cursor pending start restriction
      have nextSatisfies := run_satisfies_start rest environment satisfies
      have oldView := start.view
      rw [← restriction] at oldView
      obtain ⟨move⟩ := invert_move clauses state actual admitted (rest.toLast environment) nextSatisfies
        start.layout start.fields cursor pending oldView
      let middle : PointData (actual.result (frames (AtomData Cell (Record × Effect.Carrier))) state)
          (cursor+1) move.locals.tail := {
        layout := move.replacement.next
        environment := rest.toLast environment
        fields := fun name => (clauses move.index).after name move.locals.values
        view := move.result }
      obtain ⟨following⟩ := ih environment satisfies middle rfl
      let first : PointedEvent clauses ⟨state, cursor, pending, start⟩
          ⟨actual.result (frames (AtomData Cell (Record × Effect.Carrier))) state,
            cursor+1, move.locals.tail, middle⟩ :=
        PointedEvent.fire start actual admitted middle restriction
      refine ⟨{
        finalCursor := following.finalCursor
        remaining := following.remaining
        point := following.point
        environmentSame := following.environmentSame
        path := .cons first following.path
        projected := ?_ }⟩
      simpa only [forgetPath, Execution.toEvents, first, forgetEvent] using
        congrArg (Route.cons ((rawStep clauses).event actual admitted)) following.projected

theorem RunLiftData.exact_firing_word {Cell : Field → Type u} {Record : Type u} {Effect : Frame.{u}}
    {Index : Type v} {clauses : Index → QueueClause Cell Record Effect}
    {state : StoreData Cell (Record × Effect.Carrier)} {cursor : Nat}
    {pending : List (Record × Effect.Carrier)} {start : PointData state cursor pending}
    {run : (rawStep clauses).Run state} {environment : run.last.frame.Carrier}
    (lift : RunLiftData clauses start run environment) : firingWord lift.path = run.word := by
  rw [← forgetPath_firings, lift.projected, Execution.eventWord_toEvents]

theorem RunLiftData.exact_length {Cell : Field → Type u} {Record : Type u} {Effect : Frame.{u}}
    {Index : Type v} {clauses : Index → QueueClause Cell Record Effect}
    {state : StoreData Cell (Record × Effect.Carrier)} {cursor : Nat}
    {pending : List (Record × Effect.Carrier)} {start : PointData state cursor pending}
    {run : (rawStep clauses).Run state} {environment : run.last.frame.Carrier}
    (lift : RunLiftData clauses start run environment) : lift.path.length = run.word.length := by
  exact (firingWord_length lift.path).symm.trans (congrArg List.length lift.exact_firing_word)

theorem lift_run_of_subsingleton {Cell : Field → Type u} {Record : Type u} {Effect : Frame.{u}}
    {Index : Type v} (clauses : Index → QueueClause Cell Record Effect)
    {state : StoreData Cell (Record × Effect.Carrier)} [Subsingleton state.frame.Carrier]
    {cursor : Nat} {pending : List (Record × Effect.Carrier)} (start : PointData state cursor pending)
    (run : (rawStep clauses).Run state) (environment : run.last.frame.Carrier)
    (satisfies : Satisfies run.last.knowledge environment) : Nonempty (RunLiftData clauses start run environment) :=
  lift_run clauses run environment satisfies start
    (@Subsingleton.elim state.frame.Carrier inferInstance (run.toLast environment) start.environment)

def toTheoryPath {Cell : Field → Type u} {Record : Type u} {Effect : Frame.{u}} {Index : Type v}
    {clauses : Index → QueueClause Cell Record Effect} :
    {before after : Configuration Cell (Record × Effect.Carrier)} →
    Route (PointedEvent clauses) before after → ExecutionPath (targetTheory clauses) before after
  | _, _, .refl _ => .refl _
  | _, _, .cons event rest => .cons ⟨⟨event⟩⟩ (toTheoryPath rest)

theorem toTheoryPath_length {Cell : Field → Type u} {Record : Type u} {Effect : Frame.{u}} {Index : Type v}
    {clauses : Index → QueueClause Cell Record Effect}
    {before after : Configuration Cell (Record × Effect.Carrier)}
    (path : Route (PointedEvent clauses) before after) : (toTheoryPath path).length = path.length := by
  induction path with
  | refl => rfl
  | cons event rest ih => exact congrArg (fun count => count+1) ih

/-- Convert concrete, environment-preserving execution lifts into the
existing operational-correspondence interface. The native instance below
earns these lifts from the received source-word theorem. -/
def correspondence {Cell : Field → Type u} {Record : Type u} {Effect : Frame.{u}} {Index : Type v}
    {Observation : Type w} (clauses : Index → QueueClause Cell Record Effect)
    (read : ((name : Field) → Cell name) → Observation)
    (edge : Observation → (Record × Effect.Carrier) → Observation → Prop)
    (caseMeaning : ∀ index values effect, (clauses index).guard values effect →
      edge (read (fun name => (clauses index).before name values))
        ((clauses index).record values, effect) (read (fun name => (clauses index).after name values)))
    (sourceLifts : ∀ (current : Configuration Cell (Record × Effect.Carrier)) event remaining target,
      current.pending = event :: remaining → edge (read current.point.fields) event target →
      ∃ execution : ExecutionData (familyProgram clauses) current.state current.point.environment
          (current.cursor+1) remaining 1, read execution.fields = target) :
    OperationalCorrespondence (sourceTheory edge) (targetTheory clauses) where
  toOperationalReadback := readback clauses read edge caseMeaning
  forward := by
    rintro origin after current related sourceStep
    cases related
    obtain ⟨event, remaining, input, cursor, pending, edgeHolds⟩ := sourceStep
    obtain ⟨execution, targetSame⟩ := sourceLifts current event remaining after.value input edgeHolds
    obtain ⟨lift⟩ := lift_run clauses execution.run execution.environment execution.view.solved
      current.point execution.restricts
    have finalView := lift.point.view
    rw [lift.environmentSame] at finalView
    obtain ⟨fieldsSame, cursorSame, pendingSame⟩ := view_observables finalView execution.view
    let final : Configuration Cell (Record × Effect.Carrier) :=
      ⟨execution.run.last, lift.finalCursor, lift.remaining, lift.point⟩
    refine ⟨final, ⟨toTheoryPath lift.path⟩, ?_⟩
    apply QueueState.ext
    · exact (congrArg read fieldsSame).trans targetSame
    · exact cursorSame.trans cursor.symm
    · exact pendingSame.trans pending.symm

/-- The word-lifting theorem is consumed in its actual flat interface.
Configuration packaging occurs at abstract cell types, before specializing
the intrinsically typed native model. -/
def correspondence_of_words {Cell : Field → Type u} {Record : Type u} {Effect : Frame.{u}} {Index : Type v}
    {Observation : Type w} (clauses : Index → QueueClause Cell Record Effect)
    (read : ((name : Field) → Cell name) → Observation)
    (edge : Observation → (Record × Effect.Carrier) → Observation → Prop)
    (caseMeaning : ∀ index values effect, (clauses index).guard values effect →
      edge (read (fun name => (clauses index).before name values))
        ((clauses index).record values, effect) (read (fun name => (clauses index).after name values)))
    (wordLifts : ∀ {source target : Observation} {events : List (Record × Effect.Carrier)},
      WordData edge source events target →
      ∀ (state : StoreData Cell (Record × Effect.Carrier))
        (environment : state.frame.Carrier) (fields : (name : Field) → Cell name)
        (layout : Layout) (cursor : Nat) (remaining : List (Record × Effect.Carrier)),
        ViewData state layout environment fields cursor (events ++ remaining) → read fields = source →
        ∃ execution : ExecutionData (familyProgram clauses) state environment
            (cursor+events.length) remaining events.length, read execution.fields = target) :
    OperationalCorrespondence (sourceTheory edge) (targetTheory clauses) :=
  correspondence clauses read edge caseMeaning (by
    intro current event remaining target input sourceStep
    let word : WordData edge (read current.point.fields) [event] target := .cons sourceStep (.nil target)
    have view : ViewData current.state current.point.layout current.point.environment current.point.fields
        current.cursor (event :: remaining) := input ▸ current.point.view
    exact wordLifts word current.state current.point.environment current.point.fields
      current.point.layout current.cursor remaining view rfl)

section Native

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

include logical casesReading instanceReading in
theorem native_case (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol)
    (domains : model.InhabitedDomains) (sameModel : model = profile.frame.model other assignment)
    (allow : NativeInstanceReadback.Signature.Allow (native := signature ops) model) :
    ∀ index values effect, (nativeClause table model domains contract allow index).guard values effect →
      contract.instanceValue model allow
        (NativeFieldPacking.semanticPack ops model
          (fun name => (nativeClause table model domains contract allow index).before name values))
        ((nativeClause table model domains contract allow index).record values) effect
        (NativeFieldPacking.semanticPack ops model
          (fun name => (nativeClause table model domains contract allow index).after name values)) := by
  intro index values effect valid
  have actual := case_instance table contract profile logical casesReading instanceReading other assignment
    model sameModel allow index values effect valid
  exact Eq.mp (congrArg₂ (fun (before after : (signature ops).State model) =>
    contract.instanceValue model allow before (recordValue table model index values) effect after)
    (beforeState_pack table model index values) (afterState_pack table model index values)) actual

include logical casesReading instanceReading in
noncomputable def nativeReadback (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol)
    (domains : model.InhabitedDomains) (sameModel : model = profile.frame.model other assignment)
    (allow : NativeInstanceReadback.Signature.Allow (native := signature ops) model) :=
  readback (nativeClause table model domains contract allow) (NativeFieldPacking.semanticPack ops model)
    (fun source event target => contract.instanceValue model allow source event.1 event.2 target)
    (native_case table contract profile logical casesReading instanceReading other assignment model domains sameModel allow)

include logical casesReading instanceReading products in
noncomputable def nativeCorrespondence (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol)
    (domains : model.InhabitedDomains) (sameModel : model = profile.frame.model other assignment)
    (allow : NativeInstanceReadback.Signature.Allow (native := signature ops) model) :=
  correspondence_of_words (nativeClause table model domains contract allow) (NativeFieldPacking.semanticPack ops model)
    (fun source event target => contract.instanceValue model allow source event.1 event.2 target)
    (native_case table contract profile logical casesReading instanceReading other assignment model domains sameModel allow)
    (source_word_at table contract profile logical casesReading instanceReading products other assignment
      model domains sameModel allow)

include logical casesReading instanceReading in
noncomputable abbrev receivedReadback :=
  nativeReadback table contract profile logical casesReading instanceReading other assignment
    (profile.frame.model other assignment) (NativeFieldExecution.sourceDomains profile.frame other assignment) rfl

include logical casesReading instanceReading products in
noncomputable abbrev receivedCorrespondence :=
  nativeCorrespondence table contract profile logical casesReading instanceReading products other assignment
    (profile.frame.model other assignment) (NativeFieldExecution.sourceDomains profile.frame other assignment) rfl

end Native

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.NativeRecordRunsCorrespondence
