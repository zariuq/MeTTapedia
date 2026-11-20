import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Kernel.NativeRecordRunsInformation

/-! Actual source-instance words and constrained-information queue runs.
The interpretation and explicit permission stay fixed. This different source
representation supplies no prepared-certificate or native-consumer lifecycle.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.NativeRecordRuns

open Mettapedia.Logic Mettapedia.Languages.OpenTheory Mettapedia.Languages.HOLLight
open NativeClauseData NativeFieldSchema InterpretedFrames
open ProofExecution TypeFamilySemantics

universe u v w

attribute [local irreducible] NativeClauseData.signature
attribute [local irreducible] RegisteredReplayModels.Frame.model

/-- Labelled finite closure retains the actual intermediate source states.
The relation parameter is instantiated below by the existing native instance
meaning, rather than a replacement record evaluator. -/
inductive WordData {State : Type u} {Event : Type v} (edge : State → Event → State → Prop) :
    State → List Event → State → Type (max u v)
  | nil (state : State) : WordData edge state [] state
  | cons {source middle target : State} {first : Event} {rest : List Event}
      (firstStep : edge source first middle) (later : WordData edge middle rest target) :
      WordData edge source (first :: rest) target

abbrev SourceWord {ops : Operations} (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol)
    (contract : NativeInstanceReadback.Signature (signature ops))
    (allow : NativeInstanceReadback.Signature.Allow (native := signature ops) model) :=
  WordData (fun source (event : Event ops model) target =>
    contract.instanceValue model allow source event.1 event.2 target)

abbrev StoreData (Cell : Field → Type u) (Event : Type u) :=
  RuleSyntax.State (Terms.{u,u} (AtomData Cell Event)) Occurrence

structure PointData {Cell : Field → Type u} {Event : Type u}
    (state : StoreData Cell Event) (cursor : Nat) (pending : List Event) where
  layout : Layout
  environment : state.frame.Carrier
  fields : (name : Field) → Cell name
  view : ViewData state layout environment fields cursor pending

namespace PointData

variable {Cell : Field → Type u} {Event : Type u} {state : StoreData Cell Event}
    {cursor : Nat} {pending : List Event}

def reindex (point : PointData state cursor pending) {nextCursor : Nat} (same : cursor = nextCursor) :
    PointData state nextCursor pending := same ▸ point

theorem reindex_environment (point : PointData state cursor pending) {nextCursor : Nat} (same : cursor = nextCursor) :
    (point.reindex same).environment = point.environment := by cases same; rfl

theorem reindex_fields (point : PointData state cursor pending) {nextCursor : Nat} (same : cursor = nextCursor) :
    (point.reindex same).fields = point.fields := by cases same; rfl

end PointData

/-- An actual run and a satisfying readout of its actual last state. Its
final environment restricts to the supplied old environment. Native model
instantiation changes none of these abstract data. -/
structure ExecutionData {Cell : Field → Type u} {Event : Type u}
    (rules : RuleSyntax.Program (Terms.{u,u} (AtomData Cell Event))) (state : StoreData Cell Event)
    (start : state.frame.Carrier) (cursor : Nat) (pending : List Event) (steps : Nat) where
  run : (RuleSyntax.step (frames.{u,u} (AtomData Cell Event)) Occurrence extensions rules).toStep.Run state
  point : PointData run.last cursor pending
  count : run.word.length = steps
  restricts : run.toLast point.environment = start

namespace ExecutionData

variable {Cell : Field → Type u} {Event : Type u}
    {rules : RuleSyntax.Program (Terms.{u,u} (AtomData Cell Event))} {state : StoreData Cell Event}
    {start : state.frame.Carrier} {cursor : Nat} {pending : List Event} {steps : Nat}

def layout (execution : ExecutionData rules state start cursor pending steps) : Layout := execution.point.layout
def environment (execution : ExecutionData rules state start cursor pending steps) : execution.run.last.frame.Carrier :=
  execution.point.environment
def fields (execution : ExecutionData rules state start cursor pending steps) : (name : Field) → Cell name :=
  execution.point.fields
theorem view (execution : ExecutionData rules state start cursor pending steps) :
    ViewData execution.run.last execution.layout execution.environment execution.fields cursor pending :=
  execution.point.view

def reindex (execution : ExecutionData rules state start cursor pending steps)
    {nextCursor nextSteps : Nat} (cursorSame : cursor = nextCursor) (stepsSame : steps = nextSteps) :
    ExecutionData rules state start nextCursor pending nextSteps := cursorSame ▸ stepsSame ▸ execution

theorem reindex_fields (execution : ExecutionData rules state start cursor pending steps)
    {nextCursor nextSteps : Nat} (cursorSame : cursor = nextCursor) (stepsSame : steps = nextSteps) :
    (execution.reindex cursorSame stepsSame).fields = execution.fields := by
  cases cursorSame
  cases stepsSame
  rfl

end ExecutionData

namespace QueueClause

variable {Cell : Field → Type u} {Record : Type u} {Effect : Frame.{u}}
    (clause : QueueClause Cell Record Effect)
    {rules : RuleSyntax.Program (Terms (AtomData Cell (Record × Effect.Carrier)))}
    (member : clause.rule ∈ rules)
    (state : StoreData Cell (Record × Effect.Carrier)) (generation : Field → Nat) (cursor : Nat)
    (environment : state.frame.Carrier) (fields : (name : Field) → Cell name)
    (pending : List (Record × Effect.Carrier))
    (view : ViewData state (canonicalLayout generation cursor) environment fields cursor pending)
    (locals : clause.localFrame.Carrier)
    (same : ∀ name, fields name = clause.before name locals.values)
    (sameCursor : locals.cursor = cursor)
    (samePending : pending = (clause.record locals.values, locals.effect) :: locals.tail)
    (valid : clause.guard locals.values locals.effect)
    (admitted : (RuleSyntax.step (frames (AtomData Cell (Record × Effect.Carrier))) Occurrence extensions rules).Admits
      (s := state) (clause.firing member (selectionFor clause.writes generation cursor)))

/-- Pairing the old environment with fresh locals occurs only in this
generic context. The native caller earns `admitted` from its source facts. -/
def one_step_execution : ExecutionData rules state environment (cursor+1) locals.tail 1 := by
  let active := clause.firing member (old := state.frame) (selectionFor clause.writes generation cursor)
  have solved := clause.satisfies_of_view member state generation cursor environment fields pending view locals
    same sameCursor samePending valid
  have lastView := clause.result_view member state generation cursor admitted (environment, locals) solved
    fields pending view
  exact {
    run := .cons active admitted (.nil _)
    point := {
      layout := canonicalLayout (generationAfter clause.writes generation) (cursor+1)
      environment := (environment, locals)
      fields := fun name => clause.after name locals.values
      view := lastView }
    count := rfl
    restricts := rfl }

theorem one_step_layout :
    (clause.one_step_execution member state generation cursor environment fields pending view locals same
      sameCursor samePending valid admitted).layout =
      canonicalLayout (generationAfter clause.writes generation) (cursor+1) := rfl

theorem one_step_fields :
    (clause.one_step_execution member state generation cursor environment fields pending view locals same
      sameCursor samePending valid admitted).fields = (fun name => clause.after name locals.values) := rfl

theorem one_step_view :
    let execution := clause.one_step_execution member state generation cursor environment fields pending view locals same
      sameCursor samePending valid admitted
    ViewData execution.run.last (canonicalLayout (generationAfter clause.writes generation) (cursor+1))
      execution.environment execution.fields (cursor+1) locals.tail :=
  (clause.one_step_execution member state generation cursor environment fields pending view locals same
    sameCursor samePending valid admitted).view

theorem one_step_observe {Observation : Type v} (observe : ((name : Field) → Cell name) → Observation)
    (target : Observation) (expected : observe (fun name => clause.after name locals.values) = target) :
    observe (clause.one_step_execution member state generation cursor environment fields pending view locals same
      sameCursor samePending valid admitted).fields = target :=
  (congrArg observe (clause.one_step_fields member state generation cursor environment fields pending view locals same
    sameCursor samePending valid admitted)).trans expected

def prepend_execution {finalCursor count : Nat} {residual : List (Record × Effect.Carrier)}
    (later : ExecutionData rules
      (clause.one_step_execution member state generation cursor environment fields pending view locals same
        sameCursor samePending valid admitted).run.last
      (clause.one_step_execution member state generation cursor environment fields pending view locals same
        sameCursor samePending valid admitted).environment finalCursor residual count) :
    ExecutionData rules state environment finalCursor residual (count+1) := by
  let active := clause.firing member (old := state.frame) (selectionFor clause.writes generation cursor)
  exact {
    run := .cons active admitted later.run
    point := later.point
    count := by simp only [Step.Run.word, List.length_cons, later.count]
    restricts := congrArg Prod.fst later.restricts }

theorem prepend_fields {finalCursor count : Nat} {residual : List (Record × Effect.Carrier)}
    (later : ExecutionData rules
      (clause.one_step_execution member state generation cursor environment fields pending view locals same
        sameCursor samePending valid admitted).run.last
      (clause.one_step_execution member state generation cursor environment fields pending view locals same
        sameCursor samePending valid admitted).environment finalCursor residual count) :
    (clause.prepend_execution member state generation cursor environment fields pending view locals same
      sameCursor samePending valid admitted later).fields = later.fields := rfl

end QueueClause

namespace QueueClause

variable {Cell : Field → Type u} {Record : Type u} {Effect : Frame.{u}}
    (clause : QueueClause Cell Record Effect)
    {rules : RuleSyntax.Program (Terms (AtomData Cell (Record × Effect.Carrier)))}
    (member : clause.rule ∈ rules)
    (state : StoreData Cell (Record × Effect.Carrier)) (layout : Layout) (cursor : Nat)
    (environment : state.frame.Carrier) (fields : (name : Field) → Cell name)
    (pending : List (Record × Effect.Carrier))
    (view : ViewData state layout environment fields cursor pending) (locals : clause.localFrame.Carrier)
    (same : ∀ name, fields name = clause.before name locals.values)
    (sameCursor : locals.cursor = cursor)
    (samePending : pending = (clause.record locals.values, locals.effect) :: locals.tail)
    (valid : clause.guard locals.values locals.effect)

/-- Fresh identities are constructed against the actual current support,
irrespective of their constructor names or earlier canonical generations. -/
def one_step_at_execution : ExecutionData rules state environment (cursor+1) locals.tail 1 := by
  let made := NativeRecordLayouts.allocate layout clause.writes
  let selected := selectionAt layout clause.writes made
  let active := clause.firing member (old := state.frame) selected
  have admitted := clause.admitted_at_view member state layout environment fields cursor pending view locals
    same sameCursor samePending valid made (NativeRecordLayouts.allocate_length layout clause.writes)
    (NativeRecordLayouts.allocate_nodup layout clause.writes) (NativeRecordLayouts.allocate_fresh layout clause.writes)
  have solved := clause.satisfies_at_view member state layout environment fields cursor pending view locals
    same sameCursor samePending valid made
  let replacement := NativeRecordLayouts.allocateReplacement layout clause.writes clause.writes_distinct
  have input : clause.InputData state layout fields cursor pending locals selected :=
    ⟨rfl, rfl, sameCursor, samePending, same⟩
  have lastView := clause.result_at_view member state clause.localFrame Prod.snd selected [] admitted
    (environment, locals) solved layout fields cursor pending view input replacement
  exact {
    run := .cons active admitted (.nil _)
    point := {
      layout := replacement.next
      environment := (environment, locals)
      fields := fun name => clause.after name locals.values
      view := lastView }
    count := rfl
    restricts := rfl }

theorem one_step_at_observe {Observation : Type v} (observe : ((name : Field) → Cell name) → Observation)
    (target : Observation) (expected : observe (fun name => clause.after name locals.values) = target) :
    observe (clause.one_step_at_execution member state layout cursor environment fields pending view locals same
      sameCursor samePending valid).fields = target := expected

def prepend_at_execution {finalCursor count : Nat} {residual : List (Record × Effect.Carrier)}
    (later : ExecutionData rules
      (clause.one_step_at_execution member state layout cursor environment fields pending view locals same
        sameCursor samePending valid).run.last
      (clause.one_step_at_execution member state layout cursor environment fields pending view locals same
        sameCursor samePending valid).environment finalCursor residual count) :
    ExecutionData rules state environment finalCursor residual (count+1) := by
  let made := NativeRecordLayouts.allocate layout clause.writes
  let active := clause.firing member (old := state.frame) (selectionAt layout clause.writes made)
  have admitted := clause.admitted_at_view member state layout environment fields cursor pending view locals
    same sameCursor samePending valid made (NativeRecordLayouts.allocate_length layout clause.writes)
    (NativeRecordLayouts.allocate_nodup layout clause.writes) (NativeRecordLayouts.allocate_fresh layout clause.writes)
  exact {
    run := .cons active admitted later.run
    point := later.point
    count := by simp only [Step.Run.word, List.length_cons, later.count]
    restricts := congrArg Prod.fst later.restricts }

theorem prepend_at_fields {finalCursor count : Nat} {residual : List (Record × Effect.Carrier)}
    (later : ExecutionData rules
      (clause.one_step_at_execution member state layout cursor environment fields pending view locals same
        sameCursor samePending valid).run.last
      (clause.one_step_at_execution member state layout cursor environment fields pending view locals same
        sameCursor samePending valid).environment finalCursor residual count) :
    (clause.prepend_at_execution member state layout cursor environment fields pending view locals same
      sameCursor samePending valid later).fields = later.fields := rfl

end QueueClause

def familyProgram {Cell : Field → Type u} {Record : Type u} {Effect : Frame.{u}} {Index : Type v}
    (clauses : Index → QueueClause Cell Record Effect) :
    RuleSyntax.Program (Terms.{u,u} (AtomData Cell (Record × Effect.Carrier))) :=
  Set.range (fun index => (clauses index).rule)

/-- Complete pointwise inversion retains the actual firing, rule identity,
opened locals, ordered selections and result state. -/
structure MoveData {Cell : Field → Type u} {Record : Type u} {Effect : Frame.{u}} {Index : Type v}
    (clauses : Index → QueueClause Cell Record Effect) (state : StoreData Cell (Record × Effect.Carrier))
    (actual : RuleSyntax.Firing Occurrence extensions (familyProgram clauses) state.frame)
    (environment : (actual.result (frames (AtomData Cell (Record × Effect.Carrier))) state).frame.Carrier)
    (layout : Layout) (fields : (name : Field) → Cell name) (cursor : Nat)
    (pending : List (Record × Effect.Carrier)) where
  index : Index
  locals : (clauses index).localFrame.Carrier
  ruleSame : actual.rule = (clauses index).rule
  openingSame : HEq (actual.opening environment) locals
  input : (clauses index).InputData state layout fields cursor pending locals actual.selection
  valid : (clauses index).guard locals.values locals.effect
  replacement : NativeRecordLayouts.Replacement layout (clauses index).writes actual.selection.made
  result : ViewData (actual.result (frames (AtomData Cell (Record × Effect.Carrier))) state)
    replacement.next environment (fun name => (clauses index).after name locals.values) (cursor+1) locals.tail

theorem invert_move {Cell : Field → Type u} {Record : Type u} {Effect : Frame.{u}} {Index : Type v}
    (clauses : Index → QueueClause Cell Record Effect) (state : StoreData Cell (Record × Effect.Carrier))
    (actual : RuleSyntax.Firing Occurrence extensions (familyProgram clauses) state.frame)
    (admitted : (RuleSyntax.step (frames (AtomData Cell (Record × Effect.Carrier))) Occurrence extensions
      (familyProgram clauses)).Admits (s := state) actual)
    (environment : (actual.result (frames (AtomData Cell (Record × Effect.Carrier))) state).frame.Carrier)
    (satisfies : Satisfies (actual.result (frames (AtomData Cell (Record × Effect.Carrier))) state).knowledge environment)
    (layout : Layout) (fields : (name : Field) → Cell name) (cursor : Nat)
    (pending : List (Record × Effect.Carrier))
    (view : ViewData state layout environment.1 fields cursor pending) :
    Nonempty (MoveData clauses state actual environment layout fields cursor pending) := by
  rcases actual with ⟨code, codeMember, extension, opening, selected, seen⟩
  obtain ⟨index, rfl⟩ := codeMember
  let present : (clauses index).rule ∈ familyProgram clauses := ⟨index, rfl⟩
  let inversion := (clauses index).invert_at present state extension opening selected seen admitted
    environment satisfies layout fields cursor pending view
  exact ⟨{
    index := index
    locals := opening environment
    ruleSame := rfl
    openingSame := HEq.rfl
    input := inversion.input
    valid := inversion.valid
    replacement := inversion.replacement
    result := inversion.result }⟩

theorem run_satisfies_start {Cell : Field → Type u} {Event : Type u}
    {rules : RuleSyntax.Program (Terms.{u,u} (AtomData Cell Event))} {state : StoreData Cell Event}
    (run : (RuleSyntax.step (frames.{u,u} (AtomData Cell Event)) Occurrence extensions rules).toStep.Run state)
    (environment : run.last.frame.Carrier) (satisfies : Satisfies run.last.knowledge environment) :
    Satisfies state.knowledge (run.toLast environment) := by
  have lastModels := (InterpretedFrames.models_iff (fun _ : ground.{u}.Carrier => environment) _).mpr
    (fun _ => satisfies)
  have earlier := run.models_start (fun _ : ground.{u}.Carrier => environment) lastModels
  exact (InterpretedFrames.models_iff _ _).mp earlier PUnit.unit

theorem run_satisfiable {Cell : Field → Type u} {Event : Type u}
    {rules : RuleSyntax.Program (Terms.{u,u} (AtomData Cell Event))} {state : StoreData Cell Event}
    (run : (RuleSyntax.step (frames.{u,u} (AtomData Cell Event)) Occurrence extensions rules).toStep.Run state) :
    (∃ environment, Satisfies state.knowledge environment) →
      ∃ environment, Satisfies run.last.knowledge environment := by
  induction run with
  | nil state => exact id
  | @cons state actual admitted rest ih =>
      intro _initial
      exact ih ((InterpretedFrames.solvable_iff _).mp admitted.2.2.1)

theorem ground_environment_unique (environment : ground.{u}.Carrier) : environment = PUnit.unit := by
  cases environment
  rfl

structure ReflectionData {Cell : Field → Type u} {Event : Type u} {Observation : Type v}
    (rules : RuleSyntax.Program (Terms.{u,u} (AtomData Cell Event)))
    (observe : ((name : Field) → Cell name) → Observation) (edge : Observation → Event → Observation → Prop)
    {state : StoreData Cell Event}
    (run : (RuleSyntax.step (frames.{u,u} (AtomData Cell Event)) Occurrence extensions rules).toStep.Run state)
    (environment : run.last.frame.Carrier) (fields : (name : Field) → Cell name) (cursor : Nat) (pending : List Event) where
  events : List Event
  remaining : List Event
  input : pending = events ++ remaining
  count : run.word.length = events.length
  point : PointData run.last (cursor+events.length) remaining
  environmentSame : point.environment = environment
  word : WordData edge (observe fields) events (observe point.fields)

namespace ReflectionData

variable {Cell : Field → Type u} {Event : Type u} {Observation : Type v}
    {rules : RuleSyntax.Program (Terms.{u,u} (AtomData Cell Event))}
    {observe : ((name : Field) → Cell name) → Observation} {edge : Observation → Event → Observation → Prop}
    {state : StoreData Cell Event}
    {run : (RuleSyntax.step (frames.{u,u} (AtomData Cell Event)) Occurrence extensions rules).toStep.Run state}
    {environment : run.last.frame.Carrier} {fields : (name : Field) → Cell name} {cursor : Nat} {pending : List Event}

theorem count_input (reflection : ReflectionData rules observe edge run environment fields cursor pending) :
    run.word.length + reflection.remaining.length = pending.length := by
  exact (congrArg (fun count => count + reflection.remaining.length) reflection.count).trans
    ((show (reflection.events ++ reflection.remaining).length =
        reflection.events.length + reflection.remaining.length from List.length_append).symm.trans
      (congrArg List.length reflection.input).symm)

theorem bounded (reflection : ReflectionData rules observe edge run environment fields cursor pending) :
    run.word.length ≤ pending.length := by
  have exactCount := reflection.count_input
  omega

end ReflectionData

abbrev Reflects {Cell : Field → Type u} {Record : Type u} {Effect : Frame.{u}} {Index : Type v}
    {Observation : Type w} (clauses : Index → QueueClause Cell Record Effect)
    (observe : ((name : Field) → Cell name) → Observation)
    (edge : Observation → (Record × Effect.Carrier) → Observation → Prop) :=
  ∀ {state : StoreData Cell (Record × Effect.Carrier)}
    (run : (RuleSyntax.step (frames (AtomData Cell (Record × Effect.Carrier))) Occurrence extensions
      (familyProgram clauses)).toStep.Run state)
    (environment : run.last.frame.Carrier) (_satisfies : Satisfies run.last.knowledge environment)
    (layout : Layout) (fields : (name : Field) → Cell name) (cursor : Nat) (pending : List (Record × Effect.Carrier)),
    ViewData state layout (run.toLast environment) fields cursor pending →
    Nonempty (ReflectionData (familyProgram clauses) observe edge run environment fields cursor pending)

/-- Finite input bounds every actual run from a uniformly observed live
queue. Initial satisfiability and every solution's queue view are explicit;
no default consistency or preservation of every old solution is assumed. -/
theorem bounded_runs {Cell : Field → Type u} {Record : Type u} {Effect : Frame.{u}} {Index : Type v}
    {Observation : Type w} (clauses : Index → QueueClause Cell Record Effect)
    (observe : ((name : Field) → Cell name) → Observation)
    (edge : Observation → (Record × Effect.Carrier) → Observation → Prop)
    (reflection : Reflects clauses observe edge)
    (state : StoreData Cell (Record × Effect.Carrier)) (layout : Layout) (cursor : Nat)
    (pending : List (Record × Effect.Carrier))
    (initially : ∀ environment, Satisfies state.knowledge environment →
      ∃ fields, ViewData state layout environment fields cursor pending)
    (satisfiable : ∃ environment, Satisfies state.knowledge environment)
    (run : (RuleSyntax.step (frames (AtomData Cell (Record × Effect.Carrier))) Occurrence extensions
      (familyProgram clauses)).toStep.Run state) : run.word.length ≤ pending.length := by
  obtain ⟨environment, satisfied⟩ := run_satisfiable run satisfiable
  obtain ⟨fields, view⟩ := initially (run.toLast environment) (run_satisfies_start run environment satisfied)
  obtain ⟨readout⟩ := reflection run environment satisfied layout fields cursor pending view
  exact readout.bounded

/-- A technical observed-run lemma. A concrete source endpoint must earn
the clause interpretation; native callers below derive it from read facts. -/
theorem reflect_run {Cell : Field → Type u} {Record : Type u} {Effect : Frame.{u}} {Index : Type v}
    {Observation : Type w} (clauses : Index → QueueClause Cell Record Effect)
    (observe : ((name : Field) → Cell name) → Observation)
    (edge : Observation → (Record × Effect.Carrier) → Observation → Prop)
    (caseMeaning : ∀ index values effect, (clauses index).guard values effect →
      edge (observe (fun name => (clauses index).before name values))
        ((clauses index).record values, effect) (observe (fun name => (clauses index).after name values)))
    {state : StoreData Cell (Record × Effect.Carrier)}
    (run : (RuleSyntax.step (frames (AtomData Cell (Record × Effect.Carrier))) Occurrence extensions
      (familyProgram clauses)).toStep.Run state) :
    ∀ (environment : run.last.frame.Carrier) (_satisfies : Satisfies run.last.knowledge environment)
      (layout : Layout) (fields : (name : Field) → Cell name) (cursor : Nat) (pending : List (Record × Effect.Carrier)),
      ViewData state layout (run.toLast environment) fields cursor pending →
      Nonempty (ReflectionData (familyProgram clauses) observe edge run environment fields cursor pending) := by
  induction run with
  | nil state =>
      intro environment _satisfies layout fields cursor pending view
      exact ⟨{
        events := []
        remaining := pending
        input := rfl
        count := rfl
        point := { layout := layout, environment := environment, fields := fields, view := view }
        environmentSame := rfl
        word := .nil _ }⟩
  | @cons state actual admitted rest ih =>
      intro environment satisfies layout fields cursor pending view
      have nextSatisfies := run_satisfies_start rest environment satisfies
      obtain ⟨move⟩ := invert_move clauses state actual admitted (rest.toLast environment) nextSatisfies
        layout fields cursor pending view
      obtain ⟨following⟩ := ih environment satisfies move.replacement.next
        (fun name => (clauses move.index).after name move.locals.values)
        (cursor+1) move.locals.tail move.result
      let event := ((clauses move.index).record move.locals.values, move.locals.effect)
      have firstStep : edge (observe fields) event
          (observe (fun name => (clauses move.index).after name move.locals.values)) := by
        have before := congrArg observe (funext move.input.fieldsSame)
        rw [before]
        exact caseMeaning move.index move.locals.values move.locals.effect move.valid
      have cursorSame : cursor+1+following.events.length = cursor+(event :: following.events).length := by
        simp only [List.length_cons]
        omega
      let point := following.point.reindex cursorSame
      have finalFields : point.fields = following.point.fields := PointData.reindex_fields _ _
      have word : WordData edge (observe fields) (event :: following.events) (observe point.fields) := by
        rw [finalFields]
        exact .cons firstStep following.word
      exact ⟨{
        events := event :: following.events
        remaining := following.remaining
        input := move.input.pendingSame.trans (congrArg (List.cons event) following.input)
        count := by simpa only [Step.Run.word, List.length_cons] using congrArg (fun count => count+1) following.count
        point := point
        environmentSame := (PointData.reindex_environment _ _).trans following.environmentSame
        word := word }⟩

variable {ops : Operations} (table : Fin 29 → Syntax ops)
    (contract : NativeInstanceReadback.Signature (signature ops))
    {received : Registered.State} (profile : SourceProfileModels.ProfileFrame.{w} received)
    (logical : NativeFieldMeaning.LogicalOperations ops)
    (casesReading : NativeClauseReadback.Reading (signature ops) (NativeFieldMeaning.clauses table) received)
    (instanceReading : NativeInstanceReadback.Reading contract received)
    (products : NativeFieldPacking.Readings ops received)
    (other : OperatorFamilies.{w}) (assignment : Assignment.{w})

theorem beforeState_pack (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol) (index : Fin 29)
    (values : model.Valuation ((table index).locals.map Ty.toHOL)) :
    beforeState table model index values = NativeFieldPacking.semanticPack ops model
      (NativeFieldPacking.denoteFields model (table index).before values) :=
  NativeFieldPacking.pack_denote ops model (table index).before values

theorem afterState_pack (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol) (index : Fin 29)
    (values : model.Valuation ((table index).locals.map Ty.toHOL)) :
    afterState table model index values = NativeFieldPacking.semanticPack ops model
      (NativeFieldPacking.denoteFields model (table index).after values) :=
  NativeFieldPacking.pack_denote ops model (table index).after values

abbrev native_invert_move (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol)
    (domains : model.InhabitedDomains)
    (allow : NativeInstanceReadback.Signature.Allow (native := signature ops) model) :=
  invert_move (nativeClause table model domains contract allow)

theorem familyProgram_native (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol)
    (domains : model.InhabitedDomains)
    (allow : NativeInstanceReadback.Signature.Allow (native := signature ops) model) :
    familyProgram (nativeClause table model domains contract allow) = program table model domains contract allow := rfl

include logical casesReading instanceReading in
theorem instance_iff_obligation :
    let model := profile.frame.model other assignment
    ∀ allow source record effect target,
      contract.instanceValue model allow source record effect target ↔
        ∃ index values,
          source = beforeState table model index values ∧
          record = recordValue table model index values ∧
          target = afterState table model index values ∧
          obligation table model contract allow index values effect := by
  dsimp only
  intro allow source record effect target
  rw [NativeReceivedFrame.instance_meaning profile contract instanceReading other assignment,
    NativeReceivedFrame.field_cases profile ops logical table casesReading other assignment]
  constructor
  · rintro ⟨⟨index, values, before, recordSame, after, guard⟩, effectSame, permitted⟩
    refine ⟨index, values, before, recordSame, after, guard, ?_, ?_⟩
    · simpa only [beforeState, afterState, recordValue, ← before, ← recordSame, ← after] using effectSame
    · simpa only [beforeState, recordValue, ← before, ← recordSame] using permitted
  · rintro ⟨index, values, before, recordSame, after, valid⟩
    refine ⟨⟨index, values, before, recordSame, after, valid.1⟩, ?_, ?_⟩
    · simpa only [← before, ← recordSame, ← after] using valid.2.1
    · simpa only [← before, ← recordSame] using valid.2.2

include logical casesReading instanceReading in
theorem case_instance (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol)
    (sameModel : model = profile.frame.model other assignment) :
    ∀ allow index values effect, obligation table model contract allow index values effect →
      contract.instanceValue model allow (beforeState table model index values)
        (recordValue table model index values) effect (afterState table model index values) := by
  cases sameModel
  intro allow index values effect valid
  exact (instance_iff_obligation table contract profile logical casesReading instanceReading other assignment
    allow _ _ _ _).mpr ⟨index, values, rfl, rfl, rfl, valid⟩

include logical casesReading instanceReading in
/-- Native reflection earns its source-edge interpretation from the received
instance and case equations, not a caller-supplied simulation premise. -/
theorem source_reflects (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol)
    (domains : model.InhabitedDomains) (sameModel : model = profile.frame.model other assignment) :
    ∀ (allow : NativeInstanceReadback.Signature.Allow (native := signature ops) model),
      Reflects (Cell := fun name => HOL.Ty.denote.{0,w+1} model.Carrier (name.type ops))
        (Record := (signature ops).Record model) (Effect := effectFrame (ops := ops) model domains)
        (Index := Fin 29) (Observation := (signature ops).State model)
        (nativeClause table model domains contract allow) (NativeFieldPacking.semanticPack ops model)
        (fun source event target => contract.instanceValue model allow source event.1 event.2 target) := by
  intro allow
  have licensed : ∀ index values effect, (nativeClause table model domains contract allow index).guard values effect →
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
  intro state run
  exact reflect_run (nativeClause table model domains contract allow) (NativeFieldPacking.semanticPack ops model)
    (fun source event target => contract.instanceValue model allow source event.1 event.2 target) licensed run

include logical casesReading instanceReading in
abbrev source_reflects_received :=
  source_reflects table contract profile logical casesReading instanceReading other assignment
    (profile.frame.model other assignment) (NativeFieldExecution.sourceDomains profile.frame other assignment) rfl

include logical casesReading instanceReading products in
/-- Every actual source-instance word has a run from the actual current
queue state. Its final solution extends the supplied old solution, and its
residual input, firing count and packed result are exact. -/
theorem source_word (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol)
    (domains : model.InhabitedDomains) (sameModel : model = profile.frame.model other assignment) :
    ∀ (allow : NativeInstanceReadback.Signature.Allow (native := signature ops) model)
      {source target : (signature ops).State model} {events : List (Event ops model)},
      SourceWord model contract allow source events target →
      ∀ (state : StoreData (fun name => HOL.Ty.denote.{0,w+1} model.Carrier (name.type ops)) (Event ops model))
        (environment : state.frame.Carrier) (fields : NativeFieldPacking.Fields ops model)
        (generation : Field → Nat) (cursor : Nat) (remaining : List (Event ops model)),
        View model state (canonicalLayout generation cursor) environment fields cursor (events ++ remaining) →
        NativeFieldPacking.semanticPack ops model fields = source →
        ∃ execution : ExecutionData (program table model domains contract allow) state environment
            (cursor + events.length) remaining events.length,
          NativeFieldPacking.semanticPack ops model execution.fields = target := by
  have nativeChoice : ∀ allow source record effect target,
      contract.instanceValue model allow source record effect target ↔
        ∃ index values, source = beforeState table model index values ∧
          record = recordValue table model index values ∧ target = afterState table model index values ∧
          obligation table model contract allow index values effect := by
    cases sameModel
    exact instance_iff_obligation table contract profile logical casesReading instanceReading other assignment
  have packing : Function.Injective (NativeFieldPacking.semanticPack ops model) := by
    cases sameModel
    exact NativeReceivedFrame.packing_injective profile ops products other assignment
  intro allow source target events word
  induction word with
  | nil source =>
      intro state environment fields generation cursor remaining view begins
      refine ⟨{
        run := .nil state
        point := {
          layout := canonicalLayout generation cursor
          environment := environment
          fields := fields
          view := by simpa only [Step.Run.last, List.nil_append, List.length_nil, Nat.add_zero] using view }
        count := rfl
        restricts := rfl }, begins⟩
  | @cons source middle target first rest firstStep later ih =>
      intro state environment fields generation cursor remaining view begins
      obtain ⟨index, values, before, recordSame, after, valid⟩ :=
        (nativeChoice allow source first.1 first.2 middle).mp firstStep
      let locals : Local table model index := ⟨cursor, rest ++ remaining, values, first.2⟩
      have sameFields : fields = NativeFieldPacking.denoteFields model (table index).before values :=
        packing ((begins.trans before).trans (beforeState_pack table model index values))
      have same : ∀ name, fields name = model.denote ((table index).before name) values :=
        fun name => congrFun sameFields name
      have samePending : first :: (rest ++ remaining) =
          (recordValue table model index values, first.2) :: (rest ++ remaining) :=
        congrArg (fun event => event :: (rest ++ remaining)) (Prod.ext recordSame rfl)
      have admitted := admitted_of_view table model domains contract allow state index generation cursor environment
        fields (first :: (rest ++ remaining)) view locals same rfl samePending valid
      let next := QueueClause.one_step_execution (nativeClause table model domains contract allow index)
        (rule_member table model domains contract allow index) state generation cursor environment fields
        (first :: (rest ++ remaining)) view locals same rfl samePending valid admitted
      have nextView : View model next.run.last
          (canonicalLayout (nextGeneration table index generation) (cursor+1))
          next.environment next.fields (cursor+1) (rest ++ remaining) := by
        exact QueueClause.one_step_view (nativeClause table model domains contract allow index)
          (rule_member table model domains contract allow index) state generation cursor environment fields
          (first :: (rest ++ remaining)) view locals same rfl samePending valid admitted
      have nextPacked : NativeFieldPacking.semanticPack ops model next.fields = middle := by
        apply QueueClause.one_step_observe (nativeClause table model domains contract allow index)
          (rule_member table model domains contract allow index) state generation cursor environment fields
          (first :: (rest ++ remaining)) view locals same rfl samePending valid admitted
          (NativeFieldPacking.semanticPack ops model) middle
        exact (afterState_pack table model index values).symm.trans after.symm
      have continuation : ∃ execution : ExecutionData (program table model domains contract allow)
          next.run.last next.environment (cursor+1+rest.length) remaining rest.length,
          NativeFieldPacking.semanticPack ops model execution.fields = target := by
        exact ih next.run.last next.environment next.fields
          (nextGeneration table index generation) (cursor+1) remaining nextView nextPacked
      obtain ⟨following, final⟩ := continuation
      let joined := QueueClause.prepend_execution (nativeClause table model domains contract allow index)
        (rule_member table model domains contract allow index) state generation cursor environment fields
        (first :: (rest ++ remaining)) view locals same rfl samePending valid admitted following
      have cursorSame : cursor+1+rest.length = cursor+(first :: rest).length := by
        simp only [List.length_cons]
        omega
      refine ⟨joined.reindex cursorSame rfl, ?_⟩
      have fieldsSame := ExecutionData.reindex_fields joined cursorSame rfl
      have prepended := QueueClause.prepend_fields (nativeClause table model domains contract allow index)
        (rule_member table model domains contract allow index) state generation cursor environment fields
        (first :: (rest ++ remaining)) view locals same rfl samePending valid admitted following
      exact (congrArg (NativeFieldPacking.semanticPack ops model) (fieldsSame.trans prepended)).trans final

include logical casesReading instanceReading products in
/-- The actual received-frame instance uses this same model by reflexivity;
no separately chosen replay interpretation is equated with it. -/
theorem source_word_received :
    let model := profile.frame.model other assignment
    let domains := NativeFieldExecution.sourceDomains profile.frame other assignment
    ∀ (allow : NativeInstanceReadback.Signature.Allow (native := signature ops) model)
      {source target : (signature ops).State model} {events : List (Event ops model)},
      SourceWord model contract allow source events target →
      ∀ (state : StoreData (fun name => HOL.Ty.denote.{0,w+1} model.Carrier (name.type ops)) (Event ops model))
        (environment : state.frame.Carrier) (fields : NativeFieldPacking.Fields ops model)
        (generation : Field → Nat) (cursor : Nat) (remaining : List (Event ops model)),
        View model state (canonicalLayout generation cursor) environment fields cursor (events ++ remaining) →
        NativeFieldPacking.semanticPack ops model fields = source →
        ∃ execution : ExecutionData (program table model domains contract allow) state environment
            (cursor + events.length) remaining events.length,
          NativeFieldPacking.semanticPack ops model execution.fields = target := by
  dsimp only
  exact source_word table contract profile logical casesReading instanceReading products other assignment
    (profile.frame.model other assignment)
    (NativeFieldExecution.sourceDomains profile.frame other assignment) rfl

include logical casesReading instanceReading products in
/-- Every actual source-instance word has a run from the actual current
queue state. Its final solution extends the supplied old solution, and its
residual input, firing count and packed result are exact, from any exact current layout. -/
theorem source_word_at (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol)
    (domains : model.InhabitedDomains) (sameModel : model = profile.frame.model other assignment) :
    ∀ (allow : NativeInstanceReadback.Signature.Allow (native := signature ops) model)
      {source target : (signature ops).State model} {events : List (Event ops model)},
      SourceWord model contract allow source events target →
      ∀ (state : StoreData (fun name => HOL.Ty.denote.{0,w+1} model.Carrier (name.type ops)) (Event ops model))
        (environment : state.frame.Carrier) (fields : NativeFieldPacking.Fields ops model)
        (layout : Layout) (cursor : Nat) (remaining : List (Event ops model)),
        View model state layout environment fields cursor (events ++ remaining) →
        NativeFieldPacking.semanticPack ops model fields = source →
        ∃ execution : ExecutionData (program table model domains contract allow) state environment
            (cursor + events.length) remaining events.length,
          NativeFieldPacking.semanticPack ops model execution.fields = target := by
  have nativeChoice : ∀ allow source record effect target,
      contract.instanceValue model allow source record effect target ↔
        ∃ index values, source = beforeState table model index values ∧
          record = recordValue table model index values ∧ target = afterState table model index values ∧
          obligation table model contract allow index values effect := by
    cases sameModel
    exact instance_iff_obligation table contract profile logical casesReading instanceReading other assignment
  have packing : Function.Injective (NativeFieldPacking.semanticPack ops model) := by
    cases sameModel
    exact NativeReceivedFrame.packing_injective profile ops products other assignment
  intro allow source target events word
  induction word with
  | nil source =>
      intro state environment fields layout cursor remaining view begins
      refine ⟨{
        run := .nil state
        point := {
          layout := layout
          environment := environment
          fields := fields
          view := by simpa only [Step.Run.last, List.nil_append, List.length_nil, Nat.add_zero] using view }
        count := rfl
        restricts := rfl }, begins⟩
  | @cons source middle target first rest firstStep later ih =>
      intro state environment fields layout cursor remaining view begins
      obtain ⟨index, values, before, recordSame, after, valid⟩ :=
        (nativeChoice allow source first.1 first.2 middle).mp firstStep
      let locals : Local table model index := ⟨cursor, rest ++ remaining, values, first.2⟩
      have sameFields : fields = NativeFieldPacking.denoteFields model (table index).before values :=
        packing ((begins.trans before).trans (beforeState_pack table model index values))
      have same : ∀ name, fields name = model.denote ((table index).before name) values :=
        fun name => congrFun sameFields name
      have samePending : first :: (rest ++ remaining) =
          (recordValue table model index values, first.2) :: (rest ++ remaining) :=
        congrArg (fun event => event :: (rest ++ remaining)) (Prod.ext recordSame rfl)
      let next := QueueClause.one_step_at_execution (nativeClause table model domains contract allow index)
        (rule_member table model domains contract allow index) state layout cursor environment fields
        (first :: (rest ++ remaining)) view locals same rfl samePending valid
      have nextPacked : NativeFieldPacking.semanticPack ops model next.fields = middle := by
        apply QueueClause.one_step_at_observe (nativeClause table model domains contract allow index)
          (rule_member table model domains contract allow index) state layout cursor environment fields
          (first :: (rest ++ remaining)) view locals same rfl samePending valid
          (NativeFieldPacking.semanticPack ops model) middle
        exact (afterState_pack table model index values).symm.trans after.symm
      have continuation : ∃ execution : ExecutionData (program table model domains contract allow)
          next.run.last next.environment (cursor+1+rest.length) remaining rest.length,
          NativeFieldPacking.semanticPack ops model execution.fields = target := by
        exact ih next.run.last next.environment next.fields next.layout (cursor+1) remaining next.view nextPacked
      obtain ⟨following, final⟩ := continuation
      let joined := QueueClause.prepend_at_execution (nativeClause table model domains contract allow index)
        (rule_member table model domains contract allow index) state layout cursor environment fields
        (first :: (rest ++ remaining)) view locals same rfl samePending valid following
      have cursorSame : cursor+1+rest.length = cursor+(first :: rest).length := by
        simp only [List.length_cons]
        omega
      refine ⟨joined.reindex cursorSame rfl, ?_⟩
      have fieldsSame := ExecutionData.reindex_fields joined cursorSame rfl
      have prepended := QueueClause.prepend_at_fields (nativeClause table model domains contract allow index)
        (rule_member table model domains contract allow index) state layout cursor environment fields
        (first :: (rest ++ remaining)) view locals same rfl samePending valid following
      exact (congrArg (NativeFieldPacking.semanticPack ops model) (fieldsSame.trans prepended)).trans final

include logical casesReading instanceReading products in
abbrev source_word_at_received :=
  source_word_at table contract profile logical casesReading instanceReading products other assignment
    (profile.frame.model other assignment) (NativeFieldExecution.sourceDomains profile.frame other assignment) rfl

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.NativeRecordRuns
