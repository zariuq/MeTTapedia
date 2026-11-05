import Mettapedia.Languages.MeTTa.PeTTa.Bridges.FirstQueryCursor
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.OncePrimitiveSource

/-!
# First-witness queries with inert scalar payloads

The authored payload may be a symbol such as `t`, a Boolean, or another
grounded scalar. It remains the actual first answer. A later presence
observer may forget its value; query execution itself may not replace it
with true or interpret false as absence. Expression-shaped and variable
templates need separate source-body certificates.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.ConstantQuerySource

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open Mettapedia.Languages.ProcessCalculi.MORK (applySubst Subst)
open EagerDFS (World)
open EagerDFS.Destination NamedSpaces SpaceSemantics

inductive Scalar : Atom → Prop where
  | symbol (name : String) : Scalar (.symbol name)
  | grounded (value : GroundedValue) : Scalar (.grounded value)

def isScalar : Atom → Bool
  | .symbol _ | .grounded _ => true
  | _ => false

theorem isScalar_iff (atom : Atom) : isScalar atom = true ↔ Scalar atom := by
  cases atom with
  | symbol name => exact ⟨fun _ => .symbol name, fun _ => rfl⟩
  | grounded value => exact ⟨fun _ => .grounded value, fun _ => rfl⟩
  | var | expression => constructor <;> intro impossible <;> cases impossible

theorem Scalar.subst {payload : Atom} (scalar : Scalar payload) (bindings : Subst) :
    applySubst bindings payload = payload := by cases scalar <;> rfl

theorem Scalar.read {payload : Atom} (scalar : Scalar payload) (environment : Environment) :
    EagerDFS.Destination.read environment payload = payload := by
  cases scalar <;> simp [EagerDFS.Destination.read, encode, decode]

theorem Scalar.freeVars {payload : Atom} (scalar : Scalar payload) :
    (encode payload).freeVars = ∅ := by
  cases scalar <;> simp [encode, Mettapedia.Logic.LP.Term.freeVars]

theorem Scalar.copy {payload : Atom} (scalar : Scalar payload) (token : Token) :
    EagerDFS.Collection.copyAllocated token payload [] = (payload, []) := by
  cases scalar <;> simp [EagerDFS.Collection.copyAllocated, HE.Spec.Type.RuntimeRefinement.renameTypeVars]

theorem Scalar.allocateCopy {payload : Atom} (scalar : Scalar payload) (allocator : Allocator)
    (protectedNames : Finset String) :
    EagerDFS.Collection.allocateCopy? allocator protectedNames payload [] =
      EagerDFS.Collection.allocateAnswer? allocator := by
  cases scalar <;> simp [EagerDFS.Collection.allocateCopy?, EagerDFS.Collection.allocateAnswer?,
    EagerDFS.Collection.answerInventory, EagerDFS.Destination.ClauseChoice.names,
    HE.Spec.Type.Presentation.TypeSubst.typeVars]

theorem cursor_hit_has_first_answer (pattern payload : Atom) (scalar : Scalar payload)
    (rows : List Atom) (fuel : Nat) (entry : Nat × Subst)
    (found : (FirstQueryCursor.machine [] pattern).run fuel (0, rows) = ([], .finished (some entry))) :
    ∃ tail, query rows pattern payload = payload :: tail := by
  have first := FirstQueryCursor.finished_exact [] pattern fuel 0 rows (some entry) found
  have head : (query rows pattern payload).head? = some payload := by
    rw [FirstQueryCursor.query_first, ← first]
    simp only [Option.map_some, scalar.subst]
  cases values : query rows pattern payload with
  | nil => simp [values] at head
  | cons first tail =>
      have same : first = payload := by simpa [values] using head
      exact ⟨tail, by simp [same]⟩

theorem cursor_miss_has_no_answers (pattern payload : Atom) (rows : List Atom) (fuel : Nat)
    (missed : (FirstQueryCursor.machine [] pattern).run fuel (0, rows) = ([], .finished none)) :
    query rows pattern payload = [] := by
  have first := FirstQueryCursor.finished_exact [] pattern fuel 0 rows none missed
  have head : (query rows pattern payload).head? = none := by
    rw [FirstQueryCursor.query_first, ← first]
    rfl
  simpa using head

theorem primitive_query (state : Effects.State) (handle : Handle) (rows : List Atom)
    (pattern payload : Atom) (snapshot : state.read handle = some rows) :
    StdLib.apply state "match" [Effects.handleValue handle, pattern, payload] =
      .ok (state, query rows pattern payload) := by
  change (match Effects.readHandle (Effects.handleValue handle) >>= state.read with
    | some values => Except.ok (state, query values pattern payload)
    | none => Except.error Effects.Fault.invalidSpace) = _
  simp [snapshot]

theorem first_query_prefix {Context : Type} (policy : Policy) (program : Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (control : Control) (context : Context)
    (origins : List Nat) (inside kept : List (CollectionWork Context)) (previousBoundary : Nat)
    (arguments : List Atom) (destination pattern payload : Atom) (scalar : Scalar payload)
    (handle : Handle) (rows : List Atom) (fuel : Nat) (entry : Nat × Subst)
    (environment afterEnvironment : Environment) (bindings : Equations)
    (frontier : scope.frontier = (control, context, origins) :: inside ++ kept)
    (atCall : control.goals = [.invoke "match" arguments destination, .commit, .restoreCommit previousBoundary])
    (boundary : control.cutBoundary = kept.length)
    (resolved : resolve control.bindings = some environment)
    (operands : arguments.map (EagerDFS.Destination.read environment) = [Effects.handleValue handle, pattern, payload])
    (snapshot : world.state.read handle = some rows)
    (found : (FirstQueryCursor.machine [] pattern).run fuel (0, rows) = ([], .finished (some entry)))
    (refined : refine control.bindings payload destination = some bindings)
    (afterResolved : resolve bindings = some afterEnvironment) :
    let answer : CollectedAnswer := ⟨EagerDFS.Destination.read afterEnvironment control.destination, bindings, origins ++ [0], []⟩
    let after : ScopedCursor Context := (allocator, ⟨world, EagerDFS.Scope.record scope kept answer :: parents⟩)
    (EagerDFSStreaming.machine program (.scopedDestination Context policy)).run 5
      (allocator, ⟨world, scope :: parents⟩) =
      (if scope.caller.isNone then [answer] else [], .exhausted after) := by
  obtain ⟨tail, first⟩ := cursor_hit_has_first_answer pattern payload scalar rows fuel entry found
  have applied : StdLib.apply world.state "match" (arguments.map (EagerDFS.Destination.read environment)) =
      .ok (world.state, payload :: tail) := by
    rw [operands, primitive_query world.state handle rows pattern payload snapshot, first]
  exact OncePrimitiveSource.first_answer_prefix policy program allocator world scope parents control context
    origins inside kept previousBoundary "match" arguments destination payload tail environment afterEnvironment
    bindings world.state frontier atCall boundary resolved (by decide) (by decide) applied refined afterResolved

theorem empty_query_keeps_outer_work {Context : Type} (policy : Policy) (program : Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (control : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context)) (arguments : List Atom)
    (destination pattern payload : Atom) (older : List Goal) (handle : Handle) (rows : List Atom) (fuel : Nat)
    (environment : Environment)
    (frontier : scope.frontier = (control, context, origins) :: pending)
    (atCall : control.goals = .invoke "match" arguments destination :: older)
    (resolved : resolve control.bindings = some environment)
    (operands : arguments.map (EagerDFS.Destination.read environment) = [Effects.handleValue handle, pattern, payload])
    (snapshot : world.state.read handle = some rows)
    (missed : (FirstQueryCursor.machine [] pattern).run fuel (0, rows) = ([], .finished none)) :
    scopeStep policy program (allocator, ⟨world, scope :: parents⟩) =
      .silent (allocator, ⟨world, {scope with frontier := pending} :: parents⟩) := by
  have applied : StdLib.apply world.state "match" (arguments.map (EagerDFS.Destination.read environment)) = .ok (world.state, []) := by
    rw [operands, primitive_query world.state handle rows pattern payload snapshot,
      cursor_miss_has_no_answers pattern payload rows fuel missed]
  exact OncePrimitiveSource.empty_primitive_keeps_outer_work policy program allocator world scope parents
    control context origins pending "match" arguments destination older environment world.state frontier atCall
    resolved (by decide) (by decide) applied

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.ConstantQuerySource
