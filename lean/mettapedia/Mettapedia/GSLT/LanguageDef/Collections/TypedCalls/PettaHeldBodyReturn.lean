import Mettapedia.Languages.MeTTa.PeTTa.OutputPlanProgramFormation
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaSurfaceReturn
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaBodyEntryPolicy

/-!
# Held compiler bodies execute through the existing source return boundary

The compiler's independent equation-body formation determines its value plan.
Executing that plan quotes the actual authored body. The existing scoped
machine then performs its actual return equation and reaches the same typed
result guard, without executing a call written inside that body.

This connects a formed held body plan to source execution. Selecting it in
the complete mixed-host driver and the native explicit-function escape are
separate obligations; no second evaluator or source body-result service is
introduced here.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaHeldBodyReturn

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared (Allocator)
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open EagerDFS (World)
open EagerDFS.Destination
open PettaOccurrenceOverlay
open Bridges.ClosedOnceQueryFrame (placed)

theorem held_formation_result {context : OutputPlan.Context} {equation : SpaceSemantics.Equation}
    {result : OutputPlan.Result} (formed : OutputPlan.EquationBodyRel context equation result)
    (raw : OutputPlan.rawOutput context.source equation.head equation.arguments.length = true) :
    result = ⟨OutputPlan.Supply.start (equation.body :: equation.arguments), OutputPlan.Plan.value equation.body⟩ := by
  cases formed with
  | held => rfl
  | evaluated result notRaw body => rw [raw] at notRaw; cases notRaw

theorem held_formation_executes_quote {context : OutputPlan.Context} {equation : SpaceSemantics.Equation}
    {result : OutputPlan.Result} (formed : OutputPlan.EquationBodyRel context equation result)
    (raw : OutputPlan.rawOutput context.source equation.head equation.arguments.length = true) :
    (OutputPlan.normalized result).execute = OutputPlan.hold equation.body := by
  rw [held_formation_result formed raw]
  have normal : (OutputPlan.Supply.start (equation.body :: equation.arguments)).normalize = id := by
    funext term
    exact Unifying.resolve_of_unbound term (by intro name present; rfl)
  simp only [OutputPlan.normalized, OutputPlan.Supply.plan, OutputPlan.Plan.value, normal, id_eq,
    OutputPlan.Plan.execute, OutputPlan.sequence, beq_self_eq_true, if_true]

/-- The common clause renamer acts on the actual held body, including every
open field. It does not freshen the formal independently of that body. -/
theorem fresh_held_plan {context : OutputPlan.Context} {equation : SpaceSemantics.Equation}
    {result : OutputPlan.Result} (formed : OutputPlan.EquationBodyRel context equation result)
    (raw : OutputPlan.rawOutput context.source equation.head equation.arguments.length = true)
    (control : Control) (occurrence : Nat) :
    Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement.renameTypeVars
      (ClauseChoice.rename control occurrence (ClauseChoice.clauseAtoms equation))
      (OutputPlan.normalized result).execute = OutputPlan.hold (ClauseChoice.freshBody control occurrence equation) := by
  rw [held_formation_executes_quote formed raw]
  simp only [OutputPlan.hold, OutputPlan.call, Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement.renameTypeVars,
    List.map_cons, List.map_nil, ClauseChoice.freshBody]

theorem typed_held_body_two_steps {User : Type} (services : Services User)
    (policy : Policy) (program : SpaceSemantics.Program) (allocator : Allocator) (world : World)
    (scope : Scope User) (parents : List (Scope User)) (caller : DControl)
    (context : Context User) (origins : List Nat) (pending : List (Work User))
    (frame : CallFrame) (outside : List CallFrame) (body : Atom) (bindings : Equations)
    (calls : context.calls = frame :: outside) (phase : frame.phase = .body)
    (depth : frame.scopeDepth = (scope :: parents).length)
    (accepted : refine caller.bindings body frame.callDestination = some bindings) :
    (PettaOccurrenceOverlay.machine services policy program).run 2
      (placed allocator world scope parents
        {caller with goals := [.evaluate (OutputPlan.hold body) frame.callDestination], destination := frame.callDestination}
        context origins pending) =
      ([], .exhausted (placed allocator world scope parents
        {caller with bindings, goals := [], destination := frame.callDestination} context origins pending)) := by
  simp [Machine.run, PettaOccurrenceOverlay.machine, PettaOccurrenceOverlay.step,
    delegate, sourceOwned, EagerDFS.eagerControlForm, calls, phase, depth, liftSource,
    Bridges.ScopedQuerySource.ownedStep, Bridges.ScopedQuerySource.ownershipStep,
    Bridges.ScopedCaseSource.entryStep, Bridges.ScopedCaseSource.readyStep,
    Bridges.ScopedQuerySource.step, Bridges.ScopedQuerySource.syntaxStep,
    Bridges.ScopedQuerySource.constrainedCall, Bridges.ScopedQuerySource.mutationCall,
    Bridges.ScopedQuerySource.queryStep, placed, scopeStep, enterCollapse?, enterSuperpose?,
    EagerDFS.Destination.machine, prepare, replace, installChild, retainChild, accepted,
    OutputPlan.hold, OutputPlan.call]

theorem typed_held_body_refuses_only_current {User : Type} (services : Services User)
    (policy : Policy) (program : SpaceSemantics.Program) (allocator : Allocator) (world : World)
    (scope : Scope User) (parents : List (Scope User)) (caller : DControl)
    (context : Context User) (origins : List Nat) (pending : List (Work User))
    (frame : CallFrame) (outside : List CallFrame) (body : Atom)
    (calls : context.calls = frame :: outside) (phase : frame.phase = .body)
    (depth : frame.scopeDepth = (scope :: parents).length)
    (refused : refine caller.bindings body frame.callDestination = none) :
    (PettaOccurrenceOverlay.machine services policy program).run 2
      (placed allocator world scope parents
        {caller with goals := [.evaluate (OutputPlan.hold body) frame.callDestination], destination := frame.callDestination}
        context origins pending) =
      ([], .exhausted (allocator, ⟨world, {scope with frontier := pending} :: parents⟩)) := by
  simp [Machine.run, PettaOccurrenceOverlay.machine, PettaOccurrenceOverlay.step,
    delegate, sourceOwned, EagerDFS.eagerControlForm, calls, phase, depth, liftSource,
    Bridges.ScopedQuerySource.ownedStep, Bridges.ScopedQuerySource.ownershipStep,
    Bridges.ScopedCaseSource.entryStep, Bridges.ScopedCaseSource.readyStep,
    Bridges.ScopedQuerySource.step, Bridges.ScopedQuerySource.syntaxStep,
    Bridges.ScopedQuerySource.constrainedCall, Bridges.ScopedQuerySource.mutationCall,
    Bridges.ScopedQuerySource.queryStep, placed, scopeStep, enterCollapse?, enterSuperpose?,
    EagerDFS.Destination.machine, prepare, replace, installChild, retainChild, refused,
    OutputPlan.hold, OutputPlan.call]

/-- The read is earned by the actual return unifier. It is an open reached
read, not an assumed frozen or ground body value. -/
theorem held_body_then_guard {User : Type} (services : Services User)
    (policy : Policy) (program : SpaceSemantics.Program) (allocator : Allocator) (world : World)
    (scope : Scope User) (parents : List (Scope User)) (caller : DControl)
    (context : Context User) (origins : List Nat) (pending : List (Work User))
    (frame : CallFrame) (outside : List CallFrame) (body : Atom) (bindings : Equations) (environment : Environment)
    (calls : context.calls = frame :: outside) (phase : frame.phase = .body)
    (depth : frame.scopeDepth = (scope :: parents).length)
    (accepted : refine caller.bindings body frame.callDestination = some bindings)
    (resolved : resolve bindings = some environment) :
    let reachedControl := {caller with bindings, goals := [], destination := frame.callDestination}
    let reached := placed allocator world scope parents reachedControl context origins pending
    (PettaOccurrenceOverlay.machine services policy program).run 2
      (placed allocator world scope parents
        {caller with goals := [.evaluate (OutputPlan.hold body) frame.callDestination], destination := frame.callDestination}
        context origins pending) = ([], .exhausted reached) ∧
    PettaOccurrenceOverlay.step services policy program reached =
      consumeBody services reached {scope with frontier := (reachedControl, context, origins) :: pending}
        parents reachedControl context origins pending frame outside (read environment body) := by
  dsimp only
  refine ⟨typed_held_body_two_steps services policy program allocator world scope parents caller context origins pending
    frame outside body bindings calls phase depth accepted, ?_⟩
  have related : read environment frame.callDestination = read environment body := by
    have sourceReturn := (refinement_iff _ _ _ _).mpr accepted
    cases sourceReturn with
    | accepted witness old same =>
        exact ((solves_append_equation _ _ _ _).mp (resolve_sound resolved)).2.symm
  have actual := terminal_body_step services policy program
    (placed allocator world scope parents
      {caller with bindings, goals := [], destination := frame.callDestination} context origins pending)
    {scope with frontier :=
      ({caller with bindings, goals := [], destination := frame.callDestination}, context, origins) :: pending}
    parents {caller with bindings, goals := [], destination := frame.callDestination}
    context origins pending frame outside environment rfl rfl calls (by simpa [placed] using depth) phase rfl resolved
  simpa only [related] using actual

theorem formed_held_body_then_guard {User : Type} (services : Services User)
    (policy : Policy) (program : SpaceSemantics.Program) (allocator : Allocator) (world : World)
    (scope : Scope User) (parents : List (Scope User)) (caller : DControl)
    (context : Context User) (origins : List Nat) (pending : List (Work User))
    (frame : CallFrame) (outside : List CallFrame) (bindings : Equations) (environment : Environment)
    (compiler : OutputPlan.Context) (equation : SpaceSemantics.Equation) (result : OutputPlan.Result)
    (formed : OutputPlan.EquationBodyRel compiler equation result)
    (raw : OutputPlan.rawOutput compiler.source equation.head equation.arguments.length = true)
    (calls : context.calls = frame :: outside) (phase : frame.phase = .body)
    (depth : frame.scopeDepth = (scope :: parents).length)
    (accepted : refine caller.bindings equation.body frame.callDestination = some bindings)
    (resolved : resolve bindings = some environment) :
    let reachedControl := {caller with bindings, goals := [], destination := frame.callDestination}
    let reached := placed allocator world scope parents reachedControl context origins pending
    (PettaOccurrenceOverlay.machine services policy program).run 2
      (placed allocator world scope parents
        {caller with goals := [.evaluate (OutputPlan.normalized result).execute frame.callDestination], destination := frame.callDestination}
        context origins pending) = ([], .exhausted reached) ∧
    PettaOccurrenceOverlay.step services policy program reached =
      consumeBody services reached {scope with frontier := (reachedControl, context, origins) :: pending}
        parents reachedControl context origins pending frame outside (read environment equation.body) := by
  rw [held_formation_executes_quote formed raw]
  exact held_body_then_guard services policy program allocator world scope parents caller context origins pending
    frame outside equation.body bindings environment calls phase depth accepted resolved

/-- Exhaust both outcomes of the actual return unifier. In the accepted
case, its consistency earns a resolver result rather than requiring one as
an input premise. Refusal retains the older frontier and the reached world. -/
theorem held_body_outcome {User : Type} (services : Services User)
    (policy : Policy) (program : SpaceSemantics.Program) (allocator : Allocator) (world : World)
    (scope : Scope User) (parents : List (Scope User)) (caller : DControl)
    (context : Context User) (origins : List Nat) (pending : List (Work User))
    (frame : CallFrame) (outside : List CallFrame) (body : Atom)
    (calls : context.calls = frame :: outside) (phase : frame.phase = .body)
    (depth : frame.scopeDepth = (scope :: parents).length) :
    let initial := placed allocator world scope parents
      {caller with goals := [.evaluate (OutputPlan.hold body) frame.callDestination], destination := frame.callDestination}
      context origins pending
    match refine caller.bindings body frame.callDestination with
    | none => (PettaOccurrenceOverlay.machine services policy program).run 2 initial =
        ([], .exhausted (allocator, ⟨world, {scope with frontier := pending} :: parents⟩))
    | some bindings => ∃ environment, resolve bindings = some environment ∧
        let reachedControl := {caller with bindings, goals := [], destination := frame.callDestination}
        let reached := placed allocator world scope parents reachedControl context origins pending
        (PettaOccurrenceOverlay.machine services policy program).run 2 initial = ([], .exhausted reached) ∧
          PettaOccurrenceOverlay.step services policy program reached =
            consumeBody services reached {scope with frontier := (reachedControl, context, origins) :: pending}
              parents reachedControl context origins pending frame outside (read environment body) := by
  dsimp only
  cases refined : refine caller.bindings body frame.callDestination with
  | none =>
      exact typed_held_body_refuses_only_current services policy program allocator world scope parents caller
        context origins pending frame outside body calls phase depth refined
  | some bindings =>
      have consistent : ∃ environment, EagerDFS.Destination.Solves environment bindings := by
        obtain ⟨rfl, environment, old, related⟩ := (refine_iff _ _ _ _).mp refined
        exact ⟨environment, (solves_append_equation _ _ _ _).mpr ⟨old, related⟩⟩
      obtain ⟨environment, resolved⟩ := resolve_complete consistent
      exact ⟨environment, resolved, held_body_then_guard services policy program allocator world scope parents caller
        context origins pending frame outside body bindings environment calls phase depth refined resolved⟩

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaHeldBodyReturn
