import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaHeldBodyReturn
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedReturnEntry
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.FormedBodyReturnAdmission

/-!
# Actual clause matching earns a held-body input return

In a held body, returning an argument requires the authored RHS itself to
be that formal recipe. An eager return position under let or failure is not
such a certificate. Actual fresh matching and the actual return equation
earn the relation between the reached input and output, even for open input.

The execution below consumes the existing compiler's formed body plan. It
does not assert that the complete native driver selected that body mode.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaHeldBodyEntry

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared (Allocator)
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open EagerDFS (World)
open EagerDFS.Destination
open PettaOccurrenceOverlay
open Bridges.ClosedOnceQueryFrame (placed)

theorem returned_input_read (control next : Control) (head : String) (arguments : List Atom)
    (destination : Atom) (older : List EagerDFS.Destination.Goal) (occurrence : Nat)
    (equation : SpaceSemantics.Equation) (index : Nat) (argument recipe : Atom)
    (selected : ClauseChoice.attempt control head arguments destination older occurrence equation = some next)
    (actual : arguments[index]? = some argument) (formal : equation.arguments[index]? = some recipe)
    (body : equation.body = recipe) (bindings : Equations) (environment : Environment)
    (accepted : refine next.bindings (ClauseChoice.freshBody control occurrence equation) destination = some bindings)
    (resolved : resolve bindings = some environment) :
    read environment destination = read environment argument := by
  have refined := (refinement_iff _ _ _ _).mpr accepted
  have extended := RefinementTransport.accepted_extends refined
  have linked : read environment (ClauseChoice.freshBody control occurrence equation) = read environment argument := by
    dsimp only [ClauseChoice.freshBody]
    rw [body]
    exact Bridges.ScopedReturnEntry.fresh_recipe_read control head arguments destination older occurrence equation next
      index argument recipe selected actual formal environment (extended environment (resolve_sound resolved))
  have delivered : read environment destination =
      read environment (ClauseChoice.freshBody control occurrence equation) := by
    cases refined with
    | accepted witness old same =>
        exact ((solves_append_equation _ _ _ _).mp (resolve_sound resolved)).2.symm
  exact delivered.trans linked

/-- Source matching, held formation and the actual output unifier compose
before the existing result guard. No body-result equality is supplied. -/
theorem selected_held_body_then_guard {User : Type} (services : Services User)
    (policy : Policy) (program : SpaceSemantics.Program) (allocator : Allocator) (world : World)
    (scope : Scope User) (parents : List (Scope User)) (control next : DControl)
    (context : Context User) (origins : List Nat) (pending : List (Work User))
    (frame : CallFrame) (outside : List CallFrame) (head : String) (arguments : List Atom)
    (occurrence : Nat) (equation : SpaceSemantics.Equation) (index : Nat) (argument recipe : Atom)
    (compiler : OutputPlan.Context) (result : OutputPlan.Result)
    (formed : OutputPlan.EquationBodyRel compiler equation result)
    (raw : OutputPlan.rawOutput compiler.source equation.head equation.arguments.length = true)
    (selected : ClauseChoice.attempt control head arguments frame.callDestination [] occurrence equation = some next)
    (actual : arguments[index]? = some argument) (formal : equation.arguments[index]? = some recipe)
    (body : equation.body = recipe) (bindings : Equations) (environment : Environment)
    (calls : context.calls = frame :: outside) (phase : frame.phase = .body)
    (depth : frame.scopeDepth = (scope :: parents).length)
    (accepted : refine next.bindings (ClauseChoice.freshBody control occurrence equation) frame.callDestination = some bindings)
    (resolved : resolve bindings = some environment) :
    let heldPlan := Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement.renameTypeVars
      (ClauseChoice.rename control occurrence (ClauseChoice.clauseAtoms equation)) (OutputPlan.normalized result).execute
    let reachedControl := {next with bindings, goals := [], destination := frame.callDestination}
    let reached := placed allocator world scope parents reachedControl context origins pending
    (PettaOccurrenceOverlay.machine services policy program).run 2
      (placed allocator world scope parents
        {next with goals := [.evaluate heldPlan frame.callDestination], destination := frame.callDestination}
        context origins pending) = ([], .exhausted reached) ∧
    PettaOccurrenceOverlay.step services policy program reached =
      consumeBody services reached {scope with frontier := (reachedControl, context, origins) :: pending}
        parents reachedControl context origins pending frame outside (read environment argument) := by
  dsimp only
  rw [PettaHeldBodyReturn.fresh_held_plan formed raw control occurrence]
  have delivered := PettaHeldBodyReturn.held_body_then_guard services policy program allocator world scope parents next
    context origins pending frame outside (ClauseChoice.freshBody control occurrence equation) bindings environment
    calls phase depth accepted resolved
  have linked : read environment (ClauseChoice.freshBody control occurrence equation) = read environment argument := by
    have refined := (refinement_iff _ _ _ _).mpr accepted
    have extended := RefinementTransport.accepted_extends refined
    dsimp only [ClauseChoice.freshBody]
    rw [body]
    exact Bridges.ScopedReturnEntry.fresh_recipe_read control head arguments frame.callDestination [] occurrence equation
      next index argument recipe selected actual formal environment (extended environment (resolve_sound resolved))
  simpa only [linked] using delivered

/-- The executable whole-head check, actual table membership and actual
fresh clause matching earn the held-body input return. In particular, an
eager return-position certificate cannot be supplied for a held prefix. -/
theorem checked_selected_held_body_then_guard {User : Type} (services : Services User)
    (policy : Policy) (program : SpaceSemantics.Program) (allocator : Allocator) (world : World)
    (scope : Scope User) (parents : List (Scope User)) (control next : DControl)
    (context : Context User) (origins : List Nat) (pending : List (Work User))
    (frame : CallFrame) (outside : List CallFrame) (head : String) (arguments : List Atom)
    (occurrence : Nat) (equation : SpaceSemantics.Equation) (index fuel : Nat) (argument : Atom)
    (compiler : OutputPlan.Context) (result : OutputPlan.Result)
    (formed : OutputPlan.EquationBodyRel compiler equation result)
    (checked : Bridges.FormedBodyReturnAdmission.checksHead compiler.source head index fuel = true)
    (present : equation ∈ compiler.source.equations) (named : equation.head = head)
    (raw : OutputPlan.rawOutput compiler.source equation.head equation.arguments.length = true)
    (selected : ClauseChoice.attempt control head arguments frame.callDestination [] occurrence equation = some next)
    (actual : arguments[index]? = some argument) (bindings : Equations) (environment : Environment)
    (calls : context.calls = frame :: outside) (phase : frame.phase = .body)
    (depth : frame.scopeDepth = (scope :: parents).length)
    (accepted : refine next.bindings (ClauseChoice.freshBody control occurrence equation) frame.callDestination = some bindings)
    (resolved : resolve bindings = some environment) :
    let heldPlan := Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement.renameTypeVars
      (ClauseChoice.rename control occurrence (ClauseChoice.clauseAtoms equation)) (OutputPlan.normalized result).execute
    let reachedControl := {next with bindings, goals := [], destination := frame.callDestination}
    let reached := placed allocator world scope parents reachedControl context origins pending
    (PettaOccurrenceOverlay.machine services policy program).run 2
      (placed allocator world scope parents
        {next with goals := [.evaluate heldPlan frame.callDestination], destination := frame.callDestination}
        context origins pending) = ([], .exhausted reached) ∧
    PettaOccurrenceOverlay.step services policy program reached =
      consumeBody services reached {scope with frontier := (reachedControl, context, origins) :: pending}
        parents reachedControl context origins pending frame outside (read environment argument) := by
  obtain ⟨recipe, formal, body⟩ := Bridges.FormedBodyReturnAdmission.checked_held_row compiler.source head index fuel
    checked equation present named raw
  exact selected_held_body_then_guard services policy program allocator world scope parents control next context origins
    pending frame outside head arguments occurrence equation index argument recipe compiler result formed raw selected
    actual formal body bindings environment calls phase depth accepted resolved

/-- Checked held-body entry covers refusal as well as successful return.
Neither successful body execution nor a successful resolver is assumed. -/
theorem checked_selected_held_body_outcome {User : Type} (services : Services User)
    (policy : Policy) (program : SpaceSemantics.Program) (allocator : Allocator) (world : World)
    (scope : Scope User) (parents : List (Scope User)) (control next : DControl)
    (context : Context User) (origins : List Nat) (pending : List (Work User))
    (frame : CallFrame) (outside : List CallFrame) (head : String) (arguments : List Atom)
    (occurrence : Nat) (equation : SpaceSemantics.Equation) (index fuel : Nat) (argument : Atom)
    (compiler : OutputPlan.Context) (result : OutputPlan.Result)
    (formed : OutputPlan.EquationBodyRel compiler equation result)
    (checked : Bridges.FormedBodyReturnAdmission.checksHead compiler.source head index fuel = true)
    (present : equation ∈ compiler.source.equations) (named : equation.head = head)
    (raw : OutputPlan.rawOutput compiler.source equation.head equation.arguments.length = true)
    (selected : ClauseChoice.attempt control head arguments frame.callDestination [] occurrence equation = some next)
    (actual : arguments[index]? = some argument)
    (calls : context.calls = frame :: outside) (phase : frame.phase = .body)
    (depth : frame.scopeDepth = (scope :: parents).length) :
    let heldPlan := Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement.renameTypeVars
      (ClauseChoice.rename control occurrence (ClauseChoice.clauseAtoms equation)) (OutputPlan.normalized result).execute
    let initial := placed allocator world scope parents
      {next with goals := [.evaluate heldPlan frame.callDestination], destination := frame.callDestination}
      context origins pending
    match refine next.bindings (ClauseChoice.freshBody control occurrence equation) frame.callDestination with
    | none => (PettaOccurrenceOverlay.machine services policy program).run 2 initial =
        ([], .exhausted (allocator, ⟨world, {scope with frontier := pending} :: parents⟩))
    | some bindings => ∃ environment, resolve bindings = some environment ∧
        let reachedControl := {next with bindings, goals := [], destination := frame.callDestination}
        let reached := placed allocator world scope parents reachedControl context origins pending
        (PettaOccurrenceOverlay.machine services policy program).run 2 initial = ([], .exhausted reached) ∧
          PettaOccurrenceOverlay.step services policy program reached =
            consumeBody services reached {scope with frontier := (reachedControl, context, origins) :: pending}
              parents reachedControl context origins pending frame outside (read environment argument) := by
  dsimp only
  cases refined : refine next.bindings (ClauseChoice.freshBody control occurrence equation) frame.callDestination with
  | none =>
      rw [PettaHeldBodyReturn.fresh_held_plan formed raw control occurrence]
      exact PettaHeldBodyReturn.typed_held_body_refuses_only_current services policy program allocator world scope parents
        next context origins pending frame outside (ClauseChoice.freshBody control occurrence equation) calls phase depth refined
  | some bindings =>
      have consistent : ∃ environment, EagerDFS.Destination.Solves environment bindings := by
        obtain ⟨rfl, environment, old, related⟩ := (refine_iff _ _ _ _).mp refined
        exact ⟨environment, (solves_append_equation _ _ _ _).mpr ⟨old, related⟩⟩
      obtain ⟨environment, resolved⟩ := resolve_complete consistent
      exact ⟨environment, resolved, checked_selected_held_body_then_guard services policy program allocator world scope
        parents control next context origins pending frame outside head arguments occurrence equation index fuel argument
        compiler result formed checked present named raw selected actual bindings environment calls phase depth refined resolved⟩

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaHeldBodyEntry
