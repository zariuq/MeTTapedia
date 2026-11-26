import Mettapedia.Languages.MeTTa.MeTTaAuthoredProgramExecution

/-!
# A provided module executes in the reached PeTTa world

Interpret the existing finite provided-module source judgment. Entering
a module only changes the current target, pending commands, and caller
continuation. Finishing restores the caller's context but retains the
effects already executed.

The source judgment is not idempotent at repeated import. A separate
boundary law below describes a once-only *completed acquisition*, for
a fixed provider catalog and destination. It does not change the source
judgment inside an initializer or impose a cycle policy.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.SpaceTheory.EffectfulModules

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.OSLF.MeTTaIL.MeTTaSyntaxQuotation (Program)
open Mettapedia.Languages.MeTTa.MeTTaAuthoredProgramExecution.ProgramExecution
open Mettapedia.Languages.MeTTa.MeTTaRevisionedQueryBindEval.AuthoredActivation.AtomCommands (Command ModuleAt)
open Mettapedia.Languages.MeTTa.MeTTaFiniteRevisionedKernel.AuthoredActivation.AtomCommands (StateCode ActionCode)
open Mettapedia.Languages.MeTTa.PeTTa

/-- Acquisition does not install a syntactic union before running the
module. It prepares its source commands in the selected destination. -/
theorem entering_changes_no_store {settings : Settings} {before after : Session}
    {line : Nat} {origin : List Nat} {command : Command} {destination : NamedSpaces.Handle} {label : Atom}
    (source : Source.Handle settings before line origin command (.importModule destination label) after) :
    after.world.packet = before.world.packet ∧ after.world.bindings = before.world.bindings := by
  cases source <;> exact ⟨rfl, rfl⟩

/-- This is the original return step. The reached store, I/O and bindings
do not come from the caller saved at entry. -/
theorem return_restores_only_caller {settings : Settings} {before : Session} {frame : ImportFrame}
    {rest : List ImportFrame} (commands : before.phase = .commands)
    (exhausted : before.pending = []) (stack : before.frames = frame :: rest) :
    ∃ after, Source.Transition settings before after ∧
      after.world.current = frame.current ∧ after.pending = frame.pending ∧
      after.world.packet = before.world.packet ∧ after.world.bindings = before.world.bindings := by
  exact ⟨_, .returnedImport commands exhausted stack, rfl, rfl, rfl, rfl⟩

def Settled (body : Session) : Prop :=
  body.phase = .commands ∧ body.pending = [] ∧ body.frames = []

def withOuterFrames (session : Session) (outer : List ImportFrame) : Session :=
  {session with frames := session.frames ++ outer}

private theorem inspect_with_outer {before after : Session} {active : Evaluation}
    (read : Source.Inspect before active after) (outer : List ImportFrame) :
    Source.Inspect (withOuterFrames before outer) active (withOuterFrames after outer) := by
  cases read with
  | complete read => exact .complete read
  | fault read => exact .fault read
  | unknown read => exact .unknown read
  | stale read => exact .stale read
  | exhausted read fuel => exact .exhausted read fuel
  | evaluating read fuel => exact .evaluating read fuel

private theorem handle_with_outer {settings : Settings} {before after : Session}
    {line : Nat} {origin : List Nat} {command : Command} {action : ActionCode}
    (step : Source.Handle settings before line origin command action after) (outer : List ImportFrame) :
    Source.Handle settings (withOuterFrames before outer) line origin command action (withOuterFrames after outer) := by
  cases step with
  | done answers => exact .done answers
  | retained literal => exact .retained literal
  | fault why => exact .fault why
  | evaluate reading => exact .evaluate (inspect_with_outer reading outer)
  | imported evidence => exact .imported evidence
  | unprovided absent => exact .unprovided absent

/-- Every actual transition of the included body can run under a saved
caller. This also covers its own nested provided includes. Only the
later return to the saved caller consults the appended outer frames. -/
theorem transition_with_outer {settings : Settings} {before after : Session}
    (step : Source.Transition settings before after) (outer : List ImportFrame) :
    Source.Transition settings (withOuterFrames before outer) (withOuterFrames after outer) := by
  cases step with
  | returnedImport commands empty pending =>
    exact .returnedImport commands empty (congrArg (· ++ outer) pending)
  | dispatched commands pending dispatch handle =>
    exact .dispatched commands pending dispatch (handle_with_outer handle outer)
  | observed evaluating settled reading =>
    exact .observed evaluating settled (inspect_with_outer reading outer)
  | exhausted evaluating unfinished empty => exact .exhausted evaluating unfinished empty
  | unavailable evaluating unfinished budget stopped => exact .unavailable evaluating unfinished budget stopped
  | evaluated evaluating unfinished budget one reading =>
    exact .evaluated evaluating unfinished budget one (inspect_with_outer reading outer)

theorem trace_with_outer {settings : Settings} {before after : Session}
    (trace : Source.Trace settings before after) (outer : List ImportFrame) :
    Source.Trace settings (withOuterFrames before outer) (withOuterFrames after outer) := by
  induction trace with
  | refl => exact .refl
  | tail _ step ih => exact .tail ih (transition_with_outer step outer)

def returnTo (body : Session) (caller : ImportFrame) (outer : List ImportFrame) : Session :=
  {body with
    world := {body.world with current := caller.current}
    pending := caller.pending
    offset := caller.offset
    origin := caller.origin
    frames := outer}

theorem complete_body_returns {settings : Settings} {before reached : Session}
    (trace : Source.Trace settings before reached) (finished : Settled reached)
    (caller : ImportFrame) (outer : List ImportFrame) :
    Source.Trace settings (withOuterFrames before (caller :: outer)) (returnTo reached caller outer) := by
  obtain ⟨commands, empty, noFrames⟩ := finished
  have stack : (withOuterFrames reached (caller :: outer)).frames = caller :: outer := by
    simp only [withOuterFrames, noFrames, List.nil_append]
  exact (trace_with_outer trace _).tail (.returnedImport (before := withOuterFrames reached (caller :: outer))
    commands empty stack)

/-- The actual provided command is an include: its body runs in the
selected destination, under the importer's continuation. On return only
the caller's control is restored, not its earlier store or history. -/
theorem provided_include_returns {settings : Settings} {before launched reached : Session}
    {line : Nat} {origin : List Nat} {command : Command} {destination : NamedSpaces.Handle}
    {label : Atom} {index : Nat} {commands : Program Atom}
    (provided : ModuleAt settings.modules label index commands)
    (launches : Source.Handle settings before line origin command (.importModule destination label) launched)
    (body : Source.Trace settings {launched with frames := []} reached)
    (finished : Settled reached) :
    let saved : ImportFrame := ⟨before.pending, before.offset, before.origin, before.world.current⟩
    launched.world.current = destination ∧
      Source.Trace settings launched (returnTo reached saved before.frames) := by
  cases launches with
  | unprovided absent => exact (absent _ _ provided).elim
  | imported available =>
    exact ⟨rfl, complete_body_returns body finished _ _⟩

def Completion (settings : Settings) (destination : NamedSpaces.Handle) (commands : Program Atom)
    (before reached : StateCode) : Prop :=
  ∃ body, Source.Trace settings (initial { before with current := destination } commands) body ∧
    Settled body ∧ reached = { body.world with current := before.current }

structure Instance where
  destination : NamedSpaces.Handle
  module : Atom
  deriving DecidableEq

structure Acquisitions where
  world : StateCode
  initialized : List Instance

/-- A completed import can be shared in the same destination. Choosing
once-only acquisition expresses an explicit effect policy, rather than
an equality of the original re-executing source commands. -/
inductive Once (settings : Settings) (request : Instance) : Acquisitions → Acquisitions → Prop where
  | reuse {before} : request ∈ before.initialized → Once settings request before before
  | acquire {before : Acquisitions} {index commands reached} :
      request ∉ before.initialized →
      ModuleAt settings.modules request.module index commands →
      Completion settings request.destination commands before.world reached →
      Once settings request before ⟨reached, request :: before.initialized⟩

theorem initialized_after {settings : Settings} {request : Instance} {before after : Acquisitions}
    (result : Once settings request before after) : request ∈ after.initialized := by
  cases result with
  | reuse known => exact known
  | acquire _ _ _ => exact List.mem_cons_self

theorem repeat_after_success {settings : Settings} {request : Instance} {before after : Acquisitions}
    (finished : Once settings request before after) (later : Acquisitions) :
    Once settings request after later ↔ later = after := by
  have known := initialized_after finished
  constructor
  · intro again
    cases again with
    | reuse _ => rfl
    | acquire absent _ _ => exact (absent known).elim
  · rintro rfl
    exact .reuse known

theorem once_keys {settings : Settings} {request key : Instance} {before after : Acquisitions}
    (finished : Once settings request before after) :
    key ∈ after.initialized ↔ key ∈ before.initialized ∨ key = request := by
  cases finished with
  | reuse present =>
    exact ⟨Or.inl, fun h => h.elim id (fun same => same ▸ present)⟩
  | acquire _ _ _ => rw [List.mem_cons, or_comm]

/-- External acquisition order is explicit. This does not flatten or
reschedule commands inside any initializer. -/
inductive InOrder (settings : Settings) : List Instance → Acquisitions → Acquisitions → Prop where
  | nil (state : Acquisitions) : InOrder settings [] state state
  | cons {first remaining before middle after} : Once settings first before middle →
      InOrder settings remaining middle after → InOrder settings (first :: remaining) before after

theorem initialized_in_order {settings : Settings} {order : List Instance} {before after : Acquisitions}
    (run : InOrder settings order before after) (key : Instance) :
    key ∈ after.initialized ↔ key ∈ before.initialized ∨ key ∈ order := by
  induction run with
  | nil => simp
  | cons first _ ih => rw [ih, once_keys first, List.mem_cons, or_assoc]

theorem already_initialized_order {settings : Settings} (order : List Instance) (before after : Acquisitions)
    (known : ∀ key ∈ order, key ∈ before.initialized) :
    InOrder settings order before after ↔ after = before := by
  induction order generalizing after with
  | nil =>
    constructor
    · intro done; cases done; rfl
    · rintro rfl; exact .nil _
  | cons first remaining ih =>
    have seen := known first List.mem_cons_self
    have later : ∀ key ∈ remaining, key ∈ before.initialized :=
      fun key member => known key (List.mem_cons_of_mem _ member)
    constructor
    · intro run
      cases run with
      | cons acquired rest =>
        cases acquired with
        | reuse _ => exact (ih _ later).mp rest
        | acquire outside _ _ => exact (outside seen).elim
    · rintro rfl
      exact .cons (.reuse seen) ((ih _ later).mpr rfl)

theorem repeat_acquisition_order {settings : Settings} {order : List Instance} {before after : Acquisitions}
    (run : InOrder settings order before after) (again : Acquisitions) :
    InOrder settings order after again ↔ again = after :=
  already_initialized_order order after again
    (fun key member => (initialized_in_order run key).mpr (Or.inr member))

section Controls

private def label : Atom := .symbol "provided"
private def old : Atom := .expression [.symbol "=", .expression [.symbol "old", .var "x"], .var "x"]
private def new : Atom := .expression [.symbol "=", .expression [.symbol "new", .var "x"], .var "x"]

private def emptyWorld : StateCode where
  packet := { core := [], spaces := [], cells := [], control := .returned [], frames := [], input := [], output := [] }
  fuel := 16

private def importer : Program Atom :=
  [(1, .import (.symbol "&self") label), (2, .import (.symbol "&self") label)]

private def offered : Settings := { modules := [(label, [(1, .fact new)])] }

private def repeated : Session := advance offered 16 (initial emptyWorld importer)

/-- In the actual finite provided-module source, repeated imports
reexecute, distinguishably from the once-only completed acquisition. -/
theorem source_reexecutes_the_module :
    ∃ reached, Source.Trace offered (initial emptyWorld importer) reached ∧
      reached.world.packet.core = [new, new] ∧ reached.imports.length = 2 ∧ status reached = .complete := by
  exact ⟨repeated, Source.advance_trace _ _ _, by decide +kernel⟩

private def effectful : Program Atom :=
  [(1, .removeAtom (.symbol "&self") old), (2, .fact new),
    (3, .eval (.expression [.symbol "println!", .symbol "initialized"]))]

private def effectfulModules : Settings := { modules := [(label, effectful)] }
private def loaded : StateCode := { emptyWorld with packet := {emptyWorld.packet with core := [old]} }
private def loading : Session := initial loaded [(1, .import (.symbol "&self") label)]
private def reached : Session := advance effectfulModules 32 loading

/-- Even a successful module import need not include the old theory.
This source run really removes a function and executes the print before
return to the importing context. -/
theorem initializer_can_retract_and_publish :
    ∃ final, Source.Trace effectfulModules loading final ∧ status final = .complete ∧
      final.world.packet.core = [new] ∧ old ∉ final.world.packet.core ∧
      final.world.packet.output = [.symbol "initialized"] ∧ final.world.current = loaded.current := by
  exact ⟨reached, Source.advance_trace _ _ _, by decide +kernel⟩

private def request : Instance := ⟨.self, label⟩
private def beforeImport : Acquisitions := ⟨loaded, []⟩
private def completedBody : Session := advance effectfulModules 32 (initial loaded effectful)
private def acquired : Acquisitions := ⟨{completedBody.world with current := loaded.current}, [request]⟩

theorem chosen_once_policy_preserves_first_effects :
    Once effectfulModules request beforeImport acquired ∧
      Once effectfulModules request acquired acquired ∧
      acquired.world.packet.core = [new] ∧ acquired.world.packet.output = [.symbol "initialized"] := by
  refine ⟨.acquire (by simp [beforeImport]) (.here [] _ _)
    ⟨completedBody, Source.advance_trace _ _ _, ?_, rfl⟩,
    .reuse (by simp [acquired]), by decide +kernel⟩
  exact ⟨rfl, rfl, rfl⟩

end Controls

end Mettapedia.Languages.MeTTa.SpaceTheory.EffectfulModules
