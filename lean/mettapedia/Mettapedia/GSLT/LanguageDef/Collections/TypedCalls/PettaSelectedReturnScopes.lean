import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaSelectedReturnSources
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaScopeMarks

/-!
# Explicit occurrence marks in actual frontier and collection scopes

A mark is absent for unrelated work and otherwise names the selected frame's
physical prefix length. Mark lists are aligned with actual frontier lists;
saved collection callers carry their own mark. These are proof annotations,
not another evaluator or new fields in source configurations.

Installing fresh marked bodies, moving an obligation into a collection caller
and restoring it afterwards preserve the existing host data. The complete
source/typed step coverage for evolving these annotations is a separate join.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaSelectedReturnScopes

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open EagerDFS.Destination
open PettaOccurrenceOverlay

def WorkMarked {User : Type} (saved : CallFrame) (argument : Atom) (mark : Option Nat) (item : Work User) : Prop :=
  PettaScopeMarks.WorkMarked (PettaSelectedReturnWork.Holds saved argument) mark item

def Frontier {User : Type} (saved : CallFrame) (argument : Atom) (marks : List (Option Nat))
    (items : List (Work User)) : Prop := PettaScopeMarks.Frontier (PettaSelectedReturnWork.Holds saved argument) marks items

def CallerMarked {User : Type} (saved : CallFrame) (argument : Atom) (mark : Option Nat)
    (caller : Option (CollectionCaller (Context User))) : Prop :=
  PettaScopeMarks.CallerMarked (PettaSelectedReturnWork.Holds saved argument) mark caller

def ScopeHolds {User : Type} (saved : CallFrame) (argument : Atom) (marks : Marks) (current : Scope User) : Prop :=
  PettaScopeMarks.ScopeHolds (PettaSelectedReturnWork.Holds saved argument) marks current

def Stack {User : Type} (saved : CallFrame) (argument : Atom) (marks : List Marks)
    (scopes : List (Scope User)) : Prop := PettaScopeMarks.Stack (PettaSelectedReturnWork.Holds saved argument) marks scopes

def untracked {User : Type} (current : Scope User) : Marks :=
  PettaScopeMarks.untracked current

theorem Frontier.length {User : Type} {saved : CallFrame} {argument : Atom} {marks : List (Option Nat)}
    {items : List (Work User)} (good : Frontier saved argument marks items) : marks.length = items.length :=
  PettaScopeMarks.Frontier.length good

theorem Frontier.append {User : Type} {saved : CallFrame} {argument : Atom}
    {firstMarks secondMarks : List (Option Nat)} {first second : List (Work User)}
    (one : Frontier saved argument firstMarks first) (two : Frontier saved argument secondMarks second) :
    Frontier saved argument (firstMarks ++ secondMarks) (first ++ second) := PettaScopeMarks.Frontier.append one two

theorem untracked_frontier {User : Type} (saved : CallFrame) (argument : Atom) (items : List (Work User)) :
    Frontier saved argument (List.replicate items.length none) items :=
  PettaScopeMarks.untracked_frontier (PettaSelectedReturnWork.Holds saved argument) items

theorem marked_frontier {User : Type} (saved : CallFrame) (argument : Atom) (index : Nat)
    (items : List (Work User)) (held : ∀ item ∈ items, PettaSelectedReturnWork.Holds saved argument index item) :
    Frontier saved argument (List.replicate items.length (some index)) items :=
  PettaScopeMarks.marked_frontier (PettaSelectedReturnWork.Holds saved argument) index items held

theorem untracked_scope {User : Type} (saved : CallFrame) (argument : Atom) (current : Scope User) :
    ScopeHolds saved argument (untracked current) current :=
  PettaScopeMarks.untracked_scope (PettaSelectedReturnWork.Holds saved argument) current

theorem untracked_stack {User : Type} (saved : CallFrame) (argument : Atom) (scopes : List (Scope User)) :
    Stack saved argument (scopes.map untracked) scopes :=
  PettaScopeMarks.untracked_stack (PettaSelectedReturnWork.Holds saved argument) scopes

theorem scope_install {User : Type} {saved : CallFrame} {argument : Atom}
    (current : Scope User) (control : DControl) (context : Context User) (origins : List Nat)
    (pending : List (Work User)) (mark : Option Nat) (pendingMarks : List (Option Nat)) (callerMark : Option Nat)
    (held : ScopeHolds saved argument ⟨mark :: pendingMarks, callerMark⟩ current)
    (frontier : current.frontier = (control, context, origins) :: pending)
    (generated : List (Work User)) (newMarks : List (Option Nat))
    (produced : WorkMarked saved argument mark (control, context, origins) →
      Frontier saved argument newMarks generated) :
    ScopeHolds saved argument ⟨newMarks ++ pendingMarks, callerMark⟩
      {current with frontier := generated ++ pending} :=
  PettaScopeMarks.scope_install current control context origins pending mark pendingMarks callerMark held frontier
    generated newMarks produced

/-- Only the actual freshly selected bodies are marked. Older host work and
parents remain present with no newly imposed return obligation. -/
theorem install_selected {User : Type} (saved : CallFrame) (argument : Atom)
    (current : Scope User) (parents : List (Scope User)) (pending generated : List (Work User))
    (earned : ∀ item ∈ generated, PettaSelectedReturnWork.Holds saved argument 0 item) :
    Stack saved argument
      (⟨List.replicate generated.length (some 0) ++ List.replicate pending.length none, none⟩ :: parents.map untracked)
      ({current with frontier := generated ++ pending} :: parents) :=
  PettaScopeMarks.install_selected (PettaSelectedReturnWork.Holds saved argument) current parents pending generated earned

/-- The actual source prefix installs the marked full-host state. Both the
ready recipe and every selected-body obligation are earned before the scope
annotations are assembled; unrelated host work is not an input contract. -/
theorem source_produced_entry {User : Type} (operations : Services User)
    (program : SpaceSemantics.Program) (fuel : Nat) (source final : State User)
    (good : PettaArgumentProgress.Safe source)
    (reached : PettaCallerReturnMachine.exitState
      ((PettaOccurrenceOverlay.machine operations .eagerValue program).run fuel source).2 = some final)
    (current : Scope User) (parents : List (Scope User)) (control : DControl)
    (context : Context User) (origins : List Nat) (pending : List (Work User))
    (saved : CallFrame) (outside : List CallFrame) (environment : Environment) (resultName : String)
    (scopes : final.2.scopes = current :: parents)
    (frontier : current.frontier = (control, context, origins) :: pending)
    (calls : context.calls = saved :: outside)
    (atCall : control.goals = [.invoke saved.head saved.ready saved.callDestination])
    (target : control.destination = saved.callDestination)
    (resolved : resolve control.bindings = some environment)
    (unbound : read environment saved.callDestination = .var resultName)
    (unknown : StdLib.known saved.head = false) (notIO : Eval.ioHead saved.head = false)
    (notCase : saved.head ≠ "case") (phase : saved.phase = .body)
    (parameterIndex inspectionFuel : Nat) (within : parameterIndex < saved.row.parameters.length)
    (checked : Bridges.ScopedReturnFunction.checksHead program saved.head parameterIndex inspectionFuel = true) :
    ∃ recipe, saved.ready[parameterIndex]? = some recipe ∧
      let generated := equationWork program control (collectionSupport final.2) context origins saved.head
        (saved.ready.map (read environment)) saved.callDestination [] pending.length
      let after : State User := (final.1, ⟨final.2.world, {current with frontier := generated ++ pending} :: parents⟩)
      PettaOccurrenceOverlay.step operations .eagerValue program final = .silent after ∧
        Stack saved recipe
          (⟨List.replicate generated.length (some 0) ++ List.replicate pending.length none, none⟩ :: parents.map untracked)
          after.2.scopes := by
  obtain ⟨recipe, present, entered, marked⟩ := PettaSelectedReturnWork.source_produced_mark operations program fuel
    source final good reached current parents control context origins pending saved outside environment resultName
    scopes frontier calls atCall target resolved unbound unknown notIO notCase phase parameterIndex inspectionFuel within checked
  exact ⟨recipe, present, entered, install_selected saved recipe current parents pending _ marked⟩

/-- A collection's arbitrary child values need no return-alias obligation.
The marked continuation moves to its actual saved caller instead. -/
theorem collection_push {User : Type} {saved : CallFrame} {argument : Atom}
    (current : Scope User) (parents : List (Scope User)) (parentMarks : List Marks)
    (control : DControl) (context : Context User) (origins : List Nat) (pending : List (Work User))
    (mark : Option Nat) (pendingMarks : List (Option Nat)) (callerMark : Option Nat)
    (held : Stack saved argument (⟨mark :: pendingMarks, callerMark⟩ :: parentMarks) (current :: parents))
    (frontier : current.frontier = (control, context, origins) :: pending)
    (expression destination : Atom) (older : List EagerDFS.Destination.Goal)
    (atGoal : control.goals = .evaluate (.expression [.symbol "collapse", expression]) destination :: older)
    (child : Scope User)
    (savedCaller : child.caller = some ({control with goals := older}, destination, context, origins)) :
    Stack saved argument
      (⟨List.replicate child.frontier.length none, mark⟩ :: ⟨pendingMarks, callerMark⟩ :: parentMarks)
      (child :: {current with frontier := pending} :: parents) :=
  PettaScopeMarks.collection_push current parents parentMarks control context origins pending mark pendingMarks callerMark
    held frontier older destination
    (fun _ returning => PettaSelectedReturnWork.collapse_caller control context origins returning expression destination older atGoal)
    child savedCaller

theorem collection_resume {User : Type} {saved : CallFrame} {argument : Atom}
    (child parent : Scope User) (parents : List (Scope User))
    (childMarks parentMarks : Marks) (outsideMarks : List Marks)
    (held : Stack saved argument (childMarks :: parentMarks :: outsideMarks) (child :: parent :: parents))
    (caller : CollectionCaller (Context User)) (actualCaller : child.caller = some caller)
    (copies : List (Atom × List Atom)) :
    Stack saved argument
      (⟨childMarks.caller :: parentMarks.frontier, parentMarks.caller⟩ :: outsideMarks)
      ({parent with frontier := Source.resumeCopies copies caller :: parent.frontier} :: parents) :=
  PettaScopeMarks.collection_resume child parent parents childMarks parentMarks outsideMarks held caller actualCaller copies
    (fun _ returning => PettaSelectedReturnWork.collection_copies copies caller returning)

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaSelectedReturnScopes
