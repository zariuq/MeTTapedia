import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCompoundSelectedWork
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaScopeMarks
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaMarkedTransitions

/-!
# Compound return obligations in the existing physical scope marks

Fresh source entry earns the initial marked frontier. A collection transfers
the selected obligation to its actual saved caller, leaving arbitrary child
work unmarked, and restores it through the actual copied-answer equation.
The mark data and structural scope lemmas are shared with variable returns.

These laws are for the maintained source/body profile. They do not supply
complete mixed-host dispatcher coverage or native body-mode correspondence.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCompoundReturnScopes

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open EagerDFS.Destination
open PettaOccurrenceOverlay
open PettaSelectedReturnScopes (Marks)

def WorkMarked {User : Type} (program : SpaceSemantics.Program) (saved : CallFrame) (argument : Atom)
    (mark : Option Nat) (item : Work User) : Prop :=
  PettaScopeMarks.WorkMarked (PettaCompoundSelectedWork.Holds program saved argument) mark item

def Frontier {User : Type} (program : SpaceSemantics.Program) (saved : CallFrame) (argument : Atom)
    (marks : List (Option Nat)) (items : List (Work User)) : Prop :=
  PettaScopeMarks.Frontier (PettaCompoundSelectedWork.Holds program saved argument) marks items

def ScopeHolds {User : Type} (program : SpaceSemantics.Program) (saved : CallFrame) (argument : Atom)
    (marks : Marks) (current : Scope User) : Prop :=
  PettaScopeMarks.ScopeHolds (PettaCompoundSelectedWork.Holds program saved argument) marks current

def Stack {User : Type} (program : SpaceSemantics.Program) (saved : CallFrame) (argument : Atom)
    (marks : List Marks) (scopes : List (Scope User)) : Prop :=
  PettaScopeMarks.Stack (PettaCompoundSelectedWork.Holds program saved argument) marks scopes

theorem install_selected {User : Type} (program : SpaceSemantics.Program) (saved : CallFrame) (argument : Atom)
    (current : Scope User) (parents : List (Scope User)) (pending generated : List (Work User))
    (earned : ∀ item ∈ generated, PettaCompoundSelectedWork.Holds program saved argument 0 item) :
    Stack program saved argument
      (⟨List.replicate generated.length (some 0) ++ List.replicate pending.length none, none⟩ :: parents.map PettaScopeMarks.untracked)
      ({current with frontier := generated ++ pending} :: parents) :=
  PettaScopeMarks.install_selected (PettaCompoundSelectedWork.Holds program saved argument) current parents pending generated earned

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
    (index inspectionFuel : Nat) (within : index < saved.row.parameters.length)
    (checked : Bridges.DestinationDataReturnFunction.checksHead program saved.head index inspectionFuel = true) :
    ∃ recipe, saved.ready[index]? = some recipe ∧
      let generated := equationWork program control (collectionSupport final.2) context origins saved.head
        (saved.ready.map (read environment)) saved.callDestination [] pending.length
      let after : State User := (final.1, ⟨final.2.world, {current with frontier := generated ++ pending} :: parents⟩)
      PettaOccurrenceOverlay.step operations .eagerValue program final = .silent after ∧
        Stack program saved recipe
          (⟨List.replicate generated.length (some 0) ++ List.replicate pending.length none, none⟩ ::
            parents.map PettaScopeMarks.untracked) after.2.scopes := by
  obtain ⟨recipe, present, entered, marked⟩ := PettaCompoundSelectedWork.source_produced_mark operations program fuel
    source final good reached current parents control context origins pending saved outside environment resultName
    scopes frontier calls atCall target resolved unbound unknown notIO notCase phase index inspectionFuel within checked
  exact ⟨recipe, present, entered, install_selected program saved recipe current parents pending _ marked⟩

theorem collection_push {User : Type} {program : SpaceSemantics.Program} {saved : CallFrame} {argument : Atom}
    (current : Scope User) (parents : List (Scope User)) (parentMarks : List Marks)
    (control : DControl) (context : Context User) (origins : List Nat) (pending : List (Work User))
    (mark : Option Nat) (pendingMarks : List (Option Nat)) (callerMark : Option Nat)
    (held : Stack program saved argument (⟨mark :: pendingMarks, callerMark⟩ :: parentMarks) (current :: parents))
    (frontier : current.frontier = (control, context, origins) :: pending)
    (expression destination : Atom) (older : List EagerDFS.Destination.Goal)
    (atGoal : control.goals = .evaluate (.expression [.symbol "collapse", expression]) destination :: older)
    (child : Scope User)
    (savedCaller : child.caller = some ({control with goals := older}, destination, context, origins)) :
    Stack program saved argument
      (⟨List.replicate child.frontier.length none, mark⟩ :: ⟨pendingMarks, callerMark⟩ :: parentMarks)
      (child :: {current with frontier := pending} :: parents) :=
  PettaScopeMarks.collection_push current parents parentMarks control context origins pending mark pendingMarks callerMark
    held frontier older destination
    (fun _ returning => PettaCompoundSelectedWork.collapse_caller control context origins returning expression destination older atGoal)
    child savedCaller

theorem collection_resume {User : Type} {program : SpaceSemantics.Program} {saved : CallFrame} {argument : Atom}
    (child parent : Scope User) (parents : List (Scope User)) (childMarks parentMarks : Marks) (outsideMarks : List Marks)
    (held : Stack program saved argument (childMarks :: parentMarks :: outsideMarks) (child :: parent :: parents))
    (caller : CollectionCaller (Context User)) (actualCaller : child.caller = some caller) (copies : List (Atom × List Atom)) :
    Stack program saved argument (⟨childMarks.caller :: parentMarks.frontier, parentMarks.caller⟩ :: outsideMarks)
      ({parent with frontier := Source.resumeCopies copies caller :: parent.frontier} :: parents) :=
  PettaScopeMarks.collection_resume child parent parents childMarks parentMarks outsideMarks held caller actualCaller copies
    (fun _ returning => PettaCompoundSelectedWork.collection_copies copies caller returning)

def Preserves {User : Type} (program : SpaceSemantics.Program) (saved : CallFrame) (argument : Atom)
    (marks : List Marks) (source : State User) (reply : Step User) : Prop :=
  PettaMarkedTransitions.Preserves (PettaCompoundSelectedWork.Holds program saved argument) marks source reply

theorem call_keeps {User : Type} {program : SpaceSemantics.Program} {saved : CallFrame} {argument : Atom}
    (marks : List Marks) (source : State User) (request : Request)
    (held : Stack program saved argument marks source.2.scopes) :
    Preserves program saved argument marks source (.call request source) := PettaMarkedTransitions.call_keeps marks source request held

theorem collapse_keeps {User : Type} {program : SpaceSemantics.Program} {saved : CallFrame} {argument : Atom}
    (source : State User) (current : Scope User) (parents : List (Scope User))
    (control : DControl) (context : Context User) (origins : List Nat) (pending : List (Work User))
    (mark : Option Nat) (pendingMarks : List (Option Nat)) (callerMark : Option Nat) (parentMarks : List Marks)
    (expression destination : Atom) (older : List EagerDFS.Destination.Goal)
    (held : Stack program saved argument (⟨mark :: pendingMarks, callerMark⟩ :: parentMarks) source.2.scopes)
    (scopes : source.2.scopes = current :: parents) (front : current.frontier = (control, context, origins) :: pending)
    (goals : control.goals = .evaluate (.expression [.symbol "collapse", expression]) destination :: older)
    (child : Scope User) (atCaller : child.caller = some ({control with goals := older}, destination, context, origins))
    (allocator : Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared.Allocator) (world : EagerDFS.World) :
    Preserves program saved argument (⟨mark :: pendingMarks, callerMark⟩ :: parentMarks) source
      (.silent (allocator, ⟨world, child :: {current with frontier := pending} :: parents⟩)) :=
  PettaMarkedTransitions.collapse_keeps source current parents control context origins pending mark pendingMarks callerMark
    parentMarks held scopes front older destination
    (fun _ returning => PettaCompoundSelectedWork.collapse_caller control context origins returning expression destination older goals)
    child atCaller allocator world

theorem collection_keeps {User : Type} {program : SpaceSemantics.Program} {saved : CallFrame} {argument : Atom}
    (source : State User) (child parent : Scope User) (parents : List (Scope User))
    (childMarks parentMarks : Marks) (outsideMarks : List Marks)
    (held : Stack program saved argument (childMarks :: parentMarks :: outsideMarks) source.2.scopes)
    (scopes : source.2.scopes = child :: parent :: parents)
    (caller : CollectionCaller (Context User)) (atCaller : child.caller = some caller) (copies : List (Atom × List Atom))
    (allocator : Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared.Allocator) (world : EagerDFS.World) :
    Preserves program saved argument (childMarks :: parentMarks :: outsideMarks) source
      (.silent (allocator, ⟨world, {parent with frontier := Source.resumeCopies copies caller :: parent.frontier} :: parents⟩)) :=
  PettaMarkedTransitions.collection_keeps source child parent parents childMarks parentMarks outsideMarks held scopes caller
    atCaller copies (fun _ returning => PettaCompoundSelectedWork.collection_copies copies caller returning) allocator world

theorem commit_keeps {User : Type} {program : SpaceSemantics.Program} {saved : CallFrame} {argument : Atom}
    (source : State User) (current : Scope User) (parents : List (Scope User))
    (control : DControl) (context : Context User) (origins : List Nat) (pending younger kept : List (Work User))
    (mark : Option Nat) (pendingMarks : List (Option Nat)) (callerMark : Option Nat) (parentMarks : List Marks)
    (older : List EagerDFS.Destination.Goal)
    (held : Stack program saved argument (⟨mark :: pendingMarks, callerMark⟩ :: parentMarks) source.2.scopes)
    (scopes : source.2.scopes = current :: parents) (front : current.frontier = (control, context, origins) :: pending)
    (goals : control.goals = .commit :: older) (partition : pending = younger ++ kept)
    (sourceLane : PettaReturnMarkUpdate.frameActive source = false) :
    Preserves program saved argument (⟨mark :: pendingMarks, callerMark⟩ :: parentMarks) source
      (.silent (source.1, ⟨source.2.world,
        {current with frontier := ({control with goals := older}, context, origins) :: kept} :: parents⟩)) :=
  PettaMarkedTransitions.commit_keeps source current parents control context origins pending younger kept mark pendingMarks
    callerMark parentMarks older held scopes front goals partition sourceLane
    (fun _ returning => PettaCompoundSelectedWork.committing control context origins returning older goals)

theorem source_collection_keeps {User : Type} {program : SpaceSemantics.Program} {saved : CallFrame} {argument : Atom}
    {source after : State User} {marks : List Marks}
    (step : Source.CollectionReturn Source.FreshOperations.owned source after)
    (held : Stack program saved argument marks source.2.scopes) :
    Preserves program saved argument marks source (.silent after) :=
  PettaMarkedTransitions.source_collection_keeps step held
    (fun copies caller _ returning => PettaCompoundSelectedWork.collection_copies copies caller returning)

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCompoundReturnScopes
