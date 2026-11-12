import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCompoundReturnStep
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCompoundReturnBoundary
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaMarkedRuns

/-!
# Complete retained host runs preserve compound selected returns

The full actual step law discharges the shared finite-run theorem. A reached
selected terminal then supplies the original guard's current input read,
without assuming a successful body or replacing a compound destination.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCompoundReturnScopes

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open EagerDFS.Destination
open PettaOccurrenceOverlay
open PettaSelectedReturnScopes (Marks)
open PettaReturnMarkUpdate (runMarks)

theorem run_retained {User : Type} {saved : CallFrame} {argument : Atom}
    (operations : Services User) (program : SpaceSemantics.Program) (fuel : Nat)
    (source : State User) (marks : List Marks) (held : Stack program saved argument marks source.2.scopes)
    (depths : PettaReturnMarkDepth.Depths saved.scopeDepth marks)
    (good : PettaCallOrder.Invariant source) (body : saved.phase = .body) (final : State User)
    (reached : PettaCallerReturnMachine.exitState
      ((PettaOccurrenceOverlay.machine operations .eagerValue program).run fuel source).2 = some final) :
    ∃ next, runMarks operations program fuel source marks = some next ∧ Stack program saved argument next final.2.scopes ∧
      PettaReturnMarkDepth.Depths saved.scopeDepth next ∧ PettaCallOrder.Invariant final :=
  PettaMarkedRuns.run_retained saved.scopeDepth operations program
    (fun next tags tracked owned ordered => step_keeps operations program next tags tracked owned ordered body)
    fuel source marks held depths good final reached

theorem reached_dispatch {User : Type} {saved : CallFrame} {argument : Atom}
    (operations : Services User) (program : SpaceSemantics.Program) (fuel : Nat)
    (source : State User) (marks : List Marks) (held : Stack program saved argument marks source.2.scopes)
    (depths : PettaReturnMarkDepth.Depths saved.scopeDepth marks)
    (good : PettaCallOrder.Invariant source) (body : saved.phase = .body) (final : State User)
    (reached : PettaCallerReturnMachine.exitState
      ((PettaOccurrenceOverlay.machine operations .eagerValue program).run fuel source).2 = some final)
    (current : Scope User) (parents : List (Scope User)) (control : DControl) (context : Context User)
    (origins : List Nat) (pending : List (Work User))
    (pendingMarks : List (Option Nat)) (callerMark : Option Nat) (parentMarks : List Marks)
    (atMark : runMarks operations program fuel source marks = some (⟨some 0 :: pendingMarks, callerMark⟩ :: parentMarks))
    (scopes : final.2.scopes = current :: parents) (front : current.frontier = (control, context, origins) :: pending)
    (terminal : control.goals = []) :
    ∃ outside, context.calls = saved :: outside ∧
      PettaOccurrenceOverlay.step operations .eagerValue program final =
        match resolve control.bindings with
        | none => .call (.source (.branch .invalidEnvironment)) final
        | some environment => consumeBody operations final current parents control context origins pending saved outside
            (read environment argument) := by
  obtain ⟨next, updated, tracked, owned, ordered⟩ := run_retained operations program fuel source marks held depths good body final reached
  cases Option.some.inj (updated.symm.trans atMark)
  exact PettaCompoundReturnBoundary.marked_dispatch program saved argument operations final current parents control context origins
    pending pendingMarks callerMark parentMarks tracked owned scopes front body terminal

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCompoundReturnScopes
