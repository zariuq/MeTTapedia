import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaReturnMarkStep
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaMarkedRuns

/-!
# Actual finite runs preserve computed selected-return lineage

The metadata observer follows the existing machine's steps; it introduces
no expression evaluator or alternate choice of execution services. Every
retained outcome has the uniquely computed annotations, including exhaustion
and requests. The machine's publications, order and multiplicity are unchanged.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaReturnMarkUpdate

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open EagerDFS.Destination
open PettaOccurrenceOverlay
open PettaSelectedReturnScopes (Marks Stack)

theorem run_retained {User : Type} {saved : CallFrame} {argument : Atom}
    (operations : Services User) (program : SpaceSemantics.Program) (fuel : Nat)
    (source : State User) (marks : List Marks)
    (held : Stack saved argument marks source.2.scopes)
    (depths : PettaReturnMarkDepth.Depths saved.scopeDepth marks)
    (good : PettaCallOrder.Invariant source) (body : saved.phase = .body)
    (final : State User)
    (reached : PettaCallerReturnMachine.exitState
      ((PettaOccurrenceOverlay.machine operations .eagerValue program).run fuel source).2 = some final) :
    ∃ next, runMarks operations program fuel source marks = some next ∧
      Stack saved argument next final.2.scopes ∧ PettaReturnMarkDepth.Depths saved.scopeDepth next ∧
      PettaCallOrder.Invariant final :=
  PettaMarkedRuns.run_retained saved.scopeDepth operations program
    (fun next tags tracked owned ordered => step_keeps operations program next tags tracked owned ordered body)
    fuel source marks held depths good final reached

/-- At a reached selected terminal the real dispatcher reads the selected
argument under the reached bindings, not the entry bindings. -/
theorem reached_dispatch {User : Type} {saved : CallFrame} {argument : Atom}
    (operations : Services User) (program : SpaceSemantics.Program) (fuel : Nat)
    (source : State User) (marks : List Marks)
    (held : Stack saved argument marks source.2.scopes)
    (depths : PettaReturnMarkDepth.Depths saved.scopeDepth marks)
    (good : PettaCallOrder.Invariant source) (body : saved.phase = .body)
    (final : State User)
    (reached : PettaCallerReturnMachine.exitState
      ((PettaOccurrenceOverlay.machine operations .eagerValue program).run fuel source).2 = some final)
    (current : Scope User) (parents : List (Scope User)) (control : DControl) (context : Context User)
    (origins : List Nat) (pending : List (Work User))
    (pendingMarks : List (Option Nat)) (callerMark : Option Nat) (parentMarks : List Marks)
    (atMark : runMarks operations program fuel source marks =
      some (⟨some 0 :: pendingMarks, callerMark⟩ :: parentMarks))
    (scopes : final.2.scopes = current :: parents)
    (front : current.frontier = (control, context, origins) :: pending) (terminal : control.goals = []) :
    ∃ outside, context.calls = saved :: outside ∧
      PettaOccurrenceOverlay.step operations .eagerValue program final =
        match resolve control.bindings with
        | none => .call (.source (.branch .invalidEnvironment)) final
        | some environment => consumeBody operations final current parents control context origins pending saved outside
            (read environment argument) := by
  obtain ⟨next, updated, tracked, owned, _ordered⟩ := run_retained operations program fuel source marks held depths good body final reached
  cases Option.some.inj (updated.symm.trans atMark)
  have owner := PettaReturnMarkDepth.source_owner final _ parentMarks tracked owned 0 List.mem_cons_self
  exact PettaSelectedReturnScopes.marked_dispatch saved argument operations program final current parents control context origins
    pending pendingMarks callerMark parentMarks tracked scopes front owner body terminal

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaReturnMarkUpdate
