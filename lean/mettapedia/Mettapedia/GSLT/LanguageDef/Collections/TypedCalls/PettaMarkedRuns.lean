import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaMarkedTransitions
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaReturnMarkDepth

/-!
# One computed annotation observer over actual host runs

The observer follows existing host steps and never evaluates a source term
itself. The generic finite-run theorem consumes a proved local step law;
depths and call order are transported by their existing independent owners.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaReturnMarkUpdate

open Mettapedia.Languages.MeTTa.PeTTa
open EagerDFS.Destination
open PettaOccurrenceOverlay
open PettaSelectedReturnScopes (Marks)

def runMarks {User : Type} (operations : Services User) (program : SpaceSemantics.Program) :
    Nat → State User → List Marks → Option (List Marks)
  | 0, _, marks => some marks
  | fuel + 1, source, marks =>
      match PettaOccurrenceOverlay.step operations .eagerValue program source with
      | .silent next | .publish _ next => advance marks source next >>= runMarks operations program fuel next
      | .finish final | .call _ final => advance marks source final
      | .fail _ => none

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaReturnMarkUpdate

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaMarkedRuns

open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open EagerDFS.Destination
open PettaOccurrenceOverlay
open PettaSelectedReturnScopes (Marks)
open PettaReturnMarkUpdate (runMarks)

theorem run_retained {User : Type} {Held : Nat → Work User → Prop} (owner : Nat)
    (operations : Services User) (program : SpaceSemantics.Program)
    (keeps : ∀ source marks, PettaScopeMarks.Stack Held marks source.2.scopes →
      PettaReturnMarkDepth.Depths owner marks → PettaCallOrder.Invariant source →
      PettaMarkedTransitions.Preserves Held marks source (PettaOccurrenceOverlay.step operations .eagerValue program source))
    (fuel : Nat) (source : State User) (marks : List Marks)
    (held : PettaScopeMarks.Stack Held marks source.2.scopes) (depths : PettaReturnMarkDepth.Depths owner marks)
    (good : PettaCallOrder.Invariant source) (final : State User)
    (reached : PettaCallerReturnMachine.exitState
      ((PettaOccurrenceOverlay.machine operations .eagerValue program).run fuel source).2 = some final) :
    ∃ next, runMarks operations program fuel source marks = some next ∧ PettaScopeMarks.Stack Held next final.2.scopes ∧
      PettaReturnMarkDepth.Depths owner next ∧ PettaCallOrder.Invariant final := by
  induction fuel generalizing source marks with
  | zero =>
      cases Option.some.inj reached
      exact ⟨marks, rfl, held, depths, good⟩
  | succ fuel ih =>
      have kept := keeps source marks held depths good
      have goodNext := PettaCallOrder.step_invariant operations program source good
      cases advanced : PettaOccurrenceOverlay.step operations .eagerValue program source with
      | silent next | publish events next =>
          rw [advanced] at kept goodNext
          obtain ⟨nextMarks, computed, nextHeld⟩ := kept next (by simp [PettaOccurrenceBinding.retained])
          have nextDepths := PettaReturnMarkDepth.advance_depths marks nextMarks source next depths computed
          have nextGood := goodNext next (by simp [PettaOccurrenceBinding.retained])
          have after : PettaCallerReturnMachine.exitState
              ((PettaOccurrenceOverlay.machine operations .eagerValue program).run fuel next).2 = some final := by
            simpa only [Machine.run, PettaOccurrenceOverlay.machine, advanced] using reached
          obtain ⟨lastMarks, updated, lastHeld, lastDepths, lastGood⟩ :=
            ih next nextMarks nextHeld nextDepths nextGood after
          exact ⟨lastMarks, by simpa only [runMarks, advanced, computed, bind, Option.bind] using updated,
            lastHeld, lastDepths, lastGood⟩
      | finish reachedState | call request reachedState =>
          rw [advanced] at kept goodNext
          simp only [Machine.run, PettaOccurrenceOverlay.machine, advanced, PettaCallerReturnMachine.exitState] at reached
          cases Option.some.inj reached
          obtain ⟨nextMarks, computed, nextHeld⟩ := kept final (by simp [PettaOccurrenceBinding.retained])
          exact ⟨nextMarks, by simpa only [runMarks, advanced] using computed, nextHeld,
            PettaReturnMarkDepth.advance_depths marks nextMarks source final depths computed,
            goodNext final (by simp [PettaOccurrenceBinding.retained])⟩
      | fail events =>
          simp [Machine.run, PettaOccurrenceOverlay.machine, advanced, PettaCallerReturnMachine.exitState] at reached

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaMarkedRuns
