import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCompoundReturnActive

/-!
# Complete owned-source dispatch preserves computed compound obligations

The actual source owners are consumed in priority order. Physical positions,
depths and earned call order exclude marked terminals from untyped publication.
All reached worlds and records remain the actual source results. This is the
owned-source part of the host proof, not the typed interception/run join or
native lowered-body adequacy.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCompoundReturnScopes

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared (Allocator)
open EagerDFS.Destination
open PettaOccurrenceOverlay
open PettaSelectedReturnScopes (Marks)

theorem scoped_keeps {User : Type} {saved : CallFrame} {argument : Atom}
    {program : SpaceSemantics.Program} {source : State User} {action : Source.ScopeAction Allocator (Context User)}
    (step : Source.ScopedStep Source.FreshOperations.owned .eagerValue program source action)
    (noSequence : Bridges.ScopedQuerySource.syntaxStep source = none)
    (noQuery : Bridges.ScopedQuerySource.queryStep source = none)
    (noCase : Bridges.ScopedCaseSource.readyStep Bridges.ScopedQuerySource.plainQueryPattern source = none)
    (marks : List Marks) (held : Stack program saved argument marks source.2.scopes)
    (depths : PettaReturnMarkDepth.Depths saved.scopeDepth marks)
    (good : PettaCallOrder.Invariant source) (inactive : PettaReturnMarkUpdate.frameActive source = false) :
    Preserves program saved argument marks source (liftSource action) := by
  cases step with
  | active allocator world current parents control context origins pending action front active =>
      cases marks with
      | nil => cases held
      | cons currentMarks parentMarks =>
          rcases currentMarks with ⟨tags, callerMark⟩
          cases tags with
          | nil =>
              have impossible := (List.forall₂_cons.mp held).1.1
              rw [front] at impossible
              cases impossible
          | cons mark pendingMarks =>
              exact active_keeps active front noSequence noQuery noCase mark pendingMarks callerMark parentMarks held inactive
                (PettaReturnMarkDepth.terminal_unmarked_of_positions
                  (fun tracked => PettaCompoundSelectedWork.selected_position tracked)
                  _ current parents control context origins pending mark pendingMarks callerMark parentMarks
                  held depths good rfl front inactive)
  | finished =>
      simpa only [liftSource, Preserves, PettaMarkedTransitions.Preserves, PettaOccurrenceBinding.retained] using
        call_keeps marks _ .invalidTypedState held
  | collected collection => exact source_collection_keeps collection held
  | associated | allocation => exact call_keeps _ _ _ held

theorem base_active_keeps {User : Type} {saved : CallFrame} {argument : Atom}
    (program : SpaceSemantics.Program) (source : State User) (current : Scope User) (parents : List (Scope User))
    (control : DControl) (context : Context User) (origins : List Nat) (pending : List (Work User))
    (mark : Option Nat) (pendingMarks : List (Option Nat)) (callerMark : Option Nat) (parentMarks : List Marks)
    (held : Stack program saved argument (⟨mark :: pendingMarks, callerMark⟩ :: parentMarks) source.2.scopes)
    (depths : PettaReturnMarkDepth.Depths saved.scopeDepth (⟨mark :: pendingMarks, callerMark⟩ :: parentMarks))
    (good : PettaCallOrder.Invariant source) (inactive : PettaReturnMarkUpdate.frameActive source = false)
    (scopes : source.2.scopes = current :: parents) (front : current.frontier = (control, context, origins) :: pending)
    (noCase : Bridges.ScopedCaseSource.readyStep Bridges.ScopedQuerySource.plainQueryPattern source = none) :
    Preserves program saved argument (⟨mark :: pendingMarks, callerMark⟩ :: parentMarks) source
      (liftSource (Bridges.ScopedQuerySource.step .eagerValue program source)) := by
  unfold Bridges.ScopedQuerySource.step
  repeat' first
    | exact syntax_keeps source current parents control context origins pending mark pendingMarks callerMark parentMarks
        _ (by assumption) held scopes front
    | exact constrained_keeps _ source _ (by assumption) held
    | exact mutation_keeps _ source _ (by assumption) held
    | exact captured_keeps source current parents control context origins pending mark pendingMarks callerMark parentMarks
        _ (by assumption) held scopes front
    | exact scoped_keeps ((Source.scoped_step_iff_source .eagerValue program source good.2.valid _).mp rfl)
        (by assumption) (by assumption) noCase _ held depths good inactive
    | split

theorem owned_active_keeps {User : Type} {saved : CallFrame} {argument : Atom}
    (program : SpaceSemantics.Program) (source : State User) (current : Scope User) (parents : List (Scope User))
    (control : DControl) (context : Context User) (origins : List Nat) (pending : List (Work User))
    (mark : Option Nat) (pendingMarks : List (Option Nat)) (callerMark : Option Nat) (parentMarks : List Marks)
    (held : Stack program saved argument (⟨mark :: pendingMarks, callerMark⟩ :: parentMarks) source.2.scopes)
    (depths : PettaReturnMarkDepth.Depths saved.scopeDepth (⟨mark :: pendingMarks, callerMark⟩ :: parentMarks))
    (good : PettaCallOrder.Invariant source) (inactive : PettaReturnMarkUpdate.frameActive source = false)
    (scopes : source.2.scopes = current :: parents) (front : current.frontier = (control, context, origins) :: pending) :
    Preserves program saved argument (⟨mark :: pendingMarks, callerMark⟩ :: parentMarks) source
      (liftSource (Bridges.ScopedQuerySource.ownedStep .eagerValue program source)) := by
  unfold Bridges.ScopedQuerySource.ownedStep
  split
  · exact case_entry_keeps source current parents control context origins pending mark pendingMarks callerMark parentMarks
      _ (by assumption) held scopes front
  · split
    · exact case_ready_keeps source current parents control context origins pending mark pendingMarks callerMark parentMarks
        _ (by assumption) held scopes front
    · have base := base_active_keeps program source current parents control context origins pending mark pendingMarks callerMark
        parentMarks held depths good inactive scopes front (by assumption)
      split
      · exact ownership_keeps _ source _ (by assumption) held
      · dsimp only
        split
        · cases extended : Bridges.ScopedQuerySource.unifyingQueryStep source with
          | none => simpa only [extended, Option.getD_none] using base
          | some action =>
              simpa only [extended, Option.getD_some] using unifying_keeps source current parents control context origins pending
                mark pendingMarks callerMark parentMarks action extended held scopes front
        · exact base

theorem owned_step_keeps {User : Type} {saved : CallFrame} {argument : Atom}
    (program : SpaceSemantics.Program) (source : State User) (marks : List Marks)
    (held : Stack program saved argument marks source.2.scopes)
    (depths : PettaReturnMarkDepth.Depths saved.scopeDepth marks)
    (good : PettaCallOrder.Invariant source) (inactive : PettaReturnMarkUpdate.frameActive source = false) :
    Preserves program saved argument marks source (liftSource (Bridges.ScopedQuerySource.ownedStep .eagerValue program source)) := by
  cases scopes : source.2.scopes with
  | nil => exact False.elim (good.2.nonempty scopes)
  | cons current parents =>
      cases front : current.frontier with
      | nil =>
          have noSequence : Bridges.ScopedQuerySource.syntaxStep source = none := by
            simp [Bridges.ScopedQuerySource.syntaxStep, scopes, front]
          have noConstrained : Bridges.ScopedQuerySource.constrainedCall source = none := by
            simp [Bridges.ScopedQuerySource.constrainedCall, scopes, front]
          have noMutation : Bridges.ScopedQuerySource.mutationCall source = none := by
            simp [Bridges.ScopedQuerySource.mutationCall, scopes, front]
          have noQuery : Bridges.ScopedQuerySource.queryStep source = none := by
            simp [Bridges.ScopedQuerySource.queryStep, scopes, front]
          have noEntry : Bridges.ScopedCaseSource.entryStep source = none := by
            simp [Bridges.ScopedCaseSource.entryStep, scopes, front]
          have noCase : Bridges.ScopedCaseSource.readyStep Bridges.ScopedQuerySource.plainQueryPattern source = none := by
            simp [Bridges.ScopedCaseSource.readyStep, scopes, front]
          have noOwner : Bridges.ScopedQuerySource.ownershipStep program source = none := by
            simp [Bridges.ScopedQuerySource.ownershipStep, scopes, front]
          have noExtended : Bridges.ScopedQuerySource.unifyingQueryStep source = none := by
            simp [Bridges.ScopedQuerySource.unifyingQueryStep, scopes, front]
          have base := scoped_keeps ((Source.scoped_step_iff_source .eagerValue program source good.2.valid _).mp rfl)
            noSequence noQuery noCase marks held depths good inactive
          simp only [Bridges.ScopedQuerySource.ownedStep, noEntry, noCase, noOwner, Bridges.ScopedQuerySource.step,
            noSequence, noConstrained, noMutation, noQuery]
          split
          · simpa only [noExtended, Option.getD_none] using base
          · exact base
      | cons item pending =>
          rcases item with ⟨control, context, origins⟩
          cases marks with
          | nil => rw [scopes] at held; cases held
          | cons currentMarks parentMarks =>
              rcases currentMarks with ⟨tags, callerMark⟩
              cases tags with
              | nil =>
                  have impossible := (List.forall₂_cons.mp (scopes ▸ held)).1.1
                  rw [front] at impossible
                  cases impossible
              | cons mark pendingMarks =>
                  exact owned_active_keeps program source current parents control context origins pending mark pendingMarks callerMark
                    parentMarks held depths good inactive scopes front

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCompoundReturnScopes
