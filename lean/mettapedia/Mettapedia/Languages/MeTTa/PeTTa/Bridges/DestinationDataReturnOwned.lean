import Mettapedia.Languages.MeTTa.PeTTa.Bridges.DestinationDataReturnActive
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedReturnOwned

/-!
# Compound return preservation of the maintained owned source dispatcher

The surface owners are consumed in their actual priority order. The raw
source theorem is used only after those owners decline. This is preservation
of source return obligations, not equivalence to a native lowered body.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.DestinationDataReturnOwned

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open EagerDFS.Destination
open DestinationDataReturnScopes DestinationDataReturnInvocation

theorem syntax_preserves {Context : Type} (inputs : Context → Atom) (program : SpaceSemantics.Program)
    (source : ScopedCursor Context) (action : ScopedQuerySource.Action Context)
    (computed : ScopedQuerySource.syntaxStep source = some action)
    (valid : Stack program inputs source.2.scopes) : ActionReturns program inputs action := by
  cases scopes : source.2.scopes with
  | nil => exact (valid.nonempty scopes).elim
  | cons scope parents =>
      have stack := scopes ▸ valid
      cases frontier : scope.frontier with
      | nil => simp [ScopedQuerySource.syntaxStep, scopes, frontier] at computed
      | cons item pending =>
          rcases item with ⟨control, context, origins⟩
          simp only [ScopedQuerySource.syntaxStep, scopes, frontier] at computed
          repeat' first
            | (cases Option.some.inj computed; exact call_returns _ _ valid)
            | (cases Option.some.inj computed
               apply silent_returns
               apply stack.replace_active control context origins pending [(_, context, origins)] scope.collected frontier
               rintro ⟨recipe, data, holds⟩ work member
               cases List.mem_singleton.mp member
               exact ⟨recipe, data, DestinationDataReturnDispatch.sequence_return data control _ _ _ _ _ holds
                 (by assumption) (by assumption)⟩)
            | contradiction
            | (split at computed <;> try dsimp only [bind, Option.bind] at computed)

theorem case_entry_preserves {Context : Type} (inputs : Context → Atom) (program : SpaceSemantics.Program)
    (source : ScopedCursor Context) (action : ScopedQuerySource.Action Context)
    (computed : ScopedCaseSource.entryStep source = some action)
    (valid : Stack program inputs source.2.scopes) : ActionReturns program inputs action := by
  cases scopes : source.2.scopes with
  | nil => exact (valid.nonempty scopes).elim
  | cons scope parents =>
      have stack := scopes ▸ valid
      cases frontier : scope.frontier with
      | nil => simp [ScopedCaseSource.entryStep, scopes, frontier] at computed
      | cons item pending =>
          rcases item with ⟨control, context, origins⟩
          simp only [ScopedCaseSource.entryStep, scopes, frontier] at computed
          repeat' first
            | (cases Option.some.inj computed; exact call_returns _ _ valid)
            | (cases Option.some.inj computed
               apply silent_returns
               apply stack.replace_active control context origins pending [(_, context, origins)] scope.collected frontier
               rintro ⟨recipe, data, holds⟩ work member
               cases List.mem_singleton.mp member
               exact ⟨recipe, data, DestinationDataReturnDispatch.case_key_return data control _ _ _ _ holds (by assumption)⟩)
            | contradiction
            | (split at computed <;> try dsimp only [bind, Option.bind] at computed)

theorem case_ready_preserves {Context : Type} (inputs : Context → Atom) (program : SpaceSemantics.Program)
    (source : ScopedCursor Context) (action : ScopedQuerySource.Action Context)
    (computed : ScopedCaseSource.readyStep ScopedQuerySource.plainQueryPattern source = some action)
    (valid : Stack program inputs source.2.scopes) : ActionReturns program inputs action := by
  cases scopes : source.2.scopes with
  | nil => exact (valid.nonempty scopes).elim
  | cons scope parents =>
      have stack := scopes ▸ valid
      cases frontier : scope.frontier with
      | nil => simp [ScopedCaseSource.readyStep, scopes, frontier] at computed
      | cons item pending =>
          rcases item with ⟨control, context, origins⟩
          simp only [ScopedCaseSource.readyStep, scopes, frontier] at computed
          repeat' first
            | (cases Option.some.inj computed; exact call_returns _ _ valid)
            | (cases Option.some.inj computed
               apply silent_returns
               exact stack.replace_active control context origins pending [] scope.collected frontier
                 (by intro _ work member; cases member))
            | (cases Option.some.inj computed
               apply silent_returns
               apply stack.replace_active control context origins pending [(_, context, _)] scope.collected frontier
               rintro ⟨recipe, data, holds⟩ work member
               cases List.mem_singleton.mp member
               exact ⟨recipe, data, DestinationDataReturnDispatch.case_body_return control _ _ _ _ _ _ holds
                 (by assumption) (by assumption)
                 ((ScopedCaseSelection.select_iff_source _ _ _ _ _).mp (by assumption))⟩)
            | contradiction
            | (split at computed <;> try dsimp only [bind, Option.bind] at computed)

theorem constrained_preserves {Context : Type} (inputs : Context → Atom) (program : SpaceSemantics.Program)
    (source : ScopedCursor Context) (action : ScopedQuerySource.Action Context)
    (computed : ScopedQuerySource.constrainedCall source = some action)
    (valid : Stack program inputs source.2.scopes) : ActionReturns program inputs action := by
  unfold ScopedQuerySource.constrainedCall at computed
  repeat' first
    | (cases Option.some.inj computed; exact call_returns _ _ valid)
    | contradiction
    | (split at computed <;> try dsimp only [bind, Option.bind] at computed)

theorem mutation_preserves {Context : Type} (inputs : Context → Atom) (program : SpaceSemantics.Program)
    (source : ScopedCursor Context) (action : ScopedQuerySource.Action Context)
    (computed : ScopedQuerySource.mutationCall source = some action)
    (valid : Stack program inputs source.2.scopes) : ActionReturns program inputs action := by
  unfold ScopedQuerySource.mutationCall at computed
  repeat' first
    | (cases Option.some.inj computed; exact call_returns _ _ valid)
    | contradiction
    | (split at computed <;> try dsimp only [bind, Option.bind] at computed)

theorem ownership_preserves {Context : Type} (inputs : Context → Atom) (program : SpaceSemantics.Program)
    (source : ScopedCursor Context) (action : ScopedQuerySource.Action Context)
    (computed : ScopedQuerySource.ownershipStep program source = some action)
    (valid : Stack program inputs source.2.scopes) : ActionReturns program inputs action := by
  unfold ScopedQuerySource.ownershipStep at computed
  repeat' first
    | (cases Option.some.inj computed; exact call_returns _ _ valid)
    | contradiction
    | (split at computed <;> try dsimp only [bind, Option.bind] at computed)

theorem captured_preserves {Context : Type} (inputs : Context → Atom) (program : SpaceSemantics.Program)
    (source : ScopedCursor Context) (action : ScopedQuerySource.Action Context)
    (computed : ScopedQuerySource.queryStep source = some action)
    (valid : Stack program inputs source.2.scopes) : ActionReturns program inputs action := by
  cases scopes : source.2.scopes with
  | nil => exact (valid.nonempty scopes).elim
  | cons scope parents =>
      have stack := scopes ▸ valid
      cases frontier : scope.frontier with
      | nil => simp [ScopedQuerySource.queryStep, scopes, frontier] at computed
      | cons item pending =>
          rcases item with ⟨control, context, origins⟩
          simp only [ScopedQuerySource.queryStep, scopes, frontier] at computed
          repeat' first
            | (cases Option.some.inj computed; exact call_returns _ _ valid)
            | (cases Option.some.inj computed
               apply silent_returns
               apply stack.replace_active control context origins pending (ScopedQuerySource.work context origins _) scope.collected frontier
               rintro ⟨recipe, data, holds⟩ work member
               obtain ⟨choice, present, rfl⟩ := List.mem_map.mp member
               exact ⟨recipe, data, DestinationDataReturnDispatch.captured_query_return control _ _ _ _ _ _ _ _ _ holds
                 (by assumption) (ScopedQuerySource.capture_has_source _ _ _ _ _ _ _ _ (by assumption)) choice present⟩)
            | contradiction
            | (split at computed <;> try dsimp only [bind, Option.bind] at computed)

theorem unifying_preserves {Context : Type} (inputs : Context → Atom) (program : SpaceSemantics.Program)
    (source : ScopedCursor Context) (action : ScopedQuerySource.Action Context)
    (computed : ScopedQuerySource.unifyingQueryStep source = some action)
    (valid : Stack program inputs source.2.scopes) : ActionReturns program inputs action := by
  cases scopes : source.2.scopes with
  | nil => exact (valid.nonempty scopes).elim
  | cons scope parents =>
      have stack := scopes ▸ valid
      cases frontier : scope.frontier with
      | nil => simp [ScopedQuerySource.unifyingQueryStep, scopes, frontier] at computed
      | cons item pending =>
          rcases item with ⟨control, context, origins⟩
          simp only [ScopedQuerySource.unifyingQueryStep, scopes, frontier] at computed
          repeat' first
            | (cases Option.some.inj computed
               apply silent_returns
               apply stack.replace_active control context origins pending [(_, context, origins)] scope.collected frontier
               rintro ⟨recipe, data, holds⟩ work member
               cases List.mem_singleton.mp member
               exact ⟨recipe, data, DestinationDataReturnDispatch.query_ready_to_owned control _ _ _ _ _ holds (by assumption)⟩)
            | contradiction
            | (split at computed <;> try dsimp only [bind, Option.bind] at computed)

theorem base_step_preserves {Context : Type} (inputs : Context → Atom) (program : SpaceSemantics.Program)
    (source : ScopedCursor Context) (validScopes : EagerDFS.ScopesValid source.2.scopes)
    (noCase : ScopedCaseSource.readyStep ScopedQuerySource.plainQueryPattern source = none)
    (valid : Stack program inputs source.2.scopes) :
    ActionReturns program inputs (ScopedQuerySource.step .eagerValue program source) := by
  unfold ScopedQuerySource.step
  repeat' first
    | exact syntax_preserves inputs program source _ (by assumption) valid
    | exact constrained_preserves inputs program source _ (by assumption) valid
    | exact mutation_preserves inputs program source _ (by assumption) valid
    | exact captured_preserves inputs program source _ (by assumption) valid
    | exact DestinationDataReturnActive.scoped_preserves inputs
        ((Source.scoped_step_iff_source .eagerValue program source validScopes _).mp rfl)
        (by assumption) (by assumption) noCase valid
    | split

theorem owned_step_preserves {Context : Type} (inputs : Context → Atom) (program : SpaceSemantics.Program)
    (source : ScopedCursor Context) (validScopes : EagerDFS.ScopesValid source.2.scopes)
    (valid : Stack program inputs source.2.scopes) :
    ActionReturns program inputs (ScopedQuerySource.ownedStep .eagerValue program source) := by
  unfold ScopedQuerySource.ownedStep
  split
  · exact case_entry_preserves inputs program source _ (by assumption) valid
  · split
    · exact case_ready_preserves inputs program source _ (by assumption) valid
    · have base := base_step_preserves inputs program source validScopes (by assumption) valid
      split
      · exact ownership_preserves inputs program source _ (by assumption) valid
      · dsimp only
        split
        · cases extended : ScopedQuerySource.unifyingQueryStep source with
          | none => simpa only [extended, Option.getD_none] using base
          | some action =>
              simpa only [extended, Option.getD_some] using unifying_preserves inputs program source action extended valid
        · exact base

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.DestinationDataReturnOwned
