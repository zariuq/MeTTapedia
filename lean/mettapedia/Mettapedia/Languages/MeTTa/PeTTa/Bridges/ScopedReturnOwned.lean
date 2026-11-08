import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedReturnActive

/-!
# Return preservation of the maintained owned surface step

The macro adapters are checked against their actual computed source actions.
The raw dispatcher is used only in its genuine fallthrough branch, where
the local source theorem's phase conditions have already been earned.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedReturnOwned

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open EagerDFS.Destination
open ScopedReturnScopes ScopedReturnInvocation

theorem syntax_preserves {Context : Type} (inputs : Context → Atom) (source : ScopedCursor Context)
    (action : ScopedQuerySource.Action Context) (computed : ScopedQuerySource.syntaxStep source = some action)
    (valid : Stack inputs source.2.scopes) : ActionReturns inputs action := by
  cases scopes : source.2.scopes with
  | nil => exact False.elim (valid.nonempty scopes)
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
               rintro ⟨name, holds⟩ work member
               cases List.mem_singleton.mp member
               exact ⟨name, ScopedReturnDispatch.sequence_return name _ control _ _ _ _ _ holds
                 (by assumption) (by assumption)⟩)
            | contradiction
            | (split at computed <;> try dsimp only [bind, Option.bind] at computed)

theorem case_entry_preserves {Context : Type} (inputs : Context → Atom) (source : ScopedCursor Context)
    (action : ScopedQuerySource.Action Context) (computed : ScopedCaseSource.entryStep source = some action)
    (valid : Stack inputs source.2.scopes) : ActionReturns inputs action := by
  cases scopes : source.2.scopes with
  | nil => exact False.elim (valid.nonempty scopes)
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
               rintro ⟨name, holds⟩ work member
               cases List.mem_singleton.mp member
               exact ⟨name, ScopedReturnDispatch.case_key_return name _ control _ _ _ _ holds (by assumption)⟩)
            | contradiction
            | (split at computed <;> try dsimp only [bind, Option.bind] at computed)

theorem case_ready_preserves {Context : Type} (inputs : Context → Atom) (source : ScopedCursor Context)
    (action : ScopedQuerySource.Action Context)
    (computed : ScopedCaseSource.readyStep ScopedQuerySource.plainQueryPattern source = some action)
    (valid : Stack inputs source.2.scopes) : ActionReturns inputs action := by
  cases scopes : source.2.scopes with
  | nil => exact False.elim (valid.nonempty scopes)
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
               rintro ⟨name, holds⟩ work member
               cases List.mem_singleton.mp member
               exact ⟨name, ScopedReturnDispatch.case_body_return name _ control _ _ _ _ _ _ holds
                 (by assumption) (by assumption)
                 ((ScopedCaseSelection.select_iff_source _ _ _ _ _).mp (by assumption))⟩)
            | contradiction
            | (split at computed <;> try dsimp only [bind, Option.bind] at computed)

theorem constrained_preserves {Context : Type} (inputs : Context → Atom) (source : ScopedCursor Context)
    (action : ScopedQuerySource.Action Context) (computed : ScopedQuerySource.constrainedCall source = some action)
    (valid : Stack inputs source.2.scopes) : ActionReturns inputs action := by
  unfold ScopedQuerySource.constrainedCall at computed
  repeat' first
    | (cases Option.some.inj computed; exact call_returns _ _ valid)
    | contradiction
    | (split at computed <;> try dsimp only [bind, Option.bind] at computed)

theorem mutation_preserves {Context : Type} (inputs : Context → Atom) (source : ScopedCursor Context)
    (action : ScopedQuerySource.Action Context) (computed : ScopedQuerySource.mutationCall source = some action)
    (valid : Stack inputs source.2.scopes) : ActionReturns inputs action := by
  unfold ScopedQuerySource.mutationCall at computed
  repeat' first
    | (cases Option.some.inj computed; exact call_returns _ _ valid)
    | contradiction
    | (split at computed <;> try dsimp only [bind, Option.bind] at computed)

theorem ownership_preserves {Context : Type} (inputs : Context → Atom) (program : SpaceSemantics.Program)
    (source : ScopedCursor Context) (action : ScopedQuerySource.Action Context)
    (computed : ScopedQuerySource.ownershipStep program source = some action)
    (valid : Stack inputs source.2.scopes) : ActionReturns inputs action := by
  unfold ScopedQuerySource.ownershipStep at computed
  repeat' first
    | (cases Option.some.inj computed; exact call_returns _ _ valid)
    | contradiction
    | (split at computed <;> try dsimp only [bind, Option.bind] at computed)

theorem captured_preserves {Context : Type} (inputs : Context → Atom) (source : ScopedCursor Context)
    (action : ScopedQuerySource.Action Context) (computed : ScopedQuerySource.queryStep source = some action)
    (valid : Stack inputs source.2.scopes) : ActionReturns inputs action := by
  cases scopes : source.2.scopes with
  | nil => exact False.elim (valid.nonempty scopes)
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
               rintro ⟨name, holds⟩ work member
               obtain ⟨choice, present, rfl⟩ := List.mem_map.mp member
               exact ⟨name, ScopedReturnDispatch.captured_query_return name _ control _ _ _ _ _ _ _ _ _ holds
                 (by assumption) (ScopedQuerySource.capture_has_source _ _ _ _ _ _ _ _ (by assumption)) choice present⟩)
            | contradiction
            | (split at computed <;> try dsimp only [bind, Option.bind] at computed)

theorem unifying_preserves {Context : Type} (inputs : Context → Atom) (source : ScopedCursor Context)
    (action : ScopedQuerySource.Action Context) (computed : ScopedQuerySource.unifyingQueryStep source = some action)
    (valid : Stack inputs source.2.scopes) : ActionReturns inputs action := by
  cases scopes : source.2.scopes with
  | nil => exact False.elim (valid.nonempty scopes)
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
               rintro ⟨name, holds⟩ work member
               cases List.mem_singleton.mp member
               exact ⟨name, ScopedReturnDispatch.query_ready_to_owned name _ control _ _ _ _ _ holds (by assumption)⟩)
            | contradiction
            | (split at computed <;> try dsimp only [bind, Option.bind] at computed)

theorem base_step_preserves {Context : Type} (inputs : Context → Atom) (program : SpaceSemantics.Program)
    (source : ScopedCursor Context) (validScopes : EagerDFS.ScopesValid source.2.scopes)
    (noCase : ScopedCaseSource.readyStep ScopedQuerySource.plainQueryPattern source = none)
    (valid : Stack inputs source.2.scopes) : ActionReturns inputs (ScopedQuerySource.step .eagerValue program source) := by
  unfold ScopedQuerySource.step
  repeat' first
    | exact syntax_preserves inputs source _ (by assumption) valid
    | exact constrained_preserves inputs source _ (by assumption) valid
    | exact mutation_preserves inputs source _ (by assumption) valid
    | exact captured_preserves inputs source _ (by assumption) valid
    | exact ScopedReturnActive.scoped_preserves inputs
        ((Source.scoped_step_iff_source .eagerValue program source validScopes _).mp rfl)
        (by assumption) (by assumption) noCase valid
    | split

theorem owned_step_preserves {Context : Type} (inputs : Context → Atom) (program : SpaceSemantics.Program)
    (source : ScopedCursor Context) (validScopes : EagerDFS.ScopesValid source.2.scopes)
    (valid : Stack inputs source.2.scopes) : ActionReturns inputs (ScopedQuerySource.ownedStep .eagerValue program source) := by
  unfold ScopedQuerySource.ownedStep
  split
  · exact case_entry_preserves inputs source _ (by assumption) valid
  · split
    · exact case_ready_preserves inputs source _ (by assumption) valid
    · have base := base_step_preserves inputs program source validScopes (by assumption) valid
      split
      · exact ownership_preserves inputs program source _ (by assumption) valid
      · dsimp only
        split
        · cases extended : ScopedQuerySource.unifyingQueryStep source with
          | none => simpa only [extended, Option.getD_none] using base
          | some action =>
              simpa only [extended, Option.getD_some] using unifying_preserves inputs source action extended valid
        · exact base

theorem local_scope_validity {Context : Type} {source : ScopedCursor Context}
    {action : ScopedQuerySource.Action Context} (localAction : ScopedQueryBinding.Local source action)
    (valid : EagerDFS.ScopesValid source.2.scopes) : ScopesPreserved action := by
  cases localAction with
  | retained => exact valid
  | scheduled scope parents control context origins pending work scopes frontier records =>
      have validBefore : EagerDFS.ScopesValid (scope :: parents) := scopes ▸ valid
      exact validBefore.replace_head _ _

theorem base_step_scope_validity {Context : Type} (program : SpaceSemantics.Program)
    (source : ScopedCursor Context) (valid : EagerDFS.ScopesValid source.2.scopes) :
    ScopesPreserved (ScopedQuerySource.step .eagerValue program source) := by
  unfold ScopedQuerySource.step
  repeat' first
    | exact local_scope_validity (ScopedQueryBinding.syntax_local source _ (by assumption)) valid
    | exact local_scope_validity (ScopedQueryBinding.constrained_local source _ (by assumption)) valid
    | exact local_scope_validity (ScopedQueryBinding.mutation_local source _ (by assumption)) valid
    | exact local_scope_validity (ScopedQueryBinding.query_local source _ (by assumption)) valid
    | exact scopeStep_scopes_valid .eagerValue program source valid
    | split

theorem owned_step_scope_validity {Context : Type} (program : SpaceSemantics.Program)
    (source : ScopedCursor Context) (valid : EagerDFS.ScopesValid source.2.scopes) :
    ScopesPreserved (ScopedQuerySource.ownedStep .eagerValue program source) := by
  unfold ScopedQuerySource.ownedStep
  split
  · exact local_scope_validity (ScopedQueryBinding.case_entry_local source _ (by assumption)) valid
  · split
    · exact local_scope_validity (ScopedQueryBinding.case_ready_local _ source _ (by assumption)) valid
    · have base := base_step_scope_validity program source valid
      split
      · exact local_scope_validity (ScopedQueryBinding.ownership_local program source _ (by assumption)) valid
      · dsimp only
        split
        · cases extended : ScopedQuerySource.unifyingQueryStep source with
          | none => simpa only [extended, Option.getD_none] using base
          | some action =>
              simpa only [extended, Option.getD_some] using
                local_scope_validity (ScopedQueryBinding.unifying_local source action extended) valid
        · exact base

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedReturnOwned
