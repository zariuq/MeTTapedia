import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedQuerySource
import Mettapedia.Languages.MeTTa.PeTTa.DestinationScopeRefinement

/-!
# Binding and publication boundaries of the owned surface query profile

The existing surface adapter changes pending work or retains a request. Its
captured query records are justified by the existing Choices derivation;
the finite extension enters the existing two-way query operation. The source
body still runs in Destination's scheduler, with its reached world intact.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedQueryBinding

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open EagerDFS (World)
open EagerDFS.Destination
open EagerDFS.Destination.RefinementTransport
open ScopedQuerySource

def Safe {Context : Type} (predicate : BindingPredicate Context) (source : ScopedCursor Context) : Prop :=
  EagerDFS.ScopesValid source.2.scopes ∧ ScopesGood predicate source.2.scopes

def SafeAction {Context : Type} (predicate : BindingPredicate Context) (action : Action Context) : Prop :=
  ScopesPreserved action ∧ ActionGood predicate action

/-- Local adapter evidence concerns only retained records and work. It
cannot itself publish a body result or replace source execution. -/
inductive Local {Context : Type} (source : ScopedCursor Context) : Action Context → Prop where
  | retained (request : ScopeBoundary) : Local source (.call request source)
  | scheduled (scope : CollectionScope Context) (parents : List (CollectionScope Context))
      (control : Control) (context : Context) (origins : List Nat) (pending work : List (CollectionWork Context))
      (scopes : source.2.scopes = scope :: parents)
      (frontier : scope.frontier = (control, context, origins) :: pending)
      (records : ∀ item ∈ work, item.2.1 = context ∧ Extends control.bindings item.1.bindings) :
      Local source (.silent (source.1, ⟨source.2.world,
        {scope with frontier := work ++ pending} :: parents⟩))

theorem Local.safe {Context : Type} {source : ScopedCursor Context} {action : Action Context}
    (earned : Local source action) (predicate : BindingPredicate Context) (safe : Safe predicate source) :
    SafeAction predicate action := by
  cases earned with
  | retained => exact ⟨safe.1, action_call _ _ safe.2⟩
  | scheduled scope parents control context origins pending work scopes frontier records =>
      have valid : EagerDFS.ScopesValid (scope :: parents) := scopes ▸ safe.1
      obtain ⟨scopeGood, parentsGood, active, pendingGood⟩ := focus_good (scopes ▸ safe.2) frontier
      refine ⟨valid.replace_head _ _, action_silent _ (scopes_cons ?_ parentsGood)⟩
      apply scopeGood.frontier
      intro item present
      rcases List.mem_append.mp present with current | older
      · obtain ⟨sameContext, extended⟩ := records item current
        rw [sameContext]
        exact predicate.closed context _ _ active extended
      · exact pendingGood item older

theorem Local.not_publish {Context : Type} {source : ScopedCursor Context} {action : Action Context}
    (earned : Local source action) (events : List CollectedAnswer) (after : ScopedCursor Context) :
    action ≠ .publish events after := by cases earned <;> simp

theorem syntax_local {Context : Type} (source : ScopedCursor Context) (action : Action Context)
    (served : syntaxStep source = some action) : Local source action := by
  cases scopes : source.2.scopes with
  | nil => simp [syntaxStep, scopes] at served
  | cons scope parents =>
      cases frontier : scope.frontier with
      | nil => simp [syntaxStep, scopes, frontier] at served
      | cons item pending =>
          rcases item with ⟨control, context, origins⟩
          simp only [syntaxStep, scopes, frontier] at served
          split at served
          · split at served
            · split at served
              · cases Option.some.inj served
                exact .retained _
              · cases Option.some.inj served
                apply Local.scheduled scope parents control context origins pending [(_, context, origins)] scopes frontier
                intro item present
                cases List.mem_singleton.mp present
                exact ⟨rfl, .refl _⟩
            · cases Option.some.inj served
              exact .retained _
          · cases served

theorem constrained_local {Context : Type} (source : ScopedCursor Context) (action : Action Context)
    (served : constrainedCall source = some action) : Local source action := by
  unfold constrainedCall at served
  repeat' first
    | (cases Option.some.inj served; exact Local.retained _)
    | contradiction
    | (split at served <;> try dsimp only [bind, Option.bind] at served)

theorem mutation_local {Context : Type} (source : ScopedCursor Context) (action : Action Context)
    (served : mutationCall source = some action) : Local source action := by
  unfold mutationCall at served
  repeat' first
    | (cases Option.some.inj served; exact Local.retained _)
    | contradiction
    | (split at served <;> try dsimp only [bind, Option.bind] at served)

theorem ownership_local {Context : Type} (program : SpaceSemantics.Program)
    (source : ScopedCursor Context) (action : Action Context)
    (served : ownershipStep program source = some action) : Local source action := by
  unfold ownershipStep at served
  repeat' first
    | (cases Option.some.inj served; exact Local.retained _)
    | contradiction
    | (split at served <;> try dsimp only [bind, Option.bind] at served)

theorem unifying_local {Context : Type} (source : ScopedCursor Context) (action : Action Context)
    (served : unifyingQueryStep source = some action) : Local source action := by
  cases scopes : source.2.scopes with
  | nil => simp [unifyingQueryStep, scopes] at served
  | cons scope parents =>
      cases frontier : scope.frontier with
      | nil => simp [unifyingQueryStep, scopes, frontier] at served
      | cons item pending =>
          rcases item with ⟨control, context, origins⟩
          simp only [unifyingQueryStep, scopes, frontier] at served
          repeat' first
            | (cases Option.some.inj served
               apply Local.scheduled scope parents control context origins pending [(_, context, origins)] scopes frontier
               intro item present
               cases List.mem_singleton.mp present
               exact ⟨rfl, .refl _⟩)
            | contradiction
            | (split at served <;> try dsimp only [bind, Option.bind] at served)

theorem captured_work_records {Context : Type} (control : Control) (context : Context)
    (origins : List Nat) (pattern body destination : Atom) (older : List Goal)
    (rows : List Atom) (selected : List (Nat × Control))
    (captured : capture control pattern body destination older 0 rows = some selected) :
    ∀ item ∈ work context origins selected,
      item.2.1 = context ∧ Extends control.bindings item.1.bindings := by
  intro item present
  obtain ⟨choice, member, rfl⟩ := List.mem_map.mp present
  have frame := (capture_has_source control pattern body destination older 0 rows selected captured).frames choice member
  obtain ⟨suffix, equal⟩ := frame.2.2.2.2.2.2.1
  exact ⟨rfl, equal ▸ append_extends control.bindings suffix⟩

theorem query_local {Context : Type} (source : ScopedCursor Context) (action : Action Context)
    (served : queryStep source = some action) : Local source action := by
  cases scopes : source.2.scopes with
  | nil => simp [queryStep, scopes] at served
  | cons scope parents =>
      cases frontier : scope.frontier with
      | nil => simp [queryStep, scopes, frontier] at served
      | cons item pending =>
          rcases item with ⟨control, context, origins⟩
          simp only [queryStep, scopes, frontier] at served
          repeat' first
            | (cases Option.some.inj served; exact Local.retained _)
            | (cases Option.some.inj served
               apply Local.scheduled scope parents control context origins pending
                 (work context origins _) scopes frontier
               apply captured_work_records
               assumption)
            | contradiction
            | (split at served <;> try dsimp only [bind, Option.bind] at served)

theorem case_entry_local {Context : Type} (source : ScopedCursor Context) (action : Action Context)
    (served : ScopedCaseSource.entryStep source = some action) : Local source action := by
  cases scopes : source.2.scopes with
  | nil => simp [ScopedCaseSource.entryStep, scopes] at served
  | cons scope parents =>
      cases frontier : scope.frontier with
      | nil => simp [ScopedCaseSource.entryStep, scopes, frontier] at served
      | cons item pending =>
          rcases item with ⟨control, context, origins⟩
          simp only [ScopedCaseSource.entryStep, scopes, frontier] at served
          repeat' first
            | (cases Option.some.inj served; exact Local.retained _)
            | (cases Option.some.inj served
               apply Local.scheduled scope parents control context origins pending [(_, context, origins)] scopes frontier
               intro item present
               cases List.mem_singleton.mp present
               exact ⟨rfl, .refl _⟩)
            | contradiction
            | (split at served <;> try dsimp only [bind, Option.bind] at served)

theorem case_ready_local {Context : Type} (admitPattern : Atom → Bool)
    (source : ScopedCursor Context) (action : Action Context)
    (served : ScopedCaseSource.readyStep admitPattern source = some action) : Local source action := by
  cases scopes : source.2.scopes with
  | nil => simp [ScopedCaseSource.readyStep, scopes] at served
  | cons scope parents =>
      cases frontier : scope.frontier with
      | nil => simp [ScopedCaseSource.readyStep, scopes, frontier] at served
      | cons item pending =>
          rcases item with ⟨control, context, origins⟩
          simp only [ScopedCaseSource.readyStep, scopes, frontier] at served
          repeat' first
            | (cases Option.some.inj served; exact Local.retained _)
            | (cases Option.some.inj served
               apply Local.scheduled scope parents control context origins pending [] scopes frontier
               intro item present
               cases present)
            | (cases Option.some.inj served
               apply Local.scheduled scope parents control context origins pending [(_, context, _)] scopes frontier
               intro item present
               cases List.mem_singleton.mp present
               refine ⟨rfl, ?_⟩
               exact (ScopedCaseSelection.selected_record
                 ((ScopedCaseSelection.select_iff_source _ _ _ _ _).mp (by assumption))).1)
            | contradiction
            | (split at served <;> try dsimp only [bind, Option.bind] at served)

theorem base_step_safe {Context : Type} (predicate : BindingPredicate Context)
    (policy : Policy) (program : SpaceSemantics.Program) (source : ScopedCursor Context)
    (safe : Safe predicate source) : SafeAction predicate (step policy program source) := by
  unfold step
  repeat' first
    | exact (syntax_local source _ (by assumption)).safe predicate safe
    | exact (constrained_local source _ (by assumption)).safe predicate safe
    | exact (mutation_local source _ (by assumption)).safe predicate safe
    | exact (query_local source _ (by assumption)).safe predicate safe
    | exact ⟨scopeStep_scopes_valid policy program source safe.1,
        actual_scope_preserves policy program predicate source safe.1 safe.2⟩
    | split

theorem owned_step_safe {Context : Type} (predicate : BindingPredicate Context)
    (policy : Policy) (program : SpaceSemantics.Program) (source : ScopedCursor Context)
    (safe : Safe predicate source) : SafeAction predicate (ownedStep policy program source) := by
  unfold ownedStep
  split
  · exact (case_entry_local source _ (by assumption)).safe predicate safe
  · split
    · exact (case_ready_local _ source _ (by assumption)).safe predicate safe
    · split
      · exact (ownership_local program source _ (by assumption)).safe predicate safe
      · have base := base_step_safe predicate policy program source safe
        dsimp only
        split
        · cases extended : unifyingQueryStep source with
          | none => simpa only [extended, Option.getD_none] using base
          | some action =>
              simpa only [extended, Option.getD_some] using (unifying_local source action extended).safe predicate safe
        · exact base

theorem base_publication_is_raw {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (source after : ScopedCursor Context) (events : List CollectedAnswer)
    (published : step policy program source = .publish events after) :
    scopeStep policy program source = .publish events after := by
  unfold step at published
  repeat' first
    | exact published
    | exact False.elim ((syntax_local source _ (by assumption)).not_publish events after published)
    | exact False.elim ((constrained_local source _ (by assumption)).not_publish events after published)
    | exact False.elim ((mutation_local source _ (by assumption)).not_publish events after published)
    | exact False.elim ((query_local source _ (by assumption)).not_publish events after published)
    | split at published

theorem owned_publication_is_raw {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (source after : ScopedCursor Context) (events : List CollectedAnswer)
    (published : ownedStep policy program source = .publish events after) :
    scopeStep policy program source = .publish events after := by
  unfold ownedStep at published
  split at published
  · exact False.elim ((case_entry_local source _ (by assumption)).not_publish events after published)
  · split at published
    · exact False.elim ((case_ready_local _ source _ (by assumption)).not_publish events after published)
    · split at published
      · exact False.elim ((ownership_local program source _ (by assumption)).not_publish events after published)
      · dsimp only at published
        split at published
        · cases extended : unifyingQueryStep source with
          | none =>
              simp only [extended, Option.getD_none] at published
              exact base_publication_is_raw policy program source after events published
          | some action =>
              simp only [extended, Option.getD_some] at published
              exact False.elim ((unifying_local source action extended).not_publish events after published)
        · exact base_publication_is_raw policy program source after events published

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedQueryBinding
