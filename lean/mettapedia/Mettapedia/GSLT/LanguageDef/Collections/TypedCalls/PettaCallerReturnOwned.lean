import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCallerReturnSourceActive

/-!
# Owned source handlers preserve pending typed-caller returns

The existing surface handlers retain the same typed context and reached
logical record. Their source recipes justify the no-typed-caller case; record
refinement protects a suspended outer return when typed prefix calls are active.
This module composes those facts through the actual owned dispatcher. It proves
retained-state preservation, not a publication or native execution theorem.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCallerReturnOwned

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open EagerDFS.Destination
open PettaOccurrenceOverlay PettaCallerReturnFrames
open PettaCallerReturnSourceInvocation

private theorem nonempty {User : Type} (inputs : User → Atom) (source : State User)
    (held : PettaCallerReturnView.Holds inputs source) : source.2.scopes ≠ [] := by
  intro empty
  apply Bridges.ScopedReturnScopes.Stack.nonempty held
  simp [PettaCallerReturnView.state, empty]

theorem syntax_preserves {User : Type} (inputs : User → Atom) (source : State User)
    (action : Bridges.ScopedQuerySource.Action (Context User))
    (computed : Bridges.ScopedQuerySource.syntaxStep source = some action)
    (held : PettaCallerReturnView.Holds inputs source) : Preserves inputs action := by
  cases scopes : source.2.scopes with
  | nil => exact False.elim (nonempty inputs source held scopes)
  | cons current parents =>
      cases frontier : current.frontier with
      | nil => simp [Bridges.ScopedQuerySource.syntaxStep, scopes, frontier] at computed
      | cons item pending =>
          rcases item with ⟨control, context, origins⟩
          simp only [Bridges.ScopedQuerySource.syntaxStep, scopes, frontier] at computed
          repeat' first
            | (cases Option.some.inj computed; exact call_preserves _ _ held)
            | (cases Option.some.inj computed
               apply silent_preserves
               apply PettaCallerReturnView.replace_active inputs source current parents control context origins pending
                 [(_, context, origins)] current.collected source.1 source.2.world held scopes frontier
               intro captured work member
               cases List.mem_singleton.mp member
               apply captured.source_step
               · exact .refl _
               · rintro ⟨name, returning⟩
                 exact ⟨name, Bridges.ScopedReturnDispatch.sequence_return name _ control _ _ _ _ _ returning
                   (by assumption) (by assumption)⟩)
            | contradiction
            | (split at computed <;> try dsimp only [bind, Option.bind] at computed)

theorem case_entry_preserves {User : Type} (inputs : User → Atom) (source : State User)
    (action : Bridges.ScopedQuerySource.Action (Context User))
    (computed : Bridges.ScopedCaseSource.entryStep source = some action)
    (held : PettaCallerReturnView.Holds inputs source) : Preserves inputs action := by
  cases scopes : source.2.scopes with
  | nil => exact False.elim (nonempty inputs source held scopes)
  | cons current parents =>
      cases frontier : current.frontier with
      | nil => simp [Bridges.ScopedCaseSource.entryStep, scopes, frontier] at computed
      | cons item pending =>
          rcases item with ⟨control, context, origins⟩
          simp only [Bridges.ScopedCaseSource.entryStep, scopes, frontier] at computed
          repeat' first
            | (cases Option.some.inj computed; exact call_preserves _ _ held)
            | (cases Option.some.inj computed
               apply silent_preserves
               apply PettaCallerReturnView.replace_active inputs source current parents control context origins pending
                 [(_, context, origins)] current.collected source.1 source.2.world held scopes frontier
               intro captured work member
               cases List.mem_singleton.mp member
               apply captured.source_step
               · exact .refl _
               · rintro ⟨name, returning⟩
                 exact ⟨name, Bridges.ScopedReturnDispatch.case_key_return name _ control _ _ _ _ returning
                   (by assumption)⟩)
            | contradiction
            | (split at computed <;> try dsimp only [bind, Option.bind] at computed)

theorem case_ready_preserves {User : Type} (inputs : User → Atom) (source : State User)
    (action : Bridges.ScopedQuerySource.Action (Context User))
    (computed : Bridges.ScopedCaseSource.readyStep Bridges.ScopedQuerySource.plainQueryPattern source = some action)
    (held : PettaCallerReturnView.Holds inputs source) : Preserves inputs action := by
  cases scopes : source.2.scopes with
  | nil => exact False.elim (nonempty inputs source held scopes)
  | cons current parents =>
      cases frontier : current.frontier with
      | nil => simp [Bridges.ScopedCaseSource.readyStep, scopes, frontier] at computed
      | cons item pending =>
          rcases item with ⟨control, context, origins⟩
          simp only [Bridges.ScopedCaseSource.readyStep, scopes, frontier] at computed
          repeat' first
            | (cases Option.some.inj computed; exact call_preserves _ _ held)
            | (cases Option.some.inj computed
               apply silent_preserves
               exact PettaCallerReturnView.replace_active inputs source current parents control context origins pending
                 [] current.collected source.1 source.2.world held scopes frontier
                 (by intro _ work member; cases member))
            | (cases Option.some.inj computed
               apply silent_preserves
               apply PettaCallerReturnView.replace_active inputs source current parents control context origins pending
                 [(_, context, _)] current.collected source.1 source.2.world held scopes frontier
               intro captured work member
               cases List.mem_singleton.mp member
               have selected := (Bridges.ScopedCaseSelection.select_iff_source _ _ _ _ _).mp (by assumption)
               apply captured.source_step
               · exact (Bridges.ScopedCaseSelection.selected_record selected).1
               · rintro ⟨name, returning⟩
                 exact ⟨name, Bridges.ScopedReturnDispatch.case_body_return name _ control _ _ _ _ _ _ returning
                   (by assumption) (by assumption) selected⟩)
            | contradiction
            | (split at computed <;> try dsimp only [bind, Option.bind] at computed)

theorem constrained_preserves {User : Type} (inputs : User → Atom) (source : State User)
    (action : Bridges.ScopedQuerySource.Action (Context User))
    (computed : Bridges.ScopedQuerySource.constrainedCall source = some action)
    (held : PettaCallerReturnView.Holds inputs source) : Preserves inputs action := by
  unfold Bridges.ScopedQuerySource.constrainedCall at computed
  repeat' first
    | (cases Option.some.inj computed; exact call_preserves _ _ held)
    | contradiction
    | (split at computed <;> try dsimp only [bind, Option.bind] at computed)

theorem mutation_preserves {User : Type} (inputs : User → Atom) (source : State User)
    (action : Bridges.ScopedQuerySource.Action (Context User))
    (computed : Bridges.ScopedQuerySource.mutationCall source = some action)
    (held : PettaCallerReturnView.Holds inputs source) : Preserves inputs action := by
  unfold Bridges.ScopedQuerySource.mutationCall at computed
  repeat' first
    | (cases Option.some.inj computed; exact call_preserves _ _ held)
    | contradiction
    | (split at computed <;> try dsimp only [bind, Option.bind] at computed)

theorem ownership_preserves {User : Type} (inputs : User → Atom) (program : SpaceSemantics.Program)
    (source : State User) (action : Bridges.ScopedQuerySource.Action (Context User))
    (computed : Bridges.ScopedQuerySource.ownershipStep program source = some action)
    (held : PettaCallerReturnView.Holds inputs source) : Preserves inputs action := by
  unfold Bridges.ScopedQuerySource.ownershipStep at computed
  repeat' first
    | (cases Option.some.inj computed; exact call_preserves _ _ held)
    | contradiction
    | (split at computed <;> try dsimp only [bind, Option.bind] at computed)

theorem captured_preserves {User : Type} (inputs : User → Atom) (source : State User)
    (action : Bridges.ScopedQuerySource.Action (Context User))
    (computed : Bridges.ScopedQuerySource.queryStep source = some action)
    (held : PettaCallerReturnView.Holds inputs source) : Preserves inputs action := by
  cases scopes : source.2.scopes with
  | nil => exact False.elim (nonempty inputs source held scopes)
  | cons current parents =>
      cases frontier : current.frontier with
      | nil => simp [Bridges.ScopedQuerySource.queryStep, scopes, frontier] at computed
      | cons item pending =>
          rcases item with ⟨control, context, origins⟩
          simp only [Bridges.ScopedQuerySource.queryStep, scopes, frontier] at computed
          repeat' first
            | (cases Option.some.inj computed; exact call_preserves _ _ held)
            | (cases Option.some.inj computed
               apply silent_preserves
               apply PettaCallerReturnView.replace_active inputs source current parents control context origins pending
                 (Bridges.ScopedQuerySource.work context origins _) current.collected source.1 source.2.world held scopes frontier
               intro captured work member
               obtain ⟨choice, present, rfl⟩ := List.mem_map.mp member
               exact PettaCallerReturnSourceChoices.captured_frontier inputs control context _ _ _ _ _ _ _ _ _
                 captured (by assumption)
                 (Bridges.ScopedQuerySource.capture_has_source _ _ _ _ _ _ _ _ (by assumption)) choice present)
            | contradiction
            | (split at computed <;> try dsimp only [bind, Option.bind] at computed)

theorem unifying_preserves {User : Type} (inputs : User → Atom) (source : State User)
    (action : Bridges.ScopedQuerySource.Action (Context User))
    (computed : Bridges.ScopedQuerySource.unifyingQueryStep source = some action)
    (held : PettaCallerReturnView.Holds inputs source) : Preserves inputs action := by
  cases scopes : source.2.scopes with
  | nil => exact False.elim (nonempty inputs source held scopes)
  | cons current parents =>
      cases frontier : current.frontier with
      | nil => simp [Bridges.ScopedQuerySource.unifyingQueryStep, scopes, frontier] at computed
      | cons item pending =>
          rcases item with ⟨control, context, origins⟩
          simp only [Bridges.ScopedQuerySource.unifyingQueryStep, scopes, frontier] at computed
          repeat' first
            | (cases Option.some.inj computed
               apply silent_preserves
               apply PettaCallerReturnView.replace_active inputs source current parents control context origins pending
                 [(_, context, origins)] current.collected source.1 source.2.world held scopes frontier
               intro captured work member
               cases List.mem_singleton.mp member
               apply captured.source_step
               · exact .refl _
               · rintro ⟨name, returning⟩
                 exact ⟨name, Bridges.ScopedReturnDispatch.query_ready_to_owned name _ control _ _ _ _ _ returning
                   (by assumption)⟩)
            | contradiction
            | (split at computed <;> try dsimp only [bind, Option.bind] at computed)

theorem base_step_preserves {User : Type} (inputs : User → Atom) (program : SpaceSemantics.Program)
    (source : State User) (valid : EagerDFS.ScopesValid source.2.scopes)
    (noCase : Bridges.ScopedCaseSource.readyStep Bridges.ScopedQuerySource.plainQueryPattern source = none)
    (held : PettaCallerReturnView.Holds inputs source) :
    Preserves inputs (Bridges.ScopedQuerySource.step .eagerValue program source) := by
  unfold Bridges.ScopedQuerySource.step
  repeat' first
    | exact syntax_preserves inputs source _ (by assumption) held
    | exact constrained_preserves inputs source _ (by assumption) held
    | exact mutation_preserves inputs source _ (by assumption) held
    | exact captured_preserves inputs source _ (by assumption) held
    | exact PettaCallerReturnSourceActive.scoped_preserves inputs
        ((Source.scoped_step_iff_source .eagerValue program source valid _).mp rfl)
        (by assumption) (by assumption) noCase held
    | split

theorem owned_step_preserves {User : Type} (inputs : User → Atom) (program : SpaceSemantics.Program)
    (source : State User) (valid : EagerDFS.ScopesValid source.2.scopes)
    (held : PettaCallerReturnView.Holds inputs source) :
    Preserves inputs (Bridges.ScopedQuerySource.ownedStep .eagerValue program source) := by
  unfold Bridges.ScopedQuerySource.ownedStep
  split
  · exact case_entry_preserves inputs source _ (by assumption) held
  · split
    · exact case_ready_preserves inputs source _ (by assumption) held
    · have base := base_step_preserves inputs program source valid (by assumption) held
      split
      · exact ownership_preserves inputs program source _ (by assumption) held
      · dsimp only
        split
        · cases extended : Bridges.ScopedQuerySource.unifyingQueryStep source with
          | none => simpa only [extended, Option.getD_none] using base
          | some action =>
              simpa only [extended, Option.getD_some] using unifying_preserves inputs source action extended held
        · exact base

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCallerReturnOwned
