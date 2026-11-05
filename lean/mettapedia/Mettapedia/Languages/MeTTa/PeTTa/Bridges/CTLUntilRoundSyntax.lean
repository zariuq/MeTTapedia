import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilScopedRound
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedClosedEquationSource

/-!
# Freshened syntax of the authored EU round

The canonical round is the counted three-query source, with four formal
operands and three source-local names. The query descriptor's result name is
not part of this syntax: the collapse machine supplies its actual destination.
All handles are retained, including distinct source and publication spaces.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilRoundSyntax

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open EagerDFS.Destination
open HE.Spec.Type.RuntimeRefinement (renameTypeVars)
open HE.Spec.Type.Presentation (TypeSubst)
open CTLUntilScopedRound (Query)
open ClosedOnceQueryFrame (FreshFor)

def queryBody (query : Query) : Atom :=
  ScopedNestedQueryExecution.source query.legs query.template.source

def body (query : Query) : Atom :=
  .expression [.symbol "size-atom", .expression [.symbol "collapse", queryBody query]]

def formals (query : Query) : List String :=
  [query.names.formula, query.operand, query.currentRound, query.names.nextRound]

def locals (query : Query) : List String :=
  [query.names.next, query.names.prior, query.names.temporary]

def sourceNames (query : Query) : List String := formals query ++ locals query

/-- Rename only names actually present in the authored source. -/
def renamed (query : Query) (rename : String → String) : Query :=
  {query with
    names := {query.names with
      formula := rename query.names.formula
      nextRound := rename query.names.nextRound
      next := rename query.names.next
      prior := rename query.names.prior
      temporary := rename query.names.temporary}
    operand := rename query.operand
    currentRound := rename query.currentRound}

theorem result_metadata_unchanged (query : Query) (rename : String → String) :
    (renamed query rename).names.result = query.names.result := rfl

theorem body_ignores_result (query : Query) (result : String) :
    body {query with names := {query.names with result}} = body query := rfl

private theorem handle_renamed (handle : NamedSpaces.Handle) (rename : String → String) :
    renameTypeVars rename (Effects.handleValue handle) = Effects.handleValue handle := by
  cases handle <;> simp [Effects.handleValue, renameTypeVars]

private theorem handle_names (handle : NamedSpaces.Handle) : TypeSubst.typeVars (Effects.handleValue handle) = [] := by
  cases handle <;> simp [Effects.handleValue, TypeSubst.typeVars]

theorem queryBody_renamed (query : Query) (rename : String → String) :
    renameTypeVars rename (queryBody query) = queryBody (renamed query rename) := by
  simp [queryBody, Query.legs, Query.frontier, Query.edge, Query.satisfaction, Query.template,
    ScopedNestedQueryExecution.source, ScopedMatchPreparation.source, GuardedNestedQuerySource.Template.source,
    ScopedCallOperands.source, NamedGuardedInsertionSource.empty, ScopedInsertionSequence.source,
    ScopedInsertionSource.source, CTLUntilScopedCapture.frontierCode, CTLUntilSourceRows.reversePattern,
    NamedPresenceSource.patternCode, CTLUntilCandidateAdmission.satisfactionCode,
    CTLUntilCandidateAdmission.frontierCode, renamed, renameTypeVars, handle_renamed]

theorem body_renamed (query : Query) (rename : String → String) :
    renameTypeVars rename (body query) = body (renamed query rename) := by
  simp only [body, renameTypeVars, List.map_cons, List.map_nil, queryBody_renamed]

theorem body_names (query : Query) (name : String) :
    name ∈ TypeSubst.typeVars (body query) ↔ name ∈ sourceNames query := by
  simp only [body, queryBody, Query.legs, Query.frontier, Query.edge, Query.satisfaction, Query.template,
    ScopedNestedQueryExecution.source, ScopedMatchPreparation.source, GuardedNestedQuerySource.Template.source,
    ScopedCallOperands.source, NamedGuardedInsertionSource.empty, ScopedInsertionSequence.source,
    ScopedInsertionSource.source, CTLUntilScopedCapture.frontierCode, CTLUntilSourceRows.reversePattern,
    NamedPresenceSource.patternCode, CTLUntilCandidateAdmission.satisfactionCode,
    CTLUntilCandidateAdmission.frontierCode, TypeSubst.typeVars, TypeSubst.typeVarsList,
    handle_names, sourceNames, formals, locals, List.nil_append, List.cons_append,
    List.mem_cons, List.not_mem_nil, or_false]
  tauto

theorem next_in_body (query : Query) : query.names.next ∈ TypeSubst.typeVars (body query) :=
  (body_names query _).mpr (by simp [sourceNames, locals])

theorem prior_in_body (query : Query) : query.names.prior ∈ TypeSubst.typeVars (body query) :=
  (body_names query _).mpr (by simp [sourceNames, locals])

theorem temporary_in_body (query : Query) : query.names.temporary ∈ TypeSubst.typeVars (body query) :=
  (body_names query _).mpr (by simp [sourceNames, locals])

def definition (query : Query) (distinct : (formals query).Nodup) : ScopedClosedEquationSource.Definition :=
  ⟨"eu-round", formals query, body query, distinct⟩

def freshQuery (control : Control) (occurrence : Nat) (query : Query) (distinct : (formals query).Nodup) : Query :=
  renamed query (ScopedClosedEquationSource.formal control occurrence (definition query distinct))

theorem fresh_body (control : Control) (occurrence : Nat) (query : Query) (distinct : (formals query).Nodup) :
    ClauseChoice.freshBody control occurrence (definition query distinct).declaration =
      body (freshQuery control occurrence query distinct) := by
  exact body_renamed query _

theorem fresh_formals (control : Control) (occurrence : Nat) (query : Query) (distinct : (formals query).Nodup) :
    formals (freshQuery control occurrence query distinct) =
      ScopedClosedEquationSource.formalNames control occurrence (definition query distinct) := rfl

theorem handles_retained (query : Query) (rename : String → String) :
    (renamed query rename).handles = query.handles := rfl

theorem formals_distinct (query : Query) (distinct : (sourceNames query).Nodup) : (formals query).Nodup :=
  (List.nodup_append.mp distinct).1

theorem local_not_formal (query : Query) (distinct : (sourceNames query).Nodup)
    (name : String) (member : name ∈ locals query) : name ∉ formals query := by
  have apart := (List.nodup_append.mp distinct).2.2
  intro present
  exact apart name present name member rfl

theorem fresh_locals_distinct (control : Control) (occurrence : Nat) (query : Query)
    (distinct : (sourceNames query).Nodup) :
    (locals (freshQuery control occurrence query (formals_distinct query distinct))).Nodup := by
  have localDistinct := (List.nodup_append.mp distinct).2.1
  change ((locals query).map (ScopedClosedEquationSource.formal control occurrence
    (definition query (formals_distinct query distinct)))).Nodup
  apply localDistinct.map_on
  intro first firstMember second secondMember same
  apply ClauseChoice.rename_injective_on control occurrence _ ?_ ?_ same
  · rw [ScopedClosedEquationSource.clause_names]
    apply List.mem_append_right
    exact (body_names query first).mpr (List.mem_append_right _ firstMember)
  · rw [ScopedClosedEquationSource.clause_names]
    apply List.mem_append_right
    exact (body_names query second).mpr (List.mem_append_right _ secondMember)

theorem selected_local_fresh (control : Control) (occurrence : Nat) (query : Query)
    (distinct : (sourceNames query).Nodup) (values : List Atom) (destination : Atom) (older : List Goal)
    (name : String) (member : name ∈ locals query)
    (closed : ∀ value ∈ values, ∀ environment, read environment value = value) :
    FreshFor (ScopedClosedEquationSource.formal control occurrence
      (definition query (formals_distinct query distinct)) name)
      (ScopedClosedEquationSource.selected control occurrence (definition query (formals_distinct query distinct))
        values destination older).bindings := by
  apply ScopedClosedEquationSource.local_fresh
  · exact (body_names query name).mpr (List.mem_append_right _ member)
  · exact local_not_formal query distinct name member
  · exact closed

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilRoundSyntax
