import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualGuardMatching
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFrameUnifier
import Mathlib.Data.List.OfFn

/-!
# Joint contextual source queries with shared local variables

One query assignment is shared by every source port. Every selected read
opens a whole stored schema in its own scope, even when physical identities
repeat. Caller captures enter a later model only by its injective renaming.
The finite joint equation problem uses the existing scoped binding terms.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConjunctiveQueries

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Logic.LP (ScopedVar)
open ContextualGuardMatching

universe u
variable {S : Signature} {Query Local Shared Next Future : Type} {O : Type u}
  (queries : Query → MetaArity S) (locals : Local → MetaArity S)
  (captures : Shared → MetaArity S)

abbrev rowLocals : ScopedVar Local → MetaArity S := fun name => locals name.name
abbrev rowFamily := ContextualSelectionViews.target locals captures
abbrev family := ContextualSelectionViews.source queries (rowFamily locals captures)
abbrev queryFamily := ContextualSelectionViews.source queries captures

def rowEmbedding : Assignment (rowFamily locals captures) (family queries locals captures) :=
  ContextualSelectionViews.capturedSource queries (rowFamily locals captures)

def captureEmbedding : Assignment captures (family queries locals captures) :=
  Assignment.compose (rowEmbedding queries locals captures)
    (ContextualSelectionViews.capturedTarget locals captures)

def queryEmbedding : Assignment (queryFamily queries captures) (family queries locals captures)
  | .inl name => generator (family queries locals captures) (.inl name)
  | .inr name => generator (family queries locals captures) (.inr (.inr name))

def readSelection {count : Nat} (chosen : Fin count → O) : Selection O :=
  ⟨[], List.ofFn chosen, []⟩

def rowScope {count : Nat} (port : Fin count) : Nat := port.val + 2

theorem rowScope_is_the_actual_read_port {count : Nat} (chosen : Fin count → O) (port : Fin count) :
    rowScope port = ContextualActivationScopes.scopeAt ∅
      (ContextualActivationScopes.readPort (readSelection chosen)
        ⟨port.val, by
          change port.val < (List.ofFn chosen).length
          simpa only [List.length_ofFn] using port.isLt⟩) := by
  simp [rowScope, ContextualActivationScopes.scopeAt, ContextualActivationScopes.start,
    ContextualActivationScopes.readPort, readSelection]
  omega

theorem different_ports_have_fresh_row_scopes {count : Nat} :
    Function.Injective (rowScope (count := count)) := by
  intro first second same
  exact Fin.ext (Nat.add_right_cancel same)

def rowView {count : Nat} (port : Fin count) {Γ : Ctx S} {sort : S.Srt}
    (row : ContextualStoredRows.Row locals captures Γ sort) :
    Term (signature S (family queries locals captures)) Γ sort :=
  instantiate (rowEmbedding queries locals captures)
    (ContextualStoredRows.viewAt locals captures (rowScope port) row)

def queryView {Γ : Ctx S} {sort : S.Srt}
    (pattern : Term (signature S (queryFamily queries captures)) Γ sort) :
    Term (signature S (family queries locals captures)) Γ sort :=
  instantiate (queryEmbedding queries locals captures) pattern

variable {next : Next → MetaArity S} {future : Future → MetaArity S}

def combinedAssignment (queryBodies : Assignment queries future)
    (rowBodies : Assignment (rowLocals locals) future)
    (embedding : Assignment next future) (candidate : Assignment captures next) :
    Assignment (family queries locals captures) future
  | .inl name => queryBodies name
  | .inr (.inl name) => rowBodies name
  | .inr (.inr name) => instantiate embedding (candidate name)

theorem combined_fixes_captures (queryBodies : Assignment queries future)
    (rowBodies : Assignment (rowLocals locals) future) (embedding : Assignment next future)
    (candidate : Assignment captures next) (name : Shared) :
    instantiate (combinedAssignment queries locals captures queryBodies rowBodies embedding candidate)
      (captureEmbedding queries locals captures name) = instantiate embedding (candidate name) := by
  change instantiate (combinedAssignment queries locals captures queryBodies rowBodies embedding candidate)
    (instantiate (rowEmbedding queries locals captures)
      (generator (rowFamily locals captures) (.inr name))) = _
  exact (congrArg (instantiate (combinedAssignment queries locals captures queryBodies rowBodies embedding candidate))
    (instantiate_generator (rowEmbedding queries locals captures) (.inr name))).trans
      (instantiate_generator (combinedAssignment queries locals captures queryBodies rowBodies embedding candidate) (.inr (.inr name)))

theorem query_assignment (queryBodies : Assignment queries future)
    (rowBodies : Assignment (rowLocals locals) future) (embedding : Assignment next future)
    (candidate : Assignment captures next) :
    Assignment.compose (combinedAssignment queries locals captures queryBodies rowBodies embedding candidate)
        (queryEmbedding queries locals captures) =
      instanceAssignment queries queryBodies embedding candidate := by
  funext name
  cases name with
  | inl name => exact instantiate_generator (combinedAssignment queries locals captures queryBodies rowBodies embedding candidate) (.inl name)
  | inr name => exact instantiate_generator (combinedAssignment queries locals captures queryBodies rowBodies embedding candidate) (.inr (.inr name))

theorem instantiated_captured_value (queryBodies : Assignment queries future)
    (rowBodies : Assignment (rowLocals locals) future) (embedding : Assignment next future)
    (candidate : Assignment captures next) {Γ : Ctx S} {sort : S.Srt}
    (value : Term (signature S captures) Γ sort) :
    instantiate (combinedAssignment queries locals captures queryBodies rowBodies embedding candidate)
      (instantiate (captureEmbedding queries locals captures) value) =
      instantiate embedding (instantiate candidate value) := by
  rw [instantiate_comp, instantiate_comp]
  congr 1
  funext name
  exact combined_fixes_captures queries locals captures queryBodies rowBodies embedding candidate name

theorem row_assignment (queryBodies : Assignment queries future)
    (rowBodies : Assignment (rowLocals locals) future) (embedding : Assignment next future)
    (candidate : Assignment captures next) (scope : Nat) :
    Assignment.compose (combinedAssignment queries locals captures queryBodies rowBodies embedding candidate)
      (Assignment.compose (rowEmbedding queries locals captures) (ContextualFreshening.assignment locals captures scope)) =
      instanceAssignment locals (fun name => rowBodies (ScopedVar.at scope name)) embedding candidate := by
  funext name
  cases name with
  | inl name =>
      exact (congrArg (instantiate (combinedAssignment queries locals captures queryBodies rowBodies embedding candidate))
        (instantiate_generator (rowEmbedding queries locals captures) (.inl (ScopedVar.at scope name)))).trans
          (instantiate_generator (combinedAssignment queries locals captures queryBodies rowBodies embedding candidate)
            (.inr (.inl (ScopedVar.at scope name))))
  | inr name =>
      exact (congrArg (instantiate (combinedAssignment queries locals captures queryBodies rowBodies embedding candidate))
        (instantiate_generator (rowEmbedding queries locals captures) (.inr name))).trans
          (instantiate_generator (combinedAssignment queries locals captures queryBodies rowBodies embedding candidate) (.inr (.inr name)))

theorem instantiated_row_view (queryBodies : Assignment queries future)
    (rowBodies : Assignment (rowLocals locals) future) (embedding : Assignment next future)
    (candidate : Assignment captures next) {count : Nat} (port : Fin count) {Γ : Ctx S} {sort : S.Srt}
    (row : ContextualStoredRows.Row locals captures Γ sort) :
    instantiate (combinedAssignment queries locals captures queryBodies rowBodies embedding candidate)
        (rowView queries locals captures port row) =
      instantiate (instanceAssignment locals (fun name => rowBodies (ScopedVar.at (rowScope port) name)) embedding candidate)
        (ContextualStoredRows.asTemplate locals captures row) := by
  simp only [rowView, ContextualStoredRows.viewAt_eq_freshening, ContextualFreshening.termAt,
    instantiate_comp]
  exact congrArg (fun assignment => instantiate assignment (ContextualStoredRows.asTemplate locals captures row))
    ((Assignment.compose_associative (ContextualFreshening.assignment locals captures (rowScope port))
      (rowEmbedding queries locals captures) (combinedAssignment queries locals captures queryBodies rowBodies embedding candidate)).symm.trans
        (row_assignment queries locals captures queryBodies rowBodies embedding candidate (rowScope port)))

theorem instantiated_query_view (queryBodies : Assignment queries future)
    (rowBodies : Assignment (rowLocals locals) future) (embedding : Assignment next future)
    (candidate : Assignment captures next) {Γ : Ctx S} {sort : S.Srt}
    (pattern : Term (signature S (queryFamily queries captures)) Γ sort) :
    instantiate (combinedAssignment queries locals captures queryBodies rowBodies embedding candidate)
        (queryView queries locals captures pattern) =
      instantiate (instanceAssignment queries queryBodies embedding candidate) pattern := by
  rw [queryView, instantiate_comp]
  exact congrArg (fun assignment => instantiate assignment pattern)
    (query_assignment queries locals captures queryBodies rowBodies embedding candidate)

def Matches (candidate : Assignment captures next) {Γ : Ctx S} {sort : S.Srt}
    (patterns : List (Term (signature S (queryFamily queries captures)) Γ sort))
    (rows : O → ContextualStoredRows.Row locals captures Γ sort) (chosen : Fin patterns.length → O) : Prop :=
  ∃ extension : Extension next,
    ∃ queryBodies : Assignment queries extension.declarations,
    ∃ rowBodies : Assignment (rowLocals locals) extension.declarations,
      ∀ port : Fin patterns.length,
        instantiate (instanceAssignment locals (fun name => rowBodies (ScopedVar.at (rowScope port) name))
            extension.assignment candidate) (ContextualStoredRows.asTemplate locals captures (rows (chosen port))) =
          instantiate (instanceAssignment queries queryBodies extension.assignment candidate) (patterns.get port)

def joint {Γ : Ctx S} {sort : S.Srt}
    (problem : EquationStore (Term (signature S captures) Γ sort))
    (patterns : List (Term (signature S (queryFamily queries captures)) Γ sort))
    (rows : O → ContextualStoredRows.Row locals captures Γ sort) (chosen : Fin patterns.length → O) :
    EquationStore (Term (signature S (family queries locals captures)) Γ sort) :=
  ContextualFrameUnifier.mapProblem (captureEmbedding queries locals captures) problem ++
    List.ofFn (fun port => (rowView queries locals captures port (rows (chosen port)),
      queryView queries locals captures (patterns.get port)))

theorem match_gives_joint_model (candidate : Assignment captures next) {Γ : Ctx S} {sort : S.Srt}
    (problem : EquationStore (Term (signature S captures) Γ sort))
    (patterns : List (Term (signature S (queryFamily queries captures)) Γ sort))
    (rows : O → ContextualStoredRows.Row locals captures Γ sort) (chosen : Fin patterns.length → O)
    (solved : ContextualFrameUnifier.Models candidate problem)
    (matched : Matches queries locals captures candidate patterns rows chosen) :
    ∃ (Later : Type) (later : Later → MetaArity S)
      (combined : Assignment (family queries locals captures) later),
        ContextualFrameUnifier.Models combined (joint queries locals captures problem patterns rows chosen) := by
  obtain ⟨extension, queryBodies, rowBodies, agrees⟩ := matched
  let combined := combinedAssignment queries locals captures queryBodies rowBodies extension.assignment candidate
  refine ⟨extension.Names, extension.declarations, combined, ?_⟩
  apply (ContextualFrameUnifier.models_append _ _ _).mpr
  constructor
  · intro equation member
    obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
    exact (instantiated_captured_value queries locals captures queryBodies rowBodies extension.assignment candidate original.1).trans
      ((congrArg (instantiate extension.assignment) (solved original present)).trans
        (instantiated_captured_value queries locals captures queryBodies rowBodies extension.assignment candidate original.2).symm)
  · intro equation member
    obtain ⟨port, rfl⟩ := List.mem_ofFn.mp member
    exact (instantiated_row_view queries locals captures queryBodies rowBodies extension.assignment candidate port (rows (chosen port))).trans
      ((agrees port).trans (instantiated_query_view queries locals captures queryBodies rowBodies extension.assignment candidate (patterns.get port)).symm)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConjunctiveQueries
