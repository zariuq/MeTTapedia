import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalPublication
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualAnswerFamilies

/-!
# Conditional rows with different private families share one publication bank

Each private name is tagged by its row index. Captured names retain their
common caller meaning; values and latent equations use the same inclusion.
Unused arities receive fresh formal generators in a declaration extension.
Packing does not conjoin conditions from independent ordinary schemas.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalRowPacking

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualGuardMatching ContextualConditionalRows

variable {S : Signature} {Index Shared Next Future : Type} (Variables : Index → Type)
    (locals : ∀ index, Variables index → MetaArity S) (captures : Shared → MetaArity S)
    {next : Next → MetaArity S} {future : Future → MetaArity S} {Γ : Ctx S} {sort : S.Srt}

abbrev family := ContextualAnswerFamilies.family Variables locals

def inclusion (index : Index) : Assignment (ContextualSelectionViews.source (locals index) captures)
    (ContextualSelectionViews.source (family Variables locals) captures)
  | .inl name => generator (ContextualSelectionViews.source (family Variables locals) captures) (.inl ⟨index, name⟩)
  | .inr name => generator (ContextualSelectionViews.source (family Variables locals) captures) (.inr name)

def value (index : Index) : ContextualStoredRows.Row (locals index) captures Γ sort →
    ContextualStoredRows.Row (family Variables locals) captures Γ sort
  | .schema body => .schema (instantiate (inclusion Variables locals captures index) body)
  | .shared body => .shared body

def pack (index : Index) (row : Row (locals index) captures Γ sort) : Row (family Variables locals) captures Γ sort :=
  ⟨value Variables locals captures index row.value,
    ContextualResidual.mapProblem (inclusion Variables locals captures index) row.obligations⟩

theorem template (index : Index) (row : Row (locals index) captures Γ sort) :
    ContextualStoredRows.asTemplate (family Variables locals) captures (pack Variables locals captures index row).value =
      instantiate (inclusion Variables locals captures index)
        (ContextualStoredRows.asTemplate (locals index) captures row.value) := by
  rcases row with ⟨stored, obligations⟩
  cases stored with
  | schema body => rfl
  | shared body =>
      change instantiate (ContextualSelectionViews.capturedSource (family Variables locals) captures) body =
        instantiate (inclusion Variables locals captures index)
          (instantiate (ContextualSelectionViews.capturedSource (locals index) captures) body)
      rw [← Assignment.instantiate_compose]
      congr 1
      funext name
      exact (instantiate_generator (inclusion Variables locals captures index) (.inr name)).symm

theorem project_assignment (index : Index) (images : Assignment (family Variables locals) future)
    (embedding : Assignment next future) (candidate : Assignment captures next) :
    Assignment.compose (instanceAssignment (family Variables locals) images embedding candidate)
        (inclusion Variables locals captures index) =
      instanceAssignment (locals index) (fun name => images ⟨index, name⟩) embedding candidate := by
  funext name
  cases name <;> exact instantiate_generator _ _

variable [DecidableEq Index]

/-- Every packed row has exactly its own conditional instances under the same caller assignment. -/
theorem matches_iff (index : Index) (row : Row (locals index) captures Γ sort)
    (candidate : Assignment captures next) (pattern : Term (signature S next) Γ sort) :
    Matches (family Variables locals) captures candidate pattern (pack Variables locals captures index row) ↔
      Matches (locals index) captures candidate pattern row := by
  constructor
  · rintro ⟨extension, images, model, same⟩
    refine ⟨extension, (fun name => images ⟨index, name⟩), ?_, ?_⟩
    · have original := (ContextualResidual.models_mapProblem _ _ _).mp model
      rw [project_assignment] at original
      exact original
    · rw [template, ← Assignment.instantiate_compose, project_assignment] at same
      exact same
  · rintro ⟨extension, images, model, same⟩
    let extra := Extension.withLocals (family Variables locals) extension.declarations
    let images' : Assignment (family Variables locals) extra.declarations := fun ⟨origin, name⟩ =>
      if equal : origin = index then by
        subst origin
        exact instantiate extra.assignment (images name)
      else generator extra.declarations (.inl ⟨origin, name⟩)
    have selected : (fun name => images' ⟨index, name⟩) = Assignment.compose extra.assignment images := by
      funext name
      dsimp only [images', Assignment.compose]
      exact if_pos rfl
    have square : Assignment.compose
        (instanceAssignment (family Variables locals) images'
          (Assignment.compose extra.assignment extension.assignment) candidate)
        (inclusion Variables locals captures index) =
        Assignment.compose extra.assignment (instanceAssignment (locals index) images extension.assignment candidate) := by
      rw [project_assignment, selected]
      funext name
      cases name with
      | inl name => rfl
      | inr name =>
          change instantiate (Assignment.compose extra.assignment extension.assignment) (candidate name) =
            instantiate extra.assignment (instantiate extension.assignment (candidate name))
          rw [Assignment.instantiate_compose]
    refine ⟨extension.trans extra, images', ?_, ?_⟩
    · erw [Extension.trans_assignment]
      change ContextualResidual.Models
        (instanceAssignment (family Variables locals) images'
          (Assignment.compose extra.assignment extension.assignment) candidate)
        (ContextualResidual.mapProblem (inclusion Variables locals captures index) row.obligations)
      apply (ContextualResidual.models_mapProblem _ _ _).mpr
      rw [square]
      exact ContextualResidual.models_compose model extra.assignment
    · erw [Extension.trans_assignment]
      change instantiate (instanceAssignment (family Variables locals) images'
          (Assignment.compose extra.assignment extension.assignment) candidate)
          (ContextualStoredRows.asTemplate (family Variables locals) captures (pack Variables locals captures index row).value) =
        instantiate (Assignment.compose extra.assignment extension.assignment) pattern
      rw [template, ← Assignment.instantiate_compose, square, Assignment.instantiate_compose, same,
        Assignment.instantiate_compose]

section RecipeBank

variable {Raw O : Type} (raw : Raw → MetaArity S)

/-- The execution's existing private bank occupies `none`; each declared
output-private family occupies its own `some` block. -/
abbrev WithFallback : Option Index → Type
  | none => Raw
  | some index => Variables index

abbrev fallbackDeclarations : ∀ index, WithFallback Variables (Raw := Raw) index → MetaArity S
  | none => raw
  | some index => locals index

instance fallbackEquality [DecidableEq Raw] [∀ index, DecidableEq (Variables index)]
    (index : Option Index) : DecidableEq (WithFallback Variables (Raw := Raw) index) := by
  cases index <;> dsimp only [WithFallback] <;> infer_instance

/-- A recipe's output-private names enter the output blocks of the bank.
The existing execution-private names are kept separate. -/
def includeRecipe (recipe : ContextualConditionalPublication.Recipe (family Variables locals) captures) :
    ContextualConditionalPublication.Recipe
      (family (WithFallback Variables (Raw := Raw)) (fallbackDeclarations Variables locals raw)) captures :=
  recipe.reindexPrivate _ (fun name => ⟨some name.1, name.2⟩) (fun _ => rfl)

/-- One common publication operation for an independently declared output
bank. Its bodies come from `emitted`; its fallback rows come from the actual
execution. No source-row reconstruction function is an input. -/
def publishWithFallback
    (recipes : O → Option (ContextualConditionalPublication.Recipe (family Variables locals) captures))
    (returned : Assignment captures next)
    (emitted : O → Term (signature S captures) Γ sort)
    (fallback : O → Row raw next Γ sort) (occurrence : O) :
    Row (family (WithFallback Variables (Raw := Raw)) (fallbackDeclarations Variables locals raw)) next Γ sort :=
  match (recipes occurrence).map (includeRecipe Variables locals captures raw) with
  | some recipe => recipe.publish returned (emitted occurrence)
  | none => pack (WithFallback Variables (Raw := Raw)) (fallbackDeclarations Variables locals raw)
      next none (fallback occurrence)

omit [DecidableEq Index] in
theorem publishWithFallback_some
    (recipes : O → Option (ContextualConditionalPublication.Recipe (family Variables locals) captures))
    (returned : Assignment captures next) (emitted : O → Term (signature S captures) Γ sort)
    (fallback : O → Row raw next Γ sort) (occurrence : O)
    (recipe : ContextualConditionalPublication.Recipe (family Variables locals) captures)
    (selected : recipes occurrence = some recipe) :
    publishWithFallback Variables locals captures raw recipes returned emitted fallback occurrence =
      (includeRecipe Variables locals captures raw recipe).publish returned (emitted occurrence) := by
  simp only [publishWithFallback, selected, Option.map_some]

/-- A port without a recipe retains exactly its conditional matching
relation, despite the larger private bank. -/
theorem publishWithFallback_none_matches
    (recipes : O → Option (ContextualConditionalPublication.Recipe (family Variables locals) captures))
    (returned : Assignment captures next) (emitted : O → Term (signature S captures) Γ sort)
    (fallback : O → Row raw next Γ sort) (occurrence : O) (missing : recipes occurrence = none)
    (candidate : Assignment next future) (pattern : Term (signature S future) Γ sort) :
    Matches (family (WithFallback Variables (Raw := Raw)) (fallbackDeclarations Variables locals raw))
        next candidate pattern (publishWithFallback Variables locals captures raw recipes returned emitted fallback occurrence) ↔
      Matches raw next candidate pattern (fallback occurrence) := by
  simp only [publishWithFallback, missing, Option.map_none]
  exact matches_iff (WithFallback Variables (Raw := Raw)) (fallbackDeclarations Variables locals raw)
    next none (fallback occurrence) candidate pattern

end RecipeBank

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalRowPacking
