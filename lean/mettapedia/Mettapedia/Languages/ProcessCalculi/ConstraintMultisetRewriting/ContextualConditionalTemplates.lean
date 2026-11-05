import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualTemplatePublication
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalRows

/-!
# Constructed conditional templates keep private holes and public captures

The existing template binding map transports both the value and its latent
equations. A later read opens the private holes afresh and keeps the
declared actor captures. Conditions remain in their row; storing the row
does not assert them in the caller's global information problem.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalTemplates

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualTemplateSource ContextualConditionalRows ContextualGuardMatching

variable {S : Signature} {Local Inner Shared Names Future Model : Type}
    (locals : Local → MetaArity S) (inners : Inner → MetaArity S) (captures : Shared → MetaArity S)
    {next : Names → MetaArity S} {future : Future → MetaArity S} {model : Model → MetaArity S}

def stored (captureValues : Assignment (Actor locals captures) next) (port : Nat)
    {Γ : Ctx S} {sort : S.Srt} (source : Row inners (Actor locals captures) Γ sort) :
    Row (Expanded locals inners) next Γ sort :=
  ⟨ContextualTemplateSource.stored locals inners captures captureValues port
      (ContextualStoredRows.asTemplate inners (Actor locals captures) source.value),
    ContextualResidual.mapProblem (storedBody locals inners captures captureValues port) source.obligations⟩

theorem stored_valuation (captureValues : Assignment (Actor locals captures) next) (port : Nat)
    (images : Assignment (Expanded locals inners) model) (embedding : Assignment future model)
    (candidate : Assignment next future) :
    Assignment.compose (instanceAssignment (Expanded locals inners) images embedding candidate)
        (storedBody locals inners captures captureValues port) =
      instanceAssignment inners (fun identity => images (.inr (port, identity))) embedding
        (Assignment.compose candidate captureValues) := by
  funext identity
  cases identity with
  | inl identity => exact instantiate_generator _ _
  | inr identity =>
      exact instance_on_live_value (Expanded locals inners) images embedding candidate (captureValues identity)

theorem stored_models (captureValues : Assignment (Actor locals captures) next) (port : Nat)
    (images : Assignment (Expanded locals inners) model) (embedding : Assignment future model)
    (candidate : Assignment next future) (conditions : ContextualResidual.Problem (Blueprint locals inners captures)) :
    ContextualResidual.Models (instanceAssignment (Expanded locals inners) images embedding candidate)
        (ContextualResidual.mapProblem (storedBody locals inners captures captureValues port) conditions) ↔
      ContextualResidual.Models
        (instanceAssignment inners (fun identity => images (.inr (port, identity))) embedding
          (Assignment.compose candidate captureValues)) conditions := by
  rw [ContextualResidual.models_mapProblem, stored_valuation]

/-- The stored row preserves its entire conditional instance relation,
including correlations with captured actor variables. -/
theorem stored_matches_iff (captureValues : Assignment (Actor locals captures) next) (port : Nat)
    (candidate : Assignment next future) {Γ : Ctx S} {sort : S.Srt}
    (source : Row inners (Actor locals captures) Γ sort) (pattern : Term (signature S future) Γ sort) :
    Matches (Expanded locals inners) next candidate pattern (stored locals inners captures captureValues port source) ↔
      Matches inners (Actor locals captures) (Assignment.compose candidate captureValues) pattern source := by
  constructor
  · rintro ⟨extension, images, conditions, same⟩
    refine ⟨extension, (fun identity => images (.inr (port, identity))), ?_, ?_⟩
    · exact (stored_models locals inners captures captureValues port images extension.assignment candidate source.obligations).mp conditions
    · change instantiate (instanceAssignment (Expanded locals inners) images extension.assignment candidate)
        (instantiate (storedBody locals inners captures captureValues port)
          (ContextualStoredRows.asTemplate inners (Actor locals captures) source.value)) = _ at same
      rwa [← Assignment.instantiate_compose, stored_valuation] at same
  · rintro ⟨extension, images, conditions, same⟩
    let added := Extension.withLocals (Expanded locals inners) extension.declarations
    let images' : Assignment (Expanded locals inners) added.declarations
      | .inl identity => generator added.declarations (.inl (.inl identity))
      | .inr (origin, identity) => if origin = port then instantiate added.assignment (images identity)
          else generator added.declarations (.inl (.inr (origin, identity)))
    have assignments :
        Assignment.compose added.assignment
            (instanceAssignment inners images extension.assignment (Assignment.compose candidate captureValues)) =
          instanceAssignment inners (fun identity => images' (.inr (port, identity)))
            (Assignment.compose added.assignment extension.assignment) (Assignment.compose candidate captureValues) := by
      funext identity
      cases identity with
      | inl identity =>
          change instantiate added.assignment (images identity) =
            if port = port then instantiate added.assignment (images identity)
              else generator added.declarations (.inl (.inr (port, identity)))
          exact (if_pos rfl).symm
      | inr identity => exact (Assignment.instantiate_compose added.assignment extension.assignment
          ((Assignment.compose candidate captureValues) identity)).symm
    refine ⟨extension.trans added, images', ?_, ?_⟩
    · apply (stored_models locals inners captures captureValues port images' (extension.trans added).assignment candidate source.obligations).mpr
      rw [Extension.trans_assignment, ← assignments]
      exact ContextualResidual.models_compose conditions added.assignment
    · change instantiate (instanceAssignment (Expanded locals inners) images' (extension.trans added).assignment candidate)
        (instantiate (storedBody locals inners captures captureValues port)
          (ContextualStoredRows.asTemplate inners (Actor locals captures) source.value)) = _
      erw [← Assignment.instantiate_compose, stored_valuation, Extension.trans_assignment, ← assignments,
        Assignment.instantiate_compose, Assignment.instantiate_compose]
      exact congrArg (instantiate added.assignment) same

theorem empty_conditions (captureValues : Assignment (Actor locals captures) next) (port : Nat)
    {Γ : Ctx S} {sort : S.Srt} (body : Term (signature S (Blueprint locals inners captures)) Γ sort) :
    stored locals inners captures captureValues port ⟨.schema body, []⟩ =
      ofStored (Expanded locals inners) next (ContextualTemplateSource.stored locals inners captures captureValues port body) := rfl

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalTemplates
