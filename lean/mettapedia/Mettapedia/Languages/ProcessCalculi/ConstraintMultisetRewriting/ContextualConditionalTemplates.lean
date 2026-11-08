import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualTemplatePublication
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalRows
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalPublication

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

/-- The executable schema recipe is constructed before the solver runs.
Only template-hole declarations become private; actor declarations remain
captures. The output body is supplied by the actual production port. -/
def recipe (scope port : Nat)
    (conditions : ContextualResidual.Problem (Blueprint locals inners captures)) :
    ContextualConditionalPublication.Recipe (Expanded locals inners) (Active locals inners captures) where
  role
    | .inl ⟨_, .inr entry⟩ => .inl (.inr entry)
    | identity => .inr identity
  preserves := by
    intro identity
    cases identity with
    | inl identity => rcases identity with ⟨scope, name⟩; cases name <;> rfl
    | inr identity => rfl
  conditions := ContextualResidual.mapProblem (templateAt locals inners captures scope port) conditions

theorem recipe_square (scope port : Nat)
    (conditions : ContextualResidual.Problem (Blueprint locals inners captures))
    (returned : Assignment (Active locals inners captures) next) :
    Assignment.compose (ContextualStoredRows.liftCaptures (Expanded locals inners) returned)
        (Assignment.compose (recipe locals inners captures scope port conditions).assignment
          (templateAt locals inners captures scope port)) =
      storedBody locals inners captures
        (Assignment.compose returned (actorAt locals inners captures scope)) port := by
  funext identity
  cases identity with
  | inl identity =>
      dsimp only [Assignment.compose]
      erw [templateAt_private, instantiate_generator]
      change instantiate (ContextualStoredRows.liftCaptures (Expanded locals inners) returned)
        (generator _ (.inl (.inr (port, identity)))) = _
      exact instantiate_generator _ _
  | inr identity =>
      cases identity with
      | inl identity =>
          dsimp only [Assignment.compose]
          erw [templateAt_capture, actorAt_local, instantiate_generator]
          change instantiate (ContextualStoredRows.liftCaptures (Expanded locals inners) returned)
            (generator _ (.inr (.inl (Mettapedia.Logic.LP.ScopedVar.at scope (.inl identity))))) = _
          rw [instantiate_generator]
          change instantiate _ (returned _) = instantiate _ (instantiate returned _)
          erw [actorAt_local, instantiate_generator]
      | inr identity =>
          dsimp only [Assignment.compose]
          erw [templateAt_capture, actorAt_shared, instantiate_generator]
          change instantiate (ContextualStoredRows.liftCaptures (Expanded locals inners) returned)
            (generator _ (.inr (.inr identity))) = _
          rw [instantiate_generator]
          change instantiate _ (returned _) = instantiate _ (instantiate returned _)
          erw [actorAt_shared, instantiate_generator]

/-- Both the emitted body and the local equations decode to the authored
conditional template, with exactly its declared captures. -/
theorem recipe_publish (scope port : Nat)
    (conditions : ContextualResidual.Problem (Blueprint locals inners captures))
    (returned : Assignment (Active locals inners captures) next)
    {Γ : Ctx S} {sort : S.Srt}
    (body : Term (signature S (Blueprint locals inners captures)) Γ sort) :
    (recipe locals inners captures scope port conditions).publish returned
        (instantiate (templateAt locals inners captures scope port) body) =
      stored locals inners captures
        (Assignment.compose returned (actorAt locals inners captures scope)) port ⟨.schema body, conditions⟩ := by
  have square := recipe_square locals inners captures scope port conditions returned
  change Row.mk _ _ = Row.mk _ _
  congr 1
  · change ContextualStoredRows.Row.schema (instantiate _ (instantiate _ (instantiate _ body))) =
      ContextualStoredRows.Row.schema (instantiate _ body)
    rw [← Assignment.instantiate_compose, ← Assignment.instantiate_compose]
    rw [← Assignment.compose_associative, square]
  · change ContextualResidual.mapProblem _ (ContextualResidual.mapProblem _
      (ContextualResidual.mapProblem _ conditions)) = ContextualResidual.mapProblem _ conditions
    simp only [ContextualResidual.mapProblem, List.map_map, Function.comp_def]
    apply List.map_congr_left
    intro equation _
    simp only [instantiateObservation_comp]
    rw [square]

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
      exact instance_on_shared_value (Expanded locals inners) images embedding candidate (captureValues identity)

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
