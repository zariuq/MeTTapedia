import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentGeneralPattern
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentPiSpineScopes
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentScopedDispatch
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentStrengthening

/-!
# Principal replacement for general dependent pattern equations

The newest outer metavariable `F` has a dependent Pi spine over the
remaining outer context. Under a local rigid telescope, the flex equation
`F x̄ ≐ t` has distinct local arguments chosen by a pattern map that fixes
the outer base. When `t` is the image of a body `u` over `F`'s own telescope,
which excludes `F` itself, the equation has exactly the solutions of the
definition `F ≐ λ z̄. u`, at every outer substitution and every future
context. Hence the actual definition update is principal: it is sound, and
every original solution factors through it. No outer metavariable is
renamed, no inhabitant of a local type is chosen, and no new universe join
is needed.

The proof reads the equation through the natural lifted square of the
argument map, reflects typed equality along the reindexed injective
variable inclusion, and closes the spine with its own beta and eta laws.
Raw inversion only supplies the candidate body; failure of raw inversion is
not a refutation, because conversion may erase an out-of-image variable.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentGeneralPattern

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open TypedContextual.QuotientComprehensionSyntax
open ContextualDependentPiSpine ContextualDependentTypedInversion
open ContextualDependentEta ContextualDependentScope

section Generic

variable {Head : Type} {rules : Rules Head}

/-- A typed variable inclusion from exact declaration compatibility. -/
def ofCompatible {source target : Context rules} (rho : Ren source.arity target.arity)
    (injective : Function.Injective rho) (compatible : CtxRen source.raw target.raw rho) :
    Inclusion source target where
  forward := rho
  injective := injective
  typed := by
    intro index
    change Typed rules target.raw (.var (rho index)) (subst (renSub rho) (Ctx.lookup source.raw index))
    rw [subst_renSub, ← compatible index]
    exact .var _

variable {Γ : Context rules} {type : TypeOver Γ}

/-- `F`'s spine read in the context that contains `F`. -/
abbrev lifted (spine : Spine type) : Spine (type.reindex (projectionHom Γ type)) :=
  spine.reindex (projectionHom Γ type)

/-- The defining equation `F ≐ value` for the newest metavariable. -/
def definitionActive (value : Term Γ type) : Active (extend Γ type) :=
  ⟨type.reindex (projectionHom Γ type), newest Γ type, value.reindex (projectionHom Γ type)⟩

theorem definitionActive_equation (value : Term Γ type) :
    (definitionActive value).equation = Elimination.definition Γ value := rfl

/-- Pattern data for `F x̄` under the local telescope `scope`: distinct local
arguments, with exact declaration compatibility of the argument map. -/
structure Pattern (spine : Spine type) {scopeType : TypeOver (extend Γ type)}
    (scope : Spine scopeType) where
  args : spine.Local → scope.Local
  injective : Function.Injective args
  compatible : CtxRen (lifted spine).target.raw scope.target.raw
    (argRen (lifted spine) scope idRen (fun position => args (spine.localReindexEquiv _ position)))

namespace Pattern

variable {spine : Spine type} {scopeType : TypeOver (extend Γ type)} {scope : Spine scopeType}
  (pattern : Pattern spine scope)

def liftedArgs : (lifted spine).Local → scope.Local :=
  fun position => pattern.args (spine.localReindexEquiv _ position)

theorem liftedArgs_injective : Function.Injective pattern.liftedArgs :=
  fun _ _ same => (spine.localReindexEquiv _).injective (pattern.injective same)

/-- The typed argument map; it fixes the outer context, including `F`. -/
def map : Inclusion (lifted spine).target scope.target :=
  inclusion (lifted spine) scope idRen pattern.liftedArgs Function.injective_id
    pattern.liftedArgs_injective pattern.compatible

theorem map_fixes_outer :
    pattern.map.hom ≫ (lifted spine).projection = scope.projection :=
  (fixes_outer (lifted spine) scope idRen pattern.liftedArgs Function.injective_id
    pattern.liftedArgs_injective pattern.compatible (𝟙 _) rfl).trans (Category.comp_id _)

/-- The pattern application `F x̄` in the local telescope. -/
def application : Term scope.target ((lifted spine).result.reindex pattern.map.hom) :=
  ((lifted spine).openFunction (newest Γ type)).reindex pattern.map.hom

/-- The flex equation `F x̄ ≐ right` under the local telescope. -/
def constraint (right : Term scope.target ((lifted spine).result.reindex pattern.map.hom)) :
    Scoped (extend Γ type) :=
  scope.toScoped ⟨_, pattern.application, right⟩

/-- The occurs-checked inversion map, from `F`'s own telescope without `F`. -/
def bodyRen : Ren spine.target.arity scope.target.arity :=
  fun index => pattern.map.forward (spine.mapRen (projectionHom Γ type) wk index)

theorem bodyRen_injective : Function.Injective pattern.bodyRen :=
  pattern.map.injective.comp
    (spine.mapRen_injective (projectionHom Γ type) wk (Fin.succ_injective _))

theorem bodyRen_compatible : CtxRen spine.target.raw scope.target.raw pattern.bodyRen := by
  have composite := CtxRen.comp
    (spine.mapRen_compatible (projectionHom Γ type) wk rfl (CtxRen.wk Γ.raw type.code)) pattern.compatible
  exact composite

def bodyInclusion : Inclusion spine.target scope.target :=
  ofCompatible pattern.bodyRen pattern.bodyRen_injective pattern.bodyRen_compatible

/-- A body over `F`'s own telescope, read in the telescope containing `F`. -/
def liftBody (body : Term spine.target spine.result) : Term (lifted spine).target (lifted spine).result :=
  (body.reindex (spine.map (projectionHom Γ type))).cast (spine.result_reindex (projectionHom Γ type))

theorem liftBody_code (body : Term spine.target spine.result) :
    (liftBody body).code = Presentation.rename (spine.mapRen (projectionHom Γ type) wk) body.code := by
  rw [liftBody, Term.cast_code]
  change subst (spine.map (projectionHom Γ type)).substitution body.code = _
  rw [spine.mapRen_substitution (projectionHom Γ type) wk rfl, subst_renSub]

theorem rename_liftBody (body : Term spine.target spine.result) :
    Presentation.rename pattern.map.forward (liftBody body).code =
      Presentation.rename pattern.bodyRen body.code := by
  rw [liftBody_code, rename_comp]
  rfl

theorem abstract_liftBody (body : Term spine.target spine.result) :
    (lifted spine).abstractBody (liftBody body) = (spine.abstractBody body).reindex (projectionHom Γ type) :=
  (spine.abstractBody_reindex (projectionHom Γ type) body).symm

/-- The argument map read at an outer solution. -/
def reread {Δ : Context rules} (solution : Δ ⟶ extend Γ type) :
    Ren ((lifted spine).reindex solution).target.arity (scope.reindex solution).target.arity :=
  argRen ((lifted spine).reindex solution) (scope.reindex solution) idRen
    (reindexArgs (lifted spine) scope pattern.liftedArgs solution)

theorem reread_injective {Δ : Context rules} (solution : Δ ⟶ extend Γ type) :
    Function.Injective (pattern.reread solution) :=
  argRen_injective Function.injective_id
    (reindexArgs_injective (lifted spine) scope pattern.liftedArgs solution pattern.liftedArgs_injective)

theorem reread_compatible {Δ : Context rules} (solution : Δ ⟶ extend Γ type) :
    CtxRen ((lifted spine).reindex solution).target.raw (scope.reindex solution).target.raw
      (pattern.reread solution) :=
  reindex_compatible (lifted spine) scope pattern.liftedArgs solution pattern.compatible

/-- A body read at an outer solution, in the reindexed telescope of `F`. -/
def candidate (body : Term spine.target spine.result) {Δ : Context rules} (solution : Δ ⟶ extend Γ type) :
    Term ((lifted spine).reindex solution).target ((lifted spine).reindex solution).result :=
  ((liftBody body).reindex ((lifted spine).map solution)).cast ((lifted spine).result_reindex solution)

theorem application_code {Δ : Context rules} (solution : Δ ⟶ extend Γ type) :
    subst (scope.map solution).substitution pattern.application.code =
      Presentation.rename (pattern.reread solution)
        (((lifted spine).reindex solution).openFunction ((newest Γ type).reindex solution)).code := by
  change subst (scope.map solution).substitution
    (subst (renSub pattern.map.forward) ((lifted spine).openFunction (newest Γ type)).code) = _
  rw [subst_renSub]
  exact (subst_map_rename (lifted spine) scope pattern.liftedArgs solution _).trans
    (congrArg (Presentation.rename (pattern.reread solution))
      ((lifted spine).openFunction_reindex_code solution (newest Γ type)))

theorem right_code (body : Term spine.target spine.result)
    (right : Term scope.target ((lifted spine).result.reindex pattern.map.hom))
    (same : right.code = Presentation.rename pattern.bodyRen body.code)
    {Δ : Context rules} (solution : Δ ⟶ extend Γ type) :
    subst (scope.map solution).substitution right.code =
      Presentation.rename (pattern.reread solution) (candidate body solution).code := by
  rw [same, ← pattern.rename_liftBody body, candidate, Term.cast_code]
  exact subst_map_rename (lifted spine) scope pattern.liftedArgs solution (liftBody body).code

theorem annotation_code {Δ : Context rules} (solution : Δ ⟶ extend Γ type) :
    subst (scope.map solution).substitution ((lifted spine).result.reindex pattern.map.hom).code =
      Presentation.rename (pattern.reread solution) ((lifted spine).reindex solution).result.code := by
  change subst (scope.map solution).substitution
    (subst (renSub pattern.map.forward) (lifted spine).result.code) = _
  rw [subst_renSub]
  exact (subst_map_rename (lifted spine) scope pattern.liftedArgs solution _).trans
    (congrArg (fun result => Presentation.rename (pattern.reread solution) (TypeOver.code result))
      ((lifted spine).result_reindex solution))

theorem abstract_candidate (body : Term spine.target spine.result) {Δ : Context rules}
    (solution : Δ ⟶ extend Γ type) :
    ((lifted spine).reindex solution).abstractBody (candidate body solution) =
      ((spine.abstractBody body).reindex (projectionHom Γ type)).reindex solution := by
  rw [← abstract_liftBody body, (lifted spine).abstractBody_reindex solution]
  rfl

end Pattern
end Generic

/-! ## Exact solution correspondence and the principal update -/

section Solutions

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R)
  (heads : HeadPreserving S.R) (algebra : CumulativeAlgebra S.R)
  (reflects : ContextualDependentReductionReflection.RootReflectsInjections S.R.computation)
  (complete : AlgorithmicComplete S.R S.roles)

include facts roots heads algebra reflects complete

namespace Pattern

variable {Γ : Context S.R} {type : TypeOver Γ} {spine : Spine type}
  {scopeType : TypeOver (extend Γ type)} {scope : Spine scopeType} (pattern : Pattern spine scope)

/-- The flex equation and the definition `F ≐ λ z̄. body` have the same
solutions at every outer substitution. -/
theorem holds_iff_definition (body : Term spine.target spine.result)
    (right : Term scope.target ((lifted spine).result.reindex pattern.map.hom))
    (same : right.code = Presentation.rename pattern.bodyRen body.code)
    {Δ : Context S.R} (solution : Δ ⟶ extend Γ type) :
    (pattern.constraint right).Holds solution ↔
      (definitionActive (spine.abstractBody body)).Holds solution := by
  rw [constraint, Spine.toScoped_holds_iff]
  change Equal S.R (scope.reindex solution).target.raw
      (subst (scope.map solution).substitution pattern.application.code)
      (subst (scope.map solution).substitution right.code)
      (subst (scope.map solution).substitution ((lifted spine).result.reindex pattern.map.hom).code) ↔
    Equal S.R Δ.raw ((newest Γ type).reindex solution).code
      (((spine.abstractBody body).reindex (projectionHom Γ type)).reindex solution).code
      ((type.reindex (projectionHom Γ type)).reindex solution).code
  rw [pattern.application_code, pattern.right_code body right same, pattern.annotation_code,
    ← abstract_candidate body solution]
  refine (ContextualDependentStrengthening.equal_iff_renamed facts roots heads algebra reflects complete
    (pattern.reread_injective solution) (pattern.reread_compatible solution)
    ((lifted spine).reindex solution).target.formed (scope.reindex solution).target.formed
    (((lifted spine).reindex solution).openFunction ((newest Γ type).reindex solution)).typed
    (candidate body solution).typed).symm.trans ?_
  exact ((((lifted spine).reindex solution).openFunction_equal_iff ((newest Γ type).reindex solution)
    (((lifted spine).reindex solution).abstractBody (candidate body solution))).trans
    ⟨fun equal => equal.trans (((lifted spine).reindex solution).beta (candidate body solution)),
      fun equal => equal.trans (((lifted spine).reindex solution).beta (candidate body solution)).symm⟩).symm

theorem models_iff_definition (body : Term spine.target spine.result)
    (right : Term scope.target ((lifted spine).result.reindex pattern.map.hom))
    (same : right.code = Presentation.rename pattern.bodyRen body.code)
    {Δ : Context S.R} (solution : Δ ⟶ extend Γ type) :
    (frames S.levels).Models solution [Elimination.definition Γ (spine.abstractBody body)] ↔
      (pattern.constraint right).Holds solution := by
  rw [← definitionActive_equation, ← Active.holds_iff_models]
  exact (pattern.holds_iff_definition facts roots heads algebra reflects complete body right same solution).symm

/-- The principal replacement as an actual scoped solver result. Its closed
store is the definition itself; its update is the existing definition
elimination, with an empty residual. -/
def replace (body : Term spine.target spine.result)
    (right : Term scope.target ((lifted spine).result.reindex pattern.map.hom))
    (same : right.code = Presentation.rename pattern.bodyRen body.code) :
    ContextualDependentScopedDispatch.Result S.levels [pattern.constraint right] :=
  ⟨⟨[Elimination.definition Γ (spine.abstractBody body)], fun solution => by
      rw [pattern.models_iff_definition facts roots heads algebra reflects complete body right same solution]
      simp only [ContextualDependentScopedDispatch.Holds, List.mem_singleton, forall_eq]⟩,
    ContextualDependentUpdate.definition S.levels (spine.abstractBody body) []⟩

theorem replace_finished (body : Term spine.target spine.result)
    (right : Term scope.target ((lifted spine).result.reindex pattern.map.hom))
    (same : right.code = Presentation.rename pattern.bodyRen body.code) :
    (pattern.replace facts roots heads algebra reflects complete body right same).update.remaining = [] := rfl

theorem replace_answer (body : Term spine.target spine.result)
    (right : Term scope.target ((lifted spine).result.reindex pattern.map.hom))
    (same : right.code = Presentation.rename pattern.bodyRen body.code) :
    (pattern.replace facts roots heads algebra reflects complete body right same).update.answer =
      Elimination.instantiate Γ (spine.abstractBody body) := rfl

/-- Soundness of the computed answer, after every later refinement. -/
theorem answer_sound (body : Term spine.target spine.result)
    (right : Term scope.target ((lifted spine).result.reindex pattern.map.hom))
    (same : right.code = Presentation.rename pattern.bodyRen body.code)
    {Δ : Context S.R} (residual : Δ ⟶ Γ) :
    (pattern.constraint right).Holds (residual ≫ Elimination.instantiate Γ (spine.abstractBody body)) :=
  (pattern.replace facts roots heads algebra reflects complete body right same).sound residual
    (Frames.models_nil _) _ (List.mem_singleton_self _)

/-- No solution is lost: every solution of the flex equation, into every
future context, factors through the replacement on all annotated terms. -/
theorem no_solution_lost (body : Term spine.target spine.result)
    (right : Term scope.target ((lifted spine).result.reindex pattern.map.hom))
    (same : right.code = Presentation.rename pattern.bodyRen body.code)
    {Δ : Context S.R} (solution : Δ ⟶ extend Γ type) (solved : (pattern.constraint right).Holds solution) :
    ∃ residual : Δ ⟶ Γ, ∀ term : TotalTerm (extend Γ type),
      (frames S.levels).E (term.reindex solution)
        (term.reindex (residual ≫ Elimination.instantiate Γ (spine.abstractBody body))) := by
  obtain ⟨residual, _, factor⟩ :=
    (pattern.replace facts roots heads algebra reflects complete body right same).factors solution
      (fun constraint member => by
        obtain rfl := List.mem_singleton.mp member
        exact solved)
  exact ⟨residual, factor⟩

/-- Principality in the existing scoped result interface. -/
theorem replace_principal (body : Term spine.target spine.result)
    (right : Term scope.target ((lifted spine).result.reindex pattern.map.hom))
    (same : right.code = Presentation.rename pattern.bodyRen body.code) :
    ContextualDependentScopedDispatch.Holds [pattern.constraint right]
        (pattern.replace facts roots heads algebra reflects complete body right same).update.answer ∧
      ∀ (Δ : Context S.R) (solution : Δ ⟶ extend Γ type),
        ContextualDependentScopedDispatch.Holds [pattern.constraint right] solution →
          ∃ residual : Δ ⟶ (pattern.replace facts roots heads algebra reflects complete body right same).update.target,
            ∀ term : TotalTerm (extend Γ type),
              (frames S.levels).E (term.reindex solution)
                (term.reindex (residual ≫
                  (pattern.replace facts roots heads algebra reflects complete body right same).update.answer)) :=
  (pattern.replace facts roots heads algebra reflects complete body right same).completed rfl

/-- Closed and symbolic solvability stay separate: at each fixed target,
including the empty context, solutions correspond to outer residuals. -/
theorem fixed_point_solutions_iff (body : Term spine.target spine.result)
    (right : Term scope.target ((lifted spine).result.reindex pattern.map.hom))
    (same : right.code = Presentation.rename pattern.bodyRen body.code) (point : Context S.R) :
    (∃ solution : point ⟶ extend Γ type, (pattern.constraint right).Holds solution) ↔
      Nonempty (point ⟶ Γ) := by
  have fixed :=
    (pattern.replace facts roots heads algebra reflects complete body right same).fixed_point_solutions_iff point
  constructor
  · rintro ⟨solution, solved⟩
    obtain ⟨residual, _⟩ := fixed.mp ⟨solution, fun constraint member => by
      obtain rfl := List.mem_singleton.mp member
      exact solved⟩
    exact ⟨residual⟩
  · rintro ⟨residual⟩
    obtain ⟨solution, solved⟩ := fixed.mpr ⟨residual, Frames.models_nil _⟩
    exact ⟨solution, solved _ (List.mem_singleton_self _)⟩

end Pattern
end Solutions

end ContextualDependentGeneralPattern
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
