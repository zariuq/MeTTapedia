import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentPiSpineOrigins

/-!
# Pattern argument maps over a fixed outer context

A pattern application `F x₁ … xₙ` under a local rigid telescope is read from
an assignment of local telescope variables to the binders of `F`'s dependent
Pi spine. Outer variables follow a supplied outer renaming; they are never
captured by the local telescope. The induced variable map is injective
exactly when the assignment and the outer renaming are, its inverse is the
computed finite lookup on its image, and its typed map commutes with the
projections to the outer context.

The map is natural in every outer substitution: lifting a solution through
the local telescope and then reading the arguments equals reading the
reindexed arguments and then lifting through `F`'s spine. Exact declaration
compatibility is transported along the same square. The square is a
property of the actual lifted substitutions; no typed renaming of captured
outer metavariables is used.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentGeneralPattern

open CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open TypedContextual.QuotientComprehensionSyntax
open ContextualDependentPiSpine ContextualDependentTypedInversion

variable {Head : Type} {rules : Rules Head}

/-- The variable map of a pattern spine. The outer variable `prior` of the
function's context is read through `outer`; the binder `position` of the
function's spine is read as the local variable `args position`. -/
def argRen {Γ Δ : Context rules} {type : TypeOver Γ} {scopeType : TypeOver Δ}
    (spine : Spine type) (scope : Spine scopeType) (outer : Ren Γ.arity Δ.arity)
    (args : spine.Local → scope.Local) : Ren spine.target.arity scope.target.arity :=
  fun index => Sum.elim (fun prior => scope.outerRen (outer prior))
    (fun position => scope.localIndex (args position)) (spine.originEquiv.symm index)

section Map

variable {Γ Δ : Context rules} {type : TypeOver Γ} {scopeType : TypeOver Δ}
  (spine : Spine type) (scope : Spine scopeType) (outer : Ren Γ.arity Δ.arity)
  (args : spine.Local → scope.Local)

theorem argRen_outer (prior : Fin Γ.arity) :
    argRen spine scope outer args (spine.outerRen prior) = scope.outerRen (outer prior) := by
  unfold argRen
  rw [← spine.outer_origin, Equiv.symm_apply_apply]
  rfl

theorem argRen_local (position : spine.Local) :
    argRen spine scope outer args (spine.localIndex position) = scope.localIndex (args position) := by
  unfold argRen Spine.localIndex
  rw [Equiv.symm_apply_apply]
  rfl

variable {spine scope outer args} in
theorem argRen_injective (outerInjective : Function.Injective outer)
    (argsInjective : Function.Injective args) :
    Function.Injective (argRen spine scope outer args) := by
  intro first second same
  apply spine.originEquiv.symm.injective
  unfold argRen at same
  generalize spine.originEquiv.symm first = one at same ⊢
  generalize spine.originEquiv.symm second = two at same ⊢
  rcases one with one | one <;> rcases two with two | two <;>
    simp only [Sum.elim_inl, Sum.elim_inr] at same
  · exact congrArg Sum.inl (outerInjective (scope.outerRen_injective same))
  · exact (scope.outer_ne_local _ _ same).elim
  · exact (scope.outer_ne_local _ _ same.symm).elim
  · exact congrArg Sum.inr (argsInjective (scope.localIndex_injective same))

/-- A local variable is hit exactly when it is one of the supplied arguments. -/
theorem local_mem_range_iff (target : scope.Local) :
    (∃ index, argRen spine scope outer args index = scope.localIndex target) ↔
      ∃ position, args position = target := by
  constructor
  · rintro ⟨index, hit⟩
    rcases spine.variable_cases index with ⟨prior, rfl⟩ | ⟨position, rfl⟩
    · rw [argRen_outer] at hit
      exact (scope.outer_ne_local _ _ hit).elim
    · rw [argRen_local] at hit
      exact ⟨position, scope.localIndex_injective hit⟩
  · rintro ⟨position, rfl⟩
    exact ⟨spine.localIndex position, argRen_local spine scope outer args position⟩

variable {spine scope outer args} in
/-- The computed partial inverse is exact on the image of an injective
argument map: it returns the unique preimage there and nothing elsewhere. -/
theorem inverse_exact (outerInjective : Function.Injective outer)
    (argsInjective : Function.Injective args) :
    ContextualDependentInversion.Exact (argRen spine scope outer args)
      (ContextualDependentInversion.lookup (argRen spine scope outer args)) :=
  ContextualDependentInversion.lookup_exact _ (argRen_injective outerInjective argsInjective)

variable {spine scope outer args} in
/-- Raw inversion of a term through an injective argument map succeeds
exactly on renamed images, and then returns the unique preimage. -/
theorem invert_eq_some_iff (outerInjective : Function.Injective outer)
    (argsInjective : Function.Injective args) (term : Tm Head scope.target.arity)
    (body : Tm Head spine.target.arity) :
    ContextualDependentInversion.invert (ContextualDependentInversion.lookup (argRen spine scope outer args)) term =
        some body ↔ Presentation.rename (argRen spine scope outer args) body = term :=
  ContextualDependentInversion.invert_eq_some_iff _ _ (inverse_exact outerInjective argsInjective) term body

/-- Exact declaration compatibility makes the argument map a typed variable
inclusion. Its typing is the native variable rule; no conversion is used. -/
def inclusion (outerInjective : Function.Injective outer) (argsInjective : Function.Injective args)
    (compatible : CtxRen spine.target.raw scope.target.raw (argRen spine scope outer args)) :
    Inclusion spine.target scope.target where
  forward := argRen spine scope outer args
  injective := argRen_injective outerInjective argsInjective
  typed := by
    intro index
    change Typed rules scope.target.raw (.var (argRen spine scope outer args index))
      (subst (renSub (argRen spine scope outer args)) (Ctx.lookup spine.target.raw index))
    rw [subst_renSub, ← compatible index]
    exact .var _

/-- The argument map fixes the outer base: projecting the arguments to the
function's outer context is the scope's projection followed by the outer
renaming. -/
theorem fixes_outer (outerInjective : Function.Injective outer) (argsInjective : Function.Injective args)
    (compatible : CtxRen spine.target.raw scope.target.raw (argRen spine scope outer args))
    (base : Δ ⟶ Γ) (baseVariables : base.substitution = renSub outer) :
    (inclusion spine scope outer args outerInjective argsInjective compatible).hom ≫ spine.projection =
      scope.projection ≫ base := by
  apply Hom.ext
  funext index
  change subst (renSub (argRen spine scope outer args)) (spine.projection.substitution index) =
    subst scope.projection.substitution (base.substitution index)
  rw [spine.projection_substitution, scope.projection_substitution, baseVariables]
  exact congrArg Tm.var (argRen_outer spine scope outer args index)

end Map

section Natural

variable {Γ : Context rules} {type scopeType : TypeOver Γ}
  (spine : Spine type) (scope : Spine scopeType) (args : spine.Local → scope.Local)

/-- The same argument assignment after reindexing both telescopes. -/
def reindexArgs {Δ : Context rules} (base : Δ ⟶ Γ) :
    (spine.reindex base).Local → (scope.reindex base).Local :=
  fun position => (scope.localReindexEquiv base).symm (args (spine.localReindexEquiv base position))

theorem reindexArgs_injective {Δ : Context rules} (base : Δ ⟶ Γ) (argsInjective : Function.Injective args) :
    Function.Injective (reindexArgs spine scope args base) := by
  intro first second same
  exact (spine.localReindexEquiv base).injective
    (argsInjective ((scope.localReindexEquiv base).symm.injective same))

/-- Naturality on variables: the actual lifted outer substitution commutes
with reading pattern arguments. Outer variables follow the substitution and
local arguments stay rigid. -/
theorem map_argRen {Δ : Context rules} (base : Δ ⟶ Γ) (index : Fin spine.target.arity) :
    (scope.map base).substitution (argRen spine scope idRen args index) =
      Presentation.rename (argRen (spine.reindex base) (scope.reindex base) idRen (reindexArgs spine scope args base))
        ((spine.map base).substitution index) := by
  rcases spine.variable_cases index with ⟨prior, rfl⟩ | ⟨position, rfl⟩
  · rw [argRen_outer, scope.map_outer, spine.map_outer, rename_comp]
    exact rename_ext (fun other =>
      (argRen_outer (spine.reindex base) (scope.reindex base) idRen (reindexArgs spine scope args base) other).symm) _
  · obtain ⟨position, rfl⟩ := (spine.localReindexEquiv base).surjective position
    rw [argRen_local, spine.map_local]
    have lifted := scope.map_local base
      ((scope.localReindexEquiv base).symm (args (spine.localReindexEquiv base position)))
    rw [Equiv.apply_symm_apply] at lifted
    rw [lifted]
    exact congrArg Tm.var
      (argRen_local (spine.reindex base) (scope.reindex base) idRen (reindexArgs spine scope args base) position).symm

/-- Naturality on terms. -/
theorem subst_map_rename {Δ : Context rules} (base : Δ ⟶ Γ) (term : Tm Head spine.target.arity) :
    subst (scope.map base).substitution (Presentation.rename (argRen spine scope idRen args) term) =
      Presentation.rename (argRen (spine.reindex base) (scope.reindex base) idRen (reindexArgs spine scope args base))
        (subst (spine.map base).substitution term) := by
  rw [subst_rename, rename_subst]
  exact subst_ext (map_argRen spine scope args base) term

/-- Exact declaration compatibility survives every outer substitution. The
local case uses the dependent lookup laws of both reindexed telescopes. -/
theorem reindex_compatible {Δ : Context rules} (base : Δ ⟶ Γ)
    (compatible : CtxRen spine.target.raw scope.target.raw (argRen spine scope idRen args)) :
    CtxRen (spine.reindex base).target.raw (scope.reindex base).target.raw
      (argRen (spine.reindex base) (scope.reindex base) idRen (reindexArgs spine scope args base)) := by
  intro index
  rcases (spine.reindex base).variable_cases index with ⟨prior, rfl⟩ | ⟨position, rfl⟩
  · rw [argRen_outer, (scope.reindex base).outerRen_compatible, (spine.reindex base).outerRen_compatible,
      rename_comp]
    exact rename_ext (fun other =>
      (argRen_outer (spine.reindex base) (scope.reindex base) idRen (reindexArgs spine scope args base) other).symm) _
  · rw [argRen_local, scope.local_lookup_reindex base, spine.local_lookup_reindex base]
    have returned : scope.localReindexEquiv base (reindexArgs spine scope args base position) =
        args (spine.localReindexEquiv base position) := Equiv.apply_symm_apply _ _
    rw [returned, ← argRen_local spine scope idRen args, compatible, subst_map_rename]

/-- The reindexed argument map is again a typed inclusion. -/
def reindexInclusion {Δ : Context rules} (base : Δ ⟶ Γ) (argsInjective : Function.Injective args)
    (compatible : CtxRen spine.target.raw scope.target.raw (argRen spine scope idRen args)) :
    Inclusion (spine.reindex base).target (scope.reindex base).target :=
  inclusion (spine.reindex base) (scope.reindex base) idRen (reindexArgs spine scope args base)
    Function.injective_id (reindexArgs_injective spine scope args base argsInjective)
    (reindex_compatible spine scope args base compatible)

/-- Naturality of typed maps: the lifted scope substitution followed by the
argument map equals the reindexed argument map followed by the lifted
function-spine substitution. -/
theorem lift_square {Δ : Context rules} (base : Δ ⟶ Γ) (argsInjective : Function.Injective args)
    (compatible : CtxRen spine.target.raw scope.target.raw (argRen spine scope idRen args)) :
    scope.map base ≫ (inclusion spine scope idRen args Function.injective_id argsInjective compatible).hom =
      (reindexInclusion spine scope args base argsInjective compatible).hom ≫ spine.map base := by
  apply Hom.ext
  funext index
  change (scope.map base).substitution (argRen spine scope idRen args index) =
    subst (renSub (argRen (spine.reindex base) (scope.reindex base) idRen (reindexArgs spine scope args base)))
      ((spine.map base).substitution index)
  rw [subst_renSub]
  exact map_argRen spine scope args base index

end Natural

end ContextualDependentGeneralPattern
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
