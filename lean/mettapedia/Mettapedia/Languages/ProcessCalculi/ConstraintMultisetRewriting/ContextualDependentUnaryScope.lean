import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentScopeConsequence
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentFlex

/-!
# Two independent arguments force a normal body out of their scope

If a typed normal body gives equal results when its parameter is sent to
either of two fresh variables, the parameter is absent from its support.
Weakening inversion therefore succeeds and recovers the body in the outer
context. That context and the expected codomain need not be normal or have
closed inhabitants.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentUnaryScope

open CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentNormalChecking ContextualDependentScopeConsequence ContextualDependentTypedInversion

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

def twice (Γ : Context S.R) (domain : TypeOver Γ) : Context S.R :=
  extend (extend Γ domain) (domain.reindex (projectionHom Γ domain))

theorem left_compatible (Γ : Context S.R) (domain : TypeOver Γ) :
    CtxRen (extend Γ domain).raw (twice Γ domain).raw wk := CtxRen.wk _ _

theorem right_compatible (Γ : Context S.R) (domain : TypeOver Γ) :
    CtxRen (extend Γ domain).raw (twice Γ domain).raw (liftRen wk) := by
  have lifted := (CtxRen.wk Γ.raw domain.code).snoc domain.code
  change CtxRen (.snoc Γ.raw domain.code) (.snoc (.snoc Γ.raw domain.code) (subst projection domain.code)) (liftRen wk)
  rw [subst_projection]
  exact lifted

theorem codomain_images (Γ : Context S.R) (domain codomain : TypeOver Γ) :
    Presentation.rename (liftRen wk) (codomain.reindex (projectionHom Γ domain)).code =
      Presentation.rename wk (codomain.reindex (projectionHom Γ domain)).code := by
  change Presentation.rename (liftRen wk) (subst projection codomain.code) =
    Presentation.rename wk (subst projection codomain.code)
  rw [subst_projection, rename_comp, rename_comp]
  rfl

variable (rigid : ∀ name, S.roles name = .rigid) (complete : AlgorithmicComplete S.R S.roles)

include rigid complete in
theorem inverse_forced (Γ : Context S.R) (domain codomain : TypeOver Γ)
    (value : Term (extend Γ domain) (codomain.reindex (projectionHom Γ domain)))
    (normal : Normal (S := S) value.code)
    (same : Equal S.R (twice Γ domain).raw (Presentation.rename wk value.code)
      (Presentation.rename (liftRen wk) value.code)
      (Presentation.rename wk (codomain.reindex (projectionHom Γ domain)).code)) :
    (ContextualDependentInversion.invert (ContextualDependentInversion.lookup (wk : Ren Γ.arity (Γ.arity + 1)))
      value.code).isSome = true := by
  apply (ContextualDependentSupport.invert_lookup_defined_iff wk (Fin.succ_injective _) value.code).mpr
  have common := common_parameters_forced rigid complete wk (liftRen wk) (twice Γ domain).formed
    value.code value.code _ same normal normal
  intro index present
  revert present
  refine Fin.cases ?_ (fun prior => ?_) index
  · intro present
    obtain ⟨other, impossible⟩ := (commonMask_iff wk (liftRen wk) 0).mp (common 0 present)
    exact False.elim (Fin.succ_ne_zero other impossible)
  · intro _
    exact ⟨prior, rfl⟩

variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R)
  (heads : HeadPreserving S.R) (algebra : CumulativeAlgebra S.R)
  (headTypingUnique : ∀ {head first second : Head},
    S.R.headTyping head first → S.R.headTyping head second → first = second)
  (declared : DeclaredTypesFormed S.R)

include rigid complete facts roots heads algebra headTypingUnique declared in
theorem recovery_succeeds (Γ : Context S.R) (domain codomain : TypeOver Γ)
    (value : Term (extend Γ domain) (codomain.reindex (projectionHom Γ domain)))
    (normal : Normal (S := S) value.code)
    (same : Equal S.R (twice Γ domain).raw (Presentation.rename wk value.code)
      (Presentation.rename (liftRen wk) value.code)
      (Presentation.rename wk (codomain.reindex (projectionHom Γ domain)).code)) :
    (ContextualDependentCheckingReplay.recover_normal facts algebra headTypingUnique complete roots heads declared
      (root_reflection rigid) (ContextualDependentFlex.withoutNewest Γ domain) (CtxRen.wk _ _) codomain value normal).isSome = true := by
  have invertible := inverse_forced rigid complete Γ domain codomain value normal same
  obtain ⟨body, found⟩ := Option.isSome_iff_exists.mp invertible
  have computed := ContextualDependentCheckingReplay.recover_normal_code facts algebra headTypingUnique complete
    roots heads declared (root_reflection rigid) (ContextualDependentFlex.withoutNewest Γ domain)
    (CtxRen.wk _ _) codomain value normal found
  obtain ⟨recovered, accepted, _⟩ := Option.map_eq_some_iff.mp computed
  rw [accepted]
  rfl

def extract (Γ : Context S.R) (domain codomain : TypeOver Γ)
    (value : Term (extend Γ domain) (codomain.reindex (projectionHom Γ domain)))
    (normal : Normal (S := S) value.code)
    (same : Equal S.R (twice Γ domain).raw (Presentation.rename wk value.code)
      (Presentation.rename (liftRen wk) value.code)
      (Presentation.rename wk (codomain.reindex (projectionHom Γ domain)).code)) :
    Recovery (ContextualDependentFlex.withoutNewest Γ domain) codomain value.code :=
  (ContextualDependentCheckingReplay.recover_normal facts algebra headTypingUnique complete roots heads declared
    (root_reflection rigid) (ContextualDependentFlex.withoutNewest Γ domain) (CtxRen.wk _ _) codomain value normal).get
      (recovery_succeeds rigid complete facts roots heads algebra headTypingUnique declared Γ domain codomain value normal same)

end ContextualDependentUnaryScope
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
