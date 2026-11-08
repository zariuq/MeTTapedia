import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentUnaryScope

/-!
# Normalization and extraction forced by a two-argument equation

The original independently typed body is normalized. Its equality at two
fresh arguments transports to the normal body, which must lie in the outer
scope. Successful normalization therefore yields a typed outer value solving
the original body, with no additional inversion or checker failure.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentUnaryRecovery

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentNormalChecking ContextualDependentUnaryScope

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
variable (rigid : ∀ name, S.roles name = .rigid) (complete : AlgorithmicComplete S.R S.roles)
  (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R)
  (heads : HeadPreserving S.R) (algebra : CumulativeAlgebra S.R)
  (headTypingUnique : ∀ {head first second : Head},
    S.R.headTyping head first → S.R.headTyping head second → first = second)
  (declared : DeclaredTypesFormed S.R)

def recover (fuel : Nat) (Γ : Context S.R) (domain codomain : TypeOver Γ)
    (value : Term (extend Γ domain) (codomain.reindex (projectionHom Γ domain)))
    (same : Equal S.R (twice Γ domain).raw (Presentation.rename wk value.code)
      (Presentation.rename (liftRen wk) value.code)
      (Presentation.rename wk (codomain.reindex (projectionHom Γ domain)).code)) :
    Option (ContextualDependentProjectionInversion.Recovery S.levels (projectionHom Γ domain) codomain
      (⟨_, value⟩ : TotalTerm (extend Γ domain))) :=
  match computed : ExecutableReduction.normalize S.R (fun _ => none) fuel value.code with
  | none => none
  | some result => some <| by
      have preserved := Reduces.preserve facts roots heads (extend Γ domain).formed result.property value.typed
      let normalValue : Term (extend Γ domain) (codomain.reindex (projectionHom Γ domain)) := ⟨result.val, preserved.1⟩
      have normal : Normal (S := S) normalValue.code :=
        ContextualDependentReductionBudget.normal_of_stopped S.R (fun _ => none)
          (fun _ _ _ impossible => ContextualDependentNormalObservations.no_root rigid impossible) result.val
          (ContextualDependentReductionBudget.stopped_of_success S.R (fun _ => none) computed)
      have first := preserved.2.rename (left_compatible Γ domain)
      have second := preserved.2.rename (right_compatible Γ domain)
      have second' : Equal S.R (twice Γ domain).raw (Presentation.rename (liftRen wk) value.code)
          (Presentation.rename (liftRen wk) result.val)
          (Presentation.rename wk (codomain.reindex (projectionHom Γ domain)).code) :=
        (codomain_images (S := S) Γ domain codomain) ▸ second
      have normalSame := first.symm.trans (same.trans second')
      let recovered := extract rigid complete facts roots heads algebra headTypingUnique declared
        Γ domain codomain normalValue normal normalSame
      refine ⟨recovered.body, (codomain.reindex (projectionHom Γ domain)).isType.refl, ?_⟩
      change Equal S.R (extend Γ domain).raw (subst projection recovered.body.code) value.code
        (codomain.reindex (projectionHom Γ domain)).code
      have image : Presentation.rename wk recovered.body.code = result.val := recovered.recovers
      rw [subst_projection, image]
      exact preserved.2.symm

theorem success_iff (fuel : Nat) (Γ : Context S.R) (domain codomain : TypeOver Γ)
    (value : Term (extend Γ domain) (codomain.reindex (projectionHom Γ domain)))
    (same : Equal S.R (twice Γ domain).raw (Presentation.rename wk value.code)
      (Presentation.rename (liftRen wk) value.code)
      (Presentation.rename wk (codomain.reindex (projectionHom Γ domain)).code)) :
    (recover rigid complete facts roots heads algebra headTypingUnique declared fuel Γ domain codomain value same).isSome = true ↔
      (ExecutableReduction.normalize S.R (fun _ => none) fuel value.code).isSome = true := by
  unfold recover
  split <;> simp_all

end ContextualDependentUnaryRecovery
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
