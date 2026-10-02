import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedModelMaps

/-!
# Binding clones on equivalent represented carriers

Transport across contextwise equivalences preserves the entire binding clone,
including the environments lifted beneath operator arguments.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedTypeComparison

open Mettapedia.OSLF.Binding.BindingSubstitutionAlgebra
open Mettapedia.OSLF.Binding.FreeBindingTerms

universe u v

variable {S : Signature}

namespace CarrierTransport

variable (A : BindingCloneAlgebra.Algebra.{u} S)
variable {F : Ctx S → S.Srt → Type v}
variable (e : ∀ Γ s, A.substitution.Carrier Γ s ≃ F Γ s)

/-- The original substitution action on the represented carriers. -/
abbrev substitution : BindingSubstitutionAlgebra.Algebra.{v} S where
  Carrier := F
  injectVar v := e _ _ (A.substitution.injectVar v)
  substitute σ x := e _ _ (A.substitution.substitute
    (fun s v => (e _ s).symm (σ s v)) ((e _ _).symm x))
  substitute_var := by
    intro Γ Δ σ s v
    simp only [Equiv.symm_apply_apply, A.substitution.substitute_var,
      Equiv.apply_symm_apply]
  substitute_identity x := by
    simp only [Equiv.symm_apply_apply]
    rw [A.substitution.substitute_identity, Equiv.apply_symm_apply]
  substitute_comp σ τ x := by
    simp only [Equiv.symm_apply_apply]
    rw [A.substitution.substitute_comp]

theorem inverse_substitute {Γ Δ : Ctx S} {s : S.Srt}
    (σ : Environment S F Γ Δ) (x : F Γ s) :
    (e Δ s).symm ((substitution A e).substitute σ x) =
      A.substitution.substitute (fun t v => (e Δ t).symm (σ t v)) ((e Γ s).symm x) :=
  Equiv.symm_apply_apply _ _

theorem inverse_liftEnvironment {Γ Δ : Ctx S}
    (σ : Environment S F Γ Δ) :
    ∀ (bs : List S.Srt) (s : S.Srt) (v : Var (bs ++ Γ) s),
      (e (bs ++ Δ) s).symm ((substitution A e).liftEnvironment σ bs s v) =
        A.substitution.liftEnvironment (fun t w => (e Δ t).symm (σ t w)) bs s v
  | [], _, _ => rfl
  | b :: bs, _, .zero => Equiv.symm_apply_apply _ _
  | b :: bs, _, .succ v => by
      change (e _ _).symm ((substitution A e).substitute
        (fun _ w => (substitution A e).injectVar (.succ w))
        ((substitution A e).liftEnvironment σ bs _ v)) = _
      simp only [substitution, Equiv.symm_apply_apply]
      rw [inverse_liftEnvironment σ bs _ v]
      rfl

theorem inverse_substituteArgs {Γ Δ : Ctx S} (σ : Environment S F Γ Δ) :
    ∀ {arity : List (List S.Srt × S.Srt)} (args : FamilyArgs S F arity Γ),
      FamilyArgs.map (fun {Γ s} x => (e Γ s).symm x)
          ((substitution A e).substituteArgs σ args) =
        A.substitution.substituteArgs (fun t v => (e Δ t).symm (σ t v))
          (FamilyArgs.map (fun {Γ s} x => (e Γ s).symm x) args)
  | _, .nil => rfl
  | _, .cons (bs := bs) head tail => by
      simp only [BindingSubstitutionAlgebra.Algebra.substituteArgs, FamilyArgs.map]
      rw [inverse_substitute A e, inverse_substituteArgs σ tail]
      congr 2
      funext s v
      exact inverse_liftEnvironment A e σ bs s v

/-- Authored operators on the represented carriers. -/
abbrev algebra : BindingCloneAlgebra.Algebra.{v} S where
  substitution := substitution A e
  operation o args := e _ _ (A.operation o
    (FamilyArgs.map (fun {Γ s} x => (e Γ s).symm x) args))
  operation_substitute σ o args := by
    change e _ _ (A.substitution.substitute _ ((e _ _).symm (e _ _ _))) = _
    rw [Equiv.symm_apply_apply, A.operation_substitute]
    exact congrArg (fun a => e _ _ (A.operation o a))
      (inverse_substituteArgs A e σ args).symm

theorem map_map_inverse {Γ : Ctx S} :
    ∀ {arity : List (List S.Srt × S.Srt)}
      (args : FamilyArgs S A.substitution.Carrier arity Γ),
      FamilyArgs.map (fun {Γ s} x => (e Γ s).symm x)
        (FamilyArgs.map (fun {Γ s} x => e Γ s x) args) = args
  | _, .nil => rfl
  | _, .cons head tail => by
      simp only [FamilyArgs.map, Equiv.symm_apply_apply, map_map_inverse tail]

/-- The forward equivalence is a binding-clone map. -/
def forward : FreeBindingClone.Hom A (algebra A e) where
  raw :=
    { map := fun {Γ s} x => e Γ s x
      map_variable := by intros; rfl
      map_operation := by
        intro Γ s o args
        change e Γ s (A.operation o args) = e Γ s (A.operation o _)
        exact congrArg (fun a => e Γ s (A.operation o a)) (map_map_inverse A e args).symm }
  map_substitute := by
    intro Γ Δ s σ x
    change e Δ s (A.substitution.substitute σ x) =
      e Δ s (A.substitution.substitute _ ((e Γ s).symm (e Γ s x)))
    simp only [Equiv.symm_apply_apply]

/-- The inverse equivalence is a binding-clone map. -/
def inverse : FreeBindingClone.Hom (algebra A e) A where
  raw :=
    { map := fun {Γ s} x => (e Γ s).symm x
      map_variable := by intros; exact Equiv.symm_apply_apply _ _
      map_operation := by intros; exact Equiv.symm_apply_apply _ _ }
  map_substitute := inverse_substitute A e

theorem forward_inverse : FreeBindingClone.Hom.comp (forward A e) (inverse A e) =
    FreeBindingClone.Hom.id A := by
  apply FreeBindingClone.Hom.ext
  apply FreeBindingTerms.Hom.ext
  intros
  exact Equiv.symm_apply_apply _ _

theorem inverse_forward : FreeBindingClone.Hom.comp (inverse A e) (forward A e) =
    FreeBindingClone.Hom.id (algebra A e) := by
  apply FreeBindingClone.Hom.ext
  apply FreeBindingTerms.Hom.ext
  intros
  exact Equiv.apply_symm_apply _ _

end CarrierTransport

end Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedTypeComparison
