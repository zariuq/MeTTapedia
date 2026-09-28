import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.Constants
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.Preservation

/-!
# Typings of applied constants

A constant declared at the dependent function type of a telescope, applied to
a substitution of the telescope, is typed only as the declaration says: the
arguments are typed at the telescope's entries, the application has the
instantiated body as its least type, and every other type is above it. The
proof inverts the application one argument at a time, using injectivity of
dependent function types from the facts about the weak-head forms of types.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Normalization

open TelescopeAbstraction (closeType applyClosed)

open UniverseLevel (LevelOrder)

variable {Head L : Type} [LevelOrder L] {S : Setting Head L}

section Spines

variable (facts : FormFacts S.R S.roles)
include facts

/-- Inversion of a typing of a constant applied to a telescope substitution. -/
theorem Typed.telescope_inv {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ)
    {c : DeclName} :
    ∀ {k : Nat} (Θ : Ctx Head k) (C : Tm Head k), S.R.constantType c = some (closeType Θ C) →
      ∀ {σ : Sub Head k n} {T : Tm Head n}, Typed S.R Γ (applyClosed Θ σ (.const c)) T →
        SubstMor S.R Θ Γ σ ∧ Typed S.R Γ (applyClosed Θ σ (.const c)) (Presentation.subst σ C) ∧
          TypeLe S.R Γ (Presentation.subst σ C) T
  | _, .nil, C, declared, σ, T, typing => by
      obtain ⟨type, u, declared', typedType, hu, le⟩ := Typed.generation typing
      rw [declared] at declared'
      obtain rfl := Option.some.inj declared'
      have principal : Typed S.R Γ (.const c) (Presentation.liftClosed (closeType .nil C)) :=
        .const declared typedType hu
      refine ⟨fun i => Fin.elim0 i, ?_, ?_⟩
      · show Typed S.R Γ (.const c) (Presentation.subst σ C)
        rw [subst_closed]
        exact principal
      · rw [subst_closed]
        exact le
  | _, .snoc Θ E, C, declared, σ, T, typing => by
      have generation : GenerationAt S.R Γ (.app (applyClosed Θ (tailSub σ) (.const c)) (σ 0)) T :=
        Typed.generation typing
      obtain ⟨A, B, tg, ta, le⟩ := generation
      obtain ⟨mor, tg', le'⟩ := Typed.telescope_inv formed Θ (.pi E C) declared tg
      obtain ⟨eE, leC⟩ := TypeLe.pi_parts facts le' (Typed.isType tg formed)
        formed
      have ta' := Typed.convType ta (TypeEq.symm eE)
      refine ⟨?_, ?_, ?_⟩
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · show Typed S.R Γ (σ 0) (Presentation.subst σ (Presentation.rename wk E))
          rw [subst_rename_wk]
          exact ta'
        · show Typed S.R Γ (σ j.succ)
            (Presentation.subst σ (Presentation.rename wk (Ctx.lookup Θ j)))
          rw [subst_rename_wk]
          exact mor j
      · have application := Derivable.appElim tg' ta'
        rw [inst0_subst_liftSub, consSub_tailSub] at application
        exact application
      · have leInst := Derivable.substitutes leC (SubstMor.single ta')
        change Below S.R Γ (inst0 (σ 0) (Presentation.subst (liftSub (tailSub σ)) C))
          (inst0 (σ 0) B) at leInst
        rw [inst0_subst_liftSub, consSub_tailSub] at leInst
        exact .sub leInst le

end Spines

end Normalization
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
