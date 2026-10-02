import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.Tower
/-!
# A family into a universe is a family into every higher universe

With `A : 𝒰₀` and `F : Π (x : A). 𝒰₀` in context, the dependent function type
`Π (x : A). 𝒰₀` is usable at `Π (x : A). 𝒰₁`: the domains are equal and the
codomain `𝒰₀` is below `𝒰₁`. So `F` itself is typed at `Π (x : A). 𝒰₁`, with no
η-expansion needed, and `F` and its η-expansion `λ x. F x`, equal at
`Π (x : A). 𝒰₀`, are equal at `Π (x : A). 𝒰₁` too. Usable at is not equal to:
the two function types are not equal types (`Below.pi_codomain_raise`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Normalization

open Mettapedia.TypeTheory.UniverseLevel
open TowerModel

/-- The universes at levels 0 and 1. -/
abbrev universe₀ {n : Nat} : Tm Tower.Head n := .head (.sort Tower.zero)
abbrev universe₁ {n : Nat} : Tm Tower.Head n := .head (.sort (.succ Tower.zero))

/-- `A : 𝒰₀`, then `F : Π (x : A). 𝒰₀`. -/
abbrev familyContext : Ctx Tower.Head 2 :=
  .snoc (.snoc .nil universe₀) (.pi (.var 0) universe₀)

theorem familyContext_formed : CtxFormed Tower.rules familyContext :=
  .snoc (.snoc .nil ⟨_, LevelTower.IsUniverse.sort _, .headType (LevelTower.HeadTyping.sort _)⟩)
    ⟨_, LevelTower.IsUniverse.sort _,
      .piForm (.var 0) (LevelTower.IsUniverse.sort _) (.headType (LevelTower.HeadTyping.sort _))
        (LevelTower.IsUniverse.sort _) (LevelTower.Join.sorts _ _)⟩

/-- The η-expansion of `F` is typed at `Π (x : A). 𝒰₁`. -/
theorem etaExpansion_typed_at_raised_codomain :
    Typed Tower.rules familyContext (.lam (.app (.var 1) (.var 0)))
      (.pi (.var 1) universe₁) := by
  refine .lamIntro (u := .sort (.max Tower.zero (.succ (.succ Tower.zero))))
    (.piForm (.var 1) (.sort _) (.headType (.sort _)) (.sort _) (.sorts _ _)) (.sort _) ?_
  have applied : Typed Tower.rules (.snoc familyContext (.var 1))
      (.app (.var 1) (.var 0)) universe₀ :=
    .appElim (A := .var 2) (B := universe₀) (.var 1) (.var 0)
  exact .cumul applied (fun _ => Nat.le_succ _)

/-- `Π (x : A). 𝒰₀` is usable at `Π (x : A). 𝒰₁`. -/
theorem family_types_below :
    Below Tower.rules familyContext (.pi (.var 1) universe₀) (.pi (.var 1) universe₁) :=
  .subPi (u := .sort (.max Tower.zero (.succ Tower.zero)))
    (u' := .sort (.max Tower.zero (.succ (.succ Tower.zero)))) (w := .sort Tower.zero)
    (.piForm (.var 1) (LevelTower.IsUniverse.sort _) (.headType (LevelTower.HeadTyping.sort _))
      (LevelTower.IsUniverse.sort _) (LevelTower.Join.sorts _ _)) (LevelTower.IsUniverse.sort _)
    (.piForm (.var 1) (LevelTower.IsUniverse.sort _) (.headType (LevelTower.HeadTyping.sort _))
      (LevelTower.IsUniverse.sort _) (LevelTower.Join.sorts _ _)) (LevelTower.IsUniverse.sort _)
    (.refl (.var 1)) (LevelTower.IsUniverse.sort _) (.subUniv (fun _ => Nat.le_succ _))

/-- `F` itself is typed at `Π (x : A). 𝒰₁`. -/
theorem family_typed_at_raised_codomain :
    Typed Tower.rules familyContext (.var 0) (.pi (.var 1) universe₁) :=
  .sub (.var 0) family_types_below

/-- `F` and its η-expansion are equal at `Π (x : A). 𝒰₀`, and both, and their
equality, hold at `Π (x : A). 𝒰₁`. -/
theorem family_and_eta_expansion_at_raised_codomain :
    Equal Tower.rules familyContext (.var 0) (.lam (.app (.var 1) (.var 0)))
        (.pi (.var 1) universe₀) ∧
      Typed Tower.rules familyContext (.lam (.app (.var 1) (.var 0)))
        (.pi (.var 1) universe₁) ∧
      Typed Tower.rules familyContext (.var 0) (.pi (.var 1) universe₁) ∧
      Equal Tower.rules familyContext (.var 0) (.lam (.app (.var 1) (.var 0)))
        (.pi (.var 1) universe₁) := by
  have equal : Equal Tower.rules familyContext (.var 0) (.lam (.app (.var 1) (.var 0)))
      (.pi (.var 1) universe₀) := by
    have lamTyped : Typed Tower.rules familyContext (.lam (.app (.var 1) (.var 0)))
        (.pi (.var 1) universe₀) :=
      .lamIntro (u := .sort (.max Tower.zero (.succ Tower.zero)))
        (.piForm (.var 1) (.sort _) (.headType (.sort _)) (.sort _) (.sorts _ _)) (.sort _)
        (.appElim (A := .var 2) (B := universe₀) (.var 1) (.var 0))
    have familyTyped : Typed Tower.rules familyContext (.pi (.var 1) universe₀)
        (.head (.sort (.max Tower.zero (.succ Tower.zero)))) :=
      .piForm (.var 1) (LevelTower.IsUniverse.sort _) (.headType (LevelTower.HeadTyping.sort _))
        (LevelTower.IsUniverse.sort _) (LevelTower.Join.sorts _ _)
    have piTyped : Typed Tower.rules (.snoc familyContext (.var 1)) (.pi (.var 2) universe₀)
        (.head (.sort (.max Tower.zero (.succ Tower.zero)))) :=
      familyTyped.weaken (extension := .var 1)
    have beta : Equal Tower.rules (.snoc familyContext (.var 1))
        (.app (.lam (.app (.var 2) (.var 0))) (.var 0)) (.app (.var 1) (.var 0)) universe₀ :=
      .betaPi (A := .var 2) (B := universe₀) (body := .app (.var 2) (.var 0)) (a := .var 0)
        piTyped (LevelTower.IsUniverse.sort _)
        (.appElim (A := .var 3) (B := universe₀) (.var 2) (.var 0)) (.var 0)
    exact .etaPi (.var 0) lamTyped (.symm beta)
  exact ⟨equal, etaExpansion_typed_at_raised_codomain, family_typed_at_raised_codomain,
    .subEq equal family_types_below⟩

end Normalization
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
