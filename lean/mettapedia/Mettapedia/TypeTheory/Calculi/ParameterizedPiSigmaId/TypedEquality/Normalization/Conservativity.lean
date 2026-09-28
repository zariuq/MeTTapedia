import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.AlgorithmSoundness
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.EmptyRootConversion

/-!
# Conservativity over untyped conversion

When untyped conversion of the rule package is Church–Rosser, two typed terms
that are convertible are equal in the typed equality: both reduce to a common
term, and reduction between typed terms is typed equality. Consequently every
formation-sensitive typing derivation, whose conversion rule uses untyped
conversion, is a typing derivation of the typed equality, and results proved
about the formation-sensitive judgment transfer along this map.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Normalization

open UniverseLevel (LevelOrder)

variable {Head L : Type} [LevelOrder L] {S : Setting Head L}

section Conservativity

variable (facts : FormFacts S.R S.roles)
  (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (church : ConversionCoherence.ChurchRosser S.R)
include facts roots heads church

/-- Convertible typed terms are equal. -/
theorem Conv.toEqual {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) {a b T : Tm Head n}
    (conversion : Conv S.R.headEq a b S.R.computation) (ta : Typed S.R Γ a T)
    (tb : Typed S.R Γ b T) : Equal S.R Γ a b T := by
  obtain ⟨c, ac, bc⟩ := church conversion
  obtain ⟨_, e₁⟩ := Reduces.preserve facts roots heads formed ac ta
  obtain ⟨_, e₂⟩ := Reduces.preserve facts roots heads formed bc tb
  exact .trans e₁ (.symm e₂)

/-- Convertible types are equal types. -/
theorem Conv.toTypeEq {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) {A B : Tm Head n}
    {u v : Head} (conversion : Conv S.R.headEq A B S.R.computation)
    (tA : Typed S.R Γ A (.head u)) (hu : S.R.isUniverse u) (tB : Typed S.R Γ B (.head v))
    (hv : S.R.isUniverse v) : TypeEq S.R Γ A B := by
  obtain ⟨w, join⟩ := S.levels.join_exists hu hv
  obtain ⟨cu, cv⟩ := S.levels.join_upper join
  exact ⟨w, (S.levels.join_level join).1,
    Conv.toEqual facts roots heads church formed conversion (.cumul tA cu) (.cumul tB cv)⟩

/-- Every formation-sensitive typing derivation in a formed context is a typing
derivation of the typed equality. -/
theorem FormationSensitive.Typing.toTyped {n : Nat} {Γ : Ctx Head n} {t A : Tm Head n}
    (typing : FormationSensitive.Typing S.R Γ t A) : CtxFormed S.R Γ → Typed S.R Γ t A := by
  induction typing with
  | headType h => exact fun _ => .headType h
  | var i => exact fun _ => .var i
  | const known _ hu ih => exact fun _ => .const known (ih .nil) hu
  | piForm _ hu _ hv join ihA ihB =>
      intro formed
      have tA := ihA formed
      exact .piForm tA hu (ihB (.snoc formed ⟨_, hu, tA⟩)) hv join
  | sigmaForm _ hu _ hv join ihA ihB =>
      intro formed
      have tA := ihA formed
      exact .sigmaForm tA hu (ihB (.snoc formed ⟨_, hu, tA⟩)) hv join
  | lamIntro _ hu _ ihPi ihBody =>
      intro formed
      have tPi := ihPi formed
      obtain ⟨⟨u', hu', tA⟩, _⟩ := IsType.pi_parts ⟨_, hu, tPi⟩
      exact .lamIntro tPi hu (ihBody (.snoc formed ⟨u', hu', tA⟩))
  | appElim _ _ ihF ihA => exact fun formed => .appElim (ihF formed) (ihA formed)
  | pairIntro _ hu _ _ ihSigma ihA ihB =>
      exact fun formed => .pairIntro (ihSigma formed) hu (ihA formed) (ihB formed)
  | fstElim _ ih => exact fun formed => .fstElim (ih formed)
  | sndElim _ ih => exact fun formed => .sndElim (ih formed)
  | idForm _ hu _ _ ihA iha ihb =>
      exact fun formed => .idForm (ihA formed) hu (iha formed) (ihb formed)
  | reflIntro _ ih => exact fun formed => .reflIntro (ih formed)
  | cumul _ c ih => exact fun formed => .cumul (ih formed) c
  | conv _ _ hu conversion ihT ihB =>
      intro formed
      have tt := ihT formed
      obtain ⟨s, hs, tA⟩ := Typed.isType tt formed
      exact Typed.convType tt
        (Conv.toTypeEq facts roots heads church formed conversion tA hs (ihB formed) hu)

end Conservativity

end Normalization
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
