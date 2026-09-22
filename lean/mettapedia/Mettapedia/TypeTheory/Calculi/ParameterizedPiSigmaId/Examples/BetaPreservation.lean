import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveBeta
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Examples.FormationConversion

/-! # Concrete instances and controls for FormationSensitiveBeta -/

open Mettapedia.TypeTheory.UniverseLevel

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace FormationSensitive

variable {n : Nat}

/-! ## Dependent specialization and the conversion boundary -/

namespace BetaExamples

/-- The codomain of the first identity binder really depends on its type
argument: opening it constructs the corresponding endomorphism type. -/
theorem polymorphic_identity_instantiated_codomain (A : Tower.Tm n) :
    inst0 A (.pi (.var 0) (.var 1)) = .pi A (rename wk A) := by
  rfl

/-- Genuine dependent specialization through the general displayed-type
preservation theorem. The tower's Pi-conversion boundary remains an explicit
qualification; this result does not assert that it has been discharged. -/
theorem polymorphic_identity_beta {Γ : Tower.Ctx n} {A : Tower.Tm n}
    {level : LevelExpr} (context : ContextFormation Tower.rules Γ)
    (formed : Typing Tower.rules Γ A (sortTm level))
    (boundary : PiConversionBoundary Tower.rules) :
    Typing Tower.rules Γ (.lam (.var 0)) (.pi A (rename wk A)) := by
  have source := Typing.appElim (Examples.polymorphicIdentity_typed Γ level) formed
  have preserved := source.betaPi towerUniverseRegularity boundary context
  exact preserved

/-- Independently, the same specialization has a direct formation-sensitive
derivation from the formed argument. This control does not require a global
conversion boundary. -/
theorem polymorphic_identity_beta_direct {Γ : Tower.Ctx n} {A : Tower.Tm n}
    {level : LevelExpr} (formed : Typing Tower.rules Γ A (sortTm level)) :
    Typing Tower.rules Γ (.lam (.var 0)) (.pi A (rename wk A)) := by
  apply Typing.lamIntro
  · apply Typing.piForm formed (.sort level)
    · simpa only [sortTm, rename] using formed.weaken (extension := A)
    · exact .sort level
    · exact .sorts level level
  · exact .sort _
  · exact .var 0

/-- The existing formed-endpoint looping profile does not satisfy the Pi
boundary. Formation alone therefore cannot instantiate the general theorem's
qualification, even though the relevant types themselves are formed. -/
theorem formed_endpoints_do_not_supply_pi_boundary :
    UniverseRegularity Examples.ConversionCollapse.rules ∧
      ¬ PiConversionBoundary Examples.ConversionCollapse.rules :=
  ⟨Examples.ConversionCollapse.universeRegularity,
    Examples.ConversionCollapse.no_pi_conversion_boundary⟩

end BetaExamples


#print axioms BetaExamples.polymorphic_identity_beta
#print axioms BetaExamples.polymorphic_identity_beta_direct
#print axioms BetaExamples.formed_endpoints_do_not_supply_pi_boundary

end FormationSensitive
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
