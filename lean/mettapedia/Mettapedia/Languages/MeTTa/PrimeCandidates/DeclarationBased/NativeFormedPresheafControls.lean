import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitivePresheafSemantics
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveCwf
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveConversionFibres
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.NativeFormedFibreControls
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Examples.FormationConversion
import Mettapedia.TypeTheory.CwfYonedaCoherence

/-! # Concrete controls for retained sections and conversion observation -/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
set_option autoImplicit false

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace FormationSensitiveContextual.PresheafSemantics
open _root_.CategoryTheory FormationSensitive
namespace Controls

/-- The actual mixed declaration package has equal conversion observations
but unequal retained source sections. -/
theorem mixed_computation_boundary :
    observeSection (termEquiv Common.wireType (Common.projected (.natural 7))) =
        observeSection (termEquiv Common.wireType (Common.result (.natural 7))) ∧
      termEquiv Common.wireType (Common.projected (.natural 7)) ≠
        termEquiv Common.wireType (Common.result (.natural 7)) := by
  constructor
  · rw [observe_interpret, observe_interpret]
    exact (TermFibre.mk_eq_iff _ _).mpr (Common.projected_converts_result _)
  · intro same
    have terms := (termEquiv Common.wireType).injective same
    exact Common.converted_sections_distinct (congrArg Common.sectionHom terms)

/-- No decoder from this observation can recover every original code
section: the concrete beta step already contradicts such a retraction. -/
theorem no_observation_retraction :
    ¬ ∃ recover : TermFibre (QType.mk Common.wireType) →
        (representedFamily Common.wireType).sections,
      ∀ sectionValue, recover (observeSection sectionValue) = sectionValue := by
  rintro ⟨recover, recovers⟩
  have same := congrArg recover mixed_computation_boundary.1
  rw [recovers, recovers] at same
  exact mixed_computation_boundary.2 same

/-- The represented source includes a genuinely type-dependent program at
every cumulative level, not just the nondependent simple fragment. -/
def polymorphicType (context : Context Tower.rules) (level : LevelExpr) : TypeOver context :=
  ⟨FormationSensitive.Examples.polymorphicIdentityType level,
    .sort (FormationSensitive.Examples.identityLevel level), .sort _,
    FormationSensitive.Examples.polymorphicIdentityType_formed context.raw level⟩

def polymorphicTerm (context : Context Tower.rules) (level : LevelExpr) :
    Term context (polymorphicType context level) :=
  ⟨FormationSensitive.Examples.polymorphicIdentity,
    FormationSensitive.Examples.polymorphicIdentity_typed context.raw level⟩

theorem polymorphic_specialization (context : Context Tower.rules) (level : LevelExpr)
    {Δ : Context Tower.rules} (σ : Hom Δ context) :
    (CwfYoneda.decodeTerm (asCwf Tower.rules) (polymorphicType context level) σ
      ((termEquiv _ (polymorphicTerm context level)).val
        ⟨Opposite.op (CwfYoneda.context (asCwf Tower.rules) Δ), σ⟩)).code =
      subst σ.substitution FormationSensitive.Examples.polymorphicIdentity := by
  rw [section_at]
  rfl

end Controls

#print axioms Controls.mixed_computation_boundary
#print axioms Controls.no_observation_retraction
#print axioms Controls.polymorphic_specialization

end FormationSensitiveContextual.PresheafSemantics
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
