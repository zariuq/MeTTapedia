import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveCwf
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveConversionFibres
import Mettapedia.TypeTheory.CwfYonedaCoherence

/-! # Retained sections and conversion observation

The construction is parameterized by the declared rules and uses the existing
formation, substitution and conversion judgments. Concrete language controls
are separate consumers, not premises of these laws.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace FormationSensitiveContextual.PresheafSemantics

open _root_.CategoryTheory
open Mettapedia.TypeTheory

variable {Head : Type} {rules : Rules Head}

abbrev representedFamily {Γ : Context rules} (type : TypeOver Γ) :=
  CwfYoneda.family (asCwf rules) type

/-- All natural sections of a represented formed type come from unique
actual terms of that type. This keeps the original term code. -/
def termEquiv {Γ : Context rules} (type : TypeOver Γ) :
    Term Γ type ≃ (representedFamily type).sections :=
  CwfYoneda.termSectionEquiv (asCwf rules) type

theorem section_at {Γ Δ : Context rules} {type : TypeOver Γ}
    (term : Term Γ type) (σ : Hom Δ Γ) :
    CwfYoneda.decodeTerm (asCwf rules) type σ
      ((termEquiv type term).val
        ⟨Opposite.op (CwfYoneda.context (asCwf rules) Δ), σ⟩) = term.reindex σ :=
  CwfYoneda.decode_encode (asCwf rules) type σ (term.reindex σ)

/-- Forget retained code only at the existing, explicitly conversion-valued
observation. The source term is recovered before taking its class. -/
def observeSection {Γ : Context rules} {type : TypeOver Γ}
    (sectionValue : (representedFamily type).sections) : TermFibre (QType.mk type) :=
  TermFibre.mk ((termEquiv type).symm sectionValue)

theorem observe_interpret {Γ : Context rules} {type : TypeOver Γ}
    (term : Term Γ type) : observeSection (termEquiv type term) = TermFibre.mk term := by
  unfold observeSection
  rw [Equiv.symm_apply_apply]

theorem observation_eq_iff {Γ : Context rules} {type : TypeOver Γ}
    (left right : (representedFamily type).sections) :
    observeSection left = observeSection right ↔
      Conv rules.headEq ((termEquiv type).symm left).code
        ((termEquiv type).symm right).code rules.computation :=
  TermFibre.mk_eq_iff _ _

/-- Reindexing and forgetting conversion commute for every represented
section, not only a hand-picked term or ground environment. -/
theorem observation_substitution {Γ Δ : Context rules} {type : TypeOver Γ}
    (σ : Hom Δ Γ) (sectionValue : (representedFamily type).sections) :
    observeSection (CwfYoneda.substituteSection (asCwf rules) σ sectionValue) =
      (observeSection sectionValue).reindex σ := by
  exact congrArg (fun term : Term Δ (type.reindex σ) => TermFibre.mk term)
    (CwfYoneda.recoverTerm_substituteSection (asCwf rules) σ sectionValue)

#print axioms termEquiv
#print axioms observation_substitution

end FormationSensitiveContextual.PresheafSemantics
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
