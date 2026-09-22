import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.ConversionConservativeExtension
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.UniverseProfiles
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.SigmaConversionBoundary

/-! # Concrete examples of ConversionConservativeExtension -/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation

namespace ConversionConservativeExtensionExamples

variable {Head : Type} {n : Nat}

def doubleIdentity (term : Tm Head n) : Tm Head n :=
  .app (.lam (.var 0)) (.app (.lam (.var 0)) term)

/-- A genuine two-beta shortcut, not an arbitrary equation oracle. -/
inductive ShortcutStep : {n : Nat} → Tm Head n → Tm Head n → Prop where
  | doubleIdentity (term : Tm Head n) : ShortcutStep (doubleIdentity term) term

def shortcutRoot : RootComputation Head where
  step := ShortcutStep
  rename := by
    intro n m rho left right step
    cases step
    exact .doubleIdentity _
  substitute := by
    intro n m sigma left right step
    cases step
    exact .doubleIdentity _

def shortcutRules (R : Rules Head) : Rules Head :=
  { R with computation := shortcutRoot }

/-- The shortcut certificate is independently justified by the two authored
beta steps. Every rule package without declared root computation supports it. -/
def shortcutExtension (R : Rules Head) (empty : R.computation = RootComputation.empty) :
    ConversionConservativeExtension R (shortcutRules R) where
  headEq_eq := rfl
  root_inclusion := by
    intro n left right impossible
    rw [empty] at impossible
    exact impossible.elim
  root_sound := by
    intro n left right step
    cases step with
    | doubleIdentity =>
        exact .trans _ _ _ (.rel _ _ (.betaPi (.var 0) _))
          (.rel _ _ (.betaPi (.var 0) _))

/-- The added shortcut really is a new root step even though conversion is
unchanged for every term. -/
theorem shortcut_adds_root_without_adding_conversion (term : Tower.Tm n) :
    (shortcutRules Tower.rules).computation.step (doubleIdentity term) term ∧
      ¬ Tower.rules.computation.step (doubleIdentity term) term ∧
      (∀ left right : Tower.Tm n,
        Conv Tower.HeadEq left right ↔
          Conv Tower.HeadEq left right (shortcutRules Tower.rules).computation) :=
  ⟨.doubleIdentity term, not_false,
    (shortcutExtension Tower.rules rfl).conversion_iff⟩

end ConversionConservativeExtensionExamples

#print axioms ConversionConservativeExtensionExamples.shortcutExtension
#print axioms ConversionConservativeExtensionExamples.shortcut_adds_root_without_adding_conversion
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
