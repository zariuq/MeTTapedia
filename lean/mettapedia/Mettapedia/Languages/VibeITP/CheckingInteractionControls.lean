import Mettapedia.Languages.VibeITP.CheckingInteraction
import Mettapedia.Languages.VibeITP.Presentation.SimultaneousPresentationControls
import Mettapedia.Languages.VibeITP.Presentation.SignatureExtensionDerivation

/-!
# Concrete source judgments at the persistent interaction boundary

The existing axiom-free theory with an admitted two-parameter definition
supplies a literal-arithmetic example and a simultaneous crossing substitution.
An undeclared symbol cannot become a static theorem by requesting it through
the interaction interface. These are mathematical execution-existence controls,
not a native runtime execution or a fairness guarantee.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.CheckingInteraction.Controls

open Spec Presentation
open Presentation.SimultaneousPresentation.Controls (theory allocated hosted crossing crossing_derived)

theorem literal_addition_has_execution : Nonempty
    (StaticExecution theory allocated (litAddStatement 3 4)) :=
  (static_derives_iff_execution hosted _).mp (.litAdd (by decide +kernel) (by decide +kernel))

theorem crossing_substitution_has_execution : Nonempty
    (SimultaneousExecution theory allocated crossing) :=
  (simultaneous_derives_iff_execution hosted crossing).mp crossing_derived

theorem no_source_axioms : theory.axioms = [] :=
  Presentation.SimultaneousPresentation.Controls.no_axioms

def undeclared : Term := .app (.fresh 99) []

theorem undeclared_not_derived : ¬ Derives theory undeclared := by
  intro derived
  have shape := derivesWithExecution_termShape hosted (static_derives_with_execution derived [])
  cases shape with
  | app present _ _ =>
      simp [theory, sigOf, Presentation.SimultaneousPresentation.Controls.freshInfo] at present

theorem undeclared_request_has_no_execution : ¬ Nonempty (StaticExecution theory allocated undeclared) :=
  fun execution => undeclared_not_derived ((static_derives_iff_execution hosted undeclared).mpr execution)

#print axioms literal_addition_has_execution
#print axioms crossing_substitution_has_execution
#print axioms undeclared_request_has_no_execution
end Mettapedia.Languages.VibeITP.CheckingInteraction.Controls
