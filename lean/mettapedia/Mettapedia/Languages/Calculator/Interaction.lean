import Mettapedia.Languages.Calculator.LanguageDef
import Mettapedia.GSLT.LanguageDef.Interaction.Presentability

/-!
# The calculator and interaction

The equational calculator admits no interactive presentation, and for the
plainest of reasons: it authors no rewrite, so there is no rule at which
anything could meet anything.

The verdict belongs to that presentation and not to arithmetic.  Read the
same laws as directed rules and the three clauses of the definition of an
interactive GSLT are met to the letter: the sort of numbers, the binary
constructor `Add` on it, and a base rule headed by `Add`.  Nothing in the
definition distinguishes a sum consuming its second summand from a program
meeting its environment.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Calculator

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.StructuralMorphism
open Mettapedia.OSLF.MeTTaIL.Syntax

/-- The equational calculator admits no interactive presentation: it has no
rule to select. -/
theorem calculator_not_interactive : ¬ AdmitsInteractivePresentation calculator :=
  not_admitsInteractivePresentation_of_rewrites_eq_nil rfl

/-- The exact validated rewriting calculator. -/
def calculatorRewritingValidated : ValidatedLanguageDef :=
  ⟨calculatorRewriting, calculatorRewriting_validate_eq_nil⟩

/-- The rewriting calculator with `Add` selected as contact and the successor
law as interaction rule. -/
def calculatorRewritingPresentation : InteractivePresentation where
  presentation := calculatorRewritingValidated
  interactingSort := ⟨calculatorRewriting.types[0], List.getElem_mem (by decide)⟩
  contactConstructor := ⟨calculatorRewriting.terms[2], List.getElem_mem (by decide)⟩
  interactionRewrite := ⟨calculatorRewriting.rewrites[1], List.getElem_mem (by decide)⟩
  contactRepresentation := .binary
  representsContact := by rfl
  interactionHeaded := by rfl

/-- Its selected rule is a base rule. -/
theorem calculatorRewriting_baseInteraction :
    calculatorRewritingPresentation.BaseInteraction :=
  isBaseRewrite_of_premises_eq_nil rfl

/-- The rewriting calculator meets the letter of the definition: addition is
a same-sort binary constructor and a base rule is headed by it. -/
theorem calculatorRewriting_isInteractive : IsInteractive calculatorRewriting :=
  calculatorRewritingPresentation.isInteractive calculatorRewriting_baseInteraction

/-- The two presentations share their signature exactly. -/
theorem calculatorRewriting_signature :
    calculatorRewriting.types = calculator.types ∧
      calculatorRewriting.terms = calculator.terms :=
  ⟨rfl, rfl⟩

end Mettapedia.Languages.Calculator
