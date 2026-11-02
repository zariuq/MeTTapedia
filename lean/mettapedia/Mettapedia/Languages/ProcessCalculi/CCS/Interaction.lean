import Mettapedia.Languages.ProcessCalculi.CCS.LanguageDef
import Mettapedia.GSLT.LanguageDef.Interaction.Presentability
import Mettapedia.GSLT.LanguageDef.ClosedTermChecker

/-!
# CCS as an interactive GSLT

The interacting sort is the sort of processes, the contact constructor is parallel composition, and the interaction
rule is the reaction: two sums meet in a parallel composition, one offering an action and the other the co-action on
the same name. The contact is carried by a bag, so position within a parallel composition is not data: the surfaces
that must match are the names the two prefixes carry.

The closed controls react on a private name, so that the processes they mention have no free name.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.CCS

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.StructuralMorphism
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine

/-- The exact validated CCS definition. -/
def ccsValidatedLanguageDef : ValidatedLanguageDef :=
  ⟨ccsCalc, ccsCalc_validate_eq_nil⟩

/-- The sort of processes. -/
def ccsProcessSort : DeclaredSort ccsValidatedLanguageDef :=
  ⟨ccsCalc.types[0], List.getElem_mem (by simp [ccsCalc])⟩

/-- Parallel composition. -/
def ccsParallelConstructor : DeclaredConstructor ccsValidatedLanguageDef :=
  ⟨ccsCalc.terms[1], List.getElem_mem (by simp [ccsCalc])⟩

/-- The sum of guards. -/
def ccsSumConstructor : DeclaredConstructor ccsValidatedLanguageDef :=
  ⟨ccsCalc.terms[2], List.getElem_mem (by simp [ccsCalc])⟩

/-- The reaction. -/
def ccsReactDeclaration : DeclaredRewrite ccsValidatedLanguageDef :=
  ⟨ccsCalc.rewrites[0], List.getElem_mem (by simp [ccsCalc])⟩

/-- CCS is interactive: processes meet in parallel composition, and the reaction is headed by it. -/
def ccsInteractivePresentation : InteractivePresentation where
  presentation := ccsValidatedLanguageDef
  interactingSort := ccsProcessSort
  contactConstructor := ccsParallelConstructor
  interactionRewrite := ccsReactDeclaration
  contactRepresentation := .collection .hashBag
  representsContact := by rfl
  interactionHeaded := by
    simp [InteractionHeaded, ccsReactDeclaration, ccsCalc, ccsReactRewrite]

/-- The execution profile of the definition. -/
def ccsExecutionProfile : ExecutionProfile ccsValidatedLanguageDef where
  relationModes := []
  admitted :=
    { lang := ccsCalc
      admitted := ccsCalc_executionAdmissionErrors_eq_nil }
  exactLanguage := rfl

/-- CCS as an iGSLT. -/
def ccsIGSLT : IGSLT :=
  ⟨ccsInteractivePresentation, ccsExecutionProfile,
    isBaseRewrite_of_premises_eq_nil rfl⟩

/-- The interaction rule is a base rule. -/
theorem ccs_baseInteraction : ccsInteractivePresentation.BaseInteraction :=
  isBaseRewrite_of_premises_eq_nil rfl

/-- CCS is interactive: parallel composition is a same-sort contact and the reaction is a base rule headed by it. -/
theorem ccsCalc_isInteractive : IsInteractive ccsCalc :=
  ccsInteractivePresentation.isInteractive ccs_baseInteraction

/-- `(νx)(x.0 | ~x.0)` as a closed process. -/
def handshakeTerm : ccsInteractivePresentation.Term :=
  ClosedTerm.ofCheck privateHandshake (by decide +kernel)

/-- `(νx)(0 | 0)` as a closed process. -/
def handshakeDoneTerm : ccsInteractivePresentation.Term :=
  ClosedTerm.ofCheck (nu (par [nil, nil])) (by decide +kernel)

/-- The reaction on the private name is a step of the iGSLT. -/
theorem handshake_semantic_step :
    ccsIGSLT.toGSLT.Step handshakeTerm handshakeDoneTerm :=
  primitiveStep_to_presentedStep (base := defaultBasePremises)
    (presentation := ccsInteractivePresentation) private_steps

end Mettapedia.Languages.ProcessCalculi.CCS
