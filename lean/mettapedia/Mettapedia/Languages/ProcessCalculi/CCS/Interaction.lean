import Mettapedia.Languages.ProcessCalculi.CCS.LanguageDef
import Mettapedia.GSLT.LanguageDef.Interaction.Presentability
import Mettapedia.GSLT.LanguageDef.ClosedTermChecker

/-!
# CCS as an interactive GSLT

The interacting sort is the sort of processes, the contact constructor is
parallel composition, and the interaction rule is synchronisation.  The
contact is carried by a bag, so position within a parallel composition is not
data: the surfaces that must match are the names the two prefixes carry.
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

/-- Synchronisation. -/
def ccsSyncDeclaration : DeclaredRewrite ccsValidatedLanguageDef :=
  ⟨ccsCalc.rewrites[0], List.getElem_mem (by simp [ccsCalc])⟩

/-- CCS is interactive: processes meet in parallel composition, and
synchronisation is headed by it. -/
def ccsInteractivePresentation : InteractivePresentation where
  presentation := ccsValidatedLanguageDef
  interactingSort := ccsProcessSort
  contactConstructor := ccsParallelConstructor
  interactionRewrite := ccsSyncDeclaration
  contactRepresentation := .collection .hashBag
  representsContact := by rfl
  interactionHeaded := by
    simp [InteractionHeaded, ccsSyncDeclaration, ccsCalc, ccsSyncRewrite]

/-- The execution profile of the premise-free definition. -/
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

/-- CCS is interactive: parallel composition is a same-sort contact and
synchronisation is a base rule headed by it. -/
theorem ccsCalc_isInteractive : IsInteractive ccsCalc :=
  ccsInteractivePresentation.isInteractive ccs_baseInteraction

/-- `a.0 | ~a.(a.0)` as a closed process. -/
def handshakeTerm : ccsInteractivePresentation.Term :=
  ClosedTerm.ofCheck handshake (by decide +kernel)

/-- `0 | a.0` as a closed process. -/
def handshakeDoneTerm : ccsInteractivePresentation.Term :=
  ClosedTerm.ofCheck handshakeDone (by decide +kernel)

/-- The synchronisation is a step of the iGSLT. -/
theorem handshake_semantic_step :
    ccsIGSLT.toGSLT.Step handshakeTerm handshakeDoneTerm :=
  primitiveStep_to_presentedStep (base := defaultBasePremises)
    (presentation := ccsInteractivePresentation) handshake_steps

end Mettapedia.Languages.ProcessCalculi.CCS
