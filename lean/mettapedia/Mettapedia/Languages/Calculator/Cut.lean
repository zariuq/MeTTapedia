import Mettapedia.Languages.Calculator.Interaction
import Mettapedia.GSLT.LanguageDef.Interaction.Migration

/-!
# The rewriting calculator carries an interaction cut

Read as a rule, the successor law of addition has the full shape of an
interaction cut.  The contact is `Add`; the program is a successor, with the
number under it as continuation; the environment is the second summand,
taken directly.  The contraction joins the two continuations by `Add` again,
beneath a new successor.  Nothing is substituted and nothing is running
anywhere else, so its migration mode is interface composition: the outer
constructor of the program is carried out of the contact and the
continuations meet again under it.

The same shape is composition in an interaction category.  That arithmetic
has it is a fact about the definition of an interaction cut, which asks
nothing of the contact beyond its sorts and its head position.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Calculator

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.StructuralMorphism
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts

/-- The directed laws bind every variable of their right sides on the left. -/
theorem calculatorRewriting_executionFlowErrors_eq_nil :
    calculatorRewriting.executionFlowErrors [] = [] := by
  apply LanguageDef.executionFlowErrors_eq_nil_of_premiseFree
  · rfl
  · intro rule membership
    simp only [calculatorRewriting, laws, List.map_cons, List.map_nil, List.mem_cons,
      List.not_mem_nil, or_false] at membership
    rcases membership with rfl | rfl | rfl | rfl <;> rfl
  · intro rule membership name nameMembership
    simp only [calculatorRewriting, laws, List.map_cons, List.map_nil, List.mem_cons,
      List.not_mem_nil, or_false] at membership
    rcases membership with rfl | rfl | rfl | rfl <;>
      simp [directed, addZero, addSucc, mulZero, mulSucc, Pattern.freeFvarNames]
        at nameMembership ⊢ <;>
      tauto

/-- The rewriting calculator as an iGSLT. -/
def calculatorRewritingIGSLT : IGSLT where
  presentation := calculatorRewritingPresentation
  baseInteraction := isBaseRewrite_of_premises_eq_nil rfl
  executionProfile :=
    { relationModes := []
      admitted :=
        { lang := calculatorRewriting
          admitted := LanguageDef.executionAdmissionErrors_eq_nil_of_emptyModes
            calculatorRewriting calculatorRewriting_validate_eq_nil
            calculatorRewriting_executionFlowErrors_eq_nil }
      exactLanguage := rfl }

/-- The successor constructor. -/
def successorConstructor : DeclaredConstructor calculatorRewritingValidated :=
  ⟨calculatorRewriting.terms[1], List.getElem_mem (by decide)⟩

/-- The program side: a successor, the number under it the continuation. -/
def successorOperand : InteractionOperandProfile calculatorRewritingPresentation where
  constructor := successorConstructor
  schemaTerm := .apply "Succ" [.fvar "m"]
  continuation :=
    { index := 0
      inBounds := by decide
      hasInteractingResult := by rfl }
  continuationPattern := .fvar "m"
  continuationVariable := .plain "m"
  subject := .absent
  form := .introduced (by
      simp [RepresentedBy, UsesBareCollection, successorConstructor, calculatorRewriting,
        terms])
    (by rfl)

/-- The environment side: the second summand, taken directly. -/
def summandOperand : InteractionOperandProfile calculatorRewritingPresentation where
  constructor := calculatorRewritingPresentation.contactConstructor
  schemaTerm := .fvar "n"
  continuation :=
    { index := 1
      inBounds := by decide
      hasInteractingResult := by rfl }
  continuationPattern := .fvar "n"
  continuationVariable := .plain "n"
  subject := .absent
  form := .direct rfl

/-- Addition is the ordered core contact. -/
def additionCoreContact : CoreContactPresentation calculatorRewritingValidated where
  sort := calculatorRewritingPresentation.interactingSort
  constructor := calculatorRewritingPresentation.contactConstructor
  representation := .binary
  representsCore := by rfl

/-- The successor law as an interaction cut. -/
def successorCut : InteractionCutPresentation calculatorRewritingIGSLT where
  program := successorOperand
  environment := summandOperand
  coreContact := additionCoreContact
  programPlacement := .introduced rfl (by
      intro equality
      have labels := congrArg (fun constructor => constructor.1.label) equality
      change "Succ" = "Add" at labels
      exact (by decide : ("Succ" : String) ≠ "Add") labels)
  environmentPlacement := .direct rfl rfl rfl rfl
  sourceShape :=
    { core := (directed addSucc).left
      coreShape :=
        (CutSourceShape.binary rfl :
          CutSourceShape additionCoreContact successorOperand.schemaTerm
            summandOperand.schemaTerm
            (.apply additionCoreContact.constructor.1.label
              [successorOperand.schemaTerm, summandOperand.schemaTerm]))
      envelope := .hole
      fillsSource := rfl }
  sourceEnvelopeInSignature := .hole "Num"
  interactionPremisesEmpty := rfl
  residual := .constructor successorConstructor (by
    change RepresentedBy successorConstructor.1 (directed addSucc).right
    simp [RepresentedBy, UsesBareCollection, successorConstructor, calculatorRewriting,
      terms, directed, addSucc])
  subjectsAgree := .structural rfl (by
    intro equation membership
    cases membership)

/-- No position of the rewriting calculator is a reduction position. -/
theorem calculatorRewriting_reductionPositions :
    reductionPositions calculatorRewriting = [] := by
  decide +kernel

/-- **The successor law composes interfaces.**  Its continuations are joined
again by `Add` beneath a new successor. -/
theorem successorCut_migrationMode : successorCut.migrationMode = .interface := by
  decide +kernel

end Mettapedia.Languages.Calculator
