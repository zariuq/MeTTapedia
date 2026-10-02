import Mettapedia.Languages.ProcessCalculi.Ambient.MobileAmbients
import Mettapedia.GSLT.LanguageDef.Interaction.Presentability
import Mettapedia.GSLT.LanguageDef.Interaction.Migration
import Mettapedia.GSLT.LanguageDef.ContinuationRetyping
import Mettapedia.GSLT.LanguageDef.ClosedTermChecker

/-!
# Mobile ambients as an interactive GSLT, and what dissolution moves

The interacting sort is the sort of processes, the contact is parallel
composition, and the selected rule is dissolution: `open n.P | n[Q] ⟶ P | Q`.
It is an interaction cut.  The program is the capability, the environment is
the ambient, and the two name the same boundary.

No datum passes from one continuation to the other.  What the contraction
changes is where the environment's continuation runs: before, it is running
inside the boundary; after, it is running beside the program's continuation.
The position inside an ambient is a reduction position of the calculus, and
that is what distinguishes dissolution from the release of a guarded
continuation.  The migration mode is spatial.

The same contractum in a calculus where the boundary guards its content
would be pure release.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.Ambient.Mobile

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.StructuralMorphism
open Mettapedia.GSLT.LanguageDef.ContinuationRetypingPlan
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts

/-- The exact validated definition. -/
def ambientValidated : ValidatedLanguageDef :=
  ⟨ambientCalc, ambientCalc_validate_eq_nil⟩

/-- Mobile ambients: processes meet in parallel composition, and dissolution
is headed by it. -/
def ambientPresentation : InteractivePresentation where
  presentation := ambientValidated
  interactingSort := ⟨TypeDecl.plain "Proc", List.Mem.head _⟩
  contactConstructor := ⟨terms[1], List.getElem_mem (by decide)⟩
  interactionRewrite := ⟨openRule, List.Mem.head _⟩
  contactRepresentation := .collection .hashBag
  representsContact := by rfl
  interactionHeaded := by
    simp [InteractionHeaded, openRule, par]

/-- Mobile ambients as an iGSLT. -/
def ambientIGSLT : IGSLT where
  presentation := ambientPresentation
  baseInteraction := isBaseRewrite_of_premises_eq_nil rfl
  executionProfile :=
    { relationModes := []
      admitted :=
        { lang := ambientCalc
          admitted := ambientCalc_executionAdmissionErrors_eq_nil }
      exactLanguage := rfl }

/-- Dissolution is a base rule; the calculus is interactive. -/
theorem ambientCalc_isInteractive : IsInteractive ambientCalc :=
  ambientPresentation.isInteractive (isBaseRewrite_of_premises_eq_nil rfl)

/-- `open a.0 | a[0]` as a closed process. -/
def openingTerm : ambientPresentation.Term :=
  ClosedTerm.ofCheck opening (by decide +kernel)

/-- `0 | 0` as a closed process. -/
def dissolvedTerm : ambientPresentation.Term :=
  ClosedTerm.ofCheck (par [nil, nil] none) (by decide +kernel)

/-- The dissolution is a step of the iGSLT. -/
theorem opening_semantic_step : ambientIGSLT.toGSLT.Step openingTerm dissolvedTerm :=
  primitiveStep_to_presentedStep (base := defaultBasePremises)
    (presentation := ambientPresentation) opening_dissolves

/-! ## The cut -/

/-- The `open` capability. -/
def openConstructor : DeclaredConstructor ambientValidated :=
  ⟨terms[4], List.getElem_mem (by decide)⟩

/-- The ambient constructor. -/
def ambConstructor : DeclaredConstructor ambientValidated :=
  ⟨terms[5], List.getElem_mem (by decide)⟩

/-- The program side: the capability, the boundary's name its subject. -/
def capabilityOperand : InteractionOperandProfile ambientPresentation where
  constructor := openConstructor
  schemaTerm := .apply "AOpen" [.fvar "n", .fvar "p"]
  continuation :=
    { index := 1
      inBounds := by decide
      hasInteractingResult := by rfl }
  continuationPattern := .fvar "p"
  continuationVariable := .plain "p"
  subject := .argument { index := 0, inBounds := by decide } (.fvar "n") (by rfl)
  form := .introduced (by
      simp [RepresentedBy, UsesBareCollection, openConstructor, terms])
    (by rfl)

/-- The environment side: the ambient, its content the continuation. -/
def boundaryOperand : InteractionOperandProfile ambientPresentation where
  constructor := ambConstructor
  schemaTerm := amb (.fvar "n") (.fvar "q")
  continuation :=
    { index := 1
      inBounds := by decide
      hasInteractingResult := by rfl }
  continuationPattern := .fvar "q"
  continuationVariable := .plain "q"
  subject := .argument { index := 0, inBounds := by decide } (.fvar "n") (by rfl)
  form := .introduced (by
      simp [RepresentedBy, UsesBareCollection, ambConstructor, terms, amb])
    (by rfl)

/-- Parallel composition is the ordered core. -/
def ambientCoreContact : CoreContactPresentation ambientValidated where
  sort := ambientPresentation.interactingSort
  constructor := ambientPresentation.contactConstructor
  representation := .collection .hashBag
  representsCore := by rfl

/-- Dissolution as an interaction cut. -/
def dissolutionCut : InteractionCutPresentation ambientIGSLT where
  program := capabilityOperand
  environment := boundaryOperand
  coreContact := ambientCoreContact
  programPlacement := .introduced rfl (by
      intro equality
      have labels := congrArg (fun constructor => constructor.1.label) equality
      exact absurd labels (by decide : ("AOpen" : String) ≠ "APar"))
  environmentPlacement := .introduced rfl (by
      intro equality
      have labels := congrArg (fun constructor => constructor.1.label) equality
      exact absurd labels (by decide : ("AAmb" : String) ≠ "APar"))
  sourceShape :=
    { core := openRule.left
      coreShape :=
        (CutSourceShape.collection [] (some "rest") rfl :
          CutSourceShape ambientCoreContact capabilityOperand.schemaTerm
            boundaryOperand.schemaTerm
            (.collection .hashBag
              (capabilityOperand.schemaTerm :: boundaryOperand.schemaTerm :: [])
              (some "rest")))
      envelope := .hole
      fillsSource := rfl }
  sourceEnvelopeInSignature := .hole "Proc"
  interactionPremisesEmpty := rfl
  residual := .constructor ambientPresentation.contactConstructor (by
    change RepresentedBy ambientPresentation.contactConstructor.1 openRule.right
    exact ⟨"ps", .base "Proc", rfl⟩)
  subjectsAgree := .nominal (.fvar "n") rfl rfl

/-- The surface is the name of the boundary, carried by both sides. -/
theorem ambient_subject_nominal :
    dissolutionCut.program.subject.pattern = some (.fvar "n") ∧
      dissolutionCut.environment.subject.pattern = some (.fvar "n") :=
  ⟨rfl, rfl⟩

/-! ## What dissolution moves -/

/-- The content of an ambient is the one reduction position of the calculus
that is a constructor argument. -/
theorem ambient_reductionPositions : reductionPositions ambientCalc = [("AAmb", 1)] := by
  decide +kernel

/-- **Dissolution restructures space.**  No datum is bound; the reduction
positions above the environment's continuation change. -/
theorem dissolution_migrationMode : dissolutionCut.migrationMode = .spatial := by
  decide +kernel

/-- No datum of the environment is bound into the program's continuation. -/
theorem dissolution_not_bindsFromEnvironment : ¬ dissolutionCut.BindsFromEnvironment := by
  decide +kernel

/-- The same rule read in a calculus where the boundary is a guard would be
pure release: the classification depends on the content of an ambient being a
reduction position. -/
theorem dissolution_none_without_location :
    ({ dissolutionCut.contractionSchema with locations := [] }).mode = .none := by
  decide +kernel

/-! ## Wrapping -/

/-- Parallel composition is neither of the two introductions. -/
theorem contact_mem_continuationConstructors :
    ambientPresentation.contactConstructor ∈ continuationConstructors dissolutionCut := by
  apply (mem_continuationConstructors_iff dissolutionCut
    ambientPresentation.contactConstructor).2
  constructor
  · intro equality
    have labels := congrArg (fun constructor => constructor.1.label) equality
    exact absurd labels (by decide : ("APar" : String) ≠ "AOpen")
  · intro equality
    have labels := congrArg (fun constructor => constructor.1.label) equality
    exact absurd labels (by decide : ("APar" : String) ≠ "AAmb")

/-- The contractum is covered by the continuation signature. -/
theorem dissolutionRetyping : ContinuationRetypingPlan dissolutionCut :=
  ⟨contact_mem_continuationConstructors⟩

@[simp]
theorem ambient_costBasePar_params :
    (costBaseConstructor dissolutionCut terms[1]).params =
      [.simple "ps" (.collection .hashBag (.base (costBaseSortName "Proc")))] := by
  decide +kernel

@[simp]
theorem ambient_costBaseOpen_params :
    (costBaseConstructor dissolutionCut terms[4]).params =
      [.simple "n" (.base (costBaseSortName "Name")),
        .simple "p" (.base costWrappedSortName)] := by
  decide +kernel

@[simp]
theorem ambient_costBaseAmb_params :
    (costBaseConstructor dissolutionCut terms[5]).params =
      [.simple "n" (.base (costBaseSortName "Name")),
        .simple "p" (.base costWrappedSortName)] := by
  decide +kernel

/-- The left side of the dissolution rule stays sorted when the two
continuations are moved to the wrapped fibre. -/
theorem dissolutionRetyping_redexRetypable : dissolutionRetyping.RedexRetypable := by
  unfold ContinuationRetypingPlan.RedexRetypable
  change HasType dissolutionRetyping.generatedLanguage dissolutionRetyping.generatedFreeContext []
    (.collection .hashBag
      [.apply (costBaseConstructorName "AOpen") [.fvar "n", .fvar "p"],
        .apply (costBaseConstructorName "AAmb") [.fvar "n", .fvar "q"]] (some "rest"))
    (.base (costBaseSortName "Proc"))
  apply HasType.collectionConstructor
    (rule := costBaseConstructor dissolutionCut terms[1]) (parameterName := "ps")
  · exact dissolutionRetyping.costBaseConstructor_mem_generated terms[1]
      (List.getElem_mem (by decide))
  · exact ambient_costBasePar_params
  · apply ElementsHaveType.cons
    · apply HasType.constructor (rule := costBaseConstructor dissolutionCut terms[4])
      · exact dissolutionRetyping.costBaseConstructor_mem_generated terms[4]
          (List.getElem_mem (by decide))
      · simp [UsesBareCollection, ambient_costBaseOpen_params]
      · rw [ambient_costBaseOpen_params]
        exact .cons trivial rfl (HasType.fvar rfl) (.cons trivial rfl (HasType.fvar rfl) .nil)
    · apply ElementsHaveType.cons
      · apply HasType.constructor (rule := costBaseConstructor dissolutionCut terms[5])
        · exact dissolutionRetyping.costBaseConstructor_mem_generated terms[5]
            (List.getElem_mem (by decide))
        · simp [UsesBareCollection, ambient_costBaseAmb_params]
        · rw [ambient_costBaseAmb_params]
          exact .cons trivial rfl (HasType.fvar rfl)
            (.cons trivial rfl (HasType.fvar rfl) .nil)
      · exact .nil _ _

/-- The contractum, the two continuations side by side, has the wrapped
sort. -/
theorem dissolutionRetyping_wrappable : dissolutionRetyping.Wrappable := by
  unfold ContinuationRetypingPlan.Wrappable
  change HasType dissolutionRetyping.generatedLanguage dissolutionRetyping.generatedFreeContext []
    (.collection .hashBag [.fvar "p", .fvar "q"] (some "rest")) (.base costWrappedSortName)
  exact HasType.collectionConstructor
    (rule := costWrappedConstructor (theory := ambientIGSLT) terms[1])
    (parameterName := "ps")
    (dissolutionRetyping.costWrappedConstructor_mem_generated
      ambientPresentation.contactConstructor contact_mem_continuationConstructors)
    (by rfl)
    (.cons (HasType.fvar rfl) (.cons (HasType.fvar rfl) (.nil _ _)))

end Mettapedia.Languages.ProcessCalculi.Ambient.Mobile
