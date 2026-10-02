import Mettapedia.Languages.InteractionCategory.LanguageDef
import Mettapedia.GSLT.LanguageDef.Interaction.Presentability
import Mettapedia.GSLT.LanguageDef.Interaction.Migration
import Mettapedia.GSLT.LanguageDef.ContinuationRetyping

/-!
# Composition in an interaction category as an interaction cut

Composition is a same-sort binary contact and its rule is a base rule headed
by it, so both readings are interactive.  The rule is an interaction cut: the
two composed processes are the two introductions, the action each performs on
the shared interface is its subject, and the two subjects are one schema
variable.

The readings differ in what the contraction returns.

* Silently, the two continuations are composed again and nothing else: no
  datum moves, nothing is relocated, nothing is guarded.  The contractum is
  headed by the contact, which is neither introduction, so the contraction is
  covered by the continuation signature.
* Visibly, the two continuations are composed again beneath a new action
  prefix built from the two outer actions.  The contractum is headed by the
  very constructor that introduces both operands, so no continuation
  signature covers it.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.InteractionCategory

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.StructuralMorphism
open Mettapedia.GSLT.LanguageDef.ContinuationRetypingPlan
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts

/-- The presentation: processes, composition, and the composition rule. -/
def presentation (reading : Reading) : InteractivePresentation where
  presentation := ⟨interactionCategory reading, interactionCategory_validate_eq_nil reading⟩
  interactingSort := ⟨TypeDecl.plain "Proc", List.Mem.head _⟩
  contactConstructor := ⟨terms[4], List.getElem_mem (by decide)⟩
  interactionRewrite := ⟨composeRule reading, List.Mem.head _⟩
  contactRepresentation := .binary
  representsContact := by rfl
  interactionHeaded := by rfl

/-- Composition in an interaction category as an iGSLT. -/
def theory (reading : Reading) : IGSLT where
  presentation := presentation reading
  baseInteraction := isBaseRewrite_of_premises_eq_nil rfl
  executionProfile :=
    { relationModes := []
      admitted :=
        { lang := interactionCategory reading
          admitted := LanguageDef.executionAdmissionErrors_eq_nil_of_emptyModes _
            (interactionCategory_validate_eq_nil reading)
            (interactionCategory_executionFlowErrors_eq_nil reading) }
      exactLanguage := rfl }

/-- Both readings are interactive. -/
theorem interactionCategory_isInteractive (reading : Reading) :
    IsInteractive (interactionCategory reading) :=
  (presentation reading).isInteractive (isBaseRewrite_of_premises_eq_nil rfl)

/-! ## The cut -/

/-- The action-prefix constructor. -/
def actConstructor (reading : Reading) :
    DeclaredConstructor (presentation reading).presentation :=
  ⟨terms[3], List.getElem_mem (by decide)⟩

/-- The first process: its right action is the subject. -/
def firstOperand (reading : Reading) : InteractionOperandProfile (presentation reading) where
  constructor := actConstructor reading
  schemaTerm := act (.fvar "a") (.fvar "b") (.fvar "p")
  continuation :=
    { index := 2
      inBounds := by
        show 2 < terms[3].params.length
        decide
      hasInteractingResult := by rfl }
  continuationPattern := .fvar "p"
  continuationVariable := .plain "p"
  subject := .argument
    { index := 1
      inBounds := by
        show 1 < terms[3].params.length
        decide }
    (.fvar "b") (by rfl)
  form := .introduced (by
      simp [RepresentedBy, UsesBareCollection, actConstructor, terms, act])
    (by rfl)

/-- The second process: its left action is the subject. -/
def secondOperand (reading : Reading) : InteractionOperandProfile (presentation reading) where
  constructor := actConstructor reading
  schemaTerm := act (.fvar "b") (.fvar "c") (.fvar "q")
  continuation :=
    { index := 2
      inBounds := by
        show 2 < terms[3].params.length
        decide
      hasInteractingResult := by rfl }
  continuationPattern := .fvar "q"
  continuationVariable := .plain "q"
  subject := .argument
    { index := 0
      inBounds := by
        show 0 < terms[3].params.length
        decide }
    (.fvar "b") (by rfl)
  form := .introduced (by
      simp [RepresentedBy, UsesBareCollection, actConstructor, terms, act])
    (by rfl)

/-- Composition is the ordered core. -/
def coreContact (reading : Reading) :
    CoreContactPresentation (presentation reading).presentation where
  sort := (presentation reading).interactingSort
  constructor := (presentation reading).contactConstructor
  representation := .binary
  representsCore := by rfl

/-- The contractum is headed by composition when silent and by the action
prefix when visible. -/
def residual : (reading : Reading) →
    ResidualRepresentation (presentation := (presentation reading).presentation)
      (composeRule reading).right
  | .silent => .constructor (presentation .silent).contactConstructor (by
      refine ⟨?_, rfl, rfl⟩
      rintro ⟨parameterName, collectionType, elementType, shape⟩
      cases shape)
  | .visible => .constructor (actConstructor .visible) (by
      refine ⟨?_, rfl, rfl⟩
      rintro ⟨parameterName, collectionType, elementType, shape⟩
      cases shape)

/-- The composition rule as an interaction cut. -/
def cut (reading : Reading) : InteractionCutPresentation (theory reading) where
  program := firstOperand reading
  environment := secondOperand reading
  coreContact := coreContact reading
  programPlacement := .introduced rfl (by
      intro equality
      have labels := congrArg (fun constructor => constructor.1.label) equality
      exact absurd labels (by decide : ("Act" : String) ≠ "Comp"))
  environmentPlacement := .introduced rfl (by
      intro equality
      have labels := congrArg (fun constructor => constructor.1.label) equality
      exact absurd labels (by decide : ("Act" : String) ≠ "Comp"))
  sourceShape :=
    { core := (composeRule reading).left
      coreShape :=
        (CutSourceShape.binary rfl :
          CutSourceShape (coreContact reading) (firstOperand reading).schemaTerm
            (secondOperand reading).schemaTerm
            (.apply (coreContact reading).constructor.1.label
              [(firstOperand reading).schemaTerm, (secondOperand reading).schemaTerm]))
      envelope := .hole
      fillsSource := rfl }
  sourceEnvelopeInSignature := .hole "Proc"
  interactionPremisesEmpty := rfl
  residual := residual reading
  subjectsAgree := .nominal (.fvar "b") rfl rfl

/-- The surface is the shared interface action, named on both sides. -/
theorem subject_nominal (reading : Reading) :
    (cut reading).program.subject.pattern = some (.fvar "b") ∧
      (cut reading).environment.subject.pattern = some (.fvar "b") :=
  ⟨rfl, rfl⟩

/-- The contact occurs in no equation: the presentation authors none. -/
theorem contact_equation_free (reading : Reading) :
    ContactEquationFree (presentation reading) := by
  intro equation membership
  cases membership

/-! ## What the contraction moves -/

/-- **Silent composition moves nothing.** -/
theorem silent_migrationMode : (cut .silent).migrationMode = .none := by
  decide +kernel

/-- **Visible composition composes interfaces.**  The continuations are
joined again beneath an action prefix made of the two outer actions. -/
theorem visible_migrationMode : (cut .visible).migrationMode = .interface := by
  decide +kernel

/-- Under neither reading is a datum bound into a continuation. -/
theorem not_bindsFromEnvironment (reading : Reading) :
    ¬ (cut reading).BindsFromEnvironment := by
  cases reading <;> decide +kernel

/-! ## Wrapping -/

/-- Composition is neither of the two introductions. -/
theorem contact_mem_continuationConstructors :
    (presentation .silent).contactConstructor ∈ continuationConstructors (cut .silent) := by
  apply (mem_continuationConstructors_iff (cut .silent)
    (presentation .silent).contactConstructor).2
  constructor <;>
  · intro equality
    have labels := congrArg (fun constructor => constructor.1.label) equality
    exact absurd labels (by decide : ("Comp" : String) ≠ "Act")

/-- The silent contractum is covered by the continuation signature. -/
theorem silentRetyping : ContinuationRetypingPlan (cut .silent) :=
  ⟨contact_mem_continuationConstructors⟩

@[simp]
theorem silent_costBaseComp_params :
    (costBaseConstructor (cut .silent) terms[4]).params =
      [.simple "first" (.base (costBaseSortName "Proc")),
        .simple "second" (.base (costBaseSortName "Proc"))] := by
  decide +kernel

@[simp]
theorem silent_costBaseAct_params :
    (costBaseConstructor (cut .silent) terms[3]).params =
      [.simple "left" (.base (costBaseSortName "Label")),
        .simple "right" (.base (costBaseSortName "Label")),
        .simple "next" (.base costWrappedSortName)] := by
  decide +kernel

/-- The left side of the silent rule stays sorted when the two continuations
are moved to the wrapped fibre. -/
theorem silentRetyping_redexRetypable : silentRetyping.RedexRetypable := by
  unfold ContinuationRetypingPlan.RedexRetypable
  change HasType silentRetyping.generatedLanguage silentRetyping.generatedFreeContext []
    (.apply (costBaseConstructorName "Comp")
      [.apply (costBaseConstructorName "Act") [.fvar "a", .fvar "b", .fvar "p"],
        .apply (costBaseConstructorName "Act") [.fvar "b", .fvar "c", .fvar "q"]])
    (.base (costBaseSortName "Proc"))
  have actTyped : ∀ left right next : String,
      silentRetyping.generatedFreeContext left = some (.base (costBaseSortName "Label")) →
      silentRetyping.generatedFreeContext right = some (.base (costBaseSortName "Label")) →
      silentRetyping.generatedFreeContext next = some (.base costWrappedSortName) →
      HasType silentRetyping.generatedLanguage silentRetyping.generatedFreeContext []
        (.apply (costBaseConstructorName "Act") [.fvar left, .fvar right, .fvar next])
        (.base (costBaseSortName "Proc")) := by
    intro left right next leftType rightType nextType
    apply HasType.constructor (rule := costBaseConstructor (cut .silent) terms[3])
    · exact silentRetyping.costBaseConstructor_mem_generated terms[3]
        (List.getElem_mem (by decide))
    · simp [UsesBareCollection, silent_costBaseAct_params]
    · rw [silent_costBaseAct_params]
      exact .cons trivial rfl (HasType.fvar leftType)
        (.cons trivial rfl (HasType.fvar rightType)
          (.cons trivial rfl (HasType.fvar nextType) .nil))
  apply HasType.constructor (rule := costBaseConstructor (cut .silent) terms[4])
  · exact silentRetyping.costBaseConstructor_mem_generated terms[4]
      (List.getElem_mem (by decide))
  · simp [UsesBareCollection, silent_costBaseComp_params]
  · rw [silent_costBaseComp_params]
    exact .cons trivial rfl (actTyped "a" "b" "p" rfl rfl rfl)
      (.cons trivial rfl (actTyped "b" "c" "q" rfl rfl rfl) .nil)

/-- The silent contractum, the composition of the two continuations, has the
wrapped sort. -/
theorem silentRetyping_wrappable : silentRetyping.Wrappable := by
  unfold ContinuationRetypingPlan.Wrappable
  have wrapped : "Comp" ∈ silentRetyping.wrappedLabels := by
    decide +kernel
  have translated :
      silentRetyping.mapContractum (composeRule .silent).right =
        .apply (costWrappedConstructorName "Comp") [.fvar "p", .fvar "q"] := by
    simp [composeRule, composite, comp, mapContractum_apply, mapContractum_fvar, wrapped]
  change HasType silentRetyping.generatedLanguage silentRetyping.generatedFreeContext []
    (silentRetyping.mapContractum (composeRule .silent).right) (.base costWrappedSortName)
  rw [translated]
  exact HasType.constructor
    (language := silentRetyping.generatedLanguage)
    (free := silentRetyping.generatedFreeContext) (bound := [])
    (rule := costWrappedConstructor (theory := theory .silent) terms[4])
    (arguments := [.fvar "p", .fvar "q"])
    (silentRetyping.costWrappedConstructor_mem_generated
      (presentation .silent).contactConstructor contact_mem_continuationConstructors)
    (by simp [UsesBareCollection, costWrappedConstructor, terms, mapParameterType,
      costWrappedTypeExpr])
    (by
      change ArgumentsHaveTypes _ _ [] [.fvar "p", .fvar "q"]
        [.simple "first" (.base costWrappedSortName),
          .simple "second" (.base costWrappedSortName)]
      exact .cons trivial rfl (HasType.fvar rfl)
        (.cons trivial rfl (HasType.fvar rfl) .nil))

/-- **The visible contractum is not covered.**  It is headed by the action
prefix, which introduces both operands: no continuation signature contains
it. -/
theorem visible_no_retyping : ¬ ContinuationRetypingPlan (cut .visible) := by
  rintro ⟨covered⟩
  have membership : actConstructor .visible ∈ continuationConstructors (cut .visible) :=
    covered
  exact ((mem_continuationConstructors_iff (cut .visible) (actConstructor .visible)).mp
    membership).1 rfl

end Mettapedia.Languages.InteractionCategory
