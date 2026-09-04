import Mettapedia.GSLT.LanguageDef.Cost.Construction
import Mettapedia.GSLT.LanguageDef.CanonicalConstructorSupport
import Mettapedia.OSLF.Framework.LambdaInstance

/-!
# Lambda calculus as a continued-interactive GSLT

This module is the non-process-calculus control for the generic interaction
and Cost constructions.  It retains the exact `lambdaCalc` presentation.  In
beta reduction the abstraction is a constructor-headed program operand, while
the argument is the direct environment operand selected from application.
No synthetic environment constructor is introduced.
-/

namespace Mettapedia.GSLT.LanguageDef.LambdaContinuedInteraction

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.ContinuationRetypingPlan
open Mettapedia.OSLF.Framework.LambdaInstance
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.StructuralMorphism

/-- The exact validated lambda-calculus definition. -/
def lambdaValidatedLanguageDef : ValidatedLanguageDef :=
  ⟨lambdaCalc, lambdaCalc_validate_eq_nil⟩

/-- The sole lambda sort selected from the authored presentation. -/
def lambdaTermSort : DeclaredSort lambdaValidatedLanguageDef :=
  ⟨lambdaCalc.types[0], List.getElem_mem (by simp [lambdaCalc])⟩

/-- Authored binary application. -/
def lambdaApplicationConstructor :
    DeclaredConstructor lambdaValidatedLanguageDef :=
  ⟨lambdaCalc.terms[0], List.getElem_mem (by simp [lambdaCalc])⟩

/-- Authored abstraction. -/
def lambdaAbstractionConstructor :
    DeclaredConstructor lambdaValidatedLanguageDef :=
  ⟨lambdaCalc.terms[1], List.getElem_mem (by simp [lambdaCalc])⟩

/-- The authored beta rule. -/
def lambdaBetaRewrite : DeclaredRewrite lambdaValidatedLanguageDef :=
  ⟨lambdaCalc.rewrites[0], List.getElem_mem (by simp [lambdaCalc])⟩

/-- Application is the exact binary contact of the lambda presentation. -/
def lambdaInteractivePresentation : InteractivePresentation where
  presentation := lambdaValidatedLanguageDef
  interactingSort := lambdaTermSort
  contactConstructor := lambdaApplicationConstructor
  interactionRewrite := lambdaBetaRewrite
  contactRepresentation := .binary
  representsContact := by rfl
  interactionHeaded := by rfl

/-- Beta reduction has the premise-free execution profile proved by the sole
authored language definition. -/
def lambdaExecutionProfile :
    ExecutionProfile lambdaValidatedLanguageDef where
  relationModes := []
  admitted :=
    { lang := lambdaCalc
      admitted := lambdaCalc_executionAdmissionErrors_eq_nil }
  exactLanguage := rfl

/-- The lambda presentation as an iGSLT. -/
def lambdaIGSLT : IGSLT :=
  ⟨lambdaInteractivePresentation, lambdaExecutionProfile⟩

/-- The abstraction side of beta is introduced by `Lam`; its body is the
selected program continuation. -/
def lambdaProgramOperand :
    InteractionOperandProfile lambdaInteractivePresentation where
  constructor := lambdaAbstractionConstructor
  schemaTerm := .apply "Lam" [.lambda none (.fvar "body")]
  continuation :=
    { index := 0
      inBounds := by simp [lambdaAbstractionConstructor, lambdaCalc]
      hasInteractingResult := by rfl }
  continuationPattern := .lambda none (.fvar "body")
  continuationVariable := .abstraction none "body"
  subject := .absent
  form := .introduced (by
      simp [RepresentedBy, UsesBareCollection,
        lambdaAbstractionConstructor, lambdaCalc]) (by rfl)

/-- The argument side of beta is the direct second continuation of `App`.
This realizes the manuscript's degenerate environment operand without a
fabricated constructor. -/
def lambdaEnvironmentOperand :
    InteractionOperandProfile lambdaInteractivePresentation where
  constructor := lambdaApplicationConstructor
  schemaTerm := .fvar "arg"
  continuation :=
    { index := 1
      inBounds := by simp [lambdaApplicationConstructor, lambdaCalc]
      hasInteractingResult := by rfl }
  continuationPattern := .fvar "arg"
  continuationVariable := .plain "arg"
  subject := .absent
  form := .direct rfl

/-- Application remains the ordered interaction core. -/
def lambdaCoreContact :
    CoreContactPresentation lambdaValidatedLanguageDef where
  sort := lambdaTermSort
  constructor := lambdaApplicationConstructor
  representation := .binary
  representsCore := by rfl

/-- Beta reduction factored into an introduced abstraction and a direct
argument, with substitution as its authored residual. -/
def lambdaInteractionCut : InteractionCutPresentation lambdaIGSLT where
  program := lambdaProgramOperand
  environment := lambdaEnvironmentOperand
  coreContact := lambdaCoreContact
  programPlacement := .introduced rfl (by
      intro equality
      have labels := congrArg (fun constructor => constructor.1.label) equality
      simp [lambdaProgramOperand, lambdaAbstractionConstructor,
        lambdaCoreContact, lambdaApplicationConstructor, lambdaCalc] at labels)
  environmentPlacement := .direct rfl rfl rfl rfl
  sourceShape :=
    { core := lambdaCalc.rewrites[0].left
      coreShape := by
        change CutSourceShape lambdaCoreContact
          lambdaProgramOperand.schemaTerm lambdaEnvironmentOperand.schemaTerm
          lambdaCalc.rewrites[0].left
        exact CutSourceShape.binary rfl
      envelope := .hole
      fillsSource := rfl }
  sourceEnvelopeInSignature := .hole "Term"
  interactionPremisesEmpty := rfl
  residual := .substitution (.fvar "body") (.fvar "arg")
  subjectsAgree := .structural rfl (by
    intro equation membership
    simp [lambdaIGSLT, lambdaInteractivePresentation,
      lambdaValidatedLanguageDef, lambdaCalc] at membership)

/-- With no authored static equations, equality is the canonical section of
the lambda presentation. -/
def lambdaCanonicalSection : ComputableCanonicalSection lambdaIGSLT where
  normalize := id
  equivalent := fun term =>
    (lambdaIGSLT.toGSLT.equations).iseqv.refl term
  complete := by
    intro left right equivalent
    exact (presentedEquationSetoid_iff_eq_of_no_generators
      defaultBasePremises lambdaInteractivePresentation
      (by rfl) left right).mp equivalent

/-- Lambda equality is contextually trivial on the shared raw carrier as
well as on the closed semantic carrier.  This is the control showing that a
contextual section adds real transport data without changing a theory whose
authored equation relation is empty. -/
def lambdaContextualSection : ComputableContextualSection lambdaIGSLT where
  normalize := id
  mapsClosed := fun term => term.2
  equivalent := fun pattern => Relation.EqvGen.refl pattern
  complete := by
    intro left right equivalent
    exact
      (EquationSemantics.equationEquiv_iff_eq_of_no_generators
        (base := defaultBasePremises) (language := lambdaCalc)
        (by rfl) left right).mp equivalent
  equivalentClosed := fun term =>
    (lambdaIGSLT.toGSLT.equations).iseqv.refl term

/-- The sort-indexed open section is also identity for lambda: the authored
presentation contains no static equation or reflective generator in any
fiber. -/
def lambdaOpenSection : ComputableReflectiveOpenSection lambdaIGSLT
    (ReflectionExtension.emptyAdmitted lambdaCalc) where
  normalize := id
  equivalent := fun term => Relation.EqvGen.refl term
  complete := by
    intro free bound sort left right equivalent
    apply Subtype.ext
    exact
      (ReflectiveEquationSemantics.equationEquiv_iff_eq_of_no_generators
        (profile := .empty) (base := defaultBasePremises)
        (language := lambdaCalc) (by rfl) (by rfl) left.1 right.1).mp
        (reflectiveOpenEquationSetoid_to_equiv equivalent)
  preservesReflectiveScope := by
    intro free bound sort term safe
    exact safe

/-- Identity normalization preserves every ordinary-binder and reflective
support boundary.  Lambda has no authored reflective quote, but carrying the
generic theorem makes the Cost lift iterable without a special case. -/
def lambdaContextualOpenSection :
    ComputableReflectiveFiberContextualSection lambdaIGSLT
      (ReflectionExtension.emptyAdmitted lambdaCalc) where
  normalize := id
  equivalent := fun term => Relation.EqvGen.refl term
  complete := by
    intro free bound sort left right equivalent
    apply Subtype.ext
    exact
      (ReflectiveEquationSemantics.equationEquiv_iff_eq_of_no_generators
        (profile := .empty) (base := defaultBasePremises)
        (language := lambdaCalc) (by rfl) (by rfl) left.1 right.1).mp
        (ReflectiveEquationSemantics.reflectiveOpenPatternEquationSetoid_to_equiv
          equivalent)
  preservesFreeVariableSupport := by
    intro free bound sort term name membership
    exact membership
  normalizeRecontextualizeFree := by
    intro sourceFree targetFree bound sort term preserves
    rfl
  preservesReflectiveSupport := by
    intro free bound sort term support available binderImage supported
    exact supported

/-- Restricting lambda's contextual section recovers its established closed
section exactly. -/
theorem lambdaContextualSection_toCanonical :
    lambdaContextualSection.toComputableCanonicalSection =
      lambdaCanonicalSection := by
  rfl

/-- Substitution is covered directly, so beta needs no residual constructor
in the hereditary continuation closure. -/
def lambdaContinuationRetyping :
    ContinuationRetypingPlan lambdaInteractionCut where
  residualCovered := trivial

/-- Lambda's identity open canonicalizer preserves the exact non-principal
constructor fragment selected by its interaction cut. -/
theorem lambdaContextualOpenSection_preservesWrappedConstructors :
    lambdaContextualOpenSection.PreservesConstructors
      (· ∈ lambdaContinuationRetyping.wrappedLabels) := by
  apply ComputableReflectiveFiberContextualSection.preservesConstructors_id
    lambdaContextualOpenSection
  · intro free bound sort term
    rfl

/-- Lambda's identity open canonicalizer preserves the exact typed
non-principal constructor fragment selected by its interaction cut. -/
theorem lambdaContextualOpenSection_preservesWrappedConstructorTyping :
    lambdaContextualOpenSection.PreservesTypedConstructors
      (· ∈ lambdaContinuationRetyping.wrappedLabels) := by
  apply ComputableReflectiveFiberContextualSection.preservesTypedConstructors_id
    lambdaContextualOpenSection
  · intro free bound sort term
    rfl

/-- Lambda has no bare collection constructor, so none can hide an
interaction principal from declaration-derived constructor support. -/
theorem lambdaBareCollectionConstructorsWrapped :
    ∀ rule ∈ lambdaCalc.terms,
      UsesBareCollection rule →
        rule.label ∈ lambdaContinuationRetyping.wrappedLabels := by
  intro rule membership bare
  change rule ∈ [lambdaCalc.terms[0], lambdaCalc.terms[1]] at membership
  simp only [List.mem_cons, List.not_mem_nil, or_false] at membership
  rcases membership with first | second
  · subst rule
    simp [lambdaCalc, UsesBareCollection] at bare
  · subst rule
    simp [lambdaCalc, UsesBareCollection] at bare

@[simp]
theorem lambda_costBaseApplication_params :
    (costBaseConstructor lambdaInteractionCut lambdaCalc.terms[0]).params =
      [.simple "f" (.base (costBaseSortName "Term")),
        .simple "a" (.base costWrappedSortName)] := by
  simp [costBaseConstructor, costBaseParameter, isSelectedContinuation,
    lambdaCalc, lambdaIGSLT, lambdaInteractivePresentation, lambdaTermSort,
    lambdaValidatedLanguageDef, lambdaInteractionCut, lambdaProgramOperand,
    lambdaEnvironmentOperand, lambdaApplicationConstructor,
    lambdaAbstractionConstructor, mapParameterType, costBaseTypeExpr,
    costWrappedTypeExpr, TypeDecl.plain]

@[simp]
theorem lambda_costBaseAbstraction_params :
    (costBaseConstructor lambdaInteractionCut lambdaCalc.terms[1]).params =
      [.abstraction "body"
        (.arrow (.base costWrappedSortName) (.base costWrappedSortName))] := by
  simp [costBaseConstructor, costBaseParameter, isSelectedContinuation,
    lambdaCalc, lambdaIGSLT, lambdaInteractivePresentation, lambdaTermSort,
    lambdaValidatedLanguageDef, lambdaInteractionCut, lambdaProgramOperand,
    lambdaEnvironmentOperand, lambdaApplicationConstructor,
    lambdaAbstractionConstructor, mapParameterType,
    costWrappedTypeExpr, TypeDecl.plain]

/-- The translated beta source is sorted after the direct argument and
abstraction body are moved into the wrapped fiber. -/
theorem lambdaContinuationRetyping_redexRetypable :
    lambdaContinuationRetyping.RedexRetypable := by
  unfold ContinuationRetypingPlan.RedexRetypable
  simp [lambdaIGSLT, lambdaInteractivePresentation, lambdaBetaRewrite,
    lambdaTermSort, lambdaValidatedLanguageDef, lambdaCalc, mapPattern,
    costBaseLanguageDefSymbolMap, TypeDecl.plain]
  apply HasType.constructor
      (rule := costBaseConstructor lambdaInteractionCut lambdaCalc.terms[0])
  · have membership : lambdaCalc.terms[0] ∈
        lambdaIGSLT.presentation.presentation.language.terms := by
      simp [lambdaIGSLT, lambdaInteractivePresentation,
        lambdaValidatedLanguageDef, lambdaCalc]
    exact lambdaContinuationRetyping.costBaseConstructor_mem_generated
      lambdaCalc.terms[0] membership
  · simp [UsesBareCollection, lambda_costBaseApplication_params]
  · rw [lambda_costBaseApplication_params]
    apply ArgumentsHaveTypes.cons
    · trivial
    · rfl
    · apply HasType.constructor
          (rule := costBaseConstructor lambdaInteractionCut lambdaCalc.terms[1])
      · have membership : lambdaCalc.terms[1] ∈
            lambdaIGSLT.presentation.presentation.language.terms := by
          simp [lambdaIGSLT, lambdaInteractivePresentation,
            lambdaValidatedLanguageDef, lambdaCalc]
        exact lambdaContinuationRetyping.costBaseConstructor_mem_generated
          lambdaCalc.terms[1] membership
      · simp [UsesBareCollection, lambda_costBaseAbstraction_params]
      · rw [lambda_costBaseAbstraction_params]
        apply ArgumentsHaveTypes.cons
        · trivial
        · rfl
        · apply HasType.lambda
          exact HasType.fvar rfl
        · exact .nil
    · apply ArgumentsHaveTypes.cons
      · trivial
      · rfl
      · exact HasType.fvar rfl
      · exact .nil

/-- The exact beta contractum has the wrapped sort in the generated
continuation signature. -/
theorem lambdaContinuationRetyping_wrappable :
    lambdaContinuationRetyping.Wrappable := by
  unfold ContinuationRetypingPlan.Wrappable
  change HasType lambdaContinuationRetyping.generatedLanguage
    lambdaContinuationRetyping.generatedFreeContext []
    (.subst (.fvar "body") (.fvar "arg"))
    (.base costWrappedSortName)
  exact HasType.subst (HasType.fvar rfl) (HasType.fvar rfl)

/-- The lambda control has no static equations, so its Cost stability
obligation is empty. -/
theorem lambdaContinuationRetyping_equationsRetypable :
    EquationsRetypable lambdaContinuationRetyping := by
  intro equation membership
  simp [lambdaIGSLT, lambdaInteractivePresentation,
    lambdaValidatedLanguageDef, lambdaCalc] at membership

/-- The lambda control authors no reflective presentation, so reflective
Cost stability is vacuous. -/
theorem lambdaContinuationRetyping_reflectivePresentationsRetypable :
    ReflectivePresentationsRetypable lambdaContinuationRetyping .empty := by
  intro declaration membership
  simp at membership

/-- The exact `lambdaCalc` definition therefore carries continued interaction
structure. -/
def lambdaCIGSLT : CIGSLT where
  theory := lambdaIGSLT
  reflection := ReflectionExtension.emptyAdmitted lambdaCalc
  cut := lambdaInteractionCut
  openCanonical := lambdaContextualOpenSection
  continuationRetyping := lambdaContinuationRetyping
  bareCollectionConstructorsWrapped :=
    lambdaBareCollectionConstructorsWrapped
  openCanonicalPreservesWrappedConstructorTyping :=
    lambdaContextualOpenSection_preservesWrappedConstructorTyping
  equationsRetypable := lambdaContinuationRetyping_equationsRetypable
  reflectivePresentationsRetypable :=
    lambdaContinuationRetyping_reflectivePresentationsRetypable
  sourceEnvelopeStable := .hole "Term"
  redexRetypable := lambdaContinuationRetyping_redexRetypable
  wrappable := lambdaContinuationRetyping_wrappable

/-- Positive control: the direct application argument is retyped into the
wrapped fiber. -/
theorem lambda_argument_continuation_retyped :
    (costBaseConstructor lambdaInteractionCut lambdaCalc.terms[0]).params[1]? =
      some (.simple "a" (.base costWrappedSortName)) := by
  rw [lambda_costBaseApplication_params]
  rfl

/-- Negative control: the function position remains in the base fiber. -/
theorem lambda_function_position_not_retyped :
    (costBaseConstructor lambdaInteractionCut lambdaCalc.terms[0]).params[0]? =
      some (.simple "f" (.base (costBaseSortName "Term"))) := by
  rw [lambda_costBaseApplication_params]
  rfl

end Mettapedia.GSLT.LanguageDef.LambdaContinuedInteraction
