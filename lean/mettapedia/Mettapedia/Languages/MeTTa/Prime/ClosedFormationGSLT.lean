import Mettapedia.GSLT.LanguageDef.InferenceChecker
import Mettapedia.GSLT.LanguageDef.CalculusLanguageDef

/-!
# Prime closed formation as a rooted GSLT

This definition isolates the closed, environment-free part of Prime type
formation implemented by `prime_form_type`: primitive type symbols and
nondependent arrow telescopes.  Source terms are reified into a small list
algebra before checking.  Named binders, free variables, declared type
constructors, conversion, and environment lookup are outside this fragment and
must remain undetermined rather than being rejected by absence of a rule.

Both positive formation and the one closed negative case in this fragment
(the empty arrow telescope) are explicit judgments.  A native specialization
therefore never turns failed proof search into a negative typing verdict.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.Prime.ClosedFormationGSLT

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef

def termType : TypeDecl := TypeDecl.plain "PrimeClosedTerm"

def termConstructor (head : String) (arity : Nat) : GrammarRule :=
  { label := head
    category := "PrimeClosedTerm"
    params := (List.range arity).map fun index =>
      .simple s!"argument{index}" (.base "PrimeClosedTerm")
    syntaxPattern := [] }

def pType : Pattern := .apply "PType" []
def pDynamic : Pattern := .apply "PDynamic" []
def pAtom : Pattern := .apply "PAtom" []
def pSymbol : Pattern := .apply "PSymbol" []
def pVariable : Pattern := .apply "PVariable" []
def pExpression : Pattern := .apply "PExpression" []
def pGrounded : Pattern := .apply "PGrounded" []
def pNumber : Pattern := .apply "PNumber" []
def pBool : Pattern := .apply "PBool" []
def pString : Pattern := .apply "PString" []
def pError : Pattern := .apply "PError" []
def pNil : Pattern := .apply "PNil" []
def pCons (head tail : Pattern) : Pattern := .apply "PCons" [head, tail]
def pArrow (components : Pattern) : Pattern := .apply "PArrow" [components]

/-! The syntax-to-judgment interpretation is a separate authored component:
it explains how ordinary Prime type atoms enter this language fragment.  Exact
nullary maps cover primitive type symbols; the variadic map lowers a
nonempty source arrow telescope into the fragment's explicit list
algebra.  A compile-time backend may specialize this data, but may not infer
it from `P*` naming conventions. -/

structure SyntaxNullaryMap where
  sourceHead : String
  targetConstructor : String
deriving DecidableEq, Repr

structure SyntaxVariadicListMap where
  sourceHead : String
  minimumArity : Nat
  targetWrapper : String
  targetCons : String
  targetNil : String
deriving DecidableEq, Repr

structure GroundStructuralBinding where
  nullary : List SyntaxNullaryMap
  variadic : SyntaxVariadicListMap
  positiveJudgment : String
  negativeJudgment : String
deriving DecidableEq, Repr

def syntaxBinding : GroundStructuralBinding :=
  { nullary :=
      [ ⟨"Type", "PType"⟩,
        ⟨"%Undefined%", "PDynamic"⟩,
        ⟨"Atom", "PAtom"⟩,
        ⟨"Symbol", "PSymbol"⟩,
        ⟨"Variable", "PVariable"⟩,
        ⟨"Expression", "PExpression"⟩,
        ⟨"Grounded", "PGrounded"⟩,
        ⟨"Number", "PNumber"⟩,
        ⟨"Bool", "PBool"⟩,
        ⟨"String", "PString"⟩,
        ⟨"ErrorType", "PError"⟩ ]
    variadic := ⟨"->", 1, "PArrow", "PCons", "PNil"⟩
    positiveJudgment := "PrimeForm"
    negativeJudgment := "PrimeNotForm" }

def form (type : Pattern) : Pattern := .apply "PrimeForm" [type]
def formComponents (components : Pattern) : Pattern :=
  .apply "PrimeFormComponents" [components]
def notForm (type : Pattern) : Pattern := .apply "PrimeNotForm" [type]

def ruleId (value : String) : RuleId := ⟨value⟩

def primitiveRule (id : String) (type : Pattern) : RuleSchema :=
  { id := ruleId id
    metavariables := []
    premises := []
    conclusion := form type }

def formType : RuleSchema := primitiveRule "prime-form-type" pType
def formDynamic : RuleSchema := primitiveRule "prime-form-dynamic" pDynamic
def formAtom : RuleSchema := primitiveRule "prime-form-atom" pAtom
def formSymbol : RuleSchema := primitiveRule "prime-form-symbol" pSymbol
def formVariable : RuleSchema := primitiveRule "prime-form-variable" pVariable
def formExpression : RuleSchema :=
  primitiveRule "prime-form-expression" pExpression
def formGrounded : RuleSchema := primitiveRule "prime-form-grounded" pGrounded
def formNumber : RuleSchema := primitiveRule "prime-form-number" pNumber
def formBool : RuleSchema := primitiveRule "prime-form-bool" pBool
def formString : RuleSchema := primitiveRule "prime-form-string" pString
def formError : RuleSchema := primitiveRule "prime-form-error" pError

/-- A one-component telescope is nonempty and well formed exactly when its
component is well formed. -/
def formComponentsOne : RuleSchema :=
  { id := ruleId "prime-form-components-one"
    metavariables := [("t", 0)]
    premises := [form (.fvar "t")]
    conclusion := formComponents (pCons (.fvar "t") pNil) }

/-- Longer closed telescopes are checked left-to-right by structural
recursion over their reified component list. -/
def formComponentsCons : RuleSchema :=
  { id := ruleId "prime-form-components-cons"
    metavariables := [("t", 0), ("ts", 0)]
    premises := [form (.fvar "t"), formComponents (.fvar "ts")]
    conclusion := formComponents (pCons (.fvar "t") (.fvar "ts")) }

def formArrow : RuleSchema :=
  { id := ruleId "prime-form-arrow"
    metavariables := [("ts", 0)]
    premises := [formComponents (.fvar "ts")]
    conclusion := form (pArrow (.fvar "ts")) }

/-- Prime rejects an arrow with no result component.  This is an authored
negative judgment, not negation-as-failure. -/
def notFormEmptyArrow : RuleSchema :=
  { id := ruleId "prime-not-form-empty-arrow"
    metavariables := []
    premises := []
    conclusion := notForm (pArrow pNil) }

abbrev definition : CalculusLanguageDef :=
  { name := "prime-closed-formation-v1"
    types := [termType]
    terms :=
      [ termConstructor "PType" 0,
        termConstructor "PDynamic" 0,
        termConstructor "PAtom" 0,
        termConstructor "PSymbol" 0,
        termConstructor "PVariable" 0,
        termConstructor "PExpression" 0,
        termConstructor "PGrounded" 0,
        termConstructor "PNumber" 0,
        termConstructor "PBool" 0,
        termConstructor "PString" 0,
        termConstructor "PError" 0,
        termConstructor "PNil" 0,
        termConstructor "PCons" 2,
        termConstructor "PArrow" 1 ]
    equations := []
    rewrites := []
    judgments :=
      [ { head := "PrimeForm", arity := 1 },
        { head := "PrimeFormComponents", arity := 1 },
        { head := "PrimeNotForm", arity := 1 } ]
    rules :=
      [ formType, formDynamic, formAtom, formSymbol, formVariable,
        formExpression, formGrounded, formNumber, formBool, formString,
        formError, formComponentsOne, formComponentsCons, formArrow,
        notFormEmptyArrow ] }

def language : LanguageDef := definition.toLanguageDef
def calculus := definition.toCalculus

private def hasConstructorArity (name : String) (arity : Nat) : Bool :=
  language.terms.any fun declaration =>
    declaration.label == name && declaration.params.length == arity

private def hasJudgmentArity (name : String) (arity : Nat) : Bool :=
  calculus.judgments.any fun declaration =>
    declaration.head == name && declaration.arity == arity

/-- Internal coherence of the syntax interpretation with the target GSLT.
This validates uniqueness and every target arity; it does not turn an unknown
source head into a negative formation judgment. -/
def syntaxBindingValid : Bool :=
  let sources := syntaxBinding.nullary.map (·.sourceHead)
  sources.eraseDups.length == sources.length &&
  !sources.contains syntaxBinding.variadic.sourceHead &&
  (syntaxBinding.nullary.all fun entry =>
    hasConstructorArity entry.targetConstructor 0) &&
  syntaxBinding.variadic.minimumArity > 0 &&
  hasConstructorArity syntaxBinding.variadic.targetWrapper 1 &&
  hasConstructorArity syntaxBinding.variadic.targetCons 2 &&
  hasConstructorArity syntaxBinding.variadic.targetNil 0 &&
  hasJudgmentArity syntaxBinding.positiveJudgment 1 &&
  hasJudgmentArity syntaxBinding.negativeJudgment 1

theorem language_validate : language.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorOnly language <;>
    simp [language, termType, termConstructor,
      LanguageDef.typeNames, TypeDecl.plain, TermParam.typeExpr,
      TypeExpr.baseNames]

theorem definition_valid : definition.isValid = true := by
  have hvalidate : definition.toLanguageDef.validate = [] := by
    simpa [definition, language] using language_validate
  unfold CalculusLanguageDef.isValid CalculusLanguageDef.hasValidLocalRules
  rw [hvalidate]
  simp [definition,
    CalculusLanguageDef.ruleIds, CalculusLanguageDef.judgmentSignatureValid,
    CalculusLanguageDef.judgmentHeads, CalculusLanguageDef.conversionDeclarationValid,
    CalculusLanguageDef.lookupJudgment?, RuleSchema.isValidIn,
    RuleSchema.isLocallyValid, RuleSchema.metavariableNames,
    RuleSchema.occurrences, RuleSchema.patterns,
    patternMetavariableOccurrencesAt, patternsMetavariableOccurrencesAt,
    patternHasNoCollectionRest, patternsHaveNoCollectionRest,
    CalculusLanguageDef.judgmentSchemaValid, fixedConstructorsValid,
    fixedConstructorListsValid, languageHasConstructorArity,
    Pattern.isWellScoped, Pattern.isWellScopedAt,
    Pattern.isWellScopedListAt, Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList, Pattern.zipHead,
    Pattern.mapHead, Pattern.evalHead, termType, termConstructor,
    formType, formDynamic, formAtom, formSymbol, formVariable,
    formExpression, formGrounded, formNumber, formBool, formString,
    formError, formComponentsOne, formComponentsCons, formArrow,
    notFormEmptyArrow, primitiveRule, form, formComponents, notForm,
    pType, pDynamic, pAtom, pSymbol, pVariable, pExpression, pGrounded,
    pNumber, pBool, pString, pError, pNil, pCons, pArrow, ruleId]
  decide

theorem syntax_binding_valid : syntaxBindingValid = true := by
  decide

/-- The closed formation fragment as one GSLT.  This does not promote the
fragment to a final definition of Prime; it only totalizes the declarations
authored in this deliberately bounded module. -/
def totalTheory : Mettapedia.GSLT.GSLT :=
  definition.toGSLTOfNoEquations definition_valid rfl

theorem totalTheory_Term : totalTheory.Term = (Pattern ⊕ List Pattern) := by
  unfold totalTheory CalculusLanguageDef.toGSLTOfNoEquations
  rfl

def checked : ValidatedCalculusLanguageDef := ⟨definition, definition_valid⟩

private def ruleInstance (id : String) (arguments : List Pattern := []) :
    RuleInstance :=
  { ruleId := ruleId id, arguments }

def numberProof : RawProof :=
  .node (ruleInstance "prime-form-number") []

def arrowProof : RawProof :=
  .node (ruleInstance "prime-form-arrow" [pCons pNumber (pCons pString pNil)])
    [ .node (ruleInstance "prime-form-components-cons"
        [pNumber, pCons pString pNil])
        [ numberProof,
          .node (ruleInstance "prime-form-components-one" [pString])
            [.node (ruleInstance "prime-form-string") []] ] ]

def arrowGoal : Pattern := form (pArrow (pCons pNumber (pCons pString pNil)))

def emptyArrowProof : RawProof :=
  .node (ruleInstance "prime-not-form-empty-arrow") []

def emptyArrowGoal : Pattern := notForm (pArrow pNil)

theorem number_accepted : checkRaw checked (form pNumber) numberProof = true := by
  simp [checkRaw, checkRawChildren, checked, definition,
    numberProof, ruleInstance, formNumber, primitiveRule, form, pNumber,
    formType, formDynamic, formAtom, formSymbol, formVariable,
    formExpression, formGrounded, formBool, formString, formError,
    formComponentsOne, formComponentsCons, formArrow, notFormEmptyArrow,
    instantiateRule?, CalculusLanguageDef.lookupRule?, argumentsValidAt,
    RuleSchema.sideConditionsHold, instantiateSchema?,
    instantiateSchemaAt?, instantiateSchemas?, instantiateSchemasAt?,
    ruleId]

theorem arrow_accepted : checkRaw checked arrowGoal arrowProof = true := by
  simp [checkRaw, checkRawChildren, checked, definition,
    arrowGoal, arrowProof, numberProof, ruleInstance, formArrow,
    formComponentsCons, formComponentsOne, formNumber, formString,
    primitiveRule, form, formComponents, pArrow, pCons, pNil, pNumber,
    pString, formType, formDynamic, formAtom, formSymbol, formVariable,
    formExpression, formGrounded, formBool, formError, notFormEmptyArrow,
    instantiateRule?, CalculusLanguageDef.lookupRule?, argumentsValidAt,
    argumentValidAt, RuleSchema.sideConditionsHold, instantiateSchema?,
    instantiateSchemaAt?, instantiateSchemas?, instantiateSchemasAt?,
    lookupArgumentAt?, ruleId, Pattern.isGroundAt, Pattern.isGroundListAt,
    Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList]

theorem empty_arrow_refutation_accepted :
    checkRaw checked emptyArrowGoal emptyArrowProof = true := by
  simp [checkRaw, checkRawChildren, checked, definition,
    emptyArrowGoal, emptyArrowProof, ruleInstance, notFormEmptyArrow,
    notForm, pArrow, pNil, formType, formDynamic, formAtom, formSymbol,
    formVariable, formExpression, formGrounded, formNumber, formBool,
    formString, formError, formComponentsOne, formComponentsCons, formArrow,
    primitiveRule, form, formComponents, instantiateRule?,
    CalculusLanguageDef.lookupRule?, argumentsValidAt, RuleSchema.sideConditionsHold,
    instantiateSchema?, instantiateSchemaAt?, instantiateSchemas?,
    instantiateSchemasAt?, ruleId]

/-- Unknown nominal type forms are deliberately not rejected by the closed
fragment.  A fabricated primitive proof cannot be replayed for them. -/
def unknownNominal : Pattern := .apply "PNominal" []

theorem unknown_nominal_not_established_by_number_proof :
    checkRaw checked (form unknownNominal) numberProof = false := by
  simp [checkRaw, checkRawChildren, checked, definition,
    unknownNominal, numberProof, ruleInstance, formNumber, primitiveRule,
    form, pNumber, formType, formDynamic, formAtom, formSymbol, formVariable,
    formExpression, formGrounded, formBool, formString, formError,
    formComponentsOne, formComponentsCons, formArrow, notFormEmptyArrow,
    instantiateRule?, CalculusLanguageDef.lookupRule?, argumentsValidAt,
    RuleSchema.sideConditionsHold, instantiateSchema?, instantiateSchemaAt?,
    instantiateSchemas?, instantiateSchemasAt?, ruleId]

def exportedDefinition : CalculusLanguageDef := definition
def sampleFormGoal : Pattern := arrowGoal
def sampleFormProof : RawProof := arrowProof
def sampleRefuteGoal : Pattern := emptyArrowGoal
def sampleRefuteProof : RawProof := emptyArrowProof

end Mettapedia.Languages.MeTTa.Prime.ClosedFormationGSLT
