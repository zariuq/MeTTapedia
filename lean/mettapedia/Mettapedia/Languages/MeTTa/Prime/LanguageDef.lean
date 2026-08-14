import Mettapedia.Languages.MeTTa.Prime.Language
import Mettapedia.GSLT.LanguageDef.ExtensionComposition
import Mettapedia.GSLT.LanguageDef.ReflectionExtension
import Mettapedia.GSLT.LanguageDef.StructuralCategory

/-!
# The authored five-field definition of Prime

`Prime.Language` gives the semantic GSLT nucleus.  This module gives its
serializable five-field presentation and proves that the MeTTa Zero
presentation includes structurally.

Prime adds structural names, quote/drop equality, revision-keyed Need requests,
and explicit receipt values.  Relation implementations, grounding, and the
reflective interpretation remain coGSLT-authored extension fibres.  They are
not hidden fields of the five-field record.
-/

namespace Mettapedia.Languages.MeTTa.Prime.LanguageDef

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.Extension
open Mettapedia.GSLT.LanguageDef.ExtensionComposition
open Mettapedia.GSLT.LanguageDef.LogicExtension
open Mettapedia.GSLT.LanguageDef.OracleExtension
open Mettapedia.GSLT.LanguageDef.ReflectionExtension
open Mettapedia.Languages.MeTTa
open Mettapedia.OSLF.MeTTaIL.Reflection
open Mettapedia.OSLF.MeTTaIL.Syntax

/-! ## New Prime declarations -/

def nameType : TypeDecl := TypeDecl.plain "PrimeName"
def receiptType : TypeDecl := TypeDecl.plain "PrimeReceipt"

private def constructor (label category : String)
    (parameters : List (String × TypeExpr)) : GrammarRule :=
  { label
    category
    params := parameters.map fun parameter =>
      .simple parameter.1 parameter.2
    syntaxPattern := [] }

def unitConstructor : GrammarRule :=
  constructor "prime-unit" "Atom" []

def quoteConstructor : GrammarRule :=
  constructor "prime-quote" "PrimeName" [("term", .base "Atom")]

def dropConstructor : GrammarRule :=
  constructor "prime-drop" "Atom" [("name", .base "PrimeName")]

/-- Explicitly request evaluation of structurally quoted syntax.  Plain
quotation remains inert; this constructor is the authored crossing from
reflection into lazy evaluation. -/
def evaluateNameConstructor : GrammarRule :=
  constructor "prime-evaluate-name" "Process"
    [("space", .base "Space"), ("name", .base "PrimeName")]

def needRequestConstructor : GrammarRule :=
  constructor "prime-need" "Process"
    [("space", .base "Space"), ("subject", .base "Atom")]

def needAnswerConstructor : GrammarRule :=
  constructor "prime-need-answer" "Process"
    [("answer", .base "Atom"), ("receipt", .base "PrimeReceipt")]

/-- A serializable Need key.  The revision component is supplied by the
particular Prime model; the subject remains ordinary reflective syntax. -/
def needKeyConstructor : GrammarRule :=
  constructor "prime-need-key" "Atom"
    [("revision", .base "Atom"), ("subject", .base "Atom")]

/-- The request dependency recovered when a receipt is transitively closed. -/
def requestDependencyConstructor : GrammarRule :=
  constructor "prime-request-dependency" "Atom"
    [("key", .base "Atom")]

/-- A rule result depends on the equation atom selected from the space. -/
def spaceAtomDependencyConstructor : GrammarRule :=
  constructor "prime-space-atom-dependency" "Atom"
    [("key", .base "Atom"), ("atom", .base "Atom")]

/-- A grounded result records the explicit capability result that caused it. -/
def capabilityDependencyConstructor : GrammarRule :=
  constructor "prime-capability-dependency" "Atom"
    [("key", .base "Atom"), ("result", .base "Atom")]

/-- Open-world retention records that no interpretation was available. -/
def inertDependencyConstructor : GrammarRule :=
  constructor "prime-inert-dependency" "Atom"
    [("key", .base "Atom")]

def receiptConstructor : GrammarRule :=
  constructor "prime-receipt" "PrimeReceipt" [("root", .base "Atom")]

/- These projection-transparent forms let downstream structural proofs use
the public Zero declarations without depending on its private constructor
helper. -/
@[simp] private theorem zeroEquationConstructor :
    MeTTaZero.equationConstructor =
      { label := "=", category := "Atom",
        params := [.simple "left" (.base "Atom"),
          .simple "right" (.base "Atom")], syntaxPattern := [] } :=
  rfl

@[simp] private theorem zeroQueryRequestConstructor :
    MeTTaZero.queryRequestConstructor =
      { label := "zero-query", category := "Process",
        params := [.simple "space" (.base "Space"),
          .simple "pattern" (.base "Atom"),
          .simple "template" (.base "Atom")], syntaxPattern := [] } :=
  rfl

@[simp] private theorem zeroQueryAnswerConstructor :
    MeTTaZero.queryAnswerConstructor =
      { label := "zero-query-answer", category := "Process",
        params := [.simple "answer" (.base "Atom")], syntaxPattern := [] } :=
  rfl

@[simp] private theorem zeroEvaluationRequestConstructor :
    MeTTaZero.evaluationRequestConstructor =
      { label := "zero-evaluate", category := "Process",
        params := [.simple "space" (.base "Space"),
          .simple "subject" (.base "Atom")], syntaxPattern := [] } :=
  rfl

@[simp] private theorem zeroEvaluationAnswerConstructor :
    MeTTaZero.evaluationAnswerConstructor =
      { label := "zero-evaluate-answer", category := "Process",
        params := [.simple "answer" (.base "Atom")], syntaxPattern := [] } :=
  rfl

def quoteDropEquation : Equation :=
  { name := "prime-quote-drop"
    typeContext := [("name", .base "PrimeName")]
    premises := []
    left := .apply "prime-quote" [.apply "prime-drop" [.fvar "name"]]
    right := .fvar "name" }

def needRewrite : RewriteRule :=
  { name := "prime-need"
    typeContext :=
      [("space", .base "Space"), ("subject", .base "Atom"),
       ("answer", .base "Atom"), ("receipt", .base "PrimeReceipt")]
    premises :=
      [.relationQuery "PrimeNeed"
        [.fvar "space", .fvar "subject", .fvar "answer", .fvar "receipt"]]
    left := .apply "prime-need" [.fvar "space", .fvar "subject"]
    right := .apply "prime-need-answer" [.fvar "answer", .fvar "receipt"] }

/-- The authored crossing from extensional evaluation into Need. -/
def evaluationDemandRewrite : RewriteRule :=
  { name := "prime-evaluation-demand"
    typeContext :=
      [("space", .base "Space"), ("subject", .base "Atom")]
    premises := []
    left := MeTTaZero.evaluationRequestPattern (.fvar "space") (.fvar "subject")
    right := .apply "prime-need" [.fvar "space", .fvar "subject"] }

/-- A Need answer returns to the exact Zero evaluation observation. -/
def needReturnRewrite : RewriteRule :=
  { name := "prime-need-return"
    typeContext :=
      [("answer", .base "Atom"), ("receipt", .base "PrimeReceipt")]
    premises := []
    left := .apply "prime-need-answer" [.fvar "answer", .fvar "receipt"]
    right := MeTTaZero.evaluationAnswerPattern (.fvar "answer") }

/-- Evaluating a quoted term enters the same Need route.  The nested quote is
part of the rewrite pattern, so arbitrary names are not unquoted by accident. -/
def reflectedDemandRewrite : RewriteRule :=
  { name := "prime-reflected-demand"
    typeContext :=
      [("space", .base "Space"), ("subject", .base "Atom")]
    premises := []
    left := .apply "prime-evaluate-name"
      [.fvar "space", .apply "prime-quote" [.fvar "subject"]]
    right := .apply "prime-need" [.fvar "space", .fvar "subject"] }

/-! ## The five-field presentation -/

/-- Prime extends, rather than replaces, the exact Zero declarations. -/
def language : LanguageDef :=
  { name := "metta-prime-nucleus"
    types := MeTTaZero.language.types ++ [nameType, receiptType]
    terms := MeTTaZero.language.terms ++
      [unitConstructor, quoteConstructor, dropConstructor, evaluateNameConstructor,
       needRequestConstructor, needAnswerConstructor, needKeyConstructor,
       requestDependencyConstructor, spaceAtomDependencyConstructor,
       capabilityDependencyConstructor, inertDependencyConstructor,
       receiptConstructor]
    equations := MeTTaZero.language.equations ++ [quoteDropEquation]
    rewrites := MeTTaZero.language.rewrites ++
      [evaluationDemandRewrite, needRewrite, needReturnRewrite,
       reflectedDemandRewrite] }

set_option maxHeartbeats 1000000 in
attribute [-simp] isolated Fin.Fin1.eq_one
  LO.LogicalConnective.AndOrClosed.falsum
  LO.LogicalConnective.AndOrClosed.verum in
theorem language_validate : language.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorEquationsAndRewrites
  case htypes =>
    simp [language, MeTTaZero.language, MeTTaZero.definition, nameType,
      receiptType, MeTTaZero.atomType, MeTTaZero.spaceType,
      MeTTaZero.processType, MeTTaZero.alternativesType,
      LanguageDef.typeNames, TypeDecl.plain]
  case hconstructors =>
    simp [language, MeTTaZero.language, MeTTaZero.definition,
      unitConstructor, quoteConstructor, dropConstructor,
      evaluateNameConstructor, needRequestConstructor, needAnswerConstructor,
      needKeyConstructor, requestDependencyConstructor,
      spaceAtomDependencyConstructor, capabilityDependencyConstructor,
      inertDependencyConstructor, receiptConstructor, constructor,
      zeroEquationConstructor, zeroQueryRequestConstructor,
      zeroQueryAnswerConstructor, zeroEvaluationRequestConstructor,
      zeroEvaluationAnswerConstructor]
  case hequations =>
    simp [language, MeTTaZero.language, MeTTaZero.definition,
      quoteDropEquation]
  case hrewrites =>
    simp [language, MeTTaZero.language, MeTTaZero.definition,
      MeTTaZero.queryRewrite, MeTTaZero.evaluationRewrite,
      evaluationDemandRewrite, needRewrite, needReturnRewrite,
      reflectedDemandRewrite]
  case hcategory =>
    intro term membership
    change term ∈ MeTTaZero.language.terms ++
      [unitConstructor, quoteConstructor, dropConstructor,
       evaluateNameConstructor, needRequestConstructor, needAnswerConstructor,
       needKeyConstructor, requestDependencyConstructor,
       spaceAtomDependencyConstructor, capabilityDependencyConstructor,
       inertDependencyConstructor, receiptConstructor] at membership
    rw [List.mem_append] at membership
    rcases membership with baseMember | addedMember
    · have baseCategory := LanguageDef.termCategory_mem_of_validate_eq_nil
        MeTTaZero.language MeTTaZero.language_validate term baseMember
      have extendedCategory :
          term.category ∈ MeTTaZero.language.typeNames ++
            ["PrimeName", "PrimeReceipt"] :=
        List.mem_append_left _ baseCategory
      simpa [language, nameType, receiptType, LanguageDef.typeNames,
        TypeDecl.plain] using extendedCategory
    · simp only [List.mem_cons, List.mem_nil_iff, or_false] at addedMember
      rcases addedMember with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl <;>
        simp_all [language, MeTTaZero.language, MeTTaZero.definition,
          nameType, receiptType, unitConstructor, quoteConstructor,
          dropConstructor, evaluateNameConstructor, needRequestConstructor,
          needAnswerConstructor, needKeyConstructor,
          requestDependencyConstructor, spaceAtomDependencyConstructor,
          capabilityDependencyConstructor, inertDependencyConstructor,
          receiptConstructor, constructor, MeTTaZero.atomType,
          MeTTaZero.spaceType, MeTTaZero.processType,
          MeTTaZero.alternativesType, LanguageDef.typeNames, TypeDecl.plain]
  case hparams =>
    intro term termMember parameter parameterMember typeName typeNameMember
    change term ∈ MeTTaZero.language.terms ++
      [unitConstructor, quoteConstructor, dropConstructor,
       evaluateNameConstructor, needRequestConstructor, needAnswerConstructor,
       needKeyConstructor, requestDependencyConstructor,
       spaceAtomDependencyConstructor, capabilityDependencyConstructor,
       inertDependencyConstructor, receiptConstructor] at termMember
    rw [List.mem_append] at termMember
    rcases termMember with baseMember | addedMember
    · have baseName := LanguageDef.termParam_baseName_mem_of_validate_eq_nil
        MeTTaZero.language MeTTaZero.language_validate term baseMember
        parameter parameterMember typeName typeNameMember
      have extendedName :
          typeName ∈ MeTTaZero.language.typeNames ++
            ["PrimeName", "PrimeReceipt"] :=
        List.mem_append_left _ baseName
      simpa [language, nameType, receiptType, LanguageDef.typeNames,
        TypeDecl.plain] using extendedName
    · simp only [List.mem_cons, List.mem_nil_iff, or_false] at addedMember
      rcases addedMember with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl <;>
        simp_all [language, MeTTaZero.language, MeTTaZero.definition,
          nameType, receiptType, unitConstructor, quoteConstructor,
          dropConstructor, evaluateNameConstructor, needRequestConstructor,
          needAnswerConstructor, needKeyConstructor,
          requestDependencyConstructor, spaceAtomDependencyConstructor,
          capabilityDependencyConstructor, inertDependencyConstructor,
          receiptConstructor, constructor, MeTTaZero.atomType,
          MeTTaZero.spaceType, MeTTaZero.processType,
          MeTTaZero.alternativesType, LanguageDef.typeNames, TypeDecl.plain,
          TermParam.typeExpr, TypeExpr.baseNames]
      all_goals
        rcases parameterMember with rfl | rfl <;>
          simp_all [TypeExpr.baseNames]
  case hsyntax =>
    intro term membership
    change term ∈ MeTTaZero.language.terms ++
      [unitConstructor, quoteConstructor, dropConstructor,
       evaluateNameConstructor, needRequestConstructor, needAnswerConstructor,
       needKeyConstructor, requestDependencyConstructor,
       spaceAtomDependencyConstructor, capabilityDependencyConstructor,
       inertDependencyConstructor, receiptConstructor] at membership
    rw [List.mem_append] at membership
    rcases membership with baseMember | addedMember
    · change term ∈
        [MeTTaZero.equationConstructor, MeTTaZero.queryRequestConstructor,
         MeTTaZero.queryAnswerConstructor,
         MeTTaZero.evaluationRequestConstructor,
         MeTTaZero.evaluationAnswerConstructor] at baseMember
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at baseMember
      rcases baseMember with rfl | rfl | rfl | rfl | rfl <;>
        exact Or.inl rfl
    · simp only [List.mem_cons, List.mem_nil_iff, or_false] at addedMember
      rcases addedMember with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl <;>
        exact Or.inl rfl
  case hequationValid =>
    intro equation membership
    have equationEq : equation = quoteDropEquation := by
      simpa [language, MeTTaZero.language, MeTTaZero.definition] using membership
    subst equation
    simp [language, MeTTaZero.language, MeTTaZero.definition,
      quoteDropEquation, LanguageDef.validateEquation,
      LanguageDef.validatePatternConstructors,
      LanguageDef.validateRulePatterns, LanguageDef.patternFvarNames,
      LanguageDef.patternBinderNames, Pattern.constructorRefs,
      Pattern.constructorRefsList, Pattern.freeFvarNames,
      Pattern.isWellScoped, Pattern.isWellScopedAt,
      Pattern.isWellScopedListAt, nameType, receiptType,
      MeTTaZero.atomType, MeTTaZero.spaceType, MeTTaZero.processType,
      MeTTaZero.alternativesType, unitConstructor, quoteConstructor,
      dropConstructor, evaluateNameConstructor, needRequestConstructor,
      needAnswerConstructor, needKeyConstructor,
      requestDependencyConstructor, spaceAtomDependencyConstructor,
      capabilityDependencyConstructor, inertDependencyConstructor,
      receiptConstructor, constructor, LanguageDef.typeNames, TypeDecl.plain,
      TypeExpr.baseNames]
  case hrewriteValid =>
    intro rewrite membership
    change rewrite ∈
      [MeTTaZero.queryRewrite, MeTTaZero.evaluationRewrite,
       evaluationDemandRewrite, needRewrite, needReturnRewrite,
       reflectedDemandRewrite] at membership
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at membership
    rcases membership with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [language, MeTTaZero.language, MeTTaZero.definition,
        MeTTaZero.queryRewrite, MeTTaZero.evaluationRewrite,
        MeTTaZero.queryRequestPattern, MeTTaZero.queryAnswerPattern,
        MeTTaZero.evaluationRequestPattern,
        MeTTaZero.evaluationAnswerPattern, MeTTaZero.metavariable,
        evaluationDemandRewrite, needRewrite, needReturnRewrite,
        reflectedDemandRewrite, LanguageDef.validateRewrite,
        LanguageDef.validatePatternConstructors,
        LanguageDef.validateRulePatterns, LanguageDef.patternFvarNames,
        LanguageDef.patternBinderNames, LanguageDef.premisePatterns,
        LanguageDef.premiseFvarNames,
        LanguageDef.premiseProducedFvarNames,
        LanguageDef.premiseForAllParams, Pattern.constructorRefs,
        Pattern.constructorRefsList, Pattern.freeFvarNames,
        Pattern.isWellScoped, Pattern.isWellScopedAt,
        Pattern.isWellScopedListAt, nameType, receiptType,
        MeTTaZero.atomType, MeTTaZero.spaceType, MeTTaZero.processType,
        MeTTaZero.alternativesType, unitConstructor, quoteConstructor,
        dropConstructor, evaluateNameConstructor, needRequestConstructor,
        needAnswerConstructor, needKeyConstructor,
        requestDependencyConstructor, spaceAtomDependencyConstructor,
        capabilityDependencyConstructor, inertDependencyConstructor,
        receiptConstructor, constructor, LanguageDef.typeNames, TypeDecl.plain,
        TypeExpr.baseNames]

/-- The authored three-rule route corresponding to Prime's lazy semantic
path: enter Need, compute one admitted answer, then return to the extensional
observation. -/
def lazyEvaluationRoute : List RewriteRule :=
  [evaluationDemandRewrite, needRewrite, needReturnRewrite]

@[simp] theorem lazyEvaluationRoute_names :
    lazyEvaluationRoute.map RewriteRule.name =
      ["prime-evaluation-demand", "prime-need", "prime-need-return"] :=
  rfl

/-- Every leg of the lazy route is a rewrite of the five-field root. -/
theorem lazyEvaluationRoute_mem_language :
    ∀ rewrite ∈ lazyEvaluationRoute, rewrite ∈ language.rewrites := by
  intro rewrite member
  simp only [lazyEvaluationRoute, List.mem_cons, List.mem_nil_iff,
    or_false] at member
  rcases member with rfl | rfl | rfl
  all_goals simp [language]

/-- The reflected crossing is likewise authored in `R`. -/
theorem reflectedDemandRewrite_mem_language :
    reflectedDemandRewrite ∈ language.rewrites := by
  simp [language]

/-- Negative canary: inert quotation alone is not the source of the reflected
demand rule; an explicit `prime-evaluate-name` request is required. -/
theorem quoted_term_not_reflected_demand_source (term : Pattern) :
    Pattern.apply "prime-quote" [term] ≠ reflectedDemandRewrite.left := by
  simp [reflectedDemandRewrite]

/-- The authored-presentation specification region is the existing category
of validated five-field definitions and structural declaration maps. -/
abbrev PresentationRegion := ValidatedLanguageDef

/-- Today's authored Prime presentation is one point of the presentation region;
it is not the definition of every admissible future Prime presentation. -/
def currentPrimePresentation : PresentationRegion :=
  ⟨language, language_validate⟩

/-- Today's authored query-first Zero presentation is another named point. -/
def currentZeroPresentation : PresentationRegion :=
  ⟨MeTTaZero.language, MeTTaZero.language_validate⟩

/-- The identity symbol action includes every authored Zero declaration into
Prime.  This states preservation at the level of all five fields, not merely
at the level of names or observed examples. -/
def currentZeroToPrimePresentation :
    StructuralMorphism currentZeroPresentation currentPrimePresentation where
  symbols := PresentationSymbols.id
  mapsTypes declaration membership := by
    rw [mapTypeDecl_id]
    change List.Mem declaration MeTTaZero.language.types at membership
    change List.Mem declaration language.types
    exact List.mem_append_left [nameType, receiptType] membership
  mapsTerms declaration membership := by
    rw [mapGrammarRule_id]
    change List.Mem declaration MeTTaZero.language.terms at membership
    change List.Mem declaration language.terms
    exact List.mem_append_left
      [unitConstructor, quoteConstructor, dropConstructor,
         evaluateNameConstructor, needRequestConstructor, needAnswerConstructor,
         needKeyConstructor, requestDependencyConstructor,
         spaceAtomDependencyConstructor, capabilityDependencyConstructor,
         inertDependencyConstructor,
         receiptConstructor]
        membership
  mapsEquations declaration membership := by
    rw [Mettapedia.GSLT.LanguageDef.mapEquation_id]
    change List.Mem declaration MeTTaZero.language.equations at membership
    change List.Mem declaration language.equations
    exact List.mem_append_left [quoteDropEquation] membership
  mapsRewrites declaration membership := by
    rw [mapRewriteRule_id]
    change List.Mem declaration MeTTaZero.language.rewrites at membership
    change List.Mem declaration language.rewrites
    exact List.mem_append_left
      [evaluationDemandRewrite, needRewrite, needReturnRewrite,
       reflectedDemandRewrite] membership

/-- Prime's new quotation constructor witnesses that the inclusion is proper:
there is no identity-symbol structural map erasing Prime back to Zero. -/
theorem no_identity_symbol_retraction :
    ¬ ∃ retraction :
        StructuralMorphism currentPrimePresentation currentZeroPresentation,
      retraction.symbols = PresentationSymbols.id := by
  rintro ⟨retraction, symbols⟩
  have quoteMember : List.Mem quoteConstructor language.terms := by
    change List.Mem quoteConstructor
      (MeTTaZero.language.terms ++
        [unitConstructor, quoteConstructor, dropConstructor,
         evaluateNameConstructor, needRequestConstructor, needAnswerConstructor,
         needKeyConstructor, requestDependencyConstructor,
         spaceAtomDependencyConstructor, capabilityDependencyConstructor,
         inertDependencyConstructor,
         receiptConstructor])
    exact List.mem_append_right _ (by simp)
  have mapped := retraction.mapsTerms quoteConstructor quoteMember
  have mapped' : List.Mem quoteConstructor MeTTaZero.language.terms := by
    rw [symbols] at mapped
    simpa only [mapGrammarRule_id, currentZeroPresentation] using mapped
  have labelMember :
      List.Mem quoteConstructor.label
        (MeTTaZero.language.terms.map GrammarRule.label) :=
    List.mem_map_of_mem mapped'
  have absent : ¬ List.Mem "prime-quote"
      ["=", "zero-query", "zero-query-answer", "zero-evaluate",
       "zero-evaluate-answer"] := by
    intro member
    change "prime-quote" ∈
      ["=", "zero-query", "zero-query-answer", "zero-evaluate",
       "zero-evaluate-answer"] at member
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at member
    rcases member with equal | equal | equal | equal | equal
    · exact (by decide : "prime-quote" ≠ "=") equal
    · exact (by decide : "prime-quote" ≠ "zero-query") equal
    · exact (by decide : "prime-quote" ≠ "zero-query-answer") equal
    · exact (by decide : "prime-quote" ≠ "zero-evaluate") equal
    · exact (by decide : "prime-quote" ≠ "zero-evaluate-answer") equal
  apply absent
  simpa [MeTTaZero.language, MeTTaZero.definition, quoteConstructor, constructor]
    using labelMember

/-! ## CoGSLT-authored interpretation fibres -/

def needRelation : LogicDeclaration :=
  .relation
    { name := "PrimeNeed"
      argTypes :=
        [.base "Space", .base "Atom", .base "Atom", .base "PrimeReceipt"] }

def logicDeclarations : LogicProgram :=
  MeTTaZero.logicDeclarations ++ [needRelation]

def admittedLogic : AdmittedProgram language :=
  ⟨logicDeclarations, by decide⟩

/-- Prime retains Zero's explicit grounding capability boundary. -/
def admittedOracles : AdmittedLibrary language :=
  ⟨[MeTTaZero.groundApplyDeclaration], by decide⟩

/-- Structural quotation/drop is selected through the generic reflection
extension rather than through a special evaluator flag. -/
def reflectionPresentation : ReflectivePresentationDecl :=
  { name := "prime-structural-names"
    processSort := "Atom"
    nameSort := "PrimeName"
    quoteConstructor := "prime-quote"
    dropConstructor := "prime-drop"
    parallelCollection := .hashBag
    parallelUnitConstructor := "prime-unit"
    quoteDropEquation := "prime-quote-drop" }

def admittedReflection : AdmittedProfile language :=
  ⟨{ presentations := [reflectionPresentation] }, by decide⟩

/-! ## One compositional authoring language for the Prime fibres -/

/-- Raw logic declarations are authored by their law-bearing declaration
GSLT. -/
def logicAuthoringLayer : CompositionalLayer LanguageDef :=
  CompositionalLayer.ofCodec LanguageDef logicCodec

/-- Raw grounding interfaces are authored independently. -/
def oracleAuthoringLayer : CompositionalLayer LanguageDef :=
  CompositionalLayer.ofCodec LanguageDef oracleCodec

/-- Raw reflection declarations are likewise authored by their own GSLT. -/
def reflectionAuthoringLayer : CompositionalLayer LanguageDef :=
  CompositionalLayer.ofCodec LanguageDef reflectionCodec

/-- Prime's three interpretation fibres form one nested product of generic
compositional elaborations.  No Prime-specific composition law is introduced. -/
def authoredExtensionComposition : CompositionalLayer LanguageDef :=
  logicAuthoringLayer.product
    (oracleAuthoringLayer.product reflectionAuthoringLayer)

/-- The actual mixed authoring GSLT for Prime's logic, grounding, and
reflection declarations. -/
def authoredExtensionGSLT : GSLT :=
  (authoredExtensionComposition.system language).authoring.theory

/-- Logic authoring remains a faithful component of the mixed theory. -/
def logicAuthoringEmbedding :
    GSLT.Embedding logicDocumentGSLT authoredExtensionGSLT :=
  GSLT.compositeDocumentsLeft _ _

/-- Oracle authoring embeds through the right product and then its left
component. -/
def oracleAuthoringEmbedding :
    GSLT.Embedding oracleDocumentGSLT authoredExtensionGSLT :=
  GSLT.Embedding.comp
    (GSLT.compositeDocumentsRight _ _)
    (GSLT.compositeDocumentsLeft _ _)

/-- Reflection authoring embeds through the right product and then its right
component. -/
def reflectionAuthoringEmbedding :
    GSLT.Embedding reflectionDocumentGSLT authoredExtensionGSLT :=
  GSLT.Embedding.comp
    (GSLT.compositeDocumentsRight _ _)
    (GSLT.compositeDocumentsRight _ _)

abbrev RawExtensions :=
  LogicProgram × (List OracleDecl × List ReflectionDeclaration)

abbrev AdmittedExtensions (base : LanguageDef) :=
  AdmittedProgram base × (AdmittedLibrary base × AdmittedProfile base)

private def elaborateRawExtensions? (base : LanguageDef)
    (source : (authoredExtensionComposition.system base).authoring.theory.Term) :
    Option (authoredExtensionComposition.Fiber base) :=
  authoredExtensionComposition.elaborate base source

private theorem elaborateRawExtensions?_equation (base : LanguageDef)
    {source target :
      (authoredExtensionComposition.system base).authoring.theory.Term}
    (equivalent :
      (authoredExtensionComposition.system base).authoring.theory.Equiv
        source target) :
    elaborateRawExtensions? base source =
      elaborateRawExtensions? base target :=
  (authoredExtensionComposition.system base).elaboration.equation equivalent

private theorem elaborateRawExtensions?_rewrite (base : LanguageDef)
    {source target :
      (authoredExtensionComposition.system base).authoring.theory.Term}
    (step : (authoredExtensionComposition.system base).authoring.theory.Step
      source target) :
    elaborateRawExtensions? base source =
      elaborateRawExtensions? base target :=
  (authoredExtensionComposition.system base).elaboration.rewrite step

@[simp] private theorem elaborateRawExtensions?_quote (base : LanguageDef)
    (raw : authoredExtensionComposition.Fiber base) :
    elaborateRawExtensions? base
        (authoredExtensionComposition.quote base raw) = some raw := by
  unfold elaborateRawExtensions?
  exact authoredExtensionComposition.elaborate_quote base raw

private def elaborateExtensions? (base : LanguageDef)
    (source : (authoredExtensionComposition.system base).authoring.theory.Term) :
    Option (AdmittedExtensions base) := do
  let raw ← elaborateRawExtensions? base source
  let program := raw.1
  if programAdmitted : LogicProgram.AdmissibleFor program base = true then
    let library := raw.2.1
    if libraryAdmitted : LibraryAdmissible base library = true then
      let profile := profileOfDeclarations raw.2.2
      if profileAdmitted : ReflectionExtension.validate base profile = [] then
        some (⟨program, programAdmitted⟩,
          (⟨library, libraryAdmitted⟩, ⟨profile, profileAdmitted⟩))
      else
        none
    else
      none
  else
    none

private def quoteExtensions (base : LanguageDef)
    (extensions : AdmittedExtensions base) :
    (authoredExtensionComposition.system base).authoring.theory.Term :=
  authoredExtensionComposition.quote base
    (extensions.1.1,
      (extensions.2.1.1, profileDeclarations extensions.2.2.1))

@[simp] private theorem elaborateExtensions?_quoteExtensions
    (base : LanguageDef) (extensions : AdmittedExtensions base) :
    elaborateExtensions? base (quoteExtensions base extensions) =
      some extensions := by
  rcases extensions with
    ⟨⟨program, programAdmitted⟩,
      ⟨⟨library, libraryAdmitted⟩, ⟨profile, profileAdmitted⟩⟩⟩
  unfold elaborateExtensions? quoteExtensions elaborateRawExtensions?
  rw [authoredExtensionComposition.elaborate_quote]
  simp [programAdmitted, libraryAdmitted, profileAdmitted,
    profileOfDeclarations_declarations]

/-- Contextual admission of all three fibres is itself one coGSLT layer.
Raw composition is total; the language-indexed validators are applied only
after the mixed source has elaborated. -/
def extensionLayer : CoGSLTLayer LanguageDef where
  Fiber := AdmittedExtensions
  sourceGSLT := fun base =>
    (authoredExtensionComposition.system base).authoring.theory
  elaborate := elaborateExtensions?
  quote := quoteExtensions
  elaborate_quote := elaborateExtensions?_quoteExtensions
  elaborate_equation := by
    intro base source target equivalent
    unfold elaborateExtensions?
    rw [elaborateRawExtensions?_equation base equivalent]
  elaborate_rewrite := by
    intro base source target step
    unfold elaborateExtensions?
    rw [elaborateRawExtensions?_rewrite base step]

/-- The actual Prime fibre declarations round-trip together through one term
of the mixed authoring GSLT. -/
theorem authored_extensions_roundTrip :
    extensionLayer.elaborate language
        (extensionLayer.quote language
          (admittedLogic, (admittedOracles, admittedReflection))) =
      some (admittedLogic, (admittedOracles, admittedReflection)) :=
  extensionLayer.elaborate_quote language
    (admittedLogic, (admittedOracles, admittedReflection))

/-- Attaching all authored Prime fibres preserves the exact five-field root. -/
@[simp] theorem extensions_erase_to_language :
    extensionLayer.erase
        (extensionLayer.attach language
          (admittedLogic, (admittedOracles, admittedReflection))) =
      language :=
  rfl

@[simp] theorem logic_erases_to_language :
    LogicExtension.layer.erase
        (LogicExtension.layer.attach language admittedLogic) = language :=
  rfl

@[simp] theorem oracles_erase_to_language :
    OracleExtension.layer.erase
        (OracleExtension.layer.attach language admittedOracles) = language :=
  rfl

@[simp] theorem reflection_erases_to_language :
    ReflectionExtension.layer.erase
        (ReflectionExtension.layer.attach language admittedReflection) = language :=
  rfl

/-- A profile that names an absent quote/drop equation fails closed. -/
theorem missing_reflection_equation_rejected :
    ReflectionExtension.validate language
      { presentations :=
          [{ reflectionPresentation with
             quoteDropEquation := "missing-prime-quote-drop" }] } ≠ [] := by
  decide

end Mettapedia.Languages.MeTTa.Prime.LanguageDef
