import Mettapedia.Languages.MeTTa.HE.Spec.Type
import Mettapedia.GSLT.LanguageDef.CalculusExtension
import Mettapedia.GSLT.LanguageDef.CalculusLanguageDef

/-!
# HE typing consistency core as an authored GSLT

This module presents the certificate-free consistency core used by HE typing as
an independently meaningful inference calculus.  Its semantic reference is the
published, executable-independent `Spec.Type.TypeMatchRel`; neither the
presentation nor its semantic theorem depends on an executable HE interpreter.

The present coverage is deliberately exact and finite:

* ordinary reflexive consistency;
* `%Undefined%` consistency in both directions, retaining its dynamic edge;
* `Atom` as the expected top type, retaining its directed top edge; and
* recursively well-formed `List` and unary-arrow type syntax.

Structural congruence between distinct compound types, meta-type staging,
normalization, refinement checking, and whole-term synthesis remain outside
this first presentation.  Consequently, generated runtime metadata must label
this source as an authored fragment, never as a complete presentation of the
native HE checker.
-/

namespace Mettapedia.Languages.MeTTa.HE.TypeSystemGSLT

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.CalculusExtension
open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE.Spec.Type
open Mettapedia.Languages.MeTTa.HE.Spec.Match.Merge

/-! ## Independent semantic core -/

/-- Closed type shapes covered by this presentation.  Arrow arguments retain
their authored order and the result is stored separately. -/
inductive CoreType where
  | number
  | string
  | bool
  | dynamic
  | atom
  | list (element : CoreType)
  | arrow (argument result : CoreType)
  deriving Repr

/-- The edge reason is semantic data: dynamic and top edges may not be
silently upgraded to exact evidence. -/
inductive CoreEdge where
  | exact
  | dynamic
  | top
  deriving Repr, DecidableEq

def CoreType.toAtom : CoreType → Atom
  | .number => .symbol "Number"
  | .string => .symbol "String"
  | .bool => .symbol "Bool"
  | .dynamic => Atom.undefinedType
  | .atom => Atom.atomType
  | .list element => .expression [.symbol "List", element.toAtom]
  | .arrow argument result =>
      .expression [.symbol "->", argument.toAtom, result.toAtom]

/-- Only the two top-level special types precede exact equality in the native
classification order.  Nested occurrences do not prevent exact equality of
the complete compound type. -/
def CoreType.ordinaryRoot : CoreType → Bool
  | .dynamic | .atom => false
  | _ => true

def CoreType.nonDynamicRoot : CoreType → Bool
  | .dynamic => false
  | _ => true

/-- Independent meaning of the three covered edge classes. -/
inductive CoreConsistency : CoreType → CoreType → CoreEdge → Prop where
  | exact (type : CoreType) (ordinary : type.ordinaryRoot = true) :
      CoreConsistency type type .exact
  | dynamicLeft (type : CoreType) :
      CoreConsistency .dynamic type .dynamic
  | dynamicRight (type : CoreType) :
      CoreConsistency type .dynamic .dynamic
  | topRight (type : CoreType) (nonDynamic : type.nonDynamicRoot = true) :
      CoreConsistency type .atom .top

private theorem mergeEmptyEmpty :
    MergeRel equalityGroundedSemantic Bindings.empty Bindings.empty
      Bindings.empty := by
  exact .mk (by rfl) .nil

/-- Every covered closed type matches itself in the independent published HE
matching relation. -/
theorem CoreType.matchRel_refl (type : CoreType) :
    MatchRel equalityGroundedSemantic type.toAtom type.toAtom
      Bindings.empty := by
  cases type with
  | number =>
      simpa [CoreType.toAtom] using
        (MatchRel.symSym (p := equalityGroundedSemantic)
          "Number" semanticLoopFree_empty)
  | string =>
      simpa [CoreType.toAtom] using
        (MatchRel.symSym (p := equalityGroundedSemantic)
          "String" semanticLoopFree_empty)
  | bool =>
      simpa [CoreType.toAtom] using
        (MatchRel.symSym (p := equalityGroundedSemantic)
          "Bool" semanticLoopFree_empty)
  | dynamic =>
      simpa [CoreType.toAtom, Atom.undefinedType] using
        (MatchRel.symSym (p := equalityGroundedSemantic)
          "%Undefined%" semanticLoopFree_empty)
  | atom =>
      simpa [CoreType.toAtom, Atom.atomType] using
        (MatchRel.symSym (p := equalityGroundedSemantic)
          "Atom" semanticLoopFree_empty)
  | list element =>
      simp only [CoreType.toAtom]
      apply MatchRel.expression (p := equalityGroundedSemantic)
      · exact MatchListAccRel.cons
          (MatchRel.symSym (p := equalityGroundedSemantic)
            "List" semanticLoopFree_empty) mergeEmptyEmpty
          (MatchListAccRel.cons element.matchRel_refl mergeEmptyEmpty
            MatchListAccRel.nil)
      · exact semanticLoopFree_empty
  | arrow argument result =>
      simp only [CoreType.toAtom]
      apply MatchRel.expression (p := equalityGroundedSemantic)
      · exact MatchListAccRel.cons
          (MatchRel.symSym (p := equalityGroundedSemantic)
            "->" semanticLoopFree_empty) mergeEmptyEmpty
          (MatchListAccRel.cons argument.matchRel_refl mergeEmptyEmpty
            (MatchListAccRel.cons result.matchRel_refl mergeEmptyEmpty
              MatchListAccRel.nil))
      · exact semanticLoopFree_empty
termination_by sizeOf type

private theorem ordinary_not_undefined {type : CoreType}
    (ordinary : type.ordinaryRoot = true) :
    type.toAtom ≠ Atom.undefinedType := by
  cases type <;> simp_all [CoreType.ordinaryRoot, CoreType.toAtom,
    Atom.undefinedType]

private theorem ordinary_not_atom {type : CoreType}
    (ordinary : type.ordinaryRoot = true) :
    type.toAtom ≠ Atom.atomType := by
  cases type <;> simp_all [CoreType.ordinaryRoot, CoreType.toAtom,
    Atom.atomType]

/-- The authored semantic core is sound for the independent HE type-matching
relation.  The output bindings are existential because NIK preserves the
guest judgment rather than imposing one binding representation. -/
theorem CoreConsistency.toTypeMatchRel
    {actual expected : CoreType} {edge : CoreEdge}
    (consistent : CoreConsistency actual expected edge) :
    ∃ output, TypeMatchRel actual.toAtom expected.toAtom
      Bindings.empty output :=
  match consistent with
  | .exact core ordinary =>
      ⟨Bindings.empty, TypeMatchRel.structural
        (ordinary_not_undefined ordinary)
        (ordinary_not_atom ordinary)
        (ordinary_not_undefined ordinary)
        (ordinary_not_atom ordinary)
        (CoreType.matchRel_refl core) mergeEmptyEmpty⟩
  | .dynamicLeft core =>
      ⟨Bindings.empty,
        TypeMatchRel.undefinedLeft (CoreType.toAtom core) Bindings.empty⟩
  | .dynamicRight core =>
      ⟨Bindings.empty,
        TypeMatchRel.undefinedRight (CoreType.toAtom core) Bindings.empty⟩
  | .topRight core _ =>
      ⟨Bindings.empty,
        TypeMatchRel.atomRight (CoreType.toAtom core) Bindings.empty⟩

/-- Positive semantic canary: an ordinary base type is exact. -/
theorem semantic_number_exact :
    CoreConsistency .number .number .exact :=
  .exact .number rfl

/-- Positive semantic canary: gradual consistency retains its dynamic edge. -/
theorem semantic_number_dynamic :
    CoreConsistency .number .dynamic .dynamic :=
  .dynamicRight .number

/-- Positive semantic canary: `Atom` is a directed expected top type. -/
theorem semantic_number_top :
    CoreConsistency .number .atom .top :=
  .topRight .number rfl

/-- Negative semantic canary: two distinct ordinary base types have no edge in
this core. -/
theorem semantic_number_string_refuted (edge : CoreEdge) :
    ¬CoreConsistency .number .string edge := by
  intro derivation
  cases derivation

/-! ## Authored finite-Horn presentation -/

def termType : TypeDecl := TypeDecl.plain "HeTypeTerm"

def termConstructor (head : String) (arity : Nat) : GrammarRule :=
  { label := head
    category := "HeTypeTerm"
    params := (List.range arity).map fun index =>
      .simple s!"argument{index}" (.base "HeTypeTerm")
    syntaxPattern := [] }

def tNumber : Pattern := .apply "HTNumber" []
def tString : Pattern := .apply "HTString" []
def tBool : Pattern := .apply "HTBool" []
def tDynamic : Pattern := .apply "HTDynamic" []
def tAtom : Pattern := .apply "HTAtom" []
def tList (element : Pattern) : Pattern := .apply "HTList" [element]
def tArrow (argument result : Pattern) : Pattern :=
  .apply "HTArrow" [argument, result]

def edgeExact : Pattern := .apply "HEdgeExact" []
def edgeDynamic : Pattern := .apply "HEdgeDynamic" []
def edgeTop : Pattern := .apply "HEdgeTop" []

def isType (type : Pattern) : Pattern := .apply "HEType" [type]
def isNonDynamic (type : Pattern) : Pattern :=
  .apply "HENonDynamic" [type]
def isOrdinaryRoot (type : Pattern) : Pattern :=
  .apply "HEOrdinaryRoot" [type]
def consistent (actual expected edge : Pattern) : Pattern :=
  .apply "HEConsistent" [actual, expected, edge]

def ruleId (value : String) : RuleId := ⟨value⟩

def factRule (id : String) (conclusion : Pattern) : RuleSchema :=
  { id := ruleId id, metavariables := [], premises := [], conclusion }

def unaryRule (id variableName : String) (premises : List Pattern)
    (conclusion : Pattern) : RuleSchema :=
  { id := ruleId id
    metavariables := [(variableName, 0)]
    premises
    conclusion }

def typeNumber : RuleSchema := factRule "type-number" (isType tNumber)
def typeString : RuleSchema := factRule "type-string" (isType tString)
def typeBool : RuleSchema := factRule "type-bool" (isType tBool)
def typeDynamic : RuleSchema := factRule "type-dynamic" (isType tDynamic)
def typeAtom : RuleSchema := factRule "type-atom" (isType tAtom)
def typeList : RuleSchema :=
  unaryRule "type-list" "t" [isType (.fvar "t")]
    (isType (tList (.fvar "t")))
def typeArrow : RuleSchema :=
  { id := ruleId "type-arrow"
    metavariables := [("a", 0), ("r", 0)]
    premises := [isType (.fvar "a"), isType (.fvar "r")]
    conclusion := isType (tArrow (.fvar "a") (.fvar "r")) }

def nonDynamicNumber : RuleSchema :=
  factRule "non-dynamic-number" (isNonDynamic tNumber)
def nonDynamicString : RuleSchema :=
  factRule "non-dynamic-string" (isNonDynamic tString)
def nonDynamicBool : RuleSchema :=
  factRule "non-dynamic-bool" (isNonDynamic tBool)
def nonDynamicAtom : RuleSchema :=
  factRule "non-dynamic-atom" (isNonDynamic tAtom)
def nonDynamicList : RuleSchema :=
  unaryRule "non-dynamic-list" "t" [isType (.fvar "t")]
    (isNonDynamic (tList (.fvar "t")))
def nonDynamicArrow : RuleSchema :=
  { id := ruleId "non-dynamic-arrow"
    metavariables := [("a", 0), ("r", 0)]
    premises := [isType (.fvar "a"), isType (.fvar "r")]
    conclusion := isNonDynamic (tArrow (.fvar "a") (.fvar "r")) }

def ordinaryNumber : RuleSchema :=
  factRule "ordinary-number" (isOrdinaryRoot tNumber)
def ordinaryString : RuleSchema :=
  factRule "ordinary-string" (isOrdinaryRoot tString)
def ordinaryBool : RuleSchema :=
  factRule "ordinary-bool" (isOrdinaryRoot tBool)
def ordinaryList : RuleSchema :=
  unaryRule "ordinary-list" "t" [isType (.fvar "t")]
    (isOrdinaryRoot (tList (.fvar "t")))
def ordinaryArrow : RuleSchema :=
  { id := ruleId "ordinary-arrow"
    metavariables := [("a", 0), ("r", 0)]
    premises := [isType (.fvar "a"), isType (.fvar "r")]
    conclusion := isOrdinaryRoot (tArrow (.fvar "a") (.fvar "r")) }

def consistentExact : RuleSchema :=
  unaryRule "consistent-exact" "t" [isOrdinaryRoot (.fvar "t")]
    (consistent (.fvar "t") (.fvar "t") edgeExact)
def consistentDynamicLeft : RuleSchema :=
  unaryRule "consistent-dynamic-left" "t" [isType (.fvar "t")]
    (consistent tDynamic (.fvar "t") edgeDynamic)
def consistentDynamicRight : RuleSchema :=
  unaryRule "consistent-dynamic-right" "t" [isType (.fvar "t")]
    (consistent (.fvar "t") tDynamic edgeDynamic)
def consistentTopRight : RuleSchema :=
  unaryRule "consistent-top-right" "t" [isNonDynamic (.fvar "t")]
    (consistent (.fvar "t") tAtom edgeTop)

/-- One authored definition; object syntax and proof calculus are projections
of this record rather than parallel sources. -/
abbrev definition : CalculusLanguageDef :=
  { name := "he-typing-consistency-core"
    types := [termType]
    terms :=
      [ termConstructor "HTNumber" 0,
        termConstructor "HTString" 0,
        termConstructor "HTBool" 0,
        termConstructor "HTDynamic" 0,
        termConstructor "HTAtom" 0,
        termConstructor "HTList" 1,
        termConstructor "HTArrow" 2,
        termConstructor "HEdgeExact" 0,
        termConstructor "HEdgeDynamic" 0,
        termConstructor "HEdgeTop" 0 ]
    equations := []
    rewrites := []
    judgments :=
      [ { head := "HEType", arity := 1 },
        { head := "HENonDynamic", arity := 1 },
        { head := "HEOrdinaryRoot", arity := 1 },
        { head := "HEConsistent", arity := 3 } ]
    rules :=
      [ typeNumber, typeString, typeBool, typeDynamic, typeAtom,
        typeList, typeArrow,
        nonDynamicNumber, nonDynamicString, nonDynamicBool, nonDynamicAtom,
        nonDynamicList, nonDynamicArrow,
        ordinaryNumber, ordinaryString, ordinaryBool, ordinaryList,
        ordinaryArrow,
        consistentExact, consistentDynamicLeft, consistentDynamicRight,
        consistentTopRight ] }

abbrev language : LanguageDef := definition.toLanguageDef
abbrev calculus : InferenceExtension.ProofCalculus := definition.toCalculus
abbrev presentation : Presentation := definition.toNested

theorem language_validate : language.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorOnly language <;>
    simp [termType, termConstructor, LanguageDef.typeNames, TypeDecl.plain,
      TermParam.typeExpr, TypeExpr.baseNames]

theorem presentation_valid : presentation.isValidV2 = true := by
  have hvalidate : presentation.language.validate = [] := by
    simpa [presentation] using language_validate
  unfold Presentation.isValidV2 Presentation.isValidV1
  rw [hvalidate]
  simp [presentation, Presentation.ruleIds,
    Presentation.judgmentSignatureValid, Presentation.judgmentHeads,
    Presentation.conversionDeclarationValid, Presentation.lookupJudgment?,
    RuleSchema.isValidIn, RuleSchema.isValidV1,
    RuleSchema.metavariableNames, RuleSchema.occurrences, RuleSchema.patterns,
    patternMetavariableOccurrencesAt, patternsMetavariableOccurrencesAt,
    patternHasNoCollectionRest, patternsHaveNoCollectionRest,
    Presentation.judgmentSchemaValid, fixedConstructorsValid,
    fixedConstructorListsValid, languageHasConstructorArity,
    Pattern.isWellScoped, Pattern.isWellScopedAt, Pattern.isWellScopedListAt,
    Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList, Pattern.zipHead, Pattern.mapHead,
    Pattern.evalHead, termType, termConstructor, factRule, unaryRule,
    typeNumber, typeString, typeBool, typeDynamic, typeAtom, typeList, typeArrow,
    nonDynamicNumber, nonDynamicString, nonDynamicBool, nonDynamicAtom,
    nonDynamicList, nonDynamicArrow,
    ordinaryNumber, ordinaryString, ordinaryBool, ordinaryList,
    ordinaryArrow, consistentExact, consistentDynamicLeft,
    consistentDynamicRight, consistentTopRight,
    isType, isNonDynamic, isOrdinaryRoot, consistent,
    tNumber, tString, tBool, tDynamic, tAtom, tList, tArrow,
    edgeExact, edgeDynamic, edgeTop, ruleId]
  decide

abbrev checked : ValidatedPresentation := definition.checked presentation_valid

theorem constructor_count : language.terms.length = 10 := by decide
theorem rule_count : calculus.rules.length = 22 := by decide

def typeNumberProof : RawProof :=
  .node { ruleId := ruleId "type-number", arguments := [] } []

def dynamicRightProof : RawProof :=
  .node
    { ruleId := ruleId "consistent-dynamic-right"
      arguments := [tNumber] }
    [typeNumberProof]

/-- Positive checker canary corresponding to `semantic_number_dynamic`. -/
theorem check_number_dynamic :
    checkRaw checked (consistent tNumber tDynamic edgeDynamic)
      dynamicRightProof = true := by
  simp [checkRaw, checkRawChildren, checked, dynamicRightProof,
    typeNumberProof, typeNumber, typeString, typeBool, typeDynamic, typeAtom,
    typeList, typeArrow, nonDynamicNumber, nonDynamicString, nonDynamicBool,
    nonDynamicAtom, nonDynamicList, nonDynamicArrow, ordinaryNumber,
    ordinaryString, ordinaryBool, ordinaryList, ordinaryArrow,
    consistentExact, consistentDynamicLeft, consistentDynamicRight,
    consistentTopRight, factRule, unaryRule, instantiateRule?,
    Presentation.lookupRule?, argumentsValidAt, argumentValidAt,
    RuleSchema.sideConditionsHold, instantiateSchema?, instantiateSchemaAt?,
    instantiateSchemas?, instantiateSchemasAt?, lookupArgumentAt?, isType,
    isNonDynamic, isOrdinaryRoot, consistent, tNumber, tDynamic,
    edgeDynamic, ruleId, Pattern.isGroundAt, Pattern.isGroundListAt,
    Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList]

def ordinaryNumberProof : RawProof :=
  .node { ruleId := ruleId "ordinary-number", arguments := [] } []

def exactNumberProof : RawProof :=
  .node { ruleId := ruleId "consistent-exact", arguments := [tNumber] }
    [ordinaryNumberProof]

/-- Positive checker canary corresponding to `semantic_number_exact`. -/
theorem check_number_exact :
    checkRaw checked (consistent tNumber tNumber edgeExact)
      exactNumberProof = true := by
  simp [checkRaw, checkRawChildren, checked, exactNumberProof,
    ordinaryNumberProof, typeNumber, typeString, typeBool, typeDynamic,
    typeAtom, typeList, typeArrow, nonDynamicNumber, nonDynamicString,
    nonDynamicBool, nonDynamicAtom, nonDynamicList, nonDynamicArrow,
    ordinaryNumber, ordinaryString, ordinaryBool, ordinaryList,
    ordinaryArrow, consistentExact, consistentDynamicLeft,
    consistentDynamicRight, consistentTopRight, factRule, unaryRule,
    instantiateRule?, Presentation.lookupRule?, argumentsValidAt,
    argumentValidAt, RuleSchema.sideConditionsHold, instantiateSchema?,
    instantiateSchemaAt?, instantiateSchemas?, instantiateSchemasAt?,
    lookupArgumentAt?, isType, isNonDynamic, isOrdinaryRoot, consistent,
    tNumber, edgeExact, ruleId, Pattern.isGroundAt,
    Pattern.isGroundListAt, Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList]

def nonDynamicNumberProof : RawProof :=
  .node { ruleId := ruleId "non-dynamic-number", arguments := [] } []

def topNumberProof : RawProof :=
  .node { ruleId := ruleId "consistent-top-right", arguments := [tNumber] }
    [nonDynamicNumberProof]

/-- Positive checker canary corresponding to `semantic_number_top`. -/
theorem check_number_top :
    checkRaw checked (consistent tNumber tAtom edgeTop)
      topNumberProof = true := by
  simp [checkRaw, checkRawChildren, checked, topNumberProof,
    nonDynamicNumberProof, typeNumber, typeString, typeBool, typeDynamic,
    typeAtom, typeList, typeArrow, nonDynamicNumber, nonDynamicString,
    nonDynamicBool, nonDynamicAtom, nonDynamicList, nonDynamicArrow,
    ordinaryNumber, ordinaryString, ordinaryBool, ordinaryList,
    ordinaryArrow, consistentExact, consistentDynamicLeft,
    consistentDynamicRight, consistentTopRight, factRule, unaryRule,
    instantiateRule?, Presentation.lookupRule?, argumentsValidAt,
    argumentValidAt, RuleSchema.sideConditionsHold, instantiateSchema?,
    instantiateSchemaAt?, instantiateSchemas?, instantiateSchemasAt?,
    lookupArgumentAt?, isType, isNonDynamic, isOrdinaryRoot, consistent,
    tNumber, tAtom, edgeTop, ruleId, Pattern.isGroundAt,
    Pattern.isGroundListAt, Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList]

/-- Negative checker canary: the exact rule cannot counterfeit equality of
distinct ordinary base types. -/
theorem check_number_string_rejects_exact_proof :
    checkRaw checked (consistent tNumber tString edgeExact)
      exactNumberProof = false := by
  simp [checkRaw, checkRawChildren, checked, exactNumberProof,
    ordinaryNumberProof, typeNumber, typeString, typeBool, typeDynamic,
    typeAtom, typeList, typeArrow, nonDynamicNumber, nonDynamicString,
    nonDynamicBool, nonDynamicAtom, nonDynamicList, nonDynamicArrow,
    ordinaryNumber, ordinaryString, ordinaryBool, ordinaryList,
    ordinaryArrow, consistentExact, consistentDynamicLeft,
    consistentDynamicRight, consistentTopRight, factRule, unaryRule,
    instantiateRule?, Presentation.lookupRule?, argumentsValidAt,
    argumentValidAt, RuleSchema.sideConditionsHold, instantiateSchema?,
    instantiateSchemaAt?, instantiateSchemas?, instantiateSchemasAt?,
    lookupArgumentAt?, isType, isNonDynamic, isOrdinaryRoot, consistent,
    tNumber, tString, edgeExact, ruleId, Pattern.isGroundAt,
    Pattern.isGroundListAt, Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList]

/-- Export root for the finite-Horn renderer. -/
def corePresentation : Presentation := presentation

end Mettapedia.Languages.MeTTa.HE.TypeSystemGSLT
