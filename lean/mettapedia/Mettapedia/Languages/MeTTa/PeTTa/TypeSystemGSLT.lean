import Mettapedia.GSLT.LanguageDef.CalculusExtension
import Mettapedia.GSLT.LanguageDef.CalculusLanguageDef

/-!
# PeTTa typecheck-v2 type system as a rooted GSLT (stage 1: core)

This module defines the type system of PeTTa's `typecheck-v2` branch
(reference revision `e038e4d`, repository `trueagi-io/PeTTa`) in one flat
`CalculusLanguageDef`: the five object-language fields followed by the
judgments and rules.  Its `toExtended` view proves that those last fields are
authored by `calculusSyntaxGSLT`, while `toGSLT` gives the whole definition one
carrier, one equation relation, and one reduction relation.  The generic V2
checker contains no branch for this fixture; every acceptance and rejection
below is decided by the authored definition alone.

Provenance discipline: each rule's doc-comment cites the reference clause it
was extracted from (paths are relative to the reference repository at the
pinned revision).  The prose companion is CeTTa's
`docs/petta_type_system_spec.md`, which carries the full provenance tables.

Stage-1 scope notes (deliberate, tracked deltas — not oversights):
- Literals are represented by one witness constructor per base type
  (`VNum`, `VStr`, `VTrue`, `VFalse`); the C realization covers the full
  literal domains with native tests (`value_checks.pl:497-499`).
- Tagged-tuple types and the arrow arity check of `runtime_type_ok`
  (`value_checks.pl:505,508-514`) are stage-1.1 extensions.
- The relation presented here is CONSISTENCY (gradual-typing sense), not
  unification: the wildcard rules succeed in both directions and no rule
  composes consistency through the wildcard.  See the
  `consistent_*_accepts` / `non_transitivity_candidate_*` theorems.
-/

namespace Mettapedia.Languages.MeTTa.PeTTa.TypeSystemGSLT

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.InferenceExtension
open Mettapedia.GSLT.LanguageDef.CalculusExtension
open Mettapedia.GSLT.LanguageDef.ExtensionComposition

/-- Single carrier sort: types, mode atoms, and witness values live in one
abstract term algebra, exactly as the reference manipulates them as untyped
Prolog terms. -/
def termType : TypeDecl := TypeDecl.plain "PtTerm"

def termConstructor (head : String) (arity : Nat) : GrammarRule :=
  { label := head
    category := "PtTerm"
    params := (List.range arity).map fun index =>
      .simple s!"argument{index}" (.base "PtTerm")
    syntaxPattern := [] }

/-! ## Type-language constructors (`type_lang.pl`; declaration kinds
`decl_store.pl:137/170/202`) -/

def tNum : Pattern := .apply "TNum" []
def tStr : Pattern := .apply "TStr" []
def tBool : Pattern := .apply "TBool" []
/-- The dynamic type `%Undefined%` (wildcard; `type_lang.pl:15`). -/
def tUndefined : Pattern := .apply "TUndefined" []
def tNil : Pattern := .apply "TTNil" []
def tCons (head tail : Pattern) : Pattern := .apply "TTCons" [head, tail]
/-- Untagged union `(| ...)` over a type list (`type_lang.pl:27-29`). -/
def tUnion (members : Pattern) : Pattern := .apply "TUnion" [members]
/-- Mode-indexed arrow (`flags_arrows.pl:72-92`). -/
def tArrow (mode args ret : Pattern) : Pattern :=
  .apply "TArrow" [mode, args, ret]
/-- Generative brand over a representation (`decl_store.pl:137`,
`type_lang.pl:23`). -/
def tBrand (name repr : Pattern) : Pattern := .apply "TBrand" [name, repr]
def tList (elem : Pattern) : Pattern := .apply "TList" [elem]

def mPlain : Pattern := .apply "MPlain" []
def mDet : Pattern := .apply "MDet" []
def mSemidet : Pattern := .apply "MSemidet" []
def mNondet : Pattern := .apply "MNondet" []

/-! ## Consistency-edge reasons.  One named reason per edge, mirroring the
independently articulated doctrine in CeTTa's `he_typing.h`: the dynamic
edge is what makes the relation deliberately non-transitive. -/

def edgeExact : Pattern := .apply "EdgeExact" []
def edgeStructural : Pattern := .apply "EdgeStructural" []
def edgeDynamic : Pattern := .apply "EdgeDynamic" []

/-! ## Witness values (representative literals; nominal brand names reuse
the same algebra) -/

def vNum : Pattern := .apply "VNum" []
def vStr : Pattern := .apply "VStr" []
def vTrue : Pattern := .apply "VTrue" []
def vFalse : Pattern := .apply "VFalse" []
def vNil : Pattern := .apply "VNil" []
def vCons (head tail : Pattern) : Pattern := .apply "VCons" [head, tail]
def brandA : Pattern := .apply "BrandA" []
def brandB : Pattern := .apply "BrandB" []

/-! ## Judgment applications -/

def consistent (actual expected edge : Pattern) : Pattern :=
  .apply "Consistent" [actual, expected, edge]
def consistentList (actuals expecteds : Pattern) : Pattern :=
  .apply "ConsistentList" [actuals, expecteds]
def unionMember (member members : Pattern) : Pattern :=
  .apply "UnionMember" [member, members]
def valueHasType (value type : Pattern) : Pattern :=
  .apply "ValueHasType" [value, type]
def guardPasses (value type : Pattern) : Pattern :=
  .apply "GuardPasses" [value, type]

def ruleId (value : String) : RuleId := ⟨value⟩

/-! ## Consistency rules (`type_unify`, `type_lang.pl:17-39`) -/

/-- Syntactic identity fallback and the nominal-atom clause
(`type_lang.pl:31,39`): the shared metavariable forces both sides equal. -/
def consistentRefl : RuleSchema :=
  { id := ruleId "consistent-refl"
    metavariables := [("t", 0)]
    premises := []
    conclusion := consistent (.fvar "t") (.fvar "t") edgeExact }

/-- Wildcard on the left (`type_lang.pl:24`): the gradual axis. -/
def consistentDynLeft : RuleSchema :=
  { id := ruleId "consistent-dyn-left"
    metavariables := [("t", 0)]
    premises := []
    conclusion := consistent tUndefined (.fvar "t") edgeDynamic }

/-- Wildcard on the right (`type_lang.pl:24`). -/
def consistentDynRight : RuleSchema :=
  { id := ruleId "consistent-dyn-right"
    metavariables := [("t", 0)]
    premises := []
    conclusion := consistent (.fvar "t") tUndefined edgeDynamic }

/-- Union on the right (`type_lang.pl:29`): some member is consistent. -/
def consistentUnionRight : RuleSchema :=
  { id := ruleId "consistent-union-right"
    metavariables := [("a", 0), ("m", 0), ("ms", 0), ("e", 0)]
    premises :=
      [ unionMember (.fvar "m") (.fvar "ms"),
        consistent (.fvar "a") (.fvar "m") (.fvar "e") ]
    conclusion := consistent (.fvar "a") (tUnion (.fvar "ms")) edgeStructural }

/-- Union on the left (`type_lang.pl:27`). -/
def consistentUnionLeft : RuleSchema :=
  { id := ruleId "consistent-union-left"
    metavariables := [("b", 0), ("m", 0), ("ms", 0), ("e", 0)]
    premises :=
      [ unionMember (.fvar "m") (.fvar "ms"),
        consistent (.fvar "m") (.fvar "b") (.fvar "e") ]
    conclusion := consistent (tUnion (.fvar "ms")) (.fvar "b") edgeStructural }

/-- Brands are generative-nominal: consistency is identity of the brand
name; representations are irrelevant at this relation
(`type_lang.pl:23`; erasure lives in the dynamic judgment). -/
def consistentBrand : RuleSchema :=
  { id := ruleId "consistent-brand"
    metavariables := [("n", 0), ("r", 0), ("s", 0)]
    premises := []
    conclusion :=
      consistent (tBrand (.fvar "n") (.fvar "r"))
        (tBrand (.fvar "n") (.fvar "s")) edgeExact }

/-- Componentwise arrow consistency with identical mode discipline
(`type_lang.pl:34`). -/
def consistentArrow : RuleSchema :=
  { id := ruleId "consistent-arrow"
    metavariables :=
      [("m", 0), ("as", 0), ("bs", 0), ("r", 0), ("s", 0), ("e", 0)]
    premises :=
      [ consistentList (.fvar "as") (.fvar "bs"),
        consistent (.fvar "r") (.fvar "s") (.fvar "e") ]
    conclusion :=
      consistent (tArrow (.fvar "m") (.fvar "as") (.fvar "r"))
        (tArrow (.fvar "m") (.fvar "bs") (.fvar "s")) edgeStructural }

/-- Same-length componentwise lists (`type_lang.pl:34,38`). -/
def consistentListNil : RuleSchema :=
  { id := ruleId "consistent-list-nil"
    metavariables := []
    premises := []
    conclusion := consistentList tNil tNil }

def consistentListCons : RuleSchema :=
  { id := ruleId "consistent-list-cons"
    metavariables :=
      [("a", 0), ("b", 0), ("as", 0), ("bs", 0), ("e", 0)]
    premises :=
      [ consistent (.fvar "a") (.fvar "b") (.fvar "e"),
        consistentList (.fvar "as") (.fvar "bs") ]
    conclusion :=
      consistentList (tCons (.fvar "a") (.fvar "as"))
        (tCons (.fvar "b") (.fvar "bs")) }

/-! ## Union membership -/

def unionMemberHere : RuleSchema :=
  { id := ruleId "union-member-here"
    metavariables := [("t", 0), ("ts", 0)]
    premises := []
    conclusion := unionMember (.fvar "t") (tCons (.fvar "t") (.fvar "ts")) }

def unionMemberThere : RuleSchema :=
  { id := ruleId "union-member-there"
    metavariables := [("t", 0), ("u", 0), ("ts", 0)]
    premises := [unionMember (.fvar "t") (.fvar "ts")]
    conclusion := unionMember (.fvar "t") (tCons (.fvar "u") (.fvar "ts")) }

/-! ## Dynamic judgment (`runtime_type_ok`, `value_checks.pl:493-520`) -/

/-- Native fast path (`value_checks.pl:497`). -/
def hasTypeNum : RuleSchema :=
  { id := ruleId "has-type-num"
    metavariables := []
    premises := []
    conclusion := valueHasType vNum tNum }

/-- Native fast path (`value_checks.pl:498`). -/
def hasTypeStr : RuleSchema :=
  { id := ruleId "has-type-str"
    metavariables := []
    premises := []
    conclusion := valueHasType vStr tStr }

/-- Native fast path (`value_checks.pl:499`). -/
def hasTypeTrue : RuleSchema :=
  { id := ruleId "has-type-true"
    metavariables := []
    premises := []
    conclusion := valueHasType vTrue tBool }

def hasTypeFalse : RuleSchema :=
  { id := ruleId "has-type-false"
    metavariables := []
    premises := []
    conclusion := valueHasType vFalse tBool }

/-- Every value inhabits the wildcard (`value_checks.pl:501-502`). -/
def hasTypeWildcard : RuleSchema :=
  { id := ruleId "has-type-wildcard"
    metavariables := [("v", 0)]
    premises := []
    conclusion := valueHasType (.fvar "v") tUndefined }

/-- Union by membership (`value_checks.pl:504`). -/
def hasTypeUnion : RuleSchema :=
  { id := ruleId "has-type-union"
    metavariables := [("v", 0), ("m", 0), ("ms", 0)]
    premises :=
      [ unionMember (.fvar "m") (.fvar "ms"),
        valueHasType (.fvar "v") (.fvar "m") ]
    conclusion := valueHasType (.fvar "v") (tUnion (.fvar "ms")) }

/-- Newtype erasure: at runtime only the representation exists
(`value_checks.pl:507`). -/
def hasTypeBrand : RuleSchema :=
  { id := ruleId "has-type-brand"
    metavariables := [("v", 0), ("n", 0), ("r", 0)]
    premises := [valueHasType (.fvar "v") (.fvar "r")]
    conclusion :=
      valueHasType (.fvar "v") (tBrand (.fvar "n") (.fvar "r")) }

/-- Homogeneous list, elementwise (`value_checks.pl:503`,
`runtime_list_ok`). -/
def hasTypeNilList : RuleSchema :=
  { id := ruleId "has-type-nil-list"
    metavariables := [("t", 0)]
    premises := []
    conclusion := valueHasType vNil (tList (.fvar "t")) }

def hasTypeConsList : RuleSchema :=
  { id := ruleId "has-type-cons-list"
    metavariables := [("v", 0), ("vs", 0), ("t", 0)]
    premises :=
      [ valueHasType (.fvar "v") (.fvar "t"),
        valueHasType (.fvar "vs") (tList (.fvar "t")) ]
    conclusion :=
      valueHasType (vCons (.fvar "v") (.fvar "vs")) (tList (.fvar "t")) }

/-- The transient cast: a guard is exactly one dynamic-judgment check on a
bound value (`typecheck_or_error`, `value_checks.pl:485-487`).  Failure of
this judgment is the `literal_type_mismatch` error class. -/
def guardPassesRule : RuleSchema :=
  { id := ruleId "guard-passes"
    metavariables := [("v", 0), ("t", 0)]
    premises := [valueHasType (.fvar "v") (.fvar "t")]
    conclusion := guardPasses (.fvar "v") (.fvar "t") }

/-! ## The complete authored definition

The term grammar and proof calculus are written once, as one flat record.
`language` and `calculus` below are reducible projections retained for the
checker API; they are not separately authored definitions. -/

abbrev definition : CalculusLanguageDef :=
  { name := "petta-typecheck-v2-core"
    types := [termType]
    terms :=
      [ termConstructor "TNum" 0,
        termConstructor "TStr" 0,
        termConstructor "TBool" 0,
        termConstructor "TUndefined" 0,
        termConstructor "TTNil" 0,
        termConstructor "TTCons" 2,
        termConstructor "TUnion" 1,
        termConstructor "TArrow" 3,
        termConstructor "TBrand" 2,
        termConstructor "TList" 1,
        termConstructor "MPlain" 0,
        termConstructor "MDet" 0,
        termConstructor "MSemidet" 0,
        termConstructor "MNondet" 0,
        termConstructor "EdgeExact" 0,
        termConstructor "EdgeStructural" 0,
        termConstructor "EdgeDynamic" 0,
        termConstructor "VNum" 0,
        termConstructor "VStr" 0,
        termConstructor "VTrue" 0,
        termConstructor "VFalse" 0,
        termConstructor "VNil" 0,
        termConstructor "VCons" 2,
        termConstructor "BrandA" 0,
        termConstructor "BrandB" 0 ]
    equations := []
    rewrites := []
    judgments :=
      [ { head := "Consistent", arity := 3 },
        { head := "ConsistentList", arity := 2 },
        { head := "UnionMember", arity := 2 },
        { head := "ValueHasType", arity := 2 },
        { head := "GuardPasses", arity := 2 } ]
    rules :=
      [ consistentRefl, consistentDynLeft, consistentDynRight,
        consistentUnionRight, consistentUnionLeft, consistentBrand,
        consistentArrow, consistentListNil, consistentListCons,
        unionMemberHere, unionMemberThere,
        hasTypeNum, hasTypeStr, hasTypeTrue, hasTypeFalse,
        hasTypeWildcard, hasTypeUnion, hasTypeBrand,
        hasTypeNilList, hasTypeConsList,
        guardPassesRule ] }

/-- The exact five-field language consumed by object-language tooling. -/
abbrev language : LanguageDef := definition.toLanguageDef

/-- The exact proof calculus consumed by the generic checker. -/
abbrev calculus : ProofCalculus := definition.toCalculus

/-- The same human-authored record viewed in the general compositional
extension family.  Its extension index is the canonical calculus-authoring
layer, so this is a reducible view rather than a second definition. -/
abbrev extendedDefinition :
    ExtendedLanguageDef
      Mettapedia.GSLT.LanguageDef.ExtensionComposition.calculusLayer :=
  definition.toExtended

@[simp] theorem extendedDefinition_language :
    extendedDefinition.toLanguageDef = language := rfl

@[simp] theorem extendedDefinition_calculus :
    extendedDefinition.extension = calculus := rfl

@[simp] theorem extendedDefinition_elaborates :
    Mettapedia.GSLT.LanguageDef.ExtensionComposition.calculusLayer.elaborate
        language extendedDefinition.authoredSource =
      some calculus :=
  extendedDefinition.elaborate_authoredSource

/-- The authored calculus document.  This is a term of the canonical
calculus-authoring GSLT, not an additional field of the object language. -/
def calculusSource : CalculusSyntax := quote calculus

/-- The authored GSLT document elaborates to exactly the derived checker
input. -/
@[simp] theorem calculusSource_elaborates :
    elaborateDefinition? language calculusSource = some definition := by
  exact elaborateDefinition?_quote language calculus

/-- Erasing the calculus fibre recovers the exact five-field object language. -/
@[simp] theorem definition_language : definition.toLanguageDef = language := rfl

/-! ## Receipts -/

theorem language_validate : language.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorOnly language <;>
    simp [termType, termConstructor,
      LanguageDef.typeNames, TypeDecl.plain, TermParam.typeExpr,
      TypeExpr.baseNames]

theorem definition_valid : definition.isValid = true := by
  have hvalidate : definition.toLanguageDef.validate = [] := by
    simpa [definition] using language_validate
  unfold CalculusLanguageDef.isValid CalculusLanguageDef.hasValidLocalRules
  rw [hvalidate]
  simp [definition,
    CalculusLanguageDef.ruleIds, CalculusLanguageDef.judgmentSignatureValid,
    CalculusLanguageDef.judgmentHeads, CalculusLanguageDef.conversionDeclarationValid,
    CalculusLanguageDef.lookupJudgment?, RuleSchema.isValidIn,
    RuleSchema.isLocallyValid,
    RuleSchema.metavariableNames, RuleSchema.occurrences, RuleSchema.patterns,
    patternMetavariableOccurrencesAt, patternsMetavariableOccurrencesAt,
    patternHasNoCollectionRest, patternsHaveNoCollectionRest,
    CalculusLanguageDef.judgmentSchemaValid, fixedConstructorsValid,
    fixedConstructorListsValid, languageHasConstructorArity,
    Pattern.isWellScoped, Pattern.isWellScopedAt, Pattern.isWellScopedListAt,
    Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList, Pattern.zipHead, Pattern.mapHead,
    Pattern.evalHead, termType, termConstructor,
    consistentRefl, consistentDynLeft, consistentDynRight,
    consistentUnionRight, consistentUnionLeft, consistentBrand,
    consistentArrow, consistentListNil, consistentListCons,
    unionMemberHere, unionMemberThere, hasTypeNum, hasTypeStr, hasTypeTrue,
    hasTypeFalse, hasTypeWildcard, hasTypeUnion, hasTypeBrand,
    hasTypeNilList, hasTypeConsList, guardPassesRule,
    consistent, consistentList, unionMember, valueHasType, guardPasses,
    tNum, tStr, tBool, tUndefined, tNil, tCons, tUnion, tArrow, tBrand,
    tList, edgeExact, edgeStructural,
    edgeDynamic, vNum, vStr, vTrue, vFalse, vNil, vCons,
    ruleId]
  decide

abbrev checked : ValidatedCalculusLanguageDef := ⟨definition, definition_valid⟩

/-- Inventory pin: 25 constructors. -/
theorem language_constructor_count : language.terms.length = 25 := by decide

/-- Inventory pin: 21 inference rules. -/
theorem calculus_rule_count : calculus.rules.length = 21 := by decide

/-! ## Positive acceptance theorems -/

def dynRightProof : RawProof :=
  .node { ruleId := ruleId "consistent-dyn-right", arguments := [tNum] } []

/-- `Number` is consistent with the wildcard (gradual axis, right). -/
theorem number_consistent_with_dynamic :
    checkRaw checked (consistent tNum tUndefined edgeDynamic)
      dynRightProof = true := by
  simp [checkRaw, checkRawChildren, checked,
    dynRightProof, consistentRefl, consistentDynLeft, consistentDynRight,
    consistentUnionRight, consistentUnionLeft, consistentBrand,
    consistentArrow, consistentListNil, consistentListCons,
    unionMemberHere, unionMemberThere, hasTypeNum, hasTypeStr, hasTypeTrue,
    hasTypeFalse, hasTypeWildcard, hasTypeUnion, hasTypeBrand,
    hasTypeNilList, hasTypeConsList, guardPassesRule,
    instantiateRule?, CalculusLanguageDef.lookupRule?, argumentsValidAt,
    argumentValidAt, RuleSchema.sideConditionsHold,
    instantiateSchema?, instantiateSchemaAt?, instantiateSchemas?,
    instantiateSchemasAt?, lookupArgumentAt?, consistent, tNum, tUndefined,
    edgeDynamic, ruleId, Pattern.isGroundAt, Pattern.isGroundListAt,
    Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList]

def dynLeftProof : RawProof :=
  .node { ruleId := ruleId "consistent-dyn-left", arguments := [tStr] } []

/-- The wildcard is consistent with `String` (gradual axis, left). -/
theorem dynamic_consistent_with_string :
    checkRaw checked (consistent tUndefined tStr edgeDynamic)
      dynLeftProof = true := by
  simp [checkRaw, checkRawChildren, checked,
    dynLeftProof, consistentRefl, consistentDynLeft, consistentDynRight,
    consistentUnionRight, consistentUnionLeft, consistentBrand,
    consistentArrow, consistentListNil, consistentListCons,
    unionMemberHere, unionMemberThere, hasTypeNum, hasTypeStr, hasTypeTrue,
    hasTypeFalse, hasTypeWildcard, hasTypeUnion, hasTypeBrand,
    hasTypeNilList, hasTypeConsList, guardPassesRule,
    instantiateRule?, CalculusLanguageDef.lookupRule?, argumentsValidAt,
    argumentValidAt, RuleSchema.sideConditionsHold,
    instantiateSchema?, instantiateSchemaAt?, instantiateSchemas?,
    instantiateSchemasAt?, lookupArgumentAt?, consistent, tStr, tUndefined,
    edgeDynamic, ruleId, Pattern.isGroundAt, Pattern.isGroundListAt,
    Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList]

def numberUnion : Pattern := tUnion (tCons tNum (tCons tStr tNil))

def unionMemberProof : RawProof :=
  .node
    { ruleId := ruleId "union-member-here"
      arguments := [tNum, tCons tStr tNil] } []

def reflNumProof : RawProof :=
  .node { ruleId := ruleId "consistent-refl", arguments := [tNum] } []

def unionRightProof : RawProof :=
  .node
    { ruleId := ruleId "consistent-union-right"
      arguments := [tNum, tNum, tCons tNum (tCons tStr tNil), edgeExact] }
    [unionMemberProof, reflNumProof]

/-- `Number` is consistent with `(| Number String)` through membership. -/
theorem number_consistent_with_union :
    checkRaw checked (consistent tNum numberUnion edgeStructural)
      unionRightProof = true := by
  simp [checkRaw, checkRawChildren, checked,
    unionRightProof, unionMemberProof, reflNumProof, numberUnion,
    consistentRefl, consistentDynLeft, consistentDynRight,
    consistentUnionRight, consistentUnionLeft, consistentBrand,
    consistentArrow, consistentListNil, consistentListCons,
    unionMemberHere, unionMemberThere, hasTypeNum, hasTypeStr, hasTypeTrue,
    hasTypeFalse, hasTypeWildcard, hasTypeUnion, hasTypeBrand,
    hasTypeNilList, hasTypeConsList, guardPassesRule,
    instantiateRule?, CalculusLanguageDef.lookupRule?, argumentsValidAt,
    argumentValidAt, RuleSchema.sideConditionsHold,
    instantiateSchema?, instantiateSchemaAt?, instantiateSchemas?,
    instantiateSchemasAt?, lookupArgumentAt?, consistent, unionMember,
    tNum, tStr, tNil, tCons, tUnion, edgeExact, edgeStructural, ruleId,
    Pattern.isGroundAt, Pattern.isGroundListAt,
    Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList]

def hasTypeNumProof : RawProof :=
  .node { ruleId := ruleId "has-type-num", arguments := [] } []

/-- The dynamic judgment accepts the base-type witness. -/
theorem value_num_has_type_number :
    checkRaw checked (valueHasType vNum tNum) hasTypeNumProof = true := by
  simp [checkRaw, checkRawChildren, checked,
    hasTypeNumProof,
    consistentRefl, consistentDynLeft, consistentDynRight,
    consistentUnionRight, consistentUnionLeft, consistentBrand,
    consistentArrow, consistentListNil, consistentListCons,
    unionMemberHere, unionMemberThere, hasTypeNum, hasTypeStr, hasTypeTrue,
    hasTypeFalse, hasTypeWildcard, hasTypeUnion, hasTypeBrand,
    hasTypeNilList, hasTypeConsList, guardPassesRule,
    instantiateRule?, CalculusLanguageDef.lookupRule?, argumentsValidAt,
    RuleSchema.sideConditionsHold,
    instantiateSchema?, instantiateSchemaAt?, instantiateSchemas?,
    instantiateSchemasAt?, valueHasType, vNum, tNum,
    ruleId]

def brandedNum : Pattern := tBrand brandA tNum

def hasTypeBrandProof : RawProof :=
  .node
    { ruleId := ruleId "has-type-brand", arguments := [vNum, brandA, tNum] }
    [hasTypeNumProof]

/-- Newtype erasure: the representation witness inhabits the brand. -/
theorem value_num_has_branded_type :
    checkRaw checked (valueHasType vNum brandedNum)
      hasTypeBrandProof = true := by
  simp [checkRaw, checkRawChildren, checked,
    hasTypeBrandProof, hasTypeNumProof, brandedNum,
    consistentRefl, consistentDynLeft, consistentDynRight,
    consistentUnionRight, consistentUnionLeft, consistentBrand,
    consistentArrow, consistentListNil, consistentListCons,
    unionMemberHere, unionMemberThere, hasTypeNum, hasTypeStr, hasTypeTrue,
    hasTypeFalse, hasTypeWildcard, hasTypeUnion, hasTypeBrand,
    hasTypeNilList, hasTypeConsList, guardPassesRule,
    instantiateRule?, CalculusLanguageDef.lookupRule?, argumentsValidAt,
    argumentValidAt, RuleSchema.sideConditionsHold,
    instantiateSchema?, instantiateSchemaAt?, instantiateSchemas?,
    instantiateSchemasAt?, lookupArgumentAt?, valueHasType, vNum, tNum,
    tBrand, brandA, ruleId, Pattern.isGroundAt, Pattern.isGroundListAt,
    Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList]

def guardProof : RawProof :=
  .node
    { ruleId := ruleId "guard-passes", arguments := [vNum, tNum] }
    [hasTypeNumProof]

/-- The transient cast succeeds on a well-typed bound value
(`typecheck_or_error`, bound branch). -/
theorem guard_passes_on_welltyped :
    checkRaw checked (guardPasses vNum tNum) guardProof = true := by
  simp [checkRaw, checkRawChildren, checked,
    guardProof, hasTypeNumProof,
    consistentRefl, consistentDynLeft, consistentDynRight,
    consistentUnionRight, consistentUnionLeft, consistentBrand,
    consistentArrow, consistentListNil, consistentListCons,
    unionMemberHere, unionMemberThere, hasTypeNum, hasTypeStr, hasTypeTrue,
    hasTypeFalse, hasTypeWildcard, hasTypeUnion, hasTypeBrand,
    hasTypeNilList, hasTypeConsList, guardPassesRule,
    instantiateRule?, CalculusLanguageDef.lookupRule?, argumentsValidAt,
    argumentValidAt, RuleSchema.sideConditionsHold,
    instantiateSchema?, instantiateSchemaAt?, instantiateSchemas?,
    instantiateSchemasAt?, lookupArgumentAt?, guardPasses, valueHasType,
    vNum, tNum, ruleId, Pattern.isGroundAt, Pattern.isGroundListAt,
    Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList]

/-! ## Non-transitivity of consistency

`Number ~ %Undefined%` and `%Undefined% ~ String` hold (theorems above),
yet no rule concludes `Consistent TNum TStr e` for any edge: the refl rule
forces both sides equal, the wildcard rules place `TUndefined` literally in
one position, and every remaining rule requires union/brand/arrow structure.
The theorems below reject each candidate root instantiation; the exhaustive
impossibility statement (quantifying over all proofs) is the stage-2
soundness layer's obligation and is deliberately not claimed here. -/

def transitivityViaRefl : RawProof :=
  .node { ruleId := ruleId "consistent-refl", arguments := [tNum] } []

theorem non_transitivity_candidate_refl_rejects :
    checkRaw checked (consistent tNum tStr edgeExact)
      transitivityViaRefl = false := by
  simp [checkRaw, checked, transitivityViaRefl,
    consistentRefl, consistentDynLeft, consistentDynRight,
    consistentUnionRight, consistentUnionLeft, consistentBrand,
    consistentArrow, consistentListNil, consistentListCons,
    unionMemberHere, unionMemberThere, hasTypeNum, hasTypeStr, hasTypeTrue,
    hasTypeFalse, hasTypeWildcard, hasTypeUnion, hasTypeBrand,
    hasTypeNilList, hasTypeConsList, guardPassesRule,
    instantiateRule?, CalculusLanguageDef.lookupRule?, argumentsValidAt,
    argumentValidAt, RuleSchema.sideConditionsHold,
    instantiateSchema?, instantiateSchemaAt?, instantiateSchemas?,
    instantiateSchemasAt?, lookupArgumentAt?, checkRawChildren,
    consistent, tNum, tStr, edgeExact, ruleId,
    Pattern.isGroundAt, Pattern.isGroundListAt,
    Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList]

def transitivityViaDynLeft : RawProof :=
  .node { ruleId := ruleId "consistent-dyn-left", arguments := [tStr] } []

theorem non_transitivity_candidate_dyn_left_rejects :
    checkRaw checked (consistent tNum tStr edgeDynamic)
      transitivityViaDynLeft = false := by
  simp [checkRaw, checked, transitivityViaDynLeft,
    consistentRefl, consistentDynLeft, consistentDynRight,
    consistentUnionRight, consistentUnionLeft, consistentBrand,
    consistentArrow, consistentListNil, consistentListCons,
    unionMemberHere, unionMemberThere, hasTypeNum, hasTypeStr, hasTypeTrue,
    hasTypeFalse, hasTypeWildcard, hasTypeUnion, hasTypeBrand,
    hasTypeNilList, hasTypeConsList, guardPassesRule,
    instantiateRule?, CalculusLanguageDef.lookupRule?, argumentsValidAt,
    argumentValidAt, RuleSchema.sideConditionsHold,
    instantiateSchema?, instantiateSchemaAt?, instantiateSchemas?,
    instantiateSchemasAt?, lookupArgumentAt?, checkRawChildren,
    consistent, tNum, tStr, tUndefined, edgeDynamic, ruleId,
    Pattern.isGroundAt, Pattern.isGroundListAt,
    Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList]

def transitivityViaDynRight : RawProof :=
  .node { ruleId := ruleId "consistent-dyn-right", arguments := [tNum] } []

theorem non_transitivity_candidate_dyn_right_rejects :
    checkRaw checked (consistent tNum tStr edgeDynamic)
      transitivityViaDynRight = false := by
  simp [checkRaw, checked, transitivityViaDynRight,
    consistentRefl, consistentDynLeft, consistentDynRight,
    consistentUnionRight, consistentUnionLeft, consistentBrand,
    consistentArrow, consistentListNil, consistentListCons,
    unionMemberHere, unionMemberThere, hasTypeNum, hasTypeStr, hasTypeTrue,
    hasTypeFalse, hasTypeWildcard, hasTypeUnion, hasTypeBrand,
    hasTypeNilList, hasTypeConsList, guardPassesRule,
    instantiateRule?, CalculusLanguageDef.lookupRule?, argumentsValidAt,
    argumentValidAt, RuleSchema.sideConditionsHold,
    instantiateSchema?, instantiateSchemaAt?, instantiateSchemas?,
    instantiateSchemasAt?, lookupArgumentAt?, checkRawChildren,
    consistent, tNum, tStr, tUndefined, edgeDynamic, ruleId,
    Pattern.isGroundAt, Pattern.isGroundListAt,
    Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList]

/-! ## Further negatives -/

def wrongBaseProof : RawProof :=
  .node { ruleId := ruleId "has-type-num", arguments := [] } []

/-- A boolean witness does not inhabit `Number`
(`literal_type_mismatch` class). -/
theorem value_true_not_number :
    checkRaw checked (valueHasType vTrue tNum) wrongBaseProof = false := by
  simp [checkRaw, checked, wrongBaseProof,
    consistentRefl, consistentDynLeft, consistentDynRight,
    consistentUnionRight, consistentUnionLeft, consistentBrand,
    consistentArrow, consistentListNil, consistentListCons,
    unionMemberHere, unionMemberThere, hasTypeNum, hasTypeStr, hasTypeTrue,
    hasTypeFalse, hasTypeWildcard, hasTypeUnion, hasTypeBrand,
    hasTypeNilList, hasTypeConsList, guardPassesRule,
    instantiateRule?, CalculusLanguageDef.lookupRule?, argumentsValidAt,
    RuleSchema.sideConditionsHold,
    instantiateSchema?, instantiateSchemaAt?, instantiateSchemas?,
    instantiateSchemasAt?, checkRawChildren,
    valueHasType, vNum, vTrue, tNum, ruleId]

def brandMismatchProof : RawProof :=
  .node
    { ruleId := ruleId "consistent-brand"
      arguments := [brandA, tNum, tNum] } []

/-- Distinct brands over the same representation are NOT consistent:
generative nominality (`type_lang.pl:23`; compile-time rejection class
`type_conflict`, `value_checks.pl:346-350`). -/
theorem distinct_brands_reject :
    checkRaw checked
      (consistent (tBrand brandA tNum) (tBrand brandB tNum) edgeExact)
      brandMismatchProof = false := by
  simp [checkRaw, checked, brandMismatchProof,
    consistentRefl, consistentDynLeft, consistentDynRight,
    consistentUnionRight, consistentUnionLeft, consistentBrand,
    consistentArrow, consistentListNil, consistentListCons,
    unionMemberHere, unionMemberThere, hasTypeNum, hasTypeStr, hasTypeTrue,
    hasTypeFalse, hasTypeWildcard, hasTypeUnion, hasTypeBrand,
    hasTypeNilList, hasTypeConsList, guardPassesRule,
    instantiateRule?, CalculusLanguageDef.lookupRule?, argumentsValidAt,
    argumentValidAt, RuleSchema.sideConditionsHold,
    instantiateSchema?, instantiateSchemaAt?, instantiateSchemas?,
    instantiateSchemasAt?, lookupArgumentAt?, checkRawChildren,
    consistent, tBrand, brandA, brandB, tNum, edgeExact, ruleId,
    Pattern.isGroundAt, Pattern.isGroundListAt,
    Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList]

/-! ## PeTTa as one theory

The single flat definition above has two reducible views for existing object
and checker APIs.  This section supplies their common denotation as a single
`GSLT` — one carrier, one equation relation, and one reduction relation — and
proves that both views embed exactly.

The three components are spelled out by `rfl` immediately below the definition,
so the carrier, equations and reduction relation can be read without unfolding
anything. -/

section TotalTheory

open Mettapedia.GSLT
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.GSLT.LanguageDef.CalculusAsLanguage
open Mettapedia.GSLT.LanguageDef.EquationSemantics
open Mettapedia.GSLT.LanguageDef.TotalGSLT

/-- Compatibility is derived from the authored empty equation list, rather
than assumed by the total theory. -/
abbrev reductionRespectsEquations : ReductionRespectsEquations language :=
  ReductionRespectsEquations.of_no_equations rfl

/-- **The PeTTa type system as one GSLT.**  Object terms and proof obligations
under a single carrier, equation relation, and reduction relation. -/
def totalTheory : GSLT :=
  definition.toGSLT definition_valid reductionRespectsEquations

/-- **The carrier**: an object pattern, or a proof-obligation state. -/
theorem totalTheory_Term : totalTheory.Term = (Pattern ⊕ GoalState) := rfl

/-- **The equations**: exact equality within each component, never across. -/
theorem totalTheory_object_equiv (source target : Pattern) :
    totalTheory.Equiv (Sum.inl source) (Sum.inl target) ↔ source = target := by
  unfold totalTheory CalculusLanguageDef.toGSLT combinedGSLT
  constructor
  · intro equivalent
    cases equivalent with
    | left objectEquivalent =>
        exact (equationEquiv_iff_eq_of_no_generators rfl source target).mp
          objectEquivalent
  · intro equal
    exact GSLT.SumEquiv.left
      ((equationEquiv_iff_eq_of_no_generators rfl source target).mpr equal)

/-- **The reduction relation**: authored object reduction on one side, backward
inference-rule application on the other. -/
theorem totalTheory_rewrites :
    totalTheory.rewrites =
      GSLT.SumStep (languageGSLT language reductionRespectsEquations)
        (proofSearchGSLT checked) := rfl

/-- The authored term language declares no equations, so exact equality is the
faithful object equivalence here. -/
theorem totalTheory_object_equations_empty : language.equations = [] := rfl

/-- **The object language embeds faithfully.**  Attaching twenty-one inference
rules changes no object-term reduction, in either direction. -/
theorem totalTheory_object_step (source target : Pattern) :
    totalTheory.Step (Sum.inl source) (Sum.inl target) ↔
      langReducesUsing RelationEnv.empty language source target :=
  combinedGSLT_language_step checked reductionRespectsEquations source target

/-- Proof-search steps of the total theory are exactly the calculus's. -/
theorem totalTheory_proof_step (source target : GoalState) :
    totalTheory.Step (Sum.inr source) (Sum.inr target) ↔
      (proofSearchGSLT checked).Step source target :=
  combinedGSLT_calculus_step checked reductionRespectsEquations source target

/-- **Nothing crosses.**  With the two faithfulness laws this is exact
conservativity: the object fragment of the total theory *is* the authored term
language. -/
theorem totalTheory_no_crossing (pattern : Pattern) (state : GoalState) :
    ¬ totalTheory.Step (Sum.inl pattern) (Sum.inr state) ∧
      ¬ totalTheory.Step (Sum.inr state) (Sum.inl pattern) :=
  combinedGSLT_no_crossing checked reductionRespectsEquations pattern state

/-- **Adequacy inside the one theory.**  A goal list is derivable in the
calculus exactly when it reduces to the empty obligation state — no reference
to a separate proof-search structure. -/
theorem totalTheory_derivability (goals : GoalState) :
    Nonempty (DerivationList checked goals) ↔
      totalTheory.MultiStep (Sum.inr goals) (Sum.inr []) :=
  derivability_iff_combinedGSLT checked reductionRespectsEquations goals

/-- One concrete reduction: `Number` is consistent with the wildcard, and its
goal discharges to no outstanding obligations in a single step of the combined
theory. -/
theorem totalTheory_dynRight_discharges :
    totalTheory.Step
      (Sum.inr [consistent tNum tUndefined edgeDynamic]) (Sum.inr []) := by
  rw [totalTheory_proof_step]
  refine ⟨{ ruleId := ruleId "consistent-dyn-right", arguments := [tNum] },
    [], consistent tNum tUndefined edgeDynamic, [], ?_, rfl, rfl⟩
  simp [
    consistentRefl, consistentDynLeft, consistentDynRight,
    consistentUnionRight, consistentUnionLeft, consistentBrand,
    consistentArrow, consistentListNil, consistentListCons,
    unionMemberHere, unionMemberThere, hasTypeNum, hasTypeStr, hasTypeTrue,
    hasTypeFalse, hasTypeWildcard, hasTypeUnion, hasTypeBrand,
    hasTypeNilList, hasTypeConsList, guardPassesRule,
    instantiateRule?, CalculusLanguageDef.lookupRule?, argumentsValidAt,
    argumentValidAt, RuleSchema.sideConditionsHold,
    instantiateSchema?, instantiateSchemaAt?, instantiateSchemas?,
    instantiateSchemasAt?, lookupArgumentAt?, consistent, tNum, tUndefined,
    edgeDynamic, ruleId, Pattern.isGroundAt, Pattern.isGroundListAt,
    Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList]

end TotalTheory

/-! ## Export interface (consumed by `TypeSystemGSLTMeTTaExport`)

Public aliases over the checked language definition and receipt fixtures, so the
exporter renders exactly the checked objects: the executable relational
projection and the operational generic-checker audit both derive from
`coreDefinition`, and the sample goals/proofs are the same derivations
the `checkRaw` receipts above accept and reject. -/

def coreDefinition : CalculusLanguageDef := definition

def sampleAcceptGoal : Pattern := consistent tNum tUndefined edgeDynamic
def sampleAcceptProof : RawProof := dynRightProof
def sampleUnionGoal : Pattern := consistent tNum numberUnion edgeStructural
def sampleUnionProof : RawProof := unionRightProof
def sampleValueGoal : Pattern := valueHasType vNum tNum
def sampleValueProof : RawProof := hasTypeNumProof
def sampleRejectGoal : Pattern := consistent tNum tStr edgeExact
def sampleRejectProof : RawProof := transitivityViaRefl
def sampleBrandRejectGoal : Pattern :=
  consistent (tBrand brandA tNum) (tBrand brandB tNum) edgeExact
def sampleBrandRejectProof : RawProof := brandMismatchProof

end Mettapedia.Languages.MeTTa.PeTTa.TypeSystemGSLT
