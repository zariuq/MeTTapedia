import Mettapedia.GSLT.LanguageDef.CalculusLanguageDef
import Mettapedia.Languages.Metamath.InferenceEncoding

/-!
# Metamath inference side conditions

This file presents the finite list and substitution computations used by a
Metamath assertion step as ordinary proof-relevant judgments.  Every fact is
obtained from an explicit constructor rule: there are no callbacks and no
unrestricted fact rules.

The `DVLists` argument order follows the live verifier: substitution, caller
DV list, then callee DV list.  `DVOK` likewise carries the caller frame before
the callee frame, while each frame itself retains the runtime field order
`frame(dv, hypotheses)`.  A later bridge to `Metamath.Spec.dvOK` must account
for its source/target argument order.

`DVRel` accepts either orientation of an explicitly stored pair.  Its exact
correspondence with the runtime relation additionally requires the projected
caller-DV invariant that stored pairs are in strict canonical order.  This
simultaneously excludes self-pairs; without it a reversed stored pair is
accepted here but rejected by the runtime's normalized-pair membership test.
No unrestricted correspondence claim is made here.

Likewise, relational `Lookup` exposes duplicate bindings rather than silently
choosing one.  Runtime correspondence is restricted to substitutions generated
from a callee's pairwise-distinct floating variables.  The assertion projector
must establish that no-duplicate-key invariant before using these rules.
-/

namespace Mettapedia.Languages.Metamath.InferenceSideConditions

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.Languages.Metamath.InferenceEncoding
open Mettapedia.Languages.Metamath.InferenceEncoding.Builder

/-! ## Fixed data vocabulary and judgment signature -/

def dataTypeName : String := "$mm.data"

/-- Constructor declaration used both by the fixed carrier and by a later
finite source projection when it declares encoded nullary source strings. -/
def dataConstructor (label : String) (arity : Nat) : GrammarRule :=
  let params := (List.range arity).map fun index =>
    TermParam.simple s!"arg{index}" (.base dataTypeName)
  { label
    category := dataTypeName
    params
    syntaxPattern := [] }

def nullaryDataConstructor (label : String) : GrammarRule :=
  dataConstructor label 0

def reservedDataHeads : List String :=
  [ stringHead, nilHead, consHead, constSymHead, varSymHead, formulaHead
  , dvPairHead, frameHead, bindingHead, substitutionHead ]

def appendHead : String := "$mm.j.append"
def lookupHead : String := "$mm.j.lookup"
def substBodyHead : String := "$mm.j.subst-body"
def applySubstHead : String := "$mm.j.apply-subst"
def varsHead : String := "$mm.j.vars"
def memberHead : String := "$mm.j.member"
def dvRelHead : String := "$mm.j.dv-rel"
def allWithHead : String := "$mm.j.all-with"
def allPairsHead : String := "$mm.j.all-pairs"
def dvListsHead : String := "$mm.j.dv-lists"
def dvOKHead : String := "$mm.j.dv-ok"

def reservedJudgmentHeads : List String :=
  [ appendHead, lookupHead, substBodyHead, applySubstHead, varsHead
  , memberHead, dvRelHead, allWithHead, allPairsHead, dvListsHead, dvOKHead ]

def reservedInternalHeads : List String :=
  reservedDataHeads ++ reservedJudgmentHeads

/-- Collision gate for the finite nullary heads added by a source projection. -/
def sourceHeadsDisjoint (sourceHeads : List String) : Bool :=
  sourceHeads.all fun head => !(reservedInternalHeads.contains head)

def judgmentDecls : List JudgmentDecl :=
  [ { head := appendHead, arity := 3 }
  , { head := lookupHead, arity := 4 }
  , { head := substBodyHead, arity := 3 }
  , { head := applySubstHead, arity := 3 }
  , { head := varsHead, arity := 2 }
  , { head := memberHead, arity := 2 }
  , { head := dvRelHead, arity := 3 }
  , { head := allWithHead, arity := 3 }
  , { head := allPairsHead, arity := 3 }
  , { head := dvListsHead, arity := 3 }
  , { head := dvOKHead, arity := 3 } ]

def append (left right result : Pattern) : Pattern :=
  .apply appendHead [left, right, result]

def lookup (substitution variableName typecode body : Pattern) : Pattern :=
  .apply lookupHead [substitution, variableName, typecode, body]

def substBody (substitution source result : Pattern) : Pattern :=
  .apply substBodyHead [substitution, source, result]

def applySubst (substitution source result : Pattern) : Pattern :=
  .apply applySubstHead [substitution, source, result]

def vars (body result : Pattern) : Pattern :=
  .apply varsHead [body, result]

def member (value values : Pattern) : Pattern :=
  .apply memberHead [value, values]

def dvRel (callerDV left right : Pattern) : Pattern :=
  .apply dvRelHead [callerDV, left, right]

def allWith (callerDV left rights : Pattern) : Pattern :=
  .apply allWithHead [callerDV, left, rights]

def allPairs (callerDV lefts rights : Pattern) : Pattern :=
  .apply allPairsHead [callerDV, lefts, rights]

/-- `dvLists S callerDV calleeDV` checks every callee constraint against the
caller constraints after applying `S`. -/
def dvLists (substitution callerDV calleeDV : Pattern) : Pattern :=
  .apply dvListsHead [substitution, callerDV, calleeDV]

/-- Frames occur in live-verifier order: caller first, callee second. -/
def dvOK (substitution callerFrame calleeFrame : Pattern) : Pattern :=
  .apply dvOKHead [substitution, callerFrame, calleeFrame]

private def rid (value : String) : RuleId := { value }
private def mv (name : String) : Pattern := .fvar name
private def formal (name : String) : String × Nat := (name, 0)

/-! ## Explicit finite rules -/

def appendNilRule : RuleSchema :=
  { id := rid "$mm.append.nil"
    metavariables := [formal "Y"]
    premises := []
    conclusion := append Builder.nil (mv "Y") (mv "Y") }

def appendConsRule : RuleSchema :=
  { id := rid "$mm.append.cons"
    metavariables := [formal "X", formal "XS", formal "Y", formal "Z"]
    premises := [append (mv "XS") (mv "Y") (mv "Z")]
    conclusion :=
      append (Builder.cons (mv "X") (mv "XS")) (mv "Y")
        (Builder.cons (mv "X") (mv "Z")) }

def lookupHereRule : RuleSchema :=
  { id := rid "$mm.lookup.here"
    metavariables :=
      [formal "V", formal "TC", formal "B", formal "Rest"]
    premises := []
    conclusion :=
      lookup
        (Builder.substitution
          (Builder.cons
            (Builder.binding (mv "V") (Builder.formula (mv "TC") (mv "B")))
            (mv "Rest")))
        (mv "V") (mv "TC") (mv "B") }

def lookupThereRule : RuleSchema :=
  { id := rid "$mm.lookup.there"
    metavariables :=
      [ formal "Rest", formal "V", formal "TC", formal "B"
      , formal "W", formal "T0", formal "B0" ]
    premises :=
      [lookup (Builder.substitution (mv "Rest")) (mv "V") (mv "TC") (mv "B")]
    conclusion :=
      lookup
        (Builder.substitution
          (Builder.cons
            (Builder.binding (mv "W") (Builder.formula (mv "T0") (mv "B0")))
            (mv "Rest")))
        (mv "V") (mv "TC") (mv "B") }

def substBodyNilRule : RuleSchema :=
  { id := rid "$mm.subst-body.nil"
    metavariables := [formal "S"]
    premises := []
    conclusion := substBody (mv "S") Builder.nil Builder.nil }

def substBodyConstRule : RuleSchema :=
  { id := rid "$mm.subst-body.const"
    metavariables :=
      [formal "S", formal "C", formal "XS", formal "YS"]
    premises := [substBody (mv "S") (mv "XS") (mv "YS")]
    conclusion :=
      substBody (mv "S")
        (Builder.cons (Builder.constSym (mv "C")) (mv "XS"))
        (Builder.cons (Builder.constSym (mv "C")) (mv "YS")) }

def substBodyVarRule : RuleSchema :=
  { id := rid "$mm.subst-body.var"
    metavariables :=
      [ formal "S", formal "V", formal "TC", formal "Image"
      , formal "XS", formal "YS", formal "ZS" ]
    premises :=
      [ lookup (mv "S") (mv "V") (mv "TC") (mv "Image")
      , substBody (mv "S") (mv "XS") (mv "YS")
      , append (mv "Image") (mv "YS") (mv "ZS") ]
    conclusion :=
      substBody (mv "S")
        (Builder.cons (Builder.varSym (mv "V")) (mv "XS"))
        (mv "ZS") }

def applySubstFormulaRule : RuleSchema :=
  { id := rid "$mm.apply-subst.formula"
    metavariables :=
      [formal "S", formal "TC", formal "XS", formal "YS"]
    premises := [substBody (mv "S") (mv "XS") (mv "YS")]
    conclusion :=
      applySubst (mv "S") (Builder.formula (mv "TC") (mv "XS"))
        (Builder.formula (mv "TC") (mv "YS")) }

def varsNilRule : RuleSchema :=
  { id := rid "$mm.vars.nil"
    metavariables := []
    premises := []
    conclusion := vars Builder.nil Builder.nil }

def varsConstRule : RuleSchema :=
  { id := rid "$mm.vars.const"
    metavariables := [formal "C", formal "XS", formal "VS"]
    premises := [vars (mv "XS") (mv "VS")]
    conclusion :=
      vars (Builder.cons (Builder.constSym (mv "C")) (mv "XS")) (mv "VS") }

def varsVarRule : RuleSchema :=
  { id := rid "$mm.vars.var"
    metavariables := [formal "V", formal "XS", formal "VS"]
    premises := [vars (mv "XS") (mv "VS")]
    conclusion :=
      vars (Builder.cons (Builder.varSym (mv "V")) (mv "XS"))
        (Builder.cons (mv "V") (mv "VS")) }

def memberHereRule : RuleSchema :=
  { id := rid "$mm.member.here"
    metavariables := [formal "X", formal "XS"]
    premises := []
    conclusion := member (mv "X") (Builder.cons (mv "X") (mv "XS")) }

def memberThereRule : RuleSchema :=
  { id := rid "$mm.member.there"
    metavariables := [formal "X", formal "Y", formal "YS"]
    premises := [member (mv "X") (mv "YS")]
    conclusion := member (mv "X") (Builder.cons (mv "Y") (mv "YS")) }

def dvRelForwardRule : RuleSchema :=
  { id := rid "$mm.dv-rel.forward"
    metavariables := [formal "D", formal "X", formal "Y"]
    premises := [member (Builder.dvPair (mv "X") (mv "Y")) (mv "D")]
    conclusion := dvRel (mv "D") (mv "X") (mv "Y") }

def dvRelReverseRule : RuleSchema :=
  { id := rid "$mm.dv-rel.reverse"
    metavariables := [formal "D", formal "X", formal "Y"]
    premises := [member (Builder.dvPair (mv "Y") (mv "X")) (mv "D")]
    conclusion := dvRel (mv "D") (mv "X") (mv "Y") }

def allWithNilRule : RuleSchema :=
  { id := rid "$mm.all-with.nil"
    metavariables := [formal "D", formal "X"]
    premises := []
    conclusion := allWith (mv "D") (mv "X") Builder.nil }

def allWithConsRule : RuleSchema :=
  { id := rid "$mm.all-with.cons"
    metavariables :=
      [formal "D", formal "X", formal "Y", formal "YS"]
    premises :=
      [ dvRel (mv "D") (mv "X") (mv "Y")
      , allWith (mv "D") (mv "X") (mv "YS") ]
    conclusion :=
      allWith (mv "D") (mv "X") (Builder.cons (mv "Y") (mv "YS")) }

def allPairsNilRule : RuleSchema :=
  { id := rid "$mm.all-pairs.nil"
    metavariables := [formal "D", formal "YS"]
    premises := []
    conclusion := allPairs (mv "D") Builder.nil (mv "YS") }

def allPairsConsRule : RuleSchema :=
  { id := rid "$mm.all-pairs.cons"
    metavariables :=
      [formal "D", formal "X", formal "XS", formal "YS"]
    premises :=
      [ allWith (mv "D") (mv "X") (mv "YS")
      , allPairs (mv "D") (mv "XS") (mv "YS") ]
    conclusion :=
      allPairs (mv "D") (Builder.cons (mv "X") (mv "XS")) (mv "YS") }

def dvListsNilRule : RuleSchema :=
  { id := rid "$mm.dv-lists.nil"
    metavariables := [formal "S", formal "CallerDV"]
    premises := []
    conclusion := dvLists (mv "S") (mv "CallerDV") Builder.nil }

def dvListsConsRule : RuleSchema :=
  { id := rid "$mm.dv-lists.cons"
    metavariables :=
      [ formal "S", formal "CallerDV", formal "V", formal "W"
      , formal "Rest", formal "TC1", formal "B1", formal "TC2"
      , formal "B2", formal "VS1", formal "VS2" ]
    premises :=
      [ lookup (mv "S") (mv "V") (mv "TC1") (mv "B1")
      , lookup (mv "S") (mv "W") (mv "TC2") (mv "B2")
      , vars (mv "B1") (mv "VS1")
      , vars (mv "B2") (mv "VS2")
      , allPairs (mv "CallerDV") (mv "VS1") (mv "VS2")
      , dvLists (mv "S") (mv "CallerDV") (mv "Rest") ]
    conclusion :=
      dvLists (mv "S") (mv "CallerDV")
        (Builder.cons (Builder.dvPair (mv "V") (mv "W")) (mv "Rest")) }

def dvOKRule : RuleSchema :=
  { id := rid "$mm.dv-ok.frames"
    metavariables :=
      [ formal "S", formal "CallerDV", formal "CallerHyps"
      , formal "CalleeDV", formal "CalleeHyps" ]
    premises :=
      [dvLists (mv "S") (mv "CallerDV") (mv "CalleeDV")]
    conclusion :=
      dvOK (mv "S")
        (Builder.frame (mv "CallerDV") (mv "CallerHyps"))
        (Builder.frame (mv "CalleeDV") (mv "CalleeHyps")) }

def sideRules : List RuleSchema :=
  [ appendNilRule, appendConsRule
  , lookupHereRule, lookupThereRule
  , substBodyNilRule, substBodyConstRule, substBodyVarRule
  , applySubstFormulaRule
  , varsNilRule, varsConstRule, varsVarRule
  , memberHereRule, memberThereRule
  , dvRelForwardRule, dvRelReverseRule
  , allWithNilRule, allWithConsRule
  , allPairsNilRule, allPairsConsRule
  , dvListsNilRule, dvListsConsRule
  , dvOKRule ]

/-! ## One complete authored definition -/

/-- The Metamath data grammar and its side-condition calculus, authored as one
flat definition. -/
abbrev sideDefinition : CalculusLanguageDef :=
  { name := "metamath-inference-data"
    types := [TypeDecl.plain dataTypeName]
    terms :=
      [ dataConstructor stringHead 1
      , dataConstructor nilHead 0
      , dataConstructor consHead 2
      , dataConstructor constSymHead 1
      , dataConstructor varSymHead 1
      , dataConstructor formulaHead 2
      , dataConstructor dvPairHead 2
      , dataConstructor frameHead 2
      , dataConstructor bindingHead 2
      , dataConstructor substitutionHead 1 ]
    equations := []
    rewrites := []
    judgments := judgmentDecls
    rules := sideRules }

/-- Five-field object-language view retained for consumers. -/
abbrev dataLanguage : LanguageDef := sideDefinition.toLanguageDef

/-- Proof-calculus view retained for the generic checker. -/
abbrev sideCalculus :
    Mettapedia.GSLT.LanguageDef.InferenceExtension.ProofCalculus :=
  sideDefinition.toCalculus

/-- Every fixed side-condition rule identifier occupies the namespace later
excluded from generated source-rule identifiers. -/
theorem sideRuleId_startsWith_reservedRulePrefix
    {id : RuleId} (member : id ∈ sideRules.map RuleSchema.id) :
    id.value.startsWith "$mm." = true := by
  simp [sideRules, appendNilRule, appendConsRule, lookupHereRule,
    lookupThereRule, substBodyNilRule, substBodyConstRule, substBodyVarRule,
    applySubstFormulaRule, varsNilRule, varsConstRule, varsVarRule,
    memberHereRule, memberThereRule, dvRelForwardRule, dvRelReverseRule,
    allWithNilRule, allWithConsRule, allPairsNilRule, allPairsConsRule,
    dvListsNilRule, dvListsConsRule, dvOKRule, rid] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl <;>
    rw [String.startsWith_string_iff] <;> decide

/-- Reserved namespace for generated side-condition rules.  `$` is excluded
from Metamath labels, so the later source projector must reject or prove absent
this prefix before combining source rules with this language definition. -/
def reservedRulePrefix : String := "$mm."

/-- Explicit collision gate for a projected list of source rule identifiers. -/
def sourceRuleIdsDisjoint (sourceIds : List RuleId) : Bool :=
  sourceIds.all fun id => !(id.value.startsWith reservedRulePrefix)

theorem dataLanguage_validate : dataLanguage.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorOnly dataLanguage <;>
    simp [dataConstructor, dataTypeName, stringHead, nilHead,
      consHead, constSymHead, varSymHead, formulaHead, dvPairHead, frameHead,
      bindingHead, substitutionHead, LanguageDef.typeNames,
      TypeDecl.plain, TermParam.typeExpr, TypeExpr.baseNames]

theorem sideDefinition_valid : sideDefinition.isValid = true := by
  unfold CalculusLanguageDef.isValid CalculusLanguageDef.hasValidLocalRules
  rw [dataLanguage_validate]
  simp [sideRules, judgmentDecls, dataConstructor, dataTypeName,
    stringHead, nilHead, consHead, constSymHead, varSymHead, formulaHead,
    dvPairHead, frameHead, bindingHead, substitutionHead,
    appendHead, lookupHead, substBodyHead, applySubstHead, varsHead,
    memberHead, dvRelHead, allWithHead, allPairsHead, dvListsHead, dvOKHead,
    CalculusLanguageDef.judgmentSignatureValid,
    CalculusLanguageDef.judgmentHeads, CalculusLanguageDef.ruleIds,
    RuleSchema.isValidIn, CalculusLanguageDef.judgmentSchemaValid,
    CalculusLanguageDef.lookupJudgment?, languageHasConstructorArity,
    fixedConstructorsValid,
    RuleSchema.isLocallyValid, RuleSchema.metavariableNames,
    RuleSchema.occurrences, RuleSchema.patterns,
    patternMetavariableOccurrencesAt, patternsMetavariableOccurrencesAt,
    patternHasNoCollectionRest, patternsHaveNoCollectionRest,
    fixedConstructorListsValid, Pattern.zipHead, Pattern.mapHead,
    Pattern.evalHead, Pattern.isWellScoped, Pattern.isWellScopedAt,
    Pattern.isWellScopedListAt, Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList,
    appendNilRule, appendConsRule, lookupHereRule, lookupThereRule,
    substBodyNilRule, substBodyConstRule, substBodyVarRule,
    applySubstFormulaRule, varsNilRule, varsConstRule, varsVarRule,
    memberHereRule, memberThereRule, dvRelForwardRule, dvRelReverseRule,
    allWithNilRule, allWithConsRule, allPairsNilRule, allPairsConsRule,
    dvListsNilRule, dvListsConsRule, dvOKRule, append, lookup, substBody,
    applySubst, vars, member, dvRel, allWith, allPairs, dvLists, dvOK,
    rid, mv, formal]
  decide

/-- The side-condition language and its proof calculus as one GSLT. -/
def totalTheory : Mettapedia.GSLT.GSLT :=
  sideDefinition.toGSLTOfNoEquations sideDefinition_valid rfl

theorem totalTheory_Term : totalTheory.Term = (Pattern ⊕ List Pattern) :=
  rfl

def validatedSideDefinition : ValidatedCalculusLanguageDef :=
  ⟨sideDefinition, sideDefinition_valid⟩

/-! ## Concrete proof trees and mutation boundaries -/

private def proofNode (rule : String) (arguments : List Pattern)
    (children : List RawProof := []) : RawProof :=
  .node { ruleId := rid rule, arguments } children

local macro "side_core" : tactic =>
  `(tactic|
    simp [checkRaw, checkRawChildren, validatedSideDefinition,
      sideDefinition, sideCalculus, sideRules, appendNilRule, appendConsRule,
      lookupHereRule, lookupThereRule, substBodyNilRule, substBodyConstRule,
      substBodyVarRule, applySubstFormulaRule, varsNilRule, varsConstRule,
      varsVarRule, memberHereRule, memberThereRule, dvRelForwardRule,
      dvRelReverseRule, allWithNilRule, allWithConsRule, allPairsNilRule,
      allPairsConsRule, dvListsNilRule, dvListsConsRule, dvOKRule,
      instantiateRule?, CalculusLanguageDef.lookupRule?, argumentsValidAt,
      argumentValidAt, instantiateSchemas?, instantiateSchemasAt?,
      instantiateSchema?, instantiateSchemaAt?, lookupArgumentAt?,
      append, lookup, substBody, applySubst, vars, member, dvRel, allWith,
      allPairs, dvLists, dvOK, appendHead, lookupHead, substBodyHead,
      applySubstHead, varsHead, memberHead, dvRelHead, allWithHead,
      allPairsHead, dvListsHead, dvOKHead, proofNode, rid, mv, formal,
      encodeString, Builder.rawString, Builder.encodedString, Builder.nil,
      Builder.cons, Builder.constSym, Builder.varSym, Builder.formula,
      Builder.dvPair, Builder.frame, Builder.binding, Builder.substitution,
      stringHead, nilHead, consHead, constSymHead, varSymHead, formulaHead,
      dvPairHead, frameHead, bindingHead, substitutionHead,
      Pattern.isGroundAt, Pattern.isGroundListAt,
      Pattern.hasCanonicalBinderMetadata,
      Pattern.hasCanonicalBinderMetadataList])

private def name (value : String) : Pattern := encodeString value
private def singleton (value : Pattern) : Pattern :=
  Builder.cons value Builder.nil

private def aSym : Pattern := Builder.constSym (name "A")
private def bSym : Pattern := Builder.constSym (name "B")
private def xSym : Pattern := Builder.varSym (name "x")
private def ySym : Pattern := Builder.varSym (name "y")

private def appendLeft : Pattern :=
  Builder.cons aSym (singleton xSym)

private def appendRight : Pattern := singleton bSym

private def appendResult : Pattern :=
  Builder.cons aSym (Builder.cons xSym appendRight)

def appendExampleProof : RawProof :=
  proofNode "$mm.append.cons"
    [aSym, singleton xSym, appendRight, Builder.cons xSym appendRight]
    [proofNode "$mm.append.cons"
      [xSym, Builder.nil, appendRight, appendRight]
      [proofNode "$mm.append.nil" [appendRight]]]

def appendOmittedChildProof : RawProof :=
  proofNode "$mm.append.cons"
    [aSym, singleton xSym, appendRight, Builder.cons xSym appendRight]

def appendExtraChildProof : RawProof :=
  proofNode "$mm.append.nil" [appendRight]
    [proofNode "$mm.vars.nil" []]

theorem append_example_accepts :
    checkRaw validatedSideDefinition
      (append appendLeft appendRight appendResult) appendExampleProof = true := by
  simp [checkRaw, checkRawChildren, validatedSideDefinition, sideDefinition,
    sideRules, appendNilRule, appendConsRule, instantiateRule?,
    CalculusLanguageDef.lookupRule?, argumentsValidAt, argumentValidAt,
    instantiateSchemas?, instantiateSchemasAt?, instantiateSchema?,
    instantiateSchemaAt?, lookupArgumentAt?, appendExampleProof, proofNode,
    appendLeft, appendRight, appendResult, singleton, aSym, bSym, xSym, name,
    append, appendHead, rid, mv, formal, encodeString, Builder.rawString,
    Builder.encodedString, Builder.nil, Builder.cons, Builder.constSym,
    Builder.varSym, stringHead, nilHead, consHead, constSymHead, varSymHead,
    Pattern.isGroundAt, Pattern.isGroundListAt,
    Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList]

theorem append_omitted_child_rejects :
    checkRaw validatedSideDefinition
      (append appendLeft appendRight appendResult) appendOmittedChildProof = false := by
  simp [appendOmittedChildProof, appendLeft, appendRight, appendResult,
    singleton, aSym, bSym, xSym, name]
  side_core

theorem append_extra_child_rejects :
    checkRaw validatedSideDefinition
      (append Builder.nil appendRight appendRight) appendExtraChildProof = false := by
  simp [appendExtraChildProof, appendRight, singleton, bSym, name]
  side_core

/-! ### Substitution with variable splicing -/

private def tc : Pattern := name "|-"
private def vName : Pattern := name "v"
private def wName : Pattern := name "w"

private def imageBody : Pattern :=
  Builder.cons aSym (singleton xSym)

private def substitutionBindings : Pattern :=
  singleton (Builder.binding vName (Builder.formula tc imageBody))

private def exampleSubstitution : Pattern :=
  Builder.substitution substitutionBindings

private def sourceTail : Pattern := singleton bSym
private def sourceBody : Pattern :=
  Builder.cons (Builder.varSym vName) sourceTail
private def substitutedBody : Pattern :=
  Builder.cons aSym (Builder.cons xSym sourceTail)

private def lookupVProof : RawProof :=
  proofNode "$mm.lookup.here" [vName, tc, imageBody, Builder.nil]

private def tailSubstProof : RawProof :=
  proofNode "$mm.subst-body.const"
    [exampleSubstitution, name "B", Builder.nil, Builder.nil]
    [proofNode "$mm.subst-body.nil" [exampleSubstitution]]

private def imageAppendProof : RawProof :=
  proofNode "$mm.append.cons"
    [aSym, singleton xSym, sourceTail, Builder.cons xSym sourceTail]
    [proofNode "$mm.append.cons"
      [xSym, Builder.nil, sourceTail, sourceTail]
      [proofNode "$mm.append.nil" [sourceTail]]]

private def substBodyVarProof : RawProof :=
  proofNode "$mm.subst-body.var"
    [ exampleSubstitution, vName, tc, imageBody, sourceTail, sourceTail
    , substitutedBody ]
    [lookupVProof, tailSubstProof, imageAppendProof]

def substitutionExampleProof : RawProof :=
  proofNode "$mm.apply-subst.formula"
    [exampleSubstitution, tc, sourceBody, substitutedBody]
    [substBodyVarProof]

def substitutionSwappedChildrenProof : RawProof :=
  proofNode "$mm.apply-subst.formula"
    [exampleSubstitution, tc, sourceBody, substitutedBody]
    [proofNode "$mm.subst-body.var"
      [ exampleSubstitution, vName, tc, imageBody, sourceTail, sourceTail
      , substitutedBody ]
      [tailSubstProof, lookupVProof, imageAppendProof]]

def substitutionMissingLookupProof : RawProof :=
  proofNode "$mm.apply-subst.formula"
    [exampleSubstitution, tc, sourceBody, substitutedBody]
    [proofNode "$mm.subst-body.var"
      [ exampleSubstitution, vName, tc, imageBody, sourceTail, sourceTail
      , substitutedBody ]
      [tailSubstProof, imageAppendProof]]

def substitutionWrongTypecodeProof : RawProof :=
  proofNode "$mm.apply-subst.formula"
    [exampleSubstitution, tc, sourceBody, substitutedBody]
    [proofNode "$mm.subst-body.var"
      [ exampleSubstitution, vName, tc, imageBody, sourceTail, sourceTail
      , substitutedBody ]
      [ proofNode "$mm.lookup.here"
          [vName, name "wff", imageBody, Builder.nil]
      , tailSubstProof, imageAppendProof ]]

def substitutionWrongBodyProof : RawProof :=
  proofNode "$mm.apply-subst.formula"
    [exampleSubstitution, tc, sourceBody, substitutedBody]
    [proofNode "$mm.subst-body.var"
      [ exampleSubstitution, vName, tc, imageBody, sourceTail, sourceTail
      , substitutedBody ]
      [ proofNode "$mm.lookup.here"
          [vName, tc, singleton ySym, Builder.nil]
      , tailSubstProof, imageAppendProof ]]

theorem substitution_with_variable_splicing_accepts :
    checkRaw validatedSideDefinition
      (applySubst exampleSubstitution (Builder.formula tc sourceBody)
        (Builder.formula tc substitutedBody))
      substitutionExampleProof = true := by
  simp [substitutionExampleProof, substBodyVarProof, lookupVProof,
    tailSubstProof, imageAppendProof, exampleSubstitution,
    substitutionBindings, sourceBody, sourceTail, substitutedBody, imageBody,
    tc, vName, aSym, bSym, xSym, singleton, name]
  side_core

theorem substitution_swapped_children_rejects :
    checkRaw validatedSideDefinition
      (applySubst exampleSubstitution (Builder.formula tc sourceBody)
        (Builder.formula tc substitutedBody))
      substitutionSwappedChildrenProof = false := by
  simp [substitutionSwappedChildrenProof, lookupVProof, tailSubstProof,
    imageAppendProof, exampleSubstitution, substitutionBindings, sourceBody,
    sourceTail, substitutedBody, imageBody, tc, vName, aSym, bSym, xSym,
    singleton, name]
  side_core

theorem substitution_missing_lookup_rejects :
    checkRaw validatedSideDefinition
      (applySubst exampleSubstitution (Builder.formula tc sourceBody)
        (Builder.formula tc substitutedBody))
      substitutionMissingLookupProof = false := by
  simp [substitutionMissingLookupProof, tailSubstProof, imageAppendProof,
    exampleSubstitution, substitutionBindings, sourceBody, sourceTail,
    substitutedBody, imageBody, tc, vName, aSym, bSym, xSym, singleton, name]
  side_core

theorem substitution_wrong_typecode_rejects :
    checkRaw validatedSideDefinition
      (applySubst exampleSubstitution (Builder.formula tc sourceBody)
        (Builder.formula tc substitutedBody))
      substitutionWrongTypecodeProof = false := by
  simp [substitutionWrongTypecodeProof, tailSubstProof, imageAppendProof,
    exampleSubstitution, substitutionBindings, sourceBody, sourceTail,
    substitutedBody, imageBody, tc, vName, aSym, bSym, xSym, singleton, name]
  side_core

theorem substitution_wrong_body_rejects :
    checkRaw validatedSideDefinition
      (applySubst exampleSubstitution (Builder.formula tc sourceBody)
        (Builder.formula tc substitutedBody))
      substitutionWrongBodyProof = false := by
  simp [substitutionWrongBodyProof, tailSubstProof, imageAppendProof,
    exampleSubstitution, substitutionBindings, sourceBody, sourceTail,
    substitutedBody, imageBody, tc, vName, aSym, bSym, xSym, ySym,
    singleton, name]
  side_core

/-! ### Duplicate-key lookup boundary -/

private def firstDuplicateBody : Pattern := singleton aSym
private def secondDuplicateBody : Pattern := singleton bSym
private def duplicateBindings : Pattern :=
  Builder.cons (Builder.binding vName (Builder.formula tc firstDuplicateBody))
    (singleton (Builder.binding vName (Builder.formula tc secondDuplicateBody)))
private def duplicateSubstitution : Pattern :=
  Builder.substitution duplicateBindings

private def duplicateFirstProof : RawProof :=
  proofNode "$mm.lookup.here"
    [vName, tc, firstDuplicateBody,
      singleton (Builder.binding vName (Builder.formula tc secondDuplicateBody))]

private def duplicateSecondProof : RawProof :=
  proofNode "$mm.lookup.there"
    [ singleton (Builder.binding vName (Builder.formula tc secondDuplicateBody))
    , vName, tc, secondDuplicateBody, vName, tc, firstDuplicateBody ]
    [proofNode "$mm.lookup.here"
      [vName, tc, secondDuplicateBody, Builder.nil]]

/-- Relational lookup deliberately exposes ambiguity on duplicate keys.  The
runtime bridge may use neither result until its source-generated `NoDup` key
invariant has been proved. -/
theorem duplicate_lookup_exposes_both_results :
    checkRaw validatedSideDefinition
        (lookup duplicateSubstitution vName tc firstDuplicateBody)
        duplicateFirstProof = true ∧
      checkRaw validatedSideDefinition
        (lookup duplicateSubstitution vName tc secondDuplicateBody)
        duplicateSecondProof = true := by
  constructor
  · simp [duplicateFirstProof, duplicateSubstitution, duplicateBindings,
      firstDuplicateBody, secondDuplicateBody, vName, tc, aSym, bSym,
      singleton, name]
    side_core
  · simp [duplicateSecondProof, duplicateSubstitution, duplicateBindings,
      firstDuplicateBody, secondDuplicateBody, vName, tc, aSym, bSym,
      singleton, name]
    side_core

/-! ### A nonempty disjoint-variable proof -/

private def callerPair : Pattern := Builder.dvPair (name "x") (name "y")
private def callerDV : Pattern := singleton callerPair
private def calleePair : Pattern := Builder.dvPair vName wName
private def calleeDV : Pattern := singleton calleePair
private def xBody : Pattern := singleton xSym
private def yBody : Pattern := singleton ySym

private def dvBindingsTail : Pattern :=
  singleton (Builder.binding wName (Builder.formula tc yBody))
private def dvBindings : Pattern :=
  Builder.cons (Builder.binding vName (Builder.formula tc xBody)) dvBindingsTail
private def dvSubstitution : Pattern := Builder.substitution dvBindings

private def callerHyps : Pattern :=
  encodeListWith encodeString ["caller-hyp"]
private def calleeHyps : Pattern :=
  encodeListWith encodeString ["callee-hyp"]
private def callerFrame : Pattern := Builder.frame callerDV callerHyps
private def calleeFrame : Pattern := Builder.frame calleeDV calleeHyps

private def dvLookupVProof : RawProof :=
  proofNode "$mm.lookup.here" [vName, tc, xBody, dvBindingsTail]

private def dvLookupWProof : RawProof :=
  proofNode "$mm.lookup.there"
    [dvBindingsTail, wName, tc, yBody, vName, tc, xBody]
    [proofNode "$mm.lookup.here" [wName, tc, yBody, Builder.nil]]

private def varsXProof : RawProof :=
  proofNode "$mm.vars.var" [name "x", Builder.nil, Builder.nil]
    [proofNode "$mm.vars.nil" []]

private def varsYProof : RawProof :=
  proofNode "$mm.vars.var" [name "y", Builder.nil, Builder.nil]
    [proofNode "$mm.vars.nil" []]

private def allPairsProofFor (targetDV : Pattern) : RawProof :=
  proofNode "$mm.all-pairs.cons"
    [targetDV, name "x", Builder.nil, singleton (name "y")]
    [ proofNode "$mm.all-with.cons"
        [targetDV, name "x", name "y", Builder.nil]
        [ proofNode "$mm.dv-rel.forward" [targetDV, name "x", name "y"]
            [proofNode "$mm.member.here" [callerPair, Builder.nil]]
        , proofNode "$mm.all-with.nil" [targetDV, name "x"] ]
    , proofNode "$mm.all-pairs.nil" [targetDV, singleton (name "y")] ]

private def dvListsProofFor (targetDV : Pattern) : RawProof :=
  proofNode "$mm.dv-lists.cons"
    [ dvSubstitution, targetDV, vName, wName, Builder.nil
    , tc, xBody, tc, yBody, singleton (name "x"), singleton (name "y") ]
    [ dvLookupVProof, dvLookupWProof, varsXProof, varsYProof
    , allPairsProofFor targetDV
    , proofNode "$mm.dv-lists.nil" [dvSubstitution, targetDV] ]

def dvExampleProof : RawProof :=
  proofNode "$mm.dv-ok.frames"
    [dvSubstitution, callerDV, callerHyps, calleeDV, calleeHyps]
    [dvListsProofFor callerDV]

private def missingPairCallerFrame : Pattern :=
  Builder.frame Builder.nil callerHyps

def dvMissingPairProof : RawProof :=
  proofNode "$mm.dv-ok.frames"
    [dvSubstitution, Builder.nil, callerHyps, calleeDV, calleeHyps]
    [dvListsProofFor Builder.nil]

theorem nonempty_dv_example_accepts :
    checkRaw validatedSideDefinition
      (dvOK dvSubstitution callerFrame calleeFrame) dvExampleProof = true := by
  simp [dvExampleProof, dvListsProofFor, allPairsProofFor, dvLookupVProof,
    dvLookupWProof, varsXProof, varsYProof, dvSubstitution, dvBindings,
    dvBindingsTail, callerFrame, calleeFrame, callerDV, calleeDV, callerPair,
    calleePair, callerHyps, calleeHyps, xBody, yBody, vName, wName, tc,
    xSym, ySym, singleton, name, encodeListWith]
  side_core

theorem missing_caller_dv_pair_rejects :
    checkRaw validatedSideDefinition
      (dvOK dvSubstitution missingPairCallerFrame calleeFrame)
      dvMissingPairProof = false := by
  simp [dvMissingPairProof, dvListsProofFor, allPairsProofFor, dvLookupVProof,
    dvLookupWProof, varsXProof, varsYProof, dvSubstitution, dvBindings,
    dvBindingsTail, missingPairCallerFrame, calleeFrame, calleeDV, callerPair,
    calleePair, callerHyps, calleeHyps, xBody, yBody, vName, wName, tc,
    xSym, ySym, singleton, name, encodeListWith]
  side_core

end Mettapedia.Languages.Metamath.InferenceSideConditions
