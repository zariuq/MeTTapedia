import Mettapedia.Languages.Megalodon.TermQuantifiedKernel

/-!
# Megalodon polymorphic proof-kernel authority

This layer extends the term-quantified authority with Megalodon's independent
type-variable depth.  The new judgments retain that depth explicitly, require
plain type formation, and admit proof-level type abstraction only at empty
term and proof contexts, matching `Mathdata.extr_propofpf`.

The executable specimen is reconstructed by Megalodon from a theorem inside
an `SType` section.  Its outer type closure, term closure, implication proof,
and term-quantifier proof are all checked by the same finite coGSLT
definition.  Conversion, named known proofs, and polymorphic term
application remain separate later layers.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Megalodon.PolymorphicKernel

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.ExtensionComposition
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.Languages.Megalodon
open Mettapedia.OSLF.MeTTaIL.Syntax

def a (head : String) (arguments : List Pattern := []) : Pattern :=
  .apply head arguments

def m (name : String) : Pattern := .fvar name

def ruleId (value : String) : RuleId := ⟨value⟩

def rule (id : String) (metavariables : List String)
    (premises : List Pattern) (conclusion : Pattern) : RuleSchema :=
  { id := ruleId id
    metavariables := metavariables.map fun name => (name, 0)
    premises
    conclusion }

def plainType (depth type : Pattern) : Pattern :=
  a "MPlainType" [depth, type]

def hasType (signature typeDepth context term type : Pattern) : Pattern :=
  a "MPolyTermHasType" [signature, typeDepth, context, term, type]

def proves
    (signature typeDepth termContext proofContext proposition : Pattern) :
    Pattern :=
  a "MPolyTermProves"
    [signature, typeDepth, termContext, proofContext, proposition]

def lessThan (left right : Pattern) : Pattern :=
  a "MLessThan" [left, right]

def shiftTerm
    (amount cutoff source target : Pattern) : Pattern :=
  a "MShiftTerm" [amount, cutoff, source, target]

def shiftProofContext
    (amount cutoff source target : Pattern) : Pattern :=
  a "MShiftProofContext" [amount, cutoff, source, target]

def substituteTerm
    (index replacement body result : Pattern) : Pattern :=
  a "MSubstituteTerm" [index, replacement, body, result]

/-! ## Plain type formation at an explicit type-variable depth -/

def plainVarRule : RuleSchema :=
  rule "megalodon-poly-type-var" ["depth", "index"]
    [lessThan (m "index") (m "depth")]
    (plainType (m "depth") (a "MTpVar" [m "index"]))

def plainPropRule : RuleSchema :=
  rule "megalodon-poly-type-prop" ["depth"] []
    (plainType (m "depth") (a "MTpProp"))

def plainBaseRule : RuleSchema :=
  rule "megalodon-poly-type-base" ["depth", "index"] []
    (plainType (m "depth") (a "MTpBase" [m "index"]))

def plainArrRule : RuleSchema :=
  rule "megalodon-poly-type-arr" ["depth", "domain", "codomain"]
    [ plainType (m "depth") (m "domain"),
      plainType (m "depth") (m "codomain") ]
    (plainType (m "depth")
      (a "MTpArr" [m "domain", m "codomain"]))

/-! ## Type synthesis under the independent type depth -/

def typeVarZeroRule : RuleSchema :=
  rule "megalodon-poly-term-var-zero"
    ["signature", "typeDepth", "context", "type"] []
    (hasType (m "signature") (m "typeDepth")
      (a "MTyCtxCons" [m "type", m "context"])
      (a "MTmVar" [a "MNZero"]) (m "type"))

def typeVarSuccRule : RuleSchema :=
  rule "megalodon-poly-term-var-succ"
    ["signature", "typeDepth", "context", "head", "variable", "type"]
    [hasType (m "signature") (m "typeDepth") (m "context")
      (a "MTmVar" [m "variable"]) (m "type")]
    (hasType (m "signature") (m "typeDepth")
      (a "MTyCtxCons" [m "head", m "context"])
      (a "MTmVar" [a "MNSucc" [m "variable"]]) (m "type"))

def typeNamedZeroRule : RuleSchema :=
  rule "megalodon-poly-term-named-zero"
    ["name", "type", "signature", "typeDepth", "context"] []
    (hasType
      (a "MSigCons" [m "name", m "type", m "signature"])
      (m "typeDepth") (m "context")
      (a "MTmNamed" [m "name"]) (m "type"))

def typeNamedSuccRule : RuleSchema :=
  rule "megalodon-poly-term-named-succ"
    ["headName", "headType", "signature", "typeDepth", "context",
      "name", "type"]
    [hasType (m "signature") (m "typeDepth") (m "context")
      (a "MTmNamed" [m "name"]) (m "type")]
    (hasType
      (a "MSigCons" [m "headName", m "headType", m "signature"])
      (m "typeDepth") (m "context")
      (a "MTmNamed" [m "name"]) (m "type"))

def typeAppRule : RuleSchema :=
  rule "megalodon-poly-term-app"
    ["signature", "typeDepth", "context", "function", "argument",
      "domain", "codomain"]
    [ hasType (m "signature") (m "typeDepth") (m "context")
        (m "function") (a "MTpArr" [m "domain", m "codomain"]),
      hasType (m "signature") (m "typeDepth") (m "context")
        (m "argument") (m "domain") ]
    (hasType (m "signature") (m "typeDepth") (m "context")
      (a "MTmApp" [m "function", m "argument"]) (m "codomain"))

def typeLamRule : RuleSchema :=
  rule "megalodon-poly-term-lam"
    ["signature", "typeDepth", "context", "domain", "body", "codomain"]
    [ plainType (m "typeDepth") (m "domain"),
      hasType (m "signature") (m "typeDepth")
        (a "MTyCtxCons" [m "domain", m "context"])
        (m "body") (m "codomain") ]
    (hasType (m "signature") (m "typeDepth") (m "context")
      (a "MTmLam" [m "domain", m "body"])
      (a "MTpArr" [m "domain", m "codomain"]))

def typeImpRule : RuleSchema :=
  rule "megalodon-poly-term-imp"
    ["signature", "typeDepth", "context", "domain", "codomain"]
    [ hasType (m "signature") (m "typeDepth") (m "context")
        (m "domain") (a "MTpProp"),
      hasType (m "signature") (m "typeDepth") (m "context")
        (m "codomain") (a "MTpProp") ]
    (hasType (m "signature") (m "typeDepth") (m "context")
      (a "MTmImp" [m "domain", m "codomain"]) (a "MTpProp"))

def typeAllRule : RuleSchema :=
  rule "megalodon-poly-term-all"
    ["signature", "typeDepth", "context", "type", "body"]
    [ plainType (m "typeDepth") (m "type"),
      hasType (m "signature") (m "typeDepth")
        (a "MTyCtxCons" [m "type", m "context"])
        (m "body") (a "MTpProp") ]
    (hasType (m "signature") (m "typeDepth") (m "context")
      (a "MTmAll" [m "type", m "body"]) (a "MTpProp"))

/-! ## Proof checking -/

def proofHypZeroRule : RuleSchema :=
  rule "megalodon-poly-proof-hyp-zero"
    ["signature", "typeDepth", "termContext", "proofContext",
      "proposition"]
    [hasType (m "signature") (m "typeDepth") (m "termContext")
      (m "proposition") (a "MTpProp")]
    (proves (m "signature") (m "typeDepth") (m "termContext")
      (a "MPfCtxCons" [m "proposition", m "proofContext"])
      (m "proposition"))

def proofHypSuccRule : RuleSchema :=
  rule "megalodon-poly-proof-hyp-succ"
    ["signature", "typeDepth", "termContext", "proofContext", "head",
      "proposition"]
    [proves (m "signature") (m "typeDepth") (m "termContext")
      (m "proofContext") (m "proposition")]
    (proves (m "signature") (m "typeDepth") (m "termContext")
      (a "MPfCtxCons" [m "head", m "proofContext"])
      (m "proposition"))

def proofImpIntroRule : RuleSchema :=
  rule "megalodon-poly-proof-imp-intro"
    ["signature", "typeDepth", "termContext", "proofContext", "domain",
      "codomain"]
    [ hasType (m "signature") (m "typeDepth") (m "termContext")
        (m "domain") (a "MTpProp"),
      proves (m "signature") (m "typeDepth") (m "termContext")
        (a "MPfCtxCons" [m "domain", m "proofContext"])
        (m "codomain") ]
    (proves (m "signature") (m "typeDepth") (m "termContext")
      (m "proofContext") (a "MTmImp" [m "domain", m "codomain"]))

def proofImpElimRule : RuleSchema :=
  rule "megalodon-poly-proof-imp-elim"
    ["signature", "typeDepth", "termContext", "proofContext", "domain",
      "codomain"]
    [ proves (m "signature") (m "typeDepth") (m "termContext")
        (m "proofContext") (a "MTmImp" [m "domain", m "codomain"]),
      proves (m "signature") (m "typeDepth") (m "termContext")
        (m "proofContext") (m "domain") ]
    (proves (m "signature") (m "typeDepth") (m "termContext")
      (m "proofContext") (m "codomain"))

def proofAllIntroRule : RuleSchema :=
  rule "megalodon-poly-proof-all-intro"
    ["signature", "typeDepth", "termContext", "proofContext",
      "shiftedProofContext", "type", "body"]
    [ plainType (m "typeDepth") (m "type"),
      shiftProofContext (a "MNSucc" [a "MNZero"]) (a "MNZero")
        (m "proofContext") (m "shiftedProofContext"),
      proves (m "signature") (m "typeDepth")
        (a "MTyCtxCons" [m "type", m "termContext"])
        (m "shiftedProofContext") (m "body") ]
    (proves (m "signature") (m "typeDepth") (m "termContext")
      (m "proofContext") (a "MTmAll" [m "type", m "body"]))

def proofAllElimRule : RuleSchema :=
  rule "megalodon-poly-proof-all-elim"
    ["signature", "typeDepth", "termContext", "proofContext", "type",
      "body", "argument", "result"]
    [ proves (m "signature") (m "typeDepth") (m "termContext")
        (m "proofContext") (a "MTmAll" [m "type", m "body"]),
      hasType (m "signature") (m "typeDepth") (m "termContext")
        (m "argument") (m "type"),
      substituteTerm (a "MNZero") (m "argument")
        (m "body") (m "result") ]
    (proves (m "signature") (m "typeDepth") (m "termContext")
      (m "proofContext") (m "result"))

def proofTypeIntroRule : RuleSchema :=
  rule "megalodon-poly-proof-type-intro" ["signature", "body"]
    [proves (m "signature") (a "MNSucc" [a "MNZero"])
      (a "MTyCtxNil") (a "MPfCtxNil") (m "body")]
    (proves (m "signature") (a "MNZero")
      (a "MTyCtxNil") (a "MPfCtxNil")
      (a "MTmTypeAll" [m "body"]))

def additionalJudgments : List JudgmentDecl :=
  [ { head := "MPlainType", arity := 2 },
    { head := "MPolyTermHasType", arity := 5 },
    { head := "MPolyTermProves", arity := 5 } ]

def additionalRules : List RuleSchema :=
  [ plainVarRule, plainPropRule, plainBaseRule, plainArrRule,
    typeVarZeroRule, typeVarSuccRule, typeNamedZeroRule, typeNamedSuccRule,
    typeAppRule, typeLamRule, typeImpRule, typeAllRule,
    proofHypZeroRule, proofHypSuccRule, proofImpIntroRule, proofImpElimRule,
    proofAllIntroRule, proofAllElimRule, proofTypeIntroRule ]

def definition : CalculusLanguageDef :=
  { TermQuantifiedKernel.definition with
    name := "megalodon-polymorphic-proof-kernel-v1"
    judgments := TermQuantifiedKernel.definition.judgments ++
      additionalJudgments
    rules := TermQuantifiedKernel.definition.rules ++ additionalRules }

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem definition_valid : definition.isValid = true := by
  have hvalidate : definition.toLanguageDef.validate = [] := by
    apply LanguageDef.validate_eq_nil_of_constructorOnly <;>
      simp [definition, definition, TermQuantifiedKernel.definition,
        TermQuantifiedKernel.constructors,
        TermQuantifiedKernel.expressionType,
        TermQuantifiedKernel.expressionConstructor,
        LanguageDef.typeNames, TypeDecl.plain, TermParam.typeExpr,
        TypeExpr.baseNames]
  unfold CalculusLanguageDef.isValid CalculusLanguageDef.hasValidLocalRules
  rw [hvalidate]
  simp [definition, definition, additionalJudgments, additionalRules,
    CalculusLanguageDef.ruleIds, CalculusLanguageDef.judgmentSignatureValid,
    CalculusLanguageDef.judgmentHeads, CalculusLanguageDef.conversionDeclarationValid,
    CalculusLanguageDef.lookupJudgment?, RuleSchema.isValidIn, RuleSchema.isLocallyValid,
    RuleSchema.metavariableNames, RuleSchema.occurrences,
    RuleSchema.patterns, patternMetavariableOccurrencesAt,
    patternsMetavariableOccurrencesAt, patternHasNoCollectionRest,
    patternsHaveNoCollectionRest, CalculusLanguageDef.judgmentSchemaValid,
    fixedConstructorsValid, fixedConstructorListsValid,
    languageHasConstructorArity, Pattern.isWellScoped,
    Pattern.isWellScopedAt, Pattern.isWellScopedListAt,
    Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList, Pattern.zipHead, Pattern.mapHead,
    Pattern.evalHead, rule, ruleId, plainVarRule, plainPropRule,
    plainBaseRule, plainArrRule, typeVarZeroRule, typeVarSuccRule,
    typeNamedZeroRule, typeNamedSuccRule, typeAppRule, typeLamRule,
    typeImpRule, typeAllRule, proofHypZeroRule, proofHypSuccRule,
    proofImpIntroRule, proofImpElimRule, proofAllIntroRule,
    proofAllElimRule, proofTypeIntroRule, plainType, hasType, proves,
    lessThan, shiftProofContext, substituteTerm, a, m,
    TermQuantifiedKernel.definition, TermQuantifiedKernel.constructors,
    TermQuantifiedKernel.rules, TermQuantifiedKernel.rule,
    TermQuantifiedKernel.ruleId, TermQuantifiedKernel.addZeroRule,
    TermQuantifiedKernel.addSuccRule, TermQuantifiedKernel.lessZeroRule,
    TermQuantifiedKernel.lessSuccRule,
    TermQuantifiedKernel.shiftVarAtZeroRule,
    TermQuantifiedKernel.shiftVarBelowRule,
    TermQuantifiedKernel.shiftVarSuccRule,
    TermQuantifiedKernel.shiftNamedRule, TermQuantifiedKernel.shiftAppRule,
    TermQuantifiedKernel.shiftImpRule, TermQuantifiedKernel.shiftAllRule,
    TermQuantifiedKernel.shiftProofNilRule,
    TermQuantifiedKernel.shiftProofConsRule,
    TermQuantifiedKernel.substVarEqualRule,
    TermQuantifiedKernel.substVarBelowRule,
    TermQuantifiedKernel.substVarAboveRule,
    TermQuantifiedKernel.substNamedRule,
    TermQuantifiedKernel.substAppRule, TermQuantifiedKernel.substImpRule,
    TermQuantifiedKernel.substAllRule,
    TermQuantifiedKernel.typeVarZeroRule,
    TermQuantifiedKernel.typeVarSuccRule,
    TermQuantifiedKernel.typeNamedZeroRule,
    TermQuantifiedKernel.typeNamedSuccRule,
    TermQuantifiedKernel.typeAppRule, TermQuantifiedKernel.typeImpRule,
    TermQuantifiedKernel.typeAllRule,
    TermQuantifiedKernel.proofHypZeroRule,
    TermQuantifiedKernel.proofHypSuccRule,
    TermQuantifiedKernel.proofImpIntroRule,
    TermQuantifiedKernel.proofImpElimRule,
    TermQuantifiedKernel.proofAllIntroRule,
    TermQuantifiedKernel.proofAllElimRule,
    TermQuantifiedKernel.addNat, TermQuantifiedKernel.lessThan,
    TermQuantifiedKernel.shiftTerm,
    TermQuantifiedKernel.shiftProofContext,
    TermQuantifiedKernel.substituteTerm, TermQuantifiedKernel.hasType,
    TermQuantifiedKernel.proves, TermQuantifiedKernel.a,
    TermQuantifiedKernel.m,
    List.eraseDups, List.eraseDupsBy]
  simp (config := { maxSteps := 1000000, decide := true })

def validated : ValidatedCalculusLanguageDef := ⟨definition, definition_valid⟩

def coGSLTDefinition : ExtendedLanguageDef calculusLayer :=
  definition.toExtended

def coGSLTSource : coGSLTDefinition.authoredGSLT.Term :=
  coGSLTDefinition.authoredSource

@[simp] theorem coGSLT_source_elaborates :
    calculusLayer.elaborate definition.toLanguageDef coGSLTSource =
      some definition.toCalculus :=
  definition.toExtended_elaborate_authoredSource

private def node (id : String) (arguments : List Pattern)
    (children : List RawProof := []) : RawProof :=
  .node { ruleId := ruleId id, arguments } children

private abbrev ENat := TermQuantifiedKernel.encodeNat
private abbrev ETp := TermQuantifiedKernel.encodeTp
private abbrev ETm := TermQuantifiedKernel.encodeTm
private abbrev ETyCtx := TermQuantifiedKernel.encodeTypeContext
private abbrev EPfCtx := TermQuantifiedKernel.encodeProofContext
private abbrev ESig := TermQuantifiedKernel.encodeSignature

/-! ## Exact polymorphic theorem reconstructed by Megalodon -/

def pType : MathdataKernel.Tp := .arr (.var 0) .prop

def forallBody : MathdataKernel.Tm :=
  .app (.db 1) (.db 0)

def forallDomain : MathdataKernel.Tm :=
  .all (.var 0) forallBody

def shiftedForallBody : MathdataKernel.Tm :=
  .app (.db 2) (.db 0)

def shiftedForallDomain : MathdataKernel.Tm :=
  .all (.var 0) shiftedForallBody

def theoremBody : MathdataKernel.Tm :=
  .all pType (.imp forallDomain forallDomain)

def goalTerm : MathdataKernel.Tm :=
  .typeAll theoremBody

def proofTerm : MathdataKernel.Pf :=
  .typeLam
    (.termLam pType
      (.proofLam forallDomain
        (.termLam (.var 0) (.termApp (.hyp 0) (.db 0)))))

theorem mathdata_kernel_accepts :
    MathdataKernel.inferProof {} 16 0 [] [] proofTerm = some goalTerm := by
  simp [proofTerm, goalTerm, theoremBody, forallDomain, forallBody, pType,
    MathdataKernel.inferProof, MathdataKernel.checkProposition,
    MathdataKernel.inferTerm, MathdataKernel.normalize,
    MathdataKernel.deltaNormalize, MathdataKernel.Tm.normalize,
    MathdataKernel.Tm.normalizeOne, MathdataKernel.Tm.shift,
    MathdataKernel.Tm.instantiate, MathdataKernel.Tm.instantiateAt,
    MathdataKernel.Tp.plainWellFormed]

def goal : Pattern :=
  proves (ESig []) (ENat 0) (ETyCtx []) (EPfCtx []) (ETm goalTerm)

private def lessZeroOneArticle : RawProof :=
  node "megalodon-term-less-zero" [ENat 0]

private def lessZeroTwoArticle : RawProof :=
  node "megalodon-term-less-zero" [ENat 1]

private def plainVarArticle : RawProof :=
  node "megalodon-poly-type-var" [ENat 1, ENat 0]
    [lessZeroOneArticle]

private def plainPropArticle : RawProof :=
  node "megalodon-poly-type-prop" [ENat 1]

private def plainPTypeArticle : RawProof :=
  node "megalodon-poly-type-arr" [ENat 1, ETp (.var 0), ETp .prop]
    [plainVarArticle, plainPropArticle]

private def typePAtPContextArticle : RawProof :=
  node "megalodon-poly-term-var-zero"
    [ESig [], ENat 1, ETyCtx [], ETp pType]

private def typePAtXContextArticle : RawProof :=
  node "megalodon-poly-term-var-succ"
    [ESig [], ENat 1, ETyCtx [pType], ETp (.var 0), ENat 0, ETp pType]
    [typePAtPContextArticle]

private def typePAtYXContextArticle : RawProof :=
  node "megalodon-poly-term-var-succ"
    [ESig [], ENat 1, ETyCtx [.var 0, pType], ETp (.var 0), ENat 1,
      ETp pType]
    [typePAtXContextArticle]

private def typeXAtXPContextArticle : RawProof :=
  node "megalodon-poly-term-var-zero"
    [ESig [], ENat 1, ETyCtx [pType], ETp (.var 0)]

private def typeYAtYXPContextArticle : RawProof :=
  node "megalodon-poly-term-var-zero"
    [ESig [], ENat 1, ETyCtx [.var 0, pType], ETp (.var 0)]

private def typeForallBodyArticle : RawProof :=
  node "megalodon-poly-term-app"
    [ESig [], ENat 1, ETyCtx [.var 0, pType], ETm (.db 1), ETm (.db 0),
      ETp (.var 0), ETp .prop]
    [typePAtXContextArticle, typeXAtXPContextArticle]

private def typeForallDomainArticle : RawProof :=
  node "megalodon-poly-term-all"
    [ESig [], ENat 1, ETyCtx [pType], ETp (.var 0), ETm forallBody]
    [plainVarArticle, typeForallBodyArticle]

private def typeShiftedForallBodyArticle : RawProof :=
  node "megalodon-poly-term-app"
    [ESig [], ENat 1, ETyCtx [.var 0, .var 0, pType], ETm (.db 2),
      ETm (.db 0), ETp (.var 0), ETp .prop]
    [typePAtYXContextArticle, typeYAtYXPContextArticle]

private def typeShiftedForallDomainArticle : RawProof :=
  node "megalodon-poly-term-all"
    [ESig [], ENat 1, ETyCtx [.var 0, pType], ETp (.var 0),
      ETm shiftedForallBody]
    [plainVarArticle, typeShiftedForallBodyArticle]

private def addZeroZeroArticle : RawProof :=
  node "megalodon-term-add-zero" [ENat 0]

private def addZeroOneArticle : RawProof :=
  node "megalodon-term-add-zero" [ENat 1]

private def shiftVarZeroByZeroArticle : RawProof :=
  node "megalodon-term-shift-var-zero" [ENat 0, ENat 0, ENat 0]
    [addZeroZeroArticle]

private def shiftVarZeroByOneArticle : RawProof :=
  node "megalodon-term-shift-var-zero" [ENat 1, ENat 0, ENat 1]
    [addZeroOneArticle]

private def shiftPArticle : RawProof :=
  node "megalodon-term-shift-var-succ"
    [ENat 1, ENat 0, ENat 0, ENat 1]
    [shiftVarZeroByOneArticle]

private def shiftBoundVarArticle : RawProof :=
  node "megalodon-term-shift-var-below" [ENat 1, ENat 0]

private def shiftForallBodyArticle : RawProof :=
  node "megalodon-term-shift-app"
    [ENat 1, ENat 1, ETm (.db 1), ETm (.db 0), ETm (.db 2), ETm (.db 0)]
    [shiftPArticle, shiftBoundVarArticle]

private def shiftForallDomainArticle : RawProof :=
  node "megalodon-term-shift-all"
    [ENat 1, ENat 0, ETp (.var 0), ETm forallBody,
      ETm shiftedForallBody]
    [shiftForallBodyArticle]

private def shiftProofNilArticle : RawProof :=
  node "megalodon-term-shift-proof-nil" [ENat 1, ENat 0]

private def shiftProofContextArticle : RawProof :=
  node "megalodon-term-shift-proof-cons"
    [ENat 1, ENat 0, ETm forallDomain, EPfCtx [],
      ETm shiftedForallDomain, EPfCtx []]
    [shiftForallDomainArticle, shiftProofNilArticle]

private def typeHypArticle : RawProof :=
  node "megalodon-poly-proof-hyp-zero"
    [ESig [], ENat 1, ETyCtx [.var 0, pType], EPfCtx [],
      ETm shiftedForallDomain]
    [typeShiftedForallDomainArticle]

private def substitutePArticle : RawProof :=
  node "megalodon-term-subst-var-above"
    [ENat 0, ETm (.db 0), ENat 1]
    [lessZeroTwoArticle]

private def substituteBoundVarArticle : RawProof :=
  node "megalodon-term-subst-var-equal"
    [ENat 0, ETm (.db 0), ETm (.db 0)]
    [shiftVarZeroByZeroArticle]

private def substituteForallBodyArticle : RawProof :=
  node "megalodon-term-subst-app"
    [ENat 0, ETm (.db 0), ETm (.db 2), ETm (.db 0),
      ETm (.db 1), ETm (.db 0)]
    [substitutePArticle, substituteBoundVarArticle]

private def proofTermApplicationArticle : RawProof :=
  node "megalodon-poly-proof-all-elim"
    [ESig [], ENat 1, ETyCtx [.var 0, pType],
      EPfCtx [shiftedForallDomain], ETp (.var 0),
      ETm shiftedForallBody, ETm (.db 0), ETm forallBody]
    [typeHypArticle, typeXAtXPContextArticle,
      substituteForallBodyArticle]

private def proofXIntroductionArticle : RawProof :=
  node "megalodon-poly-proof-all-intro"
    [ESig [], ENat 1, ETyCtx [pType], EPfCtx [forallDomain],
      EPfCtx [shiftedForallDomain], ETp (.var 0), ETm forallBody]
    [plainVarArticle, shiftProofContextArticle,
      proofTermApplicationArticle]

private def proofImpIntroductionArticle : RawProof :=
  node "megalodon-poly-proof-imp-intro"
    [ESig [], ENat 1, ETyCtx [pType], EPfCtx [],
      ETm forallDomain, ETm forallDomain]
    [typeForallDomainArticle, proofXIntroductionArticle]

private def proofPIntroductionArticle : RawProof :=
  node "megalodon-poly-proof-all-intro"
    [ESig [], ENat 1, ETyCtx [], EPfCtx [], EPfCtx [],
      ETp pType, ETm (.imp forallDomain forallDomain)]
    [ plainPTypeArticle,
      node "megalodon-term-shift-proof-nil" [ENat 1, ENat 0],
      proofImpIntroductionArticle ]

def article : RawProof :=
  node "megalodon-poly-proof-type-intro" [ESig [], ETm theoremBody]
    [proofPIntroductionArticle]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem polymorphic_forall_identity_accepted :
    checkRaw validated goal article = true := by
  simp [checkRaw, validated, definition, definition,
    additionalJudgments, additionalRules, rule, ruleId,
    plainVarRule, plainPropRule, plainBaseRule, plainArrRule,
    typeVarZeroRule, typeVarSuccRule, typeNamedZeroRule,
    typeNamedSuccRule, typeAppRule, typeLamRule, typeImpRule, typeAllRule,
    proofHypZeroRule, proofHypSuccRule, proofImpIntroRule,
    proofImpElimRule, proofAllIntroRule, proofAllElimRule,
    proofTypeIntroRule,
    TermQuantifiedKernel.definition, TermQuantifiedKernel.constructors,
    TermQuantifiedKernel.rules, TermQuantifiedKernel.rule,
    TermQuantifiedKernel.ruleId, TermQuantifiedKernel.addZeroRule,
    TermQuantifiedKernel.addSuccRule, TermQuantifiedKernel.lessZeroRule,
    TermQuantifiedKernel.lessSuccRule,
    TermQuantifiedKernel.shiftVarAtZeroRule,
    TermQuantifiedKernel.shiftVarBelowRule,
    TermQuantifiedKernel.shiftVarSuccRule,
    TermQuantifiedKernel.shiftNamedRule, TermQuantifiedKernel.shiftAppRule,
    TermQuantifiedKernel.shiftImpRule, TermQuantifiedKernel.shiftAllRule,
    TermQuantifiedKernel.shiftProofNilRule,
    TermQuantifiedKernel.shiftProofConsRule,
    TermQuantifiedKernel.substVarEqualRule,
    TermQuantifiedKernel.substVarBelowRule,
    TermQuantifiedKernel.substVarAboveRule,
    TermQuantifiedKernel.substNamedRule,
    TermQuantifiedKernel.substAppRule, TermQuantifiedKernel.substImpRule,
    TermQuantifiedKernel.substAllRule,
    TermQuantifiedKernel.typeVarZeroRule,
    TermQuantifiedKernel.typeVarSuccRule,
    TermQuantifiedKernel.typeNamedZeroRule,
    TermQuantifiedKernel.typeNamedSuccRule,
    TermQuantifiedKernel.typeAppRule, TermQuantifiedKernel.typeImpRule,
    TermQuantifiedKernel.typeAllRule,
    TermQuantifiedKernel.proofHypZeroRule,
    TermQuantifiedKernel.proofHypSuccRule,
    TermQuantifiedKernel.proofImpIntroRule,
    TermQuantifiedKernel.proofImpElimRule,
    TermQuantifiedKernel.proofAllIntroRule,
    TermQuantifiedKernel.proofAllElimRule,
    TermQuantifiedKernel.addNat, TermQuantifiedKernel.lessThan,
    TermQuantifiedKernel.shiftTerm,
    TermQuantifiedKernel.shiftProofContext,
    TermQuantifiedKernel.substituteTerm, TermQuantifiedKernel.hasType,
    TermQuantifiedKernel.proves, TermQuantifiedKernel.a,
    TermQuantifiedKernel.m,
    article, proofPIntroductionArticle, proofImpIntroductionArticle,
    proofXIntroductionArticle, proofTermApplicationArticle, typeHypArticle,
    typeShiftedForallDomainArticle, typeShiftedForallBodyArticle,
    typePAtYXContextArticle, typePAtXContextArticle,
    typePAtPContextArticle, typeYAtYXPContextArticle,
    typeXAtXPContextArticle, typeForallDomainArticle,
    typeForallBodyArticle, plainPTypeArticle, plainVarArticle,
    plainPropArticle, lessZeroOneArticle, lessZeroTwoArticle,
    shiftProofContextArticle, shiftForallDomainArticle,
    shiftForallBodyArticle, shiftPArticle, shiftVarZeroByOneArticle,
    addZeroOneArticle, shiftBoundVarArticle, shiftProofNilArticle,
    substituteForallBodyArticle, substitutePArticle,
    substituteBoundVarArticle, shiftVarZeroByZeroArticle,
    addZeroZeroArticle, node, instantiateRule?, CalculusLanguageDef.lookupRule?,
    RuleSchema.sideConditionsHold, instantiateSchema?, instantiateSchemas?,
    goal, goalTerm, theoremBody, forallDomain, forallBody,
    shiftedForallDomain, shiftedForallBody, pType,
    TermQuantifiedKernel.encodeSignature,
    TermQuantifiedKernel.encodeTypeContext,
    TermQuantifiedKernel.encodeProofContext,
    TermQuantifiedKernel.encodeTm, TermQuantifiedKernel.encodeTp,
    TermQuantifiedKernel.encodeNat, plainType, hasType, proves, lessThan,
    shiftProofContext, substituteTerm, a, m]
  simp (config := { maxSteps := 2000000, decide := true })
    [checkRaw, checkRawChildren, instantiateRule?, CalculusLanguageDef.lookupRule?,
      instantiateSchema?, instantiateSchemaAt?, instantiateSchemas?,
      instantiateSchemasAt?, lookupArgumentAt?]

def wrongGoal : Pattern :=
  proves (ESig []) (ENat 0) (ETyCtx []) (EPfCtx [])
    (ETm (.typeAll (.named "fabricated")))

theorem wrong_goal_rejected :
    checkRaw validated wrongGoal article = false := by
  cases hcheck : checkRaw validated wrongGoal article with
  | false => rfl
  | true =>
      exfalso
      have equality :=
        checkRaw_goal_unique polymorphic_forall_identity_accepted hcheck
      simp [goal, wrongGoal, proves, goalTerm, theoremBody, forallDomain,
        forallBody, pType, TermQuantifiedKernel.encodeSignature,
        TermQuantifiedKernel.encodeTypeContext,
        TermQuantifiedKernel.encodeProofContext,
        TermQuantifiedKernel.encodeTm, TermQuantifiedKernel.encodeTp,
        TermQuantifiedKernel.encodeNat, TermQuantifiedKernel.a, a] at equality

end Mettapedia.Languages.Megalodon.PolymorphicKernel
