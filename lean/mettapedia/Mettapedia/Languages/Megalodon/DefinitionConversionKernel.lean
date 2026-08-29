import Mettapedia.Languages.Megalodon.EnvironmentKernel
import Mettapedia.GSLT.LanguageDef.InferenceRuntimeAdequacy

/-!
# Megalodon definition and conversion kernel

This layer retains parameter-versus-definition declarations instead of
projecting both to a type-only signature.  The retained declarations support
proof-relevant delta and beta reduction, finite reduction paths, and a rooted
binary conversion judgment.  A final proof rule ties the declaration list to
the exact type signature used by the existing checked-environment kernel and
requires the synthesized and declared propositions to have a witnessed common
reduct.

The conversion definition covers the beta, delta, and eta steps needed by
real Megalodon definition-bearing documents.  Eta reuses the already-admitted
term-shift judgment: shifting the proposed reduct by one reconstructs the
function beneath the lambda, which is proof-relevant evidence that the bound
variable is unused.  A general normalization-completeness theorem remains a
separate obligation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Megalodon.DefinitionConversionKernel

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.ExtensionComposition
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.Languages.Megalodon
open Mettapedia.OSLF.MeTTaIL.Syntax

attribute [local simp]
  EnvironmentKernel.rule EnvironmentKernel.ruleId
  EnvironmentKernel.addNat EnvironmentKernel.lessThan
  EnvironmentKernel.plainType EnvironmentKernel.baseHasType
  EnvironmentKernel.baseProves EnvironmentKernel.proves
  EnvironmentKernel.knownMember EnvironmentKernel.shiftType
  EnvironmentKernel.substituteType EnvironmentKernel.substituteTypeInTerm
  EnvironmentKernel.shiftProofContext EnvironmentKernel.substituteTerm
  EnvironmentKernel.checksDocument EnvironmentKernel.a EnvironmentKernel.m
  EnvironmentKernel.shiftTypeVarZeroRule
  EnvironmentKernel.shiftTypeVarBelowRule
  EnvironmentKernel.shiftTypeVarSuccRule
  EnvironmentKernel.shiftTypePropRule EnvironmentKernel.shiftTypeBaseRule
  EnvironmentKernel.shiftTypeArrRule EnvironmentKernel.shiftTypeAllRule
  EnvironmentKernel.substituteTypeVarEqualRule
  EnvironmentKernel.substituteTypeVarBelowRule
  EnvironmentKernel.substituteTypeVarAboveRule
  EnvironmentKernel.substituteTypePropRule
  EnvironmentKernel.substituteTypeBaseRule
  EnvironmentKernel.substituteTypeArrRule
  EnvironmentKernel.substituteTypeAllRule
  EnvironmentKernel.substituteTypeTermVarRule
  EnvironmentKernel.substituteTypeTermNamedRule
  EnvironmentKernel.substituteTypeTermPrimRule
  EnvironmentKernel.substituteTypeTermAppRule
  EnvironmentKernel.substituteTypeTermLamRule
  EnvironmentKernel.substituteTypeTermImpRule
  EnvironmentKernel.substituteTypeTermAllRule
  EnvironmentKernel.substituteTypeTermTypeAppRule
  EnvironmentKernel.substituteTypeTermTypeLamRule
  EnvironmentKernel.substituteTypeTermTypeAllRule
  EnvironmentKernel.shiftTermPrimRule EnvironmentKernel.shiftTermLamRule
  EnvironmentKernel.shiftTermTypeAppRule
  EnvironmentKernel.shiftTermTypeLamRule
  EnvironmentKernel.shiftTermTypeAllRule
  EnvironmentKernel.substituteTermPrimRule
  EnvironmentKernel.substituteTermLamRule
  EnvironmentKernel.substituteTermTypeAppRule
  EnvironmentKernel.substituteTermTypeLamRule
  EnvironmentKernel.substituteTermTypeAllRule
  EnvironmentKernel.knownHereRule EnvironmentKernel.knownThereRule
  EnvironmentKernel.proofBaseRule EnvironmentKernel.proofKnownRule
  EnvironmentKernel.proofImpIntroRule EnvironmentKernel.proofImpElimRule
  EnvironmentKernel.proofTypeElimRule EnvironmentKernel.proofAllElimRule
  EnvironmentKernel.proofAllIntroRule EnvironmentKernel.proofTypeIntroRule
  EnvironmentKernel.documentNilRule EnvironmentKernel.documentConsRule

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

def projectSignature (declarations signature : Pattern) : Pattern :=
  a "MProjectSignature" [declarations, signature]

/-- Formation of a possibly prefix-polymorphic Mathdata type at an explicit
type-variable depth.  Unlike `MPlainType`, this admits `MTpAll` only as a
prefix, matching `MathdataKernel.Tp.polyWellFormed`. -/
def polyType (depth type : Pattern) : Pattern :=
  a "MPolyType" [depth, type]

/-- A retained parameter/definition list is well formed and projects to the
given type-only signature.  Definition bodies are checked against the tail
signature, so a definition cannot grant itself its declared type. -/
def declarationsValid (declarations signature : Pattern) : Pattern :=
  a "MTermDeclarationsValid" [declarations, signature]

/-- Pointwise lifting of an ordered term-variable context across a type
binder, corresponding to Megalodon's `List.map (tpshift 0 1) cxtm`. -/
def shiftTypeContext
    (amount cutoff source target : Pattern) : Pattern :=
  a "MShiftTypeContext" [amount, cutoff, source, target]

private def definitionMember
    (declarations name type body : Pattern) : Pattern :=
  a "MDefinitionMember" [declarations, name, type, body]

private def substituteTerm
    (index replacement body result : Pattern) : Pattern :=
  a "MSubstituteTerm" [index, replacement, body, result]

private def substituteTypeInTerm
    (index replacement body result : Pattern) : Pattern :=
  a "MSubstituteTypeInTerm" [index, replacement, body, result]

private def shiftTerm
    (amount cutoff source target : Pattern) : Pattern :=
  a "MShiftTerm" [amount, cutoff, source, target]

def reduces
    (declarations source target : Pattern) : Pattern :=
  a "MDefinitionReduces" [declarations, source, target]

def reductionPath
    (declarations source target : Pattern) : Pattern :=
  a "MDefinitionReductionPath" [declarations, source, target]

def scopedTerm (declarations term : Pattern) : Pattern :=
  a "MScopedTerm" [declarations, term]

def converts
    (declarations left right : Pattern) : Pattern :=
  a "MDefinitionConverts"
    [scopedTerm declarations left, scopedTerm declarations right]

def baseProves
    (environment typeDepth termContext proofContext proposition : Pattern) :
    Pattern :=
  a "MMathdataProves"
    [environment, typeDepth, termContext, proofContext, proposition]

def fullProves
    (environment typeDepth termContext proofContext proposition : Pattern) :
    Pattern :=
  a "MDefinitionProves"
    [environment, typeDepth, termContext, proofContext, proposition]

/-- A source proposition is well formed and has the selected forward-reduct
representative.  Keeping the source and representative distinct is essential
for Megalodon proof abstraction: the source annotation is checked, while the
representative is the assumption made available to the body. -/
def propositionRepresentative
    (declarations signature typeDepth termContext source target : Pattern) :
    Pattern :=
  a "MDefinitionPropositionRepresentative"
    [declarations, signature, typeDepth, termContext, source, target]

/-! ## Declaration projection and lookup -/

def projectNilRule : RuleSchema :=
  rule "megalodon-def-project-nil" [] []
    (projectSignature (a "MDeclNil") (a "MSigNil"))

private def projectParameterRule : RuleSchema :=
  rule "megalodon-def-project-parameter"
    ["name", "type", "tail", "tailSignature"]
    [projectSignature (m "tail") (m "tailSignature")]
    (projectSignature
      (a "MDeclParameter" [m "name", m "type", m "tail"])
      (a "MSigCons" [m "name", m "type", m "tailSignature"]))

def projectDefinitionRule : RuleSchema :=
  rule "megalodon-def-project-definition"
    ["name", "type", "body", "tail", "tailSignature"]
    [projectSignature (m "tail") (m "tailSignature")]
    (projectSignature
      (a "MDeclDefinition"
        [m "name", m "type", m "body", m "tail"])
      (a "MSigCons" [m "name", m "type", m "tailSignature"]))

/-! ## Prefix-polymorphic type and retained-declaration validation -/

def polyTypePlainRule : RuleSchema :=
  rule "megalodon-def-poly-type-plain" ["depth", "type"]
    [EnvironmentKernel.plainType (m "depth") (m "type")]
    (polyType (m "depth") (m "type"))

private def polyTypeAllRule : RuleSchema :=
  rule "megalodon-def-poly-type-all" ["depth", "body"]
    [polyType (a "MNSucc" [m "depth"]) (m "body")]
    (polyType (m "depth") (a "MTpAll" [m "body"]))

private def declarationsValidNilRule : RuleSchema :=
  rule "megalodon-def-declarations-valid-nil" [] []
    (declarationsValid (a "MDeclNil") (a "MSigNil"))

private def declarationsValidParameterRule : RuleSchema :=
  rule "megalodon-def-declarations-valid-parameter"
    ["name", "type", "tail", "tailSignature"]
    [ polyType (a "MNZero") (m "type"),
      declarationsValid (m "tail") (m "tailSignature") ]
    (declarationsValid
      (a "MDeclParameter" [m "name", m "type", m "tail"])
      (a "MSigCons" [m "name", m "type", m "tailSignature"]))

private def declarationsValidDefinitionRule : RuleSchema :=
  rule "megalodon-def-declarations-valid-definition"
    ["name", "type", "body", "tail", "tailSignature"]
    [ polyType (a "MNZero") (m "type"),
      declarationsValid (m "tail") (m "tailSignature"),
      EnvironmentKernel.baseHasType
        (m "tailSignature") (a "MNZero") (a "MTyCtxNil")
        (m "body") (m "type") ]
    (declarationsValid
      (a "MDeclDefinition"
        [m "name", m "type", m "body", m "tail"])
      (a "MSigCons" [m "name", m "type", m "tailSignature"]))

/-! ## Term-level type abstraction and application -/

private def shiftTypeContextNilRule : RuleSchema :=
  rule "megalodon-def-shift-type-context-nil"
    ["amount", "cutoff"] []
    (shiftTypeContext (m "amount") (m "cutoff")
      (a "MTyCtxNil") (a "MTyCtxNil"))

private def shiftTypeContextConsRule : RuleSchema :=
  rule "megalodon-def-shift-type-context-cons"
    ["amount", "cutoff", "head", "headResult", "tail", "tailResult"]
    [ EnvironmentKernel.shiftType
        (m "amount") (m "cutoff") (m "head") (m "headResult"),
      shiftTypeContext
        (m "amount") (m "cutoff") (m "tail") (m "tailResult") ]
    (shiftTypeContext (m "amount") (m "cutoff")
      (a "MTyCtxCons" [m "head", m "tail"])
      (a "MTyCtxCons" [m "headResult", m "tailResult"]))

private def termTypeAppRule : RuleSchema :=
  rule "megalodon-def-term-type-app"
    ["signature", "typeDepth", "context", "function", "body", "type",
      "result"]
    [ EnvironmentKernel.baseHasType
        (m "signature") (m "typeDepth") (m "context")
        (m "function") (a "MTpAll" [m "body"]),
      EnvironmentKernel.plainType (m "typeDepth") (m "type"),
      EnvironmentKernel.substituteType
        (a "MNZero") (m "type") (m "body") (m "result") ]
    (EnvironmentKernel.baseHasType
      (m "signature") (m "typeDepth") (m "context")
      (a "MTmTypeApp" [m "function", m "type"]) (m "result"))

private def termTypeLamRule : RuleSchema :=
  rule "megalodon-def-term-type-lam"
    ["signature", "typeDepth", "context", "shiftedContext", "body",
      "bodyType"]
    [ shiftTypeContext (a "MNSucc" [a "MNZero"]) (a "MNZero")
        (m "context") (m "shiftedContext"),
      EnvironmentKernel.baseHasType
        (m "signature") (a "MNSucc" [m "typeDepth"])
        (m "shiftedContext") (m "body") (m "bodyType") ]
    (EnvironmentKernel.baseHasType
      (m "signature") (m "typeDepth") (m "context")
      (a "MTmTypeLam" [m "body"]) (a "MTpAll" [m "bodyType"]))

private def definitionHereRule : RuleSchema :=
  rule "megalodon-def-member-here"
    ["name", "type", "body", "tail"] []
    (definitionMember
      (a "MDeclDefinition"
        [m "name", m "type", m "body", m "tail"])
      (m "name") (m "type") (m "body"))

private def definitionThereParameterRule : RuleSchema :=
  rule "megalodon-def-member-there-parameter"
    ["headName", "headType", "tail", "name", "type", "body"]
    [definitionMember (m "tail") (m "name") (m "type") (m "body")]
    (definitionMember
      (a "MDeclParameter" [m "headName", m "headType", m "tail"])
      (m "name") (m "type") (m "body"))

private def definitionThereDefinitionRule : RuleSchema :=
  rule "megalodon-def-member-there-definition"
    ["headName", "headType", "headBody", "tail", "name", "type", "body"]
    [definitionMember (m "tail") (m "name") (m "type") (m "body")]
    (definitionMember
      (a "MDeclDefinition"
        [m "headName", m "headType", m "headBody", m "tail"])
      (m "name") (m "type") (m "body"))

/-! ## One beta-delta reduction, closed under every term constructor -/

private def reduceDeltaRule : RuleSchema :=
  rule "megalodon-def-reduce-delta"
    ["declarations", "name", "type", "body"]
    [definitionMember (m "declarations") (m "name") (m "type") (m "body")]
    (reduces (m "declarations")
      (a "MTmNamed" [m "name"]) (m "body"))

private def reduceBetaRule : RuleSchema :=
  rule "megalodon-def-reduce-beta"
    ["declarations", "type", "body", "argument", "result"]
    [substituteTerm (a "MNZero") (m "argument") (m "body") (m "result")]
    (reduces (m "declarations")
      (a "MTmApp"
        [a "MTmLam" [m "type", m "body"], m "argument"])
      (m "result"))

private def reduceTypeBetaRule : RuleSchema :=
  rule "megalodon-def-reduce-type-beta"
    ["declarations", "body", "type", "result"]
    [substituteTypeInTerm (a "MNZero") (m "type") (m "body") (m "result")]
    (reduces (m "declarations")
      (a "MTmTypeApp" [a "MTmTypeLam" [m "body"], m "type"])
      (m "result"))

/-- Eta contraction uses the inherited proof-relevant shift relation as the
unused-binder witness: lifting `result` by one must reconstruct `function`. -/
private def reduceEtaRule : RuleSchema :=
  rule "megalodon-def-reduce-eta"
    ["declarations", "type", "function", "result"]
    [shiftTerm (a "MNSucc" [a "MNZero"]) (a "MNZero")
      (m "result") (m "function")]
    (reduces (m "declarations")
      (a "MTmLam"
        [m "type", a "MTmApp"
          [m "function", a "MTmVar" [a "MNZero"]]])
      (m "result"))

private def reduceAppFunctionRule : RuleSchema :=
  rule "megalodon-def-reduce-app-function"
    ["declarations", "function", "functionResult", "argument"]
    [reduces (m "declarations") (m "function") (m "functionResult")]
    (reduces (m "declarations")
      (a "MTmApp" [m "function", m "argument"])
      (a "MTmApp" [m "functionResult", m "argument"]))

def reduceAppArgumentRule : RuleSchema :=
  rule "megalodon-def-reduce-app-argument"
    ["declarations", "function", "argument", "argumentResult"]
    [reduces (m "declarations") (m "argument") (m "argumentResult")]
    (reduces (m "declarations")
      (a "MTmApp" [m "function", m "argument"])
      (a "MTmApp" [m "function", m "argumentResult"]))

private def reduceLamBodyRule : RuleSchema :=
  rule "megalodon-def-reduce-lam-body"
    ["declarations", "type", "body", "bodyResult"]
    [reduces (m "declarations") (m "body") (m "bodyResult")]
    (reduces (m "declarations")
      (a "MTmLam" [m "type", m "body"])
      (a "MTmLam" [m "type", m "bodyResult"]))

private def reduceImpDomainRule : RuleSchema :=
  rule "megalodon-def-reduce-imp-domain"
    ["declarations", "domain", "domainResult", "codomain"]
    [reduces (m "declarations") (m "domain") (m "domainResult")]
    (reduces (m "declarations")
      (a "MTmImp" [m "domain", m "codomain"])
      (a "MTmImp" [m "domainResult", m "codomain"]))

def reduceImpCodomainRule : RuleSchema :=
  rule "megalodon-def-reduce-imp-codomain"
    ["declarations", "domain", "codomain", "codomainResult"]
    [reduces (m "declarations") (m "codomain") (m "codomainResult")]
    (reduces (m "declarations")
      (a "MTmImp" [m "domain", m "codomain"])
      (a "MTmImp" [m "domain", m "codomainResult"]))

private def reduceAllBodyRule : RuleSchema :=
  rule "megalodon-def-reduce-all-body"
    ["declarations", "type", "body", "bodyResult"]
    [reduces (m "declarations") (m "body") (m "bodyResult")]
    (reduces (m "declarations")
      (a "MTmAll" [m "type", m "body"])
      (a "MTmAll" [m "type", m "bodyResult"]))

private def reduceTypeAppFunctionRule : RuleSchema :=
  rule "megalodon-def-reduce-type-app-function"
    ["declarations", "function", "functionResult", "type"]
    [reduces (m "declarations") (m "function") (m "functionResult")]
    (reduces (m "declarations")
      (a "MTmTypeApp" [m "function", m "type"])
      (a "MTmTypeApp" [m "functionResult", m "type"]))

private def reduceTypeLamBodyRule : RuleSchema :=
  rule "megalodon-def-reduce-type-lam-body"
    ["declarations", "body", "bodyResult"]
    [reduces (m "declarations") (m "body") (m "bodyResult")]
    (reduces (m "declarations")
      (a "MTmTypeLam" [m "body"])
      (a "MTmTypeLam" [m "bodyResult"]))

private def reduceTypeAllBodyRule : RuleSchema :=
  rule "megalodon-def-reduce-type-all-body"
    ["declarations", "body", "bodyResult"]
    [reduces (m "declarations") (m "body") (m "bodyResult")]
    (reduces (m "declarations")
      (a "MTmTypeAll" [m "body"])
      (a "MTmTypeAll" [m "bodyResult"]))

/-! ## Finite conversion evidence and the proof boundary -/

def pathReflRule : RuleSchema :=
  rule "megalodon-def-path-refl" ["declarations", "term"] []
    (reductionPath (m "declarations") (m "term") (m "term"))

def pathStepRule : RuleSchema :=
  rule "megalodon-def-path-step"
    ["declarations", "source", "middle", "target"]
    [ reduces (m "declarations") (m "source") (m "middle"),
      reductionPath (m "declarations") (m "middle") (m "target") ]
    (reductionPath (m "declarations") (m "source") (m "target"))

def conversionCommonRule : RuleSchema :=
  rule "megalodon-def-conversion-common"
    ["declarations", "left", "right", "common"]
    [ reductionPath (m "declarations") (m "left") (m "common"),
      reductionPath (m "declarations") (m "right") (m "common") ]
    (converts (m "declarations") (m "left") (m "right"))

def fullProofRule : RuleSchema :=
  rule "megalodon-def-proof"
    ["primitives", "declarations", "signature", "known", "typeDepth",
      "termContext", "proofContext", "synthesized", "proposition"]
    [ projectSignature (m "declarations") (m "signature"),
      baseProves
        (a "MEnvironment" [m "primitives", m "signature", m "known"])
        (m "typeDepth") (m "termContext") (m "proofContext")
        (m "synthesized"),
      converts (m "declarations") (m "synthesized") (m "proposition") ]
    (fullProves
      (a "MFullEnvironment"
        [m "primitives", m "declarations", m "known"])
      (m "typeDepth") (m "termContext") (m "proofContext")
      (m "proposition"))

/-! ## Definition-aware dependent evidence rules

Megalodon's proof kernel normalizes at selected proof constructors rather than
only at the final theorem boundary.  In particular, proof abstraction checks
the authored domain but places its reduced representative in the proof
context.  The rules below expose each such choice as replayable evidence.
-/

private def propositionPlainRule : RuleSchema :=
  rule "megalodon-def-proposition-plain"
    ["declarations", "signature", "typeDepth", "termContext", "source",
      "target"]
    [ projectSignature (m "declarations") (m "signature"),
      EnvironmentKernel.baseHasType
        (m "signature") (m "typeDepth") (m "termContext")
        (m "source") (a "MTpProp"),
      reductionPath (m "declarations") (m "source") (m "target") ]
    (propositionRepresentative
      (m "declarations") (m "signature") (m "typeDepth")
      (m "termContext") (m "source") (m "target"))

private def propositionTypeAllRule : RuleSchema :=
  rule "megalodon-def-proposition-type-all"
    ["declarations", "signature", "typeDepth", "termContext", "sourceBody",
      "targetBody"]
    [ propositionRepresentative
        (m "declarations") (m "signature")
        (a "MNSucc" [m "typeDepth"]) (a "MTyCtxNil")
        (m "sourceBody") (m "targetBody") ]
    (propositionRepresentative
      (m "declarations") (m "signature") (m "typeDepth")
      (m "termContext") (a "MTmTypeAll" [m "sourceBody"])
      (a "MTmTypeAll" [m "targetBody"]))

private def fullConvertRule : RuleSchema :=
  rule "megalodon-def-proof-convert"
    ["primitives", "declarations", "known", "typeDepth", "termContext",
      "proofContext", "source", "target"]
    [ fullProves
        (a "MFullEnvironment"
          [m "primitives", m "declarations", m "known"])
        (m "typeDepth") (m "termContext") (m "proofContext") (m "source"),
      converts (m "declarations") (m "source") (m "target") ]
    (fullProves
      (a "MFullEnvironment"
        [m "primitives", m "declarations", m "known"])
      (m "typeDepth") (m "termContext") (m "proofContext") (m "target"))

private def fullImpIntroRule : RuleSchema :=
  rule "megalodon-def-proof-imp-intro"
    ["primitives", "declarations", "signature", "known", "typeDepth",
      "termContext", "proofContext", "sourceDomain", "domain", "codomain"]
    [ propositionRepresentative
        (m "declarations") (m "signature") (m "typeDepth")
        (m "termContext") (m "sourceDomain") (m "domain"),
      fullProves
        (a "MFullEnvironment"
          [m "primitives", m "declarations", m "known"])
        (m "typeDepth") (m "termContext")
        (a "MPfCtxCons" [m "domain", m "proofContext"])
        (m "codomain") ]
    (fullProves
      (a "MFullEnvironment"
        [m "primitives", m "declarations", m "known"])
      (m "typeDepth") (m "termContext") (m "proofContext")
      (a "MTmImp" [m "domain", m "codomain"]))

private def fullImpElimRule : RuleSchema :=
  rule "megalodon-def-proof-imp-elim"
    ["environment", "typeDepth", "termContext", "proofContext", "domain",
      "codomain"]
    [ fullProves (m "environment") (m "typeDepth") (m "termContext")
        (m "proofContext") (a "MTmImp" [m "domain", m "codomain"]),
      fullProves (m "environment") (m "typeDepth") (m "termContext")
        (m "proofContext") (m "domain") ]
    (fullProves (m "environment") (m "typeDepth") (m "termContext")
      (m "proofContext") (m "codomain"))

private def fullAllIntroRule : RuleSchema :=
  rule "megalodon-def-proof-all-intro"
    ["environment", "typeDepth", "termContext", "proofContext",
      "shiftedProofContext", "type", "body"]
    [ EnvironmentKernel.plainType (m "typeDepth") (m "type"),
      EnvironmentKernel.shiftProofContext
        (a "MNSucc" [a "MNZero"]) (a "MNZero")
        (m "proofContext") (m "shiftedProofContext"),
      fullProves (m "environment") (m "typeDepth")
        (a "MTyCtxCons" [m "type", m "termContext"])
        (m "shiftedProofContext") (m "body") ]
    (fullProves (m "environment") (m "typeDepth") (m "termContext")
      (m "proofContext") (a "MTmAll" [m "type", m "body"]))

private def fullAllElimRule : RuleSchema :=
  rule "megalodon-def-proof-all-elim"
    ["primitives", "declarations", "signature", "known", "typeDepth",
      "termContext", "proofContext", "type", "body", "argument",
      "argumentRepresentative", "substituted", "result"]
    [ fullProves
        (a "MFullEnvironment"
          [m "primitives", m "declarations", m "known"])
        (m "typeDepth") (m "termContext") (m "proofContext")
        (a "MTmAll" [m "type", m "body"]),
      projectSignature (m "declarations") (m "signature"),
      EnvironmentKernel.baseHasType
        (m "signature") (m "typeDepth") (m "termContext")
        (m "argument") (m "type"),
      reductionPath
        (m "declarations") (m "argument") (m "argumentRepresentative"),
      substituteTerm (a "MNZero") (m "argumentRepresentative")
        (m "body") (m "substituted"),
      reductionPath (m "declarations") (m "substituted") (m "result") ]
    (fullProves
      (a "MFullEnvironment"
        [m "primitives", m "declarations", m "known"])
      (m "typeDepth") (m "termContext") (m "proofContext") (m "result"))

private def fullTypeElimRule : RuleSchema :=
  rule "megalodon-def-proof-type-elim"
    ["environment", "typeDepth", "termContext", "proofContext", "body",
      "type", "result"]
    [ fullProves (m "environment") (m "typeDepth") (m "termContext")
        (m "proofContext") (a "MTmTypeAll" [m "body"]),
      EnvironmentKernel.plainType (m "typeDepth") (m "type"),
      substituteTypeInTerm
        (a "MNZero") (m "type") (m "body") (m "result") ]
    (fullProves (m "environment") (m "typeDepth") (m "termContext")
      (m "proofContext") (m "result"))

private def fullTypeIntroRule : RuleSchema :=
  rule "megalodon-def-proof-type-intro"
    ["environment", "typeDepth", "body"]
    [ fullProves (m "environment") (a "MNSucc" [m "typeDepth"])
        (a "MTyCtxNil") (a "MPfCtxNil") (m "body") ]
    (fullProves (m "environment") (m "typeDepth")
      (a "MTyCtxNil") (a "MPfCtxNil") (a "MTmTypeAll" [m "body"]))

def definitionParameterName : String :=
  "0000000000000000000000000000000000000000000000000000000000000031"

def identityDefinitionName : String :=
  "c66d8b1a4890fa183623eed6b4b2a7b9ec9c5f9dc957107567cab450e3bed2d8"

def additionalConstructors : List (String × Nat) :=
  [ ("MDeclNil", 0), ("MDeclParameter", 3), ("MDeclDefinition", 4),
    ("MFullEnvironment", 3), ("MScopedTerm", 2),
    (definitionParameterName, 0), (identityDefinitionName, 0) ]

private def additionalJudgments : List JudgmentDecl :=
  [ { head := "MProjectSignature", arity := 2 },
    { head := "MPolyType", arity := 2 },
    { head := "MTermDeclarationsValid", arity := 2 },
    { head := "MShiftTypeContext", arity := 4 },
    { head := "MDefinitionMember", arity := 4 },
    { head := "MDefinitionReduces", arity := 3 },
    { head := "MDefinitionReductionPath", arity := 3 },
    { head := "MDefinitionConverts", arity := 2 },
    { head := "MDefinitionPropositionRepresentative", arity := 6 },
    { head := "MDefinitionProves", arity := 5 } ]

private def additionalRules : List RuleSchema :=
  [ projectNilRule, projectParameterRule, projectDefinitionRule,
    polyTypePlainRule, polyTypeAllRule,
    declarationsValidNilRule, declarationsValidParameterRule,
    declarationsValidDefinitionRule,
    shiftTypeContextNilRule, shiftTypeContextConsRule,
    termTypeAppRule, termTypeLamRule,
    definitionHereRule, definitionThereParameterRule,
    definitionThereDefinitionRule,
    reduceDeltaRule, reduceBetaRule, reduceTypeBetaRule, reduceEtaRule,
    reduceAppFunctionRule, reduceAppArgumentRule, reduceLamBodyRule,
    reduceImpDomainRule, reduceImpCodomainRule, reduceAllBodyRule,
    reduceTypeAppFunctionRule, reduceTypeLamBodyRule,
    reduceTypeAllBodyRule, pathReflRule, pathStepRule,
    conversionCommonRule, fullProofRule,
    propositionPlainRule, propositionTypeAllRule,
    fullConvertRule, fullImpIntroRule, fullImpElimRule,
    fullAllIntroRule, fullAllElimRule,
    fullTypeElimRule, fullTypeIntroRule ]

def definition : CalculusLanguageDef :=
  { EnvironmentKernel.definition with
    name := "megalodon-definition-conversion-kernel-v1"
    terms := EnvironmentKernel.definition.terms ++
      additionalConstructors.map fun declaration =>
        TermQuantifiedKernel.expressionConstructor declaration.1 declaration.2
    judgments := EnvironmentKernel.definition.judgments ++
      additionalJudgments
    rules := EnvironmentKernel.definition.rules ++ additionalRules
    conversion := some
      { judgmentHead := "MDefinitionConverts"
        version := "megalodon-beta-delta-eta-v1" } }

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem definition_valid : definition.isValid = true := by
  have hvalidate : definition.toLanguageDef.validate = [] := by
    apply LanguageDef.validate_eq_nil_of_constructorOnly <;>
      simp [definition, definition, additionalConstructors,
        definitionParameterName, identityDefinitionName,
        EnvironmentKernel.definition, EnvironmentKernel.additionalConstructors,
        MathdataKernel.polymorphicReuseName,
        EnvironmentKernel.implicationReuseTermName,
        EnvironmentKernel.implicationReuseKnownName,
        PolymorphicKernel.definition, TermQuantifiedKernel.definition,
        TermQuantifiedKernel.constructors,
        TermQuantifiedKernel.expressionType,
        TermQuantifiedKernel.expressionConstructor,
        LanguageDef.typeNames, TypeDecl.plain, TermParam.typeExpr,
        TypeExpr.baseNames]
  unfold CalculusLanguageDef.isValid CalculusLanguageDef.hasValidLocalRules
  rw [hvalidate]
  simp (config := { maxSteps := 5000000, decide := true })
    [ definition, definition, additionalConstructors,
      definitionParameterName, identityDefinitionName,
      additionalJudgments, additionalRules,
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
      Pattern.mapHead, Pattern.evalHead,
      projectNilRule, projectParameterRule, projectDefinitionRule,
      polyTypePlainRule, polyTypeAllRule,
      declarationsValidNilRule, declarationsValidParameterRule,
      declarationsValidDefinitionRule,
      shiftTypeContextNilRule, shiftTypeContextConsRule,
      termTypeAppRule, termTypeLamRule,
      definitionHereRule, definitionThereParameterRule,
      definitionThereDefinitionRule,
      reduceDeltaRule, reduceBetaRule, reduceTypeBetaRule, reduceEtaRule,
      reduceAppFunctionRule, reduceAppArgumentRule, reduceLamBodyRule,
      reduceImpDomainRule, reduceImpCodomainRule, reduceAllBodyRule,
      reduceTypeAppFunctionRule, reduceTypeLamBodyRule,
      reduceTypeAllBodyRule, pathReflRule, pathStepRule,
      conversionCommonRule, fullProofRule,
      propositionPlainRule, propositionTypeAllRule,
      fullConvertRule, fullImpIntroRule, fullImpElimRule,
      fullAllIntroRule, fullAllElimRule,
      fullTypeElimRule, fullTypeIntroRule,
      rule, ruleId, projectSignature, polyType, declarationsValid,
      shiftTypeContext,
      definitionMember, substituteTerm,
      substituteTypeInTerm, shiftTerm, reduces, reductionPath, converts,
      scopedTerm, propositionRepresentative,
      baseProves, fullProves, a, m,
      EnvironmentKernel.definition, EnvironmentKernel.additionalConstructors,
      EnvironmentKernel.additionalJudgments, EnvironmentKernel.additionalRules,
      MathdataKernel.polymorphicReuseName,
      EnvironmentKernel.implicationReuseTermName,
      EnvironmentKernel.implicationReuseKnownName,
      PolymorphicKernel.definition, PolymorphicKernel.additionalJudgments,
      PolymorphicKernel.additionalRules, PolymorphicKernel.rule,
      PolymorphicKernel.ruleId, PolymorphicKernel.plainVarRule,
      PolymorphicKernel.plainPropRule, PolymorphicKernel.plainBaseRule,
      PolymorphicKernel.plainArrRule, PolymorphicKernel.typeVarZeroRule,
      PolymorphicKernel.typeVarSuccRule, PolymorphicKernel.typeNamedZeroRule,
      PolymorphicKernel.typeNamedSuccRule, PolymorphicKernel.typeAppRule,
      PolymorphicKernel.typeLamRule, PolymorphicKernel.typeImpRule,
      PolymorphicKernel.typeAllRule, PolymorphicKernel.proofHypZeroRule,
      PolymorphicKernel.proofHypSuccRule,
      PolymorphicKernel.proofImpIntroRule,
      PolymorphicKernel.proofImpElimRule,
      PolymorphicKernel.proofAllIntroRule,
      PolymorphicKernel.proofAllElimRule,
      PolymorphicKernel.proofTypeIntroRule,
      PolymorphicKernel.plainType, PolymorphicKernel.hasType,
      PolymorphicKernel.proves, PolymorphicKernel.lessThan,
      PolymorphicKernel.shiftProofContext,
      PolymorphicKernel.substituteTerm, PolymorphicKernel.a,
      PolymorphicKernel.m,
      TermQuantifiedKernel.definition, TermQuantifiedKernel.constructors,
      TermQuantifiedKernel.rules, TermQuantifiedKernel.expressionType,
      TermQuantifiedKernel.expressionConstructor,
      TermQuantifiedKernel.rule, TermQuantifiedKernel.ruleId,
      TermQuantifiedKernel.addZeroRule, TermQuantifiedKernel.addSuccRule,
      TermQuantifiedKernel.lessZeroRule, TermQuantifiedKernel.lessSuccRule,
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
      TermQuantifiedKernel.m, List.eraseDups, List.eraseDupsBy]

def validated : ValidatedCalculusLanguageDef := ⟨definition, definition_valid⟩

@[simp] private theorem lookup_projectNilRule :
    definition.lookupRule? (ruleId "megalodon-def-project-nil") =
      some projectNilRule := by
  rfl

@[simp] private theorem lookup_projectParameterRule :
    definition.lookupRule? (ruleId "megalodon-def-project-parameter") =
      some projectParameterRule := by
  rfl

@[simp] private theorem lookup_projectDefinitionRule :
    definition.lookupRule? (ruleId "megalodon-def-project-definition") =
      some projectDefinitionRule := by
  rfl

@[simp] private theorem lookup_definitionHereRule :
    definition.lookupRule? (ruleId "megalodon-def-member-here") =
      some definitionHereRule := by
  rfl

@[simp] private theorem lookup_reduceDeltaRule :
    definition.lookupRule? (ruleId "megalodon-def-reduce-delta") =
      some reduceDeltaRule := by
  rfl

@[simp] private theorem lookup_reduceBetaRule :
    definition.lookupRule? (ruleId "megalodon-def-reduce-beta") =
      some reduceBetaRule := by
  rfl

@[simp] private theorem lookup_reduceEtaRule :
    definition.lookupRule? (ruleId "megalodon-def-reduce-eta") =
      some reduceEtaRule := by
  rfl

@[simp] private theorem lookup_reduceAppFunctionRule :
    definition.lookupRule? (ruleId "megalodon-def-reduce-app-function") =
      some reduceAppFunctionRule := by
  rfl

@[simp] private theorem lookup_reduceImpDomainRule :
    definition.lookupRule? (ruleId "megalodon-def-reduce-imp-domain") =
      some reduceImpDomainRule := by
  rfl

@[simp] private theorem lookup_reduceImpCodomainRule :
    definition.lookupRule? (ruleId "megalodon-def-reduce-imp-codomain") =
      some reduceImpCodomainRule := by
  rfl

@[simp] private theorem lookup_pathReflRule :
    definition.lookupRule? (ruleId "megalodon-def-path-refl") =
      some pathReflRule := by
  rfl

@[simp] private theorem lookup_pathStepRule :
    definition.lookupRule? (ruleId "megalodon-def-path-step") =
      some pathStepRule := by
  rfl

@[simp] private theorem lookup_conversionCommonRule :
    definition.lookupRule? (ruleId "megalodon-def-conversion-common") =
      some conversionCommonRule := by
  rfl

@[simp] private theorem lookup_fullProofRule :
    definition.lookupRule? (ruleId "megalodon-def-proof") =
      some fullProofRule := by
  rfl

@[simp] private theorem lookup_environmentProofBaseRule :
    definition.lookupRule? (ruleId "megalodon-env-proof-base") =
      some EnvironmentKernel.proofBaseRule := by
  rfl

@[simp] private theorem lookup_typeNamedZeroRule :
    definition.lookupRule? (ruleId "megalodon-poly-term-named-zero") =
      some PolymorphicKernel.typeNamedZeroRule := by
  rfl

@[simp] private theorem lookup_typeNamedSuccRule :
    definition.lookupRule? (ruleId "megalodon-poly-term-named-succ") =
      some PolymorphicKernel.typeNamedSuccRule := by
  rfl

@[simp] private theorem lookup_typeAppRule :
    definition.lookupRule? (ruleId "megalodon-poly-term-app") =
      some PolymorphicKernel.typeAppRule := by
  rfl

@[simp] private theorem lookup_proofHypZeroRule :
    definition.lookupRule? (ruleId "megalodon-poly-proof-hyp-zero") =
      some PolymorphicKernel.proofHypZeroRule := by
  rfl

@[simp] private theorem lookup_proofImpIntroRule :
    definition.lookupRule? (ruleId "megalodon-poly-proof-imp-intro") =
      some PolymorphicKernel.proofImpIntroRule := by
  rfl

@[simp] private theorem lookup_shiftNamedRule :
    definition.lookupRule? (ruleId "megalodon-term-shift-named") =
      some TermQuantifiedKernel.shiftNamedRule := by
  rfl

@[simp] private theorem lookup_substVarEqualRule :
    definition.lookupRule? (ruleId "megalodon-term-subst-var-equal") =
      some TermQuantifiedKernel.substVarEqualRule := by
  rfl

def coGSLTDefinition : ExtendedLanguageDef calculusLayer :=
  definition.toExtended

def coGSLTSource : coGSLTDefinition.authoredGSLT.Term :=
  coGSLTDefinition.authoredSource

@[simp] theorem coGSLT_source_elaborates :
    calculusLayer.elaborate definition.toLanguageDef coGSLTSource =
      some definition.toCalculus :=
  definition.toExtended_elaborate_authoredSource

theorem environment_ruleLookupRefines :
    RuleLookupRefines EnvironmentKernel.validated validated := by
  apply RuleLookupRefines.of_rules_eq_append additionalRules
  rfl

/-! ## Exact source carriers and the real definition canary -/

def encodeTermDeclarations : List MathdataKernel.TermDecl → Pattern
  | [] => a "MDeclNil"
  | declaration :: declarations =>
      match declaration.definition with
      | none =>
          a "MDeclParameter"
            [a declaration.name, TermQuantifiedKernel.encodeTp declaration.type,
              encodeTermDeclarations declarations]
      | some body =>
          a "MDeclDefinition"
            [a declaration.name, TermQuantifiedKernel.encodeTp declaration.type,
              TermQuantifiedKernel.encodeTm body,
              encodeTermDeclarations declarations]

@[simp] theorem encodeTermDeclarations_ground
    (declarations : List MathdataKernel.TermDecl) :
    (encodeTermDeclarations declarations).isGroundAt 0 = true := by
  induction declarations with
  | nil =>
      simp [encodeTermDeclarations, a, Pattern.isGroundAt,
        Pattern.isGroundListAt]
  | cons declaration declarations inductionHypothesis =>
      cases declaration with
      | mk name type definition =>
          cases definition <;>
            simp [encodeTermDeclarations, a, Pattern.isGroundAt,
              Pattern.isGroundListAt, inductionHypothesis]

@[simp] theorem encodeTermDeclarations_canonical
    (declarations : List MathdataKernel.TermDecl) :
    (encodeTermDeclarations declarations).hasCanonicalBinderMetadata = true := by
  induction declarations with
  | nil =>
      simp [encodeTermDeclarations, a,
        Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList]
  | cons declaration declarations inductionHypothesis =>
      cases declaration with
      | mk name type definition =>
          cases definition <;>
            simp [encodeTermDeclarations, a,
              Pattern.hasCanonicalBinderMetadata,
              Pattern.hasCanonicalBinderMetadataList, inductionHypothesis]

@[simp] theorem encodeSignature_ground
    (declarations : List MathdataKernel.TermDecl) :
    (TermQuantifiedKernel.encodeSignature declarations).isGroundAt 0 = true := by
  induction declarations with
  | nil =>
      simp [TermQuantifiedKernel.encodeSignature, TermQuantifiedKernel.a,
        Pattern.isGroundAt, Pattern.isGroundListAt]
  | cons declaration declarations inductionHypothesis =>
      cases declaration
      simp [TermQuantifiedKernel.encodeSignature, TermQuantifiedKernel.a,
        Pattern.isGroundAt, Pattern.isGroundListAt, inductionHypothesis]

@[simp] theorem encodeSignature_canonical
    (declarations : List MathdataKernel.TermDecl) :
    (TermQuantifiedKernel.encodeSignature declarations).hasCanonicalBinderMetadata =
      true := by
  induction declarations with
  | nil =>
      simp [TermQuantifiedKernel.encodeSignature, TermQuantifiedKernel.a,
        Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList]
  | cons declaration declarations inductionHypothesis =>
      cases declaration
      simp [TermQuantifiedKernel.encodeSignature, TermQuantifiedKernel.a,
        Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList, inductionHypothesis]

def encodeFullEnvironment (environment : MathdataKernel.Environment) : Pattern :=
  a "MFullEnvironment"
    [ EnvironmentKernel.encodePrimitiveTypes environment.primitives,
      encodeTermDeclarations environment.terms,
      EnvironmentKernel.encodeKnown environment.known ]

private def node (id : String) (arguments : List Pattern)
    (children : List RawProof := []) : RawProof :=
  .node { ruleId := ruleId id, arguments } children

private abbrev ENat := TermQuantifiedKernel.encodeNat
private abbrev ETp := TermQuantifiedKernel.encodeTp
private abbrev ETm := TermQuantifiedKernel.encodeTm
private abbrev ETyCtx := TermQuantifiedKernel.encodeTypeContext
private abbrev EPfCtx := TermQuantifiedKernel.encodeProofContext
private abbrev ESig := TermQuantifiedKernel.encodeSignature

def compileProjection : List MathdataKernel.TermDecl → RawProof
  | [] => node "megalodon-def-project-nil" []
  | declaration :: declarations =>
      match declaration.definition with
      | none =>
          node "megalodon-def-project-parameter"
            [a declaration.name, ETp declaration.type,
              encodeTermDeclarations declarations, ESig declarations]
            [compileProjection declarations]
      | some body =>
          node "megalodon-def-project-definition"
            [a declaration.name, ETp declaration.type, ETm body,
              encodeTermDeclarations declarations, ESig declarations]
            [compileProjection declarations]

@[simp] theorem compileProjection_nil :
    compileProjection [] =
      .node
        { ruleId := ⟨"megalodon-def-project-nil"⟩
          arguments := [] }
        [] := by
  rfl

@[simp] theorem compileProjection_parameter
    (declaration : MathdataKernel.TermDecl)
    (declarations : List MathdataKernel.TermDecl)
    (parameter : declaration.definition = none) :
    compileProjection (declaration :: declarations) =
      .node
        { ruleId := ⟨"megalodon-def-project-parameter"⟩
          arguments :=
            [ .apply declaration.name [],
              TermQuantifiedKernel.encodeTp declaration.type,
              encodeTermDeclarations declarations,
              TermQuantifiedKernel.encodeSignature declarations ] }
        [compileProjection declarations] := by
  simp [compileProjection, parameter, node, a, ruleId]

@[simp] theorem compileProjection_definition
    (declaration : MathdataKernel.TermDecl)
    (declarations : List MathdataKernel.TermDecl)
    (body : MathdataKernel.Tm)
    (defined : declaration.definition = some body) :
    compileProjection (declaration :: declarations) =
      .node
        { ruleId := ⟨"megalodon-def-project-definition"⟩
          arguments :=
            [ .apply declaration.name [],
              TermQuantifiedKernel.encodeTp declaration.type,
              TermQuantifiedKernel.encodeTm body,
              encodeTermDeclarations declarations,
              TermQuantifiedKernel.encodeSignature declarations ] }
        [compileProjection declarations] := by
  simp [compileProjection, defined, node, a, ruleId]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem compileProjection_checked (declarations : List MathdataKernel.TermDecl) :
    checkRaw validated
      (projectSignature (encodeTermDeclarations declarations)
        (ESig declarations))
      (compileProjection declarations) = true := by
  induction declarations with
  | nil =>
      simp only [compileProjection, node, checkRaw, validated,
        instantiateRule?]
      rw [lookup_projectNilRule]
      simp [argumentsValidAt, instantiateSchemas?,
        instantiateSchema?, instantiateSchemasAt?, instantiateSchemaAt?,
        RuleSchema.sideConditionsHold, projectNilRule,
        rule, ruleId, projectSignature, encodeTermDeclarations,
        TermQuantifiedKernel.encodeSignature, TermQuantifiedKernel.a,
        checkRawChildren, a]
  | cons declaration declarations inductionHypothesis =>
      cases definitionCase : declaration.definition with
      | none =>
          simp only [compileProjection, definitionCase, node, checkRaw,
            validated, instantiateRule?]
          rw [lookup_projectParameterRule]
          simp [argumentsValidAt, argumentValidAt, instantiateSchemas?,
            instantiateSchema?, instantiateSchemasAt?, instantiateSchemaAt?,
            lookupArgumentAt?, RuleSchema.sideConditionsHold,
            projectParameterRule, rule, ruleId, projectSignature,
            encodeTermDeclarations, definitionCase,
            TermQuantifiedKernel.encodeSignature, TermQuantifiedKernel.a,
            checkRawChildren, Pattern.isGroundAt, Pattern.isGroundListAt,
            Pattern.hasCanonicalBinderMetadata,
            Pattern.hasCanonicalBinderMetadataList,
            a, m]
          simpa [validated, projectSignature, a] using inductionHypothesis
      | some body =>
          simp only [compileProjection, definitionCase, node, checkRaw,
            validated, instantiateRule?]
          rw [lookup_projectDefinitionRule]
          simp [argumentsValidAt, argumentValidAt, instantiateSchemas?,
            instantiateSchema?, instantiateSchemasAt?, instantiateSchemaAt?,
            lookupArgumentAt?, RuleSchema.sideConditionsHold,
            projectDefinitionRule, rule, ruleId, projectSignature,
            encodeTermDeclarations, definitionCase,
            TermQuantifiedKernel.encodeSignature, TermQuantifiedKernel.a,
            checkRawChildren, Pattern.isGroundAt, Pattern.isGroundListAt,
            Pattern.hasCanonicalBinderMetadata,
            Pattern.hasCanonicalBinderMetadataList,
            a, m]
          simpa [validated, projectSignature, a] using inductionHypothesis

def parameterDeclaration : MathdataKernel.TermDecl :=
  { name := definitionParameterName, type := .prop }

def identityDeclaration : MathdataKernel.TermDecl :=
  { name := identityDefinitionName
    type := .arr .prop .prop
    definition := some (.lam .prop (.db 0)) }

def definitionEnvironment : MathdataKernel.Environment :=
  { terms := [identityDeclaration, parameterDeclaration] }

def definitionDomain : MathdataKernel.Tm :=
  .app (.named identityDefinitionName) (.named definitionParameterName)

def definitionGoal : MathdataKernel.Tm :=
  .imp definitionDomain (.named definitionParameterName)

def synthesizedIdentityGoal : MathdataKernel.Tm :=
  .imp definitionDomain definitionDomain

def normalizedIdentityGoal : MathdataKernel.Tm :=
  .imp (.named definitionParameterName) (.named definitionParameterName)

def identityProof : MathdataKernel.Pf :=
  .proofLam definitionDomain (.hyp 0)

theorem mathdata_accepts_definition_identity :
    MathdataKernel.checkProof definitionEnvironment 32 0 [] []
      identityProof definitionGoal = true := by
  simp [MathdataKernel.checkProof, MathdataKernel.checkNormalizedProof,
    MathdataKernel.inferProof, definitionEnvironment, identityProof,
    definitionGoal, definitionDomain, identityDeclaration,
    parameterDeclaration, definitionParameterName, identityDefinitionName,
    MathdataKernel.checkProposition, MathdataKernel.inferTerm,
    MathdataKernel.normalize, MathdataKernel.deltaNormalize,
    MathdataKernel.Tm.normalize, MathdataKernel.Tm.normalizeOne,
    MathdataKernel.Environment.lookupTerm?, MathdataKernel.lookupTermList?,
    MathdataKernel.Tm.instantiate, MathdataKernel.Tm.instantiateAt,
    MathdataKernel.Tm.shift]

private def identityTypeArticle : RawProof :=
  node "megalodon-poly-term-named-zero"
    [a identityDefinitionName, ETp (.arr .prop .prop),
      ESig [parameterDeclaration], ENat 0, ETyCtx []]

private def parameterTailTypeArticle : RawProof :=
  node "megalodon-poly-term-named-zero"
    [a definitionParameterName, ETp .prop, ESig [], ENat 0, ETyCtx []]

private def parameterTypeArticle : RawProof :=
  node "megalodon-poly-term-named-succ"
    [ a identityDefinitionName, ETp (.arr .prop .prop),
      ESig [parameterDeclaration], ENat 0, ETyCtx [],
      a definitionParameterName, ETp .prop ]
    [parameterTailTypeArticle]

private def domainTypeArticle : RawProof :=
  node "megalodon-poly-term-app"
    [ ESig [identityDeclaration, parameterDeclaration], ENat 0, ETyCtx [],
      ETm (.named identityDefinitionName),
      ETm (.named definitionParameterName), ETp .prop, ETp .prop ]
    [identityTypeArticle, parameterTypeArticle]

private def baseHypArticle : RawProof :=
  node "megalodon-poly-proof-hyp-zero"
    [ ESig [identityDeclaration, parameterDeclaration], ENat 0, ETyCtx [],
      EPfCtx [], ETm definitionDomain ]
    [domainTypeArticle]

private def baseIdentityArticle : RawProof :=
  node "megalodon-poly-proof-imp-intro"
    [ ESig [identityDeclaration, parameterDeclaration], ENat 0, ETyCtx [],
      EPfCtx [], ETm definitionDomain, ETm definitionDomain ]
    [domainTypeArticle, baseHypArticle]

private theorem base_identity_article_accepted :
    checkRaw validated
      (PolymorphicKernel.proves
        (ESig [identityDeclaration, parameterDeclaration]) (ENat 0)
        (ETyCtx []) (EPfCtx []) (ETm synthesizedIdentityGoal))
      baseIdentityArticle = true := by
  simp (config := { maxSteps := 1000000, decide := true })
    [ baseIdentityArticle, baseHypArticle, domainTypeArticle,
      parameterTypeArticle, parameterTailTypeArticle, identityTypeArticle,
      node, checkRaw, checkRawChildren, validated, instantiateRule?,
      instantiateSchemas?,
      instantiateSchema?, instantiateSchemasAt?, instantiateSchemaAt?,
      lookupArgumentAt?,
      PolymorphicKernel.proofImpIntroRule,
      PolymorphicKernel.proofHypZeroRule, PolymorphicKernel.typeAppRule,
      PolymorphicKernel.typeNamedZeroRule,
      PolymorphicKernel.typeNamedSuccRule, PolymorphicKernel.rule,
      PolymorphicKernel.ruleId, PolymorphicKernel.hasType,
      PolymorphicKernel.proves, PolymorphicKernel.a, PolymorphicKernel.m,
      TermQuantifiedKernel.encodeSignature,
      TermQuantifiedKernel.encodeTypeContext,
      TermQuantifiedKernel.encodeProofContext,
      TermQuantifiedKernel.encodeNat, TermQuantifiedKernel.encodeTp,
      TermQuantifiedKernel.encodeTm, TermQuantifiedKernel.a,
      identityDeclaration, parameterDeclaration, synthesizedIdentityGoal,
      definitionDomain, definitionParameterName, identityDefinitionName, a]

private def environmentIdentityArticle : RawProof :=
  node "megalodon-env-proof-base"
    [ EnvironmentKernel.encodePrimitiveTypes [],
      ESig [identityDeclaration, parameterDeclaration],
      EnvironmentKernel.encodeKnown [], ENat 0, ETyCtx [], EPfCtx [],
      ETm synthesizedIdentityGoal ]
    [baseIdentityArticle]

private theorem environment_identity_article_accepted :
    checkRaw validated
      (baseProves
        (a "MEnvironment"
          [EnvironmentKernel.encodePrimitiveTypes [],
            ESig [identityDeclaration, parameterDeclaration],
            EnvironmentKernel.encodeKnown []])
        (ENat 0) (ETyCtx []) (EPfCtx []) (ETm synthesizedIdentityGoal))
      environmentIdentityArticle = true := by
  simp only [environmentIdentityArticle, node, checkRaw, validated,
    instantiateRule?]
  rw [lookup_environmentProofBaseRule]
  simp [argumentsValidAt, argumentValidAt, instantiateSchemas?,
    instantiateSchema?, instantiateSchemasAt?, instantiateSchemaAt?,
    lookupArgumentAt?, EnvironmentKernel.proofBaseRule,
    EnvironmentKernel.rule, EnvironmentKernel.ruleId,
    EnvironmentKernel.baseProves, EnvironmentKernel.proves,
    EnvironmentKernel.a, EnvironmentKernel.m, baseProves, a,
    EnvironmentKernel.encodePrimitiveTypes, EnvironmentKernel.encodeKnown,
    TermQuantifiedKernel.encodeTypeContext,
    TermQuantifiedKernel.encodeProofContext,
    TermQuantifiedKernel.a, checkRawChildren,
    Pattern.isGroundAt, Pattern.isGroundListAt,
    Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList]
  simpa [validated, PolymorphicKernel.proves, PolymorphicKernel.a,
    TermQuantifiedKernel.encodeTypeContext,
    TermQuantifiedKernel.encodeProofContext, TermQuantifiedKernel.a] using
    base_identity_article_accepted

private def definitionHereArticle : RawProof :=
  node "megalodon-def-member-here"
    [ a identityDefinitionName, ETp (.arr .prop .prop),
      ETm (.lam .prop (.db 0)),
      encodeTermDeclarations [parameterDeclaration] ]

private theorem definition_here_article_accepted :
    checkRaw validated
      (definitionMember
        (encodeTermDeclarations [identityDeclaration, parameterDeclaration])
        (a identityDefinitionName) (ETp (.arr .prop .prop))
        (ETm (.lam .prop (.db 0))))
      definitionHereArticle = true := by
  simp only [definitionHereArticle, node, checkRaw, validated,
    instantiateRule?]
  rw [lookup_definitionHereRule]
  simp [argumentsValidAt, argumentValidAt, instantiateSchemas?,
    instantiateSchema?, instantiateSchemasAt?, instantiateSchemaAt?,
    lookupArgumentAt?, definitionHereRule, rule, ruleId,
    definitionMember, encodeTermDeclarations, identityDeclaration,
    parameterDeclaration, identityDefinitionName,
    TermQuantifiedKernel.encodeTp, TermQuantifiedKernel.encodeTm,
    TermQuantifiedKernel.a, checkRawChildren,
    Pattern.isGroundAt, Pattern.isGroundListAt,
    Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList, a, m]

private def deltaIdentityArticle : RawProof :=
  node "megalodon-def-reduce-delta"
    [ encodeTermDeclarations [identityDeclaration, parameterDeclaration],
      a identityDefinitionName, ETp (.arr .prop .prop),
      ETm (.lam .prop (.db 0)) ]
    [definitionHereArticle]

private theorem delta_identity_article_accepted :
    checkRaw validated
      (reduces
        (encodeTermDeclarations [identityDeclaration, parameterDeclaration])
        (ETm (.named identityDefinitionName))
        (ETm (.lam .prop (.db 0))))
      deltaIdentityArticle = true := by
  simp only [deltaIdentityArticle, node, checkRaw, validated,
    instantiateRule?]
  rw [lookup_reduceDeltaRule]
  simp [argumentsValidAt, argumentValidAt, instantiateSchemas?,
    instantiateSchema?, instantiateSchemasAt?, instantiateSchemaAt?,
    lookupArgumentAt?, reduceDeltaRule, rule, ruleId, reduces,
    definitionMember, encodeTermDeclarations, identityDeclaration,
    parameterDeclaration, identityDefinitionName,
    TermQuantifiedKernel.encodeTp, TermQuantifiedKernel.encodeTm,
    TermQuantifiedKernel.a, checkRawChildren,
    Pattern.isGroundAt, Pattern.isGroundListAt,
    Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList, a, m]
  simpa [validated, definitionMember, encodeTermDeclarations,
    identityDeclaration, parameterDeclaration, identityDefinitionName,
    definitionParameterName, TermQuantifiedKernel.encodeNat,
    TermQuantifiedKernel.encodeTp, TermQuantifiedKernel.encodeTm,
    TermQuantifiedKernel.a, a] using
    definition_here_article_accepted

private def reduceDefinitionDomainDeltaArticle : RawProof :=
  node "megalodon-def-reduce-app-function"
    [ encodeTermDeclarations [identityDeclaration, parameterDeclaration],
      ETm (.named identityDefinitionName),
      ETm (.lam .prop (.db 0)),
      ETm (.named definitionParameterName) ]
    [deltaIdentityArticle]

private theorem reduce_definition_domain_delta_article_accepted :
    checkRaw validated
      (reduces
        (encodeTermDeclarations [identityDeclaration, parameterDeclaration])
        (ETm definitionDomain)
        (ETm (.app (.lam .prop (.db 0))
          (.named definitionParameterName))))
      reduceDefinitionDomainDeltaArticle = true := by
  simp only [reduceDefinitionDomainDeltaArticle, node, checkRaw, validated,
    instantiateRule?]
  rw [lookup_reduceAppFunctionRule]
  simp [argumentsValidAt, argumentValidAt, instantiateSchemas?,
    instantiateSchema?, instantiateSchemasAt?, instantiateSchemaAt?,
    lookupArgumentAt?, reduceAppFunctionRule, rule, ruleId, reduces,
    encodeTermDeclarations, identityDeclaration, parameterDeclaration,
    definitionDomain, definitionParameterName, identityDefinitionName,
    TermQuantifiedKernel.encodeTm, TermQuantifiedKernel.a,
    checkRawChildren,
    Pattern.isGroundAt, Pattern.isGroundListAt,
    Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList, a, m]
  simpa [validated, reduces, encodeTermDeclarations, identityDeclaration,
    parameterDeclaration, identityDefinitionName, definitionParameterName,
    TermQuantifiedKernel.encodeNat, TermQuantifiedKernel.encodeTp,
    TermQuantifiedKernel.encodeTm, TermQuantifiedKernel.a, a] using
    delta_identity_article_accepted

private def betaShiftArticle : RawProof :=
  node "megalodon-term-shift-named"
    [ENat 0, ENat 0, a definitionParameterName]

private theorem beta_shift_article_accepted :
    checkRaw validated
      (TermQuantifiedKernel.shiftTerm (ENat 0) (ENat 0)
        (ETm (.named definitionParameterName))
        (ETm (.named definitionParameterName)))
      betaShiftArticle = true := by
  simp only [betaShiftArticle, node, checkRaw, validated, instantiateRule?]
  rw [lookup_shiftNamedRule]
  simp [argumentsValidAt, argumentValidAt, instantiateSchemas?,
    instantiateSchema?, instantiateSchemasAt?, instantiateSchemaAt?,
    lookupArgumentAt?, RuleSchema.sideConditionsHold,
    TermQuantifiedKernel.shiftNamedRule, TermQuantifiedKernel.rule,
    TermQuantifiedKernel.ruleId, TermQuantifiedKernel.shiftTerm,
    TermQuantifiedKernel.encodeNat, TermQuantifiedKernel.encodeTm,
    TermQuantifiedKernel.a, TermQuantifiedKernel.m,
    definitionParameterName, Pattern.isGroundAt, Pattern.isGroundListAt,
    Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList, checkRawChildren, a]

private def betaSubstitutionArticle : RawProof :=
  node "megalodon-term-subst-var-equal"
    [ ENat 0, ETm (.named definitionParameterName),
      ETm (.named definitionParameterName) ]
    [betaShiftArticle]

theorem beta_substitution_article_accepted :
    checkRaw validated
      (substituteTerm (ENat 0) (ETm (.named definitionParameterName))
      (ETm (.db 0)) (ETm (.named definitionParameterName)))
      betaSubstitutionArticle = true := by
  simp only [betaSubstitutionArticle, node, checkRaw, validated,
    instantiateRule?]
  rw [lookup_substVarEqualRule]
  simp [argumentsValidAt, argumentValidAt, instantiateSchemas?,
    instantiateSchema?, instantiateSchemasAt?, instantiateSchemaAt?,
    lookupArgumentAt?, RuleSchema.sideConditionsHold,
    TermQuantifiedKernel.substVarEqualRule, TermQuantifiedKernel.rule,
    TermQuantifiedKernel.ruleId, TermQuantifiedKernel.substituteTerm,
    TermQuantifiedKernel.shiftTerm, substituteTerm,
    TermQuantifiedKernel.encodeNat, TermQuantifiedKernel.encodeTm,
    TermQuantifiedKernel.a, TermQuantifiedKernel.m,
    definitionParameterName, Pattern.isGroundAt, Pattern.isGroundListAt,
    Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList, checkRawChildren, a]
  simpa [validated, TermQuantifiedKernel.shiftTerm,
    TermQuantifiedKernel.encodeNat, TermQuantifiedKernel.encodeTm,
    TermQuantifiedKernel.a, definitionParameterName, a] using
    beta_shift_article_accepted

private def reduceDefinitionDomainBetaArticle : RawProof :=
  node "megalodon-def-reduce-beta"
    [ encodeTermDeclarations [identityDeclaration, parameterDeclaration],
      ETp .prop, ETm (.db 0), ETm (.named definitionParameterName),
      ETm (.named definitionParameterName) ]
    [betaSubstitutionArticle]

private theorem reduce_definition_domain_beta_article_accepted :
    checkRaw validated
      (reduces
        (encodeTermDeclarations [identityDeclaration, parameterDeclaration])
        (ETm (.app (.lam .prop (.db 0))
          (.named definitionParameterName)))
        (ETm (.named definitionParameterName)))
      reduceDefinitionDomainBetaArticle = true := by
  simp only [reduceDefinitionDomainBetaArticle, node, checkRaw, validated,
    instantiateRule?]
  rw [lookup_reduceBetaRule]
  simp [argumentsValidAt, argumentValidAt, instantiateSchemas?,
    instantiateSchema?, instantiateSchemasAt?, instantiateSchemaAt?,
    lookupArgumentAt?, reduceBetaRule, rule, ruleId, reduces,
    substituteTerm, encodeTermDeclarations, identityDeclaration,
    parameterDeclaration, definitionParameterName,
    TermQuantifiedKernel.encodeNat, TermQuantifiedKernel.encodeTp,
    TermQuantifiedKernel.encodeTm, TermQuantifiedKernel.a,
    checkRawChildren,
    Pattern.isGroundAt, Pattern.isGroundListAt,
    Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList, a, m]
  simpa [validated, substituteTerm, TermQuantifiedKernel.encodeNat,
    TermQuantifiedKernel.encodeTm, TermQuantifiedKernel.a,
    definitionParameterName, a] using
    beta_substitution_article_accepted

private def pathReflArticle (term : MathdataKernel.Tm) : RawProof :=
  node "megalodon-def-path-refl"
    [encodeTermDeclarations [identityDeclaration, parameterDeclaration],
      ETm term]

private def pathStepArticle (source middle target : MathdataKernel.Tm)
    (step rest : RawProof) : RawProof :=
  node "megalodon-def-path-step"
    [ encodeTermDeclarations [identityDeclaration, parameterDeclaration],
      ETm source, ETm middle, ETm target ]
    [step, rest]

private theorem reduce_imp_domain_article_accepted
    (domain domainResult codomain : MathdataKernel.Tm) (child : RawProof)
    (childAccepted :
      checkRaw validated
        (reduces
          (encodeTermDeclarations [identityDeclaration, parameterDeclaration])
          (ETm domain) (ETm domainResult)) child = true) :
    checkRaw validated
      (reduces
        (encodeTermDeclarations [identityDeclaration, parameterDeclaration])
        (ETm (.imp domain codomain)) (ETm (.imp domainResult codomain)))
      (node "megalodon-def-reduce-imp-domain"
        [ encodeTermDeclarations [identityDeclaration, parameterDeclaration],
          ETm domain, ETm domainResult, ETm codomain ] [child]) = true := by
  simp only [node, checkRaw, validated, instantiateRule?]
  rw [lookup_reduceImpDomainRule]
  simp [argumentsValidAt, argumentValidAt, instantiateSchemas?,
    instantiateSchema?, instantiateSchemasAt?, instantiateSchemaAt?,
    lookupArgumentAt?, reduceImpDomainRule, rule, ruleId, reduces,
    checkRawChildren, a, m]
  exact ⟨⟨rfl, rfl⟩, childAccepted⟩

private theorem reduce_imp_codomain_article_accepted
    (domain codomain codomainResult : MathdataKernel.Tm) (child : RawProof)
    (childAccepted :
      checkRaw validated
        (reduces
          (encodeTermDeclarations [identityDeclaration, parameterDeclaration])
          (ETm codomain) (ETm codomainResult)) child = true) :
    checkRaw validated
      (reduces
        (encodeTermDeclarations [identityDeclaration, parameterDeclaration])
        (ETm (.imp domain codomain)) (ETm (.imp domain codomainResult)))
      (node "megalodon-def-reduce-imp-codomain"
        [ encodeTermDeclarations [identityDeclaration, parameterDeclaration],
          ETm domain, ETm codomain, ETm codomainResult ] [child]) = true := by
  simp only [node, checkRaw, validated, instantiateRule?]
  rw [lookup_reduceImpCodomainRule]
  simp [argumentsValidAt, argumentValidAt, instantiateSchemas?,
    instantiateSchema?, instantiateSchemasAt?, instantiateSchemaAt?,
    lookupArgumentAt?, reduceImpCodomainRule, rule, ruleId, reduces,
    checkRawChildren, a, m]
  exact ⟨⟨rfl, rfl⟩, childAccepted⟩

private theorem path_refl_article_accepted (term : MathdataKernel.Tm) :
    checkRaw validated
      (reductionPath
        (encodeTermDeclarations [identityDeclaration, parameterDeclaration])
        (ETm term) (ETm term))
      (pathReflArticle term) = true := by
  simp only [pathReflArticle, node, checkRaw, validated, instantiateRule?]
  rw [lookup_pathReflRule]
  simp [argumentsValidAt, argumentValidAt, instantiateSchemas?,
    instantiateSchema?, instantiateSchemasAt?, instantiateSchemaAt?,
    lookupArgumentAt?, pathReflRule, rule, ruleId, reductionPath,
    checkRawChildren, a, m]

private theorem path_step_article_accepted
    (source middle target : MathdataKernel.Tm) (step rest : RawProof)
    (stepAccepted :
      checkRaw validated
        (reduces
          (encodeTermDeclarations [identityDeclaration, parameterDeclaration])
          (ETm source) (ETm middle)) step = true)
    (restAccepted :
      checkRaw validated
        (reductionPath
          (encodeTermDeclarations [identityDeclaration, parameterDeclaration])
          (ETm middle) (ETm target)) rest = true) :
    checkRaw validated
      (reductionPath
        (encodeTermDeclarations [identityDeclaration, parameterDeclaration])
        (ETm source) (ETm target))
      (pathStepArticle source middle target step rest) = true := by
  simp only [pathStepArticle, node, checkRaw, validated, instantiateRule?]
  rw [lookup_pathStepRule]
  simp [argumentsValidAt, argumentValidAt, instantiateSchemas?,
    instantiateSchema?, instantiateSchemasAt?, instantiateSchemaAt?,
    lookupArgumentAt?, pathStepRule, rule, ruleId, reductionPath, reduces,
    checkRawChildren, a, m]
  exact ⟨stepAccepted, restAccepted⟩

private def synthesizedPathArticle : RawProof :=
  let leftDelta :=
    node "megalodon-def-reduce-imp-domain"
      [ encodeTermDeclarations [identityDeclaration, parameterDeclaration],
        ETm definitionDomain,
        ETm (.app (.lam .prop (.db 0)) (.named definitionParameterName)),
        ETm definitionDomain ]
      [reduceDefinitionDomainDeltaArticle]
  let afterLeftDelta :=
    .imp (.app (.lam .prop (.db 0)) (.named definitionParameterName))
      definitionDomain
  let leftBeta :=
    node "megalodon-def-reduce-imp-domain"
      [ encodeTermDeclarations [identityDeclaration, parameterDeclaration],
        ETm (.app (.lam .prop (.db 0)) (.named definitionParameterName)),
        ETm (.named definitionParameterName), ETm definitionDomain ]
      [reduceDefinitionDomainBetaArticle]
  let afterLeftBeta :=
    .imp (.named definitionParameterName) definitionDomain
  let rightDelta :=
    node "megalodon-def-reduce-imp-codomain"
      [ encodeTermDeclarations [identityDeclaration, parameterDeclaration],
        ETm (.named definitionParameterName), ETm definitionDomain,
        ETm (.app (.lam .prop (.db 0)) (.named definitionParameterName)) ]
      [reduceDefinitionDomainDeltaArticle]
  let afterRightDelta :=
    .imp (.named definitionParameterName)
      (.app (.lam .prop (.db 0)) (.named definitionParameterName))
  let rightBeta :=
    node "megalodon-def-reduce-imp-codomain"
      [ encodeTermDeclarations [identityDeclaration, parameterDeclaration],
        ETm (.named definitionParameterName),
        ETm (.app (.lam .prop (.db 0)) (.named definitionParameterName)),
        ETm (.named definitionParameterName) ]
      [reduceDefinitionDomainBetaArticle]
  pathStepArticle synthesizedIdentityGoal afterLeftDelta
    normalizedIdentityGoal leftDelta
    (pathStepArticle afterLeftDelta afterLeftBeta normalizedIdentityGoal
      leftBeta
      (pathStepArticle afterLeftBeta afterRightDelta normalizedIdentityGoal
        rightDelta
        (pathStepArticle afterRightDelta normalizedIdentityGoal
          normalizedIdentityGoal rightBeta
          (pathReflArticle normalizedIdentityGoal))))

private def declaredPathArticle : RawProof :=
  let leftDelta :=
    node "megalodon-def-reduce-imp-domain"
      [ encodeTermDeclarations [identityDeclaration, parameterDeclaration],
        ETm definitionDomain,
        ETm (.app (.lam .prop (.db 0)) (.named definitionParameterName)),
        ETm (.named definitionParameterName) ]
      [reduceDefinitionDomainDeltaArticle]
  let afterDelta :=
    .imp (.app (.lam .prop (.db 0)) (.named definitionParameterName))
      (.named definitionParameterName)
  let leftBeta :=
    node "megalodon-def-reduce-imp-domain"
      [ encodeTermDeclarations [identityDeclaration, parameterDeclaration],
        ETm (.app (.lam .prop (.db 0)) (.named definitionParameterName)),
        ETm (.named definitionParameterName),
        ETm (.named definitionParameterName) ]
      [reduceDefinitionDomainBetaArticle]
  pathStepArticle definitionGoal afterDelta normalizedIdentityGoal leftDelta
    (pathStepArticle afterDelta normalizedIdentityGoal normalizedIdentityGoal
      leftBeta (pathReflArticle normalizedIdentityGoal))

private theorem synthesized_path_article_accepted :
    checkRaw validated
      (reductionPath
        (encodeTermDeclarations [identityDeclaration, parameterDeclaration])
        (ETm synthesizedIdentityGoal) (ETm normalizedIdentityGoal))
      synthesizedPathArticle = true := by
  simp only [synthesizedPathArticle]
  apply path_step_article_accepted
  · exact reduce_imp_domain_article_accepted _ _ _ _
      reduce_definition_domain_delta_article_accepted
  · apply path_step_article_accepted
    · exact reduce_imp_domain_article_accepted _ _ _ _
        reduce_definition_domain_beta_article_accepted
    · apply path_step_article_accepted
      · exact reduce_imp_codomain_article_accepted _ _ _ _
          reduce_definition_domain_delta_article_accepted
      · apply path_step_article_accepted
        · exact reduce_imp_codomain_article_accepted _ _ _ _
            reduce_definition_domain_beta_article_accepted
        · exact path_refl_article_accepted _

private theorem declared_path_article_accepted :
    checkRaw validated
      (reductionPath
        (encodeTermDeclarations [identityDeclaration, parameterDeclaration])
        (ETm definitionGoal) (ETm normalizedIdentityGoal))
      declaredPathArticle = true := by
  simp only [declaredPathArticle]
  apply path_step_article_accepted
  · exact reduce_imp_domain_article_accepted _ _ _ _
      reduce_definition_domain_delta_article_accepted
  · apply path_step_article_accepted
    · exact reduce_imp_domain_article_accepted _ _ _ _
        reduce_definition_domain_beta_article_accepted
    · exact path_refl_article_accepted _

private def conversionArticle : RawProof :=
  node "megalodon-def-conversion-common"
    [ encodeTermDeclarations [identityDeclaration, parameterDeclaration],
      ETm synthesizedIdentityGoal, ETm definitionGoal,
      ETm normalizedIdentityGoal ]
    [synthesizedPathArticle, declaredPathArticle]

private theorem conversion_article_accepted :
    checkRaw validated
      (converts
        (encodeTermDeclarations [identityDeclaration, parameterDeclaration])
      (ETm synthesizedIdentityGoal) (ETm definitionGoal))
      conversionArticle = true := by
  simp only [conversionArticle, node, checkRaw, validated, instantiateRule?]
  rw [lookup_conversionCommonRule]
  simp only [conversionCommonRule, rule, ruleId, reductionPath, converts,
    scopedTerm, a, m, argumentsValidAt, argumentValidAt,
    RuleSchema.sideConditionsHold, instantiateSchemas?, instantiateSchema?,
    instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?,
    List.map, List.all]
  simp [checkRawChildren]
  exact ⟨by simpa [validated, reductionPath, a] using
      synthesized_path_article_accepted,
    by simpa [validated, reductionPath, a] using
      declared_path_article_accepted⟩

def definitionIdentityGoal : Pattern :=
  fullProves (encodeFullEnvironment definitionEnvironment)
    (ENat 0) (ETyCtx []) (EPfCtx []) (ETm definitionGoal)

def definitionIdentityArticle : RawProof :=
  node "megalodon-def-proof"
    [ EnvironmentKernel.encodePrimitiveTypes [],
      encodeTermDeclarations [identityDeclaration, parameterDeclaration],
      ESig [identityDeclaration, parameterDeclaration],
      EnvironmentKernel.encodeKnown [], ENat 0, ETyCtx [], EPfCtx [],
      ETm synthesizedIdentityGoal, ETm definitionGoal ]
    [ compileProjection [identityDeclaration, parameterDeclaration],
      environmentIdentityArticle, conversionArticle ]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem definition_identity_article_accepted :
    checkRaw validated definitionIdentityGoal definitionIdentityArticle = true := by
  simp only [definitionIdentityArticle, node, checkRaw, validated,
    instantiateRule?]
  rw [lookup_fullProofRule]
  simp only [fullProofRule, rule, ruleId, projectSignature, baseProves,
    converts, scopedTerm, fullProves, definitionIdentityGoal,
    encodeFullEnvironment, definitionEnvironment, a, m, argumentsValidAt,
    argumentValidAt, RuleSchema.sideConditionsHold, instantiateSchemas?,
    instantiateSchema?, instantiateSchemasAt?, instantiateSchemaAt?,
    lookupArgumentAt?, List.map, List.all]
  simp [EnvironmentKernel.encodePrimitiveTypes, EnvironmentKernel.encodeKnown,
    TermQuantifiedKernel.encodeTypeContext,
    TermQuantifiedKernel.encodeProofContext, TermQuantifiedKernel.a,
    Pattern.isGroundAt, Pattern.isGroundListAt,
    Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList, checkRawChildren]
  exact ⟨by simpa [validated, projectSignature, a] using
      compileProjection_checked [identityDeclaration, parameterDeclaration],
    by simpa [validated, baseProves,
      EnvironmentKernel.encodePrimitiveTypes, EnvironmentKernel.encodeKnown,
      TermQuantifiedKernel.encodeTypeContext,
      TermQuantifiedKernel.encodeProofContext, TermQuantifiedKernel.a, a] using
      environment_identity_article_accepted,
    by simpa [validated, converts, scopedTerm, a] using
      conversion_article_accepted⟩

def definitionIdentityWrongGoal : Pattern :=
  fullProves (encodeFullEnvironment definitionEnvironment)
    (ENat 0) (ETyCtx []) (EPfCtx []) (ETm synthesizedIdentityGoal)

theorem definition_identity_wrong_goal_rejected :
    checkRaw validated definitionIdentityWrongGoal definitionIdentityArticle = false := by
  by_contra hypothesis
  have acceptedWrong :
      checkRaw validated definitionIdentityWrongGoal definitionIdentityArticle = true := by
    simpa using hypothesis
  have goalsEqual := checkRaw_goal_unique definition_identity_article_accepted
    acceptedWrong
  simp [definitionIdentityGoal, definitionIdentityWrongGoal,
    definitionGoal, synthesizedIdentityGoal, definitionDomain,
    definitionEnvironment, identityDeclaration, parameterDeclaration,
    definitionParameterName, identityDefinitionName, encodeFullEnvironment,
    encodeTermDeclarations, TermQuantifiedKernel.encodeTm,
    TermQuantifiedKernel.a, fullProves, a]
    at goalsEqual

open Mettapedia.GSLT.LanguageDef.InferenceLanguageWire

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
/-- Every fixed constructor occurrence in the exact definition article is
declared by the checker-facing runtime projection. -/
theorem definition_identity_closed_payload :
    (RuntimeInferenceLanguage.ofDefinition definition).proofPayloadsValid
        definitionIdentityArticle = true := by
  simp (config := { maxSteps := 5000000, decide := true })
    [ RuntimeInferenceLanguage.ofDefinition,
      RuntimeInferenceLanguage.proofPayloadsValid,
      RuntimeInferenceLanguage.proofPayloadListsValid,
      RuntimeInferenceLanguage.fixedConstructorListsValid,
      RuntimeInferenceLanguage.fixedConstructorsValid,
      definitionIdentityArticle, node, compileProjection,
      environmentIdentityArticle, baseIdentityArticle, baseHypArticle,
      domainTypeArticle, identityTypeArticle, parameterTypeArticle,
      parameterTailTypeArticle, conversionArticle, synthesizedPathArticle,
      declaredPathArticle, pathStepArticle, pathReflArticle,
      reduceDefinitionDomainDeltaArticle, deltaIdentityArticle,
      definitionHereArticle, reduceDefinitionDomainBetaArticle,
      betaSubstitutionArticle, betaShiftArticle,
      definition, definition, additionalConstructors,
      EnvironmentKernel.definition, EnvironmentKernel.additionalConstructors,
      PolymorphicKernel.definition, TermQuantifiedKernel.definition,
      TermQuantifiedKernel.constructors,
      TermQuantifiedKernel.expressionConstructor,
      identityDeclaration, parameterDeclaration,
      definitionGoal, synthesizedIdentityGoal, normalizedIdentityGoal,
      definitionDomain, definitionParameterName, identityDefinitionName,
      encodeTermDeclarations,
      TermQuantifiedKernel.encodeSignature,
      TermQuantifiedKernel.encodeTypeContext,
      TermQuantifiedKernel.encodeProofContext,
      TermQuantifiedKernel.encodeNat, TermQuantifiedKernel.encodeTp,
      TermQuantifiedKernel.encodeTm, TermQuantifiedKernel.a,
      EnvironmentKernel.encodePrimitiveTypes, EnvironmentKernel.encodeKnown,
      a ]

/-- The real Mathdata checker and the coGSLT authority accept the same exact
definition-bearing theorem and article specimen. -/
theorem definition_identity_direct_and_cogslt :
    MathdataKernel.checkProof definitionEnvironment 32 0 [] []
        identityProof definitionGoal = true ∧
      checkRaw validated definitionIdentityGoal definitionIdentityArticle = true :=
  ⟨mathdata_accepts_definition_identity, definition_identity_article_accepted⟩

end Mettapedia.Languages.Megalodon.DefinitionConversionKernel
