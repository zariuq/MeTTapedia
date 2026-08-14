import Mettapedia.Languages.Megalodon.PolymorphicKernel
import Mettapedia.Languages.Megalodon.SortedABTRefinement

/-!
# Megalodon checked-environment kernel

This layer separates a proof relative to an explicit Mathdata environment
from the document transition that admits a newly checked proposition into
that environment.  It adds proof-relevant known-proposition lookup and
proof-level type application to the polymorphic kernel.

Type substitution is presented recursively over the complete Mathdata type
and term syntax.  The compiler below produces its rule article and proves
that the computed endpoint is Mathdata's operation; the sorted-ABT
refinement then identifies that endpoint with substitution on the generic
two-axis carrier.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Megalodon.EnvironmentKernel

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

def addNat (left right result : Pattern) : Pattern :=
  a "MAddNat" [left, right, result]

def lessThan (left right : Pattern) : Pattern :=
  a "MLessThan" [left, right]

def plainType (depth type : Pattern) : Pattern :=
  a "MPlainType" [depth, type]

def baseHasType
    (signature typeDepth context term type : Pattern) : Pattern :=
  a "MPolyTermHasType" [signature, typeDepth, context, term, type]

def baseProves
    (signature typeDepth termContext proofContext proposition : Pattern) :
    Pattern :=
  a "MPolyTermProves"
    [signature, typeDepth, termContext, proofContext, proposition]

def proves
    (environment typeDepth termContext proofContext proposition : Pattern) :
    Pattern :=
  a "MMathdataProves"
    [environment, typeDepth, termContext, proofContext, proposition]

def knownMember
    (known identifier proposition : Pattern) : Pattern :=
  a "MKnownMember" [known, identifier, proposition]

def shiftType
    (amount cutoff source target : Pattern) : Pattern :=
  a "MShiftType" [amount, cutoff, source, target]

def substituteType
    (index replacement body result : Pattern) : Pattern :=
  a "MSubstituteType" [index, replacement, body, result]

def substituteTypeInTerm
    (index replacement body result : Pattern) : Pattern :=
  a "MSubstituteTypeInTerm" [index, replacement, body, result]

def shiftProofContext
    (amount cutoff source target : Pattern) : Pattern :=
  a "MShiftProofContext" [amount, cutoff, source, target]

def substituteTerm
    (index replacement body result : Pattern) : Pattern :=
  a "MSubstituteTerm" [index, replacement, body, result]

def checksDocument
    (initial declarations final : Pattern) : Pattern :=
  a "MMathdataChecksDocument" [initial, declarations, final]

def implicationReuseTermName : String :=
  "0000000000000000000000000000000000000000000000000000000000000021"

def implicationReuseKnownName : String :=
  "7d07234c3fd77c6cc744595636eb0f71763edce8bf62701fd76fb67f6f31e951"

def encodePrimitiveTypes : List MathdataKernel.Tp → Pattern
  | [] => a "MPrimNil"
  | type :: types =>
      a "MPrimCons"
        [TermQuantifiedKernel.encodeTp type, encodePrimitiveTypes types]

def encodeKnown : List MathdataKernel.KnownDecl → Pattern
  | [] => a "MKnownNil"
  | declaration :: declarations =>
      a "MKnownCons"
        [a declaration.name, TermQuantifiedKernel.encodeTm declaration.proposition,
          encodeKnown declarations]

def encodeEnvironment (environment : MathdataKernel.Environment) : Pattern :=
  a "MEnvironment"
    [ encodePrimitiveTypes environment.primitives,
      TermQuantifiedKernel.encodeSignature environment.terms,
      encodeKnown environment.known ]

def encodeDeclarations : List MathdataKernel.KnownDecl → Pattern
  | [] => a "MDocumentNil"
  | declaration :: declarations =>
      a "MDocumentCons"
        [a declaration.name, TermQuantifiedKernel.encodeTm declaration.proposition,
          encodeDeclarations declarations]

/-! ## Type-axis shifting -/

def shiftTypeVarZeroRule : RuleSchema :=
  rule "megalodon-env-shift-type-var-zero"
    ["amount", "variable", "result"]
    [addNat (m "variable") (m "amount") (m "result")]
    (shiftType (m "amount") (a "MNZero")
      (a "MTpVar" [m "variable"]) (a "MTpVar" [m "result"]))

def shiftTypeVarBelowRule : RuleSchema :=
  rule "megalodon-env-shift-type-var-below" ["amount", "cutoff"] []
    (shiftType (m "amount") (a "MNSucc" [m "cutoff"])
      (a "MTpVar" [a "MNZero"]) (a "MTpVar" [a "MNZero"]))

def shiftTypeVarSuccRule : RuleSchema :=
  rule "megalodon-env-shift-type-var-succ"
    ["amount", "cutoff", "variable", "result"]
    [shiftType (m "amount") (m "cutoff")
      (a "MTpVar" [m "variable"]) (a "MTpVar" [m "result"])]
    (shiftType (m "amount") (a "MNSucc" [m "cutoff"])
      (a "MTpVar" [a "MNSucc" [m "variable"]])
      (a "MTpVar" [a "MNSucc" [m "result"]]))

def shiftTypePropRule : RuleSchema :=
  rule "megalodon-env-shift-type-prop" ["amount", "cutoff"] []
    (shiftType (m "amount") (m "cutoff")
      (a "MTpProp") (a "MTpProp"))

def shiftTypeBaseRule : RuleSchema :=
  rule "megalodon-env-shift-type-base" ["amount", "cutoff", "index"] []
    (shiftType (m "amount") (m "cutoff")
      (a "MTpBase" [m "index"]) (a "MTpBase" [m "index"]))

def shiftTypeArrRule : RuleSchema :=
  rule "megalodon-env-shift-type-arr"
    ["amount", "cutoff", "domain", "codomain",
      "domainResult", "codomainResult"]
    [ shiftType (m "amount") (m "cutoff")
        (m "domain") (m "domainResult"),
      shiftType (m "amount") (m "cutoff")
        (m "codomain") (m "codomainResult") ]
    (shiftType (m "amount") (m "cutoff")
      (a "MTpArr" [m "domain", m "codomain"])
      (a "MTpArr" [m "domainResult", m "codomainResult"]))

def shiftTypeAllRule : RuleSchema :=
  rule "megalodon-env-shift-type-all"
    ["amount", "cutoff", "body", "bodyResult"]
    [shiftType (m "amount") (a "MNSucc" [m "cutoff"])
      (m "body") (m "bodyResult")]
    (shiftType (m "amount") (m "cutoff")
      (a "MTpAll" [m "body"]) (a "MTpAll" [m "bodyResult"]))

/-! ## Type substitution in types -/

def substituteTypeVarEqualRule : RuleSchema :=
  rule "megalodon-env-substitute-type-var-equal"
    ["index", "replacement", "shifted"]
    [shiftType (m "index") (a "MNZero")
      (m "replacement") (m "shifted")]
    (substituteType (m "index") (m "replacement")
      (a "MTpVar" [m "index"]) (m "shifted"))

def substituteTypeVarBelowRule : RuleSchema :=
  rule "megalodon-env-substitute-type-var-below"
    ["index", "replacement", "variable"]
    [lessThan (m "variable") (m "index")]
    (substituteType (m "index") (m "replacement")
      (a "MTpVar" [m "variable"]) (a "MTpVar" [m "variable"]))

def substituteTypeVarAboveRule : RuleSchema :=
  rule "megalodon-env-substitute-type-var-above"
    ["index", "replacement", "predecessor"]
    [lessThan (m "index") (a "MNSucc" [m "predecessor"])]
    (substituteType (m "index") (m "replacement")
      (a "MTpVar" [a "MNSucc" [m "predecessor"]])
      (a "MTpVar" [m "predecessor"]))

def substituteTypePropRule : RuleSchema :=
  rule "megalodon-env-substitute-type-prop" ["index", "replacement"] []
    (substituteType (m "index") (m "replacement")
      (a "MTpProp") (a "MTpProp"))

def substituteTypeBaseRule : RuleSchema :=
  rule "megalodon-env-substitute-type-base"
    ["index", "replacement", "base"] []
    (substituteType (m "index") (m "replacement")
      (a "MTpBase" [m "base"]) (a "MTpBase" [m "base"]))

def substituteTypeArrRule : RuleSchema :=
  rule "megalodon-env-substitute-type-arr"
    ["index", "replacement", "domain", "codomain",
      "domainResult", "codomainResult"]
    [ substituteType (m "index") (m "replacement")
        (m "domain") (m "domainResult"),
      substituteType (m "index") (m "replacement")
        (m "codomain") (m "codomainResult") ]
    (substituteType (m "index") (m "replacement")
      (a "MTpArr" [m "domain", m "codomain"])
      (a "MTpArr" [m "domainResult", m "codomainResult"]))

def substituteTypeAllRule : RuleSchema :=
  rule "megalodon-env-substitute-type-all"
    ["index", "replacement", "body", "bodyResult"]
    [substituteType (a "MNSucc" [m "index"]) (m "replacement")
      (m "body") (m "bodyResult")]
    (substituteType (m "index") (m "replacement")
      (a "MTpAll" [m "body"]) (a "MTpAll" [m "bodyResult"]))

/-! ## Type substitution throughout terms -/

def substituteTypeTermVarRule : RuleSchema :=
  rule "megalodon-env-substitute-type-term-var"
    ["index", "replacement", "variable"] []
    (substituteTypeInTerm (m "index") (m "replacement")
      (a "MTmVar" [m "variable"]) (a "MTmVar" [m "variable"]))

def substituteTypeTermNamedRule : RuleSchema :=
  rule "megalodon-env-substitute-type-term-named"
    ["index", "replacement", "name"] []
    (substituteTypeInTerm (m "index") (m "replacement")
      (a "MTmNamed" [m "name"]) (a "MTmNamed" [m "name"]))

def substituteTypeTermPrimRule : RuleSchema :=
  rule "megalodon-env-substitute-type-term-prim"
    ["index", "replacement", "primitive"] []
    (substituteTypeInTerm (m "index") (m "replacement")
      (a "MTmPrim" [m "primitive"]) (a "MTmPrim" [m "primitive"]))

def substituteTypeTermAppRule : RuleSchema :=
  rule "megalodon-env-substitute-type-term-app"
    ["index", "replacement", "function", "argument",
      "functionResult", "argumentResult"]
    [ substituteTypeInTerm (m "index") (m "replacement")
        (m "function") (m "functionResult"),
      substituteTypeInTerm (m "index") (m "replacement")
        (m "argument") (m "argumentResult") ]
    (substituteTypeInTerm (m "index") (m "replacement")
      (a "MTmApp" [m "function", m "argument"])
      (a "MTmApp" [m "functionResult", m "argumentResult"]))

def substituteTypeTermLamRule : RuleSchema :=
  rule "megalodon-env-substitute-type-term-lam"
    ["index", "replacement", "type", "body", "typeResult", "bodyResult"]
    [ substituteType (m "index") (m "replacement")
        (m "type") (m "typeResult"),
      substituteTypeInTerm (m "index") (m "replacement")
        (m "body") (m "bodyResult") ]
    (substituteTypeInTerm (m "index") (m "replacement")
      (a "MTmLam" [m "type", m "body"])
      (a "MTmLam" [m "typeResult", m "bodyResult"]))

def substituteTypeTermImpRule : RuleSchema :=
  rule "megalodon-env-substitute-type-term-imp"
    ["index", "replacement", "domain", "codomain",
      "domainResult", "codomainResult"]
    [ substituteTypeInTerm (m "index") (m "replacement")
        (m "domain") (m "domainResult"),
      substituteTypeInTerm (m "index") (m "replacement")
        (m "codomain") (m "codomainResult") ]
    (substituteTypeInTerm (m "index") (m "replacement")
      (a "MTmImp" [m "domain", m "codomain"])
      (a "MTmImp" [m "domainResult", m "codomainResult"]))

def substituteTypeTermAllRule : RuleSchema :=
  rule "megalodon-env-substitute-type-term-all"
    ["index", "replacement", "type", "body", "typeResult", "bodyResult"]
    [ substituteType (m "index") (m "replacement")
        (m "type") (m "typeResult"),
      substituteTypeInTerm (m "index") (m "replacement")
        (m "body") (m "bodyResult") ]
    (substituteTypeInTerm (m "index") (m "replacement")
      (a "MTmAll" [m "type", m "body"])
      (a "MTmAll" [m "typeResult", m "bodyResult"]))

def substituteTypeTermTypeAppRule : RuleSchema :=
  rule "megalodon-env-substitute-type-term-type-app"
    ["index", "replacement", "function", "type",
      "functionResult", "typeResult"]
    [ substituteTypeInTerm (m "index") (m "replacement")
        (m "function") (m "functionResult"),
      substituteType (m "index") (m "replacement")
        (m "type") (m "typeResult") ]
    (substituteTypeInTerm (m "index") (m "replacement")
      (a "MTmTypeApp" [m "function", m "type"])
      (a "MTmTypeApp" [m "functionResult", m "typeResult"]))

def substituteTypeTermTypeLamRule : RuleSchema :=
  rule "megalodon-env-substitute-type-term-type-lam"
    ["index", "replacement", "body", "bodyResult"]
    [substituteTypeInTerm (a "MNSucc" [m "index"])
      (m "replacement") (m "body") (m "bodyResult")]
    (substituteTypeInTerm (m "index") (m "replacement")
      (a "MTmTypeLam" [m "body"])
      (a "MTmTypeLam" [m "bodyResult"]))

def substituteTypeTermTypeAllRule : RuleSchema :=
  rule "megalodon-env-substitute-type-term-type-all"
    ["index", "replacement", "body", "bodyResult"]
    [substituteTypeInTerm (a "MNSucc" [m "index"])
      (m "replacement") (m "body") (m "bodyResult")]
    (substituteTypeInTerm (m "index") (m "replacement")
      (a "MTmTypeAll" [m "body"])
      (a "MTmTypeAll" [m "bodyResult"]))

/-! ## Completion of the term-axis relation on Mathdata syntax -/

def shiftTermPrimRule : RuleSchema :=
  rule "megalodon-env-shift-term-prim"
    ["amount", "cutoff", "primitive"] []
    (a "MShiftTerm"
      [m "amount", m "cutoff", a "MTmPrim" [m "primitive"],
        a "MTmPrim" [m "primitive"]])

def shiftTermLamRule : RuleSchema :=
  rule "megalodon-env-shift-term-lam"
    ["amount", "cutoff", "type", "body", "bodyResult"]
    [a "MShiftTerm"
      [m "amount", a "MNSucc" [m "cutoff"], m "body", m "bodyResult"]]
    (a "MShiftTerm"
      [m "amount", m "cutoff", a "MTmLam" [m "type", m "body"],
        a "MTmLam" [m "type", m "bodyResult"]])

def shiftTermTypeAppRule : RuleSchema :=
  rule "megalodon-env-shift-term-type-app"
    ["amount", "cutoff", "function", "type", "functionResult"]
    [a "MShiftTerm"
      [m "amount", m "cutoff", m "function", m "functionResult"]]
    (a "MShiftTerm"
      [m "amount", m "cutoff", a "MTmTypeApp" [m "function", m "type"],
        a "MTmTypeApp" [m "functionResult", m "type"]])

def shiftTermTypeLamRule : RuleSchema :=
  rule "megalodon-env-shift-term-type-lam"
    ["amount", "cutoff", "body", "bodyResult"]
    [a "MShiftTerm"
      [m "amount", m "cutoff", m "body", m "bodyResult"]]
    (a "MShiftTerm"
      [m "amount", m "cutoff", a "MTmTypeLam" [m "body"],
        a "MTmTypeLam" [m "bodyResult"]])

def shiftTermTypeAllRule : RuleSchema :=
  rule "megalodon-env-shift-term-type-all"
    ["amount", "cutoff", "body", "bodyResult"]
    [a "MShiftTerm"
      [m "amount", m "cutoff", m "body", m "bodyResult"]]
    (a "MShiftTerm"
      [m "amount", m "cutoff", a "MTmTypeAll" [m "body"],
        a "MTmTypeAll" [m "bodyResult"]])

def substituteTermPrimRule : RuleSchema :=
  rule "megalodon-env-substitute-term-prim"
    ["index", "replacement", "primitive"] []
    (substituteTerm (m "index") (m "replacement")
      (a "MTmPrim" [m "primitive"]) (a "MTmPrim" [m "primitive"]))

def substituteTermLamRule : RuleSchema :=
  rule "megalodon-env-substitute-term-lam"
    ["index", "replacement", "type", "body", "bodyResult"]
    [substituteTerm (a "MNSucc" [m "index"]) (m "replacement")
      (m "body") (m "bodyResult")]
    (substituteTerm (m "index") (m "replacement")
      (a "MTmLam" [m "type", m "body"])
      (a "MTmLam" [m "type", m "bodyResult"]))

def substituteTermTypeAppRule : RuleSchema :=
  rule "megalodon-env-substitute-term-type-app"
    ["index", "replacement", "function", "type", "functionResult"]
    [substituteTerm (m "index") (m "replacement")
      (m "function") (m "functionResult")]
    (substituteTerm (m "index") (m "replacement")
      (a "MTmTypeApp" [m "function", m "type"])
      (a "MTmTypeApp" [m "functionResult", m "type"]))

def substituteTermTypeLamRule : RuleSchema :=
  rule "megalodon-env-substitute-term-type-lam"
    ["index", "replacement", "body", "bodyResult"]
    [substituteTerm (m "index") (m "replacement")
      (m "body") (m "bodyResult")]
    (substituteTerm (m "index") (m "replacement")
      (a "MTmTypeLam" [m "body"])
      (a "MTmTypeLam" [m "bodyResult"]))

def substituteTermTypeAllRule : RuleSchema :=
  rule "megalodon-env-substitute-term-type-all"
    ["index", "replacement", "body", "bodyResult"]
    [substituteTerm (m "index") (m "replacement")
      (m "body") (m "bodyResult")]
    (substituteTerm (m "index") (m "replacement")
      (a "MTmTypeAll" [m "body"])
      (a "MTmTypeAll" [m "bodyResult"]))

/-! ## Explicit environment and checked document rules -/

def knownHereRule : RuleSchema :=
  rule "megalodon-env-known-here"
    ["identifier", "proposition", "tail"] []
    (knownMember
      (a "MKnownCons" [m "identifier", m "proposition", m "tail"])
      (m "identifier") (m "proposition"))

def knownThereRule : RuleSchema :=
  rule "megalodon-env-known-there"
    ["headIdentifier", "headProposition", "tail", "identifier",
      "proposition"]
    [knownMember (m "tail") (m "identifier") (m "proposition")]
    (knownMember
      (a "MKnownCons"
        [m "headIdentifier", m "headProposition", m "tail"])
      (m "identifier") (m "proposition"))

def proofBaseRule : RuleSchema :=
  rule "megalodon-env-proof-base"
    ["primitives", "signature", "known", "typeDepth", "termContext",
      "proofContext", "proposition"]
    [baseProves (m "signature") (m "typeDepth") (m "termContext")
      (m "proofContext") (m "proposition")]
    (proves
      (a "MEnvironment" [m "primitives", m "signature", m "known"])
      (m "typeDepth") (m "termContext") (m "proofContext")
      (m "proposition"))

def proofKnownRule : RuleSchema :=
  rule "megalodon-env-proof-known"
    ["primitives", "signature", "known", "typeDepth", "termContext",
      "proofContext", "identifier", "proposition"]
    [knownMember (m "known") (m "identifier") (m "proposition")]
    (proves
      (a "MEnvironment" [m "primitives", m "signature", m "known"])
      (m "typeDepth") (m "termContext") (m "proofContext")
      (m "proposition"))

def proofImpIntroRule : RuleSchema :=
  rule "megalodon-env-proof-imp-intro"
    ["primitives", "signature", "known", "typeDepth", "termContext",
      "proofContext", "domain", "codomain"]
    [ baseHasType (m "signature") (m "typeDepth") (m "termContext")
        (m "domain") (a "MTpProp"),
      proves
        (a "MEnvironment" [m "primitives", m "signature", m "known"])
        (m "typeDepth") (m "termContext")
        (a "MPfCtxCons" [m "domain", m "proofContext"])
        (m "codomain") ]
    (proves
      (a "MEnvironment" [m "primitives", m "signature", m "known"])
      (m "typeDepth") (m "termContext") (m "proofContext")
      (a "MTmImp" [m "domain", m "codomain"]))

def proofImpElimRule : RuleSchema :=
  rule "megalodon-env-proof-imp-elim"
    ["environment", "typeDepth", "termContext", "proofContext", "domain",
      "codomain"]
    [ proves (m "environment") (m "typeDepth") (m "termContext")
        (m "proofContext") (a "MTmImp" [m "domain", m "codomain"]),
      proves (m "environment") (m "typeDepth") (m "termContext")
        (m "proofContext") (m "domain") ]
    (proves (m "environment") (m "typeDepth") (m "termContext")
      (m "proofContext") (m "codomain"))

def proofTypeElimRule : RuleSchema :=
  rule "megalodon-env-proof-type-elim"
    ["environment", "typeDepth", "termContext", "proofContext",
      "body", "type", "result"]
    [ proves (m "environment") (m "typeDepth") (m "termContext")
        (m "proofContext") (a "MTmTypeAll" [m "body"]),
      substituteTypeInTerm (a "MNZero") (m "type")
        (m "body") (m "result") ]
    (proves (m "environment") (m "typeDepth") (m "termContext")
      (m "proofContext") (m "result"))

def proofAllElimRule : RuleSchema :=
  rule "megalodon-env-proof-all-elim"
    ["primitives", "signature", "known", "typeDepth", "termContext",
      "proofContext", "type", "body", "argument", "result"]
    [ proves
        (a "MEnvironment" [m "primitives", m "signature", m "known"])
        (m "typeDepth") (m "termContext") (m "proofContext")
        (a "MTmAll" [m "type", m "body"]),
      baseHasType (m "signature") (m "typeDepth") (m "termContext")
        (m "argument") (m "type"),
      substituteTerm (a "MNZero") (m "argument")
        (m "body") (m "result") ]
    (proves
      (a "MEnvironment" [m "primitives", m "signature", m "known"])
      (m "typeDepth") (m "termContext") (m "proofContext")
      (m "result"))

def proofAllIntroRule : RuleSchema :=
  rule "megalodon-env-proof-all-intro"
    ["environment", "typeDepth", "termContext", "proofContext",
      "shiftedProofContext", "type", "body"]
    [ plainType (m "typeDepth") (m "type"),
      shiftProofContext (a "MNSucc" [a "MNZero"]) (a "MNZero")
        (m "proofContext") (m "shiftedProofContext"),
      proves (m "environment") (m "typeDepth")
        (a "MTyCtxCons" [m "type", m "termContext"])
        (m "shiftedProofContext") (m "body") ]
    (proves (m "environment") (m "typeDepth") (m "termContext")
      (m "proofContext") (a "MTmAll" [m "type", m "body"]))

def proofTypeIntroRule : RuleSchema :=
  rule "megalodon-env-proof-type-intro" ["environment", "body"]
    [proves (m "environment") (a "MNSucc" [a "MNZero"])
      (a "MTyCtxNil") (a "MPfCtxNil") (m "body")]
    (proves (m "environment") (a "MNZero")
      (a "MTyCtxNil") (a "MPfCtxNil")
      (a "MTmTypeAll" [m "body"]))

def documentNilRule : RuleSchema :=
  rule "megalodon-env-document-nil" ["environment"] []
    (checksDocument (m "environment") (a "MDocumentNil")
      (m "environment"))

def documentConsRule : RuleSchema :=
  rule "megalodon-env-document-cons"
    ["primitives", "signature", "known", "identifier", "proposition",
      "declarations", "final"]
    [ proves
        (a "MEnvironment" [m "primitives", m "signature", m "known"])
        (a "MNZero") (a "MTyCtxNil") (a "MPfCtxNil")
        (m "proposition"),
      checksDocument
        (a "MEnvironment"
          [m "primitives", m "signature",
            a "MKnownCons"
              [m "identifier", m "proposition", m "known"]])
        (m "declarations") (m "final") ]
    (checksDocument
      (a "MEnvironment" [m "primitives", m "signature", m "known"])
      (a "MDocumentCons"
        [m "identifier", m "proposition", m "declarations"])
      (m "final"))

def additionalConstructors : List (String × Nat) :=
  [ ("MPrimNil", 0), ("MPrimCons", 2),
    ("MKnownNil", 0), ("MKnownCons", 3), ("MEnvironment", 3),
    ("MDocumentNil", 0), ("MDocumentCons", 3),
    (MathdataKernel.polymorphicReuseName, 0),
    (implicationReuseTermName, 0), (implicationReuseKnownName, 0) ]

def additionalJudgments : List JudgmentDecl :=
  [ { head := "MShiftType", arity := 4 },
    { head := "MSubstituteType", arity := 4 },
    { head := "MSubstituteTypeInTerm", arity := 4 },
    { head := "MKnownMember", arity := 3 },
    { head := "MMathdataProves", arity := 5 },
    { head := "MMathdataChecksDocument", arity := 3 } ]

def additionalRules : List RuleSchema :=
  [ shiftTypeVarZeroRule, shiftTypeVarBelowRule, shiftTypeVarSuccRule,
    shiftTypePropRule, shiftTypeBaseRule, shiftTypeArrRule, shiftTypeAllRule,
    substituteTypeVarEqualRule, substituteTypeVarBelowRule,
    substituteTypeVarAboveRule, substituteTypePropRule,
    substituteTypeBaseRule, substituteTypeArrRule, substituteTypeAllRule,
    substituteTypeTermVarRule, substituteTypeTermNamedRule,
    substituteTypeTermPrimRule, substituteTypeTermAppRule,
    substituteTypeTermLamRule, substituteTypeTermImpRule,
    substituteTypeTermAllRule, substituteTypeTermTypeAppRule,
    substituteTypeTermTypeLamRule, substituteTypeTermTypeAllRule,
    shiftTermPrimRule, shiftTermLamRule, shiftTermTypeAppRule,
    shiftTermTypeLamRule, shiftTermTypeAllRule,
    substituteTermPrimRule, substituteTermLamRule,
    substituteTermTypeAppRule, substituteTermTypeLamRule,
    substituteTermTypeAllRule,
    knownHereRule, knownThereRule, proofBaseRule, proofKnownRule,
    proofImpIntroRule, proofImpElimRule,
    proofTypeElimRule, proofAllElimRule, proofAllIntroRule,
    proofTypeIntroRule, documentNilRule, documentConsRule ]

def definition : CalculusLanguageDef :=
  { PolymorphicKernel.definition with
    name := "megalodon-checked-environment-kernel-v1"
    terms := PolymorphicKernel.definition.terms ++
      additionalConstructors.map fun declaration =>
        TermQuantifiedKernel.expressionConstructor declaration.1 declaration.2
    judgments := PolymorphicKernel.definition.judgments ++
      additionalJudgments
    rules := PolymorphicKernel.definition.rules ++ additionalRules }

def presentation : Presentation := definition.toNested

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem presentation_valid : presentation.isValidV2 = true := by
  have hvalidate : presentation.language.validate = [] := by
    apply LanguageDef.validate_eq_nil_of_constructorOnly <;>
      simp [presentation, definition, additionalConstructors,
        MathdataKernel.polymorphicReuseName, implicationReuseTermName,
        implicationReuseKnownName,
        PolymorphicKernel.definition, TermQuantifiedKernel.definition,
        TermQuantifiedKernel.constructors,
        TermQuantifiedKernel.expressionType,
        TermQuantifiedKernel.expressionConstructor,
        LanguageDef.typeNames, TypeDecl.plain, TermParam.typeExpr,
        TypeExpr.baseNames]
  unfold Presentation.isValidV2 Presentation.isValidV1
  rw [hvalidate]
  simp [presentation, definition, additionalConstructors,
    MathdataKernel.polymorphicReuseName, implicationReuseTermName,
    implicationReuseKnownName,
    additionalJudgments, additionalRules,
    Presentation.ruleIds, Presentation.judgmentSignatureValid,
    Presentation.judgmentHeads, Presentation.conversionDeclarationValid,
    Presentation.lookupJudgment?, RuleSchema.isValidIn, RuleSchema.isValidV1,
    RuleSchema.metavariableNames, RuleSchema.occurrences,
    RuleSchema.patterns, patternMetavariableOccurrencesAt,
    patternsMetavariableOccurrencesAt, patternHasNoCollectionRest,
    patternsHaveNoCollectionRest, Presentation.judgmentSchemaValid,
    fixedConstructorsValid, fixedConstructorListsValid,
    languageHasConstructorArity, Pattern.isWellScoped,
    Pattern.isWellScopedAt, Pattern.isWellScopedListAt,
    Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList, Pattern.zipHead, Pattern.mapHead,
    Pattern.evalHead,
    shiftTypeVarZeroRule, shiftTypeVarBelowRule, shiftTypeVarSuccRule,
    shiftTypePropRule, shiftTypeBaseRule, shiftTypeArrRule, shiftTypeAllRule,
    substituteTypeVarEqualRule, substituteTypeVarBelowRule,
    substituteTypeVarAboveRule, substituteTypePropRule,
    substituteTypeBaseRule, substituteTypeArrRule, substituteTypeAllRule,
    substituteTypeTermVarRule, substituteTypeTermNamedRule,
    substituteTypeTermPrimRule, substituteTypeTermAppRule,
    substituteTypeTermLamRule, substituteTypeTermImpRule,
    substituteTypeTermAllRule, substituteTypeTermTypeAppRule,
    substituteTypeTermTypeLamRule, substituteTypeTermTypeAllRule,
    shiftTermPrimRule, shiftTermLamRule, shiftTermTypeAppRule,
    shiftTermTypeLamRule, shiftTermTypeAllRule,
    substituteTermPrimRule, substituteTermLamRule,
    substituteTermTypeAppRule, substituteTermTypeLamRule,
    substituteTermTypeAllRule,
    knownHereRule, knownThereRule, proofBaseRule, proofKnownRule,
    proofImpIntroRule, proofImpElimRule,
    proofTypeElimRule, proofAllElimRule, proofAllIntroRule,
    proofTypeIntroRule, documentNilRule, documentConsRule,
    rule, ruleId, addNat, lessThan, plainType, baseHasType, baseProves,
    proves, knownMember, shiftType, substituteType, substituteTypeInTerm,
    shiftProofContext, substituteTerm, checksDocument, a, m,
    PolymorphicKernel.definition, PolymorphicKernel.additionalJudgments,
    PolymorphicKernel.additionalRules, PolymorphicKernel.rule,
    PolymorphicKernel.ruleId, PolymorphicKernel.plainVarRule,
    PolymorphicKernel.plainPropRule, PolymorphicKernel.plainBaseRule,
    PolymorphicKernel.plainArrRule, PolymorphicKernel.typeVarZeroRule,
    PolymorphicKernel.typeVarSuccRule, PolymorphicKernel.typeNamedZeroRule,
    PolymorphicKernel.typeNamedSuccRule, PolymorphicKernel.typeAppRule,
    PolymorphicKernel.typeLamRule, PolymorphicKernel.typeImpRule,
    PolymorphicKernel.typeAllRule, PolymorphicKernel.proofHypZeroRule,
    PolymorphicKernel.proofHypSuccRule, PolymorphicKernel.proofImpIntroRule,
    PolymorphicKernel.proofImpElimRule, PolymorphicKernel.proofAllIntroRule,
    PolymorphicKernel.proofAllElimRule, PolymorphicKernel.proofTypeIntroRule,
    PolymorphicKernel.plainType, PolymorphicKernel.hasType,
    PolymorphicKernel.proves, PolymorphicKernel.lessThan,
    PolymorphicKernel.shiftProofContext, PolymorphicKernel.substituteTerm,
    PolymorphicKernel.a, PolymorphicKernel.m,
    TermQuantifiedKernel.definition,
    TermQuantifiedKernel.constructors, TermQuantifiedKernel.rules,
    TermQuantifiedKernel.expressionType,
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
    TermQuantifiedKernel.m,
    List.eraseDups, List.eraseDupsBy]
  simp (config := { maxSteps := 3000000, decide := true })

def validated : ValidatedPresentation := ⟨presentation, presentation_valid⟩

@[simp] private theorem lookup_shiftTypeVarZeroRule :
    presentation.lookupRule? (ruleId "megalodon-env-shift-type-var-zero") =
      some shiftTypeVarZeroRule := by
  rfl

@[simp] private theorem lookup_addZeroRule :
    presentation.lookupRule?
        (ruleId "megalodon-term-add-zero") =
      some TermQuantifiedKernel.addZeroRule := by
  rfl

@[simp] private theorem lookup_addSuccRule :
    presentation.lookupRule?
        (ruleId "megalodon-term-add-succ") =
      some TermQuantifiedKernel.addSuccRule := by
  rfl

@[simp] private theorem lookup_lessZeroRule :
    presentation.lookupRule?
        (ruleId "megalodon-term-less-zero") =
      some TermQuantifiedKernel.lessZeroRule := by
  rfl

@[simp] private theorem lookup_lessSuccRule :
    presentation.lookupRule?
        (ruleId "megalodon-term-less-succ") =
      some TermQuantifiedKernel.lessSuccRule := by
  rfl

@[simp] private theorem lookup_shiftTypeVarBelowRule :
    presentation.lookupRule? (ruleId "megalodon-env-shift-type-var-below") =
      some shiftTypeVarBelowRule := by
  rfl

@[simp] private theorem lookup_shiftTypeVarSuccRule :
    presentation.lookupRule? (ruleId "megalodon-env-shift-type-var-succ") =
      some shiftTypeVarSuccRule := by
  rfl

@[simp] private theorem lookup_shiftTypePropRule :
    presentation.lookupRule? (ruleId "megalodon-env-shift-type-prop") =
      some shiftTypePropRule := by
  rfl

@[simp] private theorem lookup_shiftTypeBaseRule :
    presentation.lookupRule? (ruleId "megalodon-env-shift-type-base") =
      some shiftTypeBaseRule := by
  rfl

@[simp] private theorem lookup_shiftTypeArrRule :
    presentation.lookupRule? (ruleId "megalodon-env-shift-type-arr") =
      some shiftTypeArrRule := by
  rfl

@[simp] private theorem lookup_shiftTypeAllRule :
    presentation.lookupRule? (ruleId "megalodon-env-shift-type-all") =
      some shiftTypeAllRule := by
  rfl

@[simp] private theorem lookup_substituteTypeVarEqualRule :
    presentation.lookupRule?
        (ruleId "megalodon-env-substitute-type-var-equal") =
      some substituteTypeVarEqualRule := by
  rfl

@[simp] private theorem lookup_substituteTypeVarBelowRule :
    presentation.lookupRule?
        (ruleId "megalodon-env-substitute-type-var-below") =
      some substituteTypeVarBelowRule := by
  rfl

@[simp] private theorem lookup_substituteTypeVarAboveRule :
    presentation.lookupRule?
        (ruleId "megalodon-env-substitute-type-var-above") =
      some substituteTypeVarAboveRule := by
  rfl

@[simp] private theorem lookup_substituteTypePropRule :
    presentation.lookupRule? (ruleId "megalodon-env-substitute-type-prop") =
      some substituteTypePropRule := by
  rfl

@[simp] private theorem lookup_substituteTypeBaseRule :
    presentation.lookupRule? (ruleId "megalodon-env-substitute-type-base") =
      some substituteTypeBaseRule := by
  rfl

@[simp] private theorem lookup_substituteTypeArrRule :
    presentation.lookupRule? (ruleId "megalodon-env-substitute-type-arr") =
      some substituteTypeArrRule := by
  rfl

@[simp] private theorem lookup_substituteTypeAllRule :
    presentation.lookupRule? (ruleId "megalodon-env-substitute-type-all") =
      some substituteTypeAllRule := by
  rfl

@[simp] private theorem lookup_substituteTypeTermVarRule :
    presentation.lookupRule?
        (ruleId "megalodon-env-substitute-type-term-var") =
      some substituteTypeTermVarRule := by
  rfl

@[simp] private theorem lookup_substituteTypeTermNamedRule :
    presentation.lookupRule?
        (ruleId "megalodon-env-substitute-type-term-named") =
      some substituteTypeTermNamedRule := by
  rfl

@[simp] private theorem lookup_substituteTypeTermPrimRule :
    presentation.lookupRule?
        (ruleId "megalodon-env-substitute-type-term-prim") =
      some substituteTypeTermPrimRule := by
  rfl

@[simp] private theorem lookup_substituteTypeTermAppRule :
    presentation.lookupRule?
        (ruleId "megalodon-env-substitute-type-term-app") =
      some substituteTypeTermAppRule := by
  rfl

@[simp] private theorem lookup_substituteTypeTermLamRule :
    presentation.lookupRule?
        (ruleId "megalodon-env-substitute-type-term-lam") =
      some substituteTypeTermLamRule := by
  rfl

@[simp] private theorem lookup_substituteTypeTermImpRule :
    presentation.lookupRule?
        (ruleId "megalodon-env-substitute-type-term-imp") =
      some substituteTypeTermImpRule := by
  rfl

@[simp] private theorem lookup_substituteTypeTermAllRule :
    presentation.lookupRule?
        (ruleId "megalodon-env-substitute-type-term-all") =
      some substituteTypeTermAllRule := by
  rfl

@[simp] private theorem lookup_substituteTypeTermTypeAppRule :
    presentation.lookupRule?
        (ruleId "megalodon-env-substitute-type-term-type-app") =
      some substituteTypeTermTypeAppRule := by
  rfl

@[simp] private theorem lookup_substituteTypeTermTypeLamRule :
    presentation.lookupRule?
        (ruleId "megalodon-env-substitute-type-term-type-lam") =
      some substituteTypeTermTypeLamRule := by
  rfl

@[simp] private theorem lookup_substituteTypeTermTypeAllRule :
    presentation.lookupRule?
        (ruleId "megalodon-env-substitute-type-term-type-all") =
      some substituteTypeTermTypeAllRule := by
  rfl

@[simp] private theorem lookup_shiftTermVarZeroRule :
    presentation.lookupRule? (ruleId "megalodon-term-shift-var-zero") =
      some TermQuantifiedKernel.shiftVarAtZeroRule := by
  rfl

@[simp] private theorem lookup_shiftTermVarBelowRule :
    presentation.lookupRule? (ruleId "megalodon-term-shift-var-below") =
      some TermQuantifiedKernel.shiftVarBelowRule := by
  rfl

@[simp] private theorem lookup_shiftTermVarSuccRule :
    presentation.lookupRule? (ruleId "megalodon-term-shift-var-succ") =
      some TermQuantifiedKernel.shiftVarSuccRule := by
  rfl

@[simp] private theorem lookup_shiftTermNamedRule :
    presentation.lookupRule? (ruleId "megalodon-term-shift-named") =
      some TermQuantifiedKernel.shiftNamedRule := by
  rfl

@[simp] private theorem lookup_shiftTermPrimRule :
    presentation.lookupRule? (ruleId "megalodon-env-shift-term-prim") =
      some shiftTermPrimRule := by
  rfl

@[simp] private theorem lookup_shiftTermAppRule :
    presentation.lookupRule? (ruleId "megalodon-term-shift-app") =
      some TermQuantifiedKernel.shiftAppRule := by
  rfl

@[simp] private theorem lookup_shiftTermLamRule :
    presentation.lookupRule? (ruleId "megalodon-env-shift-term-lam") =
      some shiftTermLamRule := by
  rfl

@[simp] private theorem lookup_shiftTermImpRule :
    presentation.lookupRule? (ruleId "megalodon-term-shift-imp") =
      some TermQuantifiedKernel.shiftImpRule := by
  rfl

@[simp] private theorem lookup_shiftTermAllRule :
    presentation.lookupRule? (ruleId "megalodon-term-shift-all") =
      some TermQuantifiedKernel.shiftAllRule := by
  rfl

@[simp] private theorem lookup_shiftTermTypeAppRule :
    presentation.lookupRule? (ruleId "megalodon-env-shift-term-type-app") =
      some shiftTermTypeAppRule := by
  rfl

@[simp] private theorem lookup_shiftTermTypeLamRule :
    presentation.lookupRule? (ruleId "megalodon-env-shift-term-type-lam") =
      some shiftTermTypeLamRule := by
  rfl

@[simp] private theorem lookup_shiftTermTypeAllRule :
    presentation.lookupRule? (ruleId "megalodon-env-shift-term-type-all") =
      some shiftTermTypeAllRule := by
  rfl

@[simp] private theorem lookup_substituteTermVarEqualRule :
    presentation.lookupRule? (ruleId "megalodon-term-subst-var-equal") =
      some TermQuantifiedKernel.substVarEqualRule := by
  rfl

@[simp] private theorem lookup_substituteTermVarBelowRule :
    presentation.lookupRule? (ruleId "megalodon-term-subst-var-below") =
      some TermQuantifiedKernel.substVarBelowRule := by
  rfl

@[simp] private theorem lookup_substituteTermVarAboveRule :
    presentation.lookupRule? (ruleId "megalodon-term-subst-var-above") =
      some TermQuantifiedKernel.substVarAboveRule := by
  rfl

@[simp] private theorem lookup_substituteTermNamedRule :
    presentation.lookupRule? (ruleId "megalodon-term-subst-named") =
      some TermQuantifiedKernel.substNamedRule := by
  rfl

@[simp] private theorem lookup_substituteTermPrimRule :
    presentation.lookupRule? (ruleId "megalodon-env-substitute-term-prim") =
      some substituteTermPrimRule := by
  rfl

@[simp] private theorem lookup_substituteTermAppRule :
    presentation.lookupRule? (ruleId "megalodon-term-subst-app") =
      some TermQuantifiedKernel.substAppRule := by
  rfl

@[simp] private theorem lookup_substituteTermLamRule :
    presentation.lookupRule? (ruleId "megalodon-env-substitute-term-lam") =
      some substituteTermLamRule := by
  rfl

@[simp] private theorem lookup_substituteTermImpRule :
    presentation.lookupRule? (ruleId "megalodon-term-subst-imp") =
      some TermQuantifiedKernel.substImpRule := by
  rfl

@[simp] private theorem lookup_substituteTermAllRule :
    presentation.lookupRule? (ruleId "megalodon-term-subst-all") =
      some TermQuantifiedKernel.substAllRule := by
  rfl

@[simp] private theorem lookup_substituteTermTypeAppRule :
    presentation.lookupRule?
        (ruleId "megalodon-env-substitute-term-type-app") =
      some substituteTermTypeAppRule := by
  rfl

@[simp] private theorem lookup_substituteTermTypeLamRule :
    presentation.lookupRule?
        (ruleId "megalodon-env-substitute-term-type-lam") =
      some substituteTermTypeLamRule := by
  rfl

@[simp] private theorem lookup_substituteTermTypeAllRule :
    presentation.lookupRule?
        (ruleId "megalodon-env-substitute-term-type-all") =
      some substituteTermTypeAllRule := by
  rfl

def coGSLTDefinition : ExtendedLanguageDef calculusLayer :=
  definition.toExtended

def coGSLTSource : coGSLTDefinition.authoredGSLT.Term :=
  coGSLTDefinition.authoredSource

@[simp] theorem coGSLT_source_elaborates :
    calculusLayer.elaborate definition.toLanguageDef coGSLTSource =
      some definition.toCalculus :=
  definition.toExtended_elaborate_authoredSource

theorem polymorphic_ruleLookupRefines :
    RuleLookupRefines PolymorphicKernel.validated validated := by
  apply RuleLookupRefines.of_rules_eq_append additionalRules
  rfl

/-! ## Proof-producing type-substitution compiler -/

private def node (id : String) (arguments : List Pattern)
    (children : List RawProof := []) : RawProof :=
  .node { ruleId := ruleId id, arguments } children

private abbrev ENat := TermQuantifiedKernel.encodeNat
private abbrev ETp := TermQuantifiedKernel.encodeTp
private abbrev ETm := TermQuantifiedKernel.encodeTm
private abbrev ETyCtx := TermQuantifiedKernel.encodeTypeContext
private abbrev EPfCtx := TermQuantifiedKernel.encodeProofContext
private abbrev ESig := TermQuantifiedKernel.encodeSignature

def addArticle : (left right : Nat) → RawProof
  | 0, right =>
      node "megalodon-term-add-zero" [ENat right]
  | left + 1, right =>
      node "megalodon-term-add-succ"
        [ENat left, ENat right, ENat (left + right)]
        [addArticle left right]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem addArticle_checked (left right : Nat) :
    checkRaw validated
      (addNat (ENat left) (ENat right) (ENat (left + right)))
      (addArticle left right) = true := by
  induction left with
  | zero =>
      simp only [addArticle, node, checkRaw, validated, instantiateRule?]
      rw [lookup_addZeroRule]
      simp [argumentsValidAt, argumentValidAt, instantiateSchemas?,
        instantiateSchema?, instantiateSchemasAt?, instantiateSchemaAt?,
        lookupArgumentAt?, RuleSchema.sideConditionsHold,
        TermQuantifiedKernel.addZeroRule, TermQuantifiedKernel.rule,
        TermQuantifiedKernel.ruleId, TermQuantifiedKernel.addNat,
        TermQuantifiedKernel.a, TermQuantifiedKernel.m,
        TermQuantifiedKernel.encodeNat,
        addNat, a, checkRawChildren]
  | succ left inductionHypothesis =>
      have sumStep : left + 1 + right = (left + right) + 1 := by omega
      simp only [addArticle, node, checkRaw, validated, instantiateRule?]
      rw [lookup_addSuccRule]
      simp [argumentsValidAt, argumentValidAt, instantiateSchemas?,
        instantiateSchema?, instantiateSchemasAt?, instantiateSchemaAt?,
        lookupArgumentAt?, RuleSchema.sideConditionsHold,
        TermQuantifiedKernel.addSuccRule, TermQuantifiedKernel.rule,
        TermQuantifiedKernel.ruleId, TermQuantifiedKernel.addNat,
        TermQuantifiedKernel.a, TermQuantifiedKernel.m,
        TermQuantifiedKernel.encodeNat,
        addNat, a, checkRawChildren,
        sumStep]
      simpa [validated, addNat, a] using inductionHypothesis

def lessArticle : (left right : Nat) → left < right → RawProof
  | 0, right + 1, _ =>
      node "megalodon-term-less-zero" [ENat right]
  | left + 1, right + 1, hypothesis =>
      node "megalodon-term-less-succ" [ENat left, ENat right]
        [lessArticle left right (Nat.succ_lt_succ_iff.mp hypothesis)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem lessArticle_checked (left right : Nat) (hypothesis : left < right) :
    checkRaw validated (lessThan (ENat left) (ENat right))
      (lessArticle left right hypothesis) = true := by
  induction left generalizing right with
  | zero =>
      cases right with
      | zero => omega
      | succ right =>
          simp only [lessArticle, node, checkRaw, validated, instantiateRule?]
          rw [lookup_lessZeroRule]
          simp [argumentsValidAt, argumentValidAt,
            instantiateSchemas?, instantiateSchema?,
            instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?,
            RuleSchema.sideConditionsHold,
            TermQuantifiedKernel.lessZeroRule, TermQuantifiedKernel.rule,
            TermQuantifiedKernel.ruleId, TermQuantifiedKernel.lessThan,
            TermQuantifiedKernel.encodeNat, TermQuantifiedKernel.a,
            TermQuantifiedKernel.m, lessThan, a, checkRawChildren]
  | succ left inductionHypothesis =>
      cases right with
      | zero => omega
      | succ right =>
          have smaller : left < right := Nat.succ_lt_succ_iff.mp hypothesis
          simp only [lessArticle, node, checkRaw, validated, instantiateRule?]
          rw [lookup_lessSuccRule]
          simp [argumentsValidAt, argumentValidAt,
            instantiateSchemas?, instantiateSchema?,
            instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?,
            RuleSchema.sideConditionsHold,
            TermQuantifiedKernel.lessSuccRule, TermQuantifiedKernel.rule,
            TermQuantifiedKernel.ruleId, TermQuantifiedKernel.lessThan,
            TermQuantifiedKernel.encodeNat, TermQuantifiedKernel.a,
            TermQuantifiedKernel.m, lessThan, a, checkRawChildren]
          simpa [validated, lessThan, a] using
            inductionHypothesis right smaller

def shiftedVariableIndex (amount cutoff index : Nat) : Nat :=
  if index < cutoff then index else index + amount

def compileTypeVariableShift (amount : Nat) :
    (cutoff index : Nat) → MathdataKernel.Tp × RawProof
  | 0, index =>
      (.var (index + amount),
        node "megalodon-env-shift-type-var-zero"
          [ENat amount, ENat index, ENat (index + amount)]
          [addArticle index amount])
  | cutoff + 1, 0 =>
      (.var 0,
        node "megalodon-env-shift-type-var-below"
          [ENat amount, ENat cutoff])
  | cutoff + 1, index + 1 =>
      let compiled := compileTypeVariableShift amount cutoff index
      (.var (shiftedVariableIndex amount cutoff index + 1),
        node "megalodon-env-shift-type-var-succ"
          [ENat amount, ENat cutoff, ENat index,
            ENat (shiftedVariableIndex amount cutoff index)]
          [compiled.2])

def compileTypeShift (amount cutoff : Nat) :
    (type : MathdataKernel.Tp) → MathdataKernel.Tp × RawProof
  | .var index => compileTypeVariableShift amount cutoff index
  | .prop =>
      (.prop,
        node "megalodon-env-shift-type-prop" [ENat amount, ENat cutoff])
  | .base index =>
      (.base index,
        node "megalodon-env-shift-type-base"
          [ENat amount, ENat cutoff, ENat index])
  | .arr domain codomain =>
      let domainCompiled := compileTypeShift amount cutoff domain
      let codomainCompiled := compileTypeShift amount cutoff codomain
      (.arr domainCompiled.1 codomainCompiled.1,
        node "megalodon-env-shift-type-arr"
          [ENat amount, ENat cutoff, ETp domain, ETp codomain,
            ETp domainCompiled.1, ETp codomainCompiled.1]
          [domainCompiled.2, codomainCompiled.2])
  | .all body =>
      let bodyCompiled := compileTypeShift amount (cutoff + 1) body
      (.all bodyCompiled.1,
        node "megalodon-env-shift-type-all"
          [ENat amount, ENat cutoff, ETp body, ETp bodyCompiled.1]
          [bodyCompiled.2])

theorem compileTypeVariableShift_result (amount cutoff index : Nat) :
    (compileTypeVariableShift amount cutoff index).1 =
      MathdataKernel.Tp.shift cutoff amount (.var index) := by
  induction cutoff generalizing index with
  | zero => simp [compileTypeVariableShift, MathdataKernel.Tp.shift]
  | succ cutoff inductionHypothesis =>
      cases index with
      | zero => simp [compileTypeVariableShift, MathdataKernel.Tp.shift]
      | succ index =>
          by_cases below : index < cutoff
          · simp [compileTypeVariableShift, MathdataKernel.Tp.shift,
              shiftedVariableIndex, below]
          · simp [compileTypeVariableShift, MathdataKernel.Tp.shift,
              shiftedVariableIndex, below]
            omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem compileTypeVariableShift_checked (amount cutoff index : Nat) :
    checkRaw validated
      (shiftType (ENat amount) (ENat cutoff) (ETp (.var index))
        (ETp (compileTypeVariableShift amount cutoff index).1))
      (compileTypeVariableShift amount cutoff index).2 = true := by
  induction cutoff generalizing index with
  | zero =>
      simp only [compileTypeVariableShift, node, checkRaw, validated]
      simp only [instantiateRule?]
      rw [lookup_shiftTypeVarZeroRule]
      simp [argumentsValidAt, argumentValidAt,
        instantiateSchemas?, instantiateSchema?,
        instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?,
        RuleSchema.sideConditionsHold,
        shiftTypeVarZeroRule, rule, ruleId, shiftType, addNat,
        checkRawChildren,
        TermQuantifiedKernel.encodeNat, TermQuantifiedKernel.encodeTp,
        TermQuantifiedKernel.a, a, m]
      simpa [validated, addNat, a] using addArticle_checked index amount
  | succ cutoff inductionHypothesis =>
      cases index with
      | zero =>
          simp only [compileTypeVariableShift, node, checkRaw, validated]
          simp only [instantiateRule?]
          rw [lookup_shiftTypeVarBelowRule]
          simp [argumentsValidAt, argumentValidAt,
            instantiateSchemas?, instantiateSchema?,
            instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?,
            RuleSchema.sideConditionsHold,
            shiftTypeVarBelowRule, rule, ruleId, shiftType,
            checkRawChildren, TermQuantifiedKernel.encodeNat,
            TermQuantifiedKernel.encodeTp, TermQuantifiedKernel.a, a, m]
      | succ index =>
          have endpoint :
              (compileTypeVariableShift amount cutoff index).1 =
                .var (shiftedVariableIndex amount cutoff index) := by
            rw [compileTypeVariableShift_result]
            by_cases below : index < cutoff <;>
              simp [MathdataKernel.Tp.shift, shiftedVariableIndex, below]
          simp only [compileTypeVariableShift, node, checkRaw, validated]
          simp only [instantiateRule?]
          rw [lookup_shiftTypeVarSuccRule]
          simp [argumentsValidAt, argumentValidAt,
            instantiateSchemas?, instantiateSchema?,
            instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?,
            RuleSchema.sideConditionsHold,
            shiftTypeVarSuccRule, rule, ruleId, shiftType,
            checkRawChildren,
            TermQuantifiedKernel.encodeNat, TermQuantifiedKernel.encodeTp,
            TermQuantifiedKernel.a, a, m]
          simpa [validated, shiftType, a, TermQuantifiedKernel.encodeTp,
            TermQuantifiedKernel.encodeNat, TermQuantifiedKernel.a,
            endpoint] using
            inductionHypothesis index

theorem compileTypeShift_result (amount cutoff : Nat)
    (type : MathdataKernel.Tp) :
    (compileTypeShift amount cutoff type).1 =
      MathdataKernel.Tp.shift cutoff amount type := by
  induction type generalizing cutoff with
  | var index => exact compileTypeVariableShift_result amount cutoff index
  | prop => rfl
  | base index => rfl
  | arr domain codomain domainHypothesis codomainHypothesis =>
      simp [compileTypeShift, MathdataKernel.Tp.shift,
        domainHypothesis, codomainHypothesis]
  | all body inductionHypothesis =>
      simp [compileTypeShift, MathdataKernel.Tp.shift, inductionHypothesis]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem compileTypeShift_checked (amount cutoff : Nat)
    (type : MathdataKernel.Tp) :
    checkRaw validated
      (shiftType (ENat amount) (ENat cutoff) (ETp type)
        (ETp (compileTypeShift amount cutoff type).1))
      (compileTypeShift amount cutoff type).2 = true := by
  induction type generalizing cutoff with
  | var index =>
      exact compileTypeVariableShift_checked amount cutoff index
  | prop =>
      simp only [compileTypeShift, node, checkRaw, validated, instantiateRule?]
      rw [lookup_shiftTypePropRule]
      simp [argumentsValidAt, argumentValidAt,
        instantiateSchemas?, instantiateSchema?,
        instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?,
        RuleSchema.sideConditionsHold,
        shiftTypePropRule, rule, ruleId, shiftType, checkRawChildren,
        TermQuantifiedKernel.encodeTp,
        TermQuantifiedKernel.a, a, m]
  | base index =>
      simp only [compileTypeShift, node, checkRaw, validated, instantiateRule?]
      rw [lookup_shiftTypeBaseRule]
      simp [argumentsValidAt, argumentValidAt,
        instantiateSchemas?, instantiateSchema?,
        instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?,
        RuleSchema.sideConditionsHold,
        shiftTypeBaseRule, rule, ruleId, shiftType, checkRawChildren,
        TermQuantifiedKernel.encodeTp,
        TermQuantifiedKernel.a, a, m]
  | arr domain codomain domainHypothesis codomainHypothesis =>
      simp only [compileTypeShift, node, checkRaw, validated, instantiateRule?]
      rw [lookup_shiftTypeArrRule]
      simp [argumentsValidAt, argumentValidAt,
        instantiateSchemas?, instantiateSchema?,
        instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?,
        RuleSchema.sideConditionsHold,
        shiftTypeArrRule, rule, ruleId, shiftType, checkRawChildren,
        TermQuantifiedKernel.encodeTp,
        TermQuantifiedKernel.a, a, m]
      exact ⟨domainHypothesis cutoff, codomainHypothesis cutoff⟩
  | all body inductionHypothesis =>
      simp only [compileTypeShift, node, checkRaw, validated, instantiateRule?]
      rw [lookup_shiftTypeAllRule]
      simp [argumentsValidAt, argumentValidAt,
        instantiateSchemas?, instantiateSchema?,
        instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?,
        RuleSchema.sideConditionsHold,
        shiftTypeAllRule, rule, ruleId, shiftType, checkRawChildren,
        TermQuantifiedKernel.encodeTp,
        TermQuantifiedKernel.a, a, m]
      exact inductionHypothesis (cutoff + 1)

def compileTypeSubstituteType (index : Nat)
    (replacement : MathdataKernel.Tp) :
    (body : MathdataKernel.Tp) → MathdataKernel.Tp × RawProof
  | .var varIndex =>
      if below : varIndex < index then
        (.var varIndex,
          node "megalodon-env-substitute-type-var-below"
            [ENat index, ETp replacement, ENat varIndex]
            [lessArticle varIndex index below])
      else if equal : varIndex = index then
        let shifted := compileTypeShift index 0 replacement
        (shifted.1,
          node "megalodon-env-substitute-type-var-equal"
            [ENat index, ETp replacement, ETp shifted.1]
            [shifted.2])
      else
        let predecessor := varIndex - 1
        have above : index < predecessor + 1 := by omega
        (.var predecessor,
          node "megalodon-env-substitute-type-var-above"
            [ENat index, ETp replacement, ENat predecessor]
            [lessArticle index (predecessor + 1) above])
  | .prop =>
      (.prop,
        node "megalodon-env-substitute-type-prop"
          [ENat index, ETp replacement])
  | .base base =>
      (.base base,
        node "megalodon-env-substitute-type-base"
          [ENat index, ETp replacement, ENat base])
  | .arr domain codomain =>
      let domainCompiled := compileTypeSubstituteType index replacement domain
      let codomainCompiled :=
        compileTypeSubstituteType index replacement codomain
      (.arr domainCompiled.1 codomainCompiled.1,
        node "megalodon-env-substitute-type-arr"
          [ENat index, ETp replacement, ETp domain, ETp codomain,
            ETp domainCompiled.1, ETp codomainCompiled.1]
          [domainCompiled.2, codomainCompiled.2])
  | .all body =>
      let bodyCompiled :=
        compileTypeSubstituteType (index + 1) replacement body
      (.all bodyCompiled.1,
        node "megalodon-env-substitute-type-all"
          [ENat index, ETp replacement, ETp body, ETp bodyCompiled.1]
          [bodyCompiled.2])

theorem compileTypeSubstituteType_result (index : Nat)
    (replacement body : MathdataKernel.Tp) :
    (compileTypeSubstituteType index replacement body).1 =
      MathdataKernel.Tp.instantiateAt index replacement body := by
  induction body generalizing index with
  | var varIndex =>
      by_cases below : varIndex < index
      · simp [compileTypeSubstituteType, MathdataKernel.Tp.instantiateAt,
          below]
      · by_cases equal : varIndex = index
        · simp [compileTypeSubstituteType, MathdataKernel.Tp.instantiateAt,
            equal, compileTypeShift_result]
        · simp [compileTypeSubstituteType, MathdataKernel.Tp.instantiateAt,
            below, equal]
  | prop => rfl
  | base base => rfl
  | arr domain codomain domainHypothesis codomainHypothesis =>
      simp [compileTypeSubstituteType, MathdataKernel.Tp.instantiateAt,
        domainHypothesis, codomainHypothesis]
  | all body inductionHypothesis =>
      simp [compileTypeSubstituteType, MathdataKernel.Tp.instantiateAt,
        inductionHypothesis]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem compileTypeSubstituteType_checked (index : Nat)
    (replacement body : MathdataKernel.Tp) :
    checkRaw validated
      (substituteType (ENat index) (ETp replacement) (ETp body)
        (ETp (compileTypeSubstituteType index replacement body).1))
      (compileTypeSubstituteType index replacement body).2 = true := by
  induction body generalizing index with
  | var varIndex =>
      by_cases below : varIndex < index
      · simp only [compileTypeSubstituteType, dif_pos below, node,
          checkRaw, validated, instantiateRule?]
        rw [lookup_substituteTypeVarBelowRule]
        simp [argumentsValidAt, argumentValidAt,
          instantiateSchemas?, instantiateSchema?,
          instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?,
          RuleSchema.sideConditionsHold,
          substituteTypeVarBelowRule, rule, ruleId, substituteType, lessThan,
          checkRawChildren, TermQuantifiedKernel.encodeTp,
          TermQuantifiedKernel.a, a, m]
        simpa [validated, lessThan, a] using
          lessArticle_checked varIndex index below
      · by_cases equal : varIndex = index
        · simp only [compileTypeSubstituteType, dif_neg below, dif_pos equal,
            node, checkRaw, validated, instantiateRule?]
          rw [lookup_substituteTypeVarEqualRule]
          simp [argumentsValidAt, argumentValidAt,
            instantiateSchemas?, instantiateSchema?,
            instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?,
            RuleSchema.sideConditionsHold,
            substituteTypeVarEqualRule, rule, ruleId, substituteType,
            shiftType, checkRawChildren, TermQuantifiedKernel.encodeTp,
            TermQuantifiedKernel.a, a, m]
          subst varIndex
          simpa [validated, shiftType, a, TermQuantifiedKernel.encodeNat,
            TermQuantifiedKernel.a] using
            compileTypeShift_checked index 0 replacement
        · have above : index < varIndex := by omega
          have predecessor : varIndex = varIndex - 1 + 1 := by omega
          simp only [compileTypeSubstituteType, dif_neg below, dif_neg equal,
            node, checkRaw, validated, instantiateRule?]
          rw [lookup_substituteTypeVarAboveRule]
          simp [argumentsValidAt, argumentValidAt,
            instantiateSchemas?, instantiateSchema?,
            instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?,
            RuleSchema.sideConditionsHold,
            substituteTypeVarAboveRule, rule, ruleId, substituteType,
            lessThan, checkRawChildren, TermQuantifiedKernel.encodeTp,
            TermQuantifiedKernel.a, a, m]
          constructor
          · rw [predecessor]
            rfl
          · simpa [validated, lessThan, a, TermQuantifiedKernel.encodeNat,
              TermQuantifiedKernel.a] using
              lessArticle_checked index (varIndex - 1 + 1) (by omega)
  | prop =>
      simp only [compileTypeSubstituteType, node, checkRaw, validated,
        instantiateRule?]
      rw [lookup_substituteTypePropRule]
      simp [argumentsValidAt, argumentValidAt,
        instantiateSchemas?, instantiateSchema?,
        instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?,
        RuleSchema.sideConditionsHold,
        substituteTypePropRule, rule, ruleId, substituteType,
        checkRawChildren, TermQuantifiedKernel.encodeTp,
        TermQuantifiedKernel.a, a, m]
  | base base =>
      simp only [compileTypeSubstituteType, node, checkRaw, validated,
        instantiateRule?]
      rw [lookup_substituteTypeBaseRule]
      simp [argumentsValidAt, argumentValidAt,
        instantiateSchemas?, instantiateSchema?,
        instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?,
        RuleSchema.sideConditionsHold,
        substituteTypeBaseRule, rule, ruleId, substituteType,
        checkRawChildren, TermQuantifiedKernel.encodeTp,
        TermQuantifiedKernel.a, a, m]
  | arr domain codomain domainHypothesis codomainHypothesis =>
      simp only [compileTypeSubstituteType, node, checkRaw, validated,
        instantiateRule?]
      rw [lookup_substituteTypeArrRule]
      simp [argumentsValidAt, argumentValidAt,
        instantiateSchemas?, instantiateSchema?,
        instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?,
        RuleSchema.sideConditionsHold,
        substituteTypeArrRule, rule, ruleId, substituteType,
        checkRawChildren, TermQuantifiedKernel.encodeTp,
        TermQuantifiedKernel.a, a, m]
      exact ⟨domainHypothesis index, codomainHypothesis index⟩
  | all body inductionHypothesis =>
      simp only [compileTypeSubstituteType, node, checkRaw, validated,
        instantiateRule?]
      rw [lookup_substituteTypeAllRule]
      simp [argumentsValidAt, argumentValidAt,
        instantiateSchemas?, instantiateSchema?,
        instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?,
        RuleSchema.sideConditionsHold,
        substituteTypeAllRule, rule, ruleId, substituteType,
        checkRawChildren, TermQuantifiedKernel.encodeTp,
        TermQuantifiedKernel.a, a, m]
      exact inductionHypothesis (index + 1)

def compileTypeSubstituteTerm (index : Nat)
    (replacement : MathdataKernel.Tp) :
    (body : MathdataKernel.Tm) → MathdataKernel.Tm × RawProof
  | .db varIndex =>
      (.db varIndex,
        node "megalodon-env-substitute-type-term-var"
          [ENat index, ETp replacement, ENat varIndex])
  | .named name =>
      (.named name,
        node "megalodon-env-substitute-type-term-named"
          [ENat index, ETp replacement, a name])
  | .prim primitive =>
      (.prim primitive,
        node "megalodon-env-substitute-type-term-prim"
          [ENat index, ETp replacement, ENat primitive])
  | .app function argument =>
      let functionCompiled :=
        compileTypeSubstituteTerm index replacement function
      let argumentCompiled :=
        compileTypeSubstituteTerm index replacement argument
      (.app functionCompiled.1 argumentCompiled.1,
        node "megalodon-env-substitute-type-term-app"
          [ENat index, ETp replacement, ETm function, ETm argument,
            ETm functionCompiled.1, ETm argumentCompiled.1]
          [functionCompiled.2, argumentCompiled.2])
  | .lam type body =>
      let typeCompiled := compileTypeSubstituteType index replacement type
      let bodyCompiled := compileTypeSubstituteTerm index replacement body
      (.lam typeCompiled.1 bodyCompiled.1,
        node "megalodon-env-substitute-type-term-lam"
          [ENat index, ETp replacement, ETp type, ETm body,
            ETp typeCompiled.1, ETm bodyCompiled.1]
          [typeCompiled.2, bodyCompiled.2])
  | .imp domain codomain =>
      let domainCompiled :=
        compileTypeSubstituteTerm index replacement domain
      let codomainCompiled :=
        compileTypeSubstituteTerm index replacement codomain
      (.imp domainCompiled.1 codomainCompiled.1,
        node "megalodon-env-substitute-type-term-imp"
          [ENat index, ETp replacement, ETm domain, ETm codomain,
            ETm domainCompiled.1, ETm codomainCompiled.1]
          [domainCompiled.2, codomainCompiled.2])
  | .all type body =>
      let typeCompiled := compileTypeSubstituteType index replacement type
      let bodyCompiled := compileTypeSubstituteTerm index replacement body
      (.all typeCompiled.1 bodyCompiled.1,
        node "megalodon-env-substitute-type-term-all"
          [ENat index, ETp replacement, ETp type, ETm body,
            ETp typeCompiled.1, ETm bodyCompiled.1]
          [typeCompiled.2, bodyCompiled.2])
  | .typeApp function type =>
      let functionCompiled :=
        compileTypeSubstituteTerm index replacement function
      let typeCompiled := compileTypeSubstituteType index replacement type
      (.typeApp functionCompiled.1 typeCompiled.1,
        node "megalodon-env-substitute-type-term-type-app"
          [ENat index, ETp replacement, ETm function, ETp type,
            ETm functionCompiled.1, ETp typeCompiled.1]
          [functionCompiled.2, typeCompiled.2])
  | .typeLam body =>
      let bodyCompiled :=
        compileTypeSubstituteTerm (index + 1) replacement body
      (.typeLam bodyCompiled.1,
        node "megalodon-env-substitute-type-term-type-lam"
          [ENat index, ETp replacement, ETm body, ETm bodyCompiled.1]
          [bodyCompiled.2])
  | .typeAll body =>
      let bodyCompiled :=
        compileTypeSubstituteTerm (index + 1) replacement body
      (.typeAll bodyCompiled.1,
        node "megalodon-env-substitute-type-term-type-all"
          [ENat index, ETp replacement, ETm body, ETm bodyCompiled.1]
          [bodyCompiled.2])

theorem compileTypeSubstituteTerm_result (index : Nat)
    (replacement : MathdataKernel.Tp) (body : MathdataKernel.Tm) :
    (compileTypeSubstituteTerm index replacement body).1 =
      MathdataKernel.Tm.typeInstantiateAt index replacement body := by
  induction body generalizing index with
  | db varIndex => rfl
  | named name => rfl
  | prim primitive => rfl
  | app function argument functionHypothesis argumentHypothesis =>
      simp [compileTypeSubstituteTerm,
        MathdataKernel.Tm.typeInstantiateAt,
        functionHypothesis, argumentHypothesis]
  | lam type body bodyHypothesis =>
      simp [compileTypeSubstituteTerm,
        MathdataKernel.Tm.typeInstantiateAt,
        compileTypeSubstituteType_result, bodyHypothesis]
  | imp domain codomain domainHypothesis codomainHypothesis =>
      simp [compileTypeSubstituteTerm,
        MathdataKernel.Tm.typeInstantiateAt,
        domainHypothesis, codomainHypothesis]
  | all type body bodyHypothesis =>
      simp [compileTypeSubstituteTerm,
        MathdataKernel.Tm.typeInstantiateAt,
        compileTypeSubstituteType_result, bodyHypothesis]
  | typeApp function type functionHypothesis =>
      simp [compileTypeSubstituteTerm,
        MathdataKernel.Tm.typeInstantiateAt,
        compileTypeSubstituteType_result, functionHypothesis]
  | typeLam body bodyHypothesis =>
      simp [compileTypeSubstituteTerm,
        MathdataKernel.Tm.typeInstantiateAt, bodyHypothesis]
  | typeAll body bodyHypothesis =>
      simp [compileTypeSubstituteTerm,
        MathdataKernel.Tm.typeInstantiateAt, bodyHypothesis]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem compileTypeSubstituteTerm_checked (index : Nat)
    (replacement : MathdataKernel.Tp) (body : MathdataKernel.Tm) :
    checkRaw validated
      (substituteTypeInTerm (ENat index) (ETp replacement) (ETm body)
        (ETm (compileTypeSubstituteTerm index replacement body).1))
      (compileTypeSubstituteTerm index replacement body).2 = true := by
  induction body generalizing index with
  | db varIndex =>
      simp only [compileTypeSubstituteTerm, node, checkRaw, validated,
        instantiateRule?]
      rw [lookup_substituteTypeTermVarRule]
      simp [argumentsValidAt, argumentValidAt,
        instantiateSchemas?, instantiateSchema?,
        instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?,
        RuleSchema.sideConditionsHold,
        substituteTypeTermVarRule, rule, ruleId, substituteTypeInTerm,
        checkRawChildren, TermQuantifiedKernel.encodeTm,
        TermQuantifiedKernel.a, a, m]
  | named name =>
      simp only [compileTypeSubstituteTerm, node, checkRaw, validated,
        instantiateRule?]
      rw [lookup_substituteTypeTermNamedRule]
      simp [argumentsValidAt, argumentValidAt,
        instantiateSchemas?, instantiateSchema?,
        instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?,
        RuleSchema.sideConditionsHold,
        substituteTypeTermNamedRule, rule, ruleId, substituteTypeInTerm,
        checkRawChildren, TermQuantifiedKernel.encodeTm,
        TermQuantifiedKernel.a, a, m,
        Pattern.isGroundAt, Pattern.isGroundListAt,
        Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList]
  | prim primitive =>
      simp only [compileTypeSubstituteTerm, node, checkRaw, validated,
        instantiateRule?]
      rw [lookup_substituteTypeTermPrimRule]
      simp [argumentsValidAt, argumentValidAt,
        instantiateSchemas?, instantiateSchema?,
        instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?,
        RuleSchema.sideConditionsHold,
        substituteTypeTermPrimRule, rule, ruleId, substituteTypeInTerm,
        checkRawChildren, TermQuantifiedKernel.encodeTm,
        TermQuantifiedKernel.a, a, m]
  | app function argument functionHypothesis argumentHypothesis =>
      simp only [compileTypeSubstituteTerm, node, checkRaw, validated,
        instantiateRule?]
      rw [lookup_substituteTypeTermAppRule]
      simp [argumentsValidAt, argumentValidAt,
        instantiateSchemas?, instantiateSchema?,
        instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?,
        RuleSchema.sideConditionsHold,
        substituteTypeTermAppRule, rule, ruleId, substituteTypeInTerm,
        checkRawChildren, TermQuantifiedKernel.encodeTm,
        TermQuantifiedKernel.a, a, m]
      exact ⟨functionHypothesis index, argumentHypothesis index⟩
  | lam type body bodyHypothesis =>
      simp only [compileTypeSubstituteTerm, node, checkRaw, validated,
        instantiateRule?]
      rw [lookup_substituteTypeTermLamRule]
      simp [argumentsValidAt, argumentValidAt,
        instantiateSchemas?, instantiateSchema?,
        instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?,
        RuleSchema.sideConditionsHold,
        substituteTypeTermLamRule, rule, ruleId, substituteTypeInTerm,
        substituteType, checkRawChildren, TermQuantifiedKernel.encodeTm,
        TermQuantifiedKernel.a, a, m]
      exact ⟨compileTypeSubstituteType_checked index replacement type,
        bodyHypothesis index⟩
  | imp domain codomain domainHypothesis codomainHypothesis =>
      simp only [compileTypeSubstituteTerm, node, checkRaw, validated,
        instantiateRule?]
      rw [lookup_substituteTypeTermImpRule]
      simp [argumentsValidAt, argumentValidAt,
        instantiateSchemas?, instantiateSchema?,
        instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?,
        RuleSchema.sideConditionsHold,
        substituteTypeTermImpRule, rule, ruleId, substituteTypeInTerm,
        checkRawChildren, TermQuantifiedKernel.encodeTm,
        TermQuantifiedKernel.a, a, m]
      exact ⟨domainHypothesis index, codomainHypothesis index⟩
  | all type body bodyHypothesis =>
      simp only [compileTypeSubstituteTerm, node, checkRaw, validated,
        instantiateRule?]
      rw [lookup_substituteTypeTermAllRule]
      simp [argumentsValidAt, argumentValidAt,
        instantiateSchemas?, instantiateSchema?,
        instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?,
        RuleSchema.sideConditionsHold,
        substituteTypeTermAllRule, rule, ruleId, substituteTypeInTerm,
        substituteType, checkRawChildren, TermQuantifiedKernel.encodeTm,
        TermQuantifiedKernel.a, a, m]
      exact ⟨compileTypeSubstituteType_checked index replacement type,
        bodyHypothesis index⟩
  | typeApp function type functionHypothesis =>
      simp only [compileTypeSubstituteTerm, node, checkRaw, validated,
        instantiateRule?]
      rw [lookup_substituteTypeTermTypeAppRule]
      simp [argumentsValidAt, argumentValidAt,
        instantiateSchemas?, instantiateSchema?,
        instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?,
        RuleSchema.sideConditionsHold,
        substituteTypeTermTypeAppRule, rule, ruleId, substituteTypeInTerm,
        substituteType, checkRawChildren, TermQuantifiedKernel.encodeTm,
        TermQuantifiedKernel.a, a, m]
      exact ⟨functionHypothesis index,
        compileTypeSubstituteType_checked index replacement type⟩
  | typeLam body bodyHypothesis =>
      simp only [compileTypeSubstituteTerm, node, checkRaw, validated,
        instantiateRule?]
      rw [lookup_substituteTypeTermTypeLamRule]
      simp [argumentsValidAt, argumentValidAt,
        instantiateSchemas?, instantiateSchema?,
        instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?,
        RuleSchema.sideConditionsHold,
        substituteTypeTermTypeLamRule, rule, ruleId, substituteTypeInTerm,
        checkRawChildren, TermQuantifiedKernel.encodeTm,
        TermQuantifiedKernel.a, a, m]
      exact bodyHypothesis (index + 1)
  | typeAll body bodyHypothesis =>
      simp only [compileTypeSubstituteTerm, node, checkRaw, validated,
        instantiateRule?]
      rw [lookup_substituteTypeTermTypeAllRule]
      simp [argumentsValidAt, argumentValidAt,
        instantiateSchemas?, instantiateSchema?,
        instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?,
        RuleSchema.sideConditionsHold,
        substituteTypeTermTypeAllRule, rule, ruleId, substituteTypeInTerm,
        checkRawChildren, TermQuantifiedKernel.encodeTm,
        TermQuantifiedKernel.a, a, m]
      exact bodyHypothesis (index + 1)

def compileTermVariableShift (amount : Nat) :
    (cutoff index : Nat) → MathdataKernel.Tm × RawProof
  | 0, index =>
      (.db (index + amount),
        node "megalodon-term-shift-var-zero"
          [ENat amount, ENat index, ENat (index + amount)]
          [addArticle index amount])
  | cutoff + 1, 0 =>
      (.db 0,
        node "megalodon-term-shift-var-below"
          [ENat amount, ENat cutoff])
  | cutoff + 1, index + 1 =>
      let compiled := compileTermVariableShift amount cutoff index
      (.db (shiftedVariableIndex amount cutoff index + 1),
        node "megalodon-term-shift-var-succ"
          [ENat amount, ENat cutoff, ENat index,
            ENat (shiftedVariableIndex amount cutoff index)]
          [compiled.2])

def compileTermShift (amount cutoff : Nat) :
    (term : MathdataKernel.Tm) → MathdataKernel.Tm × RawProof
  | .db index => compileTermVariableShift amount cutoff index
  | .named name =>
      (.named name,
        node "megalodon-term-shift-named"
          [ENat amount, ENat cutoff, a name])
  | .prim primitive =>
      (.prim primitive,
        node "megalodon-env-shift-term-prim"
          [ENat amount, ENat cutoff, ENat primitive])
  | .app function argument =>
      let functionCompiled := compileTermShift amount cutoff function
      let argumentCompiled := compileTermShift amount cutoff argument
      (.app functionCompiled.1 argumentCompiled.1,
        node "megalodon-term-shift-app"
          [ENat amount, ENat cutoff, ETm function, ETm argument,
            ETm functionCompiled.1, ETm argumentCompiled.1]
          [functionCompiled.2, argumentCompiled.2])
  | .lam type body =>
      let bodyCompiled := compileTermShift amount (cutoff + 1) body
      (.lam type bodyCompiled.1,
        node "megalodon-env-shift-term-lam"
          [ENat amount, ENat cutoff, ETp type, ETm body,
            ETm bodyCompiled.1]
          [bodyCompiled.2])
  | .imp domain codomain =>
      let domainCompiled := compileTermShift amount cutoff domain
      let codomainCompiled := compileTermShift amount cutoff codomain
      (.imp domainCompiled.1 codomainCompiled.1,
        node "megalodon-term-shift-imp"
          [ENat amount, ENat cutoff, ETm domain, ETm codomain,
            ETm domainCompiled.1, ETm codomainCompiled.1]
          [domainCompiled.2, codomainCompiled.2])
  | .all type body =>
      let bodyCompiled := compileTermShift amount (cutoff + 1) body
      (.all type bodyCompiled.1,
        node "megalodon-term-shift-all"
          [ENat amount, ENat cutoff, ETp type, ETm body,
            ETm bodyCompiled.1]
          [bodyCompiled.2])
  | .typeApp function type =>
      let functionCompiled := compileTermShift amount cutoff function
      (.typeApp functionCompiled.1 type,
        node "megalodon-env-shift-term-type-app"
          [ENat amount, ENat cutoff, ETm function, ETp type,
            ETm functionCompiled.1]
          [functionCompiled.2])
  | .typeLam body =>
      let bodyCompiled := compileTermShift amount cutoff body
      (.typeLam bodyCompiled.1,
        node "megalodon-env-shift-term-type-lam"
          [ENat amount, ENat cutoff, ETm body, ETm bodyCompiled.1]
          [bodyCompiled.2])
  | .typeAll body =>
      let bodyCompiled := compileTermShift amount cutoff body
      (.typeAll bodyCompiled.1,
        node "megalodon-env-shift-term-type-all"
          [ENat amount, ENat cutoff, ETm body, ETm bodyCompiled.1]
          [bodyCompiled.2])

/-- The named-term compiler emits one explicit shift article.  Exposing this
equation lets downstream runtime refinements inspect the article without
depending on the private construction helper. -/
@[simp] theorem compileTermShift_named_article
    (amount cutoff : Nat) (name : String) :
    (compileTermShift amount cutoff (.named name)).2 =
      .node
        { ruleId := ⟨"megalodon-term-shift-named"⟩
          arguments :=
            [ TermQuantifiedKernel.encodeNat amount,
              TermQuantifiedKernel.encodeNat cutoff,
              .apply name [] ] }
        [] := by
  rfl

theorem compileTermVariableShift_result (amount cutoff index : Nat) :
    (compileTermVariableShift amount cutoff index).1 =
      MathdataKernel.Tm.shift cutoff amount (.db index) := by
  induction cutoff generalizing index with
  | zero => simp [compileTermVariableShift, MathdataKernel.Tm.shift]
  | succ cutoff inductionHypothesis =>
      cases index with
      | zero => simp [compileTermVariableShift, MathdataKernel.Tm.shift]
      | succ index =>
          by_cases below : index < cutoff
          · simp [compileTermVariableShift, MathdataKernel.Tm.shift,
              shiftedVariableIndex, below]
          · simp [compileTermVariableShift, MathdataKernel.Tm.shift,
              shiftedVariableIndex, below]
            omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem compileTermVariableShift_checked (amount cutoff index : Nat) :
    checkRaw validated
      (TermQuantifiedKernel.shiftTerm
        (ENat amount) (ENat cutoff) (ETm (.db index))
        (ETm (compileTermVariableShift amount cutoff index).1))
      (compileTermVariableShift amount cutoff index).2 = true := by
  induction cutoff generalizing index with
  | zero =>
      simp only [compileTermVariableShift, node, checkRaw, validated,
        instantiateRule?]
      rw [lookup_shiftTermVarZeroRule]
      simp [argumentsValidAt, argumentValidAt,
        instantiateSchemas?, instantiateSchema?,
        instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?,
        RuleSchema.sideConditionsHold,
        TermQuantifiedKernel.shiftVarAtZeroRule,
        TermQuantifiedKernel.rule, TermQuantifiedKernel.ruleId,
        TermQuantifiedKernel.shiftTerm, TermQuantifiedKernel.addNat,
        checkRawChildren, TermQuantifiedKernel.encodeNat,
        TermQuantifiedKernel.encodeTm, TermQuantifiedKernel.a,
        TermQuantifiedKernel.m]
      simpa [validated, addNat, a, TermQuantifiedKernel.addNat,
        TermQuantifiedKernel.a] using addArticle_checked index amount
  | succ cutoff inductionHypothesis =>
      cases index with
      | zero =>
          simp only [compileTermVariableShift, node, checkRaw, validated,
            instantiateRule?]
          rw [lookup_shiftTermVarBelowRule]
          simp [argumentsValidAt, argumentValidAt,
            instantiateSchemas?, instantiateSchema?,
            instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?,
            RuleSchema.sideConditionsHold,
            TermQuantifiedKernel.shiftVarBelowRule,
            TermQuantifiedKernel.rule, TermQuantifiedKernel.ruleId,
            TermQuantifiedKernel.shiftTerm, checkRawChildren,
            TermQuantifiedKernel.encodeNat, TermQuantifiedKernel.encodeTm,
            TermQuantifiedKernel.a, TermQuantifiedKernel.m]
      | succ index =>
          have endpoint :
              (compileTermVariableShift amount cutoff index).1 =
                .db (shiftedVariableIndex amount cutoff index) := by
            rw [compileTermVariableShift_result]
            by_cases below : index < cutoff <;>
              simp [MathdataKernel.Tm.shift, shiftedVariableIndex, below]
          simp only [compileTermVariableShift, node, checkRaw, validated,
            instantiateRule?]
          rw [lookup_shiftTermVarSuccRule]
          simp [argumentsValidAt, argumentValidAt,
            instantiateSchemas?, instantiateSchema?,
            instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?,
            RuleSchema.sideConditionsHold,
            TermQuantifiedKernel.shiftVarSuccRule,
            TermQuantifiedKernel.rule, TermQuantifiedKernel.ruleId,
            TermQuantifiedKernel.shiftTerm, checkRawChildren,
            TermQuantifiedKernel.encodeNat, TermQuantifiedKernel.encodeTm,
            TermQuantifiedKernel.a, TermQuantifiedKernel.m]
          simpa [validated, TermQuantifiedKernel.shiftTerm,
            TermQuantifiedKernel.a, TermQuantifiedKernel.encodeTm,
            TermQuantifiedKernel.encodeNat, endpoint] using
            inductionHypothesis index

theorem compileTermShift_result (amount cutoff : Nat)
    (term : MathdataKernel.Tm) :
    (compileTermShift amount cutoff term).1 =
      MathdataKernel.Tm.shift cutoff amount term := by
  induction term generalizing cutoff with
  | db index => exact compileTermVariableShift_result amount cutoff index
  | named name => rfl
  | prim primitive => rfl
  | app function argument functionHypothesis argumentHypothesis =>
      simp [compileTermShift, MathdataKernel.Tm.shift,
        functionHypothesis, argumentHypothesis]
  | lam type body bodyHypothesis =>
      simp [compileTermShift, MathdataKernel.Tm.shift, bodyHypothesis]
  | imp domain codomain domainHypothesis codomainHypothesis =>
      simp [compileTermShift, MathdataKernel.Tm.shift,
        domainHypothesis, codomainHypothesis]
  | all type body bodyHypothesis =>
      simp [compileTermShift, MathdataKernel.Tm.shift, bodyHypothesis]
  | typeApp function type functionHypothesis =>
      simp [compileTermShift, MathdataKernel.Tm.shift, functionHypothesis]
  | typeLam body bodyHypothesis =>
      simp [compileTermShift, MathdataKernel.Tm.shift, bodyHypothesis]
  | typeAll body bodyHypothesis =>
      simp [compileTermShift, MathdataKernel.Tm.shift, bodyHypothesis]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem compileTermShift_checked (amount cutoff : Nat)
    (term : MathdataKernel.Tm) :
    checkRaw validated
      (TermQuantifiedKernel.shiftTerm
        (ENat amount) (ENat cutoff) (ETm term)
        (ETm (compileTermShift amount cutoff term).1))
      (compileTermShift amount cutoff term).2 = true := by
  induction term generalizing cutoff with
  | db index =>
      exact compileTermVariableShift_checked amount cutoff index
  | named name =>
      simp only [compileTermShift, node, checkRaw, validated, instantiateRule?]
      rw [lookup_shiftTermNamedRule]
      simp [argumentsValidAt, argumentValidAt,
        instantiateSchemas?, instantiateSchema?,
        instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?,
        RuleSchema.sideConditionsHold,
        TermQuantifiedKernel.shiftNamedRule,
        TermQuantifiedKernel.rule, TermQuantifiedKernel.ruleId,
        TermQuantifiedKernel.shiftTerm, checkRawChildren,
        TermQuantifiedKernel.encodeTm, TermQuantifiedKernel.a,
        TermQuantifiedKernel.m, a,
        Pattern.isGroundAt, Pattern.isGroundListAt,
        Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList]
  | prim primitive =>
      simp only [compileTermShift, node, checkRaw, validated, instantiateRule?]
      rw [lookup_shiftTermPrimRule]
      simp [argumentsValidAt, argumentValidAt,
        instantiateSchemas?, instantiateSchema?,
        instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?,
        RuleSchema.sideConditionsHold,
        shiftTermPrimRule, rule, ruleId, checkRawChildren,
        TermQuantifiedKernel.shiftTerm, TermQuantifiedKernel.encodeTm,
        TermQuantifiedKernel.a, a, m]
  | app function argument functionHypothesis argumentHypothesis =>
      simp only [compileTermShift, node, checkRaw, validated, instantiateRule?]
      rw [lookup_shiftTermAppRule]
      simp [argumentsValidAt, argumentValidAt,
        instantiateSchemas?, instantiateSchema?,
        instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?,
        RuleSchema.sideConditionsHold,
        TermQuantifiedKernel.shiftAppRule,
        TermQuantifiedKernel.rule, TermQuantifiedKernel.ruleId,
        TermQuantifiedKernel.shiftTerm, checkRawChildren,
        TermQuantifiedKernel.encodeTm, TermQuantifiedKernel.a,
        TermQuantifiedKernel.m]
      exact ⟨functionHypothesis cutoff, argumentHypothesis cutoff⟩
  | lam type body bodyHypothesis =>
      simp only [compileTermShift, node, checkRaw, validated, instantiateRule?]
      rw [lookup_shiftTermLamRule]
      simp [argumentsValidAt, argumentValidAt,
        instantiateSchemas?, instantiateSchema?,
        instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?,
        RuleSchema.sideConditionsHold,
        shiftTermLamRule, rule, ruleId, checkRawChildren,
        TermQuantifiedKernel.shiftTerm, TermQuantifiedKernel.encodeTm,
        TermQuantifiedKernel.a, a, m]
      exact bodyHypothesis (cutoff + 1)
  | imp domain codomain domainHypothesis codomainHypothesis =>
      simp only [compileTermShift, node, checkRaw, validated, instantiateRule?]
      rw [lookup_shiftTermImpRule]
      simp [argumentsValidAt, argumentValidAt,
        instantiateSchemas?, instantiateSchema?,
        instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?,
        RuleSchema.sideConditionsHold,
        TermQuantifiedKernel.shiftImpRule,
        TermQuantifiedKernel.rule, TermQuantifiedKernel.ruleId,
        TermQuantifiedKernel.shiftTerm, checkRawChildren,
        TermQuantifiedKernel.encodeTm, TermQuantifiedKernel.a,
        TermQuantifiedKernel.m]
      exact ⟨domainHypothesis cutoff, codomainHypothesis cutoff⟩
  | all type body bodyHypothesis =>
      simp only [compileTermShift, node, checkRaw, validated, instantiateRule?]
      rw [lookup_shiftTermAllRule]
      simp [argumentsValidAt, argumentValidAt,
        instantiateSchemas?, instantiateSchema?,
        instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?,
        RuleSchema.sideConditionsHold,
        TermQuantifiedKernel.shiftAllRule,
        TermQuantifiedKernel.rule, TermQuantifiedKernel.ruleId,
        TermQuantifiedKernel.shiftTerm, checkRawChildren,
        TermQuantifiedKernel.encodeTm, TermQuantifiedKernel.a,
        TermQuantifiedKernel.m]
      exact bodyHypothesis (cutoff + 1)
  | typeApp function type functionHypothesis =>
      simp only [compileTermShift, node, checkRaw, validated, instantiateRule?]
      rw [lookup_shiftTermTypeAppRule]
      simp [argumentsValidAt, argumentValidAt,
        instantiateSchemas?, instantiateSchema?,
        instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?,
        RuleSchema.sideConditionsHold,
        shiftTermTypeAppRule, rule, ruleId, checkRawChildren,
        TermQuantifiedKernel.shiftTerm, TermQuantifiedKernel.encodeTm,
        TermQuantifiedKernel.a, a, m]
      exact functionHypothesis cutoff
  | typeLam body bodyHypothesis =>
      simp only [compileTermShift, node, checkRaw, validated, instantiateRule?]
      rw [lookup_shiftTermTypeLamRule]
      simp [argumentsValidAt, argumentValidAt,
        instantiateSchemas?, instantiateSchema?,
        instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?,
        RuleSchema.sideConditionsHold,
        shiftTermTypeLamRule, rule, ruleId, checkRawChildren,
        TermQuantifiedKernel.shiftTerm, TermQuantifiedKernel.encodeTm,
        TermQuantifiedKernel.a, a, m]
      exact bodyHypothesis cutoff
  | typeAll body bodyHypothesis =>
      simp only [compileTermShift, node, checkRaw, validated, instantiateRule?]
      rw [lookup_shiftTermTypeAllRule]
      simp [argumentsValidAt, argumentValidAt,
        instantiateSchemas?, instantiateSchema?,
        instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?,
        RuleSchema.sideConditionsHold,
        shiftTermTypeAllRule, rule, ruleId, checkRawChildren,
        TermQuantifiedKernel.shiftTerm, TermQuantifiedKernel.encodeTm,
        TermQuantifiedKernel.a, a, m]
      exact bodyHypothesis cutoff

def compileTermSubstitute (index : Nat) (replacement : MathdataKernel.Tm) :
    (body : MathdataKernel.Tm) → MathdataKernel.Tm × RawProof
  | .db varIndex =>
      if below : varIndex < index then
        (.db varIndex,
          node "megalodon-term-subst-var-below"
            [ENat index, ETm replacement, ENat varIndex]
            [lessArticle varIndex index below])
      else if equal : varIndex = index then
        let shifted := compileTermShift index 0 replacement
        (shifted.1,
          node "megalodon-term-subst-var-equal"
            [ENat index, ETm replacement, ETm shifted.1]
            [shifted.2])
      else
        let predecessor := varIndex - 1
        have above : index < predecessor + 1 := by omega
        (.db predecessor,
          node "megalodon-term-subst-var-above"
            [ENat index, ETm replacement, ENat predecessor]
            [lessArticle index (predecessor + 1) above])
  | .named name =>
      (.named name,
        node "megalodon-term-subst-named"
          [ENat index, ETm replacement, a name])
  | .prim primitive =>
      (.prim primitive,
        node "megalodon-env-substitute-term-prim"
          [ENat index, ETm replacement, ENat primitive])
  | .app function argument =>
      let functionCompiled := compileTermSubstitute index replacement function
      let argumentCompiled := compileTermSubstitute index replacement argument
      (.app functionCompiled.1 argumentCompiled.1,
        node "megalodon-term-subst-app"
          [ENat index, ETm replacement, ETm function, ETm argument,
            ETm functionCompiled.1, ETm argumentCompiled.1]
          [functionCompiled.2, argumentCompiled.2])
  | .lam type body =>
      let bodyCompiled := compileTermSubstitute (index + 1) replacement body
      (.lam type bodyCompiled.1,
        node "megalodon-env-substitute-term-lam"
          [ENat index, ETm replacement, ETp type, ETm body,
            ETm bodyCompiled.1]
          [bodyCompiled.2])
  | .imp domain codomain =>
      let domainCompiled := compileTermSubstitute index replacement domain
      let codomainCompiled := compileTermSubstitute index replacement codomain
      (.imp domainCompiled.1 codomainCompiled.1,
        node "megalodon-term-subst-imp"
          [ENat index, ETm replacement, ETm domain, ETm codomain,
            ETm domainCompiled.1, ETm codomainCompiled.1]
          [domainCompiled.2, codomainCompiled.2])
  | .all type body =>
      let bodyCompiled := compileTermSubstitute (index + 1) replacement body
      (.all type bodyCompiled.1,
        node "megalodon-term-subst-all"
          [ENat index, ETm replacement, ETp type, ETm body,
            ETm bodyCompiled.1]
          [bodyCompiled.2])
  | .typeApp function type =>
      let functionCompiled := compileTermSubstitute index replacement function
      (.typeApp functionCompiled.1 type,
        node "megalodon-env-substitute-term-type-app"
          [ENat index, ETm replacement, ETm function, ETp type,
            ETm functionCompiled.1]
          [functionCompiled.2])
  | .typeLam body =>
      let bodyCompiled := compileTermSubstitute index replacement body
      (.typeLam bodyCompiled.1,
        node "megalodon-env-substitute-term-type-lam"
          [ENat index, ETm replacement, ETm body, ETm bodyCompiled.1]
          [bodyCompiled.2])
  | .typeAll body =>
      let bodyCompiled := compileTermSubstitute index replacement body
      (.typeAll bodyCompiled.1,
        node "megalodon-env-substitute-term-type-all"
          [ENat index, ETm replacement, ETm body, ETm bodyCompiled.1]
          [bodyCompiled.2])

theorem compileTermSubstitute_result (index : Nat)
    (replacement body : MathdataKernel.Tm) :
    (compileTermSubstitute index replacement body).1 =
      MathdataKernel.Tm.instantiateAt index replacement body := by
  induction body generalizing index with
  | db varIndex =>
      by_cases below : varIndex < index
      · simp [compileTermSubstitute, MathdataKernel.Tm.instantiateAt, below]
      · by_cases equal : varIndex = index
        · simp [compileTermSubstitute, MathdataKernel.Tm.instantiateAt,
            equal, compileTermShift_result]
        · simp [compileTermSubstitute, MathdataKernel.Tm.instantiateAt,
            below, equal]
  | named name => rfl
  | prim primitive => rfl
  | app function argument functionHypothesis argumentHypothesis =>
      simp [compileTermSubstitute, MathdataKernel.Tm.instantiateAt,
        functionHypothesis, argumentHypothesis]
  | lam type body bodyHypothesis =>
      simp [compileTermSubstitute, MathdataKernel.Tm.instantiateAt,
        bodyHypothesis]
  | imp domain codomain domainHypothesis codomainHypothesis =>
      simp [compileTermSubstitute, MathdataKernel.Tm.instantiateAt,
        domainHypothesis, codomainHypothesis]
  | all type body bodyHypothesis =>
      simp [compileTermSubstitute, MathdataKernel.Tm.instantiateAt,
        bodyHypothesis]
  | typeApp function type functionHypothesis =>
      simp [compileTermSubstitute, MathdataKernel.Tm.instantiateAt,
        functionHypothesis]
  | typeLam body bodyHypothesis =>
      simp [compileTermSubstitute, MathdataKernel.Tm.instantiateAt,
        bodyHypothesis]
  | typeAll body bodyHypothesis =>
      simp [compileTermSubstitute, MathdataKernel.Tm.instantiateAt,
        bodyHypothesis]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem compileTermSubstitute_checked (index : Nat)
    (replacement body : MathdataKernel.Tm) :
    checkRaw validated
      (substituteTerm (ENat index) (ETm replacement) (ETm body)
        (ETm (compileTermSubstitute index replacement body).1))
      (compileTermSubstitute index replacement body).2 = true := by
  induction body generalizing index with
  | db varIndex =>
      by_cases below : varIndex < index
      · simp only [compileTermSubstitute, dif_pos below, node,
          checkRaw, validated, instantiateRule?]
        rw [lookup_substituteTermVarBelowRule]
        simp [argumentsValidAt, argumentValidAt,
          instantiateSchemas?, instantiateSchema?,
          instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?,
          RuleSchema.sideConditionsHold,
          TermQuantifiedKernel.substVarBelowRule,
          TermQuantifiedKernel.rule, TermQuantifiedKernel.ruleId,
          TermQuantifiedKernel.substituteTerm,
          TermQuantifiedKernel.lessThan, checkRawChildren,
          TermQuantifiedKernel.encodeTm, TermQuantifiedKernel.a,
          TermQuantifiedKernel.m, substituteTerm, a]
        simpa [validated, lessThan, a, TermQuantifiedKernel.lessThan,
          TermQuantifiedKernel.a] using
          lessArticle_checked varIndex index below
      · by_cases equal : varIndex = index
        · simp only [compileTermSubstitute, dif_neg below, dif_pos equal,
            node, checkRaw, validated, instantiateRule?]
          rw [lookup_substituteTermVarEqualRule]
          simp [argumentsValidAt, argumentValidAt,
            instantiateSchemas?, instantiateSchema?,
            instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?,
            RuleSchema.sideConditionsHold,
            TermQuantifiedKernel.substVarEqualRule,
            TermQuantifiedKernel.rule, TermQuantifiedKernel.ruleId,
            TermQuantifiedKernel.substituteTerm,
            TermQuantifiedKernel.shiftTerm, checkRawChildren,
            TermQuantifiedKernel.encodeTm, TermQuantifiedKernel.a,
            TermQuantifiedKernel.m, substituteTerm, a]
          subst varIndex
          simpa [validated, TermQuantifiedKernel.shiftTerm,
            TermQuantifiedKernel.encodeNat, TermQuantifiedKernel.a] using
            compileTermShift_checked index 0 replacement
        · have above : index < varIndex := by omega
          have predecessor : varIndex = varIndex - 1 + 1 := by omega
          simp only [compileTermSubstitute, dif_neg below, dif_neg equal,
            node, checkRaw, validated, instantiateRule?]
          rw [lookup_substituteTermVarAboveRule]
          simp [argumentsValidAt, argumentValidAt,
            instantiateSchemas?, instantiateSchema?,
            instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?,
            RuleSchema.sideConditionsHold,
            TermQuantifiedKernel.substVarAboveRule,
            TermQuantifiedKernel.rule, TermQuantifiedKernel.ruleId,
            TermQuantifiedKernel.substituteTerm,
            TermQuantifiedKernel.lessThan, checkRawChildren,
            TermQuantifiedKernel.encodeTm, TermQuantifiedKernel.a,
            TermQuantifiedKernel.m, substituteTerm, a]
          constructor
          · rw [predecessor]
            rfl
          · simpa [validated, lessThan, a,
              TermQuantifiedKernel.lessThan,
              TermQuantifiedKernel.encodeNat,
              TermQuantifiedKernel.a] using
              lessArticle_checked index (varIndex - 1 + 1) (by omega)
  | named name =>
      simp only [compileTermSubstitute, node, checkRaw, validated,
        instantiateRule?]
      rw [lookup_substituteTermNamedRule]
      simp [argumentsValidAt, argumentValidAt,
        instantiateSchemas?, instantiateSchema?,
        instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?,
        RuleSchema.sideConditionsHold,
        TermQuantifiedKernel.substNamedRule,
        TermQuantifiedKernel.rule, TermQuantifiedKernel.ruleId,
        TermQuantifiedKernel.substituteTerm, checkRawChildren,
        TermQuantifiedKernel.encodeTm, TermQuantifiedKernel.a,
        TermQuantifiedKernel.m, substituteTerm, a,
        Pattern.isGroundAt, Pattern.isGroundListAt,
        Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList]
  | prim primitive =>
      simp only [compileTermSubstitute, node, checkRaw, validated,
        instantiateRule?]
      rw [lookup_substituteTermPrimRule]
      simp [argumentsValidAt, argumentValidAt,
        instantiateSchemas?, instantiateSchema?,
        instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?,
        RuleSchema.sideConditionsHold,
        substituteTermPrimRule, rule, ruleId, substituteTerm,
        checkRawChildren, TermQuantifiedKernel.encodeTm,
        TermQuantifiedKernel.a, a, m]
  | app function argument functionHypothesis argumentHypothesis =>
      simp only [compileTermSubstitute, node, checkRaw, validated,
        instantiateRule?]
      rw [lookup_substituteTermAppRule]
      simp [argumentsValidAt, argumentValidAt,
        instantiateSchemas?, instantiateSchema?,
        instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?,
        RuleSchema.sideConditionsHold,
        TermQuantifiedKernel.substAppRule,
        TermQuantifiedKernel.rule, TermQuantifiedKernel.ruleId,
        TermQuantifiedKernel.substituteTerm, checkRawChildren,
        TermQuantifiedKernel.encodeTm, TermQuantifiedKernel.a,
        TermQuantifiedKernel.m, substituteTerm, a]
      exact ⟨functionHypothesis index, argumentHypothesis index⟩
  | lam type body bodyHypothesis =>
      simp only [compileTermSubstitute, node, checkRaw, validated,
        instantiateRule?]
      rw [lookup_substituteTermLamRule]
      simp [argumentsValidAt, argumentValidAt,
        instantiateSchemas?, instantiateSchema?,
        instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?,
        RuleSchema.sideConditionsHold,
        substituteTermLamRule, rule, ruleId, substituteTerm,
        checkRawChildren, TermQuantifiedKernel.encodeTm,
        TermQuantifiedKernel.a, a, m]
      exact bodyHypothesis (index + 1)
  | imp domain codomain domainHypothesis codomainHypothesis =>
      simp only [compileTermSubstitute, node, checkRaw, validated,
        instantiateRule?]
      rw [lookup_substituteTermImpRule]
      simp [argumentsValidAt, argumentValidAt,
        instantiateSchemas?, instantiateSchema?,
        instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?,
        RuleSchema.sideConditionsHold,
        TermQuantifiedKernel.substImpRule,
        TermQuantifiedKernel.rule, TermQuantifiedKernel.ruleId,
        TermQuantifiedKernel.substituteTerm, checkRawChildren,
        TermQuantifiedKernel.encodeTm, TermQuantifiedKernel.a,
        TermQuantifiedKernel.m, substituteTerm, a]
      exact ⟨domainHypothesis index, codomainHypothesis index⟩
  | all type body bodyHypothesis =>
      simp only [compileTermSubstitute, node, checkRaw, validated,
        instantiateRule?]
      rw [lookup_substituteTermAllRule]
      simp [argumentsValidAt, argumentValidAt,
        instantiateSchemas?, instantiateSchema?,
        instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?,
        RuleSchema.sideConditionsHold,
        TermQuantifiedKernel.substAllRule,
        TermQuantifiedKernel.rule, TermQuantifiedKernel.ruleId,
        TermQuantifiedKernel.substituteTerm, checkRawChildren,
        TermQuantifiedKernel.encodeTm, TermQuantifiedKernel.a,
        TermQuantifiedKernel.m, substituteTerm, a]
      exact bodyHypothesis (index + 1)
  | typeApp function type functionHypothesis =>
      simp only [compileTermSubstitute, node, checkRaw, validated,
        instantiateRule?]
      rw [lookup_substituteTermTypeAppRule]
      simp [argumentsValidAt, argumentValidAt,
        instantiateSchemas?, instantiateSchema?,
        instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?,
        RuleSchema.sideConditionsHold,
        substituteTermTypeAppRule, rule, ruleId, substituteTerm,
        checkRawChildren, TermQuantifiedKernel.encodeTm,
        TermQuantifiedKernel.a, a, m]
      exact functionHypothesis index
  | typeLam body bodyHypothesis =>
      simp only [compileTermSubstitute, node, checkRaw, validated,
        instantiateRule?]
      rw [lookup_substituteTermTypeLamRule]
      simp [argumentsValidAt, argumentValidAt,
        instantiateSchemas?, instantiateSchema?,
        instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?,
        RuleSchema.sideConditionsHold,
        substituteTermTypeLamRule, rule, ruleId, substituteTerm,
        checkRawChildren, TermQuantifiedKernel.encodeTm,
        TermQuantifiedKernel.a, a, m]
      exact bodyHypothesis index
  | typeAll body bodyHypothesis =>
      simp only [compileTermSubstitute, node, checkRaw, validated,
        instantiateRule?]
      rw [lookup_substituteTermTypeAllRule]
      simp [argumentsValidAt, argumentValidAt,
        instantiateSchemas?, instantiateSchema?,
        instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?,
        RuleSchema.sideConditionsHold,
        substituteTermTypeAllRule, rule, ruleId, substituteTerm,
        checkRawChildren, TermQuantifiedKernel.encodeTm,
        TermQuantifiedKernel.a, a, m]
      exact bodyHypothesis index

theorem compiled_type_shift_is_sortedABT
    (amount cutoff : Nat) (type : MathdataKernel.Tp) :
    SortedABTRefinement.encodeType
        (compileTypeShift amount cutoff type).1 =
      Mettapedia.GSLT.LanguageDef.SortedSignatureIndexedABT.Term.lift
        SortedABTRefinement.VarSort.type cutoff amount
        (SortedABTRefinement.encodeType type) := by
  rw [compileTypeShift_result]
  exact SortedABTRefinement.encodeType_shift cutoff amount type

theorem compiled_type_substitution_in_type_is_sortedABT
    (index : Nat) (replacement body : MathdataKernel.Tp) :
    SortedABTRefinement.encodeType
        (compileTypeSubstituteType index replacement body).1 =
      Mettapedia.GSLT.LanguageDef.SortedSignatureIndexedABT.Term.instantiateAt
        SortedABTRefinement.VarSort.type index
        (SortedABTRefinement.encodeType replacement)
        (SortedABTRefinement.encodeType body) := by
  rw [compileTypeSubstituteType_result]
  exact SortedABTRefinement.encodeType_instantiateAt index replacement body

theorem compiled_term_shift_is_sortedABT
    (amount cutoff : Nat) (term : MathdataKernel.Tm) :
    SortedABTRefinement.encode (compileTermShift amount cutoff term).1 =
      Mettapedia.GSLT.LanguageDef.SortedSignatureIndexedABT.Term.lift
        SortedABTRefinement.VarSort.term cutoff amount
        (SortedABTRefinement.encode term) := by
  rw [compileTermShift_result]
  exact SortedABTRefinement.encode_shift cutoff amount term

theorem compiled_term_substitution_is_sortedABT
    (index : Nat) (replacement body : MathdataKernel.Tm) :
    SortedABTRefinement.encode
        (compileTermSubstitute index replacement body).1 =
      Mettapedia.GSLT.LanguageDef.SortedSignatureIndexedABT.Term.instantiateAt
        SortedABTRefinement.VarSort.term index
        (SortedABTRefinement.encode replacement)
        (SortedABTRefinement.encode body) := by
  rw [compileTermSubstitute_result]
  exact SortedABTRefinement.encode_instantiateAt index replacement body

theorem compiled_type_substitution_is_sortedABT
    (index : Nat) (replacement : MathdataKernel.Tp)
    (body : MathdataKernel.Tm) :
    SortedABTRefinement.encode
        (compileTypeSubstituteTerm index replacement body).1 =
      Mettapedia.GSLT.LanguageDef.SortedSignatureIndexedABT.Term.instantiateAt
        SortedABTRefinement.VarSort.type index
        (SortedABTRefinement.encodeType replacement)
        (SortedABTRefinement.encode body) := by
  rw [compileTypeSubstituteTerm_result]
  exact SortedABTRefinement.encode_typeInstantiateAt index replacement body

/-! ## A checked two-theorem Megalodon document -/

def polymorphicReuseDeclaration : MathdataKernel.KnownDecl :=
  { name := MathdataKernel.polymorphicReuseName
    proposition := PolymorphicKernel.goalTerm }

def polymorphicReuseInitialEnvironment : MathdataKernel.Environment := {}

def polymorphicReuseAfterFirstEnvironment : MathdataKernel.Environment :=
  { known := [polymorphicReuseDeclaration] }

def polymorphicReuseFinalEnvironment : MathdataKernel.Environment :=
  { known := [polymorphicReuseDeclaration, polymorphicReuseDeclaration] }

def polymorphicReuseDeclarations : List MathdataKernel.KnownDecl :=
  [polymorphicReuseDeclaration, polymorphicReuseDeclaration]

private def plainPTypeArticle : RawProof :=
  node "megalodon-poly-type-arr"
    [ENat 1, ETp (.var 0), ETp .prop]
    [ node "megalodon-poly-type-var" [ENat 1, ENat 0]
        [node "megalodon-term-less-zero" [ENat 0]],
      node "megalodon-poly-type-prop" [ENat 1] ]

private def emptyProofContextShiftArticle : RawProof :=
  node "megalodon-term-shift-proof-nil" [ENat 1, ENat 0]

private def firstEnvironmentProofArticle : RawProof :=
  node "megalodon-env-proof-base"
    [ encodePrimitiveTypes [], ESig [], encodeKnown [], ENat 0,
      ETyCtx [], EPfCtx [], ETm PolymorphicKernel.goalTerm ]
    [PolymorphicKernel.article]

private def knownReuseArticle : RawProof :=
  node "megalodon-env-proof-known"
    [ encodePrimitiveTypes [], ESig [],
      encodeKnown [polymorphicReuseDeclaration], ENat 1,
      ETyCtx [PolymorphicKernel.pType], EPfCtx [],
      a MathdataKernel.polymorphicReuseName,
      ETm PolymorphicKernel.goalTerm ]
    [ node "megalodon-env-known-here"
        [ a MathdataKernel.polymorphicReuseName,
          ETm PolymorphicKernel.goalTerm, encodeKnown [] ] ]

private def reuseTypeApplicationArticle : RawProof :=
  let substitution := compileTypeSubstituteTerm 0 (.var 0)
    PolymorphicKernel.theoremBody
  node "megalodon-env-proof-type-elim"
    [ encodeEnvironment polymorphicReuseAfterFirstEnvironment,
      ENat 1, ETyCtx [PolymorphicKernel.pType], EPfCtx [],
      ETm PolymorphicKernel.theoremBody, ETp (.var 0),
      ETm substitution.1 ]
    [knownReuseArticle, substitution.2]

private def reuseArgumentTypeArticle : RawProof :=
  node "megalodon-poly-term-var-zero"
    [ESig [], ENat 1, ETyCtx [], ETp PolymorphicKernel.pType]

private def reuseApplicationArticle : RawProof :=
  let body := .imp PolymorphicKernel.forallDomain
    PolymorphicKernel.forallDomain
  let substitution := compileTermSubstitute 0 (.db 0) body
  node "megalodon-env-proof-all-elim"
    [ encodePrimitiveTypes [], ESig [],
      encodeKnown [polymorphicReuseDeclaration], ENat 1,
      ETyCtx [PolymorphicKernel.pType], EPfCtx [],
      ETp PolymorphicKernel.pType, ETm body, ETm (.db 0),
      ETm substitution.1 ]
    [reuseTypeApplicationArticle, reuseArgumentTypeArticle, substitution.2]

private def secondEnvironmentProofArticle : RawProof :=
  let body := .imp PolymorphicKernel.forallDomain
    PolymorphicKernel.forallDomain
  node "megalodon-env-proof-type-intro"
    [encodeEnvironment polymorphicReuseAfterFirstEnvironment,
      ETm PolymorphicKernel.theoremBody]
    [ node "megalodon-env-proof-all-intro"
        [ encodeEnvironment polymorphicReuseAfterFirstEnvironment,
          ENat 1, ETyCtx [], EPfCtx [], EPfCtx [],
          ETp PolymorphicKernel.pType, ETm body ]
        [plainPTypeArticle, emptyProofContextShiftArticle,
          reuseApplicationArticle] ]

def polymorphicReuseDocumentGoal : Pattern :=
  checksDocument
    (encodeEnvironment polymorphicReuseInitialEnvironment)
    (encodeDeclarations polymorphicReuseDeclarations)
    (encodeEnvironment polymorphicReuseFinalEnvironment)

def polymorphicReuseDocumentArticle : RawProof :=
  node "megalodon-env-document-cons"
    [ encodePrimitiveTypes [], ESig [], encodeKnown [],
      a MathdataKernel.polymorphicReuseName,
      ETm PolymorphicKernel.goalTerm,
      encodeDeclarations [polymorphicReuseDeclaration],
      encodeEnvironment polymorphicReuseFinalEnvironment ]
    [ firstEnvironmentProofArticle,
      (node "megalodon-env-document-cons"
        [ encodePrimitiveTypes [], ESig [],
          encodeKnown [polymorphicReuseDeclaration],
          a MathdataKernel.polymorphicReuseName,
          ETm PolymorphicKernel.goalTerm, encodeDeclarations [],
          encodeEnvironment polymorphicReuseFinalEnvironment ]
        [ secondEnvironmentProofArticle,
          (node "megalodon-env-document-nil"
            [encodeEnvironment polymorphicReuseFinalEnvironment] []) ]) ]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem polymorphic_reuse_document_accepted :
    checkRaw validated polymorphicReuseDocumentGoal
      polymorphicReuseDocumentArticle = true := by
  simp (config := { maxSteps := 4000000, decide := true })
    [checkRaw, checkRawChildren, instantiateRule?, Presentation.lookupRule?,
      instantiateSchemas?, instantiateSchema?, instantiateSchemasAt?,
      instantiateSchemaAt?, lookupArgumentAt?,
      polymorphicReuseDocumentGoal,
      polymorphicReuseDocumentArticle, firstEnvironmentProofArticle,
      secondEnvironmentProofArticle, reuseApplicationArticle,
      reuseTypeApplicationArticle, reuseArgumentTypeArticle,
      knownReuseArticle, plainPTypeArticle, emptyProofContextShiftArticle,
      compileTypeSubstituteTerm, compileTypeSubstituteType,
      compileTypeShift, compileTypeVariableShift,
      compileTermSubstitute, compileTermShift, compileTermVariableShift,
      addArticle, lessArticle,
      polymorphicReuseInitialEnvironment,
      polymorphicReuseAfterFirstEnvironment,
      polymorphicReuseFinalEnvironment, polymorphicReuseDeclarations,
      polymorphicReuseDeclaration, encodeDeclarations, encodeEnvironment,
      encodePrimitiveTypes, encodeKnown, node,
      validated, presentation, definition, additionalConstructors,
      additionalJudgments, additionalRules,
      shiftTypeVarZeroRule, shiftTypeVarBelowRule, shiftTypeVarSuccRule,
      shiftTypePropRule, shiftTypeBaseRule, shiftTypeArrRule,
      shiftTypeAllRule, substituteTypeVarEqualRule,
      substituteTypeVarBelowRule, substituteTypeVarAboveRule,
      substituteTypePropRule, substituteTypeBaseRule,
      substituteTypeArrRule, substituteTypeAllRule,
      substituteTypeTermVarRule, substituteTypeTermNamedRule,
      substituteTypeTermPrimRule, substituteTypeTermAppRule,
      substituteTypeTermLamRule, substituteTypeTermImpRule,
      substituteTypeTermAllRule, substituteTypeTermTypeAppRule,
      substituteTypeTermTypeLamRule, substituteTypeTermTypeAllRule,
      shiftTermPrimRule, shiftTermLamRule, shiftTermTypeAppRule,
      shiftTermTypeLamRule, shiftTermTypeAllRule,
      substituteTermPrimRule, substituteTermLamRule,
      substituteTermTypeAppRule, substituteTermTypeLamRule,
      substituteTermTypeAllRule, knownHereRule, knownThereRule,
      proofBaseRule, proofKnownRule, proofImpIntroRule, proofImpElimRule,
      proofTypeElimRule,
      proofAllElimRule, proofAllIntroRule, proofTypeIntroRule,
      documentNilRule, documentConsRule, rule, ruleId,
      addNat, lessThan, plainType, baseHasType, baseProves, proves,
      knownMember, shiftType, substituteType, substituteTypeInTerm,
      shiftProofContext, substituteTerm, checksDocument, a, m,
      PolymorphicKernel.definition, PolymorphicKernel.additionalRules,
      PolymorphicKernel.additionalJudgments, PolymorphicKernel.rule,
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
      PolymorphicKernel.shiftProofContext, PolymorphicKernel.substituteTerm,
      PolymorphicKernel.a, PolymorphicKernel.m,
      TermQuantifiedKernel.definition, TermQuantifiedKernel.rules,
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
      TermQuantifiedKernel.substAppRule,
      TermQuantifiedKernel.substImpRule,
      TermQuantifiedKernel.substAllRule,
      TermQuantifiedKernel.typeVarZeroRule,
      TermQuantifiedKernel.typeVarSuccRule,
      TermQuantifiedKernel.typeNamedZeroRule,
      TermQuantifiedKernel.typeNamedSuccRule,
      TermQuantifiedKernel.typeAppRule,
      TermQuantifiedKernel.typeImpRule,
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
      TermQuantifiedKernel.substituteTerm, TermQuantifiedKernel.a,
      TermQuantifiedKernel.m,
      PolymorphicKernel.pType, PolymorphicKernel.theoremBody,
      PolymorphicKernel.forallDomain, PolymorphicKernel.forallBody,
      PolymorphicKernel.goalTerm, MathdataKernel.polymorphicReuseName]
  exact checkRaw_true_of_ruleLookupRefines polymorphic_ruleLookupRefines
    PolymorphicKernel.polymorphic_forall_identity_accepted

def polymorphicReuseWrongFinalGoal : Pattern :=
  checksDocument
    (encodeEnvironment polymorphicReuseInitialEnvironment)
    (encodeDeclarations polymorphicReuseDeclarations)
    (encodeEnvironment polymorphicReuseAfterFirstEnvironment)

theorem polymorphic_reuse_wrong_final_rejected :
    checkRaw validated polymorphicReuseWrongFinalGoal
      polymorphicReuseDocumentArticle = false := by
  by_contra hypothesis
  have acceptedWrong :
      checkRaw validated polymorphicReuseWrongFinalGoal
        polymorphicReuseDocumentArticle = true := by
    simpa using hypothesis
  have goalsEqual := checkRaw_goal_unique polymorphic_reuse_document_accepted
    acceptedWrong
  simp [polymorphicReuseDocumentGoal, polymorphicReuseWrongFinalGoal,
    polymorphicReuseFinalEnvironment, polymorphicReuseAfterFirstEnvironment,
    polymorphicReuseDeclaration, encodeEnvironment, encodeKnown,
    MathdataKernel.polymorphicReuseName, checksDocument, a] at goalsEqual

/-! ## Known implication application emitted by Megalodon -/

def implicationReuseTerm : MathdataKernel.Tm :=
  .named implicationReuseTermName

def implicationReuseProposition : MathdataKernel.Tm :=
  .imp implicationReuseTerm implicationReuseTerm

def implicationReuseTermDeclaration : MathdataKernel.TermDecl :=
  { name := implicationReuseTermName
    type := .prop }

def implicationReuseKnownDeclaration : MathdataKernel.KnownDecl :=
  { name := implicationReuseKnownName
    proposition := implicationReuseProposition }

def implicationReuseInitialEnvironment : MathdataKernel.Environment :=
  { terms := [implicationReuseTermDeclaration] }

def implicationReuseAfterFirstEnvironment : MathdataKernel.Environment :=
  { terms := [implicationReuseTermDeclaration]
    known := [implicationReuseKnownDeclaration] }

def implicationReuseFinalEnvironment : MathdataKernel.Environment :=
  { terms := [implicationReuseTermDeclaration]
    known := [implicationReuseKnownDeclaration,
      implicationReuseKnownDeclaration] }

def implicationReuseFirstProof : MathdataKernel.Pf :=
  .proofLam implicationReuseTerm (.hyp 0)

def implicationReuseSecondProof : MathdataKernel.Pf :=
  .proofLam implicationReuseTerm
    (.proofApp (.known implicationReuseKnownName) (.hyp 0))

theorem mathdata_accepts_implication_reuse_first :
    MathdataKernel.checkProof implicationReuseInitialEnvironment 32
      0 [] [] implicationReuseFirstProof implicationReuseProposition = true := by
  simp [MathdataKernel.checkProof, MathdataKernel.checkNormalizedProof,
    MathdataKernel.inferProof,
    implicationReuseInitialEnvironment, implicationReuseFirstProof,
    implicationReuseProposition, implicationReuseTerm,
    implicationReuseTermDeclaration, implicationReuseTermName,
    MathdataKernel.checkProposition, MathdataKernel.inferTerm,
    MathdataKernel.normalize, MathdataKernel.deltaNormalize,
    MathdataKernel.Tm.normalize, MathdataKernel.Tm.normalizeOne,
    MathdataKernel.Environment.lookupTerm?, MathdataKernel.lookupTermList?]

theorem mathdata_accepts_implication_reuse_second :
    MathdataKernel.checkProof implicationReuseAfterFirstEnvironment 32
      0 [] [] implicationReuseSecondProof implicationReuseProposition = true := by
  simp [MathdataKernel.checkProof, MathdataKernel.checkNormalizedProof,
    MathdataKernel.inferProof,
    implicationReuseAfterFirstEnvironment, implicationReuseSecondProof,
    implicationReuseProposition, implicationReuseTerm,
    implicationReuseKnownDeclaration, implicationReuseTermDeclaration,
    implicationReuseKnownName, implicationReuseTermName,
    MathdataKernel.checkProposition, MathdataKernel.inferTerm,
    MathdataKernel.normalize, MathdataKernel.deltaNormalize,
    MathdataKernel.Tm.normalize, MathdataKernel.Tm.normalizeOne,
    MathdataKernel.Environment.lookupTerm?, MathdataKernel.lookupTermList?,
    MathdataKernel.Environment.lookupKnown?, MathdataKernel.lookupKnownList?]

def implicationReuseUnknownProof : MathdataKernel.Pf :=
  .proofLam implicationReuseTerm
    (.proofApp (.known (implicationReuseKnownName ++ "0")) (.hyp 0))

theorem mathdata_rejects_unknown_implication_reuse :
    MathdataKernel.checkProof implicationReuseAfterFirstEnvironment 32
      0 [] [] implicationReuseUnknownProof implicationReuseProposition = false := by
  simp [MathdataKernel.checkProof, MathdataKernel.checkNormalizedProof,
    MathdataKernel.inferProof,
    implicationReuseAfterFirstEnvironment, implicationReuseUnknownProof,
    implicationReuseProposition, implicationReuseTerm,
    implicationReuseKnownDeclaration, implicationReuseTermDeclaration,
    implicationReuseKnownName, implicationReuseTermName,
    MathdataKernel.checkProposition, MathdataKernel.inferTerm,
    MathdataKernel.normalize, MathdataKernel.deltaNormalize,
    MathdataKernel.Tm.normalize, MathdataKernel.Tm.normalizeOne,
    MathdataKernel.Environment.lookupTerm?, MathdataKernel.lookupTermList?,
    MathdataKernel.Environment.lookupKnown?, MathdataKernel.lookupKnownList?]

private def implicationReuseNamedTypeArticle : RawProof :=
  node "megalodon-poly-term-named-zero"
    [ a implicationReuseTermName, ETp .prop, ESig [], ENat 0, ETyCtx [] ]

private def implicationReuseBaseHypArticle : RawProof :=
  node "megalodon-poly-proof-hyp-zero"
    [ ESig [implicationReuseTermDeclaration], ENat 0, ETyCtx [],
      EPfCtx [], ETm implicationReuseTerm ]
    [implicationReuseNamedTypeArticle]

private def implicationReuseBaseProofArticle : RawProof :=
  node "megalodon-poly-proof-imp-intro"
    [ ESig [implicationReuseTermDeclaration], ENat 0, ETyCtx [],
      EPfCtx [], ETm implicationReuseTerm, ETm implicationReuseTerm ]
    [implicationReuseNamedTypeArticle, implicationReuseBaseHypArticle]

private def implicationReuseFirstEnvironmentProofArticle : RawProof :=
  node "megalodon-env-proof-base"
    [ encodePrimitiveTypes [], ESig [implicationReuseTermDeclaration],
      encodeKnown [], ENat 0, ETyCtx [], EPfCtx [],
      ETm implicationReuseProposition ]
    [implicationReuseBaseProofArticle]

private def implicationReuseKnownArticle : RawProof :=
  node "megalodon-env-proof-known"
    [ encodePrimitiveTypes [], ESig [implicationReuseTermDeclaration],
      encodeKnown [implicationReuseKnownDeclaration], ENat 0, ETyCtx [],
      EPfCtx [implicationReuseTerm], a implicationReuseKnownName,
      ETm implicationReuseProposition ]
    [ node "megalodon-env-known-here"
        [ a implicationReuseKnownName, ETm implicationReuseProposition,
          encodeKnown [] ] ]

private def implicationReuseEnvironmentHypArticle : RawProof :=
  node "megalodon-env-proof-base"
    [ encodePrimitiveTypes [], ESig [implicationReuseTermDeclaration],
      encodeKnown [implicationReuseKnownDeclaration], ENat 0, ETyCtx [],
      EPfCtx [implicationReuseTerm], ETm implicationReuseTerm ]
    [implicationReuseBaseHypArticle]

private def implicationReuseSecondEnvironmentProofArticle : RawProof :=
  node "megalodon-env-proof-imp-intro"
    [ encodePrimitiveTypes [], ESig [implicationReuseTermDeclaration],
      encodeKnown [implicationReuseKnownDeclaration], ENat 0, ETyCtx [],
      EPfCtx [], ETm implicationReuseTerm, ETm implicationReuseTerm ]
    [ implicationReuseNamedTypeArticle,
      node "megalodon-env-proof-imp-elim"
        [ encodeEnvironment implicationReuseAfterFirstEnvironment,
          ENat 0, ETyCtx [], EPfCtx [implicationReuseTerm],
          ETm implicationReuseTerm, ETm implicationReuseTerm ]
        [implicationReuseKnownArticle, implicationReuseEnvironmentHypArticle] ]

def implicationReuseDocumentGoal : Pattern :=
  checksDocument
    (encodeEnvironment implicationReuseInitialEnvironment)
    (encodeDeclarations
      [implicationReuseKnownDeclaration, implicationReuseKnownDeclaration])
    (encodeEnvironment implicationReuseFinalEnvironment)

def implicationReuseDocumentArticle : RawProof :=
  node "megalodon-env-document-cons"
    [ encodePrimitiveTypes [], ESig [implicationReuseTermDeclaration],
      encodeKnown [], a implicationReuseKnownName,
      ETm implicationReuseProposition,
      encodeDeclarations [implicationReuseKnownDeclaration],
      encodeEnvironment implicationReuseFinalEnvironment ]
    [ implicationReuseFirstEnvironmentProofArticle,
      node "megalodon-env-document-cons"
        [ encodePrimitiveTypes [], ESig [implicationReuseTermDeclaration],
          encodeKnown [implicationReuseKnownDeclaration],
          a implicationReuseKnownName, ETm implicationReuseProposition,
          encodeDeclarations [],
          encodeEnvironment implicationReuseFinalEnvironment ]
        [ implicationReuseSecondEnvironmentProofArticle,
          node "megalodon-env-document-nil"
            [encodeEnvironment implicationReuseFinalEnvironment] [] ] ]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem implication_reuse_document_accepted :
    checkRaw validated implicationReuseDocumentGoal
      implicationReuseDocumentArticle = true := by
  simp (config := { maxSteps := 4000000, decide := true })
    [ checkRaw, checkRawChildren, instantiateRule?, Presentation.lookupRule?,
      instantiateSchemas?, instantiateSchema?, instantiateSchemasAt?,
      instantiateSchemaAt?, lookupArgumentAt?,
      implicationReuseDocumentGoal, implicationReuseDocumentArticle,
      implicationReuseFirstEnvironmentProofArticle,
      implicationReuseSecondEnvironmentProofArticle,
      implicationReuseEnvironmentHypArticle, implicationReuseKnownArticle,
      implicationReuseBaseProofArticle, implicationReuseBaseHypArticle,
      implicationReuseNamedTypeArticle, implicationReuseInitialEnvironment,
      implicationReuseAfterFirstEnvironment, implicationReuseFinalEnvironment,
      implicationReuseKnownDeclaration, implicationReuseTermDeclaration,
      implicationReuseProposition, implicationReuseTerm,
      implicationReuseTermName, implicationReuseKnownName,
      encodeDeclarations, encodeEnvironment, encodePrimitiveTypes, encodeKnown,
      node, validated, presentation, definition, additionalConstructors,
      additionalJudgments, additionalRules, proofImpIntroRule,
      proofImpElimRule, proofBaseRule, proofKnownRule, knownHereRule,
      documentNilRule, documentConsRule, rule, ruleId,
      baseHasType, baseProves, proves, knownMember, checksDocument, a, m,
      PolymorphicKernel.definition, PolymorphicKernel.additionalRules,
      PolymorphicKernel.additionalJudgments, PolymorphicKernel.rule,
      PolymorphicKernel.ruleId, PolymorphicKernel.typeNamedZeroRule,
      PolymorphicKernel.proofHypZeroRule,
      PolymorphicKernel.proofImpIntroRule,
      PolymorphicKernel.hasType, PolymorphicKernel.proves,
      PolymorphicKernel.a, PolymorphicKernel.m,
      TermQuantifiedKernel.definition, TermQuantifiedKernel.rules,
      TermQuantifiedKernel.a,
      TermQuantifiedKernel.encodeNat, TermQuantifiedKernel.encodeTp,
      TermQuantifiedKernel.encodeTm, TermQuantifiedKernel.encodeTypeContext,
      TermQuantifiedKernel.encodeProofContext ]

def implicationReuseWrongFinalGoal : Pattern :=
  checksDocument
    (encodeEnvironment implicationReuseInitialEnvironment)
    (encodeDeclarations
      [implicationReuseKnownDeclaration, implicationReuseKnownDeclaration])
    (encodeEnvironment implicationReuseAfterFirstEnvironment)

theorem implication_reuse_wrong_final_rejected :
    checkRaw validated implicationReuseWrongFinalGoal
      implicationReuseDocumentArticle = false := by
  by_contra hypothesis
  have acceptedWrong :
      checkRaw validated implicationReuseWrongFinalGoal
        implicationReuseDocumentArticle = true := by
    simpa using hypothesis
  have goalsEqual := checkRaw_goal_unique implication_reuse_document_accepted
    acceptedWrong
  simp [implicationReuseDocumentGoal, implicationReuseWrongFinalGoal,
    implicationReuseFinalEnvironment, implicationReuseAfterFirstEnvironment,
    implicationReuseKnownDeclaration, implicationReuseTermDeclaration,
    implicationReuseProposition, implicationReuseTerm,
    implicationReuseTermName, implicationReuseKnownName,
    encodeEnvironment, encodeKnown, encodeDeclarations, checksDocument, a]
    at goalsEqual

end Mettapedia.Languages.Megalodon.EnvironmentKernel
