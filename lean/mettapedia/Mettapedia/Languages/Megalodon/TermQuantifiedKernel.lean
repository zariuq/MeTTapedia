import Mettapedia.GSLT.LanguageDef.CalculusLanguageDef
import Mettapedia.GSLT.LanguageDef.InferenceChecker
import Mettapedia.Languages.Megalodon.MathdataKernel

/-!
# Megalodon term-quantified kernel authority

This is the first binder-bearing extension of the implicational authority.  It
models the monomorphic `Mathdata` constructors `Hyp`, `PPfAp`, `PLam`,
`PTmAp`, and `TLam`, together with explicit term typing, shifting, and
capture-avoiding de Bruijn substitution.  Type polymorphism, named known
proofs, and beta/eta/delta conversion remain outside this fragment.

Object-language de Bruijn indices are explicit first-order data.  This keeps
arbitrary term-context depth representable in a finite inference
definition; the separate ABT refinement identifies these operations with
the support-indexed physical carrier.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Megalodon.TermQuantifiedKernel

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.ExtensionComposition
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.OSLF.MeTTaIL.Syntax

def expressionType : TypeDecl := TypeDecl.plain "MegalodonTermExpr"

def expressionConstructor (head : String) (arity : Nat) : GrammarRule :=
  { label := head
    category := "MegalodonTermExpr"
    params := (List.range arity).map fun index =>
      .simple s!"argument{index}" (.base "MegalodonTermExpr")
    syntaxPattern := [] }

def a (head : String) (arguments : List Pattern := []) : Pattern :=
  .apply head arguments

def m (name : String) : Pattern := .fvar name

def encodeNat : Nat → Pattern
  | 0 => a "MNZero"
  | value + 1 => a "MNSucc" [encodeNat value]

def encodeTp : MathdataKernel.Tp → Pattern
  | .var index => a "MTpVar" [encodeNat index]
  | .prop => a "MTpProp"
  | .base index => a "MTpBase" [encodeNat index]
  | .arr domain codomain => a "MTpArr" [encodeTp domain, encodeTp codomain]
  | .all body => a "MTpAll" [encodeTp body]

def encodeTm : MathdataKernel.Tm → Pattern
  | .db index => a "MTmVar" [encodeNat index]
  | .named name => a "MTmNamed" [a name]
  | .prim index => a "MTmPrim" [encodeNat index]
  | .app function argument => a "MTmApp" [encodeTm function, encodeTm argument]
  | .lam type body => a "MTmLam" [encodeTp type, encodeTm body]
  | .imp domain codomain => a "MTmImp" [encodeTm domain, encodeTm codomain]
  | .all type body => a "MTmAll" [encodeTp type, encodeTm body]
  | .typeApp function type => a "MTmTypeApp" [encodeTm function, encodeTp type]
  | .typeLam body => a "MTmTypeLam" [encodeTm body]
  | .typeAll body => a "MTmTypeAll" [encodeTm body]

def encodeTypeContext : List MathdataKernel.Tp → Pattern
  | [] => a "MTyCtxNil"
  | type :: context => a "MTyCtxCons" [encodeTp type, encodeTypeContext context]

def encodeProofContext : List MathdataKernel.Tm → Pattern
  | [] => a "MPfCtxNil"
  | proposition :: context =>
      a "MPfCtxCons" [encodeTm proposition, encodeProofContext context]

def encodeSignature : List MathdataKernel.TermDecl → Pattern
  | [] => a "MSigNil"
  | declaration :: declarations =>
      a "MSigCons"
        [a declaration.name, encodeTp declaration.type,
          encodeSignature declarations]

/-! ## Exact carrier invariants -/

@[simp] theorem encodeNat_ground (value : Nat) :
    (encodeNat value).isGroundAt 0 = true := by
  induction value with
  | zero =>
      simp [encodeNat, a, Pattern.isGroundAt, Pattern.isGroundListAt]
  | succ value inductionHypothesis =>
      simp [encodeNat, a, Pattern.isGroundAt, Pattern.isGroundListAt,
        inductionHypothesis]

@[simp] theorem encodeNat_canonical (value : Nat) :
    (encodeNat value).hasCanonicalBinderMetadata = true := by
  induction value with
  | zero =>
      simp [encodeNat, a, Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList]
  | succ value inductionHypothesis =>
      simp [encodeNat, a, Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList, inductionHypothesis]

@[simp] theorem encodeTp_ground (type : MathdataKernel.Tp) :
    (encodeTp type).isGroundAt 0 = true := by
  induction type with
  | var index =>
      simp [encodeTp, a, Pattern.isGroundAt, Pattern.isGroundListAt]
  | prop =>
      simp [encodeTp, a, Pattern.isGroundAt, Pattern.isGroundListAt]
  | base index =>
      simp [encodeTp, a, Pattern.isGroundAt, Pattern.isGroundListAt]
  | arr domain codomain domainHypothesis codomainHypothesis =>
      simp [encodeTp, a, Pattern.isGroundAt, Pattern.isGroundListAt,
        domainHypothesis, codomainHypothesis]
  | all body inductionHypothesis =>
      simp [encodeTp, a, Pattern.isGroundAt, Pattern.isGroundListAt,
        inductionHypothesis]

@[simp] theorem encodeTp_canonical (type : MathdataKernel.Tp) :
    (encodeTp type).hasCanonicalBinderMetadata = true := by
  induction type with
  | var index =>
      simp [encodeTp, a, Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList]
  | prop =>
      simp [encodeTp, a, Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList]
  | base index =>
      simp [encodeTp, a, Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList]
  | arr domain codomain domainHypothesis codomainHypothesis =>
      simp [encodeTp, a, Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList,
        domainHypothesis, codomainHypothesis]
  | all body inductionHypothesis =>
      simp [encodeTp, a, Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList, inductionHypothesis]

@[simp] theorem encodeTm_ground (term : MathdataKernel.Tm) :
    (encodeTm term).isGroundAt 0 = true := by
  induction term with
  | db index =>
      simp [encodeTm, a, Pattern.isGroundAt, Pattern.isGroundListAt]
  | named name =>
      simp [encodeTm, a, Pattern.isGroundAt, Pattern.isGroundListAt]
  | prim index =>
      simp [encodeTm, a, Pattern.isGroundAt, Pattern.isGroundListAt]
  | app function argument functionHypothesis argumentHypothesis =>
      simp [encodeTm, a, Pattern.isGroundAt, Pattern.isGroundListAt,
        functionHypothesis, argumentHypothesis]
  | lam type body bodyHypothesis =>
      simp [encodeTm, a, Pattern.isGroundAt, Pattern.isGroundListAt,
        bodyHypothesis]
  | imp domain codomain domainHypothesis codomainHypothesis =>
      simp [encodeTm, a, Pattern.isGroundAt, Pattern.isGroundListAt,
        domainHypothesis, codomainHypothesis]
  | all type body bodyHypothesis =>
      simp [encodeTm, a, Pattern.isGroundAt, Pattern.isGroundListAt,
        bodyHypothesis]
  | typeApp function type functionHypothesis =>
      simp [encodeTm, a, Pattern.isGroundAt, Pattern.isGroundListAt,
        functionHypothesis]
  | typeLam body bodyHypothesis =>
      simp [encodeTm, a, Pattern.isGroundAt, Pattern.isGroundListAt,
        bodyHypothesis]
  | typeAll body bodyHypothesis =>
      simp [encodeTm, a, Pattern.isGroundAt, Pattern.isGroundListAt,
        bodyHypothesis]

@[simp] theorem encodeTm_canonical (term : MathdataKernel.Tm) :
    (encodeTm term).hasCanonicalBinderMetadata = true := by
  induction term with
  | db index =>
      simp [encodeTm, a, Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList]
  | named name =>
      simp [encodeTm, a, Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList]
  | prim index =>
      simp [encodeTm, a, Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList]
  | app function argument functionHypothesis argumentHypothesis =>
      simp [encodeTm, a, Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList,
        functionHypothesis, argumentHypothesis]
  | lam type body bodyHypothesis =>
      simp [encodeTm, a, Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList, bodyHypothesis]
  | imp domain codomain domainHypothesis codomainHypothesis =>
      simp [encodeTm, a, Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList,
        domainHypothesis, codomainHypothesis]
  | all type body bodyHypothesis =>
      simp [encodeTm, a, Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList, bodyHypothesis]
  | typeApp function type functionHypothesis =>
      simp [encodeTm, a, Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList, functionHypothesis]
  | typeLam body bodyHypothesis =>
      simp [encodeTm, a, Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList, bodyHypothesis]
  | typeAll body bodyHypothesis =>
      simp [encodeTm, a, Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList, bodyHypothesis]

def addNat (left right result : Pattern) : Pattern :=
  a "MAddNat" [left, right, result]

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

def hasType
    (signature context term type : Pattern) : Pattern :=
  a "MTermHasType" [signature, context, term, type]

def proves
    (signature termContext proofContext proposition : Pattern) : Pattern :=
  a "MTermProves" [signature, termContext, proofContext, proposition]

def ruleId (value : String) : RuleId := ⟨value⟩

def rule (id : String) (metavariables : List String)
    (premises : List Pattern) (conclusion : Pattern) : RuleSchema :=
  { id := ruleId id
    metavariables := metavariables.map fun name => (name, 0)
    premises
    conclusion }

/-! ## Natural-number evidence -/

def addZeroRule : RuleSchema :=
  rule "megalodon-term-add-zero" ["right"] []
    (addNat (a "MNZero") (m "right") (m "right"))

def addSuccRule : RuleSchema :=
  rule "megalodon-term-add-succ" ["left", "right", "result"]
    [addNat (m "left") (m "right") (m "result")]
    (addNat (a "MNSucc" [m "left"]) (m "right")
      (a "MNSucc" [m "result"]))

def lessZeroRule : RuleSchema :=
  rule "megalodon-term-less-zero" ["right"] []
    (lessThan (a "MNZero") (a "MNSucc" [m "right"]))

def lessSuccRule : RuleSchema :=
  rule "megalodon-term-less-succ" ["left", "right"]
    [lessThan (m "left") (m "right")]
    (lessThan (a "MNSucc" [m "left"]) (a "MNSucc" [m "right"]))

/-! ## Proof-carrying term shifting -/

def shiftVarAtZeroRule : RuleSchema :=
  rule "megalodon-term-shift-var-zero"
    ["amount", "variable", "result"]
    [addNat (m "variable") (m "amount") (m "result")]
    (shiftTerm (m "amount") (a "MNZero")
      (a "MTmVar" [m "variable"]) (a "MTmVar" [m "result"]))

def shiftVarBelowRule : RuleSchema :=
  rule "megalodon-term-shift-var-below" ["amount", "cutoff"] []
    (shiftTerm (m "amount") (a "MNSucc" [m "cutoff"])
      (a "MTmVar" [a "MNZero"]) (a "MTmVar" [a "MNZero"]))

def shiftVarSuccRule : RuleSchema :=
  rule "megalodon-term-shift-var-succ"
    ["amount", "cutoff", "variable", "result"]
    [shiftTerm (m "amount") (m "cutoff")
      (a "MTmVar" [m "variable"]) (a "MTmVar" [m "result"])]
    (shiftTerm (m "amount") (a "MNSucc" [m "cutoff"])
      (a "MTmVar" [a "MNSucc" [m "variable"]])
      (a "MTmVar" [a "MNSucc" [m "result"]]))

def shiftNamedRule : RuleSchema :=
  rule "megalodon-term-shift-named" ["amount", "cutoff", "name"] []
    (shiftTerm (m "amount") (m "cutoff")
      (a "MTmNamed" [m "name"]) (a "MTmNamed" [m "name"]))

def shiftAppRule : RuleSchema :=
  rule "megalodon-term-shift-app"
    ["amount", "cutoff", "function", "argument",
      "functionResult", "argumentResult"]
    [ shiftTerm (m "amount") (m "cutoff")
        (m "function") (m "functionResult"),
      shiftTerm (m "amount") (m "cutoff")
        (m "argument") (m "argumentResult") ]
    (shiftTerm (m "amount") (m "cutoff")
      (a "MTmApp" [m "function", m "argument"])
      (a "MTmApp" [m "functionResult", m "argumentResult"]))

def shiftImpRule : RuleSchema :=
  rule "megalodon-term-shift-imp"
    ["amount", "cutoff", "domain", "codomain",
      "domainResult", "codomainResult"]
    [ shiftTerm (m "amount") (m "cutoff")
        (m "domain") (m "domainResult"),
      shiftTerm (m "amount") (m "cutoff")
        (m "codomain") (m "codomainResult") ]
    (shiftTerm (m "amount") (m "cutoff")
      (a "MTmImp" [m "domain", m "codomain"])
      (a "MTmImp" [m "domainResult", m "codomainResult"]))

def shiftAllRule : RuleSchema :=
  rule "megalodon-term-shift-all"
    ["amount", "cutoff", "type", "body", "bodyResult"]
    [shiftTerm (m "amount") (a "MNSucc" [m "cutoff"])
      (m "body") (m "bodyResult")]
    (shiftTerm (m "amount") (m "cutoff")
      (a "MTmAll" [m "type", m "body"])
      (a "MTmAll" [m "type", m "bodyResult"]))

def shiftProofNilRule : RuleSchema :=
  rule "megalodon-term-shift-proof-nil" ["amount", "cutoff"] []
    (shiftProofContext (m "amount") (m "cutoff")
      (a "MPfCtxNil") (a "MPfCtxNil"))

def shiftProofConsRule : RuleSchema :=
  rule "megalodon-term-shift-proof-cons"
    ["amount", "cutoff", "head", "tail", "headResult", "tailResult"]
    [ shiftTerm (m "amount") (m "cutoff") (m "head") (m "headResult"),
      shiftProofContext (m "amount") (m "cutoff")
        (m "tail") (m "tailResult") ]
    (shiftProofContext (m "amount") (m "cutoff")
      (a "MPfCtxCons" [m "head", m "tail"])
      (a "MPfCtxCons" [m "headResult", m "tailResult"]))

/-! ## Proof-carrying substitution -/

def substVarEqualRule : RuleSchema :=
  rule "megalodon-term-subst-var-equal"
    ["index", "replacement", "shifted"]
    [shiftTerm (m "index") (a "MNZero")
      (m "replacement") (m "shifted")]
    (substituteTerm (m "index") (m "replacement")
      (a "MTmVar" [m "index"]) (m "shifted"))

def substVarBelowRule : RuleSchema :=
  rule "megalodon-term-subst-var-below"
    ["index", "replacement", "variable"]
    [lessThan (m "variable") (m "index")]
    (substituteTerm (m "index") (m "replacement")
      (a "MTmVar" [m "variable"]) (a "MTmVar" [m "variable"]))

def substVarAboveRule : RuleSchema :=
  rule "megalodon-term-subst-var-above"
    ["index", "replacement", "predecessor"]
    [lessThan (m "index") (a "MNSucc" [m "predecessor"])]
    (substituteTerm (m "index") (m "replacement")
      (a "MTmVar" [a "MNSucc" [m "predecessor"]])
      (a "MTmVar" [m "predecessor"]))

def substNamedRule : RuleSchema :=
  rule "megalodon-term-subst-named" ["index", "replacement", "name"] []
    (substituteTerm (m "index") (m "replacement")
      (a "MTmNamed" [m "name"]) (a "MTmNamed" [m "name"]))

def substAppRule : RuleSchema :=
  rule "megalodon-term-subst-app"
    ["index", "replacement", "function", "argument",
      "functionResult", "argumentResult"]
    [ substituteTerm (m "index") (m "replacement")
        (m "function") (m "functionResult"),
      substituteTerm (m "index") (m "replacement")
        (m "argument") (m "argumentResult") ]
    (substituteTerm (m "index") (m "replacement")
      (a "MTmApp" [m "function", m "argument"])
      (a "MTmApp" [m "functionResult", m "argumentResult"]))

def substImpRule : RuleSchema :=
  rule "megalodon-term-subst-imp"
    ["index", "replacement", "domain", "codomain",
      "domainResult", "codomainResult"]
    [ substituteTerm (m "index") (m "replacement")
        (m "domain") (m "domainResult"),
      substituteTerm (m "index") (m "replacement")
        (m "codomain") (m "codomainResult") ]
    (substituteTerm (m "index") (m "replacement")
      (a "MTmImp" [m "domain", m "codomain"])
      (a "MTmImp" [m "domainResult", m "codomainResult"]))

def substAllRule : RuleSchema :=
  rule "megalodon-term-subst-all"
    ["index", "replacement", "type", "body", "bodyResult"]
    [substituteTerm (a "MNSucc" [m "index"]) (m "replacement")
      (m "body") (m "bodyResult")]
    (substituteTerm (m "index") (m "replacement")
      (a "MTmAll" [m "type", m "body"])
      (a "MTmAll" [m "type", m "bodyResult"]))

/-! ## Term typing -/

def typeVarZeroRule : RuleSchema :=
  rule "megalodon-term-type-var-zero" ["signature", "context", "type"] []
    (hasType (m "signature")
      (a "MTyCtxCons" [m "type", m "context"])
      (a "MTmVar" [a "MNZero"]) (m "type"))

def typeVarSuccRule : RuleSchema :=
  rule "megalodon-term-type-var-succ"
    ["signature", "context", "head", "variable", "type"]
    [hasType (m "signature") (m "context")
      (a "MTmVar" [m "variable"]) (m "type")]
    (hasType (m "signature")
      (a "MTyCtxCons" [m "head", m "context"])
      (a "MTmVar" [a "MNSucc" [m "variable"]]) (m "type"))

def typeNamedZeroRule : RuleSchema :=
  rule "megalodon-term-type-named-zero"
    ["name", "type", "signature", "context"] []
    (hasType (a "MSigCons" [m "name", m "type", m "signature"])
      (m "context") (a "MTmNamed" [m "name"]) (m "type"))

def typeNamedSuccRule : RuleSchema :=
  rule "megalodon-term-type-named-succ"
    ["headName", "headType", "signature", "context", "name", "type"]
    [hasType (m "signature") (m "context")
      (a "MTmNamed" [m "name"]) (m "type")]
    (hasType
      (a "MSigCons" [m "headName", m "headType", m "signature"])
      (m "context") (a "MTmNamed" [m "name"]) (m "type"))

def typeAppRule : RuleSchema :=
  rule "megalodon-term-type-app"
    ["signature", "context", "function", "argument", "domain", "codomain"]
    [ hasType (m "signature") (m "context") (m "function")
        (a "MTpArr" [m "domain", m "codomain"]),
      hasType (m "signature") (m "context") (m "argument") (m "domain") ]
    (hasType (m "signature") (m "context")
      (a "MTmApp" [m "function", m "argument"]) (m "codomain"))

def typeImpRule : RuleSchema :=
  rule "megalodon-term-type-imp"
    ["signature", "context", "domain", "codomain"]
    [ hasType (m "signature") (m "context") (m "domain") (a "MTpProp"),
      hasType (m "signature") (m "context") (m "codomain") (a "MTpProp") ]
    (hasType (m "signature") (m "context")
      (a "MTmImp" [m "domain", m "codomain"]) (a "MTpProp"))

def typeAllRule : RuleSchema :=
  rule "megalodon-term-type-all"
    ["signature", "context", "type", "body"]
    [hasType (m "signature")
      (a "MTyCtxCons" [m "type", m "context"])
      (m "body") (a "MTpProp")]
    (hasType (m "signature") (m "context")
      (a "MTmAll" [m "type", m "body"]) (a "MTpProp"))

/-! ## Proof checking -/

def proofHypZeroRule : RuleSchema :=
  rule "megalodon-term-proof-hyp-zero"
    ["signature", "termContext", "proofContext", "proposition"]
    [hasType (m "signature") (m "termContext")
      (m "proposition") (a "MTpProp")]
    (proves (m "signature") (m "termContext")
      (a "MPfCtxCons" [m "proposition", m "proofContext"])
      (m "proposition"))

def proofHypSuccRule : RuleSchema :=
  rule "megalodon-term-proof-hyp-succ"
    ["signature", "termContext", "proofContext", "head", "proposition"]
    [proves (m "signature") (m "termContext")
      (m "proofContext") (m "proposition")]
    (proves (m "signature") (m "termContext")
      (a "MPfCtxCons" [m "head", m "proofContext"])
      (m "proposition"))

def proofImpIntroRule : RuleSchema :=
  rule "megalodon-term-proof-imp-intro"
    ["signature", "termContext", "proofContext", "domain", "codomain"]
    [ hasType (m "signature") (m "termContext")
        (m "domain") (a "MTpProp"),
      proves (m "signature") (m "termContext")
        (a "MPfCtxCons" [m "domain", m "proofContext"])
        (m "codomain") ]
    (proves (m "signature") (m "termContext") (m "proofContext")
      (a "MTmImp" [m "domain", m "codomain"]))

def proofImpElimRule : RuleSchema :=
  rule "megalodon-term-proof-imp-elim"
    ["signature", "termContext", "proofContext", "domain", "codomain"]
    [ proves (m "signature") (m "termContext") (m "proofContext")
        (a "MTmImp" [m "domain", m "codomain"]),
      proves (m "signature") (m "termContext") (m "proofContext")
        (m "domain") ]
    (proves (m "signature") (m "termContext")
      (m "proofContext") (m "codomain"))

def proofAllIntroRule : RuleSchema :=
  rule "megalodon-term-proof-all-intro"
    ["signature", "termContext", "proofContext", "shiftedProofContext",
      "type", "body"]
    [ shiftProofContext (a "MNSucc" [a "MNZero"]) (a "MNZero")
        (m "proofContext") (m "shiftedProofContext"),
      proves (m "signature")
        (a "MTyCtxCons" [m "type", m "termContext"])
        (m "shiftedProofContext") (m "body") ]
    (proves (m "signature") (m "termContext") (m "proofContext")
      (a "MTmAll" [m "type", m "body"]))

def proofAllElimRule : RuleSchema :=
  rule "megalodon-term-proof-all-elim"
    ["signature", "termContext", "proofContext", "type", "body",
      "argument", "result"]
    [ proves (m "signature") (m "termContext") (m "proofContext")
        (a "MTmAll" [m "type", m "body"]),
      hasType (m "signature") (m "termContext")
        (m "argument") (m "type"),
      substituteTerm (a "MNZero") (m "argument")
        (m "body") (m "result") ]
    (proves (m "signature") (m "termContext")
      (m "proofContext") (m "result"))

def constructors : List (String × Nat) :=
  [ ("MNZero", 0), ("MNSucc", 1),
    ("MTpVar", 1), ("MTpProp", 0), ("MTpBase", 1), ("MTpArr", 2),
    ("MTpAll", 1), ("MTmVar", 1), ("MTmNamed", 1), ("MTmPrim", 1),
    ("MTmApp", 2), ("MTmLam", 2), ("MTmImp", 2), ("MTmAll", 2),
    ("MTmTypeApp", 2), ("MTmTypeLam", 1), ("MTmTypeAll", 1),
    ("MTyCtxNil", 0), ("MTyCtxCons", 2),
    ("MPfCtxNil", 0), ("MPfCtxCons", 2),
    ("MSigNil", 0), ("MSigCons", 3), ("PName", 0) ]

def rules : List RuleSchema :=
  [ addZeroRule, addSuccRule, lessZeroRule, lessSuccRule,
    shiftVarAtZeroRule, shiftVarBelowRule, shiftVarSuccRule, shiftNamedRule,
    shiftAppRule, shiftImpRule, shiftAllRule,
    shiftProofNilRule, shiftProofConsRule,
    substVarEqualRule, substVarBelowRule, substVarAboveRule, substNamedRule,
    substAppRule, substImpRule, substAllRule,
    typeVarZeroRule, typeVarSuccRule, typeNamedZeroRule, typeNamedSuccRule,
    typeAppRule, typeImpRule, typeAllRule,
    proofHypZeroRule, proofHypSuccRule, proofImpIntroRule, proofImpElimRule,
    proofAllIntroRule, proofAllElimRule ]

def definition : CalculusLanguageDef :=
  { name := "megalodon-term-quantified-kernel-v1"
    types := [expressionType]
    terms := constructors.map fun declaration =>
      expressionConstructor declaration.1 declaration.2
    equations := []
    rewrites := []
    judgments :=
      [ { head := "MAddNat", arity := 3 },
        { head := "MLessThan", arity := 2 },
        { head := "MShiftTerm", arity := 4 },
        { head := "MShiftProofContext", arity := 4 },
        { head := "MSubstituteTerm", arity := 4 },
        { head := "MTermHasType", arity := 4 },
        { head := "MTermProves", arity := 4 } ]
    rules }

def coGSLTDefinition : ExtendedLanguageDef calculusLayer :=
  definition.toExtended

def coGSLTSource : coGSLTDefinition.authoredGSLT.Term :=
  coGSLTDefinition.authoredSource

@[simp] theorem coGSLT_source_elaborates :
    calculusLayer.elaborate definition.toLanguageDef coGSLTSource =
      some definition.toCalculus :=
  definition.toExtended_elaborate_authoredSource

theorem language_validate : definition.toLanguageDef.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorOnly <;>
    simp [definition, constructors, expressionType, expressionConstructor,
      LanguageDef.typeNames, TypeDecl.plain, TermParam.typeExpr,
      TypeExpr.baseNames]

set_option maxRecDepth 100000 in
theorem definition_valid : definition.isValid = true := by
  have hvalidate : definition.toLanguageDef.validate = [] := by
    simpa [definition] using language_validate
  unfold CalculusLanguageDef.isValid CalculusLanguageDef.hasValidLocalRules
  rw [hvalidate]
  simp [definition, definition, constructors, rules,
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
    Pattern.evalHead, expressionType, expressionConstructor, rule, ruleId,
    addZeroRule, addSuccRule, lessZeroRule, lessSuccRule,
    shiftVarAtZeroRule, shiftVarBelowRule, shiftVarSuccRule, shiftNamedRule,
    shiftAppRule, shiftImpRule, shiftAllRule,
    shiftProofNilRule, shiftProofConsRule,
    substVarEqualRule, substVarBelowRule, substVarAboveRule, substNamedRule,
    substAppRule, substImpRule, substAllRule,
    typeVarZeroRule, typeVarSuccRule, typeNamedZeroRule, typeNamedSuccRule,
    typeAppRule, typeImpRule, typeAllRule,
    proofHypZeroRule, proofHypSuccRule, proofImpIntroRule, proofImpElimRule,
    proofAllIntroRule, proofAllElimRule, addNat, lessThan, shiftTerm,
    shiftProofContext, substituteTerm, hasType, proves, a, m,
    List.eraseDups, List.eraseDupsBy]
  simp (config := { maxSteps := 1000000, decide := true })

def validated : ValidatedCalculusLanguageDef := ⟨definition, definition_valid⟩

private def ruleInstance (id : String) (arguments : List Pattern) :
    RuleInstance :=
  { ruleId := ruleId id, arguments }

private def node (id : String) (arguments : List Pattern)
    (children : List RawProof := []) : RawProof :=
  .node (ruleInstance id arguments) children

/-! ## Actual `forall_identity` PFG witness -/

def pType : MathdataKernel.Tp := .arr (.base 0) .prop

def pDeclaration : MathdataKernel.TermDecl :=
  { name := "PName", type := pType }

def signature : Pattern := encodeSignature [pDeclaration]

def forallBody : MathdataKernel.Tm := .app (.named "PName") (.db 0)

def forallDomain : MathdataKernel.Tm := .all (.base 0) forallBody

def goal : Pattern :=
  proves signature (encodeTypeContext []) (encodeProofContext [])
    (encodeTm (.imp forallDomain forallDomain))

private def addZeroZeroArticle : RawProof :=
  node "megalodon-term-add-zero" [encodeNat 0]

private def shiftVarZeroByZeroArticle : RawProof :=
  node "megalodon-term-shift-var-zero"
    [encodeNat 0, encodeNat 0, encodeNat 0] [addZeroZeroArticle]

private def shiftVarZeroBelowOneArticle : RawProof :=
  node "megalodon-term-shift-var-below" [encodeNat 1, encodeNat 0]

private def shiftNamedArticle : RawProof :=
  node "megalodon-term-shift-named"
    [encodeNat 1, encodeNat 1, a "PName"]

private def shiftBodyArticle : RawProof :=
  node "megalodon-term-shift-app"
    [ encodeNat 1, encodeNat 1,
      encodeTm (.named "PName"), encodeTm (.db 0),
      encodeTm (.named "PName"), encodeTm (.db 0) ]
    [shiftNamedArticle, shiftVarZeroBelowOneArticle]

private def shiftDomainArticle : RawProof :=
  node "megalodon-term-shift-all"
    [encodeNat 1, encodeNat 0, encodeTp (.base 0),
      encodeTm forallBody, encodeTm forallBody]
    [shiftBodyArticle]

private def shiftNilArticle : RawProof :=
  node "megalodon-term-shift-proof-nil" [encodeNat 1, encodeNat 0]

private def shiftProofContextArticle : RawProof :=
  node "megalodon-term-shift-proof-cons"
    [encodeNat 1, encodeNat 0, encodeTm forallDomain,
      encodeProofContext [], encodeTm forallDomain, encodeProofContext []]
    [shiftDomainArticle, shiftNilArticle]

private def typeNamedPArticle (context : List MathdataKernel.Tp) : RawProof :=
  node "megalodon-term-type-named-zero"
    [a "PName", encodeTp pType, encodeSignature [],
      encodeTypeContext context]

private def typeVarZeroArticle (context : List MathdataKernel.Tp) : RawProof :=
  node "megalodon-term-type-var-zero"
    [signature, encodeTypeContext context, encodeTp (.base 0)]

private def typeBodyArticle (context : List MathdataKernel.Tp) : RawProof :=
  node "megalodon-term-type-app"
    [signature, encodeTypeContext (.base 0 :: context),
      encodeTm (.named "PName"),
      encodeTm (.db 0), encodeTp (.base 0), encodeTp .prop]
    [typeNamedPArticle (.base 0 :: context), typeVarZeroArticle context]

private def typeDomainArticle (context : List MathdataKernel.Tp) : RawProof :=
  node "megalodon-term-type-all"
    [signature, encodeTypeContext context, encodeTp (.base 0),
      encodeTm forallBody]
    [typeBodyArticle context]

private def proofHypArticle : RawProof :=
  node "megalodon-term-proof-hyp-zero"
    [signature, encodeTypeContext [.base 0], encodeProofContext [],
      encodeTm forallDomain]
    [typeDomainArticle [.base 0]]

private def substNamedArticle : RawProof :=
  node "megalodon-term-subst-named"
    [encodeNat 0, encodeTm (.db 0), a "PName"]

private def substVarArticle : RawProof :=
  node "megalodon-term-subst-var-equal"
    [encodeNat 0, encodeTm (.db 0), encodeTm (.db 0)]
    [shiftVarZeroByZeroArticle]

private def substBodyArticle : RawProof :=
  node "megalodon-term-subst-app"
    [encodeNat 0, encodeTm (.db 0), encodeTm (.named "PName"),
      encodeTm (.db 0), encodeTm (.named "PName"), encodeTm (.db 0)]
    [substNamedArticle, substVarArticle]

private def proofTermApplicationArticle : RawProof :=
  node "megalodon-term-proof-all-elim"
    [signature, encodeTypeContext [.base 0],
      encodeProofContext [forallDomain], encodeTp (.base 0),
      encodeTm forallBody, encodeTm (.db 0), encodeTm forallBody]
    [proofHypArticle, typeVarZeroArticle [], substBodyArticle]

private def proofAllIntroductionArticle : RawProof :=
  node "megalodon-term-proof-all-intro"
    [signature, encodeTypeContext [], encodeProofContext [forallDomain],
      encodeProofContext [forallDomain], encodeTp (.base 0),
      encodeTm forallBody]
    [shiftProofContextArticle, proofTermApplicationArticle]

def article : RawProof :=
  node "megalodon-term-proof-imp-intro"
    [signature, encodeTypeContext [], encodeProofContext [],
      encodeTm forallDomain, encodeTm forallDomain]
    [typeDomainArticle [], proofAllIntroductionArticle]

theorem forall_identity_accepted :
    checkRaw validated goal article = true := by
  simp [checkRaw, validated, definition, definition,
    constructors, rules, rule, addZeroRule, shiftVarAtZeroRule,
    shiftVarBelowRule, shiftNamedRule, shiftAppRule, shiftAllRule,
    shiftProofNilRule, shiftProofConsRule, substVarEqualRule, substNamedRule,
    substAppRule, typeVarZeroRule, typeNamedZeroRule, typeAppRule,
    typeAllRule, proofHypZeroRule, proofImpIntroRule, proofAllIntroRule,
    proofAllElimRule, article, proofAllIntroductionArticle,
    proofTermApplicationArticle, proofHypArticle, shiftProofContextArticle,
    shiftDomainArticle, shiftBodyArticle, shiftNamedArticle,
    shiftVarZeroBelowOneArticle, shiftNilArticle, typeDomainArticle,
    typeBodyArticle, typeNamedPArticle, typeVarZeroArticle,
    substBodyArticle, substNamedArticle, substVarArticle,
    shiftVarZeroByZeroArticle, addZeroZeroArticle, node, ruleInstance,
    instantiateRule?, CalculusLanguageDef.lookupRule?,
    RuleSchema.sideConditionsHold, instantiateSchema?, instantiateSchemas?,
    goal, signature, encodeSignature, pDeclaration,
    pType, forallDomain, forallBody, encodeTypeContext, encodeProofContext,
    encodeTm, encodeTp, encodeNat, proves, hasType, shiftProofContext,
    shiftTerm, substituteTerm, addNat, a, m, ruleId]
  simp (config := { maxSteps := 1000000, decide := true })
    [checkRaw, checkRawChildren, instantiateRule?, CalculusLanguageDef.lookupRule?,
      instantiateSchema?,
      instantiateSchemaAt?, instantiateSchemas?, instantiateSchemasAt?,
      lookupArgumentAt?]

def wrongGoal : Pattern :=
  proves signature (encodeTypeContext []) (encodeProofContext [])
    (encodeTm (.imp forallDomain forallBody))

theorem wrong_goal_rejected :
    checkRaw validated wrongGoal article = false := by
  cases hcheck : checkRaw validated wrongGoal article with
  | false => rfl
  | true =>
      exfalso
      have equality := checkRaw_goal_unique forall_identity_accepted hcheck
      simp [goal, wrongGoal, proves, encodeTm, forallDomain, forallBody,
        encodeTp, encodeNat, encodeTypeContext, encodeProofContext,
        signature, encodeSignature, pDeclaration, pType, a] at equality

end Mettapedia.Languages.Megalodon.TermQuantifiedKernel
