import Mettapedia.Languages.Megalodon.DefinitionConversionKernel
import Mettapedia.GSLT.LanguageDef.CalculusLanguageExtension

/-!
# Megalodon theory admission kernel

This layer presents a Megalodon theory as an ordered sequence of authority
transitions.  Primitive declarations extend the primitive inventory at their
exact index; parameters and definitions extend the retained term signature;
axioms extend the known inventory only after their propositions are checked;
and theorems extend it only after a proof article is replayed.

The order is semantic.  A theorem transition receives only the environment
produced by its source prefix, so later declarations cannot justify an earlier
item.  Axiom admission remains visibly distinct from theorem verification.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Megalodon.TheoryAdmissionKernel

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

/-- Lookup in the ordered primitive-type inventory. -/
def primitiveTypeAt
    (primitives index type : Pattern) : Pattern :=
  a "MPrimitiveTypeAt" [primitives, index, type]

/-- Append one primitive at exactly the supplied next index. -/
def primitiveAppendAt
    (primitives index type result : Pattern) : Pattern :=
  a "MPrimitiveAppendAt" [primitives, index, type, result]

/-- Term synthesis relative to both the theory primitive inventory and the
retained term signature. -/
def hasType
    (primitives signature typeDepth context term type : Pattern) : Pattern :=
  a "MEnvironmentTermHasType"
    [primitives, signature, typeDepth, context, term, type]

/-- Definition-aware proposition checking and reduction relative to the full
theory environment. -/
def propositionRepresentative
    (primitives declarations signature typeDepth termContext source target :
      Pattern) : Pattern :=
  a "MEnvironmentPropositionRepresentative"
    [primitives, declarations, signature, typeDepth, termContext, source,
      target]

/-- One authenticated source item changes one exact theory state. -/
def admits (initial item final : Pattern) : Pattern :=
  a "MMegalodonTheoryAdmits" [initial, item, final]

/-- Ordered closure of single-item admission. -/
def checks (initial items final : Pattern) : Pattern :=
  a "MMegalodonTheoryChecks" [initial, items, final]

/-! ## Primitive inventory -/

def primitiveTypeZeroRule : RuleSchema :=
  rule "megalodon-theory-primitive-type-zero"
    ["type", "tail"] []
    (primitiveTypeAt
      (a "MPrimCons" [m "type", m "tail"])
      (a "MNZero") (m "type"))

def primitiveTypeSuccRule : RuleSchema :=
  rule "megalodon-theory-primitive-type-succ"
    ["head", "tail", "index", "type"]
    [primitiveTypeAt (m "tail") (m "index") (m "type")]
    (primitiveTypeAt
      (a "MPrimCons" [m "head", m "tail"])
      (a "MNSucc" [m "index"]) (m "type"))

def primitiveAppendZeroRule : RuleSchema :=
  rule "megalodon-theory-primitive-append-zero"
    ["type"] []
    (primitiveAppendAt (a "MPrimNil") (a "MNZero") (m "type")
      (a "MPrimCons" [m "type", a "MPrimNil"]))

def primitiveAppendSuccRule : RuleSchema :=
  rule "megalodon-theory-primitive-append-succ"
    ["head", "tail", "index", "type", "result"]
    [primitiveAppendAt
      (m "tail") (m "index") (m "type") (m "result")]
    (primitiveAppendAt
      (a "MPrimCons" [m "head", m "tail"])
      (a "MNSucc" [m "index"]) (m "type")
      (a "MPrimCons" [m "head", m "result"]))

/-! ## Environment-indexed term synthesis -/

/-- A term derivation that uses only the retained signature remains valid in
an environment that also carries an independently checked primitive
inventory.  Primitive declarations enter the signature only through ordered
admission, so this bridge reuses the established polymorphic checker without
bypassing primitive-index validation. -/
def typeFromSignatureRule : RuleSchema :=
  rule "megalodon-theory-term-from-signature"
    ["primitives", "signature", "typeDepth", "context", "term", "type"]
    [ PolymorphicKernel.hasType
        (m "signature") (m "typeDepth") (m "context")
        (m "term") (m "type") ]
    (hasType (m "primitives") (m "signature") (m "typeDepth")
      (m "context") (m "term") (m "type"))

def typeVarZeroRule : RuleSchema :=
  rule "megalodon-theory-term-var-zero"
    ["primitives", "signature", "typeDepth", "context", "type"] []
    (hasType (m "primitives") (m "signature") (m "typeDepth")
      (a "MTyCtxCons" [m "type", m "context"])
      (a "MTmVar" [a "MNZero"]) (m "type"))

def typeVarSuccRule : RuleSchema :=
  rule "megalodon-theory-term-var-succ"
    ["primitives", "signature", "typeDepth", "context", "head",
      "variable", "type"]
    [hasType (m "primitives") (m "signature") (m "typeDepth")
      (m "context") (a "MTmVar" [m "variable"]) (m "type")]
    (hasType (m "primitives") (m "signature") (m "typeDepth")
      (a "MTyCtxCons" [m "head", m "context"])
      (a "MTmVar" [a "MNSucc" [m "variable"]]) (m "type"))

def typeNamedZeroRule : RuleSchema :=
  rule "megalodon-theory-term-named-zero"
    ["primitives", "name", "type", "signature", "typeDepth", "context"]
    []
    (hasType (m "primitives")
      (a "MSigCons" [m "name", m "type", m "signature"])
      (m "typeDepth") (m "context")
      (a "MTmNamed" [m "name"]) (m "type"))

def typeNamedSuccRule : RuleSchema :=
  rule "megalodon-theory-term-named-succ"
    ["primitives", "headName", "headType", "signature", "typeDepth",
      "context", "name", "type"]
    [hasType (m "primitives") (m "signature") (m "typeDepth")
      (m "context") (a "MTmNamed" [m "name"]) (m "type")]
    (hasType (m "primitives")
      (a "MSigCons" [m "headName", m "headType", m "signature"])
      (m "typeDepth") (m "context")
      (a "MTmNamed" [m "name"]) (m "type"))

def typePrimitiveRule : RuleSchema :=
  rule "megalodon-theory-term-primitive"
    ["primitives", "signature", "typeDepth", "context", "index", "type"]
    [primitiveTypeAt (m "primitives") (m "index") (m "type")]
    (hasType (m "primitives") (m "signature") (m "typeDepth")
      (m "context") (a "MTmPrim" [m "index"]) (m "type"))

def typeAppRule : RuleSchema :=
  rule "megalodon-theory-term-app"
    ["primitives", "signature", "typeDepth", "context", "function",
      "argument", "domain", "codomain"]
    [ hasType (m "primitives") (m "signature") (m "typeDepth")
        (m "context") (m "function")
        (a "MTpArr" [m "domain", m "codomain"]),
      hasType (m "primitives") (m "signature") (m "typeDepth")
        (m "context") (m "argument") (m "domain") ]
    (hasType (m "primitives") (m "signature") (m "typeDepth")
      (m "context") (a "MTmApp" [m "function", m "argument"])
      (m "codomain"))

def typeLamRule : RuleSchema :=
  rule "megalodon-theory-term-lam"
    ["primitives", "signature", "typeDepth", "context", "domain", "body",
      "codomain"]
    [ EnvironmentKernel.plainType (m "typeDepth") (m "domain"),
      hasType (m "primitives") (m "signature") (m "typeDepth")
        (a "MTyCtxCons" [m "domain", m "context"])
        (m "body") (m "codomain") ]
    (hasType (m "primitives") (m "signature") (m "typeDepth")
      (m "context") (a "MTmLam" [m "domain", m "body"])
      (a "MTpArr" [m "domain", m "codomain"]))

def typeImpRule : RuleSchema :=
  rule "megalodon-theory-term-imp"
    ["primitives", "signature", "typeDepth", "context", "domain",
      "codomain"]
    [ hasType (m "primitives") (m "signature") (m "typeDepth")
        (m "context") (m "domain") (a "MTpProp"),
      hasType (m "primitives") (m "signature") (m "typeDepth")
        (m "context") (m "codomain") (a "MTpProp") ]
    (hasType (m "primitives") (m "signature") (m "typeDepth")
      (m "context") (a "MTmImp" [m "domain", m "codomain"])
      (a "MTpProp"))

def typeAllRule : RuleSchema :=
  rule "megalodon-theory-term-all"
    ["primitives", "signature", "typeDepth", "context", "type", "body"]
    [ EnvironmentKernel.plainType (m "typeDepth") (m "type"),
      hasType (m "primitives") (m "signature") (m "typeDepth")
        (a "MTyCtxCons" [m "type", m "context"])
        (m "body") (a "MTpProp") ]
    (hasType (m "primitives") (m "signature") (m "typeDepth")
      (m "context") (a "MTmAll" [m "type", m "body"])
      (a "MTpProp"))

def typeTypeAppRule : RuleSchema :=
  rule "megalodon-theory-term-type-app"
    ["primitives", "signature", "typeDepth", "context", "function",
      "body", "type", "result"]
    [ hasType (m "primitives") (m "signature") (m "typeDepth")
        (m "context") (m "function") (a "MTpAll" [m "body"]),
      EnvironmentKernel.plainType (m "typeDepth") (m "type"),
      EnvironmentKernel.substituteType
        (a "MNZero") (m "type") (m "body") (m "result") ]
    (hasType (m "primitives") (m "signature") (m "typeDepth")
      (m "context") (a "MTmTypeApp" [m "function", m "type"])
      (m "result"))

def typeTypeLamRule : RuleSchema :=
  rule "megalodon-theory-term-type-lam"
    ["primitives", "signature", "typeDepth", "context", "shiftedContext",
      "body", "bodyType"]
    [ DefinitionConversionKernel.shiftTypeContext
        (a "MNSucc" [a "MNZero"]) (a "MNZero")
        (m "context") (m "shiftedContext"),
      hasType (m "primitives") (m "signature")
        (a "MNSucc" [m "typeDepth"])
        (m "shiftedContext") (m "body") (m "bodyType") ]
    (hasType (m "primitives") (m "signature") (m "typeDepth")
      (m "context") (a "MTmTypeLam" [m "body"])
      (a "MTpAll" [m "bodyType"]))

/-! ## Primitive-aware proof evidence -/

def propositionPlainRule : RuleSchema :=
  rule "megalodon-theory-proposition-plain"
    ["primitives", "declarations", "signature", "typeDepth",
      "termContext", "source", "target"]
    [ DefinitionConversionKernel.projectSignature
        (m "declarations") (m "signature"),
      hasType (m "primitives") (m "signature") (m "typeDepth")
        (m "termContext") (m "source") (a "MTpProp"),
      DefinitionConversionKernel.reductionPath
        (m "declarations") (m "source") (m "target") ]
    (propositionRepresentative
      (m "primitives") (m "declarations") (m "signature")
      (m "typeDepth") (m "termContext") (m "source") (m "target"))

def propositionTypeAllRule : RuleSchema :=
  rule "megalodon-theory-proposition-type-all"
    ["primitives", "declarations", "signature", "typeDepth",
      "termContext", "sourceBody", "targetBody"]
    [ propositionRepresentative
        (m "primitives") (m "declarations") (m "signature")
        (a "MNSucc" [m "typeDepth"]) (a "MTyCtxNil")
        (m "sourceBody") (m "targetBody") ]
    (propositionRepresentative
      (m "primitives") (m "declarations") (m "signature")
      (m "typeDepth") (m "termContext")
      (a "MTmTypeAll" [m "sourceBody"])
      (a "MTmTypeAll" [m "targetBody"]))

def proofHypZeroRule : RuleSchema :=
  rule "megalodon-theory-proof-hyp-zero"
    ["environment", "typeDepth", "termContext", "proofContext",
      "proposition"] []
    (DefinitionConversionKernel.fullProves
      (m "environment") (m "typeDepth") (m "termContext")
      (a "MPfCtxCons" [m "proposition", m "proofContext"])
      (m "proposition"))

def proofHypSuccRule : RuleSchema :=
  rule "megalodon-theory-proof-hyp-succ"
    ["environment", "typeDepth", "termContext", "proofContext", "head",
      "proposition"]
    [DefinitionConversionKernel.fullProves
      (m "environment") (m "typeDepth") (m "termContext")
      (m "proofContext") (m "proposition")]
    (DefinitionConversionKernel.fullProves
      (m "environment") (m "typeDepth") (m "termContext")
      (a "MPfCtxCons" [m "head", m "proofContext"])
      (m "proposition"))

def proofKnownRule : RuleSchema :=
  rule "megalodon-theory-proof-known"
    ["primitives", "declarations", "known", "typeDepth", "termContext",
      "proofContext", "identifier", "source", "target"]
    [ EnvironmentKernel.knownMember
        (m "known") (m "identifier") (m "source"),
      DefinitionConversionKernel.reductionPath
        (m "declarations") (m "source") (m "target") ]
    (DefinitionConversionKernel.fullProves
      (a "MFullEnvironment"
        [m "primitives", m "declarations", m "known"])
      (m "typeDepth") (m "termContext") (m "proofContext")
      (m "target"))

def proofImpIntroRule : RuleSchema :=
  rule "megalodon-theory-proof-imp-intro"
    ["primitives", "declarations", "signature", "known", "typeDepth",
      "termContext", "proofContext", "sourceDomain", "domain", "codomain"]
    [ propositionRepresentative
        (m "primitives") (m "declarations") (m "signature")
        (m "typeDepth") (m "termContext") (m "sourceDomain") (m "domain"),
      DefinitionConversionKernel.fullProves
        (a "MFullEnvironment"
          [m "primitives", m "declarations", m "known"])
        (m "typeDepth") (m "termContext")
        (a "MPfCtxCons" [m "domain", m "proofContext"])
        (m "codomain") ]
    (DefinitionConversionKernel.fullProves
      (a "MFullEnvironment"
        [m "primitives", m "declarations", m "known"])
      (m "typeDepth") (m "termContext") (m "proofContext")
      (a "MTmImp" [m "domain", m "codomain"]))

def proofImpElimRule : RuleSchema :=
  rule "megalodon-theory-proof-imp-elim"
    ["environment", "typeDepth", "termContext", "proofContext", "domain",
      "codomain"]
    [ DefinitionConversionKernel.fullProves
        (m "environment") (m "typeDepth") (m "termContext")
        (m "proofContext") (a "MTmImp" [m "domain", m "codomain"]),
      DefinitionConversionKernel.fullProves
        (m "environment") (m "typeDepth") (m "termContext")
        (m "proofContext") (m "domain") ]
    (DefinitionConversionKernel.fullProves
      (m "environment") (m "typeDepth") (m "termContext")
      (m "proofContext") (m "codomain"))

def proofAllIntroRule : RuleSchema :=
  rule "megalodon-theory-proof-all-intro"
    ["environment", "typeDepth", "termContext", "proofContext",
      "shiftedProofContext", "type", "body"]
    [ EnvironmentKernel.plainType (m "typeDepth") (m "type"),
      EnvironmentKernel.shiftProofContext
        (a "MNSucc" [a "MNZero"]) (a "MNZero")
        (m "proofContext") (m "shiftedProofContext"),
      DefinitionConversionKernel.fullProves
        (m "environment") (m "typeDepth")
        (a "MTyCtxCons" [m "type", m "termContext"])
        (m "shiftedProofContext") (m "body") ]
    (DefinitionConversionKernel.fullProves
      (m "environment") (m "typeDepth") (m "termContext")
      (m "proofContext") (a "MTmAll" [m "type", m "body"]))

def proofAllElimRule : RuleSchema :=
  rule "megalodon-theory-proof-all-elim"
    ["primitives", "declarations", "signature", "known", "typeDepth",
      "termContext", "proofContext", "type", "body", "argument",
      "argumentRepresentative", "substituted", "result"]
    [ DefinitionConversionKernel.fullProves
        (a "MFullEnvironment"
          [m "primitives", m "declarations", m "known"])
        (m "typeDepth") (m "termContext") (m "proofContext")
        (a "MTmAll" [m "type", m "body"]),
      DefinitionConversionKernel.projectSignature
        (m "declarations") (m "signature"),
      hasType (m "primitives") (m "signature") (m "typeDepth")
        (m "termContext") (m "argument") (m "type"),
      DefinitionConversionKernel.reductionPath
        (m "declarations") (m "argument") (m "argumentRepresentative"),
      EnvironmentKernel.substituteTerm
        (a "MNZero") (m "argumentRepresentative")
        (m "body") (m "substituted"),
      DefinitionConversionKernel.reductionPath
        (m "declarations") (m "substituted") (m "result") ]
    (DefinitionConversionKernel.fullProves
      (a "MFullEnvironment"
        [m "primitives", m "declarations", m "known"])
      (m "typeDepth") (m "termContext") (m "proofContext")
      (m "result"))

def proofTypeElimRule : RuleSchema :=
  rule "megalodon-theory-proof-type-elim"
    ["environment", "typeDepth", "termContext", "proofContext", "body",
      "type", "result"]
    [ DefinitionConversionKernel.fullProves
        (m "environment") (m "typeDepth") (m "termContext")
        (m "proofContext") (a "MTmTypeAll" [m "body"]),
      EnvironmentKernel.plainType (m "typeDepth") (m "type"),
      EnvironmentKernel.substituteTypeInTerm
        (a "MNZero") (m "type") (m "body") (m "result") ]
    (DefinitionConversionKernel.fullProves
      (m "environment") (m "typeDepth") (m "termContext")
      (m "proofContext") (m "result"))

def proofTypeIntroRule : RuleSchema :=
  rule "megalodon-theory-proof-type-intro"
    ["environment", "typeDepth", "body"]
    [DefinitionConversionKernel.fullProves
      (m "environment") (a "MNSucc" [m "typeDepth"])
      (a "MTyCtxNil") (a "MPfCtxNil") (m "body")]
    (DefinitionConversionKernel.fullProves
      (m "environment") (m "typeDepth")
      (a "MTyCtxNil") (a "MPfCtxNil")
      (a "MTmTypeAll" [m "body"]))

/-! ## Ordered theory transitions -/

def admitPrimitiveRule : RuleSchema :=
  rule "megalodon-theory-admit-primitive"
    ["primitives", "declarations", "known", "identifier", "index", "type",
      "resultPrimitives"]
    [ DefinitionConversionKernel.polyType (a "MNZero") (m "type"),
      primitiveAppendAt (m "primitives") (m "index") (m "type")
        (m "resultPrimitives") ]
    (admits
      (a "MFullEnvironment"
        [m "primitives", m "declarations", m "known"])
      (a "MTheoryPrimitive" [m "identifier", m "index", m "type"])
      (a "MFullEnvironment"
        [ m "resultPrimitives",
          a "MDeclDefinition"
            [m "identifier", m "type", a "MTmPrim" [m "index"],
              m "declarations"],
          m "known" ]))

def admitParameterRule : RuleSchema :=
  rule "megalodon-theory-admit-parameter"
    ["primitives", "declarations", "known", "identifier", "type"]
    [DefinitionConversionKernel.polyType (a "MNZero") (m "type")]
    (admits
      (a "MFullEnvironment"
        [m "primitives", m "declarations", m "known"])
      (a "MTheoryParameter" [m "identifier", m "type"])
      (a "MFullEnvironment"
        [ m "primitives",
          a "MDeclParameter" [m "identifier", m "type", m "declarations"],
          m "known" ]))

def admitDefinitionRule : RuleSchema :=
  rule "megalodon-theory-admit-definition"
    ["primitives", "declarations", "signature", "known", "identifier",
      "type", "body"]
    [ DefinitionConversionKernel.projectSignature
        (m "declarations") (m "signature"),
      DefinitionConversionKernel.polyType (a "MNZero") (m "type"),
      hasType (m "primitives") (m "signature") (a "MNZero")
        (a "MTyCtxNil") (m "body") (m "type") ]
    (admits
      (a "MFullEnvironment"
        [m "primitives", m "declarations", m "known"])
      (a "MTheoryDefinition" [m "identifier", m "type", m "body"])
      (a "MFullEnvironment"
        [ m "primitives",
          a "MDeclDefinition"
            [m "identifier", m "type", m "body", m "declarations"],
          m "known" ]))

def admitAxiomRule : RuleSchema :=
  rule "megalodon-theory-admit-axiom"
    ["primitives", "declarations", "signature", "known", "identifier",
      "proposition"]
    [ DefinitionConversionKernel.projectSignature
        (m "declarations") (m "signature"),
      hasType (m "primitives") (m "signature") (a "MNZero")
        (a "MTyCtxNil") (m "proposition") (a "MTpProp") ]
    (admits
      (a "MFullEnvironment"
        [m "primitives", m "declarations", m "known"])
      (a "MTheoryAxiom" [m "identifier", m "proposition"])
      (a "MFullEnvironment"
        [ m "primitives", m "declarations",
          a "MKnownCons" [m "identifier", m "proposition", m "known"] ]))

def admitTheoremRule : RuleSchema :=
  rule "megalodon-theory-admit-theorem"
    ["primitives", "declarations", "known", "identifier", "proposition"]
    [DefinitionConversionKernel.fullProves
      (a "MFullEnvironment"
        [m "primitives", m "declarations", m "known"])
      (a "MNZero") (a "MTyCtxNil") (a "MPfCtxNil")
      (m "proposition")]
    (admits
      (a "MFullEnvironment"
        [m "primitives", m "declarations", m "known"])
      (a "MTheoryTheorem" [m "identifier", m "proposition"])
      (a "MFullEnvironment"
        [ m "primitives", m "declarations",
          a "MKnownCons" [m "identifier", m "proposition", m "known"] ]))

def checksNilRule : RuleSchema :=
  rule "megalodon-theory-checks-nil" ["environment"] []
    (checks (m "environment") (a "MTheoryItemsNil") (m "environment"))

def checksConsRule : RuleSchema :=
  rule "megalodon-theory-checks-cons"
    ["initial", "item", "items", "middle", "final"]
    [ admits (m "initial") (m "item") (m "middle"),
      checks (m "middle") (m "items") (m "final") ]
    (checks (m "initial")
      (a "MTheoryItemsCons" [m "item", m "items"])
      (m "final"))

def additionalConstructors : List (String × Nat) :=
  [ ("MTheoryPrimitive", 3), ("MTheoryParameter", 2),
    ("MTheoryDefinition", 3), ("MTheoryAxiom", 2),
    ("MTheoryTheorem", 2), ("MTheoryItemsNil", 0),
    ("MTheoryItemsCons", 2),
    ("MTheoryCanaryPrimitive", 0), ("MTheoryCanaryAxiom", 0),
    ("MTheoryCanaryTheorem", 0) ]

def additionalJudgments : List JudgmentDecl :=
  [ { head := "MPrimitiveTypeAt", arity := 3 },
    { head := "MPrimitiveAppendAt", arity := 4 },
    { head := "MEnvironmentTermHasType", arity := 6 },
    { head := "MEnvironmentPropositionRepresentative", arity := 7 },
    { head := "MMegalodonTheoryAdmits", arity := 3 },
    { head := "MMegalodonTheoryChecks", arity := 3 } ]

def additionalRules : List RuleSchema :=
  [ primitiveTypeZeroRule, primitiveTypeSuccRule,
    primitiveAppendZeroRule, primitiveAppendSuccRule,
    typeFromSignatureRule,
    typeVarZeroRule, typeVarSuccRule, typeNamedZeroRule, typeNamedSuccRule,
    typePrimitiveRule, typeAppRule, typeLamRule, typeImpRule, typeAllRule,
    typeTypeAppRule, typeTypeLamRule,
    propositionPlainRule, propositionTypeAllRule,
    proofHypZeroRule, proofHypSuccRule, proofKnownRule,
    proofImpIntroRule, proofImpElimRule, proofAllIntroRule,
    proofAllElimRule, proofTypeElimRule, proofTypeIntroRule,
    admitPrimitiveRule, admitParameterRule, admitDefinitionRule,
    admitAxiomRule, admitTheoremRule, checksNilRule, checksConsRule ]

def definition : CalculusLanguageDef :=
  { DefinitionConversionKernel.definition with
    name := "megalodon-theory-admission-kernel-v1"
    terms := DefinitionConversionKernel.definition.terms ++
      additionalConstructors.map fun declaration =>
        TermQuantifiedKernel.expressionConstructor declaration.1 declaration.2
    judgments := DefinitionConversionKernel.definition.judgments ++
      additionalJudgments
    rules := DefinitionConversionKernel.definition.rules ++ additionalRules }

def admissionExtension :
    CalculusLanguageExtension :=
  { newTerms := additionalConstructors.map fun declaration =>
      TermQuantifiedKernel.expressionConstructor declaration.1 declaration.2
    newJudgments := additionalJudgments
    newRules := additionalRules
    rename := some definition.name }

@[simp] theorem admissionExtension_apply :
    admissionExtension.apply DefinitionConversionKernel.definition =
      definition := by
  rfl

theorem admissionExtension_disjoint :
    admissionExtension.disjointFrom
      DefinitionConversionKernel.definition = true := by
  rfl

private theorem admissionTermDisjoint
    {newTerm oldTerm : GrammarRule}
    (newMember : newTerm ∈ admissionExtension.newTerms)
    (oldMember : oldTerm ∈
      DefinitionConversionKernel.definition.toLanguageDef.terms) :
    newTerm.label ≠ oldTerm.label := by
  have disjoint := admissionExtension_disjoint
  unfold CalculusLanguageExtension.disjointFrom at disjoint
  simp only [Bool.and_eq_true] at disjoint
  have fresh := List.all_eq_true.mp disjoint.1.1 newTerm newMember
  intro equalLabels
  have collision :
      DefinitionConversionKernel.definition.toLanguageDef.terms.any
          (fun existing => existing.label == newTerm.label) = true :=
    List.any_eq_true.mpr
      ⟨oldTerm, oldMember, by simp [equalLabels]⟩
  simp [collision] at fresh

private theorem admissionJudgmentDisjoint
    {newJudgment oldJudgment : JudgmentDecl}
    (newMember : newJudgment ∈ admissionExtension.newJudgments)
    (oldMember : oldJudgment ∈
      DefinitionConversionKernel.definition.judgments) :
    newJudgment.head ≠ oldJudgment.head := by
  have disjoint := admissionExtension_disjoint
  unfold CalculusLanguageExtension.disjointFrom at disjoint
  simp only [Bool.and_eq_true] at disjoint
  have fresh := List.all_eq_true.mp disjoint.1.2 newJudgment newMember
  intro equalHeads
  have collision :
      DefinitionConversionKernel.definition.judgments.any
          (fun existing => existing.head == newJudgment.head) = true :=
    List.any_eq_true.mpr
      ⟨oldJudgment, oldMember, by simp [equalHeads]⟩
  rw [collision] at fresh
  simp at fresh

private theorem constructorLookup_preserved (head : String) (arity : Nat)
    (sourceValid :
      languageHasConstructorArity
        DefinitionConversionKernel.definition.toLanguageDef head arity = true) :
    languageHasConstructorArity definition.toLanguageDef head arity = true := by
  unfold languageHasConstructorArity at sourceValid ⊢
  rw [show definition.toLanguageDef.terms =
      DefinitionConversionKernel.definition.toLanguageDef.terms ++
        admissionExtension.newTerms by rfl,
    List.filter_append]
  generalize sourceFiltered :
      DefinitionConversionKernel.definition.toLanguageDef.terms.filter
        (fun declaration => declaration.label == head) = filtered at sourceValid ⊢
  cases filtered with
  | nil => simp at sourceValid
  | cons declaration tail =>
      cases tail with
      | nil =>
          have declarationFiltered :
              declaration ∈
                DefinitionConversionKernel.definition.toLanguageDef.terms.filter
                  (fun candidate => candidate.label == head) := by
            rw [sourceFiltered]
            simp
          have declarationMember := (List.mem_filter.mp declarationFiltered).1
          have declarationLabel : declaration.label = head := by
            simpa using (List.mem_filter.mp declarationFiltered).2
          have extensionFiltered :
              admissionExtension.newTerms.filter
                  (fun candidate => candidate.label == head) = [] := by
            refine List.filter_eq_nil_iff.mpr ?_
            intro candidate candidateMember
            have labelsDiffer :=
              admissionTermDisjoint candidateMember declarationMember
            have candidateLabel : candidate.label ≠ head := by
              simpa [declarationLabel] using labelsDiffer
            simp [candidateLabel]
          rw [extensionFiltered]
          simpa [sourceFiltered] using sourceValid
      | cons second rest => simp at sourceValid

private theorem judgmentLookup_preserved (head : String) (arity : Nat)
    (sourceValid :
      (DefinitionConversionKernel.definition.lookupJudgment?
        head arity).isSome = true) :
    (definition.lookupJudgment? head arity).isSome = true := by
  unfold CalculusLanguageDef.lookupJudgment? at sourceValid ⊢
  rw [show definition.judgments =
      DefinitionConversionKernel.definition.judgments ++
        admissionExtension.newJudgments by rfl,
    List.filter_append]
  generalize sourceFiltered :
      DefinitionConversionKernel.definition.judgments.filter
        (fun declaration =>
          declaration.head == head && declaration.arity == arity) = filtered at sourceValid ⊢
  cases filtered with
  | nil => simp at sourceValid
  | cons declaration tail =>
      cases tail with
      | nil =>
          have declarationFiltered :
              declaration ∈
                DefinitionConversionKernel.definition.judgments.filter
                  (fun candidate =>
                    candidate.head == head && candidate.arity == arity) := by
            rw [sourceFiltered]
            simp
          have declarationMember := (List.mem_filter.mp declarationFiltered).1
          have declarationHead : declaration.head = head := by
            have accepted := (List.mem_filter.mp declarationFiltered).2
            simp only [Bool.and_eq_true, beq_iff_eq] at accepted
            exact accepted.1
          have extensionFiltered :
              admissionExtension.newJudgments.filter
                  (fun candidate =>
                    candidate.head == head && candidate.arity == arity) = [] := by
            refine List.filter_eq_nil_iff.mpr ?_
            intro candidate candidateMember
            have headsDiffer :=
              admissionJudgmentDisjoint candidateMember declarationMember
            have candidateHead : candidate.head ≠ head := by
              simpa [declarationHead] using headsDiffer
            simp [candidateHead]
          rw [extensionFiltered]
          simp at sourceValid ⊢
      | cons second rest => simp at sourceValid

mutual
  private theorem fixedConstructorsValid_preserved (pattern : Pattern)
      (sourceValid :
        fixedConstructorsValid
          DefinitionConversionKernel.definition.toLanguageDef pattern = true) :
      fixedConstructorsValid definition.toLanguageDef pattern = true := by
    cases pattern with
    | bvar index => simp [fixedConstructorsValid]
    | fvar name => simp [fixedConstructorsValid]
    | apply head arguments =>
        simp only [fixedConstructorsValid, Bool.and_eq_true] at sourceValid ⊢
        exact ⟨constructorLookup_preserved head arguments.length sourceValid.1,
          fixedConstructorListsValid_preserved arguments sourceValid.2⟩
    | lambda binder body =>
        simp only [fixedConstructorsValid] at sourceValid ⊢
        exact fixedConstructorsValid_preserved body sourceValid
    | multiLambda arity binder body =>
        simp only [fixedConstructorsValid] at sourceValid ⊢
        exact fixedConstructorsValid_preserved body sourceValid
    | subst body replacement =>
        simp only [fixedConstructorsValid, Bool.and_eq_true] at sourceValid ⊢
        exact ⟨fixedConstructorsValid_preserved body sourceValid.1,
          fixedConstructorsValid_preserved replacement sourceValid.2⟩
    | collection kind elements rest =>
        simp only [fixedConstructorsValid] at sourceValid ⊢
        exact fixedConstructorListsValid_preserved elements sourceValid

  private theorem fixedConstructorListsValid_preserved (patterns : List Pattern)
      (sourceValid :
        fixedConstructorListsValid
          DefinitionConversionKernel.definition.toLanguageDef patterns = true) :
      fixedConstructorListsValid definition.toLanguageDef patterns = true := by
    cases patterns with
    | nil => simp [fixedConstructorListsValid]
    | cons pattern patterns =>
        simp only [fixedConstructorListsValid, Bool.and_eq_true] at sourceValid ⊢
        exact ⟨fixedConstructorsValid_preserved pattern sourceValid.1,
          fixedConstructorListsValid_preserved patterns sourceValid.2⟩
end

private theorem judgmentSchemaValid_preserved (judgment : Pattern)
    (sourceValid :
      DefinitionConversionKernel.definition.judgmentSchemaValid judgment =
        true) :
    definition.judgmentSchemaValid judgment = true := by
  cases judgment with
  | apply head arguments =>
      simp only [CalculusLanguageDef.judgmentSchemaValid, Bool.and_eq_true] at sourceValid ⊢
      exact ⟨judgmentLookup_preserved head arguments.length sourceValid.1,
        fixedConstructorListsValid_preserved arguments sourceValid.2⟩
  | bvar index => simp [CalculusLanguageDef.judgmentSchemaValid] at sourceValid
  | fvar name => simp [CalculusLanguageDef.judgmentSchemaValid] at sourceValid
  | lambda binder body =>
      simp [CalculusLanguageDef.judgmentSchemaValid] at sourceValid
  | multiLambda arity binder body =>
      simp [CalculusLanguageDef.judgmentSchemaValid] at sourceValid
  | subst body replacement =>
      simp [CalculusLanguageDef.judgmentSchemaValid] at sourceValid
  | collection kind elements rest =>
      simp [CalculusLanguageDef.judgmentSchemaValid] at sourceValid

private theorem ruleIsValidIn_preserved (candidate : RuleSchema)
    (sourceValid :
      RuleSchema.isValidIn DefinitionConversionKernel.definition candidate =
        true) :
    RuleSchema.isValidIn definition candidate = true := by
  unfold RuleSchema.isValidIn at sourceValid ⊢
  simp only [Bool.and_eq_true] at sourceValid ⊢
  refine ⟨sourceValid.1, ?_, sourceValid.2.2⟩
  apply List.all_eq_true.mpr
  intro judgment member
  exact judgmentSchemaValid_preserved judgment
    (List.all_eq_true.mp sourceValid.2.1 judgment member)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 12000000 in
theorem definition_valid : definition.isValid = true := by
  have hbaseValid := DefinitionConversionKernel.definition_valid
  unfold CalculusLanguageDef.isValid at hbaseValid
  simp only [Bool.and_eq_true] at hbaseValid
  have hbaseV1 := hbaseValid.1.1.1
  have hbaseJudgments := hbaseValid.1.1.2
  have hbaseRulesIn := hbaseValid.1.2
  have hbaseConversion := hbaseValid.2
  unfold CalculusLanguageDef.hasValidLocalRules at hbaseV1
  simp only [Bool.and_eq_true] at hbaseV1
  have hbaseRulesV1 := hbaseV1.1.2
  change DefinitionConversionKernel.definition.rules.all
      RuleSchema.isLocallyValid = true at hbaseRulesV1
  change DefinitionConversionKernel.definition.rules.all
      (RuleSchema.isValidIn DefinitionConversionKernel.definition) = true at hbaseRulesIn
  have hbaseRulesInTarget :
      DefinitionConversionKernel.definition.rules.all
        (RuleSchema.isValidIn definition) = true := by
    apply List.all_eq_true.mpr
    intro candidate member
    exact ruleIsValidIn_preserved candidate
      (List.all_eq_true.mp hbaseRulesIn candidate member)
  have hadditionalRulesIn :
      additionalRules.all (RuleSchema.isValidIn definition) = true := by
    simp (config := { maxSteps := 12000000, decide := true })
      [ definition, definition, additionalConstructors,
        additionalJudgments, additionalRules,
        CalculusLanguageDef.lookupJudgment?, RuleSchema.isValidIn,
        RuleSchema.isLocallyValid, RuleSchema.metavariableNames,
        RuleSchema.occurrences, RuleSchema.patterns,
        patternMetavariableOccurrencesAt, patternsMetavariableOccurrencesAt,
        patternHasNoCollectionRest, patternsHaveNoCollectionRest,
        CalculusLanguageDef.judgmentSchemaValid, fixedConstructorsValid,
        fixedConstructorListsValid, languageHasConstructorArity,
        Pattern.isWellScoped, Pattern.isWellScopedAt,
        Pattern.isWellScopedListAt, Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList,
        primitiveTypeZeroRule, primitiveTypeSuccRule,
        primitiveAppendZeroRule, primitiveAppendSuccRule,
        typeFromSignatureRule,
        typeVarZeroRule, typeVarSuccRule, typeNamedZeroRule,
        typeNamedSuccRule, typePrimitiveRule, typeAppRule, typeLamRule,
        typeImpRule, typeAllRule, typeTypeAppRule, typeTypeLamRule,
        propositionPlainRule, propositionTypeAllRule,
        proofHypZeroRule, proofHypSuccRule, proofKnownRule,
        proofImpIntroRule, proofImpElimRule, proofAllIntroRule,
        proofAllElimRule, proofTypeElimRule, proofTypeIntroRule,
        admitPrimitiveRule, admitParameterRule, admitDefinitionRule,
        admitAxiomRule, admitTheoremRule, checksNilRule, checksConsRule,
        primitiveTypeAt, primitiveAppendAt, hasType,
        propositionRepresentative, admits, checks, rule, ruleId, a, m,
        EnvironmentKernel.plainType, EnvironmentKernel.knownMember,
        EnvironmentKernel.shiftProofContext,
        EnvironmentKernel.substituteType,
        EnvironmentKernel.substituteTypeInTerm,
        EnvironmentKernel.substituteTerm, EnvironmentKernel.a,
        DefinitionConversionKernel.projectSignature,
        DefinitionConversionKernel.polyType,
        DefinitionConversionKernel.shiftTypeContext,
        DefinitionConversionKernel.reductionPath,
        DefinitionConversionKernel.fullProves, DefinitionConversionKernel.a,
        PolymorphicKernel.hasType, PolymorphicKernel.a]
  have htargetRulesIn :
      definition.rules.all (RuleSchema.isValidIn definition) = true := by
    change (DefinitionConversionKernel.definition.rules ++ additionalRules).all
      (RuleSchema.isValidIn definition) = true
    simp only [List.all_append, hbaseRulesInTarget, hadditionalRulesIn,
      Bool.and_self]
  have hvalidate : definition.toLanguageDef.validate = [] := by
    apply LanguageDef.validate_eq_nil_of_constructorOnly <;>
      simp [definition, definition, additionalConstructors,
        DefinitionConversionKernel.definition,
        DefinitionConversionKernel.additionalConstructors,
        DefinitionConversionKernel.definitionParameterName,
        DefinitionConversionKernel.identityDefinitionName,
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
  have hstatic :
      definition.hasValidLocalRules = true ∧
        definition.judgmentSignatureValid = true ∧
        definition.conversionDeclarationValid = true := by
    unfold CalculusLanguageDef.hasValidLocalRules
    rw [hvalidate]
    simp (config := { maxSteps := 12000000, decide := true })
      [ definition, definition, additionalConstructors,
        additionalJudgments, additionalRules,
        CalculusLanguageDef.ruleIds,
        RuleSchema.isLocallyValid, RuleSchema.metavariableNames,
        RuleSchema.occurrences, RuleSchema.patterns,
        patternMetavariableOccurrencesAt, patternsMetavariableOccurrencesAt,
        patternHasNoCollectionRest, patternsHaveNoCollectionRest,
        Pattern.isWellScoped, Pattern.isWellScopedAt,
        Pattern.isWellScopedListAt, Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList,
        primitiveTypeZeroRule, primitiveTypeSuccRule,
        primitiveAppendZeroRule, primitiveAppendSuccRule,
        typeFromSignatureRule,
        typeVarZeroRule, typeVarSuccRule, typeNamedZeroRule,
        typeNamedSuccRule, typePrimitiveRule, typeAppRule, typeLamRule,
        typeImpRule, typeAllRule, typeTypeAppRule, typeTypeLamRule,
        propositionPlainRule, propositionTypeAllRule,
        proofHypZeroRule, proofHypSuccRule, proofKnownRule,
        proofImpIntroRule, proofImpElimRule, proofAllIntroRule,
        proofAllElimRule, proofTypeElimRule, proofTypeIntroRule,
        admitPrimitiveRule, admitParameterRule, admitDefinitionRule,
        admitAxiomRule, admitTheoremRule, checksNilRule, checksConsRule,
        primitiveTypeAt, primitiveAppendAt, hasType,
        propositionRepresentative, admits, checks, rule, ruleId, a, m,
        EnvironmentKernel.plainType, EnvironmentKernel.knownMember,
        EnvironmentKernel.shiftProofContext,
        EnvironmentKernel.substituteType,
        EnvironmentKernel.substituteTypeInTerm,
        EnvironmentKernel.substituteTerm, EnvironmentKernel.a,
        DefinitionConversionKernel.projectSignature,
        DefinitionConversionKernel.polyType,
        DefinitionConversionKernel.shiftTypeContext,
        DefinitionConversionKernel.reductionPath,
        DefinitionConversionKernel.fullProves,
        DefinitionConversionKernel.a, PolymorphicKernel.hasType,
        PolymorphicKernel.a,
        hbaseRulesV1]
  unfold CalculusLanguageDef.isValid
  simp only [Bool.and_eq_true]
  exact ⟨⟨⟨hstatic.1, hstatic.2.1⟩, htargetRulesIn⟩, hstatic.2.2⟩

def validated : ValidatedCalculusLanguageDef := ⟨definition, definition_valid⟩

private theorem lookupBaseRule (id : RuleId) (candidate : RuleSchema)
    (lookup : DefinitionConversionKernel.definition.lookupRule? id =
      some candidate) :
    definition.lookupRule? id = some candidate :=
  CalculusLanguageDef.lookupRule?_append_of_eq_some
    DefinitionConversionKernel.definition additionalRules lookup

private theorem lookupAdditionalRule (id : String) (candidate : RuleSchema)
    (missing : DefinitionConversionKernel.definition.lookupRule?
      (ruleId id) = none)
    (lookup : additionalRules.find?
      (fun existing => decide (existing.id = ruleId id)) = some candidate) :
    definition.lookupRule? (ruleId id) = some candidate := by
  unfold CalculusLanguageDef.lookupRule? at missing ⊢
  change List.find? (fun existing => decide (existing.id = ruleId id))
      (DefinitionConversionKernel.definition.rules ++ additionalRules) =
    some candidate
  rw [List.find?_append]
  rw [missing]
  exact lookup

@[simp] private theorem lookup_checksConsRule :
    definition.lookupRule?
        ({ value := "megalodon-theory-checks-cons" } : RuleId) =
      some checksConsRule :=
  lookupAdditionalRule _ _ (by rfl) (by rfl)

@[simp] private theorem lookup_checksNilRule :
    definition.lookupRule?
        ({ value := "megalodon-theory-checks-nil" } : RuleId) =
      some checksNilRule :=
  lookupAdditionalRule _ _ (by rfl) (by rfl)

@[simp] private theorem lookup_admitPrimitiveRule :
    definition.lookupRule?
        ({ value := "megalodon-theory-admit-primitive" } : RuleId) =
      some admitPrimitiveRule :=
  lookupAdditionalRule _ _ (by rfl) (by rfl)

@[simp] private theorem lookup_admitAxiomRule :
    definition.lookupRule?
        ({ value := "megalodon-theory-admit-axiom" } : RuleId) =
      some admitAxiomRule :=
  lookupAdditionalRule _ _ (by rfl) (by rfl)

@[simp] private theorem lookup_admitTheoremRule :
    definition.lookupRule?
        ({ value := "megalodon-theory-admit-theorem" } : RuleId) =
      some admitTheoremRule :=
  lookupAdditionalRule _ _ (by rfl) (by rfl)

@[simp] private theorem lookup_primitiveAppendZeroRule :
    definition.lookupRule?
        ({ value := "megalodon-theory-primitive-append-zero" } : RuleId) =
      some primitiveAppendZeroRule :=
  lookupAdditionalRule _ _ (by rfl) (by rfl)

@[simp] private theorem lookup_primitiveTypeZeroRule :
    definition.lookupRule?
        ({ value := "megalodon-theory-primitive-type-zero" } : RuleId) =
      some primitiveTypeZeroRule :=
  lookupAdditionalRule _ _ (by rfl) (by rfl)

@[simp] private theorem lookup_typePrimitiveRule :
    definition.lookupRule?
        ({ value := "megalodon-theory-term-primitive" } : RuleId) =
      some typePrimitiveRule :=
  lookupAdditionalRule _ _ (by rfl) (by rfl)

@[simp] private theorem lookup_proofKnownRule :
    definition.lookupRule?
        ({ value := "megalodon-theory-proof-known" } : RuleId) =
      some proofKnownRule :=
  lookupAdditionalRule _ _ (by rfl) (by rfl)

@[simp] private theorem lookup_projectNilRule :
    definition.lookupRule?
        ({ value := "megalodon-def-project-nil" } : RuleId) =
      some DefinitionConversionKernel.projectNilRule :=
  lookupBaseRule _ _ (by rfl)

@[simp] private theorem lookup_projectDefinitionRule :
    definition.lookupRule?
        ({ value := "megalodon-def-project-definition" } : RuleId) =
      some DefinitionConversionKernel.projectDefinitionRule :=
  lookupBaseRule _ _ (by rfl)

@[simp] private theorem lookup_polyTypePlainRule :
    definition.lookupRule?
        ({ value := "megalodon-def-poly-type-plain" } : RuleId) =
      some DefinitionConversionKernel.polyTypePlainRule :=
  lookupBaseRule _ _ (by rfl)

@[simp] private theorem lookup_plainTypePropRule :
    definition.lookupRule?
        ({ value := "megalodon-poly-type-prop" } : RuleId) =
      some PolymorphicKernel.plainPropRule :=
  lookupBaseRule _ _ (by rfl)

@[simp] private theorem lookup_knownHereRule :
    definition.lookupRule?
        ({ value := "megalodon-env-known-here" } : RuleId) =
      some EnvironmentKernel.knownHereRule :=
  lookupBaseRule _ _ (by rfl)

@[simp] private theorem lookup_pathReflRule :
    definition.lookupRule?
        ({ value := "megalodon-def-path-refl" } : RuleId) =
      some DefinitionConversionKernel.pathReflRule :=
  lookupBaseRule _ _ (by rfl)

theorem definition_ruleLookupRefines :
    RuleLookupRefines DefinitionConversionKernel.validated validated := by
  apply RuleLookupRefines.of_rules_eq_append additionalRules
  rfl

def coGSLTDefinition : ExtendedLanguageDef calculusLayer :=
  definition.toExtended

def coGSLTSource : coGSLTDefinition.authoredGSLT.Term :=
  coGSLTDefinition.authoredSource

@[simp] theorem coGSLT_source_elaborates :
    calculusLayer.elaborate definition.toLanguageDef coGSLTSource =
      some definition.toCalculus :=
  definition.toExtended_elaborate_authoredSource

/-! ## Ordered admission canaries -/

private def proofNode (id : String) (arguments : List Pattern)
    (children : List RawProof := []) : RawProof :=
  .node { ruleId := ruleId id, arguments } children

def canaryPrimitiveIdentifier : Pattern := a "MTheoryCanaryPrimitive"
def canaryAxiomIdentifier : Pattern := a "MTheoryCanaryAxiom"
def canaryTheoremIdentifier : Pattern := a "MTheoryCanaryTheorem"
def canaryProposition : Pattern := a "MTmPrim" [a "MNZero"]

def canaryInitialEnvironment : Pattern :=
  a "MFullEnvironment" [a "MPrimNil", a "MDeclNil", a "MKnownNil"]

def canaryPrimitiveTypes : Pattern :=
  a "MPrimCons" [a "MTpProp", a "MPrimNil"]

def canaryDeclarations : Pattern :=
  a "MDeclDefinition"
    [canaryPrimitiveIdentifier, a "MTpProp", canaryProposition,
      a "MDeclNil"]

def canarySignature : Pattern :=
  a "MSigCons"
    [canaryPrimitiveIdentifier, a "MTpProp", a "MSigNil"]

def canaryPrimitiveEnvironment : Pattern :=
  a "MFullEnvironment"
    [canaryPrimitiveTypes, canaryDeclarations, a "MKnownNil"]

def canaryAxiomKnown : Pattern :=
  a "MKnownCons"
    [canaryAxiomIdentifier, canaryProposition, a "MKnownNil"]

def canaryAxiomEnvironment : Pattern :=
  a "MFullEnvironment"
    [canaryPrimitiveTypes, canaryDeclarations, canaryAxiomKnown]

def canaryTheoremKnown : Pattern :=
  a "MKnownCons"
    [canaryTheoremIdentifier, canaryProposition, canaryAxiomKnown]

def canaryFinalEnvironment : Pattern :=
  a "MFullEnvironment"
    [canaryPrimitiveTypes, canaryDeclarations, canaryTheoremKnown]

def canaryPrimitiveItem : Pattern :=
  a "MTheoryPrimitive"
    [canaryPrimitiveIdentifier, a "MNZero", a "MTpProp"]

def canaryAxiomItem : Pattern :=
  a "MTheoryAxiom" [canaryAxiomIdentifier, canaryProposition]

def canaryTheoremItem : Pattern :=
  a "MTheoryTheorem" [canaryTheoremIdentifier, canaryProposition]

def canaryItems : Pattern :=
  a "MTheoryItemsCons"
    [ canaryPrimitiveItem,
      a "MTheoryItemsCons"
        [ canaryAxiomItem,
          a "MTheoryItemsCons"
            [canaryTheoremItem, a "MTheoryItemsNil"] ] ]

private def canaryPrimitiveAdmissionArticle : RawProof :=
  proofNode "megalodon-theory-admit-primitive"
    [ a "MPrimNil", a "MDeclNil", a "MKnownNil",
      canaryPrimitiveIdentifier, a "MNZero", a "MTpProp",
      canaryPrimitiveTypes ]
    [ proofNode "megalodon-def-poly-type-plain"
        [a "MNZero", a "MTpProp"]
        [proofNode "megalodon-poly-type-prop" [a "MNZero"]],
      proofNode "megalodon-theory-primitive-append-zero" [a "MTpProp"] ]

private def canaryAxiomAdmissionArticle : RawProof :=
  proofNode "megalodon-theory-admit-axiom"
    [ canaryPrimitiveTypes, canaryDeclarations, canarySignature,
      a "MKnownNil", canaryAxiomIdentifier, canaryProposition ]
    [ proofNode "megalodon-def-project-definition"
        [ canaryPrimitiveIdentifier, a "MTpProp", canaryProposition,
          a "MDeclNil", a "MSigNil" ]
        [proofNode "megalodon-def-project-nil" []],
      proofNode "megalodon-theory-term-primitive"
        [ canaryPrimitiveTypes, canarySignature, a "MNZero",
          a "MTyCtxNil", a "MNZero", a "MTpProp" ]
        [ proofNode "megalodon-theory-primitive-type-zero"
            [a "MTpProp", a "MPrimNil"] ] ]

private def canaryKnownProofArticle : RawProof :=
  proofNode "megalodon-theory-proof-known"
    [ canaryPrimitiveTypes, canaryDeclarations, canaryAxiomKnown,
      a "MNZero", a "MTyCtxNil", a "MPfCtxNil",
      canaryAxiomIdentifier, canaryProposition, canaryProposition ]
    [ proofNode "megalodon-env-known-here"
        [canaryAxiomIdentifier, canaryProposition, a "MKnownNil"],
      proofNode "megalodon-def-path-refl"
        [canaryDeclarations, canaryProposition] ]

private def canaryTheoremAdmissionArticle : RawProof :=
  proofNode "megalodon-theory-admit-theorem"
    [ canaryPrimitiveTypes, canaryDeclarations, canaryAxiomKnown,
      canaryTheoremIdentifier, canaryProposition ]
    [canaryKnownProofArticle]

def canaryArticle : RawProof :=
  proofNode "megalodon-theory-checks-cons"
    [ canaryInitialEnvironment, canaryPrimitiveItem,
      a "MTheoryItemsCons"
        [ canaryAxiomItem,
          a "MTheoryItemsCons"
            [canaryTheoremItem, a "MTheoryItemsNil"] ],
      canaryPrimitiveEnvironment, canaryFinalEnvironment ]
    [ canaryPrimitiveAdmissionArticle,
      proofNode "megalodon-theory-checks-cons"
        [ canaryPrimitiveEnvironment, canaryAxiomItem,
          a "MTheoryItemsCons"
            [canaryTheoremItem, a "MTheoryItemsNil"],
          canaryAxiomEnvironment, canaryFinalEnvironment ]
        [ canaryAxiomAdmissionArticle,
          proofNode "megalodon-theory-checks-cons"
            [ canaryAxiomEnvironment, canaryTheoremItem,
              a "MTheoryItemsNil", canaryFinalEnvironment,
              canaryFinalEnvironment ]
            [ canaryTheoremAdmissionArticle,
              proofNode "megalodon-theory-checks-nil"
                [canaryFinalEnvironment] ] ] ]

def canaryGoal : Pattern :=
  checks canaryInitialEnvironment canaryItems canaryFinalEnvironment

set_option maxRecDepth 200000 in
set_option maxHeartbeats 12000000 in
theorem ordered_primitive_axiom_theorem_accepted :
    checkRaw validated canaryGoal canaryArticle = true := by
  simp only [ canaryGoal, canaryArticle, canaryItems,
    canaryPrimitiveAdmissionArticle, canaryAxiomAdmissionArticle,
    canaryTheoremAdmissionArticle, canaryKnownProofArticle, proofNode,
    checkRaw, validated, instantiateRule? ]
  simp (config := { maxSteps := 12000000, decide := true })
    [ lookup_checksConsRule, lookup_checksNilRule,
      lookup_admitPrimitiveRule, lookup_admitAxiomRule,
      lookup_admitTheoremRule, lookup_primitiveAppendZeroRule,
      lookup_primitiveTypeZeroRule, lookup_typePrimitiveRule,
      lookup_proofKnownRule, lookup_projectNilRule,
      lookup_projectDefinitionRule, lookup_polyTypePlainRule,
      lookup_plainTypePropRule, lookup_knownHereRule, lookup_pathReflRule,
      checkRaw, checkRawChildren, instantiateRule?,
      checksConsRule, checksNilRule, admitPrimitiveRule, admitAxiomRule,
      admitTheoremRule, primitiveAppendZeroRule, primitiveTypeZeroRule,
      typePrimitiveRule, proofKnownRule,
      PolymorphicKernel.plainPropRule, EnvironmentKernel.knownHereRule,
      DefinitionConversionKernel.pathReflRule,
      DefinitionConversionKernel.projectNilRule,
      DefinitionConversionKernel.projectDefinitionRule,
      DefinitionConversionKernel.polyTypePlainRule,
      DefinitionConversionKernel.polyType,
      DefinitionConversionKernel.projectSignature,
      DefinitionConversionKernel.fullProves,
      DefinitionConversionKernel.reductionPath,
      EnvironmentKernel.knownMember,
      EnvironmentKernel.plainType,
      DefinitionConversionKernel.a, DefinitionConversionKernel.m,
      DefinitionConversionKernel.rule, DefinitionConversionKernel.ruleId,
      EnvironmentKernel.a, EnvironmentKernel.m,
      EnvironmentKernel.rule, EnvironmentKernel.ruleId,
      PolymorphicKernel.a, PolymorphicKernel.m,
      PolymorphicKernel.rule, PolymorphicKernel.ruleId,
      PolymorphicKernel.plainType,
      instantiateSchemas?, instantiateSchema?, instantiateSchemasAt?,
      instantiateSchemaAt?, lookupArgumentAt?,
      canaryInitialEnvironment, canaryPrimitiveEnvironment,
      canaryAxiomEnvironment, canaryFinalEnvironment,
      canaryPrimitiveTypes, canaryDeclarations, canarySignature,
      canaryAxiomKnown, canaryTheoremKnown, canaryPrimitiveItem,
      canaryAxiomItem, canaryTheoremItem, canaryProposition,
      canaryPrimitiveIdentifier, canaryAxiomIdentifier,
      canaryTheoremIdentifier, primitiveTypeAt, primitiveAppendAt,
      hasType, admits, checks, rule, ruleId, a, m]

def wrongPrimitiveIndexItem : Pattern :=
  a "MTheoryPrimitive"
    [canaryPrimitiveIdentifier, a "MNSucc" [a "MNZero"], a "MTpProp"]

def wrongPrimitiveIndexArticle : RawProof :=
  proofNode "megalodon-theory-admit-primitive"
    [ a "MPrimNil", a "MDeclNil", a "MKnownNil",
      canaryPrimitiveIdentifier, a "MNSucc" [a "MNZero"], a "MTpProp",
      canaryPrimitiveTypes ]
    [ proofNode "megalodon-def-poly-type-plain"
        [a "MNZero", a "MTpProp"]
        [proofNode "megalodon-poly-type-prop" [a "MNZero"]],
      proofNode "megalodon-theory-primitive-append-zero" [a "MTpProp"] ]

def wrongPrimitiveIndexGoal : Pattern :=
  admits canaryInitialEnvironment wrongPrimitiveIndexItem
    canaryPrimitiveEnvironment

set_option maxRecDepth 200000 in
set_option maxHeartbeats 12000000 in
theorem skipped_primitive_index_rejected :
    checkRaw validated wrongPrimitiveIndexGoal
      wrongPrimitiveIndexArticle = false := by
  simp only [ wrongPrimitiveIndexGoal, wrongPrimitiveIndexItem,
    wrongPrimitiveIndexArticle,
    canaryInitialEnvironment, canaryPrimitiveEnvironment,
    canaryPrimitiveTypes, canaryDeclarations, canaryPrimitiveIdentifier,
    proofNode, checkRaw, validated, instantiateRule? ]
  simp (config := { maxSteps := 12000000, decide := true })
    [ lookup_admitPrimitiveRule, checkRawChildren,
      admitPrimitiveRule, primitiveAppendAt, admits,
      DefinitionConversionKernel.polyType,
      DefinitionConversionKernel.a,
      instantiateSchemas?,
      instantiateSchema?, instantiateSchemasAt?, instantiateSchemaAt?,
      lookupArgumentAt?,
      rule, ruleId, a, m]

def prematureTheoremArticle : RawProof :=
  proofNode "megalodon-theory-admit-theorem"
    [ canaryPrimitiveTypes, canaryDeclarations, a "MKnownNil",
      canaryTheoremIdentifier, canaryProposition ]
    [ canaryKnownProofArticle ]

def prematureTheoremGoal : Pattern :=
  admits canaryPrimitiveEnvironment canaryTheoremItem
    canaryAxiomEnvironment

set_option maxRecDepth 200000 in
set_option maxHeartbeats 12000000 in
theorem theorem_before_axiom_rejected :
    checkRaw validated prematureTheoremGoal
      prematureTheoremArticle = false := by
  simp only [ prematureTheoremGoal, prematureTheoremArticle,
    canaryKnownProofArticle,
    canaryPrimitiveEnvironment, canaryAxiomEnvironment,
    canaryPrimitiveTypes, canaryDeclarations, canaryAxiomKnown,
    canaryTheoremItem, canaryTheoremIdentifier, canaryProposition,
    proofNode, checkRaw, validated, instantiateRule? ]
  simp (config := { maxSteps := 12000000, decide := true })
    [ lookup_admitTheoremRule, checkRawChildren,
      admitTheoremRule, admits, DefinitionConversionKernel.fullProves,
      DefinitionConversionKernel.a,
      instantiateSchemas?, instantiateSchema?, instantiateSchemasAt?,
      instantiateSchemaAt?, lookupArgumentAt?,
      rule, ruleId, a, m]

end Mettapedia.Languages.Megalodon.TheoryAdmissionKernel
