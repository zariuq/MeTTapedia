import Mettapedia.GSLT.LanguageDef.TptpOfficialFofToNamedLanguageDef

/-!
# Complete official TPTP FOF formula elaboration

This layer extends the authored term elaboration with every formula form in
the official TPTP 9.2 FOF abstract syntax.  Routing through grammar wrappers,
connectives, quantifier lists, atoms, and sequent tuples is expressed entirely
by rewrite rows and congruence premises.  The semantic target is the inert
named-FOF language; binder resolution remains a separate transformation.

The broad structural grammar is refined at the semantic boundary: its
nullary defined-proposition case accepts exactly `$true` and `$false`, as
required by the TPTP semantic BNF.  Other defined predicates require an
argument list.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.TptpOfficialFofToNamedFormulaLanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.GSLT.LanguageDef.RewriteValidationCertificate
open Mettapedia.GSLT.LanguageDef.TptpOfficialFofToNamedLanguageDef

def request (label : String) (source : Pattern) : Pattern :=
  a label [source]

def requestWithBody (label : String) (source body : Pattern) : Pattern :=
  a label [source, body]

def targetNullary : String → Pattern
  | "verum" => a "tptp-fof-named:verum"
  | "falsum" => a "tptp-fof-named:falsum"
  | label => a s!"tptp-fof-named:{label}"

def targetUnary : String → Pattern → Pattern
  | "not", body => a "tptp-fof-named:not" [body]
  | label, body => a s!"tptp-fof-named:{label}" [body]

def targetBinary : String → Pattern → Pattern → Pattern
  | "and", left, right => a "tptp-fof-named:and" [left, right]
  | "or", left, right => a "tptp-fof-named:or" [left, right]
  | "iff", left, right => a "tptp-fof-named:iff" [left, right]
  | "implies", left, right => a "tptp-fof-named:implies" [left, right]
  | "reverse-implies", left, right =>
      a "tptp-fof-named:reverse-implies" [left, right]
  | "xor", left, right => a "tptp-fof-named:xor" [left, right]
  | "nor", left, right => a "tptp-fof-named:nor" [left, right]
  | "nand", left, right => a "tptp-fof-named:nand" [left, right]
  | label, left, right => a s!"tptp-fof-named:{label}" [left, right]

def targetPredicateHead (constructor : String) (lexeme : Pattern) : Pattern :=
  a constructor [lexeme]

def targetPredicate (head arguments : Pattern) : Pattern :=
  a "tptp-fof-named:predicate" [head, arguments]

def targetEqual (left right : Pattern) : Pattern :=
  a "tptp-fof-named:equal" [left, right]

def targetBinder : String → Pattern → Pattern → Pattern
  | "all", lexeme, body =>
      a "tptp-fof-named:all" [targetName lexeme, body]
  | "ex", lexeme, body =>
      a "tptp-fof-named:ex" [targetName lexeme, body]
  | label, lexeme, body =>
      a s!"tptp-fof-named:{label}" [targetName lexeme, body]

def delegateRule (name outerRequest outerConstructor innerRequest sourceSort :
    String) : RewriteRule :=
  mkRule name
    [("source", sourceSort), ("result", "TptpNamedFof:Formula")]
    [congruence (request innerRequest (v "source")) (v "result")]
    (request outerRequest (a outerConstructor [v "source"]))
    (v "result")

def delegationFormulaRules : List RewriteRule := [
  delegateRule "tptp-fof-elab:formula-logic" "tptp-fof-elab:formula"
    "tptp92-ast:fof-formula:alt-1" "tptp-fof-elab:logic"
    "Tptp92Ast:fof-logic-formula",
  delegateRule "tptp-fof-elab:formula-sequent" "tptp-fof-elab:formula"
    "tptp92-ast:fof-formula:alt-2" "tptp-fof-elab:sequent"
    "Tptp92Ast:fof-sequent"
]

def delegationLogicRules : List RewriteRule := [
  delegateRule "tptp-fof-elab:logic-binary" "tptp-fof-elab:logic"
    "tptp92-ast:fof-logic-formula:alt-1" "tptp-fof-elab:binary"
    "Tptp92Ast:fof-binary-formula",
  delegateRule "tptp-fof-elab:logic-unary" "tptp-fof-elab:logic"
    "tptp92-ast:fof-logic-formula:alt-2" "tptp-fof-elab:unary"
    "Tptp92Ast:fof-unary-formula",
  delegateRule "tptp-fof-elab:logic-unitary" "tptp-fof-elab:logic"
    "tptp92-ast:fof-logic-formula:alt-3" "tptp-fof-elab:unitary"
    "Tptp92Ast:fof-unitary-formula"
]

def delegationBinaryRouteRules : List RewriteRule := [
  delegateRule "tptp-fof-elab:binary-nonassoc-route" "tptp-fof-elab:binary"
    "tptp92-ast:fof-binary-formula:alt-1"
    "tptp-fof-elab:binary-nonassoc" "Tptp92Ast:fof-binary-nonassoc",
  delegateRule "tptp-fof-elab:binary-assoc-route" "tptp-fof-elab:binary"
    "tptp92-ast:fof-binary-formula:alt-2"
    "tptp-fof-elab:binary-assoc" "Tptp92Ast:fof-binary-assoc"
]

def delegationAssocRouteRules : List RewriteRule := [
  delegateRule "tptp-fof-elab:binary-assoc-or" "tptp-fof-elab:binary-assoc"
    "tptp92-ast:fof-binary-assoc:alt-1" "tptp-fof-elab:or"
    "Tptp92Ast:fof-or-formula",
  delegateRule "tptp-fof-elab:binary-assoc-and" "tptp-fof-elab:binary-assoc"
    "tptp92-ast:fof-binary-assoc:alt-2" "tptp-fof-elab:and"
    "Tptp92Ast:fof-and-formula"
]

def delegationUnitRouteRules : List RewriteRule := [
  delegateRule "tptp-fof-elab:unary-infix" "tptp-fof-elab:unary"
    "tptp92-ast:fof-unary-formula:alt-2" "tptp-fof-elab:infix-unary"
    "Tptp92Ast:fof-infix-unary",
  delegateRule "tptp-fof-elab:unit-unitary" "tptp-fof-elab:unit"
    "tptp92-ast:fof-unit-formula:alt-1" "tptp-fof-elab:unitary"
    "Tptp92Ast:fof-unitary-formula",
  delegateRule "tptp-fof-elab:unit-unary" "tptp-fof-elab:unit"
    "tptp92-ast:fof-unit-formula:alt-2" "tptp-fof-elab:unary"
    "Tptp92Ast:fof-unary-formula"
]

def delegationUnitaryRouteRules : List RewriteRule := [
  delegateRule "tptp-fof-elab:unitary-quantified" "tptp-fof-elab:unitary"
    "tptp92-ast:fof-unitary-formula:alt-1" "tptp-fof-elab:quantified"
    "Tptp92Ast:fof-quantified-formula",
  delegateRule "tptp-fof-elab:unitary-atomic" "tptp-fof-elab:unitary"
    "tptp92-ast:fof-unitary-formula:alt-2" "tptp-fof-elab:atomic"
    "Tptp92Ast:fof-atomic-formula",
  delegateRule "tptp-fof-elab:unitary-logic" "tptp-fof-elab:unitary"
    "tptp92-ast:fof-unitary-formula:alt-3" "tptp-fof-elab:logic"
    "Tptp92Ast:fof-logic-formula"
]

def delegationAtomicRouteRules : List RewriteRule := [
  delegateRule "tptp-fof-elab:atomic-plain" "tptp-fof-elab:atomic"
    "tptp92-ast:fof-atomic-formula:alt-1" "tptp-fof-elab:plain-atomic"
    "Tptp92Ast:fof-plain-atomic-formula",
  delegateRule "tptp-fof-elab:atomic-defined" "tptp-fof-elab:atomic"
    "tptp92-ast:fof-atomic-formula:alt-2" "tptp-fof-elab:defined-atomic"
    "Tptp92Ast:fof-defined-atomic-formula",
  delegateRule "tptp-fof-elab:atomic-system" "tptp-fof-elab:atomic"
    "tptp92-ast:fof-atomic-formula:alt-3" "tptp-fof-elab:system-atomic"
    "Tptp92Ast:fof-system-atomic-formula"
]

def delegationTailRules : List RewriteRule := [
  delegateRule "tptp-fof-elab:defined-atomic-plain"
    "tptp-fof-elab:defined-atomic"
    "tptp92-ast:fof-defined-atomic-formula:alt-1"
    "tptp-fof-elab:defined-plain" "Tptp92Ast:fof-defined-plain-formula",
  delegateRule "tptp-fof-elab:defined-atomic-infix"
    "tptp-fof-elab:defined-atomic"
    "tptp92-ast:fof-defined-atomic-formula:alt-2"
    "tptp-fof-elab:defined-infix" "Tptp92Ast:fof-defined-infix-formula",
  delegateRule "tptp-fof-elab:sequent-parenthesized" "tptp-fof-elab:sequent"
    "tptp92-ast:fof-sequent:alt-2" "tptp-fof-elab:sequent"
    "Tptp92Ast:fof-sequent"
]

def delegationRules : List RewriteRule :=
  delegationFormulaRules ++ delegationLogicRules ++
    delegationBinaryRouteRules ++ delegationAssocRouteRules ++
      delegationUnitRouteRules ++ delegationUnitaryRouteRules ++
        delegationAtomicRouteRules ++ delegationTailRules

def nonassocRule (name connective target : String) : RewriteRule :=
  mkRule name
    [("left", "Tptp92Ast:fof-unit-formula"),
     ("right", "Tptp92Ast:fof-unit-formula"),
     ("leftResult", "TptpNamedFof:Formula"),
     ("rightResult", "TptpNamedFof:Formula")]
    [congruence (request "tptp-fof-elab:unit" (v "left"))
        (v "leftResult"),
     congruence (request "tptp-fof-elab:unit" (v "right"))
        (v "rightResult")]
    (request "tptp-fof-elab:binary-nonassoc" <|
      a "tptp92-ast:fof-binary-nonassoc:alt-1" [
        v "left", a connective, v "right"])
    (targetBinary target (v "leftResult") (v "rightResult"))

def nonassocIffRules : List RewriteRule := [
  nonassocRule "tptp-fof-elab:binary-iff"
    "tptp92-ast:nonassoc-connective:alt-1" "iff"
]

def nonassocImplicationRules : List RewriteRule := [
  nonassocRule "tptp-fof-elab:binary-implies"
    "tptp92-ast:nonassoc-connective:alt-2" "implies",
  nonassocRule "tptp-fof-elab:binary-reverse-implies"
    "tptp92-ast:nonassoc-connective:alt-3" "reverse-implies"
]

def nonassocXorRules : List RewriteRule := [
  nonassocRule "tptp-fof-elab:binary-xor"
    "tptp92-ast:nonassoc-connective:alt-4" "xor"
]

def nonassocNorNandRules : List RewriteRule := [
  nonassocRule "tptp-fof-elab:binary-nor"
    "tptp92-ast:nonassoc-connective:alt-5" "nor",
  nonassocRule "tptp-fof-elab:binary-nand"
    "tptp92-ast:nonassoc-connective:alt-6" "nand"
]

def nonassocRules : List RewriteRule :=
  nonassocIffRules ++ nonassocImplicationRules ++ nonassocXorRules ++
    nonassocNorNandRules

def assocRule (name requestLabel sourceConstructor leftRequest leftSort target :
    String) : RewriteRule :=
  mkRule name
    [("left", leftSort), ("right", "Tptp92Ast:fof-unit-formula"),
     ("leftResult", "TptpNamedFof:Formula"),
     ("rightResult", "TptpNamedFof:Formula")]
    [congruence (request leftRequest (v "left")) (v "leftResult"),
     congruence (request "tptp-fof-elab:unit" (v "right"))
       (v "rightResult")]
    (request requestLabel (a sourceConstructor [v "left", v "right"]))
    (targetBinary target (v "leftResult") (v "rightResult"))

def assocOrRules : List RewriteRule := [
  assocRule "tptp-fof-elab:or-first" "tptp-fof-elab:or"
    "tptp92-ast:fof-or-formula:alt-1" "tptp-fof-elab:unit"
    "Tptp92Ast:fof-unit-formula" "or",
  assocRule "tptp-fof-elab:or-more" "tptp-fof-elab:or"
    "tptp92-ast:fof-or-formula:alt-2" "tptp-fof-elab:or"
    "Tptp92Ast:fof-or-formula" "or"
]

def assocAndRules : List RewriteRule := [
  assocRule "tptp-fof-elab:and-first" "tptp-fof-elab:and"
    "tptp92-ast:fof-and-formula:alt-1" "tptp-fof-elab:unit"
    "Tptp92Ast:fof-unit-formula" "and",
  assocRule "tptp-fof-elab:and-more" "tptp-fof-elab:and"
    "tptp92-ast:fof-and-formula:alt-2" "tptp-fof-elab:and"
    "Tptp92Ast:fof-and-formula" "and"
]

def assocRules : List RewriteRule := assocOrRules ++ assocAndRules

def unaryNotRule : RewriteRule :=
  mkRule "tptp-fof-elab:unary-not"
    [("body", "Tptp92Ast:fof-unit-formula"),
     ("bodyResult", "TptpNamedFof:Formula")]
    [congruence (request "tptp-fof-elab:unit" (v "body"))
      (v "bodyResult")]
    (request "tptp-fof-elab:unary" <|
      a "tptp92-ast:fof-unary-formula:alt-1" [
        a "tptp92-ast:unary-connective:alt-1", v "body"])
    (targetUnary "not" (v "bodyResult"))

def sourceVariable (lexeme : Pattern) : Pattern :=
  a "tptp92-ast:variable:alt-1" [
    sourceToken "tptp92-ast:token:upper-word" lexeme]

def quantifiedRule (name quantifier binderRequest : String) : RewriteRule :=
  mkRule name
    [("variables", "Tptp92Ast:fof-variable-list"),
     ("body", "Tptp92Ast:fof-unit-formula"),
     ("bodyResult", "TptpNamedFof:Formula"),
     ("result", "TptpNamedFof:Formula")]
    [congruence (request "tptp-fof-elab:unit" (v "body"))
        (v "bodyResult"),
     congruence (requestWithBody binderRequest (v "variables")
        (v "bodyResult")) (v "result")]
    (request "tptp-fof-elab:quantified" <|
      a "tptp92-ast:fof-quantified-formula:alt-1" [
        a quantifier, v "variables", v "body"])
    (v "result")

def bindOneRule (name binderRequest target : String) : RewriteRule :=
  mkRule name
    [("lexeme", "String"), ("body", "TptpNamedFof:Formula")]
    []
    (requestWithBody binderRequest
      (a "tptp92-ast:fof-variable-list:alt-1" [
        sourceVariable (v "lexeme")]) (v "body"))
    (targetBinder target (v "lexeme") (v "body"))

def bindMoreRule (name binderRequest target : String) : RewriteRule :=
  mkRule name
    [("lexeme", "String"),
     ("rest", "Tptp92Ast:fof-variable-list"),
     ("body", "TptpNamedFof:Formula"),
     ("restResult", "TptpNamedFof:Formula")]
    [congruence (requestWithBody binderRequest (v "rest") (v "body"))
      (v "restResult")]
    (requestWithBody binderRequest
      (a "tptp92-ast:fof-variable-list:alt-2" [
        sourceVariable (v "lexeme"), v "rest"]) (v "body"))
    (targetBinder target (v "lexeme") (v "restResult"))

def quantifierHeadRules : List RewriteRule := [
  quantifiedRule "tptp-fof-elab:quantified-all"
    "tptp92-ast:fof-quantifier:alt-1" "tptp-fof-elab:bind-all",
  quantifiedRule "tptp-fof-elab:quantified-ex"
    "tptp92-ast:fof-quantifier:alt-2" "tptp-fof-elab:bind-ex"
]

def bindAllRules : List RewriteRule := [
  bindOneRule "tptp-fof-elab:bind-all-one"
    "tptp-fof-elab:bind-all" "all",
  bindMoreRule "tptp-fof-elab:bind-all-more"
    "tptp-fof-elab:bind-all" "all"
]

def bindExRules : List RewriteRule := [
  bindOneRule "tptp-fof-elab:bind-ex-one"
    "tptp-fof-elab:bind-ex" "ex",
  bindMoreRule "tptp-fof-elab:bind-ex-more"
    "tptp-fof-elab:bind-ex" "ex"
]

def quantifierRules : List RewriteRule :=
  quantifierHeadRules ++ bindAllRules ++ bindExRules

def sourceFunctor (atomicAlternative tokenLabel : String)
    (lexeme : Pattern) : Pattern :=
  a "tptp92-ast:functor:alt-1" [
    sourceAtomicWord atomicAlternative tokenLabel lexeme]

def plainAtomicNullaryRule
    (name atomicAlternative tokenLabel : String) : RewriteRule :=
  mkRule name [("lexeme", "String")] []
    (request "tptp-fof-elab:plain-atomic" <|
      a "tptp92-ast:fof-plain-atomic-formula:alt-1" [
        a "tptp92-ast:fof-plain-term:alt-1" [
          a "tptp92-ast:constant:alt-1" [
            sourceFunctor atomicAlternative tokenLabel (v "lexeme")]]])
    (targetPredicate
      (targetPredicateHead "tptp-fof-symbol:predicate-plain" (v "lexeme"))
      targetTermsNil)

def plainAtomicAppliedRule
    (name atomicAlternative tokenLabel : String) : RewriteRule :=
  mkRule name
    [("lexeme", "String"), ("arguments", "Tptp92Ast:fof-arguments"),
     ("argumentsResult", "TptpNamedFof:Terms")]
    [congruence (translateArguments (v "arguments")) (v "argumentsResult")]
    (request "tptp-fof-elab:plain-atomic" <|
      a "tptp92-ast:fof-plain-atomic-formula:alt-1" [
        a "tptp92-ast:fof-plain-term:alt-2" [
          sourceFunctor atomicAlternative tokenLabel (v "lexeme"),
          v "arguments"]])
    (targetPredicate
      (targetPredicateHead "tptp-fof-symbol:predicate-plain" (v "lexeme"))
      (v "argumentsResult"))

def definedTruthRule (name lexeme target : String) : RewriteRule :=
  mkRule name [] []
    (request "tptp-fof-elab:defined-plain" <|
      a "tptp92-ast:fof-defined-plain-formula:alt-1" [
        a "tptp92-ast:fof-defined-plain-term:alt-1" [
          a "tptp92-ast:defined-constant:alt-1" [
            sourceDefinedFunctor (a lexeme)]]])
    (targetNullary target)

def definedPredicateRule : RewriteRule :=
  mkRule "tptp-fof-elab:defined-predicate"
    [("lexeme", "String"), ("arguments", "Tptp92Ast:fof-arguments"),
     ("argumentsResult", "TptpNamedFof:Terms")]
    [congruence (translateArguments (v "arguments")) (v "argumentsResult")]
    (request "tptp-fof-elab:defined-plain" <|
      a "tptp92-ast:fof-defined-plain-formula:alt-1" [
        a "tptp92-ast:fof-defined-plain-term:alt-2" [
          sourceDefinedFunctor (v "lexeme"), v "arguments"]])
    (targetPredicate
      (targetPredicateHead "tptp-fof-symbol:predicate-defined" (v "lexeme"))
      (v "argumentsResult"))

def systemAtomicNullaryRule : RewriteRule :=
  mkRule "tptp-fof-elab:system-predicate-nullary"
    [("lexeme", "String")] []
    (request "tptp-fof-elab:system-atomic" <|
      a "tptp92-ast:fof-system-atomic-formula:alt-1" [
        a "tptp92-ast:fof-system-term:alt-1" [
          a "tptp92-ast:system-constant:alt-1" [
            sourceSystemFunctor (v "lexeme")]]])
    (targetPredicate
      (targetPredicateHead "tptp-fof-symbol:predicate-system" (v "lexeme"))
      targetTermsNil)

def systemAtomicAppliedRule : RewriteRule :=
  mkRule "tptp-fof-elab:system-predicate-applied"
    [("lexeme", "String"), ("arguments", "Tptp92Ast:fof-arguments"),
     ("argumentsResult", "TptpNamedFof:Terms")]
    [congruence (translateArguments (v "arguments")) (v "argumentsResult")]
    (request "tptp-fof-elab:system-atomic" <|
      a "tptp92-ast:fof-system-atomic-formula:alt-1" [
        a "tptp92-ast:fof-system-term:alt-2" [
          sourceSystemFunctor (v "lexeme"), v "arguments"]])
    (targetPredicate
      (targetPredicateHead "tptp-fof-symbol:predicate-system" (v "lexeme"))
      (v "argumentsResult"))

def equalityRule : RewriteRule :=
  mkRule "tptp-fof-elab:equality"
    [("left", "Tptp92Ast:fof-term"), ("right", "Tptp92Ast:fof-term"),
     ("leftResult", "TptpNamedFof:Term"),
     ("rightResult", "TptpNamedFof:Term")]
    [congruence (translateTerm (v "left")) (v "leftResult"),
     congruence (translateTerm (v "right")) (v "rightResult")]
    (request "tptp-fof-elab:defined-infix" <|
      a "tptp92-ast:fof-defined-infix-formula:alt-1" [
        v "left", a "tptp92-ast:defined-infix-pred:alt-1" [
          a "tptp92-ast:infix-equality:alt-1"], v "right"])
    (targetEqual (v "leftResult") (v "rightResult"))

def inequalityRule : RewriteRule :=
  mkRule "tptp-fof-elab:inequality"
    [("left", "Tptp92Ast:fof-term"), ("right", "Tptp92Ast:fof-term"),
     ("leftResult", "TptpNamedFof:Term"),
     ("rightResult", "TptpNamedFof:Term")]
    [congruence (translateTerm (v "left")) (v "leftResult"),
     congruence (translateTerm (v "right")) (v "rightResult")]
    (request "tptp-fof-elab:infix-unary" <|
      a "tptp92-ast:fof-infix-unary:alt-1" [
        v "left", a "tptp92-ast:infix-inequality:alt-1", v "right"])
    (targetUnary "not" (targetEqual (v "leftResult") (v "rightResult")))

def plainAtomicLowerNullaryRules : List RewriteRule := [
  plainAtomicNullaryRule "tptp-fof-elab:plain-lower-nullary"
    "tptp92-ast:atomic-word:alt-1" "tptp92-ast:token:lower-word"
]

def plainAtomicQuotedNullaryRules : List RewriteRule := [
  plainAtomicNullaryRule "tptp-fof-elab:plain-quoted-nullary"
    "tptp92-ast:atomic-word:alt-2" "tptp92-ast:token:single-quoted",
  plainAtomicNullaryRule "tptp-fof-elab:plain-backquoted-nullary"
    "tptp92-ast:atomic-word:alt-3" "tptp92-ast:token:back-quoted"
]

def plainAtomicLowerAppliedRules : List RewriteRule := [
  plainAtomicAppliedRule "tptp-fof-elab:plain-lower-applied"
    "tptp92-ast:atomic-word:alt-1" "tptp92-ast:token:lower-word"
]

def plainAtomicQuotedAppliedRules : List RewriteRule := [
  plainAtomicAppliedRule "tptp-fof-elab:plain-quoted-applied"
    "tptp92-ast:atomic-word:alt-2" "tptp92-ast:token:single-quoted",
  plainAtomicAppliedRule "tptp-fof-elab:plain-backquoted-applied"
    "tptp92-ast:atomic-word:alt-3" "tptp92-ast:token:back-quoted"
]

def definedTruthRules : List RewriteRule := [
  definedTruthRule "tptp-fof-elab:defined-true" "$true" "verum",
  definedTruthRule "tptp-fof-elab:defined-false" "$false" "falsum"
]

def definedPredicateRules : List RewriteRule := [
  definedPredicateRule
]

def systemAtomicRules : List RewriteRule := [
  systemAtomicNullaryRule,
  systemAtomicAppliedRule
]

def equalityRules : List RewriteRule := [
  equalityRule,
  inequalityRule
]

def atomicRules : List RewriteRule :=
  plainAtomicLowerNullaryRules ++ plainAtomicQuotedNullaryRules ++
    plainAtomicLowerAppliedRules ++ plainAtomicQuotedAppliedRules ++
      definedTruthRules ++ definedPredicateRules ++ systemAtomicRules ++
        equalityRules

def sequentRule : RewriteRule :=
  mkRule "tptp-fof-elab:sequent"
    [("left", "Tptp92Ast:fof-formula-tuple"),
     ("right", "Tptp92Ast:fof-formula-tuple"),
     ("leftResult", "TptpNamedFof:Formula"),
     ("rightResult", "TptpNamedFof:Formula")]
    [congruence (request "tptp-fof-elab:tuple-conjunction" (v "left"))
        (v "leftResult"),
     congruence (request "tptp-fof-elab:tuple-disjunction" (v "right"))
        (v "rightResult")]
    (request "tptp-fof-elab:sequent" <|
      a "tptp92-ast:fof-sequent:alt-1" [
        v "left", a "tptp92-ast:gentzen-arrow:alt-1", v "right"])
    (targetBinary "implies" (v "leftResult") (v "rightResult"))

def tupleEmptyRule (name requestLabel target : String) : RewriteRule :=
  mkRule name [] []
    (request requestLabel (a "tptp92-ast:fof-formula-tuple:alt-1"))
    (targetNullary target)

def tupleNonemptyRule (name requestLabel commaRequest : String) : RewriteRule :=
  mkRule name
    [("first", "Tptp92Ast:fof-logic-formula"),
     ("rest", "Tptp92AstList:tptp92ast-comma-fof-logic-formula"),
     ("firstResult", "TptpNamedFof:Formula"),
     ("result", "TptpNamedFof:Formula")]
    [congruence (request "tptp-fof-elab:logic" (v "first"))
        (v "firstResult"),
     congruence (requestWithBody commaRequest (v "rest")
        (v "firstResult")) (v "result")]
    (request requestLabel <|
      a "tptp92-ast:fof-formula-tuple:alt-2" [
        a "tptp92-ast:fof-formula-tuple-list:alt-1" [
          v "first", v "rest"]])
    (v "result")

def commaNilRule (name requestLabel : String) : RewriteRule :=
  mkRule name [("body", "TptpNamedFof:Formula")] []
    (requestWithBody requestLabel
      (a "tptp92-ast:list:tptp92ast-comma-fof-logic-formula:nil")
      (v "body"))
    (v "body")

def commaConsRule (name requestLabel target : String) : RewriteRule :=
  mkRule name
    [("body", "TptpNamedFof:Formula"),
     ("formula", "Tptp92Ast:fof-logic-formula"),
     ("rest", "Tptp92AstList:tptp92ast-comma-fof-logic-formula"),
     ("formulaResult", "TptpNamedFof:Formula"),
     ("result", "TptpNamedFof:Formula")]
    [congruence (request "tptp-fof-elab:logic" (v "formula"))
        (v "formulaResult"),
     congruence (requestWithBody requestLabel (v "rest")
        (targetBinary target (v "body") (v "formulaResult")))
        (v "result")]
    (requestWithBody requestLabel
      (a "tptp92-ast:list:tptp92ast-comma-fof-logic-formula:cons" [
        a "tptp92-ast:comma-fof-logic-formula:alt-1" [v "formula"],
        v "rest"]) (v "body"))
    (v "result")

def sequentMainRules : List RewriteRule := [sequentRule]

def conjunctionHeadRules : List RewriteRule := [
  tupleEmptyRule "tptp-fof-elab:tuple-conjunction-empty"
    "tptp-fof-elab:tuple-conjunction" "verum",
  tupleNonemptyRule "tptp-fof-elab:tuple-conjunction-nonempty"
    "tptp-fof-elab:tuple-conjunction" "tptp-fof-elab:comma-conjunction"
]

def conjunctionTailRules : List RewriteRule := [
  commaNilRule "tptp-fof-elab:comma-conjunction-nil"
    "tptp-fof-elab:comma-conjunction",
  commaConsRule "tptp-fof-elab:comma-conjunction-cons"
    "tptp-fof-elab:comma-conjunction" "and"
]

def disjunctionHeadRules : List RewriteRule := [
  tupleEmptyRule "tptp-fof-elab:tuple-disjunction-empty"
    "tptp-fof-elab:tuple-disjunction" "falsum",
  tupleNonemptyRule "tptp-fof-elab:tuple-disjunction-nonempty"
    "tptp-fof-elab:tuple-disjunction" "tptp-fof-elab:comma-disjunction"
]

def disjunctionTailRules : List RewriteRule := [
  commaNilRule "tptp-fof-elab:comma-disjunction-nil"
    "tptp-fof-elab:comma-disjunction",
  commaConsRule "tptp-fof-elab:comma-disjunction-cons"
    "tptp-fof-elab:comma-disjunction" "or"
]

def sequentRules : List RewriteRule :=
  sequentMainRules ++ conjunctionHeadRules ++ conjunctionTailRules ++
    disjunctionHeadRules ++ disjunctionTailRules

def formulaRewrites : List RewriteRule :=
  delegationRules ++ nonassocRules ++ assocRules ++ [unaryNotRule] ++
    quantifierRules ++ atomicRules ++ sequentRules

def language : LanguageDef := {
  syntaxLanguage with rewrites := termRewrites ++ formulaRewrites
}

theorem formula_rewrite_count : formulaRewrites.length = 60 := by
  decide

private theorem constructorLabels_nodup :
    (language.terms.map (·.label)).Nodup := by
  simpa [language] using
    LanguageDef.constructorLabels_nodup_of_validate_eq_nil syntaxLanguage
      syntaxLanguage_validate

private def constructorLabelNamespaced (label : String) : Bool :=
  label.startsWith "tptp92-ast:" ||
    label.startsWith "tptp-fof-named:" ||
      label.startsWith "tptp-fof-symbol:" ||
        label.startsWith "tptp-fof-elab:" ||
        label = "$true" || label = "$false"

private theorem constructorLabels_namespaced :
    (RewriteValidationCertificate.constructorLabels language).all
      constructorLabelNamespaced = true := by
  decide +kernel

private theorem plainName_not_constructor (name : String)
    (plain : constructorLabelNamespaced name = false) :
    name ∉ RewriteValidationCertificate.constructorLabels language := by
  intro membership
  have namespaced := (List.all_eq_true.mp constructorLabels_namespaced)
    name membership
  simp [plain] at namespaced

local macro "certify_formula_row" : tactic =>
  `(tactic|
    (simp [RewriteValidationCertificate.check,
      RewriteValidationCertificate.contextTypesCheck,
      RewriteValidationCertificate.patternDeclaredCheck,
      RewriteValidationCertificate.premisesDeclaredCheck,
      RewriteValidationCertificate.allPatternsScopedCheck,
      RewriteValidationCertificate.fvarsAvoidConstructorsCheck,
      RewriteValidationCertificate.bindersAvoidConstructorsCheck,
      RewriteValidationCertificate.contextAvoidsConstructorsCheck,
      RewriteValidationCertificate.rightBoundCheck,
      delegateRule, nonassocRule, assocRule, unaryNotRule, quantifiedRule,
      bindOneRule, bindMoreRule, plainAtomicNullaryRule,
      plainAtomicAppliedRule, definedTruthRule, definedPredicateRule,
      systemAtomicNullaryRule, systemAtomicAppliedRule, equalityRule,
      inequalityRule, sequentRule, tupleEmptyRule,
      tupleNonemptyRule, commaNilRule, commaConsRule,
      request, requestWithBody, targetNullary, targetUnary, targetBinary,
      targetPredicateHead, targetPredicate, targetEqual, targetBinder,
      sourceVariable,
      sourceFunctor, mkRule, typed, congruence, translateTerm,
      translateArguments, targetName, targetTermsNil,
      sourceDefinedFunctor, sourceSystemFunctor, sourceToken,
      sourceAtomicWord, a, v,
      RewriteValidationCertificate.constructorSignatures,
      Pattern.constructorRefs, Pattern.constructorRefsList,
      Pattern.isWellScoped, Pattern.isWellScopedAt,
      Pattern.isWellScopedListAt, Pattern.freeFvarNames,
      LanguageDef.patternFvarNames, LanguageDef.patternBinderNames,
      LanguageDef.premisePatterns, LanguageDef.premiseFvarNames,
      LanguageDef.premiseForAllParams,
      LanguageDef.premiseProducedFvarNames, TypeExpr.baseNames,
      plainName_not_constructor, constructorLabelNamespaced] <;>
      decide +kernel))

private theorem delegationFormulaRules_checked :
    delegationFormulaRules.all
      (RewriteValidationCertificate.check language) = true := by
  simp only [delegationFormulaRules, List.all_cons, List.all_nil,
    Bool.and_eq_true]
  repeat' apply And.intro
  all_goals certify_formula_row

private theorem delegationLogicRules_checked :
    delegationLogicRules.all
      (RewriteValidationCertificate.check language) = true := by
  simp only [delegationLogicRules, List.all_cons, List.all_nil,
    Bool.and_eq_true]
  repeat' apply And.intro
  all_goals certify_formula_row

private theorem delegationBinaryRouteRules_checked :
    delegationBinaryRouteRules.all
      (RewriteValidationCertificate.check language) = true := by
  simp only [delegationBinaryRouteRules, List.all_cons, List.all_nil,
    Bool.and_eq_true]
  repeat' apply And.intro
  all_goals certify_formula_row

private theorem delegationAssocRouteRules_checked :
    delegationAssocRouteRules.all
      (RewriteValidationCertificate.check language) = true := by
  simp only [delegationAssocRouteRules, List.all_cons, List.all_nil,
    Bool.and_eq_true]
  repeat' apply And.intro
  all_goals certify_formula_row

private theorem delegationUnitRouteRules_checked :
    delegationUnitRouteRules.all
      (RewriteValidationCertificate.check language) = true := by
  simp only [delegationUnitRouteRules, List.all_cons, List.all_nil,
    Bool.and_eq_true]
  repeat' apply And.intro
  all_goals certify_formula_row

private theorem delegationUnitaryRouteRules_checked :
    delegationUnitaryRouteRules.all
      (RewriteValidationCertificate.check language) = true := by
  simp only [delegationUnitaryRouteRules, List.all_cons, List.all_nil,
    Bool.and_eq_true]
  repeat' apply And.intro
  all_goals certify_formula_row

private theorem delegationAtomicRouteRules_checked :
    delegationAtomicRouteRules.all
      (RewriteValidationCertificate.check language) = true := by
  simp only [delegationAtomicRouteRules, List.all_cons, List.all_nil,
    Bool.and_eq_true]
  repeat' apply And.intro
  all_goals certify_formula_row

private theorem delegationTailRules_checked :
    delegationTailRules.all
      (RewriteValidationCertificate.check language) = true := by
  simp only [delegationTailRules, List.all_cons, List.all_nil,
    Bool.and_eq_true]
  repeat' apply And.intro
  all_goals certify_formula_row

private theorem delegationRules_checked :
    delegationRules.all (RewriteValidationCertificate.check language) = true := by
  simp only [delegationRules, List.all_append,
    delegationFormulaRules_checked, delegationLogicRules_checked,
    delegationBinaryRouteRules_checked, delegationAssocRouteRules_checked,
    delegationUnitRouteRules_checked, delegationUnitaryRouteRules_checked,
    delegationAtomicRouteRules_checked, delegationTailRules_checked,
    Bool.and_self]

private theorem nonassocIffRules_checked :
    nonassocIffRules.all
      (RewriteValidationCertificate.check language) = true := by
  simp only [nonassocIffRules, List.all_cons, List.all_nil,
    Bool.and_eq_true]
  repeat' apply And.intro
  all_goals certify_formula_row

private theorem nonassocImplicationRules_checked :
    nonassocImplicationRules.all
      (RewriteValidationCertificate.check language) = true := by
  simp only [nonassocImplicationRules, List.all_cons, List.all_nil,
    Bool.and_eq_true]
  repeat' apply And.intro
  all_goals certify_formula_row

private theorem nonassocXorRules_checked :
    nonassocXorRules.all
      (RewriteValidationCertificate.check language) = true := by
  simp only [nonassocXorRules, List.all_cons, List.all_nil, Bool.and_eq_true]
  repeat' apply And.intro
  all_goals certify_formula_row

private theorem nonassocNorNandRules_checked :
    nonassocNorNandRules.all
      (RewriteValidationCertificate.check language) = true := by
  simp only [nonassocNorNandRules, List.all_cons, List.all_nil,
    Bool.and_eq_true]
  repeat' apply And.intro
  all_goals certify_formula_row

private theorem nonassocRules_checked :
    nonassocRules.all (RewriteValidationCertificate.check language) = true := by
  simp only [nonassocRules, List.all_append,
    nonassocIffRules_checked, nonassocImplicationRules_checked,
    nonassocXorRules_checked, nonassocNorNandRules_checked, Bool.and_self]

private theorem assocOrRules_checked :
    assocOrRules.all (RewriteValidationCertificate.check language) = true := by
  simp only [assocOrRules, List.all_cons, List.all_nil, Bool.and_eq_true]
  repeat' apply And.intro
  all_goals certify_formula_row

private theorem assocAndRules_checked :
    assocAndRules.all (RewriteValidationCertificate.check language) = true := by
  simp only [assocAndRules, List.all_cons, List.all_nil, Bool.and_eq_true]
  repeat' apply And.intro
  all_goals certify_formula_row

private theorem assocRules_checked :
    assocRules.all (RewriteValidationCertificate.check language) = true := by
  simp only [assocRules, List.all_append, assocOrRules_checked,
    assocAndRules_checked, Bool.and_self]

private theorem unaryNotRule_checked :
    RewriteValidationCertificate.check language unaryNotRule = true := by
  certify_formula_row

private theorem quantifierHeadRules_checked :
    quantifierHeadRules.all
      (RewriteValidationCertificate.check language) = true := by
  simp only [quantifierHeadRules, List.all_cons, List.all_nil,
    Bool.and_eq_true]
  repeat' apply And.intro
  all_goals certify_formula_row

private theorem bindAllRules_checked :
    bindAllRules.all (RewriteValidationCertificate.check language) = true := by
  simp only [bindAllRules, List.all_cons, List.all_nil, Bool.and_eq_true]
  repeat' apply And.intro
  all_goals certify_formula_row

private theorem bindExRules_checked :
    bindExRules.all (RewriteValidationCertificate.check language) = true := by
  simp only [bindExRules, List.all_cons, List.all_nil, Bool.and_eq_true]
  repeat' apply And.intro
  all_goals certify_formula_row

private theorem quantifierRules_checked :
    quantifierRules.all (RewriteValidationCertificate.check language) = true := by
  simp only [quantifierRules, List.all_append, quantifierHeadRules_checked,
    bindAllRules_checked, bindExRules_checked, Bool.and_self]

private theorem plainAtomicLowerNullaryRules_checked :
    plainAtomicLowerNullaryRules.all
      (RewriteValidationCertificate.check language) = true := by
  simp only [plainAtomicLowerNullaryRules, List.all_cons, List.all_nil,
    Bool.and_eq_true]
  repeat' apply And.intro
  all_goals certify_formula_row

private theorem plainAtomicQuotedNullaryRules_checked :
    plainAtomicQuotedNullaryRules.all
      (RewriteValidationCertificate.check language) = true := by
  simp only [plainAtomicQuotedNullaryRules, List.all_cons, List.all_nil,
    Bool.and_eq_true]
  repeat' apply And.intro
  all_goals certify_formula_row

private theorem plainAtomicLowerAppliedRules_checked :
    plainAtomicLowerAppliedRules.all
      (RewriteValidationCertificate.check language) = true := by
  simp only [plainAtomicLowerAppliedRules, List.all_cons, List.all_nil,
    Bool.and_eq_true]
  repeat' apply And.intro
  all_goals certify_formula_row

private theorem plainAtomicQuotedAppliedRule_checked :
    RewriteValidationCertificate.check language
      (plainAtomicAppliedRule "tptp-fof-elab:plain-quoted-applied"
        "tptp92-ast:atomic-word:alt-2"
        "tptp92-ast:token:single-quoted") = true := by
  certify_formula_row

private theorem plainAtomicBackquotedAppliedRule_checked :
    RewriteValidationCertificate.check language
      (plainAtomicAppliedRule "tptp-fof-elab:plain-backquoted-applied"
        "tptp92-ast:atomic-word:alt-3"
        "tptp92-ast:token:back-quoted") = true := by
  certify_formula_row

private theorem plainAtomicQuotedAppliedRules_checked :
    plainAtomicQuotedAppliedRules.all
      (RewriteValidationCertificate.check language) = true := by
  simp [plainAtomicQuotedAppliedRules,
    plainAtomicQuotedAppliedRule_checked,
    plainAtomicBackquotedAppliedRule_checked]

private theorem definedTruthRules_checked :
    definedTruthRules.all
      (RewriteValidationCertificate.check language) = true := by
  simp only [definedTruthRules, List.all_cons, List.all_nil, Bool.and_eq_true]
  repeat' apply And.intro
  all_goals certify_formula_row

private theorem definedPredicateRules_checked :
    definedPredicateRules.all
      (RewriteValidationCertificate.check language) = true := by
  simp only [definedPredicateRules, List.all_cons, List.all_nil,
    Bool.and_eq_true]
  repeat' apply And.intro
  all_goals certify_formula_row

private theorem systemAtomicRules_checked :
    systemAtomicRules.all
      (RewriteValidationCertificate.check language) = true := by
  simp only [systemAtomicRules, List.all_cons, List.all_nil, Bool.and_eq_true]
  repeat' apply And.intro
  all_goals certify_formula_row

private theorem equalityRules_checked :
    equalityRules.all (RewriteValidationCertificate.check language) = true := by
  simp only [equalityRules, List.all_cons, List.all_nil, Bool.and_eq_true]
  repeat' apply And.intro
  all_goals certify_formula_row

private theorem atomicRules_checked :
    atomicRules.all (RewriteValidationCertificate.check language) = true := by
  simp only [atomicRules, List.all_append,
    plainAtomicLowerNullaryRules_checked,
    plainAtomicQuotedNullaryRules_checked,
    plainAtomicLowerAppliedRules_checked,
    plainAtomicQuotedAppliedRules_checked, definedTruthRules_checked,
    definedPredicateRules_checked, systemAtomicRules_checked,
    equalityRules_checked, Bool.and_self]

private theorem sequentMainRules_checked :
    sequentMainRules.all
      (RewriteValidationCertificate.check language) = true := by
  simp only [sequentMainRules, List.all_cons, List.all_nil, Bool.and_eq_true]
  repeat' apply And.intro
  all_goals certify_formula_row

private theorem conjunctionHeadRules_checked :
    conjunctionHeadRules.all
      (RewriteValidationCertificate.check language) = true := by
  simp only [conjunctionHeadRules, List.all_cons, List.all_nil,
    Bool.and_eq_true]
  repeat' apply And.intro
  all_goals certify_formula_row

private theorem conjunctionTailRules_checked :
    conjunctionTailRules.all
      (RewriteValidationCertificate.check language) = true := by
  simp only [conjunctionTailRules, List.all_cons, List.all_nil,
    Bool.and_eq_true]
  repeat' apply And.intro
  all_goals certify_formula_row

private theorem disjunctionHeadRules_checked :
    disjunctionHeadRules.all
      (RewriteValidationCertificate.check language) = true := by
  simp only [disjunctionHeadRules, List.all_cons, List.all_nil,
    Bool.and_eq_true]
  repeat' apply And.intro
  all_goals certify_formula_row

private theorem disjunctionTailRules_checked :
    disjunctionTailRules.all
      (RewriteValidationCertificate.check language) = true := by
  simp only [disjunctionTailRules, List.all_cons, List.all_nil,
    Bool.and_eq_true]
  repeat' apply And.intro
  all_goals certify_formula_row

private theorem sequentRules_checked :
    sequentRules.all (RewriteValidationCertificate.check language) = true := by
  simp only [sequentRules, List.all_append, sequentMainRules_checked,
    conjunctionHeadRules_checked, conjunctionTailRules_checked,
    disjunctionHeadRules_checked, disjunctionTailRules_checked, Bool.and_self]

private theorem checkedRow_validate {rows : List RewriteRule}
    (checks : rows.all (RewriteValidationCertificate.check language) = true)
    {rewrite : RewriteRule} (membership : rewrite ∈ rows) :
    language.validateRewrite rewrite = [] := by
  apply RewriteValidationCertificate.validateRewrite_eq_nil_of_check
    constructorLabels_nodup
  exact (List.all_eq_true.mp checks) rewrite membership

theorem formulaRewrite_validate (rewrite : RewriteRule)
    (membership : rewrite ∈ formulaRewrites) :
    language.validateRewrite rewrite = [] := by
  simp only [formulaRewrites, List.mem_append, List.mem_singleton] at membership
  rcases membership with beforeSequent | sequent
  · rcases beforeSequent with beforeAtomic | atomic
    · rcases beforeAtomic with beforeQuantifier | quantifier
      · rcases beforeQuantifier with beforeUnary | unary
        · rcases beforeUnary with beforeAssoc | assoc
          · rcases beforeAssoc with routing | nonassoc
            · exact checkedRow_validate delegationRules_checked routing
            · exact checkedRow_validate nonassocRules_checked nonassoc
          · exact checkedRow_validate assocRules_checked assoc
        · subst rewrite
          exact RewriteValidationCertificate.validateRewrite_eq_nil_of_check
            constructorLabels_nodup unaryNotRule_checked
      · exact checkedRow_validate quantifierRules_checked quantifier
    · exact checkedRow_validate atomicRules_checked atomic
  · exact checkedRow_validate sequentRules_checked sequent

theorem language_validate : language.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_rows
  · simpa [language, LanguageDef.typeNames] using
      LanguageDef.typeNames_nodup_of_validate_eq_nil syntaxLanguage
        syntaxLanguage_validate
  · exact constructorLabels_nodup
  · change syntaxLanguage.equations.map (·.name) |>.Nodup
    exact LanguageDef.equationNames_nodup_of_validate_eq_nil syntaxLanguage
      syntaxLanguage_validate
  · decide +kernel
  · intro term membership
    exact LanguageDef.validateTerm_eq_nil_of_validate_eq_nil syntaxLanguage
      syntaxLanguage_validate term membership
  · intro equation membership
    change equation ∈ syntaxLanguage.equations at membership
    have noEquations : syntaxLanguage.equations = [] := rfl
    simp [noEquations] at membership
  · intro rewrite membership
    simp only [language, List.mem_append] at membership
    rcases membership with termMembership | formulaMembership
    · change TptpOfficialFofToNamedLanguageDef.language.validateRewrite
        rewrite = []
      exact termRewrite_validate rewrite termMembership
    · exact formulaRewrite_validate rewrite formulaMembership

namespace Canary

open Mettapedia.GSLT.LanguageDef.TptpOfficialFofElaboration

theorem true_semantics_agrees :
    decodeFormula?
      (TptpOfficialFofElaboration.Canary.definedNullaryFormula "$true") =
        some .verum :=
  TptpOfficialFofElaboration.Canary.defined_true_is_verum

def malformed : Pattern :=
  a "tptp92-ast:fof-formula:alt-1" [a "invented"]

theorem malformed_semantics_fails : decodeFormula? malformed = none := by
  rfl

end Canary

#print axioms formulaRewrite_validate
#print axioms language_validate
#print axioms Canary.true_semantics_agrees
#print axioms Canary.malformed_semantics_fails

end Mettapedia.GSLT.LanguageDef.TptpOfficialFofToNamedFormulaLanguageDef
