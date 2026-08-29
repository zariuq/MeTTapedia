import Mettapedia.GSLT.LanguageDef.ConversionCertificate
import Mettapedia.GSLT.LanguageDef.CalculusLanguageDef

/-!
# First-order contextual conversion language for empty-signature LF

The intrinsic rooted LF language represents object-language binders with
`Pattern.lambda`.  That representation is convenient for direct substitution,
but a fixed inference schema cannot quantify over arbitrary ambient binder
depth.  This module instead serializes de Bruijn syntax as ordinary
first-order data and makes every auxiliary computation proof-carrying.

The language definition contains generic judgments for:

* Peano order and addition;
* de Bruijn lifting, substitution, and successful unused-variable removal;
* filling an explicit one-hole context;
* root beta and eta contraction;
* one contextual conversion edge.

There is deliberately no delta rule here: this source is the
empty-signature conversion profile used by the DTT corpus.  Transparent
definitions require a separately checked signature-lookup language.

All rules are consumed by the source-neutral inference checker.  The positive
fixture checks a beta contraction under a product body.  Negative fixtures
reject captured eta and a fabricated contextual endpoint.  Universal
correspondence with the LF semantic relations is established separately.
-/

namespace Mettapedia.GSLT.LanguageDef.LFFirstOrderContextualConversion

set_option maxRecDepth 100000

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.CheckedSource
open Mettapedia.GSLT.LanguageDef.ConversionCertificate
open Mettapedia.GSLT.LanguageDef

def natType : TypeDecl := TypeDecl.plain "LFNat"
def sortTypeDecl : TypeDecl := TypeDecl.plain "LFSort"
def nameType : TypeDecl := TypeDecl.plain "LFName"
def termType : TypeDecl := TypeDecl.plain "LFTerm"
def contextType : TypeDecl := TypeDecl.plain "LFContext"

def constructor
    (head resultType : String) (params : List TermParam) : GrammarRule :=
  { label := head
    category := resultType
    params
    syntaxPattern := [] }

def zero : Pattern := .apply "Zero" []
def succ (value : Pattern) : Pattern := .apply "Succ" [value]
def one : Pattern := succ zero

def typeSort : Pattern := .apply "TypeSort" []
def kindSort : Pattern := .apply "KindSort" []
def nameNil : Pattern := .apply "NameNil" []
def nameCons (codepoint rest : Pattern) : Pattern :=
  .apply "NameCons" [codepoint, rest]
def srt (sort : Pattern) : Pattern := .apply "Srt" [sort]
def con (name : Pattern) : Pattern := .apply "Con" [name]
def var (index : Pattern) : Pattern := .apply "Var" [index]
def pi (domain body : Pattern) : Pattern := .apply "Pi" [domain, body]
def lam (domain body : Pattern) : Pattern := .apply "Lam" [domain, body]
def app (function argument : Pattern) : Pattern :=
  .apply "App" [function, argument]

def hole : Pattern := .apply "Hole" []
def piDomainContext (rest body : Pattern) : Pattern :=
  .apply "PiDomainContext" [rest, body]
def piBodyContext (domain rest : Pattern) : Pattern :=
  .apply "PiBodyContext" [domain, rest]
def lamDomainContext (rest body : Pattern) : Pattern :=
  .apply "LamDomainContext" [rest, body]
def lamBodyContext (domain rest : Pattern) : Pattern :=
  .apply "LamBodyContext" [domain, rest]
def appFunctionContext (rest argument : Pattern) : Pattern :=
  .apply "AppFunctionContext" [rest, argument]
def appArgumentContext (function rest : Pattern) : Pattern :=
  .apply "AppArgumentContext" [function, rest]

def lt (left right : Pattern) : Pattern := .apply "NatLt" [left, right]
def add (left right result : Pattern) : Pattern :=
  .apply "NatAdd" [left, right, result]
def lifts (distance cutoff source target : Pattern) : Pattern :=
  .apply "Lifts" [distance, cutoff, source, target]
def substitutes (index replacement source target : Pattern) : Pattern :=
  .apply "Substitutes" [index, replacement, source, target]
def unbinds (cutoff source target : Pattern) : Pattern :=
  .apply "Unbinds" [cutoff, source, target]
def plugs (context inner whole : Pattern) : Pattern :=
  .apply "Plugs" [context, inner, whole]
def rootStep (source target : Pattern) : Pattern :=
  .apply "RootStep" [source, target]
def converts (source target : Pattern) : Pattern :=
  .apply "Converts" [source, target]

def conversionDeclaration : ConversionDecl :=
  { judgmentHead := "Converts"
    version := "first-order-empty-signature-contextual-beta-eta-v2" }

def ruleId (value : String) : RuleId := ⟨value⟩

def formal (name : String) : String × Nat := (name, 0)

def rule (id : String) (names : List String)
    (premises : List Pattern) (conclusion : Pattern) : RuleSchema :=
  { id := ruleId id
    metavariables := names.map formal
    premises
    conclusion }

def m (name : String) : Pattern := .fvar name

/-! ## Peano arithmetic evidence -/

def ltZeroSuccRule : RuleSchema :=
  rule "lf-fo-lt-zero-succ" ["right"]
    [] (lt zero (succ (m "right")))

def ltSuccSuccRule : RuleSchema :=
  rule "lf-fo-lt-succ-succ" ["left", "right"]
    [lt (m "left") (m "right")]
    (lt (succ (m "left")) (succ (m "right")))

def addZeroRule : RuleSchema :=
  rule "lf-fo-add-zero" ["right"]
    [] (add zero (m "right") (m "right"))

def addSuccRule : RuleSchema :=
  rule "lf-fo-add-succ" ["left", "right", "result"]
    [add (m "left") (m "right") (m "result")]
    (add (succ (m "left")) (m "right") (succ (m "result")))

/-! ## Proof-carrying lift -/

def liftVarBelowRule : RuleSchema :=
  rule "lf-fo-lift-var-below" ["distance", "cutoff", "index"]
    [lt (m "index") (m "cutoff")]
    (lifts (m "distance") (m "cutoff")
      (var (m "index")) (var (m "index")))

def liftVarEqualRule : RuleSchema :=
  rule "lf-fo-lift-var-equal"
    ["distance", "cutoff", "result"]
    [add (m "cutoff") (m "distance") (m "result")]
    (lifts (m "distance") (m "cutoff")
      (var (m "cutoff")) (var (m "result")))

def liftVarAboveRule : RuleSchema :=
  rule "lf-fo-lift-var-above"
    ["distance", "cutoff", "index", "result"]
    [lt (m "cutoff") (m "index"),
     add (m "index") (m "distance") (m "result")]
    (lifts (m "distance") (m "cutoff")
      (var (m "index")) (var (m "result")))

def liftSrtRule : RuleSchema :=
  rule "lf-fo-lift-srt" ["distance", "cutoff", "sort"]
    [] (lifts (m "distance") (m "cutoff")
      (srt (m "sort")) (srt (m "sort")))

def liftConRule : RuleSchema :=
  rule "lf-fo-lift-con" ["distance", "cutoff", "name"]
    [] (lifts (m "distance") (m "cutoff")
      (con (m "name")) (con (m "name")))

def liftPiRule : RuleSchema :=
  rule "lf-fo-lift-pi"
    ["distance", "cutoff", "domain", "body", "domainResult", "bodyResult"]
    [lifts (m "distance") (m "cutoff")
        (m "domain") (m "domainResult"),
     lifts (m "distance") (succ (m "cutoff"))
        (m "body") (m "bodyResult")]
    (lifts (m "distance") (m "cutoff")
      (pi (m "domain") (m "body"))
      (pi (m "domainResult") (m "bodyResult")))

def liftLamRule : RuleSchema :=
  rule "lf-fo-lift-lam"
    ["distance", "cutoff", "domain", "body", "domainResult", "bodyResult"]
    [lifts (m "distance") (m "cutoff")
        (m "domain") (m "domainResult"),
     lifts (m "distance") (succ (m "cutoff"))
        (m "body") (m "bodyResult")]
    (lifts (m "distance") (m "cutoff")
      (lam (m "domain") (m "body"))
      (lam (m "domainResult") (m "bodyResult")))

def liftAppRule : RuleSchema :=
  rule "lf-fo-lift-app"
    ["distance", "cutoff", "function", "argument",
      "functionResult", "argumentResult"]
    [lifts (m "distance") (m "cutoff")
        (m "function") (m "functionResult"),
     lifts (m "distance") (m "cutoff")
        (m "argument") (m "argumentResult")]
    (lifts (m "distance") (m "cutoff")
      (app (m "function") (m "argument"))
      (app (m "functionResult") (m "argumentResult")))

/-! ## Proof-carrying substitution -/

def substVarEqualRule : RuleSchema :=
  rule "lf-fo-subst-var-equal" ["index", "replacement"]
    [] (substitutes (m "index") (m "replacement")
      (var (m "index")) (m "replacement"))

def substVarBelowRule : RuleSchema :=
  rule "lf-fo-subst-var-below" ["index", "replacement", "variable"]
    [lt (m "variable") (m "index")]
    (substitutes (m "index") (m "replacement")
      (var (m "variable")) (var (m "variable")))

def substVarAboveRule : RuleSchema :=
  rule "lf-fo-subst-var-above"
    ["index", "replacement", "predecessor"]
    [lt (m "index") (succ (m "predecessor"))]
    (substitutes (m "index") (m "replacement")
      (var (succ (m "predecessor"))) (var (m "predecessor")))

def substSrtRule : RuleSchema :=
  rule "lf-fo-subst-srt" ["index", "replacement", "sort"]
    [] (substitutes (m "index") (m "replacement")
      (srt (m "sort")) (srt (m "sort")))

def substConRule : RuleSchema :=
  rule "lf-fo-subst-con" ["index", "replacement", "name"]
    [] (substitutes (m "index") (m "replacement")
      (con (m "name")) (con (m "name")))

def substPiRule : RuleSchema :=
  rule "lf-fo-subst-pi"
    ["index", "replacement", "domain", "body", "domainResult",
      "liftedReplacement", "bodyResult"]
    [substitutes (m "index") (m "replacement")
        (m "domain") (m "domainResult"),
     lifts one zero (m "replacement") (m "liftedReplacement"),
     substitutes (succ (m "index")) (m "liftedReplacement")
        (m "body") (m "bodyResult")]
    (substitutes (m "index") (m "replacement")
      (pi (m "domain") (m "body"))
      (pi (m "domainResult") (m "bodyResult")))

def substLamRule : RuleSchema :=
  rule "lf-fo-subst-lam"
    ["index", "replacement", "domain", "body", "domainResult",
      "liftedReplacement", "bodyResult"]
    [substitutes (m "index") (m "replacement")
        (m "domain") (m "domainResult"),
     lifts one zero (m "replacement") (m "liftedReplacement"),
     substitutes (succ (m "index")) (m "liftedReplacement")
        (m "body") (m "bodyResult")]
    (substitutes (m "index") (m "replacement")
      (lam (m "domain") (m "body"))
      (lam (m "domainResult") (m "bodyResult")))

def substAppRule : RuleSchema :=
  rule "lf-fo-subst-app"
    ["index", "replacement", "function", "argument",
      "functionResult", "argumentResult"]
    [substitutes (m "index") (m "replacement")
        (m "function") (m "functionResult"),
     substitutes (m "index") (m "replacement")
        (m "argument") (m "argumentResult")]
    (substitutes (m "index") (m "replacement")
      (app (m "function") (m "argument"))
      (app (m "functionResult") (m "argumentResult")))

/-! ## Proof-carrying unused-variable elimination -/

def unbindVarBelowRule : RuleSchema :=
  rule "lf-fo-unbind-var-below" ["cutoff", "index"]
    [lt (m "index") (m "cutoff")]
    (unbinds (m "cutoff") (var (m "index")) (var (m "index")))

def unbindVarAboveRule : RuleSchema :=
  rule "lf-fo-unbind-var-above" ["cutoff", "predecessor"]
    [lt (m "cutoff") (succ (m "predecessor"))]
    (unbinds (m "cutoff")
      (var (succ (m "predecessor"))) (var (m "predecessor")))

def unbindSrtRule : RuleSchema :=
  rule "lf-fo-unbind-srt" ["cutoff", "sort"]
    [] (unbinds (m "cutoff") (srt (m "sort")) (srt (m "sort")))

def unbindConRule : RuleSchema :=
  rule "lf-fo-unbind-con" ["cutoff", "name"]
    [] (unbinds (m "cutoff") (con (m "name")) (con (m "name")))

def unbindPiRule : RuleSchema :=
  rule "lf-fo-unbind-pi"
    ["cutoff", "domain", "body", "domainResult", "bodyResult"]
    [unbinds (m "cutoff") (m "domain") (m "domainResult"),
     unbinds (succ (m "cutoff")) (m "body") (m "bodyResult")]
    (unbinds (m "cutoff")
      (pi (m "domain") (m "body"))
      (pi (m "domainResult") (m "bodyResult")))

def unbindLamRule : RuleSchema :=
  rule "lf-fo-unbind-lam"
    ["cutoff", "domain", "body", "domainResult", "bodyResult"]
    [unbinds (m "cutoff") (m "domain") (m "domainResult"),
     unbinds (succ (m "cutoff")) (m "body") (m "bodyResult")]
    (unbinds (m "cutoff")
      (lam (m "domain") (m "body"))
      (lam (m "domainResult") (m "bodyResult")))

def unbindAppRule : RuleSchema :=
  rule "lf-fo-unbind-app"
    ["cutoff", "function", "argument", "functionResult", "argumentResult"]
    [unbinds (m "cutoff") (m "function") (m "functionResult"),
     unbinds (m "cutoff") (m "argument") (m "argumentResult")]
    (unbinds (m "cutoff")
      (app (m "function") (m "argument"))
      (app (m "functionResult") (m "argumentResult")))

/-! ## Explicit context filling -/

def plugHoleRule : RuleSchema :=
  rule "lf-fo-plug-hole" ["inner"]
    [] (plugs hole (m "inner") (m "inner"))

def plugPiDomainRule : RuleSchema :=
  rule "lf-fo-plug-pi-domain"
    ["rest", "body", "inner", "domainResult"]
    [plugs (m "rest") (m "inner") (m "domainResult")]
    (plugs (piDomainContext (m "rest") (m "body")) (m "inner")
      (pi (m "domainResult") (m "body")))

def plugPiBodyRule : RuleSchema :=
  rule "lf-fo-plug-pi-body"
    ["domain", "rest", "inner", "bodyResult"]
    [plugs (m "rest") (m "inner") (m "bodyResult")]
    (plugs (piBodyContext (m "domain") (m "rest")) (m "inner")
      (pi (m "domain") (m "bodyResult")))

def plugLamDomainRule : RuleSchema :=
  rule "lf-fo-plug-lam-domain"
    ["rest", "body", "inner", "domainResult"]
    [plugs (m "rest") (m "inner") (m "domainResult")]
    (plugs (lamDomainContext (m "rest") (m "body")) (m "inner")
      (lam (m "domainResult") (m "body")))

def plugLamBodyRule : RuleSchema :=
  rule "lf-fo-plug-lam-body"
    ["domain", "rest", "inner", "bodyResult"]
    [plugs (m "rest") (m "inner") (m "bodyResult")]
    (plugs (lamBodyContext (m "domain") (m "rest")) (m "inner")
      (lam (m "domain") (m "bodyResult")))

def plugAppFunctionRule : RuleSchema :=
  rule "lf-fo-plug-app-function"
    ["rest", "argument", "inner", "functionResult"]
    [plugs (m "rest") (m "inner") (m "functionResult")]
    (plugs (appFunctionContext (m "rest") (m "argument")) (m "inner")
      (app (m "functionResult") (m "argument")))

def plugAppArgumentRule : RuleSchema :=
  rule "lf-fo-plug-app-argument"
    ["function", "rest", "inner", "argumentResult"]
    [plugs (m "rest") (m "inner") (m "argumentResult")]
    (plugs (appArgumentContext (m "function") (m "rest")) (m "inner")
      (app (m "function") (m "argumentResult")))

/-! ## Root and contextual conversion -/

def rootBetaRule : RuleSchema :=
  rule "lf-fo-root-beta" ["domain", "body", "argument", "result"]
    [substitutes zero (m "argument") (m "body") (m "result")]
    (rootStep
      (app (lam (m "domain") (m "body")) (m "argument"))
      (m "result"))

def rootEtaRule : RuleSchema :=
  rule "lf-fo-root-eta" ["domain", "function", "result"]
    [unbinds zero (m "function") (m "result")]
    (rootStep
      (lam (m "domain") (app (m "function") (var zero)))
      (m "result"))

def contextualConversionRule : RuleSchema :=
  rule "lf-fo-contextual-conversion"
    ["context", "rootSource", "rootTarget", "source", "target"]
    [rootStep (m "rootSource") (m "rootTarget"),
     plugs (m "context") (m "rootSource") (m "source"),
     plugs (m "context") (m "rootTarget") (m "target")]
    (converts (m "source") (m "target"))

/-- Reflexivity is explicit proof data rather than an endpoint shortcut. -/
def conversionReflRule : RuleSchema :=
  rule "lf-fo-conversion-refl" ["term"] []
    (converts (m "term") (m "term"))

/-- Compose two checked conversion certificates through one syntactically
shared intermediate term. -/
def conversionTransRule : RuleSchema :=
  rule "lf-fo-conversion-trans" ["source", "middle", "target"]
    [converts (m "source") (m "middle"),
     converts (m "middle") (m "target")]
    (converts (m "source") (m "target"))

def allRules : List RuleSchema :=
  [ltZeroSuccRule, ltSuccSuccRule, addZeroRule, addSuccRule,
   liftVarBelowRule, liftVarEqualRule, liftVarAboveRule,
   liftSrtRule, liftConRule, liftPiRule, liftLamRule, liftAppRule,
   substVarEqualRule, substVarBelowRule, substVarAboveRule,
   substSrtRule, substConRule, substPiRule, substLamRule, substAppRule,
   unbindVarBelowRule, unbindVarAboveRule, unbindSrtRule, unbindConRule,
   unbindPiRule, unbindLamRule, unbindAppRule,
   plugHoleRule, plugPiDomainRule, plugPiBodyRule,
   plugLamDomainRule, plugLamBodyRule,
   plugAppFunctionRule, plugAppArgumentRule,
   rootBetaRule, rootEtaRule, contextualConversionRule,
   conversionReflRule, conversionTransRule]

abbrev definition : CalculusLanguageDef :=
  { name := "indexed-lf-first-order-contextual-beta-eta"
    types := [natType, sortTypeDecl, nameType, termType, contextType]
    terms :=
      [constructor "Zero" "LFNat" [],
       constructor "Succ" "LFNat" [.simple "predecessor" (.base "LFNat")],
       constructor "TypeSort" "LFSort" [],
       constructor "KindSort" "LFSort" [],
       constructor "NameNil" "LFName" [],
       constructor "NameCons" "LFName"
         [.simple "codepoint" (.base "LFNat"),
          .simple "rest" (.base "LFName")],
       constructor "Srt" "LFTerm" [.simple "sort" (.base "LFSort")],
       constructor "Con" "LFTerm" [.simple "name" (.base "LFName")],
       constructor "Var" "LFTerm" [.simple "index" (.base "LFNat")],
       constructor "Pi" "LFTerm"
         [.simple "domain" (.base "LFTerm"), .simple "body" (.base "LFTerm")],
       constructor "Lam" "LFTerm"
         [.simple "domain" (.base "LFTerm"), .simple "body" (.base "LFTerm")],
       constructor "App" "LFTerm"
         [.simple "function" (.base "LFTerm"),
          .simple "argument" (.base "LFTerm")],
       constructor "Hole" "LFContext" [],
       constructor "PiDomainContext" "LFContext"
         [.simple "rest" (.base "LFContext"), .simple "body" (.base "LFTerm")],
       constructor "PiBodyContext" "LFContext"
         [.simple "domain" (.base "LFTerm"), .simple "rest" (.base "LFContext")],
       constructor "LamDomainContext" "LFContext"
         [.simple "rest" (.base "LFContext"), .simple "body" (.base "LFTerm")],
       constructor "LamBodyContext" "LFContext"
         [.simple "domain" (.base "LFTerm"), .simple "rest" (.base "LFContext")],
       constructor "AppFunctionContext" "LFContext"
         [.simple "rest" (.base "LFContext"),
          .simple "argument" (.base "LFTerm")],
       constructor "AppArgumentContext" "LFContext"
         [.simple "function" (.base "LFTerm"),
          .simple "rest" (.base "LFContext")]]
    equations := []
    rewrites := []
    judgments :=
      [{ head := "NatLt", arity := 2 },
       { head := "NatAdd", arity := 3 },
       { head := "Lifts", arity := 4 },
       { head := "Substitutes", arity := 4 },
       { head := "Unbinds", arity := 3 },
       { head := "Plugs", arity := 3 },
       { head := "RootStep", arity := 2 },
       { head := "Converts", arity := 2 }]
    rules := allRules
    conversion := some conversionDeclaration }

def language : LanguageDef := definition.toLanguageDef
def calculus := definition.toCalculus

theorem language_validate : language.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorOnly language <;>
    simp [language, natType, sortTypeDecl, nameType, termType, contextType,
      constructor, LanguageDef.typeNames, TypeDecl.plain,
      TermParam.typeExpr, TypeExpr.baseNames]

theorem definition_valid : definition.isValid = true := by
  have hvalidate : definition.toLanguageDef.validate = [] := by
    simpa [language] using language_validate
  unfold CalculusLanguageDef.isValid CalculusLanguageDef.hasValidLocalRules
  rw [hvalidate]
  simp [definition, CalculusLanguageDef.ruleIds,
    CalculusLanguageDef.judgmentSignatureValid,
    CalculusLanguageDef.judgmentHeads,
    CalculusLanguageDef.conversionDeclarationValid,
    CalculusLanguageDef.lookupJudgment?,
    RuleSchema.isValidIn, RuleSchema.isLocallyValid,
    RuleSchema.metavariableNames, RuleSchema.occurrences,
    RuleSchema.patterns,
    patternMetavariableOccurrencesAt, patternsMetavariableOccurrencesAt,
    patternHasNoCollectionRest, patternsHaveNoCollectionRest,
    CalculusLanguageDef.judgmentSchemaValid, fixedConstructorsValid,
    fixedConstructorListsValid, languageHasConstructorArity,
    Pattern.isWellScoped, Pattern.isWellScopedAt,
    Pattern.isWellScopedListAt, Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList, Pattern.zipHead,
    Pattern.mapHead, Pattern.evalHead, allRules,
    natType, sortTypeDecl, nameType, termType, contextType, constructor,
    conversionDeclaration, rule, formal, m,
    ltZeroSuccRule, ltSuccSuccRule, addZeroRule, addSuccRule,
    liftVarBelowRule, liftVarEqualRule, liftVarAboveRule,
    liftSrtRule, liftConRule, liftPiRule, liftLamRule, liftAppRule,
    substVarEqualRule, substVarBelowRule, substVarAboveRule,
    substSrtRule, substConRule, substPiRule, substLamRule, substAppRule,
    unbindVarBelowRule, unbindVarAboveRule, unbindSrtRule, unbindConRule,
    unbindPiRule, unbindLamRule, unbindAppRule,
    plugHoleRule, plugPiDomainRule, plugPiBodyRule,
    plugLamDomainRule, plugLamBodyRule,
    plugAppFunctionRule, plugAppArgumentRule,
    rootBetaRule, rootEtaRule, contextualConversionRule,
    conversionReflRule, conversionTransRule,
    lt, add, lifts, substitutes, unbinds, plugs, rootStep, converts,
    zero, succ, one, srt, con, var, pi, lam, app, hole,
    piDomainContext, piBodyContext, lamDomainContext, lamBodyContext,
    appFunctionContext, appArgumentContext, ruleId]
  simp (config := { maxSteps := 1000000, decide := true })

/-- The complete first-order LF conversion language as one GSLT. -/
def totalTheory : Mettapedia.GSLT.GSLT :=
  definition.toGSLTOfNoEquations definition_valid rfl

theorem totalTheory_Term : totalTheory.Term = (Pattern ⊕ List Pattern) := by
  unfold totalTheory CalculusLanguageDef.toGSLTOfNoEquations
  rfl

def source : GSLTSource :=
  { identity :=
      { systemId := "indexed-lf"
        revision := "first-order-contextual-beta-eta-v2"
        artifactDigest :=
          "lean-definition:LFFirstOrderContextualConversion.language" }
    assumptions := { entries := [] }
    profiles :=
      { entries :=
          [{ name := "signature"
             version := "empty-v1"
             payload := .apply "EmptySignature" [] },
           { name := "conversion"
             version := conversionDeclaration.version
             payload := .apply "ExplicitContextPath" [] }] }
    definition := definition }

def checked : CheckedGSLT :=
  { source
    identityValid := by decide
    assumptionsValid := by decide
    profilesValid := by decide
    definitionValid := by
      simpa [source] using definition_valid }

def rootedConversion : RootedConversion checked :=
  { declaration := conversionDeclaration
    isRooted := rfl }

def rawProof (id : String) (arguments : List Pattern)
    (children : List RawProof) : RawProof :=
  .node { ruleId := ruleId id, arguments } children

/-! ## Executable contextual beta fixture -/

def typeTerm : Pattern := srt typeSort
def identity : Pattern := lam typeTerm (var zero)
def betaSource : Pattern := app identity typeTerm
def piBetaSource : Pattern := pi typeTerm betaSource
def piBetaTarget : Pattern := pi typeTerm typeTerm
def piBodyHole : Pattern := piBodyContext typeTerm hole

def substIdentityProof : RawProof :=
  rawProof "lf-fo-subst-var-equal" [zero, typeTerm] []

def betaRootProof : RawProof :=
  rawProof "lf-fo-root-beta"
    [typeTerm, var zero, typeTerm, typeTerm]
    [substIdentityProof]

def plugBetaSourceProof : RawProof :=
  rawProof "lf-fo-plug-pi-body"
    [typeTerm, hole, betaSource, betaSource]
    [rawProof "lf-fo-plug-hole" [betaSource] []]

def plugBetaTargetProof : RawProof :=
  rawProof "lf-fo-plug-pi-body"
    [typeTerm, hole, typeTerm, typeTerm]
    [rawProof "lf-fo-plug-hole" [typeTerm] []]

def piBodyBetaProof : RawProof :=
  rawProof "lf-fo-contextual-conversion"
    [piBodyHole, betaSource, typeTerm, piBetaSource, piBetaTarget]
    [betaRootProof, plugBetaSourceProof, plugBetaTargetProof]

def piBodyBetaCertificate : RawConversionCertificate :=
  .step piBetaTarget piBodyBetaProof .refl

theorem pi_body_beta_certificate_accepts :
    check checked rootedConversion
      piBetaSource piBetaTarget piBodyBetaCertificate = true := by
  simp (config := { maxSteps := 1000000, decide := true })
    [check, RootedConversion.judgment, CheckedGSLT.checkRaw,
     InferenceChecker.checkRaw, InferenceChecker.checkRawChildren,
     CheckedGSLT.definition, checked, source, definition,
     rootedConversion, piBodyBetaCertificate, piBodyBetaProof, betaRootProof,
     substIdentityProof, plugBetaSourceProof, plugBetaTargetProof, rawProof,
     allRules, contextualConversionRule, rootBetaRule, substVarEqualRule,
     plugPiBodyRule, plugHoleRule, rule, formal, m, instantiateRule?,
     CalculusLanguageDef.lookupRule?, instantiateSchema?, instantiateSchemaAt?,
     instantiateSchemas?, instantiateSchemasAt?, lookupArgumentAt?,
     conversionDeclaration, converts, rootStep, substitutes, plugs,
     piBodyHole, betaSource, piBetaSource, piBetaTarget, typeTerm, identity,
     zero, srt, typeSort, var, pi, lam, app, hole, piBodyContext, ruleId]

/-- Captured eta has no successful unbind proof.  This deliberately malformed
tree tries the below-cutoff rule and then fabricates `0 < 0`. -/
def capturedEtaSource : Pattern :=
  lam typeTerm (app (var zero) (var zero))

def fabricatedCapturedUnbindProof : RawProof :=
  rawProof "lf-fo-unbind-var-below" [zero, zero]
    [rawProof "lf-fo-lt-zero-succ" [zero] []]

def fabricatedCapturedEtaProof : RawProof :=
  rawProof "lf-fo-root-eta" [typeTerm, var zero, var zero]
    [fabricatedCapturedUnbindProof]

theorem captured_eta_root_proof_rejects :
    checked.checkRaw
      (rootStep capturedEtaSource (var zero))
      fabricatedCapturedEtaProof = false := by
  simp (config := { maxSteps := 1000000, decide := true })
    [CheckedGSLT.checkRaw, InferenceChecker.checkRaw,
     InferenceChecker.checkRawChildren, CheckedGSLT.definition, checked,
     source, definition, fabricatedCapturedEtaProof,
     fabricatedCapturedUnbindProof, rawProof, allRules, rootEtaRule,
     unbindVarBelowRule, ltZeroSuccRule, rule, formal, m, instantiateRule?,
     CalculusLanguageDef.lookupRule?, instantiateSchema?, instantiateSchemaAt?,
     instantiateSchemas?, instantiateSchemasAt?, lookupArgumentAt?, rootStep,
     unbinds, lt, capturedEtaSource, typeTerm, zero, succ, srt, typeSort, var,
     lam, app, ruleId]

/-- A correct root beta proof cannot launder an unrelated whole-term target:
the final context-fill child fails. -/
def fabricatedContextTargetProof : RawProof :=
  rawProof "lf-fo-contextual-conversion"
    [piBodyHole, betaSource, typeTerm, piBetaSource, typeTerm]
    [betaRootProof, plugBetaSourceProof, plugBetaTargetProof]

theorem fabricated_context_target_rejects :
    checked.checkRaw
      (converts piBetaSource typeTerm)
      fabricatedContextTargetProof = false := by
  simp (config := { maxSteps := 1000000, decide := true })
    [CheckedGSLT.checkRaw, InferenceChecker.checkRaw,
     InferenceChecker.checkRawChildren, CheckedGSLT.definition, checked,
     source, definition, fabricatedContextTargetProof,
     betaRootProof, substIdentityProof, plugBetaSourceProof,
     plugBetaTargetProof, rawProof, allRules, contextualConversionRule,
     rootBetaRule, substVarEqualRule, plugPiBodyRule, plugHoleRule, rule,
     formal, m, instantiateRule?, CalculusLanguageDef.lookupRule?,
     instantiateSchema?, instantiateSchemaAt?, instantiateSchemas?,
     instantiateSchemasAt?, lookupArgumentAt?, converts, rootStep,
     substitutes, plugs, piBodyHole, betaSource, piBetaSource, typeTerm,
     identity, zero, srt, typeSort, var, pi, lam, app, hole, piBodyContext,
     ruleId]

#print axioms language_validate
#print axioms definition_valid
#print axioms pi_body_beta_certificate_accepts
#print axioms captured_eta_root_proof_rejects
#print axioms fabricated_context_target_rejects

end Mettapedia.GSLT.LanguageDef.LFFirstOrderContextualConversion
