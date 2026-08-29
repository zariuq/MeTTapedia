import Mettapedia.GSLT.LanguageDef.ContextualInferenceRule
import Mettapedia.GSLT.LanguageDef.CalculusLanguageExtension
import Mettapedia.OSLF.Framework.CarrierTypingLanguageDef

/-!
# Contextual claims over carrier-indexed typing judgments

The sparse native-type foundation declares one binary typing judgment for
each generated carrier.  Contextual modal rules need those same facts as
first-order formula data under explicit variable and relation contexts.

This module supplies one reusable bridge layer:

* one shared formula sort, context sort, and ternary contextual judgment;
* variable, typing, and reduction claim constructors for every carrier; and
* one rule lifting a carrier-indexed typing judgment into arbitrary explicit
  contexts.

The carrier family is append-homomorphic.  The shared context signature is
added once, after which later carriers contribute only their own claim rows
and bridge rule.  Applying the layer produces one ordinary flat
`CalculusLanguageDef`; the factorization exists for generation and proofs,
not as a nested runtime representation.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.ContextualCarrierClaims

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.ContextualInference
open Mettapedia.GSLT.LanguageDef.InferenceChecker

/-! ## Stable claim names -/

inductive ClaimKind
  | variable
  | typing
  | reduction
deriving Repr, DecidableEq

def ClaimKind.tag : ClaimKind → Char
  | .variable => 'v'
  | .typing => 't'
  | .reduction => 'r'

/-- Carrier-indexed constructor name in one reserved claim namespace. -/
def claimLabel (kind : ClaimKind) (carrier : String) : String :=
  String.ofList
    ("$oslf:claim:".toList ++ kind.tag :: ':' :: carrier.toList)

theorem claimLabel_injective (kind : ClaimKind) :
    Function.Injective (claimLabel kind) := by
  intro first second equality
  apply String.toList_injective
  have lists := congrArg String.toList equality
  simpa [claimLabel, ClaimKind.tag] using lists

theorem claimLabel_ne_of_kind_ne
    {first second : ClaimKind} (different : first ≠ second)
    (firstCarrier secondCarrier : String) :
    claimLabel first firstCarrier ≠ claimLabel second secondCarrier := by
  intro equality
  have lists := congrArg String.toList equality
  cases first <;> cases second <;>
    simp [claimLabel, ClaimKind.tag] at lists different

/-- Bridge-rule identifier for one carrier. -/
def bridgeRuleName (carrier : String) : String :=
  String.ofList
    ("$oslf:contextual-typing:".toList ++ carrier.toList)

theorem bridgeRuleName_injective : Function.Injective bridgeRuleName := by
  intro first second equality
  apply String.toList_injective
  have lists := congrArg String.toList equality
  simpa [bridgeRuleName] using lists

/-! ## Carrier-indexed claim constructors -/

def variableClaimTerm (carrier : String) : GrammarRule where
  label := claimLabel .variable carrier
  category := formulaType.name
  params := [.simple "term" (.base carrier)]
  syntaxPattern := []

def typingClaimTerm (carrier : String) : GrammarRule where
  label := claimLabel .typing carrier
  category := formulaType.name
  params :=
    [ .simple "term" (.base carrier)
    , .simple "type" (.base carrier) ]
  syntaxPattern := []

def reductionClaimTerm (carrier : String) : GrammarRule where
  label := claimLabel .reduction carrier
  category := formulaType.name
  params :=
    [ .simple "source" (.base carrier)
    , .simple "target" (.base carrier) ]
  syntaxPattern := []

def claimTerms (carrier : String) : List GrammarRule :=
  [variableClaimTerm carrier, typingClaimTerm carrier,
    reductionClaimTerm carrier]

def claimTermsFor (carrierNames : List String) : List GrammarRule :=
  carrierNames.flatMap claimTerms

@[simp] theorem claimTermsFor_append (first second : List String) :
    claimTermsFor (first ++ second) =
      claimTermsFor first ++ claimTermsFor second := by
  simp [claimTermsFor]

def variableClaim (carrier : String) (term : Pattern) : Pattern :=
  .apply (claimLabel .variable carrier) [term]

def typingClaim (carrier : String) (term type : Pattern) : Pattern :=
  .apply (claimLabel .typing carrier) [term, type]

def reductionClaim (carrier : String) (source target : Pattern) : Pattern :=
  .apply (claimLabel .reduction carrier) [source, target]

/-! ## Mixed-judgment bridge -/

private def gamma : ContextSchema := .hole "Gamma"
private def delta : ContextSchema := .hole "Delta"

/-- Lift a foundation typing fact into the contextual judgment under any two
ambient contexts.  The premise remains the existing carrier-indexed judgment;
the conclusion is its reified formula view. -/
def liftTypingRule (carrier : String) : RuleSchema where
  id := ⟨bridgeRuleName carrier⟩
  metavariables :=
    [("Gamma", 0), ("Delta", 0), ("term", 0), ("type", 0)]
  premises :=
    [.apply (CarrierTypingLanguageDef.typingHead carrier)
      [.fvar "term", .fvar "type"]]
  conclusion :=
    lowerSequent
      { variableContext := gamma
        relationContext := delta
        conclusion := typingClaim carrier (.fvar "term") (.fvar "type") }

theorem liftTypingRule_locallyValid (carrier : String) :
    RuleSchema.isLocallyValid (liftTypingRule carrier) = true := by
  simp [liftTypingRule, lowerSequent, encodeContext, gamma, delta,
    typingClaim, claimLabel, ClaimKind.tag, bridgeRuleName,
    RuleSchema.isLocallyValid, RuleSchema.metavariableNames,
    RuleSchema.occurrences, RuleSchema.patterns,
    patternMetavariableOccurrencesAt, patternsMetavariableOccurrencesAt,
    patternHasNoCollectionRest, patternsHaveNoCollectionRest,
    Pattern.isWellScoped, Pattern.isWellScopedAt,
    Pattern.isWellScopedListAt, Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList]
  decide

/-- Exact public checker shape of the contextual typing bridge.  Clients can
validate the bridge inside a larger flat calculus without reopening the
private names used to author its ambient contexts. -/
theorem liftTypingRule_patterns (carrier : String) :
    RuleSchema.patterns (liftTypingRule carrier) =
      [ .apply (CarrierTypingLanguageDef.typingHead carrier)
          [.fvar "term", .fvar "type"]
      , .apply contextualJudgment.head
          [.fvar "Gamma", .fvar "Delta",
            typingClaim carrier (.fvar "term") (.fvar "type")] ] := by
  rfl

def bridgeRules (carrierNames : List String) : List RuleSchema :=
  carrierNames.map liftTypingRule

@[simp] theorem bridgeRules_append (first second : List String) :
    bridgeRules (first ++ second) = bridgeRules first ++ bridgeRules second := by
  simp [bridgeRules]

/-! ## Lawful flat extensions -/

/-- Shared contextual rows, emitted exactly once. -/
def contextExtension : CalculusLanguageExtension where
  newTypes := [formulaType, contextType]
  newTerms := [emptyContextTerm, extendContextTerm]
  newJudgments := [contextualJudgment]

/-- Per-carrier rows, suitable for incremental append. -/
def carrierExtension (carrierNames : List String) :
    CalculusLanguageExtension where
  newTerms := claimTermsFor carrierNames
  newRules := bridgeRules carrierNames

/-- Per-carrier contextual generation preserves ordered composition exactly. -/
theorem carrierExtension_append (first second : List String) :
    carrierExtension (first ++ second) =
      (carrierExtension first).comp (carrierExtension second) := by
  simp [carrierExtension, CalculusLanguageExtension.comp]

/-- Complete contextual-claim delta: shared rows once, then the carrier
family. -/
def extension (carrierNames : List String) : CalculusLanguageExtension :=
  contextExtension.comp (carrierExtension carrierNames)

/-- Apply the generation layer to an existing flat carrier calculus. -/
def apply (base : CalculusLanguageDef) (carrierNames : List String) :
    CalculusLanguageDef :=
  (extension carrierNames).apply base

@[simp] theorem apply_types (base : CalculusLanguageDef)
    (carrierNames : List String) :
    (apply base carrierNames).types =
      base.types ++ [formulaType, contextType] := by
  simp [apply, extension, contextExtension, carrierExtension,
    CalculusLanguageExtension.comp]

@[simp] theorem apply_terms (base : CalculusLanguageDef)
    (carrierNames : List String) :
    (apply base carrierNames).terms =
      base.terms ++
        ([emptyContextTerm, extendContextTerm] ++ claimTermsFor carrierNames) := by
  simp [apply, extension, contextExtension, carrierExtension,
    CalculusLanguageExtension.comp]

@[simp] theorem apply_equations (base : CalculusLanguageDef)
    (carrierNames : List String) :
    (apply base carrierNames).equations = base.equations := by
  simp [apply, extension, contextExtension, carrierExtension,
    CalculusLanguageExtension.comp]

@[simp] theorem apply_rewrites (base : CalculusLanguageDef)
    (carrierNames : List String) :
    (apply base carrierNames).rewrites = base.rewrites := by
  simp [apply, extension, contextExtension, carrierExtension,
    CalculusLanguageExtension.comp]

@[simp] theorem apply_judgments (base : CalculusLanguageDef)
    (carrierNames : List String) :
    (apply base carrierNames).judgments =
      base.judgments ++ [contextualJudgment] := by
  simp [apply, extension, contextExtension, carrierExtension,
    CalculusLanguageExtension.comp]

@[simp] theorem apply_rules (base : CalculusLanguageDef)
    (carrierNames : List String) :
    (apply base carrierNames).rules =
      base.rules ++ bridgeRules carrierNames := by
  simp [apply, extension, contextExtension, carrierExtension,
    CalculusLanguageExtension.comp]

@[simp] theorem apply_conversion (base : CalculusLanguageDef)
    (carrierNames : List String) :
    (apply base carrierNames).conversion = base.conversion := by
  rfl

/-! ## Concrete admission canary -/

namespace Canary

private def carrierA : TypeDecl := TypeDecl.plain "$oslf:claim-canary:A"
private def carrierB : TypeDecl := TypeDecl.plain "$oslf:claim-canary:B"

private def sourceLanguage : LanguageDef :=
  { name := "$oslf:contextual-claim-canary"
    types := [carrierA, carrierB]
    terms := []
    equations := []
    rewrites := [] }

private theorem sourceLanguage_valid : sourceLanguage.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorOnly <;>
    simp [sourceLanguage, carrierA, carrierB,
      LanguageDef.typeNames, TypeDecl.plain]

private def source : ValidatedLanguageDef :=
  ⟨sourceLanguage, sourceLanguage_valid⟩

/-- One ordinary flat definition containing carrier universes, their binary
typing judgments, explicit contexts, reified claims, and the bridge rules. -/
def definition : CalculusLanguageDef :=
  apply (CarrierTypingLanguageDef.definition source)
    [carrierA.name, carrierB.name]

theorem definition_valid : definition.isValid = true := by
  have validate : definition.toLanguageDef.validate = [] := by
    apply LanguageDef.validate_eq_nil_of_constructorOnly <;>
      simp [definition, apply, extension, contextExtension, carrierExtension,
        claimTermsFor, claimTerms, variableClaimTerm, typingClaimTerm,
        reductionClaimTerm, formulaType, contextType, emptyContextTerm,
        extendContextTerm, source, sourceLanguage, carrierA, carrierB,
        CarrierTypingLanguageDef.definition,
        CarrierTypingLanguageDef.calculus,
        CarrierTypingLanguageDef.judgments,
        CarrierTypingLanguageDef.axioms,
        CarrierUniverseSignature.language,
        CarrierUniverseSignature.terms,
        CarrierUniverseSignature.termsFor,
        CarrierUniverseSignature.rule,
        CarrierUniverseSignature.label,
        CarrierUniverseSignature.Code.tag,
        claimLabel, ClaimKind.tag,
        CalculusLanguageExtension.comp,
        CalculusLanguageExtension.apply,
        LanguageDef.typeNames, TypeDecl.plain,
        TermParam.typeExpr, TypeExpr.baseNames]
  unfold CalculusLanguageDef.isValid CalculusLanguageDef.hasValidLocalRules
  rw [validate]
  simp [definition, apply, extension, contextExtension, carrierExtension,
    claimTermsFor, claimTerms, bridgeRules, liftTypingRule,
    lowerSequent, encodeContext, gamma, delta, typingClaim,
    variableClaimTerm, typingClaimTerm, reductionClaimTerm,
    formulaType, contextType, emptyContextTerm, extendContextTerm,
    contextualJudgment, source, sourceLanguage, carrierA, carrierB,
    CarrierTypingLanguageDef.definition,
    CarrierTypingLanguageDef.calculus,
    CarrierTypingLanguageDef.judgments,
    CarrierTypingLanguageDef.axioms,
    CarrierTypingLanguageDef.judgment,
    CarrierTypingLanguageDef.universeAxiom,
    CarrierTypingLanguageDef.typingHead,
    CarrierTypingLanguageDef.axiomName,
    CarrierUniverseSignature.language,
    CarrierUniverseSignature.terms,
    CarrierUniverseSignature.termsFor,
    CarrierUniverseSignature.rule,
    CarrierUniverseSignature.label,
    CarrierUniverseSignature.Code.tag,
    claimLabel, ClaimKind.tag, bridgeRuleName,
    CalculusLanguageExtension.comp,
    CalculusLanguageExtension.apply,
    CalculusLanguageDef.ruleIds,
    CalculusLanguageDef.judgmentSignatureValid,
    CalculusLanguageDef.judgmentHeads,
    CalculusLanguageDef.conversionDeclarationValid,
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
    Pattern.mapHead, Pattern.evalHead]
  decide

/-- The context bridge retains the carrier coordinate. -/
theorem carrier_claims_distinct :
    typingClaim carrierA.name (.fvar "term") (.fvar "type") ≠
      typingClaim carrierB.name (.fvar "term") (.fvar "type") := by
  intro equality
  unfold typingClaim at equality
  injection equality with labels _arguments
  have carrierNames : carrierA.name = carrierB.name :=
    claimLabel_injective .typing labels
  exact (by decide : carrierA.name ≠ carrierB.name) carrierNames

/-- The admitted record denotes one combined GSLT. -/
def theory : Mettapedia.GSLT.GSLT :=
  definition.toGSLTOfNoEquations definition_valid rfl

theorem theory_term : theory.Term = (Pattern ⊕ List Pattern) :=
  rfl

end Canary

#print axioms claimLabel_injective
#print axioms claimLabel_ne_of_kind_ne
#print axioms carrierExtension_append
#print axioms liftTypingRule_locallyValid
#print axioms Canary.definition_valid
#print axioms Canary.carrier_claims_distinct

end Mettapedia.OSLF.Framework.ContextualCarrierClaims
