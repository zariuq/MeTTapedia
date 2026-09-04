import Mettapedia.GSLT.LanguageDef.ContextualInferenceRule
import Mettapedia.GSLT.LanguageDef.CalculusLanguageExtension
import Mettapedia.GSLT.LanguageDef.ContextualInferenceCanonicalContext
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

/-- Decode exactly the generated contextual-claim namespace. -/
def decodeClaimLabel? (name : String) : Option (ClaimKind × String) :=
  match name.toList with
  | '$' :: 'o' :: 's' :: 'l' :: 'f' :: ':' ::
      'c' :: 'l' :: 'a' :: 'i' :: 'm' :: ':' :: 'v' :: ':' :: carrier =>
      some (.variable, String.ofList carrier)
  | '$' :: 'o' :: 's' :: 'l' :: 'f' :: ':' ::
      'c' :: 'l' :: 'a' :: 'i' :: 'm' :: ':' :: 't' :: ':' :: carrier =>
      some (.typing, String.ofList carrier)
  | '$' :: 'o' :: 's' :: 'l' :: 'f' :: ':' ::
      'c' :: 'l' :: 'a' :: 'i' :: 'm' :: ':' :: 'r' :: ':' :: carrier =>
      some (.reduction, String.ofList carrier)
  | _ => none

@[simp]
theorem decodeClaimLabel?_claimLabel (kind : ClaimKind) (carrier : String) :
    decodeClaimLabel? (claimLabel kind carrier) = some (kind, carrier) := by
  cases kind <;> simp [decodeClaimLabel?, claimLabel, ClaimKind.tag]

/-- Successful claim decoding reconstructs the exact generated label. -/
theorem claimLabel_of_decodeClaimLabel?_eq_some
    {name : String} {kind : ClaimKind} {carrier : String}
    (decoded : decodeClaimLabel? name = some (kind, carrier)) :
    claimLabel kind carrier = name := by
  unfold decodeClaimLabel? at decoded
  split at decoded <;> try { simp at decoded }
  all_goals
    cases decoded
    rw [← String.ofList_toList (s := name)]
    simp_all [claimLabel, ClaimKind.tag]

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

/-- Lift a foundation typing fact into the contextual judgment under two
certified ambient contexts.  The first two premises prevent arbitrary ground
wires from masquerading as context encodings; the final premise remains the
existing carrier-indexed judgment. -/
def liftTypingRule (carrier : String) : RuleSchema where
  id := ⟨bridgeRuleName carrier⟩
  metavariables :=
    [("Gamma", 0), ("Delta", 0), ("term", 0), ("type", 0)]
  premises :=
    [ lowerSequent
        (ContextualInferenceCanonicalContext.premise "Gamma")
    , lowerSequent
        (ContextualInferenceCanonicalContext.premise "Delta")
    , .apply (CarrierTypingLanguageDef.typingHead carrier)
        [.fvar "term", .fvar "type"] ]
  conclusion :=
    lowerSequent
      { variableContext := gamma
        relationContext := delta
        conclusion := typingClaim carrier (.fvar "term") (.fvar "type") }

theorem liftTypingRule_locallyValid (carrier : String) :
    RuleSchema.isLocallyValid (liftTypingRule carrier) = true := by
  simp [liftTypingRule, lowerSequent, encodeContext, gamma, delta,
    ContextualInferenceCanonicalContext.premise,
    ContextualInferenceCanonicalContext.sequent,
    ContextualInferenceCanonicalContext.claim,
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
      [ lowerSequent
          (ContextualInferenceCanonicalContext.premise "Gamma")
      , lowerSequent
          (ContextualInferenceCanonicalContext.premise "Delta")
      , .apply (CarrierTypingLanguageDef.typingHead carrier)
          [.fvar "term", .fvar "type"]
      , .apply contextualJudgment.head
          [.fvar "Gamma", .fvar "Delta",
            typingClaim carrier (.fvar "term") (.fvar "type")] ] := by
  rfl

/-- An admitted application of a carrier bridge has one exact argument row,
two canonical-context certificate premises, the original direct typing
premise, and the corresponding contextual conclusion.  This is a structural
inversion theorem: it assigns no semantic meaning to any of those wires. -/
theorem liftTypingRule_application_exact
    (carrier : String) {definition : ValidatedCalculusLanguageDef}
    {ruleInstance : RuleInstance} {premises : List Pattern}
    {conclusion : Pattern}
    (lookup : definition.1.lookupRule? ruleInstance.ruleId =
      some (liftTypingRule carrier))
    (application :
      RuleApplication definition ruleInstance premises conclusion) :
    ∃ gammaWire deltaWire term type,
      ruleInstance.arguments = [gammaWire, deltaWire, term, type] ∧
      premises =
        [ lowerSequent
            (ContextualInferenceCanonicalContext.sequent gammaWire)
        , lowerSequent
            (ContextualInferenceCanonicalContext.sequent deltaWire)
        , .apply (CarrierTypingLanguageDef.typingHead carrier) [term, type] ] ∧
      conclusion =
        .apply contextualJudgment.head
          [gammaWire, deltaWire, typingClaim carrier term type] := by
  cases application with
  | intro actualRule actualLookup argumentsValid _sideConditionsValid
      premisesInstantiate conclusionInstantiates =>
      have actualRuleExact : actualRule = liftTypingRule carrier := by
        rw [actualLookup] at lookup
        exact Option.some.inj lookup
      subst actualRule
      have argumentsLength : ruleInstance.arguments.length = 4 := by
        have exactLength :=
          InferenceChecker.argumentsValidAt_length argumentsValid
        simpa [liftTypingRule] using exactLength.symm
      obtain ⟨gammaWire, deltaWire, term, type, argumentsExact⟩ :=
        List.length_eq_four.mp argumentsLength
      rw [argumentsExact] at premisesInstantiate conclusionInstantiates
      have premisesComputed :=
        instantiateSchemasAt?_complete premisesInstantiate
      have conclusionComputed :=
        instantiateSchemaAt?_complete conclusionInstantiates
      refine ⟨gammaWire, deltaWire, term, type, argumentsExact, ?_, ?_⟩
      · simpa [liftTypingRule,
          ContextualInferenceCanonicalContext.premise,
          ContextualInferenceCanonicalContext.sequent,
          ContextualInferenceCanonicalContext.claim,
          lowerSequent, encodeContext, gamma, delta, typingClaim,
          instantiateSchemas?, instantiateSchema?, instantiateSchemaAt?,
          instantiateSchemasAt?, lookupArgumentAt?] using
            premisesComputed.symm
      · simpa [liftTypingRule, lowerSequent, encodeContext, gamma, delta,
          typingClaim, instantiateSchema?, instantiateSchemaAt?,
          instantiateSchemasAt?, lookupArgumentAt?] using
            conclusionComputed.symm

def bridgeRules (carrierNames : List String) : List RuleSchema :=
  carrierNames.map liftTypingRule

@[simp] theorem bridgeRules_append (first second : List String) :
    bridgeRules (first ++ second) = bridgeRules first ++ bridgeRules second := by
  simp [bridgeRules]

/-! ## Lawful flat extensions -/

/-- Shared contextual rows and canonical-context certificates, emitted exactly
once. -/
def contextExtension : CalculusLanguageExtension where
  newTypes := [formulaType, contextType]
  newTerms := [emptyContextTerm, extendContextTerm] ++
    ContextualInferenceCanonicalContext.extension.newTerms
  newJudgments := [contextualJudgment]
  newRules := ContextualInferenceCanonicalContext.extension.newRules

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
        ([emptyContextTerm, extendContextTerm] ++
          ContextualInferenceCanonicalContext.extension.newTerms ++
            claimTermsFor carrierNames) := by
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
      base.rules ++
        ContextualInferenceCanonicalContext.extension.newRules ++
          bridgeRules carrierNames := by
  simp [apply, extension, contextExtension, carrierExtension,
    CalculusLanguageExtension.comp, List.append_assoc]

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
        ContextualInferenceCanonicalContext.extension,
        ContextualInferenceCanonicalContext.contextCodeTerm,
        ContextualInferenceCanonicalContext.nilRule,
        ContextualInferenceCanonicalContext.consRule,
        ContextualInferenceCanonicalContext.premise,
        ContextualInferenceCanonicalContext.sequent,
        ContextualInferenceCanonicalContext.claim,
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
    ContextualInferenceCanonicalContext.extension,
    ContextualInferenceCanonicalContext.contextCodeTerm,
    ContextualInferenceCanonicalContext.nilRule,
    ContextualInferenceCanonicalContext.consRule,
    ContextualInferenceCanonicalContext.premise,
    ContextualInferenceCanonicalContext.sequent,
    ContextualInferenceCanonicalContext.claim,
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
    Pattern.mapHead, Pattern.evalHead, LanguageDef.typeNames, TypeDecl.plain]
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
  definition.toGSLTOfEquationFree definition_valid rfl

theorem theory_term : theory.Term = (Pattern ⊕ List Pattern) :=
  rfl

end Canary

#print axioms claimLabel_injective
#print axioms claimLabel_ne_of_kind_ne
#print axioms decodeClaimLabel?_claimLabel
#print axioms claimLabel_of_decodeClaimLabel?_eq_some
#print axioms carrierExtension_append
#print axioms liftTypingRule_locallyValid
#print axioms liftTypingRule_application_exact
#print axioms Canary.definition_valid
#print axioms Canary.carrier_claims_distinct

end Mettapedia.OSLF.Framework.ContextualCarrierClaims
