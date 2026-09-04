import Mettapedia.GSLT.LanguageDef.ContextualInferenceRule
import Mettapedia.GSLT.LanguageDef.CalculusLanguageExtension
import Mettapedia.OSLF.Framework.CarrierUniverseSignature

/-!
# A complete single-rely contextual modal calculus

This module realizes the one-rely instance of the contextual modal rules from
the native-type construction. It is deliberately small but not context-free:
the result type is a one-variable family, introduction carries an authored
one-step reduction assumption, and elimination discharges a generic focus,
its reduct, and the reduct typing evidence into an arbitrary predicate.

The authoring rules use `ContextualInference.Rule`. Their injective lowering
is an ordinary `RuleSchema`, and the resulting checked artifact is one flat
`CalculusLanguageDef`. The `star`/`box` assignment changes only the generated
rule extension; the shared carrier, modal, claim, and context signatures are
unchanged.

This is the arity-one base case for the list-indexed occurrence generator. It
does not claim that every displayed rewrite occurrence has one rely.
-/

namespace Mettapedia.OSLF.Framework.SingleRelyContextualModalInference

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.ContextualInference
open Mettapedia.GSLT.LanguageDef.InferenceChecker

/-! ## Flat signature -/

def termType : TypeDecl := TypeDecl.plain "$oslf:single-rely:term"

def modalTerm : GrammarRule where
  label := "$oslf:single-rely:modal"
  category := termType.name
  params :=
    [ .simple "rely-type" (.base termType.name)
    , .simple "result-family"
        (.arrow (.base termType.name) (.base termType.name)) ]
  syntaxPattern := []

/-- The fixed one-hole context is represented by a constructor whose first
argument is its rely parameter and whose second argument fills the hole. -/
def contextPlugTerm : GrammarRule where
  label := "$oslf:single-rely:plug"
  category := termType.name
  params :=
    [ .simple "parameter" (.base termType.name)
    , .simple "focus" (.base termType.name) ]
  syntaxPattern := []

def variableClaimTerm : GrammarRule where
  label := "$oslf:single-rely:variable"
  category := formulaType.name
  params := [.simple "term" (.base termType.name)]
  syntaxPattern := []

def typingClaimTerm : GrammarRule where
  label := "$oslf:single-rely:typing"
  category := formulaType.name
  params :=
    [ .simple "term" (.base termType.name)
    , .simple "type" (.base termType.name) ]
  syntaxPattern := []

def reductionClaimTerm : GrammarRule where
  label := "$oslf:single-rely:reduces"
  category := formulaType.name
  params :=
    [ .simple "source" (.base termType.name)
    , .simple "target" (.base termType.name) ]
  syntaxPattern := []

def universeTerms : List GrammarRule :=
  [ CarrierUniverseSignature.rule .star termType.name
  , CarrierUniverseSignature.rule .box termType.name ]

@[simp]
theorem starLabel_eq :
    CarrierUniverseSignature.label .star termType.name =
      "$oslf:u:s$oslf:single-rely:term" :=
  rfl

@[simp]
theorem boxLabel_eq :
    CarrierUniverseSignature.label .box termType.name =
      "$oslf:u:b$oslf:single-rely:term" :=
  rfl

/-- Profile-independent syntax shared by every local vertex. -/
def signature : CalculusLanguageDef where
  name := "$oslf:single-rely-contextual-modal"
  types := [termType, formulaType, contextType]
  terms := universeTerms ++
    [ modalTerm, contextPlugTerm, variableClaimTerm, typingClaimTerm,
      reductionClaimTerm, emptyContextTerm, extendContextTerm ]
  equations := []
  rewrites := []
  judgments := [contextualJudgment]
  rules := []

/-! ## Reified formula constructors -/

def sortCode (code : CarrierUniverseSignature.Code) : Pattern :=
  .apply (CarrierUniverseSignature.label code termType.name) []

def variableClaim (term : Pattern) : Pattern :=
  .apply variableClaimTerm.label [term]

def typingClaim (term type : Pattern) : Pattern :=
  .apply typingClaimTerm.label [term, type]

def reductionClaim (source target : Pattern) : Pattern :=
  .apply reductionClaimTerm.label [source, target]

def modalType (relyType resultBody : Pattern) : Pattern :=
  .apply modalTerm.label [relyType, .lambda none resultBody]

def resultAt (resultBody parameter : Pattern) : Pattern :=
  .subst resultBody parameter

def contextPlug (parameter focus : Pattern) : Pattern :=
  .apply contextPlugTerm.label [parameter, focus]

private def gamma : ContextSchema := .hole "Gamma"
private def delta : ContextSchema := .hole "Delta"

private def ruleId (name : String) : RuleId := ⟨name⟩

/-! ## Profile-sensitive rules -/

/-- The carrier universe axiom is polymorphic in the two ambient contexts. -/
def universeRule : ContextualInference.Rule where
  id := ruleId "$oslf:single-rely:universe"
  metavariables := [("Gamma", 0), ("Delta", 0)]
  premises := []
  conclusion :=
    { variableContext := gamma
      relationContext := delta
      conclusion := typingClaim (sortCode .star) (sortCode .box) }

/-- Formation checks the rely type in the ambient context and the dependent
result body under the rely parameter assumption. -/
def formationRule (relySort resultSort : CarrierUniverseSignature.Code) :
    ContextualInference.Rule where
  id := ruleId "$oslf:single-rely:formation"
  metavariables :=
    [("Gamma", 0), ("Delta", 0), ("relyType", 0),
     ("resultBody", 1), ("parameter", 0)]
  premises :=
    [ { variableContext := gamma
        relationContext := delta
        conclusion := typingClaim (.fvar "relyType") (sortCode relySort) }
    , { variableContext :=
          .extend (variableClaim (.fvar "parameter")) gamma
        relationContext :=
          .extend (typingClaim (.fvar "parameter") (.fvar "relyType")) delta
        conclusion :=
          typingClaim
            (resultAt (.fvar "resultBody") (.fvar "parameter"))
            (sortCode resultSort) } ]
  conclusion :=
    { variableContext := gamma
      relationContext := delta
      conclusion :=
        typingClaim
          (modalType (.fvar "relyType") (.fvar "resultBody"))
          (sortCode resultSort) }

/-- Introduction exposes the operational content: after placing the focus in
the fixed context, one authored step reaches a reduct inhabiting the dependent
result family. -/
def introductionRule (relySort resultSort : CarrierUniverseSignature.Code) :
    ContextualInference.Rule where
  id := ruleId "$oslf:single-rely:introduction"
  metavariables :=
    [("Gamma", 0), ("Delta", 0), ("relyType", 0),
     ("resultBody", 1), ("parameter", 0), ("focus", 0),
     ("reduct", 0)]
  premises :=
    [ { variableContext := gamma
        relationContext := delta
        conclusion := typingClaim (.fvar "relyType") (sortCode relySort) }
    , { variableContext :=
          .extend (variableClaim (.fvar "parameter")) gamma
        relationContext :=
          .extend (typingClaim (.fvar "parameter") (.fvar "relyType")) delta
        conclusion :=
          typingClaim
            (resultAt (.fvar "resultBody") (.fvar "parameter"))
            (sortCode resultSort) }
    , { variableContext :=
          ContextSchema.prepend
            [variableClaim (.fvar "focus"),
             variableClaim (.fvar "parameter")] gamma
        relationContext :=
          ContextSchema.prepend
            [ reductionClaim
                (contextPlug (.fvar "parameter") (.fvar "focus"))
                (.fvar "reduct")
            , typingClaim (.fvar "parameter") (.fvar "relyType") ] delta
        conclusion :=
          typingClaim (.fvar "reduct")
            (resultAt (.fvar "resultBody") (.fvar "parameter")) } ]
  conclusion :=
    { variableContext := gamma
      relationContext := delta
      conclusion :=
        typingClaim (.fvar "focus")
          (modalType (.fvar "relyType") (.fvar "resultBody")) }

/-- Elimination is proof-relevant hypothetical discharge. The premise proves
an arbitrary predicate for a generic focus using a generic reduct and its
typing evidence; the conclusion transfers that predicate to an inhabitant of
the modal type. -/
def eliminationRule (relySort resultSort : CarrierUniverseSignature.Code) :
    ContextualInference.Rule where
  id := ruleId "$oslf:single-rely:elimination"
  metavariables :=
    [("Gamma", 0), ("Delta", 0), ("relyType", 0),
     ("resultBody", 1), ("parameter", 0), ("genericFocus", 0),
     ("reduct", 0), ("member", 0), ("predicateBody", 1)]
  premises :=
    [ { variableContext := gamma
        relationContext := delta
        conclusion := typingClaim (.fvar "relyType") (sortCode relySort) }
    , { variableContext :=
          .extend (variableClaim (.fvar "parameter")) gamma
        relationContext :=
          .extend (typingClaim (.fvar "parameter") (.fvar "relyType")) delta
        conclusion :=
          typingClaim
            (resultAt (.fvar "resultBody") (.fvar "parameter"))
            (sortCode resultSort) }
    , { variableContext :=
          ContextSchema.prepend
            [variableClaim (.fvar "genericFocus"),
             variableClaim (.fvar "parameter")] gamma
        relationContext :=
          ContextSchema.prepend
            [ typingClaim (.fvar "reduct")
                (resultAt (.fvar "resultBody") (.fvar "parameter"))
            , reductionClaim
                (contextPlug (.fvar "parameter") (.fvar "genericFocus"))
                (.fvar "reduct")
            , typingClaim (.fvar "parameter") (.fvar "relyType") ] delta
        conclusion :=
          resultAt (.fvar "predicateBody") (.fvar "genericFocus") } ]
  conclusion :=
    { variableContext :=
        .extend (variableClaim (.fvar "member")) gamma
      relationContext :=
        .extend
          (typingClaim (.fvar "member")
            (modalType (.fvar "relyType") (.fvar "resultBody"))) delta
      conclusion := resultAt (.fvar "predicateBody") (.fvar "member") }

def profiledRules (relySort resultSort : CarrierUniverseSignature.Code) :
    List RuleSchema :=
  [ lowerRule universeRule
  , lowerRule (formationRule relySort resultSort)
  , lowerRule (introductionRule relySort resultSort)
  , lowerRule (eliminationRule relySort resultSort) ]

/-- Profile selection is a lawful calculus-layer extension, not concatenation
of independently completed generated languages. -/
def profileExtension (relySort resultSort : CarrierUniverseSignature.Code) :
    CalculusLanguageExtension where
  newRules := profiledRules relySort resultSort

/-- One ordinary flat GSLT authoring record at the selected local vertex. -/
def definition (relySort resultSort : CarrierUniverseSignature.Code) :
    CalculusLanguageDef :=
  (profileExtension relySort resultSort).apply signature

/-! ## Admission and exact controls -/

theorem definition_valid (relySort resultSort : CarrierUniverseSignature.Code) :
    (definition relySort resultSort).isValid = true := by
  have validate :
      (definition relySort resultSort).toLanguageDef.validate = [] := by
    apply LanguageDef.validate_eq_nil_of_constructorOnly <;>
      simp [definition, profileExtension, signature, universeTerms, termType,
        formulaType, contextType, modalTerm, contextPlugTerm,
        variableClaimTerm, typingClaimTerm, reductionClaimTerm,
        emptyContextTerm, extendContextTerm, CarrierUniverseSignature.rule,
        CarrierUniverseSignature.label, CarrierUniverseSignature.Code.tag,
        LanguageDef.typeNames, TypeDecl.plain, TermParam.typeExpr,
        TypeExpr.baseNames]
  unfold CalculusLanguageDef.isValid CalculusLanguageDef.hasValidLocalRules
  rw [validate]
  cases relySort <;> cases resultSort <;>
    simp [definition, profileExtension, signature, profiledRules,
      universeRule, formationRule, introductionRule, eliminationRule,
      lowerRule, lowerSequent, encodeContext, ContextSchema.prepend,
      gamma, delta, ruleId, sortCode, variableClaim, typingClaim,
      reductionClaim, modalType, resultAt, contextPlug,
      universeTerms, termType, formulaType, contextType, modalTerm,
      contextPlugTerm, variableClaimTerm, typingClaimTerm,
      reductionClaimTerm, emptyContextTerm, extendContextTerm,
      contextualJudgment, CarrierUniverseSignature.rule,
      CarrierUniverseSignature.label,
      CarrierUniverseSignature.Code.tag, TypeDecl.plain,
      CalculusLanguageDef.ruleIds,
      CalculusLanguageDef.judgmentSignatureValid,
      CalculusLanguageDef.judgmentHeads,
      CalculusLanguageDef.conversionDeclarationValid,
      CalculusLanguageDef.lookupJudgment?, RuleSchema.isValidIn,
      RuleSchema.isLocallyValid,
      RuleSchema.metavariableNames, RuleSchema.occurrences,
      RuleSchema.patterns, patternMetavariableOccurrencesAt,
      patternsMetavariableOccurrencesAt, patternHasNoCollectionRest,
      patternsHaveNoCollectionRest,
      CalculusLanguageDef.judgmentSchemaValid, fixedConstructorsValid,
      fixedConstructorListsValid, languageHasConstructorArity,
      Pattern.isWellScoped, Pattern.isWellScopedAt,
      Pattern.isWellScopedListAt, Pattern.hasCanonicalBinderMetadata,
      Pattern.hasCanonicalBinderMetadataList, Pattern.zipHead,
      Pattern.mapHead, Pattern.evalHead] <;>
    decide

/-- Each contextual rule is accepted by the exact generic checker. -/
theorem generated_rules_valid
    (relySort resultSort : CarrierUniverseSignature.Code) :
    (profiledRules relySort resultSort).all
      (RuleSchema.isValidIn (definition relySort resultSort)) = true := by
  have valid := definition_valid relySort resultSort
  unfold CalculusLanguageDef.isValid at valid
  simp only [Bool.and_eq_true] at valid
  simpa [definition, profileExtension, signature, profiledRules] using valid.1.2

/-- The two local endpoints share their entire signature. -/
theorem endpoint_signatures_equal : signature = signature := rfl

/-- Their generated rule families are observably different. -/
theorem endpoint_rules_distinct :
    profiledRules .star .star ≠ profiledRules .box .box := by
  decide

/-- Hence the complete flat calculus retains the local endpoint choice. -/
theorem endpoint_definitions_distinct :
    definition .star .star ≠ definition .box .box := by
  intro equality
  exact endpoint_rules_distinct
    (congrArg CalculusLanguageDef.rules equality)

/-- Introduction really contains a reduction assumption; erasing it changes
the authored hypothetical premise and therefore its lowered schema. -/
theorem introduction_operational_premise_nonempty
    (relySort resultSort : CarrierUniverseSignature.Code) :
    ((introductionRule relySort resultSort).premises.get
      ⟨2, by simp [introductionRule]⟩).relationContext ≠
      delta := by
  simp [introductionRule, delta]

/-- Elimination discharges a strictly richer relation context than its
conclusion retains. -/
theorem elimination_discharges_operational_evidence
    (relySort resultSort : CarrierUniverseSignature.Code) :
    ((eliminationRule relySort resultSort).premises.get
      ⟨2, by simp [eliminationRule]⟩).relationContext ≠
      (eliminationRule relySort resultSort).conclusion.relationContext := by
  simp [eliminationRule, ContextSchema.prepend, delta, gamma,
    variableClaim, typingClaim, reductionClaim, modalType, resultAt,
    contextPlug, variableClaimTerm, typingClaimTerm, reductionClaimTerm,
    modalTerm, contextPlugTerm]

/-- The admitted flat record denotes one combined GSLT. -/
def theory (relySort resultSort : CarrierUniverseSignature.Code) :
    Mettapedia.GSLT.GSLT :=
  (definition relySort resultSort).toGSLTOfEquationFree
    (definition_valid relySort resultSort) rfl

theorem theory_term (relySort resultSort : CarrierUniverseSignature.Code) :
    (theory relySort resultSort).Term = (Pattern ⊕ List Pattern) :=
  rfl

#print axioms definition_valid
#print axioms generated_rules_valid
#print axioms endpoint_rules_distinct
#print axioms endpoint_definitions_distinct
#print axioms introduction_operational_premise_nonempty
#print axioms elimination_discharges_operational_evidence
#print axioms theory_term

end Mettapedia.OSLF.Framework.SingleRelyContextualModalInference
