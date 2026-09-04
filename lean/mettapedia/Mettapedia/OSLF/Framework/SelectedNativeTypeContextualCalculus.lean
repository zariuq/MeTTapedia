import Mettapedia.OSLF.Framework.ContextualCarrierClaims
import Mettapedia.OSLF.Framework.ContextualFamilyApplication
import Mettapedia.OSLF.Framework.ContextualModalSignatureCompiler
import Mettapedia.OSLF.Framework.SelectedNativeTypeDemand

/-!
# Profile-sensitive contextual native-type calculus

The selected native-type input retains an authored list of displayed rewrite
occurrences.  Each occurrence carries both its fixed-context telescope and one
local star/box profile.  This module makes that retained information affect the
generated calculus.

For every selected occurrence it emits first-order constructors for applying
the dependent result family, filling the displayed one-hole context, and
applying an arbitrary predicate.  It then emits formation, introduction, and
elimination rules whose universe codes are read from the occurrence's exact
profile.  The authoring view uses explicit ordered contexts and lowers through
`ContextualInference.lowerRule` to ordinary `RuleSchema` rows.

The output is one flat `CalculusLanguageDef`.  Carrier generation, modal
signature generation, contextual claims, and profile rules remain visible as
lawful construction factors, but they are not separate runtime objects.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.SelectedNativeTypeContextualCalculus

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.ContextualInference
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.OSLF.Framework

/-! ## Stable occurrence-local names -/

inductive AuxiliaryKind
  | familyApplication
  | contextPlug
  | predicateApplication
deriving Repr, DecidableEq

def AuxiliaryKind.tag : AuxiliaryKind → Char
  | .familyApplication => 'f'
  | .contextPlug => 'c'
  | .predicateApplication => 'p'

def auxiliaryLabel (kind : AuxiliaryKind) (slot : Nat) : String :=
  String.ofList
    ("$oslf:contextual:".toList ++ kind.tag :: ':' ::
      List.replicate slot 's')

/-- Decode exactly the occurrence-local support-constructor namespace. -/
def decodeAuxiliaryLabel? (name : String) : Option (AuxiliaryKind × Nat) :=
  match name.toList with
  | '$' :: 'o' :: 's' :: 'l' :: 'f' :: ':' ::
      'c' :: 'o' :: 'n' :: 't' :: 'e' :: 'x' :: 't' :: 'u' :: 'a' :: 'l' ::
      ':' :: 'f' :: ':' :: suffix =>
      if suffix = List.replicate suffix.length 's'
      then some (.familyApplication, suffix.length)
      else none
  | '$' :: 'o' :: 's' :: 'l' :: 'f' :: ':' ::
      'c' :: 'o' :: 'n' :: 't' :: 'e' :: 'x' :: 't' :: 'u' :: 'a' :: 'l' ::
      ':' :: 'c' :: ':' :: suffix =>
      if suffix = List.replicate suffix.length 's'
      then some (.contextPlug, suffix.length)
      else none
  | '$' :: 'o' :: 's' :: 'l' :: 'f' :: ':' ::
      'c' :: 'o' :: 'n' :: 't' :: 'e' :: 'x' :: 't' :: 'u' :: 'a' :: 'l' ::
      ':' :: 'p' :: ':' :: suffix =>
      if suffix = List.replicate suffix.length 's'
      then some (.predicateApplication, suffix.length)
      else none
  | _ => none

@[simp]
theorem decodeAuxiliaryLabel?_auxiliaryLabel
    (kind : AuxiliaryKind) (slot : Nat) :
    decodeAuxiliaryLabel? (auxiliaryLabel kind slot) = some (kind, slot) := by
  cases kind <;>
    simp [decodeAuxiliaryLabel?, auxiliaryLabel, AuxiliaryKind.tag]

/-- Successful auxiliary decoding reconstructs the exact private label. -/
theorem auxiliaryLabel_of_decodeAuxiliaryLabel?_eq_some
    {name : String} {kind : AuxiliaryKind} {slot : Nat}
    (decoded : decodeAuxiliaryLabel? name = some (kind, slot)) :
    auxiliaryLabel kind slot = name := by
  unfold decodeAuxiliaryLabel? at decoded
  split at decoded
  next suffix equation =>
    split at decoded
    next canonical =>
      cases decoded
      rw [← String.ofList_toList (s := name), equation]
      unfold auxiliaryLabel
      rw [canonical]
      simp only [List.length_replicate]
      congr 1
    next notCanonical => simp at decoded
  next suffix equation =>
    split at decoded
    next canonical =>
      cases decoded
      rw [← String.ofList_toList (s := name), equation]
      unfold auxiliaryLabel
      rw [canonical]
      simp only [List.length_replicate]
      congr 1
    next notCanonical => simp at decoded
  next suffix equation =>
    split at decoded
    next canonical =>
      cases decoded
      rw [← String.ofList_toList (s := name), equation]
      unfold auxiliaryLabel
      rw [canonical]
      simp only [List.length_replicate]
      congr 1
    next notCanonical => simp at decoded
  next => simp at decoded

theorem auxiliaryLabel_injective (kind : AuxiliaryKind) :
    Function.Injective (auxiliaryLabel kind) := by
  intro first second equality
  have lengths := congrArg String.length equality
  simp [auxiliaryLabel, AuxiliaryKind.tag] at lengths
  omega

theorem auxiliaryLabel_ne_of_kind_ne
    {first second : AuxiliaryKind} (different : first ≠ second)
    (firstSlot secondSlot : Nat) :
    auxiliaryLabel first firstSlot ≠ auxiliaryLabel second secondSlot := by
  intro equality
  have lists := congrArg String.toList equality
  cases first <;> cases second <;>
    simp [auxiliaryLabel, AuxiliaryKind.tag] at lists different

inductive RuleKind
  | formation
  | introduction
  | elimination
deriving Repr, DecidableEq

def RuleKind.tag : RuleKind → Char
  | .formation => 'f'
  | .introduction => 'i'
  | .elimination => 'e'

def ruleName (kind : RuleKind) (slot : Nat) : String :=
  String.ofList
    ("$oslf:contextual-rule:".toList ++ kind.tag :: ':' ::
      List.replicate slot 's')

def indexedMetavariable (stem : String) (index : Nat) : String :=
  String.ofList (stem.toList ++ ':' :: List.replicate index 's')

def relyTypeName (index : Nat) : String :=
  indexedMetavariable "$oslf:rely-type" index

def relyValueName (index : Nat) : String :=
  indexedMetavariable "$oslf:rely-value" index

/-! ## One profiled occurrence -/

abbrev Occurrence {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) :=
  Fin demand.occurrences.length

def occurrenceAt {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand) :
    ProfiledRewriteOccurrence source :=
  demand.occurrences.get slot

def typingAt {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand) :
    DisplayedRewriteTyping source :=
  (occurrenceAt demand slot).typing

def bindingsAt {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand) :
    List (String × TypeExpr) :=
  DisplayedContextProfile.bindings (typingAt demand slot)

def resolve {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) : TypeExpr → String :=
  ContextualModalExtension.compiledCarrierName demand.foundation

def carrierAt {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) (object : TypeExpr) : String :=
  resolve demand object

def relyTypes {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand) :
    List Pattern :=
  List.ofFn fun index : Fin (bindingsAt demand slot).length =>
    .fvar (relyTypeName index.val)

def relyValues {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand) :
    List Pattern :=
  List.ofFn fun index : Fin (bindingsAt demand slot).length =>
    .fvar (relyValueName index.val)

def sortCode (carrier : String) (code : CarrierUniverseSignature.Code) :
    Pattern :=
  .apply (CarrierUniverseSignature.label code carrier) []

def modalType {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand)
    (resultFamily : Pattern) : Pattern :=
  .apply (SelectedModalNaming.label slot.val)
    (relyTypes demand slot ++ [resultFamily])

def familyApplication {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand)
    (resultFamily : Pattern) : Pattern :=
  ContextualFamilyApplication.applyFamily
    (auxiliaryLabel .familyApplication slot.val)
    resultFamily (relyValues demand slot)

def contextPlug {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand)
    (focus : Pattern) : Pattern :=
  .apply (auxiliaryLabel .contextPlug slot.val)
    (relyValues demand slot ++ [focus])

def predicateApplication {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand)
    (predicate focus : Pattern) : Pattern :=
  .apply (auxiliaryLabel .predicateApplication slot.val) [predicate, focus]

/-! ## First-order support constructors -/

def familyApplicationTerm {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand) :
    GrammarRule where
  label := auxiliaryLabel .familyApplication slot.val
  category := carrierAt demand (typingAt demand slot).rewriteType
  params :=
    .simple "result-family"
        (ContextualModalSignature.resultFamilyType
          (resolve demand) (typingAt demand slot)) ::
      (bindingsAt demand slot).map fun binding =>
        .simple ("rely:" ++ binding.1)
          (.base (carrierAt demand binding.2))
  syntaxPattern := []

def contextPlugTerm {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand) :
    GrammarRule where
  label := auxiliaryLabel .contextPlug slot.val
  category := carrierAt demand (typingAt demand slot).rewriteType
  params :=
    (bindingsAt demand slot).map (fun binding =>
      .simple ("rely:" ++ binding.1) (.base (carrierAt demand binding.2))) ++
    [.simple "focus" (.base (carrierAt demand (typingAt demand slot).focusType))]
  syntaxPattern := []

def predicateApplicationTerm {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand) :
    GrammarRule where
  label := auxiliaryLabel .predicateApplication slot.val
  category := formulaType.name
  params :=
    [ .simple "predicate"
        (.arrow (.base (carrierAt demand (typingAt demand slot).focusType))
          (.base formulaType.name))
    , .simple "focus"
        (.base (carrierAt demand (typingAt demand slot).focusType)) ]
  syntaxPattern := []

def supportTermsAt {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand) :
    List GrammarRule :=
  [familyApplicationTerm demand slot, contextPlugTerm demand slot,
    predicateApplicationTerm demand slot]

def supportTerms {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) : List GrammarRule :=
  (List.ofFn fun slot : Occurrence demand => supportTermsAt demand slot).flatten

/-! ## Context rows derived from the exact rely telescope -/

private def gamma : ContextSchema := .hole "Gamma"
private def delta : ContextSchema := .hole "Delta"

def relyVariableClaims {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand) :
    List Pattern :=
  List.ofFn fun index : Fin (bindingsAt demand slot).length =>
    let binding := (bindingsAt demand slot).get index
    ContextualCarrierClaims.variableClaim (carrierAt demand binding.2)
      (.fvar (relyValueName index.val))

def relyTypingClaims {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand) :
    List Pattern :=
  List.ofFn fun index : Fin (bindingsAt demand slot).length =>
    let binding := (bindingsAt demand slot).get index
    ContextualCarrierClaims.typingClaim (carrierAt demand binding.2)
      (.fvar (relyValueName index.val)) (.fvar (relyTypeName index.val))

def relySortPremises {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand) :
    List Sequent :=
  List.ofFn fun index : Fin (bindingsAt demand slot).length =>
    let binding := (bindingsAt demand slot).get index
    let carrier := carrierAt demand binding.2
    { variableContext := gamma
      relationContext := delta
      conclusion := ContextualCarrierClaims.typingClaim carrier
        (.fvar (relyTypeName index.val))
        (sortCode carrier
          ((occurrenceAt demand slot).profile
            (ContextualModalProfile.relySlot (typingAt demand slot) index))) }

def resultSortPremise {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand) :
    Sequent :=
  let carrier := carrierAt demand (typingAt demand slot).rewriteType
  { variableContext := ContextSchema.prepend (relyVariableClaims demand slot) gamma
    relationContext := ContextSchema.prepend (relyTypingClaims demand slot) delta
    conclusion := ContextualCarrierClaims.typingClaim carrier
      (familyApplication demand slot (.fvar "result-family"))
      (sortCode carrier (ContextualModalProfile.resultCode
        (occurrenceAt demand slot).profile)) }

def relyMetavariables {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand) :
    List (String × Nat) :=
  (List.ofFn fun index : Fin (bindingsAt demand slot).length =>
    [(relyTypeName index.val, 0), (relyValueName index.val, 0)]).flatten

/-! ## Profile-sensitive contextual rules -/

def formationRule {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand) :
    ContextualInference.Rule where
  id := ⟨ruleName .formation slot.val⟩
  metavariables :=
    [("Gamma", 0), ("Delta", 0), ("result-family", 0)] ++
      relyMetavariables demand slot
  premises := relySortPremises demand slot ++ [resultSortPremise demand slot]
  conclusion :=
    let carrier := carrierAt demand (typingAt demand slot).focusType
    { variableContext := gamma
      relationContext := delta
      conclusion := ContextualCarrierClaims.typingClaim carrier
        (modalType demand slot (.fvar "result-family"))
        (sortCode carrier (ContextualModalProfile.resultCode
          (occurrenceAt demand slot).profile)) }

def introductionRule {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand) :
    ContextualInference.Rule where
  id := ⟨ruleName .introduction slot.val⟩
  metavariables :=
    [("Gamma", 0), ("Delta", 0), ("result-family", 0),
      ("focus", 0), ("reduct", 0)] ++ relyMetavariables demand slot
  premises := relySortPremises demand slot ++ [resultSortPremise demand slot,
    { variableContext := ContextSchema.prepend
        (ContextualCarrierClaims.variableClaim
          (carrierAt demand (typingAt demand slot).focusType)
          (.fvar "focus") :: relyVariableClaims demand slot) gamma
      relationContext := ContextSchema.prepend
        (ContextualCarrierClaims.reductionClaim
          (carrierAt demand (typingAt demand slot).rewriteType)
          (contextPlug demand slot (.fvar "focus")) (.fvar "reduct") ::
            relyTypingClaims demand slot) delta
      conclusion := ContextualCarrierClaims.typingClaim
        (carrierAt demand (typingAt demand slot).rewriteType)
        (.fvar "reduct")
        (familyApplication demand slot (.fvar "result-family")) }]
  conclusion :=
    { variableContext := gamma
      relationContext := delta
      conclusion := ContextualCarrierClaims.typingClaim
        (carrierAt demand (typingAt demand slot).focusType)
        (.fvar "focus") (modalType demand slot (.fvar "result-family")) }

def eliminationRule {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand) :
    ContextualInference.Rule where
  id := ⟨ruleName .elimination slot.val⟩
  metavariables :=
    [("Gamma", 0), ("Delta", 0), ("result-family", 0),
      ("predicate", 0), ("generic-focus", 0), ("reduct", 0),
      ("member", 0)] ++ relyMetavariables demand slot
  premises := relySortPremises demand slot ++ [resultSortPremise demand slot,
    { variableContext := ContextSchema.prepend
        (ContextualCarrierClaims.variableClaim
          (carrierAt demand (typingAt demand slot).focusType)
          (.fvar "generic-focus") :: relyVariableClaims demand slot) gamma
      relationContext := ContextSchema.prepend
        (ContextualCarrierClaims.typingClaim
          (carrierAt demand (typingAt demand slot).rewriteType)
          (.fvar "reduct")
          (familyApplication demand slot (.fvar "result-family")) ::
        ContextualCarrierClaims.reductionClaim
          (carrierAt demand (typingAt demand slot).rewriteType)
          (contextPlug demand slot (.fvar "generic-focus")) (.fvar "reduct") ::
        relyTypingClaims demand slot) delta
      conclusion := predicateApplication demand slot
        (.fvar "predicate") (.fvar "generic-focus") }]
  conclusion :=
    { variableContext := ContextSchema.prepend
        [ContextualCarrierClaims.variableClaim
          (carrierAt demand (typingAt demand slot).focusType) (.fvar "member")] gamma
      relationContext := ContextSchema.prepend
        [ContextualCarrierClaims.typingClaim
          (carrierAt demand (typingAt demand slot).focusType) (.fvar "member")
          (modalType demand slot (.fvar "result-family"))] delta
      conclusion := predicateApplication demand slot
        (.fvar "predicate") (.fvar "member") }

def rulesAt {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand) :
    List RuleSchema :=
  [lowerRule (formationRule demand slot),
    lowerRule (introductionRule demand slot),
    lowerRule (eliminationRule demand slot)]

def profiledRules {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) : List RuleSchema :=
  (List.ofFn fun slot : Occurrence demand => rulesAt demand slot).flatten

/-! ## One flat generated calculus -/

def signature {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) : CalculusLanguageDef :=
  ContextualCarrierClaims.apply
    (ContextualModalSignatureCompiler.definition demand.foundation)
    (SelectedNativeTypeFoundation.stableCarrierNames demand.foundation)

def profileExtension {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) : CalculusLanguageExtension where
  newTerms := supportTerms demand
  newRules := profiledRules demand

def definition {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) : CalculusLanguageDef :=
  (profileExtension demand).apply (signature demand)

/-- Batch-order reference with the same generated rows.  The public
definition retains chronological constructor order; this grouped object is
used only to state and prove order-insensitive structural properties. -/
def groupedDefinition {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) : CalculusLanguageDef :=
  (profileExtension demand).apply
    (ContextualCarrierClaims.apply
      (ContextualModalExtension.language demand.foundation)
      (SelectedNativeTypeFoundation.stableCarrierNames demand.foundation))

theorem definition_constructorPermutation_grouped
    {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) :
    ConstructorPermutation (definition demand) (groupedDefinition demand) := by
  have signaturePermutation :=
    (ContextualModalSignatureCompiler.definition_constructorPermutation_grouped
      demand.foundation).apply_extension
        (ContextualCarrierClaims.extension
          (SelectedNativeTypeFoundation.stableCarrierNames demand.foundation))
  exact signaturePermutation.apply_extension (profileExtension demand)

/-- With no compiled prefix, the chronological singleton step already has
the grouped row order: no earlier modal declaration exists for a newly
allocated carrier row to cross. -/
theorem singletonCompiler_eq_grouped {source : ValidatedLanguageDef}
    (occurrence : GroundedRewriteOccurrence source) :
    ContextualModalSignatureCompiler.definition
        (ContextualModalSignatureCompiler.singleton occurrence) =
      ContextualModalExtension.language
        (ContextualModalSignatureCompiler.singleton occurrence) := by
  let empty := SelectedNativeTypeFoundation.Demand.empty source
  let singleton := ContextualModalSignatureCompiler.singleton occurrence
  calc
    ContextualModalSignatureCompiler.definition singleton =
        (ContextualModalSignatureCompiler.continuationExtension empty singleton).apply
          (ContextualModalSignatureCompiler.definition empty) := by
            have compiled :=
              ContextualModalSignatureCompiler.definition_append empty singleton
            rw [SelectedNativeTypeFoundation.Demand.empty_append] at compiled
            exact compiled
    _ = (ContextualModalSignatureCompiler.stepExtension empty occurrence).apply
          (ContextualModalSignatureCompiler.base source) := by
            rw [ContextualModalSignatureCompiler.continuationExtension_singleton,
              ContextualModalSignatureCompiler.definition_empty]
    _ = (ConstructorTermExtension.ofList
          [ContextualModalSignatureCompiler.modalTerm empty occurrence]).apply
          (SelectedNativeTypeFoundation.definition singleton) := by
            rw [ContextualModalSignatureCompiler.stepExtension,
              CalculusLanguageExtension.comp_apply]
            change
              (ConstructorTermExtension.ofList
                [ContextualModalSignatureCompiler.modalTerm empty occurrence]).apply
                ((SelectedNativeTypeFoundation.appendExtension empty singleton).apply
                  (SelectedNativeTypeFoundation.definition empty)) = _
            rw [← SelectedNativeTypeFoundation.definition_append empty singleton]
            rw [SelectedNativeTypeFoundation.Demand.empty_append]
    _ = ContextualModalExtension.language singleton := by
          unfold ContextualModalExtension.language ContextualModalExtension.extension
          congr 1

@[simp] theorem definition_rules {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) :
    (definition demand).rules =
      (signature demand).rules ++ profiledRules demand :=
  rfl

@[simp] theorem foundation_types {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeFoundation.Demand source) :
    (SelectedNativeTypeFoundation.definition demand).types =
      SelectedNativeTypeFoundation.stableCarrierTypes demand :=
  rfl

@[simp] theorem foundation_terms {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeFoundation.Demand source) :
    (SelectedNativeTypeFoundation.definition demand).terms =
      CarrierUniverseSignature.termsFor
        (SelectedNativeTypeFoundation.stableCarrierNames demand) :=
  rfl

@[simp] theorem foundation_equations {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeFoundation.Demand source) :
    (SelectedNativeTypeFoundation.definition demand).equations = [] :=
  rfl

@[simp] theorem foundation_rewrites {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeFoundation.Demand source) :
    (SelectedNativeTypeFoundation.definition demand).rewrites = [] :=
  rfl

/-- Every constructor in the generated carrier foundation omits concrete
syntax.  This structural row theorem lets later generators reuse validation
evidence without reducing the whole foundation at once. -/
theorem foundation_term_syntax_nil {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeFoundation.Demand source)
    {term : GrammarRule}
    (membership : term ∈ (SelectedNativeTypeFoundation.definition demand).terms) :
    term.syntaxPattern = [] := by
  change term ∈ CarrierUniverseSignature.termsFor
    (SelectedNativeTypeFoundation.stableCarrierNames demand) at membership
  simp [CarrierUniverseSignature.termsFor, CarrierUniverseSignature.rule]
    at membership
  rcases membership with ⟨carrier, _membership, star | box⟩
  · subst term
    rfl
  · subst term
    rfl

theorem universe_term_syntax_nil (carrierNames : List String)
    {term : GrammarRule}
    (membership : term ∈ CarrierUniverseSignature.termsFor carrierNames) :
    term.syntaxPattern = [] := by
  simp [CarrierUniverseSignature.termsFor, CarrierUniverseSignature.rule]
    at membership
  rcases membership with ⟨carrier, _membership, star | box⟩
  · subst term
    rfl
  · subst term
    rfl

theorem modal_term_syntax_nil {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeFoundation.Demand source)
    {term : GrammarRule}
    (membership : term ∈ ContextualModalExtension.modalTerms demand) :
    term.syntaxPattern = [] := by
  change term ∈ List.ofFn (ContextualModalExtension.modalRuleAt demand)
    at membership
  obtain ⟨slot, rfl⟩ := List.mem_ofFn.mp membership
  rfl

theorem contextual_claim_term_syntax_nil (carrierNames : List String)
    {term : GrammarRule}
    (membership : term ∈
      [emptyContextTerm, extendContextTerm] ++
        ContextualInferenceCanonicalContext.extension.newTerms ++
          ContextualCarrierClaims.claimTermsFor carrierNames) :
    term.syntaxPattern = [] := by
  simp only [List.mem_append] at membership
  rcases membership with (shared | canonical) | claim
  · simp at shared
    rcases shared with empty | extended
    · subst term
      rfl
    · subst term
      rfl
  · simp [ContextualInferenceCanonicalContext.extension,
      ContextualInferenceCanonicalContext.contextCodeTerm] at canonical
    subst term
    rfl
  · unfold ContextualCarrierClaims.claimTermsFor at claim
    obtain ⟨carrier, _carrierMembership, rowMembership⟩ :=
      List.mem_flatMap.mp claim
    simp [ContextualCarrierClaims.claimTerms] at rowMembership
    rcases rowMembership with variableRow | typingRow | reductionRow
    · subst term
      rfl
    · subst term
      rfl
    · subst term
      rfl

theorem support_term_syntax_nil {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) {term : GrammarRule}
    (membership : term ∈ supportTerms demand) :
    term.syntaxPattern = [] := by
  unfold supportTerms at membership
  obtain ⟨rows, rowsMembership, termMembership⟩ :=
    List.mem_flatten.mp membership
  obtain ⟨slot, rfl⟩ := List.mem_ofFn.mp rowsMembership
  simp [supportTermsAt] at termMembership
  rcases termMembership with family | context | predicate
  · subst term
    rfl
  · subst term
    rfl
  · subst term
    rfl

/-! ## A nonempty contextual witness -/

namespace Canary

open ContextualModalSignature.Canary

theorem middleGrounded :
    SelectedNativeTypeFoundation.CarrierGrounded middleTyping := by
  intro object objectMembership name nameMembership
  simp [SelectedNativeTypeFoundation.requiredCarrierRoots,
    DisplayedContextProfile.carrierTypes,
    middle_occurrence_dependencies_exact] at objectMembership
  have objectEq : object = .base termType.name := by
    rcases objectMembership with rewrite | focus | bound | dependency
    · simpa [middleTyping] using rewrite
    · simpa [middleTyping] using focus
    · simp [middleTyping] at bound
    · exact dependency
  subst object
  have nameEq : name = termType.name := by
    simpa [TypeExpr.baseNames] using nameMembership
  subst name
  simp [source, sourceLanguage, termType, LanguageDef.typeNames,
    TypeDecl.plain]

def middleOccurrence (code : CarrierUniverseSignature.Code) :
    ProfiledRewriteOccurrence source :=
  ProfiledRewriteOccurrence.constant middleTyping middleGrounded code

def middleDemand (code : CarrierUniverseSignature.Code) :
    SelectedNativeTypeDemand source where
  occurrences := [middleOccurrence code]

theorem middleDemand_nonempty (code : CarrierUniverseSignature.Code) :
    (middleDemand code).occurrences ≠ [] := by
  simp [middleDemand]

theorem middle_binding_count :
    (bindingsAt (middleDemand .star) ⟨0, by simp [middleDemand]⟩).length = 2 := by
  change (DisplayedContextProfile.bindings middleTyping).length = 2
  rw [middle_occurrence_dependencies_exact]
  rfl

theorem middle_slot_eq_zero (code : CarrierUniverseSignature.Code)
    (slot : Occurrence (middleDemand code)) :
    slot = ⟨0, by simp [middleDemand]⟩ := by
  apply Fin.ext
  have bound : slot.val < 1 := by
    simpa only [middleDemand, List.length_cons, List.length_nil] using slot.isLt
  show slot.val = 0
  omega

theorem middle_occurrenceAt (code : CarrierUniverseSignature.Code)
    (slot : Occurrence (middleDemand code)) :
    occurrenceAt (middleDemand code) slot = middleOccurrence code := by
  rw [middle_slot_eq_zero code slot]
  rfl

theorem middle_typingAt (code : CarrierUniverseSignature.Code)
    (slot : Occurrence (middleDemand code)) :
    typingAt (middleDemand code) slot = middleTyping := by
  rw [typingAt, middle_occurrenceAt]
  rfl

theorem middle_bindingsAt (code : CarrierUniverseSignature.Code)
    (slot : Occurrence (middleDemand code)) :
    bindingsAt (middleDemand code) slot =
      [("left", .base termType.name), ("right", .base termType.name)] := by
  rw [bindingsAt, middle_typingAt]
  exact middle_occurrence_dependencies_exact

theorem middle_support_term_count :
    (supportTerms (middleDemand .star)).length = 3 := by
  decide

theorem middle_profile_rule_count :
    (profiledRules (middleDemand .star)).length = 3 := by
  decide

theorem middle_definition_eq_grouped :
    definition (middleDemand .star) =
      groupedDefinition (middleDemand .star) := by
  have foundationEq :
      (middleDemand .star).foundation =
        ContextualModalSignatureCompiler.singleton
          (middleOccurrence .star).groundedOccurrence := by
    apply SelectedNativeTypeFoundation.Demand.ext
    rfl
  unfold definition groupedDefinition signature
  rw [foundationEq, singletonCompiler_eq_grouped]

theorem middle_carrier_objects :
    (middleDemand .star).foundation.carrierObjects.objects =
      [.base termType.name] := by
  unfold SelectedNativeTypeDemand.foundation
    SelectedNativeTypeFoundation.Demand.carrierObjects
    SelectedNativeTypeFoundation.Demand.carrierRoots
    SelectedNativeTypeFoundation.requiredCarrierRoots
    DisplayedContextProfile.carrierTypes
    CarrierObjectClosure.Request.objects CarrierObjectClosure.close
  simp only [middleDemand, middleOccurrence,
    ProfiledRewriteOccurrence.constant, List.map_singleton,
    List.flatMap_singleton]
  rw [middle_occurrence_dependencies_exact]
  simp [CarrierObjectClosure.constituents, middleTyping]
  decide

theorem middle_stableCarrierNames :
    SelectedNativeTypeFoundation.stableCarrierNames
        (middleDemand .star).foundation =
      [CarrierObjectLanguageDef.Naming.indexedNameAt 0] := by
  simp [SelectedNativeTypeFoundation.stableCarrierNames,
    SelectedNativeTypeFoundation.stableCarrierTypes,
    CarrierObjectLanguageDef.carrierTypes,
    CarrierObjectLanguageDef.Naming.indexed,
    CarrierObjectLanguageDef.Naming.indexedName,
    middle_carrier_objects, TypeDecl.plain]

theorem middle_stableCarrierTypes :
    SelectedNativeTypeFoundation.stableCarrierTypes
        (middleDemand .star).foundation =
      [TypeDecl.plain (CarrierObjectLanguageDef.Naming.indexedNameAt 0)] := by
  simp [SelectedNativeTypeFoundation.stableCarrierTypes,
    CarrierObjectLanguageDef.carrierTypes,
    CarrierObjectLanguageDef.Naming.indexed,
    CarrierObjectLanguageDef.Naming.indexedName,
    middle_carrier_objects]

theorem middle_compiledCarrierName :
    ContextualModalExtension.compiledCarrierName
        (middleDemand .star).foundation (.base termType.name) =
      CarrierObjectLanguageDef.Naming.indexedNameAt 0 := by
  simp [ContextualModalExtension.compiledCarrierName,
    CarrierObjectNameLookup.indexed?, CarrierObjectNameLookup.lookup?,
    CarrierObjectNameLookup.nameOf, CarrierObjectNameLookup.slotOf,
    CarrierObjectLanguageDef.Naming.indexed,
    CarrierObjectLanguageDef.Naming.indexedName,
    middle_carrier_objects]

private abbrev middleCarrierName : String :=
  CarrierObjectLanguageDef.Naming.indexedNameAt 0

theorem middle_grouped_types :
    (groupedDefinition (middleDemand .star)).types =
      [TypeDecl.plain middleCarrierName, formulaType, contextType] := by
  simp [groupedDefinition, profileExtension, middle_stableCarrierTypes,
    middleCarrierName]

theorem middle_grouped_terms :
    (groupedDefinition (middleDemand .star)).terms =
      ((CarrierUniverseSignature.termsFor [middleCarrierName] ++
          ContextualModalExtension.modalTerms (middleDemand .star).foundation) ++
        ([emptyContextTerm, extendContextTerm] ++
          ContextualInferenceCanonicalContext.extension.newTerms ++
            ContextualCarrierClaims.claimTermsFor [middleCarrierName])) ++
      supportTerms (middleDemand .star) := by
  simp [groupedDefinition, profileExtension, middle_stableCarrierNames,
    middleCarrierName]

/-- Exact constructor inventory of the nonempty two-rely witness.  Exposing
this row lets the contextual checker reduce constructor lookup one declaration
at a time rather than reevaluating the entire generator. -/
theorem middle_grouped_terms_explicit :
    (groupedDefinition (middleDemand .star)).terms =
      [ CarrierUniverseSignature.rule .star middleCarrierName
      , CarrierUniverseSignature.rule .box middleCarrierName
      , ContextualModalExtension.modalRuleAt
          (middleDemand .star).foundation ⟨0, by simp [middleDemand]⟩
      , emptyContextTerm
      , extendContextTerm
      , ContextualInferenceCanonicalContext.contextCodeTerm
      , ContextualCarrierClaims.variableClaimTerm middleCarrierName
      , ContextualCarrierClaims.typingClaimTerm middleCarrierName
      , ContextualCarrierClaims.reductionClaimTerm middleCarrierName
      , familyApplicationTerm
          (middleDemand .star) ⟨0, by simp [middleDemand]⟩
      , contextPlugTerm
          (middleDemand .star) ⟨0, by simp [middleDemand]⟩
      , predicateApplicationTerm
          (middleDemand .star) ⟨0, by simp [middleDemand]⟩ ] := by
  rw [middle_grouped_terms]
  simp [CarrierUniverseSignature.termsFor,
    ContextualModalExtension.modalTerms,
    ContextualInferenceCanonicalContext.extension,
    ContextualCarrierClaims.claimTermsFor,
    ContextualCarrierClaims.claimTerms,
    supportTerms, supportTermsAt,
    SelectedNativeTypeDemand.foundation, middleDemand, middleOccurrence,
    ProfiledRewriteOccurrence.constant]

@[simp] theorem middle_grouped_equations :
    (groupedDefinition (middleDemand .star)).equations = [] :=
  rfl

theorem middle_grouped_judgments :
    (groupedDefinition (middleDemand .star)).judgments =
      [CarrierTypingLanguageDef.judgment middleCarrierName,
        contextualJudgment] := by
  simp [groupedDefinition, profileExtension, middle_stableCarrierNames,
    middleCarrierName]

theorem middle_grouped_rules :
    (groupedDefinition (middleDemand .star)).rules =
      [ CarrierTypingLanguageDef.universeAxiom middleCarrierName
      , ContextualInferenceCanonicalContext.nilRule
      , ContextualInferenceCanonicalContext.consRule
      , ContextualCarrierClaims.liftTypingRule middleCarrierName
      , lowerRule
          (formationRule (middleDemand .star) ⟨0, by simp [middleDemand]⟩)
      , lowerRule
          (introductionRule (middleDemand .star) ⟨0, by simp [middleDemand]⟩)
      , lowerRule
          (eliminationRule (middleDemand .star) ⟨0, by simp [middleDemand]⟩) ] := by
  simp only [groupedDefinition, CalculusLanguageExtension.apply_rules,
    profileExtension, ContextualCarrierClaims.apply_rules,
    ContextualModalExtension.language_rules,
    SelectedNativeTypeFoundation.definition_rules]
  rw [middle_stableCarrierNames]
  simp [profiledRules, rulesAt, ContextualCarrierClaims.bridgeRules,
    ContextualInferenceCanonicalContext.extension,
    middleDemand, middleCarrierName]

theorem middle_grouped_conversion :
    (groupedDefinition (middleDemand .star)).conversion = none := by
  rfl

theorem middle_grouped_rules_locallyValid :
    (groupedDefinition (middleDemand .star)).rules.all
      RuleSchema.isLocallyValid = true := by
  rw [middle_grouped_rules]
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [CarrierTypingLanguageDef.universeAxiom_isValidV1,
    ContextualCarrierClaims.liftTypingRule_locallyValid]
  simp only [Bool.true_and]
  simp [formationRule, introductionRule, eliminationRule, relySortPremises,
    ContextualInferenceCanonicalContext.nilRule,
    ContextualInferenceCanonicalContext.consRule,
    ContextualInferenceCanonicalContext.premise,
    ContextualInferenceCanonicalContext.sequent,
    ContextualInferenceCanonicalContext.claim,
    ContextualInference.lowerSequent,
    ContextualInference.encodeContext,
    resultSortPremise, relyMetavariables, relyVariableClaims, relyTypingClaims,
    modalType, familyApplication, contextPlug, predicateApplication,
    relyTypes, relyValues, sortCode,
    carrierAt, resolve, auxiliaryLabel, AuxiliaryKind.tag, ruleName,
    RuleKind.tag, relyTypeName, relyValueName, indexedMetavariable,
    middle_typingAt, middle_bindingsAt, middleTyping,
    middle_compiledCarrierName, ContextualFamilyApplication.applyFamily,
    ContextualCarrierClaims.variableClaim,
    ContextualCarrierClaims.typingClaim,
    ContextualCarrierClaims.reductionClaim,
    ContextualCarrierClaims.claimLabel,
    ContextualCarrierClaims.ClaimKind.tag,
    ContextualInference.lowerRule, ContextualInference.lowerSequent,
    ContextualInference.encodeContext, ContextSchema.prepend, gamma, delta,
    CarrierUniverseSignature.label, CarrierUniverseSignature.Code.tag,
    CarrierObjectLanguageDef.Naming.indexedNameAt,
    RuleSchema.isLocallyValid, RuleSchema.metavariableNames,
    RuleSchema.occurrences, RuleSchema.patterns,
    patternMetavariableOccurrencesAt, patternsMetavariableOccurrencesAt,
    patternHasNoCollectionRest, patternsHaveNoCollectionRest,
    Pattern.isWellScoped, Pattern.isWellScopedAt,
    Pattern.isWellScopedListAt, Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList] ;
  decide

/-- The carrier-universe axiom resolves against the exact constructor and
judgment rows of the combined calculus. -/
theorem middle_universe_rule_validIn :
    RuleSchema.isValidIn (groupedDefinition (middleDemand .star))
      (CarrierTypingLanguageDef.universeAxiom middleCarrierName) = true := by
  unfold RuleSchema.isValidIn
  rw [CarrierTypingLanguageDef.universeAxiom_isValidV1]
  simp only [Bool.true_and, RuleSchema.patterns,
    CarrierTypingLanguageDef.universeAxiom, List.nil_append,
    List.all_cons, List.all_nil, Bool.and_true]
  simp [CalculusLanguageDef.judgmentSchemaValid,
    CalculusLanguageDef.lookupJudgment?, middle_grouped_judgments,
    middle_grouped_terms_explicit, fixedConstructorListsValid,
    fixedConstructorsValid, languageHasConstructorArity,
    CarrierTypingLanguageDef.judgment, CarrierTypingLanguageDef.typingHead,
    CarrierUniverseSignature.rule, CarrierUniverseSignature.label,
    CarrierUniverseSignature.Code.tag, ContextualModalExtension.modalRuleAt,
    ContextualModalExtension.typingAt, ContextualModalSignature.modalRule,
    ContextualModalSignature.parameters,
    ContextualModalSignature.parametersFor,
    ContextualModalSignature.relyParametersFor,
    ContextualModalSignature.relyBindings,
    ContextualModalSignature.resultFamilyType,
    ContextualModalSignature.resolvedCarrier,
    ContextualInference.emptyContextTerm,
    ContextualInference.extendContextTerm,
    ContextualCarrierClaims.variableClaimTerm,
    ContextualCarrierClaims.typingClaimTerm,
    ContextualCarrierClaims.reductionClaimTerm,
    ContextualCarrierClaims.claimLabel, ContextualCarrierClaims.ClaimKind.tag,
    familyApplicationTerm, contextPlugTerm, predicateApplicationTerm,
    carrierAt, resolve, auxiliaryLabel, AuxiliaryKind.tag,
    middle_typingAt, middle_bindingsAt, middleTyping,
    middle_compiledCarrierName, middleCarrierName,
    SelectedModalNaming.label]
  decide

/-- The carrier-to-contextual bridge resolves against the mixed judgment
signature and the exact claim-constructor rows. -/
theorem middle_bridge_rule_validIn :
    RuleSchema.isValidIn (groupedDefinition (middleDemand .star))
      (ContextualCarrierClaims.liftTypingRule middleCarrierName) = true := by
  unfold RuleSchema.isValidIn
  rw [ContextualCarrierClaims.liftTypingRule_locallyValid]
  simp only [Bool.true_and]
  rw [ContextualCarrierClaims.liftTypingRule_patterns]
  simp [CalculusLanguageDef.judgmentSchemaValid,
    CalculusLanguageDef.lookupJudgment?, middle_grouped_judgments,
    middle_grouped_terms_explicit, fixedConstructorListsValid,
    fixedConstructorsValid, languageHasConstructorArity,
    CarrierTypingLanguageDef.judgment, CarrierTypingLanguageDef.typingHead,
    CarrierUniverseSignature.rule, CarrierUniverseSignature.label,
    CarrierUniverseSignature.Code.tag, ContextualModalExtension.modalRuleAt,
    ContextualModalExtension.typingAt, ContextualModalSignature.modalRule,
    ContextualModalSignature.parameters,
    ContextualModalSignature.parametersFor,
    ContextualModalSignature.relyParametersFor,
    ContextualModalSignature.relyBindings,
    ContextualModalSignature.resultFamilyType,
    ContextualModalSignature.resolvedCarrier,
    ContextualInference.contextualJudgment,
    ContextualInference.emptyContextTerm,
    ContextualInference.extendContextTerm,
    ContextualInferenceCanonicalContext.contextCodeTerm,
    ContextualInferenceCanonicalContext.premise,
    ContextualInferenceCanonicalContext.sequent,
    ContextualInferenceCanonicalContext.claim,
    ContextualInference.lowerSequent,
    ContextualInference.encodeContext,
    ContextualCarrierClaims.variableClaimTerm,
    ContextualCarrierClaims.typingClaimTerm,
    ContextualCarrierClaims.reductionClaimTerm,
    ContextualCarrierClaims.typingClaim,
    ContextualCarrierClaims.claimLabel, ContextualCarrierClaims.ClaimKind.tag,
    familyApplicationTerm, contextPlugTerm, predicateApplicationTerm,
    carrierAt, resolve, auxiliaryLabel, AuxiliaryKind.tag,
    middle_typingAt, middle_bindingsAt, middleTyping,
    middle_compiledCarrierName, middleCarrierName,
    SelectedModalNaming.label]
  decide

private abbrev middleSlot : Occurrence (middleDemand .star) :=
  ⟨0, by simp [middleDemand]⟩

theorem middle_formation_rule_locallyValid :
    RuleSchema.isLocallyValid
      (lowerRule (formationRule (middleDemand .star) middleSlot)) = true := by
  exact (List.all_eq_true.mp middle_grouped_rules_locallyValid) _ (by
    rw [middle_grouped_rules]
    simp)

theorem middle_introduction_rule_locallyValid :
    RuleSchema.isLocallyValid
      (lowerRule (introductionRule (middleDemand .star) middleSlot)) = true := by
  exact (List.all_eq_true.mp middle_grouped_rules_locallyValid) _ (by
    rw [middle_grouped_rules]
    simp)

theorem middle_elimination_rule_locallyValid :
    RuleSchema.isLocallyValid
      (lowerRule (eliminationRule (middleDemand .star) middleSlot)) = true := by
  exact (List.all_eq_true.mp middle_grouped_rules_locallyValid) _ (by
    rw [middle_grouped_rules]
    simp)

theorem middle_grouped_language_validate :
    (groupedDefinition (middleDemand .star)).toLanguageDef.validate = [] := by
  have compiledNameExpanded :
      ContextualModalExtension.compiledCarrierName
          ({ occurrences :=
              [ProfiledRewriteOccurrence.constant middleTyping middleGrounded
                .star] } : SelectedNativeTypeDemand source).foundation
          (.base termType.name) =
        CarrierObjectLanguageDef.Naming.indexedNameAt 0 := by
    exact middle_compiledCarrierName
  have bindingsExpanded :
      DisplayedContextProfile.bindings middleTyping =
        [("left", .base termType.name), ("right", .base termType.name)] :=
    middle_occurrence_dependencies_exact
  apply LanguageDef.validate_eq_nil_of_constructorOnly
  all_goals
    simp only [groupedDefinition, profileExtension,
      ContextualCarrierClaims.apply, ContextualCarrierClaims.extension,
      ContextualCarrierClaims.contextExtension,
      ContextualCarrierClaims.carrierExtension,
      ContextualModalExtension.language, ContextualModalExtension.extension,
      CalculusLanguageExtension.comp, CalculusLanguageExtension.apply,
      ConstructorTermExtension.ofList,
      foundation_types, foundation_terms, foundation_equations,
      foundation_rewrites]
  all_goals
    try simp only [middle_stableCarrierNames, middle_stableCarrierTypes]
  case hsyntax =>
    intro term membership
    left
    simp only [List.mem_append] at membership
    rcases membership with ((foundation | modal) | contextual) | support
    · exact universe_term_syntax_nil _ foundation
    · exact modal_term_syntax_nil _ modal
    · apply contextual_claim_term_syntax_nil _
      simpa only [List.mem_append] using contextual
    · exact support_term_syntax_nil _ support
  case hparams =>
    intro term termMembership parameter parameterMembership typeName
      typeNameMembership
    simp [supportTerms, supportTermsAt, familyApplicationTerm,
      contextPlugTerm, predicateApplicationTerm, bindingsAt, typingAt,
      occurrenceAt, carrierAt, resolve, auxiliaryLabel, AuxiliaryKind.tag,
      middleDemand, middleOccurrence, ProfiledRewriteOccurrence.constant,
      middleTyping,
      ContextualCarrierClaims.claimTermsFor,
      ContextualCarrierClaims.claimTerms,
      ContextualCarrierClaims.variableClaimTerm,
      ContextualCarrierClaims.typingClaimTerm,
      ContextualCarrierClaims.reductionClaimTerm,
      ContextualInference.formulaType, ContextualInference.contextType,
      ContextualInference.emptyContextTerm,
      ContextualInference.extendContextTerm,
      ContextualInferenceCanonicalContext.extension,
      ContextualInferenceCanonicalContext.contextCodeTerm,
      ContextualModalExtension.modalTerms,
      ContextualModalExtension.modalRuleAt,
      ContextualModalExtension.typingAt,
      ContextualModalSignature.modalRule,
      ContextualModalSignature.parameters,
      ContextualModalSignature.relyBindings,
      ContextualModalSignature.resultFamilyType,
      ContextualModalSignature.resolvedCarrier,
      SelectedModalNaming.label,
      CarrierUniverseSignature.termsFor, CarrierUniverseSignature.rule,
      CarrierObjectLanguageDef.Naming.indexedNameAt,
      LanguageDef.typeNames, TypeDecl.plain,
      TermParam.typeExpr] at *
    rcases termMembership with star | box | modal | emptyContext |
      extendedContext | canonicalContext | variableClaimRow | typingClaimRow |
      reductionClaimRow | familyApplicationRow | contextPlugRow |
      predicateApplicationRow
    · subst term
      simp at parameterMembership
    · subst term
      simp at parameterMembership
    · subst term
      simp [bindingsExpanded, ContextualModalSignature.parametersFor,
        ContextualModalSignature.relyParametersFor,
        ContextualModalSignature.curryType] at parameterMembership
      rcases parameterMembership with rfl | rfl | rfl <;>
        simp [compiledNameExpanded, ContextualModalSignature.resolvedCarrier,
          TypeExpr.baseNames] at typeNameMembership ⊢ <;>
        aesop
    · subst term
      simp at parameterMembership
    · subst term
      simp at parameterMembership
      rcases parameterMembership with rfl | rfl <;>
        simp [TypeExpr.baseNames] at typeNameMembership ⊢ <;>
        aesop
    · subst term
      simp at parameterMembership
      subst parameter
      simp [TypeExpr.baseNames] at typeNameMembership
      exact Or.inr (Or.inr typeNameMembership)
    · subst term
      simp at parameterMembership
      subst parameter
      simp [TypeExpr.baseNames] at typeNameMembership ⊢ ;
        aesop
    · subst term
      simp at parameterMembership
      rcases parameterMembership with rfl | rfl <;>
        simp [TypeExpr.baseNames] at typeNameMembership ⊢ <;>
        aesop
    · subst term
      simp at parameterMembership
      rcases parameterMembership with rfl | rfl <;>
        simp [TypeExpr.baseNames] at typeNameMembership ⊢ <;>
        aesop
    · subst term
      simp [bindingsExpanded, ContextualModalSignature.curryType]
        at parameterMembership
      rcases parameterMembership with rfl | rfl | rfl <;>
        simp [compiledNameExpanded, TypeExpr.baseNames]
          at typeNameMembership ⊢ <;>
        aesop
    · subst term
      simp [bindingsExpanded] at parameterMembership
      rcases parameterMembership with rfl | rfl | rfl <;>
        simp [compiledNameExpanded, TypeExpr.baseNames]
          at typeNameMembership ⊢ <;>
        aesop
    · subst term
      simp at parameterMembership
      rcases parameterMembership with rfl | rfl <;>
        simp [compiledNameExpanded, TypeExpr.baseNames]
          at typeNameMembership ⊢ <;>
        aesop
  case hcategory =>
    intro term termMembership
    simp [supportTerms, supportTermsAt, familyApplicationTerm,
      contextPlugTerm, predicateApplicationTerm, bindingsAt, typingAt,
      occurrenceAt, carrierAt, resolve, middleDemand, middleOccurrence,
      ProfiledRewriteOccurrence.constant,
      ContextualCarrierClaims.claimTermsFor,
      ContextualCarrierClaims.claimTerms,
      ContextualCarrierClaims.variableClaimTerm,
      ContextualCarrierClaims.typingClaimTerm,
      ContextualCarrierClaims.reductionClaimTerm,
      ContextualInference.formulaType, ContextualInference.contextType,
      ContextualInference.emptyContextTerm,
      ContextualInference.extendContextTerm,
      ContextualInferenceCanonicalContext.extension,
      ContextualInferenceCanonicalContext.contextCodeTerm,
      ContextualModalExtension.modalTerms,
      ContextualModalExtension.modalRuleAt,
      ContextualModalExtension.typingAt,
      ContextualModalSignature.modalRule,
      CarrierUniverseSignature.termsFor, CarrierUniverseSignature.rule,
      LanguageDef.typeNames, TypeDecl.plain] at *
    rcases termMembership with star | box | modal | emptyContext |
      extendedContext | canonicalContext | variableClaimRow | typingClaimRow |
      reductionClaimRow | familyApplicationRow | contextPlugRow |
      predicateApplicationRow <;> subst term
    all_goals
      simp [middleTyping]
    all_goals aesop
  all_goals
    try simp only [ContextualModalExtension.modalTerms]
  all_goals
    simp [
      supportTerms, supportTermsAt, familyApplicationTerm, contextPlugTerm,
      predicateApplicationTerm, bindingsAt, typingAt, occurrenceAt, carrierAt,
      resolve, auxiliaryLabel, AuxiliaryKind.tag,
      middleDemand, middleOccurrence, ProfiledRewriteOccurrence.constant,
      middleTyping,
      ContextualCarrierClaims.claimTermsFor,
      ContextualCarrierClaims.claimTerms,
      ContextualCarrierClaims.variableClaimTerm,
      ContextualCarrierClaims.typingClaimTerm,
      ContextualCarrierClaims.reductionClaimTerm,
      ContextualCarrierClaims.claimLabel,
      ContextualCarrierClaims.ClaimKind.tag,
      ContextualInference.formulaType, ContextualInference.contextType,
      ContextualInference.emptyContextTerm,
      ContextualInference.extendContextTerm,
      ContextualInferenceCanonicalContext.extension,
      ContextualInferenceCanonicalContext.contextCodeTerm,
      ContextualInferenceCanonicalContext.nilRule,
      ContextualInferenceCanonicalContext.consRule,
      ContextualInferenceCanonicalContext.premise,
      ContextualInferenceCanonicalContext.sequent,
      ContextualInferenceCanonicalContext.claim,
      ContextualModalSignature.relyBindings,
      ContextualModalSignature.resultFamilyType,
      ContextualModalSignature.resolvedCarrier,
      CarrierUniverseSignature.termsFor, CarrierUniverseSignature.rule,
      CarrierUniverseSignature.label, CarrierUniverseSignature.Code.tag,
      CarrierObjectLanguageDef.Naming.indexedNameAt,
      LanguageDef.typeNames, TypeDecl.plain] <;>
    decide

/-- Any constructor in the validated concrete inventory is resolved at its
authored arity by the contextual checker. -/
theorem middle_constructor_has_arity (term : GrammarRule)
    (membership : term ∈ (groupedDefinition (middleDemand .star)).terms) :
    languageHasConstructorArity
      (groupedDefinition (middleDemand .star)).toLanguageDef
      term.label term.params.length = true := by
  unfold languageHasConstructorArity
  rw [LanguageDef.filter_terms_by_label_eq_singleton _ term
    (LanguageDef.constructorLabels_nodup_of_validate_eq_nil _
      middle_grouped_language_validate) membership]
  simp

theorem middle_star_has_arity :
    languageHasConstructorArity
      (groupedDefinition (middleDemand .star)).toLanguageDef
      (CarrierUniverseSignature.label .star middleCarrierName) 0 = true := by
  simpa [CarrierUniverseSignature.rule] using
    middle_constructor_has_arity
      (CarrierUniverseSignature.rule .star middleCarrierName) (by
        rw [middle_grouped_terms_explicit]
        simp)

theorem middle_box_has_arity :
    languageHasConstructorArity
      (groupedDefinition (middleDemand .star)).toLanguageDef
      (CarrierUniverseSignature.label .box middleCarrierName) 0 = true := by
  simpa [CarrierUniverseSignature.rule] using
    middle_constructor_has_arity
      (CarrierUniverseSignature.rule .box middleCarrierName) (by
        rw [middle_grouped_terms_explicit]
        simp)

theorem middle_emptyContext_has_arity :
    languageHasConstructorArity
      (groupedDefinition (middleDemand .star)).toLanguageDef
      emptyContextTerm.label 0 = true := by
  simpa [emptyContextTerm] using
    middle_constructor_has_arity emptyContextTerm (by
      rw [middle_grouped_terms_explicit]
      simp)

theorem middle_extendContext_has_arity :
    languageHasConstructorArity
      (groupedDefinition (middleDemand .star)).toLanguageDef
      extendContextTerm.label 2 = true := by
  simpa [extendContextTerm] using
    middle_constructor_has_arity extendContextTerm (by
      rw [middle_grouped_terms_explicit]
      simp)

theorem middle_contextCode_has_arity :
    languageHasConstructorArity
      (groupedDefinition (middleDemand .star)).toLanguageDef
      ContextualInferenceCanonicalContext.contextCodeTerm.label 1 = true := by
  simpa [ContextualInferenceCanonicalContext.contextCodeTerm] using
    middle_constructor_has_arity
      ContextualInferenceCanonicalContext.contextCodeTerm (by
        rw [middle_grouped_terms_explicit]
        simp)

theorem middle_variableClaim_has_arity :
    languageHasConstructorArity
      (groupedDefinition (middleDemand .star)).toLanguageDef
      (ContextualCarrierClaims.claimLabel .variable middleCarrierName) 1 = true := by
  simpa [ContextualCarrierClaims.variableClaimTerm] using
    middle_constructor_has_arity
      (ContextualCarrierClaims.variableClaimTerm middleCarrierName) (by
        rw [middle_grouped_terms_explicit]
        simp)

theorem middle_typingClaim_has_arity :
    languageHasConstructorArity
      (groupedDefinition (middleDemand .star)).toLanguageDef
      (ContextualCarrierClaims.claimLabel .typing middleCarrierName) 2 = true := by
  simpa [ContextualCarrierClaims.typingClaimTerm] using
    middle_constructor_has_arity
      (ContextualCarrierClaims.typingClaimTerm middleCarrierName) (by
        rw [middle_grouped_terms_explicit]
        simp)

theorem middle_reductionClaim_has_arity :
    languageHasConstructorArity
      (groupedDefinition (middleDemand .star)).toLanguageDef
      (ContextualCarrierClaims.claimLabel .reduction middleCarrierName) 2 = true := by
  simpa [ContextualCarrierClaims.reductionClaimTerm] using
    middle_constructor_has_arity
      (ContextualCarrierClaims.reductionClaimTerm middleCarrierName) (by
        rw [middle_grouped_terms_explicit]
        simp)

theorem middle_familyApplication_has_arity :
    languageHasConstructorArity
      (groupedDefinition (middleDemand .star)).toLanguageDef
      (auxiliaryLabel .familyApplication 0) 3 = true := by
  simpa [familyApplicationTerm, middleSlot, middle_typingAt,
    middle_bindingsAt] using
    middle_constructor_has_arity
      (familyApplicationTerm (middleDemand .star) middleSlot) (by
        rw [middle_grouped_terms_explicit]
        simp [middleSlot])

theorem middle_contextPlug_has_arity :
    languageHasConstructorArity
      (groupedDefinition (middleDemand .star)).toLanguageDef
      (auxiliaryLabel .contextPlug 0) 3 = true := by
  simpa [contextPlugTerm, middleSlot, middle_typingAt,
    middle_bindingsAt] using
    middle_constructor_has_arity
      (contextPlugTerm (middleDemand .star) middleSlot) (by
        rw [middle_grouped_terms_explicit]
        simp [middleSlot])

theorem middle_predicateApplication_has_arity :
    languageHasConstructorArity
      (groupedDefinition (middleDemand .star)).toLanguageDef
      (auxiliaryLabel .predicateApplication 0) 2 = true := by
  simpa [predicateApplicationTerm, middleSlot, middle_typingAt] using
    middle_constructor_has_arity
      (predicateApplicationTerm (middleDemand .star) middleSlot) (by
        rw [middle_grouped_terms_explicit]
        simp [middleSlot])

theorem middle_modal_has_arity :
    languageHasConstructorArity
      (groupedDefinition (middleDemand .star)).toLanguageDef
      (SelectedModalNaming.label 0) 3 = true := by
  simpa [ContextualModalExtension.modalRuleAt,
    ContextualModalExtension.typingAt,
    ContextualModalSignature.modalRule_parameter_count,
    SelectedNativeTypeDemand.foundation, middleDemand, middleOccurrence,
    ProfiledRewriteOccurrence.constant, middleSlot,
    middle_occurrence_dependencies_exact] using
    middle_constructor_has_arity
      (ContextualModalExtension.modalRuleAt
        (middleDemand .star).foundation middleSlot) (by
          rw [middle_grouped_terms]
          simp only [List.mem_append]
          exact Or.inl (Or.inl (Or.inr
            (List.mem_ofFn.mpr ⟨middleSlot, rfl⟩))))

/-- The shared empty-context certificate is valid in the concrete mixed
signature. -/
theorem middle_context_nil_rule_validIn :
    RuleSchema.isValidIn (groupedDefinition (middleDemand .star))
      ContextualInferenceCanonicalContext.nilRule = true := by
  unfold RuleSchema.isValidIn
  have localValidity :
      RuleSchema.isLocallyValid
        ContextualInferenceCanonicalContext.nilRule = true := by
    decide +kernel
  rw [localValidity]
  simp [RuleSchema.patterns,
    ContextualInferenceCanonicalContext.nilRule,
    ContextualInferenceCanonicalContext.sequent,
    ContextualInferenceCanonicalContext.claim,
    ContextualInference.lowerSequent,
    ContextualInference.encodeContext,
    CalculusLanguageDef.judgmentSchemaValid,
    CalculusLanguageDef.lookupJudgment?, middle_grouped_judgments,
    fixedConstructorListsValid, fixedConstructorsValid,
    ContextualInference.contextualJudgment,
    CarrierTypingLanguageDef.judgment, CarrierTypingLanguageDef.typingHead,
    middleCarrierName,
    middle_emptyContext_has_arity, middle_contextCode_has_arity]

/-- The shared context-extension certificate is valid in the concrete mixed
signature. -/
theorem middle_context_cons_rule_validIn :
    RuleSchema.isValidIn (groupedDefinition (middleDemand .star))
      ContextualInferenceCanonicalContext.consRule = true := by
  unfold RuleSchema.isValidIn
  have localValidity :
      RuleSchema.isLocallyValid
        ContextualInferenceCanonicalContext.consRule = true := by
    decide +kernel
  rw [localValidity]
  simp [RuleSchema.patterns,
    ContextualInferenceCanonicalContext.consRule,
    ContextualInferenceCanonicalContext.premise,
    ContextualInferenceCanonicalContext.sequent,
    ContextualInferenceCanonicalContext.claim,
    ContextualInference.lowerSequent,
    ContextualInference.encodeContext,
    CalculusLanguageDef.judgmentSchemaValid,
    CalculusLanguageDef.lookupJudgment?, middle_grouped_judgments,
    fixedConstructorListsValid, fixedConstructorsValid,
    ContextualInference.contextualJudgment,
    CarrierTypingLanguageDef.judgment, CarrierTypingLanguageDef.typingHead,
    middleCarrierName,
    middle_emptyContext_has_arity, middle_extendContext_has_arity,
    middle_contextCode_has_arity]

@[simp] theorem middle_profileAt_star
    (slot : Occurrence (middleDemand .star)) :
    (occurrenceAt (middleDemand .star) slot).profile = fun _ => .star := by
  rw [middle_occurrenceAt]
  rfl

/-- The profile-sensitive formation rule is accepted by the mixed contextual
checker, including every fixed constructor in its exact rely telescope. -/
theorem middle_formation_rule_validIn :
    RuleSchema.isValidIn (groupedDefinition (middleDemand .star))
      (lowerRule (formationRule (middleDemand .star) middleSlot)) = true := by
  unfold RuleSchema.isValidIn
  rw [middle_formation_rule_locallyValid]
  simp only [Bool.true_and]
  simp [RuleSchema.patterns, formationRule, relySortPremises,
    resultSortPremise, relyMetavariables, relyVariableClaims,
    relyTypingClaims, modalType, familyApplication, relyTypes, relyValues,
    sortCode, carrierAt, resolve,
    ruleName, RuleKind.tag, relyTypeName, relyValueName,
    indexedMetavariable, middleSlot, middle_typingAt,
    middle_bindingsAt, middleTyping, middle_profileAt_star,
    middle_compiledCarrierName,
    ContextualModalProfile.resultCode,
    ContextualFamilyApplication.applyFamily,
    ContextualCarrierClaims.variableClaim,
    ContextualCarrierClaims.typingClaim,
    ContextualInference.lowerRule, ContextualInference.lowerSequent,
    ContextualInference.encodeContext, ContextSchema.prepend, gamma, delta,
    CalculusLanguageDef.judgmentSchemaValid,
    CalculusLanguageDef.lookupJudgment?, middle_grouped_judgments,
    fixedConstructorListsValid, fixedConstructorsValid,
    ContextualInference.contextualJudgment,
    CarrierTypingLanguageDef.judgment, CarrierTypingLanguageDef.typingHead,
    middle_star_has_arity, middle_extendContext_has_arity,
    middle_variableClaim_has_arity, middle_typingClaim_has_arity,
    middle_familyApplication_has_arity,
    middle_modal_has_arity]

/-- The profile-sensitive introduction rule is accepted by the mixed
contextual checker. -/
theorem middle_introduction_rule_validIn :
    RuleSchema.isValidIn (groupedDefinition (middleDemand .star))
      (lowerRule (introductionRule (middleDemand .star) middleSlot)) = true := by
  unfold RuleSchema.isValidIn
  rw [middle_introduction_rule_locallyValid]
  simp only [Bool.true_and]
  simp [RuleSchema.patterns, introductionRule, relySortPremises,
    resultSortPremise, relyMetavariables, relyVariableClaims,
    relyTypingClaims, modalType, familyApplication, contextPlug,
    relyTypes, relyValues, sortCode, carrierAt, resolve,
    ruleName, RuleKind.tag, relyTypeName, relyValueName,
    indexedMetavariable, middleSlot, middle_typingAt,
    middle_bindingsAt, middleTyping, middle_profileAt_star,
    middle_compiledCarrierName, ContextualModalProfile.resultCode,
    ContextualFamilyApplication.applyFamily,
    ContextualCarrierClaims.variableClaim,
    ContextualCarrierClaims.typingClaim,
    ContextualCarrierClaims.reductionClaim,
    ContextualInference.lowerRule, ContextualInference.lowerSequent,
    ContextualInference.encodeContext, ContextSchema.prepend, gamma, delta,
    CalculusLanguageDef.judgmentSchemaValid,
    CalculusLanguageDef.lookupJudgment?, middle_grouped_judgments,
    fixedConstructorListsValid, fixedConstructorsValid,
    ContextualInference.contextualJudgment,
    CarrierTypingLanguageDef.judgment, CarrierTypingLanguageDef.typingHead,
    middle_star_has_arity, middle_extendContext_has_arity,
    middle_variableClaim_has_arity, middle_typingClaim_has_arity,
    middle_reductionClaim_has_arity, middle_familyApplication_has_arity,
    middle_contextPlug_has_arity,
    middle_modal_has_arity]

/-- The profile-sensitive elimination rule is accepted by the mixed
contextual checker. -/
theorem middle_elimination_rule_validIn :
    RuleSchema.isValidIn (groupedDefinition (middleDemand .star))
      (lowerRule (eliminationRule (middleDemand .star) middleSlot)) = true := by
  unfold RuleSchema.isValidIn
  rw [middle_elimination_rule_locallyValid]
  simp only [Bool.true_and]
  simp [RuleSchema.patterns, eliminationRule, relySortPremises,
    resultSortPremise, relyMetavariables, relyVariableClaims,
    relyTypingClaims, modalType, familyApplication, contextPlug,
    predicateApplication, relyTypes, relyValues, sortCode, carrierAt, resolve,
    ruleName, RuleKind.tag, relyTypeName, relyValueName,
    indexedMetavariable, middleSlot, middle_typingAt,
    middle_bindingsAt, middleTyping, middle_profileAt_star,
    middle_compiledCarrierName, ContextualModalProfile.resultCode,
    ContextualFamilyApplication.applyFamily,
    ContextualCarrierClaims.variableClaim,
    ContextualCarrierClaims.typingClaim,
    ContextualCarrierClaims.reductionClaim,
    ContextualInference.lowerRule, ContextualInference.lowerSequent,
    ContextualInference.encodeContext, ContextSchema.prepend, gamma, delta,
    CalculusLanguageDef.judgmentSchemaValid,
    CalculusLanguageDef.lookupJudgment?, middle_grouped_judgments,
    fixedConstructorListsValid, fixedConstructorsValid,
    ContextualInference.contextualJudgment,
    CarrierTypingLanguageDef.judgment, CarrierTypingLanguageDef.typingHead,
    middle_star_has_arity, middle_extendContext_has_arity,
    middle_variableClaim_has_arity, middle_typingClaim_has_arity,
    middle_reductionClaim_has_arity, middle_familyApplication_has_arity,
    middle_contextPlug_has_arity, middle_predicateApplication_has_arity,
    middle_modal_has_arity]

theorem middle_grouped_rules_validIn :
    (groupedDefinition (middleDemand .star)).rules.all
      (RuleSchema.isValidIn (groupedDefinition (middleDemand .star))) = true := by
  rw [middle_grouped_rules]
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [middle_universe_rule_validIn, middle_context_nil_rule_validIn,
    middle_context_cons_rule_validIn, middle_bridge_rule_validIn,
    middle_formation_rule_validIn, middle_introduction_rule_validIn,
    middle_elimination_rule_validIn]
  rfl

theorem middle_grouped_ruleIds_unique :
    ((groupedDefinition (middleDemand .star)).ruleIds.eraseDups.length ==
      (groupedDefinition (middleDemand .star)).ruleIds.length) = true := by
  rw [CalculusLanguageDef.ruleIds, middle_grouped_rules]
  simp [CarrierTypingLanguageDef.universeAxiom,
    CarrierTypingLanguageDef.axiomName,
    ContextualCarrierClaims.liftTypingRule,
    ContextualCarrierClaims.bridgeRuleName,
    ContextualInference.lowerRule, formationRule, introductionRule,
    eliminationRule, ruleName, RuleKind.tag]
  decide

theorem middle_grouped_judgmentSignatureValid :
    (groupedDefinition (middleDemand .star)).judgmentSignatureValid = true := by
  unfold CalculusLanguageDef.judgmentSignatureValid
    CalculusLanguageDef.judgmentHeads
  rw [middle_grouped_judgments, middle_grouped_terms_explicit]
  simp [CarrierTypingLanguageDef.judgment,
    CarrierTypingLanguageDef.typingHead,
    ContextualInference.contextualJudgment,
    CarrierUniverseSignature.rule, CarrierUniverseSignature.label,
    CarrierUniverseSignature.Code.tag,
    ContextualModalExtension.modalRuleAt,
    ContextualModalExtension.typingAt,
    ContextualModalSignature.modalRule,
    ContextualInference.emptyContextTerm,
    ContextualInference.extendContextTerm,
    ContextualCarrierClaims.variableClaimTerm,
    ContextualCarrierClaims.typingClaimTerm,
    ContextualCarrierClaims.reductionClaimTerm,
    ContextualCarrierClaims.claimLabel, ContextualCarrierClaims.ClaimKind.tag,
    familyApplicationTerm, contextPlugTerm, predicateApplicationTerm,
    auxiliaryLabel, AuxiliaryKind.tag, middle_typingAt,
    middle_bindingsAt,
    Pattern.zipHead, Pattern.mapHead, Pattern.evalHead]
  decide

/-- The concrete two-rely generated calculus passes the complete checker. -/
theorem middle_definition_valid :
    (definition (middleDemand .star)).isValid = true := by
  rw [middle_definition_eq_grouped]
  unfold CalculusLanguageDef.isValid CalculusLanguageDef.hasValidLocalRules
  rw [middle_grouped_language_validate, middle_grouped_rules_locallyValid,
    middle_grouped_ruleIds_unique, middle_grouped_judgmentSignatureValid,
    middle_grouped_rules_validIn]
  simp [CalculusLanguageDef.conversionDeclarationValid,
    middle_grouped_conversion]

/-- Changing only the selected local endpoint changes the emitted rule rows. -/
theorem middle_formation_conclusions_distinct :
    (formationRule (middleDemand .star) ⟨0, by simp [middleDemand]⟩).conclusion ≠
      (formationRule (middleDemand .box) ⟨0, by simp [middleDemand]⟩).conclusion := by
  intro equality
  have conclusionEquality := congrArg Sequent.conclusion equality
  injection conclusionEquality with _ argumentsEquality
  injection argumentsEquality with _ tailEquality
  injection tailEquality with typeEquality _
  change
    sortCode
        (carrierAt (middleDemand .star)
          (typingAt (middleDemand .star) ⟨0, by simp [middleDemand]⟩).focusType)
        .star =
      sortCode
        (carrierAt (middleDemand .box)
          (typingAt (middleDemand .box) ⟨0, by simp [middleDemand]⟩).focusType)
        .box at typeEquality
  unfold sortCode at typeEquality
  injection typeEquality with labels _
  exact CarrierUniverseSignature.star_label_ne_box_label _ _ labels

theorem middle_profiledRules_head
    (code : CarrierUniverseSignature.Code) :
    (profiledRules (middleDemand code)).head? =
      some (lowerRule
        (formationRule (middleDemand code) ⟨0, by simp [middleDemand]⟩)) := by
  simp [profiledRules, rulesAt, middleDemand]

theorem middle_endpoint_rules_distinct :
    profiledRules (middleDemand .star) ≠
      profiledRules (middleDemand .box) := by
  intro equality
  apply middle_formation_conclusions_distinct
  have heads := congrArg List.head? equality
  rw [middle_profiledRules_head, middle_profiledRules_head] at heads
  simp only [Option.some.injEq] at heads
  have lowerConclusions := congrArg RuleSchema.conclusion heads
  exact lowerSequent_injective lowerConclusions

theorem middle_signatures_equal :
    signature (middleDemand .star) = signature (middleDemand .box) := by
  rfl

/-- Hence the complete flat calculus consumes rather than discards the
profile coordinate. -/
theorem middle_endpoint_definitions_distinct :
    definition (middleDemand .star) ≠ definition (middleDemand .box) := by
  intro equality
  have rulesEquality := congrArg CalculusLanguageDef.rules equality
  rw [definition_rules, definition_rules, middle_signatures_equal] at rulesEquality
  exact middle_endpoint_rules_distinct (List.append_cancel_left rulesEquality)

/-- The closed contextual canary introduces only ordinary constructor
parameters.  In particular, none of its generated carrier or proof-calculus
rows silently contributes a collection equation. -/
theorem middle_definition_equationFree :
    (definition (middleDemand .star)).toLanguageDef.isEquationFree = true := by
  rw [middle_definition_eq_grouped]
  unfold LanguageDef.isEquationFree LanguageDef.usesCollection
    LanguageDef.hasAlgebraDeclarations
  rw [middle_grouped_terms_explicit, middle_grouped_equations]
  simp [CarrierUniverseSignature.rule, ContextualModalExtension.modalRuleAt,
    ContextualModalExtension.typingAt, ContextualModalSignature.modalRule,
    ContextualModalSignature.parameters,
    ContextualModalSignature.parametersFor,
    ContextualModalSignature.relyParametersFor,
    ContextualModalSignature.relyBindings,
    ContextualModalSignature.resultFamilyType,
    ContextualModalSignature.resolvedCarrier,
    ContextualInferenceCanonicalContext.contextCodeTerm,
    ContextualCarrierClaims.variableClaimTerm,
    ContextualCarrierClaims.typingClaimTerm,
    ContextualCarrierClaims.reductionClaimTerm,
    familyApplicationTerm, contextPlugTerm, predicateApplicationTerm,
    ContextualInference.emptyContextTerm, ContextualInference.extendContextTerm,
    ContextualModalSignature.mentionsCollection_curryType_map_base,
    middle_typingAt, middle_bindingsAt,
    middleTyping,
    resolve, ContextualModalExtension.compiledCarrierName,
    TermParam.typeExpr, TypeExpr.mentionsCollection]

def middleTheory : Mettapedia.GSLT.GSLT :=
  (definition (middleDemand .star)).toGSLTOfEquationFree
    middle_definition_valid middle_definition_equationFree

theorem middleTheory_term :
    middleTheory.Term = (Pattern ⊕ List Pattern) :=
  rfl

end Canary

#print axioms auxiliaryLabel_injective
#print axioms auxiliaryLabel_ne_of_kind_ne
#print axioms decodeAuxiliaryLabel?_auxiliaryLabel
#print axioms auxiliaryLabel_of_decodeAuxiliaryLabel?_eq_some
#print axioms Canary.middleGrounded
#print axioms Canary.middle_definition_valid
#print axioms Canary.middle_formation_conclusions_distinct
#print axioms Canary.middle_endpoint_rules_distinct
#print axioms Canary.middle_endpoint_definitions_distinct
#print axioms Canary.middle_definition_equationFree
#print axioms Canary.middleTheory_term

end Mettapedia.OSLF.Framework.SelectedNativeTypeContextualCalculus
