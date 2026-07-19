import Mettapedia.Languages.Metamath.InferenceSideConditions

/-!
# Semantics of the Metamath inference side conditions

This file relates the explicit proof-relevant side-condition calculus to
ordinary list and finite-substitution semantics on canonical encodings.  The
semantic relations are defined independently of proof trees and rule names.
-/

namespace Mettapedia.Languages.Metamath.InferenceSideConditionsSemantics

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.Languages.Metamath.MMLean4Bridge
open Mettapedia.Languages.Metamath.InferenceEncoding
open Mettapedia.Languages.Metamath.InferenceEncoding.Builder
open Mettapedia.Languages.Metamath.InferenceSideConditions

private def ruleId (value : String) : RuleId := { value }
private def formal (name : String) : String × Nat := (name, 0)
private def metavariable (name : String) : Pattern := .fvar name

private def proofNode (rule : String) (arguments : List Pattern)
    (children : List RawProof := []) : RawProof :=
  .node { ruleId := ruleId rule, arguments } children

private abbrev EncodedBody (body : List RuntimeSym) : Pattern :=
  encodeListWith encodeSym body

@[simp] private theorem encodeSym_isGroundAt (depth : Nat)
    (symbol : RuntimeSym) : (encodeSym symbol).isGroundAt depth = true := by
  cases symbol <;>
    simp [encodeSym, encodeString, Builder.rawString, Builder.encodedString,
      Builder.constSym, Builder.varSym, Pattern.isGroundAt,
      Pattern.isGroundListAt]

@[simp] private theorem encodedBody_isGroundAt (depth : Nat)
    (body : List RuntimeSym) : (EncodedBody body).isGroundAt depth = true := by
  induction body with
  | nil => simp [EncodedBody, encodeListWith, Pattern.isGroundAt,
      Pattern.isGroundListAt]
  | cons symbol body ih =>
      simp [EncodedBody, encodeListWith, Pattern.isGroundAt,
        Pattern.isGroundListAt, ih]

@[simp] private theorem encodeSym_hasCanonicalBinderMetadata
    (symbol : RuntimeSym) : (encodeSym symbol).hasCanonicalBinderMetadata = true := by
  cases symbol <;>
    simp [encodeSym, encodeString, Builder.rawString, Builder.encodedString,
      Builder.constSym, Builder.varSym, Pattern.hasCanonicalBinderMetadata,
      Pattern.hasCanonicalBinderMetadataList]

@[simp] private theorem encodedBody_hasCanonicalBinderMetadata
    (body : List RuntimeSym) :
    (EncodedBody body).hasCanonicalBinderMetadata = true := by
  induction body with
  | nil => simp [EncodedBody, encodeListWith,
      Pattern.hasCanonicalBinderMetadata,
      Pattern.hasCanonicalBinderMetadataList]
  | cons symbol body ih =>
      simp [EncodedBody, encodeListWith,
        Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList, ih]

private def appendProof : (left right : List RuntimeSym) → RawProof
  | [], right => proofNode "$mm.append.nil" [EncodedBody right]
  | symbol :: left, right =>
      proofNode "$mm.append.cons"
        [ encodeSym symbol, EncodedBody left, EncodedBody right
        , EncodedBody (left ++ right) ]
        [appendProof left right]

private def appendNilSchema : RuleSchema :=
  { id := ruleId "$mm.append.nil"
    metavariables := [formal "Y"]
    premises := []
    conclusion := append Builder.nil (metavariable "Y") (metavariable "Y") }

private def appendConsSchema : RuleSchema :=
  { id := ruleId "$mm.append.cons"
    metavariables :=
      [formal "X", formal "XS", formal "Y", formal "Z"]
    premises :=
      [append (metavariable "XS") (metavariable "Y") (metavariable "Z")]
    conclusion :=
      append (Builder.cons (metavariable "X") (metavariable "XS"))
        (metavariable "Y")
        (Builder.cons (metavariable "X") (metavariable "Z")) }

private def ruleConclusionIs (head : String) (rule : RuleSchema) : Bool :=
  match rule.conclusion with
  | .apply actualHead _ => actualHead == head
  | _ => false

@[simp] private theorem appendNilRule_eq_schema :
    appendNilRule = appendNilSchema := by
  rfl

@[simp] private theorem appendConsRule_eq_schema :
    appendConsRule = appendConsSchema := by
  rfl

private theorem appendRules_filter :
    sideRules.filter (ruleConclusionIs appendHead) =
      [appendNilRule, appendConsRule] := by
  rfl

private theorem InstantiatesAt.apply_head_eq
    {formals : List (String × Nat)} {arguments : List Pattern} {depth : Nat}
    {sourceHead resultHead : String} {sourceArgs resultArgs : List Pattern}
    (instantiation :
      InstantiatesAt formals arguments depth
        (.apply sourceHead sourceArgs) (.apply resultHead resultArgs)) :
    sourceHead = resultHead := by
  cases instantiation
  rfl

@[simp] private theorem appendNilRule_id :
    appendNilRule.id = ruleId "$mm.append.nil" := by
  rfl

@[simp] private theorem appendConsRule_id :
    appendConsRule.id = ruleId "$mm.append.cons" := by
  rfl

private theorem lookup_appendNilRule :
    validatedSidePresentation.1.lookupRule? (ruleId "$mm.append.nil") =
      some appendNilRule := by
  simp [validatedSidePresentation, sidePresentation, sideRules,
    Presentation.lookupRule?, appendNilSchema, appendConsSchema, ruleId,
    formal, metavariable]

private theorem lookup_appendConsRule :
    validatedSidePresentation.1.lookupRule? (ruleId "$mm.append.cons") =
      some appendConsRule := by
  simp [validatedSidePresentation, sidePresentation, sideRules,
    Presentation.lookupRule?, appendNilSchema, appendConsSchema, ruleId,
    formal, metavariable]

private theorem appendNil_instantiates (right : List RuntimeSym) :
    instantiateRule? validatedSidePresentation
        { ruleId := ruleId "$mm.append.nil", arguments := [EncodedBody right] } =
      some ([], append Builder.nil (EncodedBody right) (EncodedBody right)) := by
  simp [instantiateRule?, lookup_appendNilRule, appendNilRule_eq_schema,
    appendNilSchema, formal, metavariable,
    argumentsValidAt, argumentValidAt, instantiateSchemas?,
    instantiateSchemasAt?, instantiateSchema?, instantiateSchemaAt?,
    lookupArgumentAt?, append, appendHead]

private theorem appendCons_instantiates (symbol : RuntimeSym)
    (left right : List RuntimeSym) :
    instantiateRule? validatedSidePresentation
        { ruleId := ruleId "$mm.append.cons"
          arguments :=
            [ encodeSym symbol, EncodedBody left, EncodedBody right
            , EncodedBody (left ++ right) ] } =
      some
        ( [append (EncodedBody left) (EncodedBody right)
            (EncodedBody (left ++ right))]
        , append (EncodedBody (symbol :: left)) (EncodedBody right)
            (EncodedBody (symbol :: (left ++ right))) ) := by
  simp [instantiateRule?, lookup_appendConsRule, appendConsRule_eq_schema,
    appendConsSchema, formal, metavariable, argumentsValidAt,
    argumentValidAt, instantiateSchemas?, instantiateSchemasAt?,
    instantiateSchema?, instantiateSchemaAt?, lookupArgumentAt?, append,
    appendHead, EncodedBody, encodeListWith]

private theorem appendProof_checks (left right : List RuntimeSym) :
    checkRaw validatedSidePresentation
      (append (EncodedBody left) (EncodedBody right) (EncodedBody (left ++ right)))
      (appendProof left right) = true := by
  induction left with
  | nil =>
      simp [appendProof, proofNode, checkRaw, appendNil_instantiates,
        checkRawChildren, EncodedBody, encodeListWith]
  | cons symbol left ih =>
      simpa [appendProof, proofNode, checkRaw, appendCons_instantiates,
        checkRawChildren] using ih

private theorem appendApplication_decompose
    {ruleInstance : RuleInstance} {premises : List Pattern}
    {leftPattern rightPattern resultPattern : Pattern}
    (application :
      RuleApplication validatedSidePresentation ruleInstance premises
        (append leftPattern rightPattern resultPattern)) :
    ∃ rule : RuleSchema,
      (rule = appendNilRule ∨ rule = appendConsRule) ∧
      validatedSidePresentation.1.lookupRule? ruleInstance.ruleId = some rule ∧
      argumentsValidAt rule.metavariables ruleInstance.arguments = true ∧
      InstantiatesList rule.metavariables ruleInstance.arguments
        rule.premises premises ∧
      Instantiates rule.metavariables ruleInstance.arguments rule.conclusion
        (append leftPattern rightPattern resultPattern) := by
  cases application with
  | intro rule hlookup harguments hpremises hconclusion =>
      have hvalid := rule_isValidIn_of_lookup validatedSidePresentation hlookup
      have hshape := RuleSchema.conclusion_hasJudgmentShape_of_validIn hvalid
      have hmem : rule ∈ sideRules := by
        change rule ∈ validatedSidePresentation.1.rules
        exact List.mem_of_find?_eq_some hlookup
      have hrule : rule = appendNilRule ∨ rule = appendConsRule := by
        cases hconclusionRule : rule.conclusion with
        | apply sourceHead sourceArgs =>
            rw [hconclusionRule] at hconclusion
            have hhead : sourceHead = appendHead := by
              exact InstantiatesAt.apply_head_eq hconclusion
            have hselected : ruleConclusionIs appendHead rule = true := by
              simp [ruleConclusionIs, hconclusionRule, hhead]
            have hfiltered :
                rule ∈ sideRules.filter (ruleConclusionIs appendHead) :=
              List.mem_filter.mpr ⟨hmem, hselected⟩
            rw [appendRules_filter] at hfiltered
            simpa using hfiltered
        | bvar index =>
            rw [hconclusionRule] at hshape
            simp [Presentation.hasJudgmentShape] at hshape
        | fvar name =>
            rw [hconclusionRule] at hshape
            simp [Presentation.hasJudgmentShape] at hshape
        | lambda binder body =>
            rw [hconclusionRule] at hshape
            simp [Presentation.hasJudgmentShape] at hshape
        | multiLambda arity binders body =>
            rw [hconclusionRule] at hshape
            simp [Presentation.hasJudgmentShape] at hshape
        | subst body replacement =>
            rw [hconclusionRule] at hshape
            simp [Presentation.hasJudgmentShape] at hshape
        | collection collectionType elements rest =>
            rw [hconclusionRule] at hshape
            simp [Presentation.hasJudgmentShape] at hshape
      exact ⟨rule, hrule, hlookup, harguments, hpremises, hconclusion⟩

private theorem appendNil_application_inv
    {ruleInstance : RuleInstance} {premises : List Pattern}
    {right result : List RuntimeSym}
    (application :
      RuleApplication validatedSidePresentation ruleInstance premises
        (append (EncodedBody []) (EncodedBody right) (EncodedBody result))) :
    premises = [] ∧ result = right := by
  rcases appendApplication_decompose application with
    ⟨rule, hrule, hlookup, harguments, hpremises, hconclusion⟩
  rcases hrule with rfl | rfl
  · cases hargs : ruleInstance.arguments with
    | nil =>
        simp [hargs, appendNilRule_eq_schema, appendNilSchema, formal,
          argumentsValidAt]
          at harguments
    | cons argument rest =>
        cases rest with
        | nil =>
            have hpremises' := instantiateSchemasAt?_complete hpremises
            have hconclusion' := instantiateSchemaAt?_complete hconclusion
            simp [hargs, appendNilRule_eq_schema, appendNilSchema, formal,
              metavariable, instantiateSchemasAt?, instantiateSchemaAt?,
              lookupArgumentAt?, append, EncodedBody, encodeListWith]
              at hpremises' hconclusion'
            constructor
            · exact hpremises'
            · have hencoded : EncodedBody right = EncodedBody result :=
                hconclusion'.1.symm.trans hconclusion'.2
              have hdecoded := congrArg (decodeListWith decodeSym) hencoded
              simpa using hdecoded.symm
        | cons extra extras =>
            simp [hargs, appendNilRule_eq_schema, appendNilSchema, formal,
              argumentsValidAt] at harguments
  · cases hargs : ruleInstance.arguments with
    | nil =>
        simp [hargs, appendConsRule_eq_schema, appendConsSchema, formal,
          argumentsValidAt]
          at harguments
    | cons first rest =>
        cases rest with
        | nil =>
            simp [hargs, appendConsRule_eq_schema, appendConsSchema, formal,
              argumentsValidAt] at harguments
        | cons second rest =>
            cases rest with
            | nil =>
                simp [hargs, appendConsRule_eq_schema, appendConsSchema, formal,
                  argumentsValidAt] at harguments
            | cons third rest =>
                cases rest with
                | nil =>
                    simp [hargs, appendConsRule_eq_schema, appendConsSchema,
                      formal,
                      argumentsValidAt] at harguments
                | cons fourth rest =>
                    cases rest with
                    | nil =>
                        have hconclusion' :=
                          instantiateSchemaAt?_complete hconclusion
                        simp [hargs, appendConsRule_eq_schema, appendConsSchema,
                          formal, metavariable, instantiateSchemaAt?,
                          instantiateSchemasAt?, lookupArgumentAt?, append,
                          EncodedBody, encodeListWith] at hconclusion'
                    | cons extra extras =>
                        simp [hargs, appendConsRule_eq_schema, appendConsSchema,
                          formal, argumentsValidAt] at harguments

private theorem appendCons_application_inv
    {ruleInstance : RuleInstance} {premises : List Pattern}
    {symbol : RuntimeSym} {left right result : List RuntimeSym}
    (application :
      RuleApplication validatedSidePresentation ruleInstance premises
        (append (EncodedBody (symbol :: left)) (EncodedBody right)
          (EncodedBody result))) :
    ∃ resultTail : List RuntimeSym,
      result = symbol :: resultTail ∧
      premises =
        [append (EncodedBody left) (EncodedBody right)
          (EncodedBody resultTail)] := by
  rcases appendApplication_decompose application with
    ⟨rule, hrule, hlookup, harguments, hpremises, hconclusion⟩
  rcases hrule with rfl | rfl
  · cases hargs : ruleInstance.arguments with
    | nil =>
        simp [hargs, appendNilRule_eq_schema, appendNilSchema, formal,
          argumentsValidAt] at harguments
    | cons argument rest =>
        cases rest with
        | nil =>
            have hconclusion' := instantiateSchemaAt?_complete hconclusion
            simp [hargs, appendNilRule_eq_schema, appendNilSchema, formal,
              metavariable, instantiateSchemaAt?, instantiateSchemasAt?,
              lookupArgumentAt?, append, EncodedBody, encodeListWith]
              at hconclusion'
        | cons extra extras =>
            simp [hargs, appendNilRule_eq_schema, appendNilSchema, formal,
              argumentsValidAt] at harguments
  · cases hargs : ruleInstance.arguments with
    | nil =>
        simp [hargs, appendConsRule_eq_schema, appendConsSchema, formal,
          argumentsValidAt] at harguments
    | cons first rest =>
        cases rest with
        | nil =>
            simp [hargs, appendConsRule_eq_schema, appendConsSchema, formal,
              argumentsValidAt] at harguments
        | cons second rest =>
            cases rest with
            | nil =>
                simp [hargs, appendConsRule_eq_schema, appendConsSchema,
                  formal, argumentsValidAt] at harguments
            | cons third rest =>
                cases rest with
                | nil =>
                    simp [hargs, appendConsRule_eq_schema, appendConsSchema,
                      formal, argumentsValidAt] at harguments
                | cons fourth rest =>
                    cases rest with
                    | nil =>
                        have hpremises' :=
                          instantiateSchemasAt?_complete hpremises
                        have hconclusion' :=
                          instantiateSchemaAt?_complete hconclusion
                        cases result with
                        | nil =>
                            simp [hargs, appendConsRule_eq_schema,
                              appendConsSchema, formal, metavariable,
                              instantiateSchemaAt?, instantiateSchemasAt?,
                              lookupArgumentAt?, append, EncodedBody,
                              encodeListWith] at hconclusion'
                        | cons resultSymbol resultTail =>
                            simp [hargs, appendConsRule_eq_schema,
                              appendConsSchema, formal, metavariable,
                              instantiateSchemaAt?, instantiateSchemasAt?,
                              lookupArgumentAt?, append, EncodedBody,
                              encodeListWith] at hpremises' hconclusion'
                            have hsymbol : symbol = resultSymbol := by
                              apply encodeSym_injective
                              exact hconclusion'.1.1.symm.trans
                                hconclusion'.2.2.1
                            subst resultSymbol
                            refine ⟨resultTail, rfl, ?_⟩
                            simpa [append, EncodedBody, hconclusion'.1.2,
                              hconclusion'.2.1,
                              hconclusion'.2.2.2] using hpremises'.symm
                    | cons extra extras =>
                        simp [hargs, appendConsRule_eq_schema,
                          appendConsSchema, formal, argumentsValidAt]
                          at harguments

/-- Every derivation of canonical encoded append reflects ordinary list
append. -/
theorem append_derivation_sound (left right result : List RuntimeSym)
    (derivation :
      Derivation validatedSidePresentation
        (append (EncodedBody left) (EncodedBody right) (EncodedBody result))) :
    left ++ right = result := by
  induction left generalizing result with
  | nil =>
      cases derivation with
      | byRule ruleInstance application children =>
          exact (appendNil_application_inv application).2.symm
  | cons symbol left ih =>
      cases derivation with
      | byRule ruleInstance application children =>
          rcases appendCons_application_inv application with
            ⟨resultTail, hresult, hpremises⟩
          subst result
          rw [hpremises] at children
          cases children with
          | cons child remaining =>
              cases remaining with
              | nil =>
                  simp [ih resultTail child]

/-- Ordinary list append always has a derivation on canonical symbol-list
encodings. -/
theorem append_derivable (left right : List RuntimeSym) :
    Nonempty
      (Derivation validatedSidePresentation
        (append (EncodedBody left) (EncodedBody right)
          (EncodedBody (left ++ right)))) :=
  checkRaw_soundness (appendProof_checks left right)

/-- The explicit Append judgment is adequate for ordinary append on canonical
runtime-symbol lists. -/
theorem append_derivation_iff (left right result : List RuntimeSym) :
    Nonempty
        (Derivation validatedSidePresentation
          (append (EncodedBody left) (EncodedBody right)
            (EncodedBody result))) ↔
      left ++ right = result := by
  constructor
  · rintro ⟨derivation⟩
    exact append_derivation_sound left right result derivation
  · intro hresult
    subst result
    exact append_derivable left right

/-- A non-append result has no derivation. -/
theorem append_not_derivable_of_ne (left right result : List RuntimeSym)
    (hresult : left ++ right ≠ result) :
    ¬Nonempty
      (Derivation validatedSidePresentation
        (append (EncodedBody left) (EncodedBody right)
          (EncodedBody result))) := by
  intro derivable
  exact hresult ((append_derivation_iff left right result).mp derivable)

/-! ## Lookup -/

/-- Independent ordinary-list semantics for finite substitution lookup.  This
is deliberately relational: duplicate keys remain visible until a separate
key-uniqueness hypothesis is supplied. -/
def LookupSemantics (substitution : FiniteSubstitution)
    (variableName : String) (replacement : ConstantHeadedFormula) : Prop :=
  ({ variableName, replacement } : FormulaBinding) ∈ substitution

private abbrev EncodedBindings
    (substitution : FiniteSubstitution) : Pattern :=
  encodeListWith encodeBinding substitution

private abbrev EncodedLookup (substitution : FiniteSubstitution)
    (binding : FormulaBinding) : Pattern :=
  lookup (encodeSubstitution substitution)
    (encodeString binding.variableName)
    (encodeString binding.replacement.typecode)
    (EncodedBody binding.replacement.body)

private theorem encodedBody_injective : Function.Injective EncodedBody := by
  intro left right hencoded
  have hdecoded := congrArg (decodeListWith decodeSym) hencoded
  simpa using hdecoded

@[simp] private theorem encodeString_isGroundAt (depth : Nat)
    (value : String) : (encodeString value).isGroundAt depth = true := by
  simp [encodeString, Builder.rawString, Builder.encodedString,
    Pattern.isGroundAt, Pattern.isGroundListAt]

@[simp] private theorem encodeString_hasCanonicalBinderMetadata
    (value : String) :
    (encodeString value).hasCanonicalBinderMetadata = true := by
  simp [encodeString, Builder.rawString, Builder.encodedString,
    Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList]

@[simp] private theorem encodeFormula_isGroundAt (depth : Nat)
    (formula : ConstantHeadedFormula) :
    (encodeFormula formula).isGroundAt depth = true := by
  cases formula
  simp [encodeFormula, Builder.formula, Pattern.isGroundAt,
    Pattern.isGroundListAt]

@[simp] private theorem encodeFormula_hasCanonicalBinderMetadata
    (formula : ConstantHeadedFormula) :
    (encodeFormula formula).hasCanonicalBinderMetadata = true := by
  cases formula
  simp [encodeFormula, Builder.formula,
    Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList]

@[simp] private theorem encodeBinding_isGroundAt (depth : Nat)
    (binding : FormulaBinding) :
    (encodeBinding binding).isGroundAt depth = true := by
  cases binding
  simp [encodeBinding, Builder.binding, Pattern.isGroundAt,
    Pattern.isGroundListAt]

@[simp] private theorem encodeBinding_hasCanonicalBinderMetadata
    (binding : FormulaBinding) :
    (encodeBinding binding).hasCanonicalBinderMetadata = true := by
  cases binding
  simp [encodeBinding, Builder.binding,
    Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList]

@[simp] private theorem encodedBindings_isGroundAt (depth : Nat)
    (substitution : FiniteSubstitution) :
    (EncodedBindings substitution).isGroundAt depth = true := by
  induction substitution with
  | nil =>
      simp [EncodedBindings, encodeListWith, Pattern.isGroundAt,
        Pattern.isGroundListAt]
  | cons binding substitution ih =>
      simp [EncodedBindings, encodeListWith, Pattern.isGroundAt,
        Pattern.isGroundListAt, ih]

@[simp] private theorem encodedBindings_hasCanonicalBinderMetadata
    (substitution : FiniteSubstitution) :
    (EncodedBindings substitution).hasCanonicalBinderMetadata = true := by
  induction substitution with
  | nil =>
      simp [EncodedBindings, encodeListWith,
        Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList]
  | cons binding substitution ih =>
      simp [EncodedBindings, encodeListWith,
        Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList, ih]

private def lookupHereSchema : RuleSchema :=
  { id := ruleId "$mm.lookup.here"
    metavariables :=
      [formal "V", formal "TC", formal "B", formal "Rest"]
    premises := []
    conclusion :=
      lookup
        (Builder.substitution
          (Builder.cons
            (Builder.binding (metavariable "V")
              (Builder.formula (metavariable "TC") (metavariable "B")))
            (metavariable "Rest")))
        (metavariable "V") (metavariable "TC") (metavariable "B") }

private def lookupThereSchema : RuleSchema :=
  { id := ruleId "$mm.lookup.there"
    metavariables :=
      [ formal "Rest", formal "V", formal "TC", formal "B"
      , formal "W", formal "T0", formal "B0" ]
    premises :=
      [lookup (Builder.substitution (metavariable "Rest"))
        (metavariable "V") (metavariable "TC") (metavariable "B")]
    conclusion :=
      lookup
        (Builder.substitution
          (Builder.cons
            (Builder.binding (metavariable "W")
              (Builder.formula (metavariable "T0") (metavariable "B0")))
            (metavariable "Rest")))
        (metavariable "V") (metavariable "TC") (metavariable "B") }

@[simp] private theorem lookupHereRule_eq_schema :
    lookupHereRule = lookupHereSchema := by
  rfl

@[simp] private theorem lookupThereRule_eq_schema :
    lookupThereRule = lookupThereSchema := by
  rfl

private theorem lookupRules_filter :
    sideRules.filter (ruleConclusionIs lookupHead) =
      [lookupHereRule, lookupThereRule] := by
  rfl

private theorem lookup_lookupHereRule :
    validatedSidePresentation.1.lookupRule? (ruleId "$mm.lookup.here") =
      some lookupHereRule := by
  simp [validatedSidePresentation, sidePresentation, sideRules,
    Presentation.lookupRule?, appendNilSchema, appendConsSchema,
    lookupHereSchema, ruleId, formal, metavariable]

private theorem lookup_lookupThereRule :
    validatedSidePresentation.1.lookupRule? (ruleId "$mm.lookup.there") =
      some lookupThereRule := by
  simp [validatedSidePresentation, sidePresentation, sideRules,
    Presentation.lookupRule?, appendNilSchema, appendConsSchema,
    lookupHereSchema, lookupThereSchema, ruleId, formal, metavariable]

private theorem lookupHere_instantiates (binding : FormulaBinding)
    (rest : FiniteSubstitution) :
    instantiateRule? validatedSidePresentation
        { ruleId := ruleId "$mm.lookup.here"
          arguments :=
            [ encodeString binding.variableName
            , encodeString binding.replacement.typecode
            , EncodedBody binding.replacement.body
            , EncodedBindings rest ] } =
      some ([], EncodedLookup (binding :: rest) binding) := by
  cases binding with
  | mk variableName replacement =>
      cases replacement with
      | mk typecode body =>
          simp [instantiateRule?, lookup_lookupHereRule,
            lookupHereRule_eq_schema, lookupHereSchema, formal, metavariable,
            argumentsValidAt, argumentValidAt, instantiateSchemas?,
            instantiateSchemasAt?, instantiateSchema?, instantiateSchemaAt?,
            lookupArgumentAt?, EncodedLookup, EncodedBindings, EncodedBody,
            encodeSubstitution, encodeBinding, encodeFormula, encodeListWith,
            lookup, lookupHead]

private theorem lookupThere_instantiates (head target : FormulaBinding)
    (rest : FiniteSubstitution) :
    instantiateRule? validatedSidePresentation
        { ruleId := ruleId "$mm.lookup.there"
          arguments :=
            [ EncodedBindings rest
            , encodeString target.variableName
            , encodeString target.replacement.typecode
            , EncodedBody target.replacement.body
            , encodeString head.variableName
            , encodeString head.replacement.typecode
            , EncodedBody head.replacement.body ] } =
      some
        ([EncodedLookup rest target], EncodedLookup (head :: rest) target) := by
  cases head with
  | mk headVariable headReplacement =>
      cases headReplacement with
      | mk headTypecode headBody =>
          cases target with
          | mk targetVariable targetReplacement =>
              cases targetReplacement with
              | mk targetTypecode targetBody =>
                  simp [instantiateRule?, lookup_lookupThereRule,
                    lookupThereRule_eq_schema, lookupThereSchema, formal,
                    metavariable, argumentsValidAt, argumentValidAt,
                    instantiateSchemas?, instantiateSchemasAt?,
                    instantiateSchema?, instantiateSchemaAt?, lookupArgumentAt?,
                    EncodedLookup, EncodedBindings, EncodedBody,
                    encodeSubstitution, encodeBinding, encodeFormula,
                    encodeListWith, lookup, lookupHead]

/-- Membership in the ordinary substitution list constructs a derivation of
the canonical encoded Lookup judgment. -/
theorem lookup_derivable_of_mem (substitution : FiniteSubstitution)
    (target : FormulaBinding) (hmem : target ∈ substitution) :
    Nonempty
      (Derivation validatedSidePresentation
        (EncodedLookup substitution target)) := by
  induction substitution with
  | nil => simp at hmem
  | cons head rest ih =>
      by_cases hhead : head = target
      · subst head
        let ruleInstance : RuleInstance :=
          { ruleId := ruleId "$mm.lookup.here"
            arguments :=
              [ encodeString target.variableName
              , encodeString target.replacement.typecode
              , EncodedBody target.replacement.body
              , EncodedBindings rest ] }
        have happlication :
            RuleApplication validatedSidePresentation ruleInstance []
              (EncodedLookup (target :: rest) target) :=
          instantiateRule?_eq_some_iff_application.mp
            (lookupHere_instantiates target rest)
        exact ⟨Derivation.byRule ruleInstance happlication .nil⟩
      · have htail : target ∈ rest := by
          have htarget : target ≠ head := fun h => hhead h.symm
          simpa [htarget] using hmem
        rcases ih htail with ⟨child⟩
        let ruleInstance : RuleInstance :=
          { ruleId := ruleId "$mm.lookup.there"
            arguments :=
              [ EncodedBindings rest
              , encodeString target.variableName
              , encodeString target.replacement.typecode
              , EncodedBody target.replacement.body
              , encodeString head.variableName
              , encodeString head.replacement.typecode
              , EncodedBody head.replacement.body ] }
        have happlication :
            RuleApplication validatedSidePresentation ruleInstance
              [EncodedLookup rest target]
              (EncodedLookup (head :: rest) target) :=
          instantiateRule?_eq_some_iff_application.mp
            (lookupThere_instantiates head target rest)
        exact ⟨Derivation.byRule ruleInstance happlication
          (.cons child .nil)⟩

private theorem lookupApplication_decompose
    {ruleInstance : RuleInstance} {premises : List Pattern}
    {substitutionPattern variablePattern typecodePattern bodyPattern : Pattern}
    (application :
      RuleApplication validatedSidePresentation ruleInstance premises
        (lookup substitutionPattern variablePattern typecodePattern bodyPattern)) :
    ∃ rule : RuleSchema,
      (rule = lookupHereRule ∨ rule = lookupThereRule) ∧
      validatedSidePresentation.1.lookupRule? ruleInstance.ruleId = some rule ∧
      argumentsValidAt rule.metavariables ruleInstance.arguments = true ∧
      InstantiatesList rule.metavariables ruleInstance.arguments
        rule.premises premises ∧
      Instantiates rule.metavariables ruleInstance.arguments rule.conclusion
        (lookup substitutionPattern variablePattern typecodePattern bodyPattern) := by
  cases application with
  | intro rule hlookup harguments hpremises hconclusion =>
      have hvalid := rule_isValidIn_of_lookup validatedSidePresentation hlookup
      have hshape := RuleSchema.conclusion_hasJudgmentShape_of_validIn hvalid
      have hmem : rule ∈ sideRules := by
        change rule ∈ validatedSidePresentation.1.rules
        exact List.mem_of_find?_eq_some hlookup
      have hrule : rule = lookupHereRule ∨ rule = lookupThereRule := by
        cases hconclusionRule : rule.conclusion with
        | apply sourceHead sourceArgs =>
            rw [hconclusionRule] at hconclusion
            have hhead : sourceHead = lookupHead := by
              exact InstantiatesAt.apply_head_eq hconclusion
            have hselected : ruleConclusionIs lookupHead rule = true := by
              simp [ruleConclusionIs, hconclusionRule, hhead]
            have hfiltered :
                rule ∈ sideRules.filter (ruleConclusionIs lookupHead) :=
              List.mem_filter.mpr ⟨hmem, hselected⟩
            rw [lookupRules_filter] at hfiltered
            simpa using hfiltered
        | bvar index =>
            rw [hconclusionRule] at hshape
            simp [Presentation.hasJudgmentShape] at hshape
        | fvar name =>
            rw [hconclusionRule] at hshape
            simp [Presentation.hasJudgmentShape] at hshape
        | lambda binder body =>
            rw [hconclusionRule] at hshape
            simp [Presentation.hasJudgmentShape] at hshape
        | multiLambda arity binders body =>
            rw [hconclusionRule] at hshape
            simp [Presentation.hasJudgmentShape] at hshape
        | subst body replacement =>
            rw [hconclusionRule] at hshape
            simp [Presentation.hasJudgmentShape] at hshape
        | collection collectionType elements rest =>
            rw [hconclusionRule] at hshape
            simp [Presentation.hasJudgmentShape] at hshape
      exact ⟨rule, hrule, hlookup, harguments, hpremises, hconclusion⟩

private theorem argumentsValidAt_length_eq
    {formals : List (String × Nat)} {arguments : List Pattern}
    (hvalid : argumentsValidAt formals arguments = true) :
    arguments.length = formals.length := by
  induction formals generalizing arguments with
  | nil =>
      cases arguments <;> simp [argumentsValidAt] at hvalid ⊢
  | cons formal formals ih =>
      cases arguments with
      | nil => simp [argumentsValidAt] at hvalid
      | cons argument arguments =>
          simp only [argumentsValidAt, Bool.and_eq_true] at hvalid
          simp [ih hvalid.2]

private theorem List.length_eq_seven {α : Type} {values : List α} :
    values.length = 7 ↔
      ∃ a b c d e f g, values = [a, b, c, d, e, f, g] := by
  constructor
  · intro hlength
    rcases values with _ | ⟨a, values⟩ <;> simp at hlength
    rcases values with _ | ⟨b, values⟩ <;> simp at hlength
    rcases values with _ | ⟨c, values⟩ <;> simp at hlength
    rcases values with _ | ⟨d, values⟩ <;> simp at hlength
    rcases values with _ | ⟨e, values⟩ <;> simp at hlength
    rcases values with _ | ⟨f, values⟩ <;> simp at hlength
    rcases values with _ | ⟨g, values⟩ <;> simp at hlength
    cases values <;> simp at hlength
    exact ⟨a, b, c, d, e, f, g, rfl⟩
  · rintro ⟨a, b, c, d, e, f, g, rfl⟩
    rfl

private theorem lookupCons_application_inv
    {ruleInstance : RuleInstance} {premises : List Pattern}
    {head target : FormulaBinding} {rest : FiniteSubstitution}
    (application :
      RuleApplication validatedSidePresentation ruleInstance premises
        (EncodedLookup (head :: rest) target)) :
    (head = target ∧ premises = []) ∨
      premises = [EncodedLookup rest target] := by
  rcases lookupApplication_decompose application with
    ⟨rule, hrule, hlookup, harguments, hpremises, hconclusion⟩
  rcases hrule with rfl | rfl
  · have hlength := argumentsValidAt_length_eq harguments
    rw [lookupHereRule_eq_schema] at hlength
    simp [lookupHereSchema] at hlength
    rcases List.length_eq_four.mp hlength with
      ⟨encodedVariable, typecode, body, encodedRest, hargs⟩
    have hpremises' := instantiateSchemasAt?_complete hpremises
    have hconclusion' := instantiateSchemaAt?_complete hconclusion
    simp [hargs, lookupHereRule_eq_schema, lookupHereSchema, formal,
      metavariable, instantiateSchemasAt?, instantiateSchemaAt?,
      lookupArgumentAt?, EncodedBody,
      encodeSubstitution, encodeBinding, encodeFormula, encodeListWith,
      lookup, lookupHead] at hpremises' hconclusion'
    left
    constructor
    · have hvariable : head.variableName = target.variableName :=
        encodeString_injective
          (hconclusion'.1.1.1.symm.trans hconclusion'.2.1)
      have htypecode :
          head.replacement.typecode = target.replacement.typecode :=
        encodeString_injective
          (hconclusion'.1.1.2.1.symm.trans hconclusion'.2.2.1)
      have hbody : head.replacement.body = target.replacement.body :=
        encodedBody_injective
          (hconclusion'.1.1.2.2.symm.trans hconclusion'.2.2.2)
      rcases head with ⟨headName, ⟨headCode, headBody⟩⟩
      rcases target with ⟨targetName, ⟨targetCode, targetBody⟩⟩
      change headName = targetName at hvariable
      change headCode = targetCode at htypecode
      change headBody = targetBody at hbody
      subst targetName
      subst targetCode
      subst targetBody
      rfl
    · exact hpremises'
  · have hlength := argumentsValidAt_length_eq harguments
    rw [lookupThereRule_eq_schema] at hlength
    simp [lookupThereSchema] at hlength
    rcases List.length_eq_seven.mp hlength with
      ⟨encodedRest, encodedVariable, typecode, body, headVariable, headTypecode,
        headBody, hargs⟩
    have hpremises' := instantiateSchemasAt?_complete hpremises
    have hconclusion' := instantiateSchemaAt?_complete hconclusion
    simp [hargs, lookupThereRule_eq_schema, lookupThereSchema, formal,
      metavariable, instantiateSchemasAt?, instantiateSchemaAt?,
      lookupArgumentAt?, EncodedBody,
      encodeSubstitution, encodeBinding, encodeFormula, encodeListWith,
      lookup, lookupHead] at hpremises' hconclusion'
    right
    simpa [EncodedLookup, EncodedBindings, EncodedBody, encodeSubstitution,
      lookup, lookupHead,
      hconclusion'.1.2, hconclusion'.2.1, hconclusion'.2.2.1,
      hconclusion'.2.2.2] using hpremises'.symm

private theorem lookupRawCons_application_inv
    {ruleInstance : RuleInstance} {premises : List Pattern}
    {head : FormulaBinding} {rest : FiniteSubstitution}
    {variableName : String} {typecodePattern bodyPattern : Pattern}
    (application :
      RuleApplication validatedSidePresentation ruleInstance premises
        (lookup (encodeSubstitution (head :: rest))
          (encodeString variableName) typecodePattern bodyPattern)) :
    (head.variableName = variableName ∧
        typecodePattern = encodeString head.replacement.typecode ∧
        bodyPattern = EncodedBody head.replacement.body ∧ premises = []) ∨
      premises =
        [lookup (encodeSubstitution rest) (encodeString variableName)
          typecodePattern bodyPattern] := by
  rcases lookupApplication_decompose application with
    ⟨rule, hrule, hlookup, harguments, hpremises, hconclusion⟩
  rcases hrule with rfl | rfl
  · have hlength := argumentsValidAt_length_eq harguments
    rw [lookupHereRule_eq_schema] at hlength
    simp [lookupHereSchema] at hlength
    rcases List.length_eq_four.mp hlength with
      ⟨encodedVariable, typecode, body, encodedRest, hargs⟩
    have hpremises' := instantiateSchemasAt?_complete hpremises
    have hconclusion' := instantiateSchemaAt?_complete hconclusion
    simp [hargs, lookupHereRule_eq_schema, lookupHereSchema, formal,
      metavariable, instantiateSchemasAt?, instantiateSchemaAt?,
      lookupArgumentAt?, encodeSubstitution, encodeBinding, encodeFormula,
      encodeListWith, lookup, lookupHead]
      at hpremises' hconclusion'
    left
    refine ⟨?_, ?_, ?_, hpremises'⟩
    · exact encodeString_injective
        (hconclusion'.1.1.1.symm.trans hconclusion'.2.1)
    · exact hconclusion'.2.2.1.symm.trans hconclusion'.1.1.2.1
    · exact hconclusion'.2.2.2.symm.trans hconclusion'.1.1.2.2
  · have hlength := argumentsValidAt_length_eq harguments
    rw [lookupThereRule_eq_schema] at hlength
    simp [lookupThereSchema] at hlength
    rcases List.length_eq_seven.mp hlength with
      ⟨encodedRest, encodedVariable, typecode, body, headVariable,
        headTypecode, headBody, hargs⟩
    have hpremises' := instantiateSchemasAt?_complete hpremises
    have hconclusion' := instantiateSchemaAt?_complete hconclusion
    simp [hargs, lookupThereRule_eq_schema, lookupThereSchema, formal,
      metavariable, instantiateSchemasAt?, instantiateSchemaAt?,
      lookupArgumentAt?, encodeSubstitution, encodeBinding, encodeFormula,
      encodeListWith, lookup, lookupHead]
      at hpremises' hconclusion'
    right
    simpa [lookup, lookupHead, encodeSubstitution, hconclusion'.1.2,
      hconclusion'.2.1, hconclusion'.2.2.1,
      hconclusion'.2.2.2] using hpremises'.symm

private theorem lookupNil_application_false
    {ruleInstance : RuleInstance} {premises : List Pattern}
    {variableName : String} {typecodePattern bodyPattern : Pattern}
    (application :
      RuleApplication validatedSidePresentation ruleInstance premises
        (lookup (encodeSubstitution []) (encodeString variableName)
          typecodePattern bodyPattern)) : False := by
  rcases lookupApplication_decompose application with
    ⟨rule, hrule, hlookup, harguments, hpremises, hconclusion⟩
  rcases hrule with rfl | rfl
  · have hlength := argumentsValidAt_length_eq harguments
    rw [lookupHereRule_eq_schema] at hlength
    simp [lookupHereSchema] at hlength
    rcases List.length_eq_four.mp hlength with
      ⟨encodedVariable, typecode, body, encodedRest, hargs⟩
    have hconclusion' := instantiateSchemaAt?_complete hconclusion
    simp [hargs, lookupHereRule_eq_schema, lookupHereSchema, formal,
      metavariable, instantiateSchemaAt?, instantiateSchemasAt?,
      lookupArgumentAt?, encodeSubstitution,
      encodeListWith, lookup, lookupHead]
      at hconclusion'
  · have hlength := argumentsValidAt_length_eq harguments
    rw [lookupThereRule_eq_schema] at hlength
    simp [lookupThereSchema] at hlength
    rcases List.length_eq_seven.mp hlength with
      ⟨encodedRest, encodedVariable, typecode, body, headVariable,
        headTypecode, headBody, hargs⟩
    have hconclusion' := instantiateSchemaAt?_complete hconclusion
    simp [hargs, lookupThereRule_eq_schema, lookupThereSchema, formal,
      metavariable, instantiateSchemaAt?, instantiateSchemasAt?,
      lookupArgumentAt?, encodeSubstitution,
      encodeListWith, lookup, lookupHead]
      at hconclusion'

/-- Every derivation of canonical encoded Lookup reflects ordinary list
membership. -/
theorem lookup_derivation_sound (substitution : FiniteSubstitution)
    (target : FormulaBinding)
    (derivation :
      Derivation validatedSidePresentation
        (EncodedLookup substitution target)) :
    target ∈ substitution := by
  induction substitution with
  | nil =>
      cases derivation with
      | byRule ruleInstance application children =>
          exact False.elim (lookupNil_application_false application)
  | cons head rest ih =>
      cases derivation with
      | byRule ruleInstance application children =>
          rcases lookupCons_application_inv application with hhere | hthere
          · simp [hhere.1]
          · rw [hthere] at children
            cases children with
            | cons child remaining =>
                cases remaining with
                | nil => exact List.mem_cons_of_mem head (ih child)

/-- A derivation whose query payloads were not assumed canonical still
decodes them to an actual binding in the canonical substitution.  This is the
form needed by substitution soundness. -/
theorem lookup_derivation_decodes (substitution : FiniteSubstitution)
    (variableName : String) (typecodePattern bodyPattern : Pattern)
    (derivation :
      Derivation validatedSidePresentation
        (lookup (encodeSubstitution substitution) (encodeString variableName)
          typecodePattern bodyPattern)) :
    ∃ replacement : ConstantHeadedFormula,
      LookupSemantics substitution variableName replacement ∧
      typecodePattern = encodeString replacement.typecode ∧
      bodyPattern = EncodedBody replacement.body := by
  induction substitution generalizing typecodePattern bodyPattern with
  | nil =>
      cases derivation with
      | byRule ruleInstance application children =>
          exact False.elim (lookupNil_application_false application)
  | cons head rest ih =>
      cases derivation with
      | byRule ruleInstance application children =>
          rcases lookupRawCons_application_inv application with hhere | hthere
          · refine ⟨head.replacement, ?_, hhere.2.1, hhere.2.2.1⟩
            change
              ({ variableName, replacement := head.replacement } :
                FormulaBinding) ∈ head :: rest
            apply List.mem_cons.mpr
            left
            rcases head with ⟨headName, replacement⟩
            have hname : headName = variableName := hhere.1
            cases hname
            rfl
          · rw [hthere] at children
            cases children with
            | cons child remaining =>
                cases remaining with
                | nil =>
                    rcases ih typecodePattern bodyPattern child with
                      ⟨replacement, hlookup, htypecode, hbody⟩
                    exact ⟨replacement,
                      List.mem_cons_of_mem head hlookup, htypecode, hbody⟩

/-- Relational Lookup derivability is exactly ordinary membership, including
the duplicate-key behavior of the explicit calculus. -/
theorem lookup_binding_derivation_iff
    (substitution : FiniteSubstitution) (target : FormulaBinding) :
    Nonempty
        (Derivation validatedSidePresentation
          (EncodedLookup substitution target)) ↔
      target ∈ substitution := by
  constructor
  · rintro ⟨derivation⟩
    exact lookup_derivation_sound substitution target derivation
  · exact lookup_derivable_of_mem substitution target

/-- Lookup adequacy stated with the independent semantic relation's public
variable-and-formula interface. -/
theorem lookup_derivation_iff (substitution : FiniteSubstitution)
    (variableName : String) (replacement : ConstantHeadedFormula) :
    Nonempty
        (Derivation validatedSidePresentation
          (lookup (encodeSubstitution substitution) (encodeString variableName)
            (encodeString replacement.typecode)
            (encodeListWith encodeSym replacement.body))) ↔
      LookupSemantics substitution variableName replacement := by
  exact lookup_binding_derivation_iff substitution { variableName, replacement }

/-- A binding absent from the ordinary substitution list has no Lookup
derivation. -/
theorem lookup_not_derivable_of_not_mem
    (substitution : FiniteSubstitution) (target : FormulaBinding)
    (habsent : target ∉ substitution) :
    ¬Nonempty
      (Derivation validatedSidePresentation
        (EncodedLookup substitution target)) := by
  intro derivable
  exact habsent ((lookup_binding_derivation_iff substitution target).mp derivable)

/-- The exact source-side invariant under which relational Lookup becomes a
partial function. -/
def SubstitutionKeysUnique (substitution : FiniteSubstitution) : Prop :=
  (substitution.map fun binding => binding.variableName).Nodup

/-- A substitution with unique keys cannot relate one variable to two
different replacement formulas. -/
theorem lookupSemantics_functional
    {substitution : FiniteSubstitution}
    (hunique : SubstitutionKeysUnique substitution)
    {variableName : String}
    {first second : ConstantHeadedFormula}
    (hfirst : LookupSemantics substitution variableName first)
    (hsecond : LookupSemantics substitution variableName second) :
    first = second := by
  induction substitution generalizing first second with
  | nil => simp [LookupSemantics] at hfirst
  | cons head rest ih =>
      simp only [SubstitutionKeysUnique, List.map_cons, List.nodup_cons]
        at hunique
      rcases hunique with ⟨hhead, hrest⟩
      change ({ variableName, replacement := first } : FormulaBinding) ∈
        head :: rest at hfirst
      change ({ variableName, replacement := second } : FormulaBinding) ∈
        head :: rest at hsecond
      simp only [List.mem_cons] at hfirst hsecond
      rcases hfirst with hfirst | hfirst
      · rcases hsecond with hsecond | hsecond
        · exact congrArg FormulaBinding.replacement
            (hfirst.trans hsecond.symm)
        · subst head
          have hkey : variableName ∈
              rest.map fun binding => binding.variableName :=
            List.mem_map.mpr ⟨_, hsecond, rfl⟩
          exact False.elim (hhead hkey)
      · rcases hsecond with hsecond | hsecond
        · subst head
          have hkey : variableName ∈
              rest.map fun binding => binding.variableName :=
            List.mem_map.mpr ⟨_, hfirst, rfl⟩
          exact False.elim (hhead hkey)
        · exact ih hrest hfirst hsecond

/-- Under unique substitution keys, two Lookup derivations at one variable
have the same decoded replacement. -/
theorem lookup_derivation_functional
    {substitution : FiniteSubstitution}
    (hunique : SubstitutionKeysUnique substitution)
    {variableName : String}
    {first second : ConstantHeadedFormula}
    (hfirst :
      Nonempty
        (Derivation validatedSidePresentation
          (lookup (encodeSubstitution substitution) (encodeString variableName)
            (encodeString first.typecode)
            (encodeListWith encodeSym first.body))))
    (hsecond :
      Nonempty
        (Derivation validatedSidePresentation
          (lookup (encodeSubstitution substitution) (encodeString variableName)
            (encodeString second.typecode)
            (encodeListWith encodeSym second.body)))) :
    first = second :=
  lookupSemantics_functional hunique
    ((lookup_derivation_iff substitution variableName first).mp hfirst)
    ((lookup_derivation_iff substitution variableName second).mp hsecond)

/-- Without key uniqueness, both occurrences remain derivable, exactly as
ordinary list membership predicts. -/
theorem duplicate_lookup_derivable (variableName : String)
    (first second : ConstantHeadedFormula)
    (rest : FiniteSubstitution) :
    Nonempty
        (Derivation validatedSidePresentation
          (lookup
            (encodeSubstitution
              ({ variableName, replacement := first } ::
                { variableName, replacement := second } :: rest))
            (encodeString variableName) (encodeString first.typecode)
            (encodeListWith encodeSym first.body))) ∧
      Nonempty
        (Derivation validatedSidePresentation
          (lookup
            (encodeSubstitution
              ({ variableName, replacement := first } ::
                { variableName, replacement := second } :: rest))
            (encodeString variableName) (encodeString second.typecode)
            (encodeListWith encodeSym second.body))) := by
  constructor
  · exact (lookup_derivation_iff _ variableName first).mpr (by
      simp [LookupSemantics])
  · exact (lookup_derivation_iff _ variableName second).mpr (by
      simp [LookupSemantics])

/-! ## Variable extraction -/

/-- Ordinary variable-name extraction from a runtime formula body.  Order and
duplicates are preserved, matching `Formula.varsList`. -/
def BodyVariables : List RuntimeSym → List String
  | [] => []
  | .const _ :: rest => BodyVariables rest
  | .var name :: rest => name :: BodyVariables rest

private abbrev EncodedNames (names : List String) : Pattern :=
  encodeListWith encodeString names

@[simp] private theorem encodedNames_isGroundAt (depth : Nat)
    (names : List String) : (EncodedNames names).isGroundAt depth = true := by
  induction names with
  | nil =>
      simp [EncodedNames, encodeListWith, Pattern.isGroundAt,
        Pattern.isGroundListAt]
  | cons name names ih =>
      simp [EncodedNames, encodeListWith, Pattern.isGroundAt,
        Pattern.isGroundListAt, ih]

@[simp] private theorem encodedNames_hasCanonicalBinderMetadata
    (names : List String) :
    (EncodedNames names).hasCanonicalBinderMetadata = true := by
  induction names with
  | nil =>
      simp [EncodedNames, encodeListWith,
        Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList]
  | cons name names ih =>
      simp [EncodedNames, encodeListWith,
        Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList, ih]

private theorem encodedNames_injective : Function.Injective EncodedNames := by
  intro left right hencoded
  have hdecoded := congrArg (decodeListWith decodeString) hencoded
  simpa using hdecoded

private def varsNilSchema : RuleSchema :=
  { id := ruleId "$mm.vars.nil"
    metavariables := []
    premises := []
    conclusion := vars Builder.nil Builder.nil }

private def varsConstSchema : RuleSchema :=
  { id := ruleId "$mm.vars.const"
    metavariables := [formal "C", formal "XS", formal "VS"]
    premises := [vars (metavariable "XS") (metavariable "VS")]
    conclusion :=
      vars (Builder.cons (Builder.constSym (metavariable "C"))
        (metavariable "XS")) (metavariable "VS") }

private def varsVarSchema : RuleSchema :=
  { id := ruleId "$mm.vars.var"
    metavariables := [formal "V", formal "XS", formal "VS"]
    premises := [vars (metavariable "XS") (metavariable "VS")]
    conclusion :=
      vars (Builder.cons (Builder.varSym (metavariable "V"))
        (metavariable "XS"))
        (Builder.cons (metavariable "V") (metavariable "VS")) }

@[simp] private theorem varsNilRule_eq_schema :
    varsNilRule = varsNilSchema := by
  rfl

@[simp] private theorem varsConstRule_eq_schema :
    varsConstRule = varsConstSchema := by
  rfl

@[simp] private theorem varsVarRule_eq_schema :
    varsVarRule = varsVarSchema := by
  rfl

@[simp] private theorem substBodyNilRule_id :
    substBodyNilRule.id = ruleId "$mm.subst-body.nil" := by
  rfl

@[simp] private theorem substBodyConstRule_id :
    substBodyConstRule.id = ruleId "$mm.subst-body.const" := by
  rfl

@[simp] private theorem substBodyVarRule_id :
    substBodyVarRule.id = ruleId "$mm.subst-body.var" := by
  rfl

@[simp] private theorem applySubstFormulaRule_id :
    applySubstFormulaRule.id = ruleId "$mm.apply-subst.formula" := by
  rfl

private theorem varsRules_filter :
    sideRules.filter (ruleConclusionIs varsHead) =
      [varsNilRule, varsConstRule, varsVarRule] := by
  rfl

private theorem lookup_varsNilRule :
    validatedSidePresentation.1.lookupRule? (ruleId "$mm.vars.nil") =
      some varsNilRule := by
  simp [validatedSidePresentation, sidePresentation, sideRules,
    Presentation.lookupRule?, appendNilSchema, appendConsSchema,
    lookupHereSchema, lookupThereSchema, varsNilSchema, ruleId, formal,
    metavariable]

private theorem lookup_varsConstRule :
    validatedSidePresentation.1.lookupRule? (ruleId "$mm.vars.const") =
      some varsConstRule := by
  simp [validatedSidePresentation, sidePresentation, sideRules,
    Presentation.lookupRule?, appendNilSchema, appendConsSchema,
    lookupHereSchema, lookupThereSchema, varsNilSchema, varsConstSchema,
    ruleId, formal, metavariable]

private theorem lookup_varsVarRule :
    validatedSidePresentation.1.lookupRule? (ruleId "$mm.vars.var") =
      some varsVarRule := by
  simp [validatedSidePresentation, sidePresentation, sideRules,
    Presentation.lookupRule?, appendNilSchema, appendConsSchema,
    lookupHereSchema, lookupThereSchema, varsNilSchema, varsConstSchema,
    varsVarSchema, ruleId, formal, metavariable]

private theorem varsNil_instantiates :
    instantiateRule? validatedSidePresentation
        { ruleId := ruleId "$mm.vars.nil", arguments := [] } =
      some ([], vars (EncodedBody []) (EncodedNames [])) := by
  simp [instantiateRule?, lookup_varsNilRule, varsNilRule_eq_schema,
    varsNilSchema, argumentsValidAt, instantiateSchemas?, instantiateSchemasAt?,
    instantiateSchema?, instantiateSchemaAt?, vars, varsHead, EncodedBody,
    EncodedNames, encodeListWith]

private theorem varsConst_instantiates (name : String)
    (rest : List RuntimeSym) (result : List String) :
    instantiateRule? validatedSidePresentation
        { ruleId := ruleId "$mm.vars.const"
          arguments :=
            [encodeString name, EncodedBody rest, EncodedNames result] } =
      some
        ([vars (EncodedBody rest) (EncodedNames result)],
          vars (EncodedBody (.const name :: rest)) (EncodedNames result)) := by
  simp [instantiateRule?, lookup_varsConstRule, varsConstRule_eq_schema,
    varsConstSchema, formal, metavariable, argumentsValidAt, argumentValidAt,
    instantiateSchemas?, instantiateSchemasAt?, instantiateSchema?,
    instantiateSchemaAt?, lookupArgumentAt?, vars, varsHead, EncodedBody,
    EncodedNames, encodeListWith, encodeSym]

private theorem varsVar_instantiates (name : String)
    (rest : List RuntimeSym) (result : List String) :
    instantiateRule? validatedSidePresentation
        { ruleId := ruleId "$mm.vars.var"
          arguments :=
            [encodeString name, EncodedBody rest, EncodedNames result] } =
      some
        ([vars (EncodedBody rest) (EncodedNames result)],
          vars (EncodedBody (.var name :: rest))
            (EncodedNames (name :: result))) := by
  simp [instantiateRule?, lookup_varsVarRule, varsVarRule_eq_schema,
    varsVarSchema, formal, metavariable, argumentsValidAt, argumentValidAt,
    instantiateSchemas?, instantiateSchemasAt?, instantiateSchema?,
    instantiateSchemaAt?, lookupArgumentAt?, vars, varsHead, EncodedBody,
    EncodedNames, encodeListWith, encodeSym]

/-- Every runtime body has a derivation of its ordinary extracted variable
list. -/
theorem vars_derivable (body : List RuntimeSym) :
    Nonempty
      (Derivation validatedSidePresentation
        (vars (EncodedBody body) (EncodedNames (BodyVariables body)))) := by
  induction body with
  | nil =>
      let ruleInstance : RuleInstance :=
        { ruleId := ruleId "$mm.vars.nil", arguments := [] }
      have happlication :
          RuleApplication validatedSidePresentation ruleInstance []
            (vars (EncodedBody []) (EncodedNames [])) :=
        instantiateRule?_eq_some_iff_application.mp varsNil_instantiates
      exact ⟨Derivation.byRule ruleInstance happlication .nil⟩
  | cons symbol rest ih =>
      rcases ih with ⟨child⟩
      cases symbol with
      | const name =>
          let ruleInstance : RuleInstance :=
            { ruleId := ruleId "$mm.vars.const"
              arguments :=
                [ encodeString name, EncodedBody rest
                , EncodedNames (BodyVariables rest) ] }
          have happlication :
              RuleApplication validatedSidePresentation ruleInstance
                [vars (EncodedBody rest) (EncodedNames (BodyVariables rest))]
                (vars (EncodedBody (.const name :: rest))
                  (EncodedNames (BodyVariables rest))) :=
            instantiateRule?_eq_some_iff_application.mp
              (varsConst_instantiates name rest (BodyVariables rest))
          exact ⟨Derivation.byRule ruleInstance happlication
            (.cons child .nil)⟩
      | var name =>
          let ruleInstance : RuleInstance :=
            { ruleId := ruleId "$mm.vars.var"
              arguments :=
                [ encodeString name, EncodedBody rest
                , EncodedNames (BodyVariables rest) ] }
          have happlication :
              RuleApplication validatedSidePresentation ruleInstance
                [vars (EncodedBody rest) (EncodedNames (BodyVariables rest))]
                (vars (EncodedBody (.var name :: rest))
                  (EncodedNames (name :: BodyVariables rest))) :=
            instantiateRule?_eq_some_iff_application.mp
              (varsVar_instantiates name rest (BodyVariables rest))
          exact ⟨Derivation.byRule ruleInstance happlication
            (.cons child .nil)⟩

private theorem varsApplication_decompose
    {ruleInstance : RuleInstance} {premises : List Pattern}
    {bodyPattern resultPattern : Pattern}
    (application :
      RuleApplication validatedSidePresentation ruleInstance premises
        (vars bodyPattern resultPattern)) :
    ∃ rule : RuleSchema,
      (rule = varsNilRule ∨ rule = varsConstRule ∨ rule = varsVarRule) ∧
      validatedSidePresentation.1.lookupRule? ruleInstance.ruleId = some rule ∧
      argumentsValidAt rule.metavariables ruleInstance.arguments = true ∧
      InstantiatesList rule.metavariables ruleInstance.arguments
        rule.premises premises ∧
      Instantiates rule.metavariables ruleInstance.arguments rule.conclusion
        (vars bodyPattern resultPattern) := by
  cases application with
  | intro rule hlookup harguments hpremises hconclusion =>
      have hvalid := rule_isValidIn_of_lookup validatedSidePresentation hlookup
      have hshape := RuleSchema.conclusion_hasJudgmentShape_of_validIn hvalid
      have hmem : rule ∈ sideRules := by
        change rule ∈ validatedSidePresentation.1.rules
        exact List.mem_of_find?_eq_some hlookup
      have hrule :
          rule = varsNilRule ∨ rule = varsConstRule ∨ rule = varsVarRule := by
        cases hconclusionRule : rule.conclusion with
        | apply sourceHead sourceArgs =>
            rw [hconclusionRule] at hconclusion
            have hhead : sourceHead = varsHead := by
              exact InstantiatesAt.apply_head_eq hconclusion
            have hselected : ruleConclusionIs varsHead rule = true := by
              simp [ruleConclusionIs, hconclusionRule, hhead]
            have hfiltered :
                rule ∈ sideRules.filter (ruleConclusionIs varsHead) :=
              List.mem_filter.mpr ⟨hmem, hselected⟩
            rw [varsRules_filter] at hfiltered
            simpa using hfiltered
        | bvar index =>
            rw [hconclusionRule] at hshape
            simp [Presentation.hasJudgmentShape] at hshape
        | fvar name =>
            rw [hconclusionRule] at hshape
            simp [Presentation.hasJudgmentShape] at hshape
        | lambda binder inner =>
            rw [hconclusionRule] at hshape
            simp [Presentation.hasJudgmentShape] at hshape
        | multiLambda arity binders inner =>
            rw [hconclusionRule] at hshape
            simp [Presentation.hasJudgmentShape] at hshape
        | subst inner replacement =>
            rw [hconclusionRule] at hshape
            simp [Presentation.hasJudgmentShape] at hshape
        | collection collectionType elements rest =>
            rw [hconclusionRule] at hshape
            simp [Presentation.hasJudgmentShape] at hshape
      exact ⟨rule, hrule, hlookup, harguments, hpremises, hconclusion⟩

private theorem varsNil_application_inv
    {ruleInstance : RuleInstance} {premises : List Pattern}
    {result : List String}
    (application :
      RuleApplication validatedSidePresentation ruleInstance premises
        (vars (EncodedBody []) (EncodedNames result))) :
    premises = [] ∧ result = [] := by
  rcases varsApplication_decompose application with
    ⟨rule, hrule, hlookup, harguments, hpremises, hconclusion⟩
  rcases hrule with rfl | rfl | rfl
  · have hlength := argumentsValidAt_length_eq harguments
    rw [varsNilRule_eq_schema] at hlength
    have hargs : ruleInstance.arguments = [] := by
      exact List.eq_nil_of_length_eq_zero
        (by simpa [varsNilSchema] using hlength)
    have hpremises' := instantiateSchemasAt?_complete hpremises
    have hconclusion' := instantiateSchemaAt?_complete hconclusion
    simp [hargs, varsNilRule_eq_schema, varsNilSchema,
      instantiateSchemasAt?, instantiateSchemaAt?, vars, varsHead,
      EncodedBody, EncodedNames, encodeListWith] at hpremises' hconclusion'
    constructor
    · exact hpremises'
    · exact encodedNames_injective hconclusion'.symm
  · have hlength := argumentsValidAt_length_eq harguments
    rw [varsConstRule_eq_schema] at hlength
    simp [varsConstSchema] at hlength
    rcases List.length_eq_three.mp hlength with
      ⟨encodedName, encodedRest, encodedResult, hargs⟩
    have hconclusion' := instantiateSchemaAt?_complete hconclusion
    simp [hargs, varsConstRule_eq_schema, varsConstSchema, formal,
      metavariable, instantiateSchemaAt?, instantiateSchemasAt?,
      lookupArgumentAt?, vars, varsHead, EncodedBody, EncodedNames,
      encodeListWith] at hconclusion'
  · have hlength := argumentsValidAt_length_eq harguments
    rw [varsVarRule_eq_schema] at hlength
    simp [varsVarSchema] at hlength
    rcases List.length_eq_three.mp hlength with
      ⟨encodedName, encodedRest, encodedResult, hargs⟩
    have hconclusion' := instantiateSchemaAt?_complete hconclusion
    simp [hargs, varsVarRule_eq_schema, varsVarSchema, formal, metavariable,
      instantiateSchemaAt?, instantiateSchemasAt?, lookupArgumentAt?, vars,
      varsHead, EncodedBody, EncodedNames, encodeListWith] at hconclusion'

private theorem varsConst_application_inv
    {ruleInstance : RuleInstance} {premises : List Pattern}
    {name : String} {rest : List RuntimeSym} {result : List String}
    (application :
      RuleApplication validatedSidePresentation ruleInstance premises
        (vars (EncodedBody (.const name :: rest)) (EncodedNames result))) :
    premises = [vars (EncodedBody rest) (EncodedNames result)] := by
  rcases varsApplication_decompose application with
    ⟨rule, hrule, hlookup, harguments, hpremises, hconclusion⟩
  rcases hrule with rfl | rfl | rfl
  · have hlength := argumentsValidAt_length_eq harguments
    rw [varsNilRule_eq_schema] at hlength
    have hargs : ruleInstance.arguments = [] :=
      List.eq_nil_of_length_eq_zero (by simpa [varsNilSchema] using hlength)
    have hconclusion' := instantiateSchemaAt?_complete hconclusion
    simp [hargs, varsNilRule_eq_schema, varsNilSchema,
      instantiateSchemaAt?, instantiateSchemasAt?, vars, varsHead,
      EncodedBody, EncodedNames, encodeListWith, encodeSym] at hconclusion'
  · have hlength := argumentsValidAt_length_eq harguments
    rw [varsConstRule_eq_schema] at hlength
    simp [varsConstSchema] at hlength
    rcases List.length_eq_three.mp hlength with
      ⟨encodedName, encodedRest, encodedResult, hargs⟩
    have hpremises' := instantiateSchemasAt?_complete hpremises
    have hconclusion' := instantiateSchemaAt?_complete hconclusion
    simp [hargs, varsConstRule_eq_schema, varsConstSchema, formal,
      metavariable, instantiateSchemasAt?, instantiateSchemaAt?,
      lookupArgumentAt?, vars, varsHead, EncodedBody, EncodedNames,
      encodeListWith, encodeSym] at hpremises' hconclusion'
    simpa [vars, varsHead, hconclusion'.1.2, hconclusion'.2] using
      hpremises'.symm
  · have hlength := argumentsValidAt_length_eq harguments
    rw [varsVarRule_eq_schema] at hlength
    simp [varsVarSchema] at hlength
    rcases List.length_eq_three.mp hlength with
      ⟨encodedName, encodedRest, encodedResult, hargs⟩
    have hconclusion' := instantiateSchemaAt?_complete hconclusion
    simp [hargs, varsVarRule_eq_schema, varsVarSchema, formal, metavariable,
      instantiateSchemaAt?, instantiateSchemasAt?, lookupArgumentAt?, vars,
      varsHead, EncodedBody, EncodedNames, encodeListWith, encodeSym,
      varSymHead, constSymHead]
      at hconclusion'

private theorem varsVar_application_inv
    {ruleInstance : RuleInstance} {premises : List Pattern}
    {name : String} {rest : List RuntimeSym} {result : List String}
    (application :
      RuleApplication validatedSidePresentation ruleInstance premises
        (vars (EncodedBody (.var name :: rest)) (EncodedNames result))) :
    ∃ resultTail : List String,
      result = name :: resultTail ∧
      premises = [vars (EncodedBody rest) (EncodedNames resultTail)] := by
  rcases varsApplication_decompose application with
    ⟨rule, hrule, hlookup, harguments, hpremises, hconclusion⟩
  rcases hrule with rfl | rfl | rfl
  · have hlength := argumentsValidAt_length_eq harguments
    rw [varsNilRule_eq_schema] at hlength
    have hargs : ruleInstance.arguments = [] :=
      List.eq_nil_of_length_eq_zero (by simpa [varsNilSchema] using hlength)
    have hconclusion' := instantiateSchemaAt?_complete hconclusion
    simp [hargs, varsNilRule_eq_schema, varsNilSchema,
      instantiateSchemaAt?, instantiateSchemasAt?, vars, varsHead,
      EncodedBody, EncodedNames, encodeListWith, encodeSym] at hconclusion'
  · have hlength := argumentsValidAt_length_eq harguments
    rw [varsConstRule_eq_schema] at hlength
    simp [varsConstSchema] at hlength
    rcases List.length_eq_three.mp hlength with
      ⟨encodedName, encodedRest, encodedResult, hargs⟩
    have hconclusion' := instantiateSchemaAt?_complete hconclusion
    simp [hargs, varsConstRule_eq_schema, varsConstSchema, formal,
      metavariable, instantiateSchemaAt?, instantiateSchemasAt?,
      lookupArgumentAt?, vars, varsHead, EncodedBody, EncodedNames,
      encodeListWith, encodeSym, constSymHead, varSymHead] at hconclusion'
  · have hlength := argumentsValidAt_length_eq harguments
    rw [varsVarRule_eq_schema] at hlength
    simp [varsVarSchema] at hlength
    rcases List.length_eq_three.mp hlength with
      ⟨encodedName, encodedRest, encodedResult, hargs⟩
    have hpremises' := instantiateSchemasAt?_complete hpremises
    have hconclusion' := instantiateSchemaAt?_complete hconclusion
    cases result with
    | nil =>
        simp [hargs, varsVarRule_eq_schema, varsVarSchema, formal,
          metavariable, instantiateSchemaAt?, instantiateSchemasAt?,
          lookupArgumentAt?, vars, varsHead, EncodedBody, EncodedNames,
          encodeListWith, encodeSym] at hconclusion'
    | cons resultName resultTail =>
        simp [hargs, varsVarRule_eq_schema, varsVarSchema, formal,
          metavariable, instantiateSchemasAt?, instantiateSchemaAt?,
          lookupArgumentAt?, vars, varsHead, EncodedBody, EncodedNames,
          encodeListWith, encodeSym] at hpremises' hconclusion'
        have hname : name = resultName :=
          encodeString_injective
            (hconclusion'.1.1.symm.trans hconclusion'.2.1)
        subst resultName
        refine ⟨resultTail, rfl, ?_⟩
        simpa [vars, varsHead, hconclusion'.1.2,
          hconclusion'.2.2] using hpremises'.symm

/-- Every canonical Vars derivation reflects ordinary variable-name
extraction. -/
theorem vars_derivation_sound (body : List RuntimeSym) (result : List String)
    (derivation :
      Derivation validatedSidePresentation
        (vars (EncodedBody body) (EncodedNames result))) :
    result = BodyVariables body := by
  induction body generalizing result with
  | nil =>
      cases derivation with
      | byRule ruleInstance application children =>
          exact (varsNil_application_inv application).2
  | cons symbol rest ih =>
      cases symbol with
      | const name =>
          cases derivation with
          | byRule ruleInstance application children =>
              have hpremises := varsConst_application_inv application
              rw [hpremises] at children
              cases children with
              | cons child remaining =>
                  cases remaining with
                  | nil => exact ih result child
      | var name =>
          cases derivation with
          | byRule ruleInstance application children =>
              rcases varsVar_application_inv application with
                ⟨resultTail, hresult, hpremises⟩
              rw [hpremises] at children
              cases children with
              | cons child remaining =>
                  cases remaining with
                  | nil =>
                      calc
                        result = name :: resultTail := hresult
                        _ = name :: BodyVariables rest :=
                          congrArg (List.cons name) (ih resultTail child)
                        _ = BodyVariables (.var name :: rest) := rfl

/-- Vars derivability on canonical bodies is exactly ordinary ordered
variable extraction. -/
theorem vars_derivation_iff (body : List RuntimeSym) (result : List String) :
    Nonempty
        (Derivation validatedSidePresentation
          (vars (EncodedBody body) (EncodedNames result))) ↔
      result = BodyVariables body := by
  constructor
  · rintro ⟨derivation⟩
    exact vars_derivation_sound body result derivation
  · intro hresult
    subst result
    exact vars_derivable body

/-- A list different from the extracted runtime variables has no Vars
derivation. -/
theorem vars_not_derivable_of_ne (body : List RuntimeSym)
    (result : List String) (hne : result ≠ BodyVariables body) :
    ¬Nonempty
      (Derivation validatedSidePresentation
        (vars (EncodedBody body) (EncodedNames result))) := by
  intro derivable
  exact hne ((vars_derivation_iff body result).mp derivable)

private theorem varsNil_raw_application_inv
    {ruleInstance : RuleInstance} {premises : List Pattern}
    {resultPattern : Pattern}
    (application :
      RuleApplication validatedSidePresentation ruleInstance premises
        (vars (EncodedBody []) resultPattern)) :
    premises = [] ∧ resultPattern = EncodedNames [] := by
  rcases varsApplication_decompose application with
    ⟨rule, hrule, hlookup, harguments, hpremises, hconclusion⟩
  rcases hrule with rfl | rfl | rfl
  · have hlength := argumentsValidAt_length_eq harguments
    rw [varsNilRule_eq_schema] at hlength
    have hargs : ruleInstance.arguments = [] :=
      List.eq_nil_of_length_eq_zero (by simpa [varsNilSchema] using hlength)
    have hpremises' := instantiateSchemasAt?_complete hpremises
    have hconclusion' := instantiateSchemaAt?_complete hconclusion
    simp [hargs, varsNilRule_eq_schema, varsNilSchema,
      instantiateSchemasAt?, instantiateSchemaAt?, vars, EncodedBody,
      encodeListWith] at hpremises' hconclusion'
    exact ⟨hpremises', hconclusion'.symm⟩
  · have hlength := argumentsValidAt_length_eq harguments
    rw [varsConstRule_eq_schema] at hlength
    simp [varsConstSchema] at hlength
    rcases List.length_eq_three.mp hlength with
      ⟨first, second, third, hargs⟩
    have hconclusion' := instantiateSchemaAt?_complete hconclusion
    simp [hargs, varsConstRule_eq_schema, varsConstSchema, formal,
      metavariable, instantiateSchemaAt?, instantiateSchemasAt?,
      lookupArgumentAt?, vars, EncodedBody, encodeListWith]
      at hconclusion'
  · have hlength := argumentsValidAt_length_eq harguments
    rw [varsVarRule_eq_schema] at hlength
    simp [varsVarSchema] at hlength
    rcases List.length_eq_three.mp hlength with
      ⟨first, second, third, hargs⟩
    have hconclusion' := instantiateSchemaAt?_complete hconclusion
    simp [hargs, varsVarRule_eq_schema, varsVarSchema, formal, metavariable,
      instantiateSchemaAt?, instantiateSchemasAt?, lookupArgumentAt?, vars,
      EncodedBody, encodeListWith] at hconclusion'

private theorem varsConst_raw_application_inv
    {ruleInstance : RuleInstance} {premises : List Pattern}
    {name : String} {rest : List RuntimeSym} {resultPattern : Pattern}
    (application :
      RuleApplication validatedSidePresentation ruleInstance premises
        (vars (EncodedBody (.const name :: rest)) resultPattern)) :
    premises = [vars (EncodedBody rest) resultPattern] := by
  rcases varsApplication_decompose application with
    ⟨rule, hrule, hlookup, harguments, hpremises, hconclusion⟩
  rcases hrule with rfl | rfl | rfl
  · have hlength := argumentsValidAt_length_eq harguments
    rw [varsNilRule_eq_schema] at hlength
    have hargs : ruleInstance.arguments = [] :=
      List.eq_nil_of_length_eq_zero (by simpa [varsNilSchema] using hlength)
    have hconclusion' := instantiateSchemaAt?_complete hconclusion
    simp [hargs, varsNilRule_eq_schema, varsNilSchema,
      instantiateSchemaAt?, instantiateSchemasAt?, vars, EncodedBody,
      encodeListWith] at hconclusion'
  · have hlength := argumentsValidAt_length_eq harguments
    rw [varsConstRule_eq_schema] at hlength
    simp [varsConstSchema] at hlength
    rcases List.length_eq_three.mp hlength with
      ⟨first, second, third, hargs⟩
    have hpremises' := instantiateSchemasAt?_complete hpremises
    have hconclusion' := instantiateSchemaAt?_complete hconclusion
    simp [hargs, varsConstRule_eq_schema, varsConstSchema, formal,
      metavariable, instantiateSchemasAt?, instantiateSchemaAt?,
      lookupArgumentAt?, vars, EncodedBody, encodeListWith, encodeSym]
      at hpremises' hconclusion'
    simpa [vars, EncodedBody, hconclusion'.1.2,
      hconclusion'.2] using hpremises'.symm
  · have hlength := argumentsValidAt_length_eq harguments
    rw [varsVarRule_eq_schema] at hlength
    simp [varsVarSchema] at hlength
    rcases List.length_eq_three.mp hlength with
      ⟨first, second, third, hargs⟩
    have hconclusion' := instantiateSchemaAt?_complete hconclusion
    simp [hargs, varsVarRule_eq_schema, varsVarSchema, formal, metavariable,
      instantiateSchemaAt?, instantiateSchemasAt?, lookupArgumentAt?, vars,
      EncodedBody, encodeListWith, encodeSym, constSymHead, varSymHead]
      at hconclusion'

private theorem varsVar_raw_application_inv
    {ruleInstance : RuleInstance} {premises : List Pattern}
    {name : String} {rest : List RuntimeSym} {resultPattern : Pattern}
    (application :
      RuleApplication validatedSidePresentation ruleInstance premises
        (vars (EncodedBody (.var name :: rest)) resultPattern)) :
    ∃ resultTailPattern : Pattern,
      resultPattern = Builder.cons (encodeString name) resultTailPattern ∧
      premises = [vars (EncodedBody rest) resultTailPattern] := by
  rcases varsApplication_decompose application with
    ⟨rule, hrule, hlookup, harguments, hpremises, hconclusion⟩
  rcases hrule with rfl | rfl | rfl
  · have hlength := argumentsValidAt_length_eq harguments
    rw [varsNilRule_eq_schema] at hlength
    have hargs : ruleInstance.arguments = [] :=
      List.eq_nil_of_length_eq_zero (by simpa [varsNilSchema] using hlength)
    have hconclusion' := instantiateSchemaAt?_complete hconclusion
    simp [hargs, varsNilRule_eq_schema, varsNilSchema,
      instantiateSchemaAt?, instantiateSchemasAt?, vars, EncodedBody,
      encodeListWith] at hconclusion'
  · have hlength := argumentsValidAt_length_eq harguments
    rw [varsConstRule_eq_schema] at hlength
    simp [varsConstSchema] at hlength
    rcases List.length_eq_three.mp hlength with
      ⟨first, second, third, hargs⟩
    have hconclusion' := instantiateSchemaAt?_complete hconclusion
    simp [hargs, varsConstRule_eq_schema, varsConstSchema, formal,
      metavariable, instantiateSchemaAt?, instantiateSchemasAt?,
      lookupArgumentAt?, vars, EncodedBody, encodeListWith, encodeSym,
      constSymHead, varSymHead] at hconclusion'
  · have hlength := argumentsValidAt_length_eq harguments
    rw [varsVarRule_eq_schema] at hlength
    simp [varsVarSchema] at hlength
    rcases List.length_eq_three.mp hlength with
      ⟨first, second, third, hargs⟩
    have hpremises' := instantiateSchemasAt?_complete hpremises
    have hconclusion' := instantiateSchemaAt?_complete hconclusion
    simp [hargs, varsVarRule_eq_schema, varsVarSchema, formal, metavariable,
      instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?, vars,
      EncodedBody, encodeListWith, encodeSym] at hpremises' hconclusion'
    refine ⟨third, ?_, ?_⟩
    · exact hconclusion'.2.symm.trans
        (congrArg (fun value => Builder.cons value third)
          hconclusion'.1.1)
    · simpa [vars, EncodedBody, hconclusion'.1.2] using hpremises'.symm

/-- A Vars derivation with a canonical body forces an initially arbitrary
result pattern to be the canonical ordered variable list. -/
theorem vars_derivation_decodes (body : List RuntimeSym)
    (resultPattern : Pattern)
    (derivation :
      Derivation validatedSidePresentation
        (vars (EncodedBody body) resultPattern)) :
    resultPattern = EncodedNames (BodyVariables body) := by
  induction body generalizing resultPattern with
  | nil =>
      cases derivation with
      | byRule ruleInstance application children =>
          exact (varsNil_raw_application_inv application).2
  | cons symbol body ih =>
      cases symbol with
      | const name =>
          cases derivation with
          | byRule ruleInstance application children =>
              have hpremises := varsConst_raw_application_inv application
              rw [hpremises] at children
              cases children with
              | cons child remaining =>
                  cases remaining with
                  | nil => exact ih resultPattern child
      | var name =>
          cases derivation with
          | byRule ruleInstance application children =>
              rcases varsVar_raw_application_inv application with
                ⟨resultTailPattern, hresult, hpremises⟩
              rw [hpremises] at children
              cases children with
              | cons child remaining =>
                  cases remaining with
                  | nil =>
                      rw [hresult, ih resultTailPattern child]
                      rfl

/-! ## Substitution -/

/- The substitution rules expose intermediate list arguments as arbitrary
patterns.  Before interpreting those rules, recover the canonical result of
Append from canonical inputs. -/

private theorem appendNil_raw_application_inv
    {ruleInstance : RuleInstance} {premises : List Pattern}
    {right : List RuntimeSym} {resultPattern : Pattern}
    (application :
      RuleApplication validatedSidePresentation ruleInstance premises
        (append (EncodedBody []) (EncodedBody right) resultPattern)) :
    premises = [] ∧ resultPattern = EncodedBody right := by
  rcases appendApplication_decompose application with
    ⟨rule, hrule, hlookup, harguments, hpremises, hconclusion⟩
  rcases hrule with rfl | rfl
  · have hlength := argumentsValidAt_length_eq harguments
    rw [appendNilRule_eq_schema] at hlength
    cases hargs : ruleInstance.arguments with
    | nil =>
        simp [hargs, appendNilRule_eq_schema, appendNilSchema, formal,
          argumentsValidAt] at harguments
    | cons argument rest =>
        cases rest with
        | nil =>
            have hpremises' := instantiateSchemasAt?_complete hpremises
            have hconclusion' := instantiateSchemaAt?_complete hconclusion
            simp [hargs, appendNilRule_eq_schema, appendNilSchema, formal,
              metavariable, instantiateSchemasAt?, instantiateSchemaAt?,
              lookupArgumentAt?, append, EncodedBody, encodeListWith]
              at hpremises' hconclusion'
            exact ⟨hpremises', hconclusion'.2.symm.trans hconclusion'.1⟩
        | cons extra extras =>
            simp [hargs, appendNilSchema] at hlength
  · have hlength := argumentsValidAt_length_eq harguments
    rw [appendConsRule_eq_schema] at hlength
    simp [appendConsSchema] at hlength
    rcases List.length_eq_four.mp hlength with
      ⟨first, second, third, fourth, hargs⟩
    have hconclusion' := instantiateSchemaAt?_complete hconclusion
    simp [hargs, appendConsRule_eq_schema, appendConsSchema, formal,
      metavariable, instantiateSchemaAt?, instantiateSchemasAt?,
      lookupArgumentAt?, append, EncodedBody, encodeListWith]
      at hconclusion'

private theorem appendCons_raw_application_inv
    {ruleInstance : RuleInstance} {premises : List Pattern}
    {symbol : RuntimeSym} {left right : List RuntimeSym}
    {resultPattern : Pattern}
    (application :
      RuleApplication validatedSidePresentation ruleInstance premises
        (append (EncodedBody (symbol :: left)) (EncodedBody right)
          resultPattern)) :
    ∃ resultTailPattern : Pattern,
      resultPattern = Builder.cons (encodeSym symbol) resultTailPattern ∧
      premises =
        [append (EncodedBody left) (EncodedBody right) resultTailPattern] := by
  rcases appendApplication_decompose application with
    ⟨rule, hrule, hlookup, harguments, hpremises, hconclusion⟩
  rcases hrule with rfl | rfl
  · have hlength := argumentsValidAt_length_eq harguments
    rw [appendNilRule_eq_schema] at hlength
    cases hargs : ruleInstance.arguments with
    | nil =>
        simp [hargs, appendNilSchema] at hlength
    | cons argument rest =>
        cases rest with
        | nil =>
            have hconclusion' := instantiateSchemaAt?_complete hconclusion
            simp [hargs, appendNilRule_eq_schema, appendNilSchema, formal,
              metavariable, instantiateSchemaAt?, instantiateSchemasAt?,
              lookupArgumentAt?, append, EncodedBody, encodeListWith]
              at hconclusion'
        | cons extra extras =>
            simp [hargs, appendNilSchema] at hlength
  · have hlength := argumentsValidAt_length_eq harguments
    rw [appendConsRule_eq_schema] at hlength
    simp [appendConsSchema] at hlength
    rcases List.length_eq_four.mp hlength with
      ⟨first, second, third, fourth, hargs⟩
    have hpremises' := instantiateSchemasAt?_complete hpremises
    have hconclusion' := instantiateSchemaAt?_complete hconclusion
    simp [hargs, appendConsRule_eq_schema, appendConsSchema, formal,
      metavariable, instantiateSchemasAt?, instantiateSchemaAt?,
      lookupArgumentAt?, append, EncodedBody, encodeListWith]
      at hpremises' hconclusion'
    refine ⟨fourth, ?_, ?_⟩
    · exact hconclusion'.2.2.symm.trans
        (congrArg (fun value => Builder.cons value fourth)
          hconclusion'.1.1)
    · simpa [append, hconclusion'.1.2, hconclusion'.2.1] using
        hpremises'.symm

/-- A derivation of Append with canonical inputs forces its initially
unconstrained output pattern to be the canonical encoding of ordinary list
append. -/
theorem append_derivation_decodes (left right : List RuntimeSym)
    (resultPattern : Pattern)
    (derivation :
      Derivation validatedSidePresentation
        (append (EncodedBody left) (EncodedBody right) resultPattern)) :
    resultPattern = EncodedBody (left ++ right) := by
  induction left generalizing resultPattern with
  | nil =>
      cases derivation with
      | byRule ruleInstance application children =>
          exact (appendNil_raw_application_inv application).2
  | cons symbol left ih =>
      cases derivation with
      | byRule ruleInstance application children =>
          rcases appendCons_raw_application_inv application with
            ⟨resultTailPattern, hresult, hpremises⟩
          rw [hpremises] at children
          cases children with
          | cons child remaining =>
              cases remaining with
              | nil =>
                  rw [hresult, ih resultTailPattern child]
                  rfl

/-- Ordinary, proof-tree-independent semantics of body substitution.  A
variable contributes the body of one matching replacement formula; constants
are copied and the source order is preserved. -/
inductive BodySubstitution (substitution : FiniteSubstitution) :
    List RuntimeSym → List RuntimeSym → Prop
  | nil : BodySubstitution substitution [] []
  | const {name : String} {sourceTail resultTail : List RuntimeSym}
      (tail : BodySubstitution substitution sourceTail resultTail) :
      BodySubstitution substitution (.const name :: sourceTail)
        (.const name :: resultTail)
  | var {name : String} {replacement : ConstantHeadedFormula}
      {sourceTail resultTail : List RuntimeSym}
      (binding : LookupSemantics substitution name replacement)
      (tail : BodySubstitution substitution sourceTail resultTail) :
      BodySubstitution substitution (.var name :: sourceTail)
        (replacement.body ++ resultTail)

private def substBodyNilSchema : RuleSchema :=
  { id := ruleId "$mm.subst-body.nil"
    metavariables := [formal "S"]
    premises := []
    conclusion := substBody (metavariable "S") Builder.nil Builder.nil }

private def substBodyConstSchema : RuleSchema :=
  { id := ruleId "$mm.subst-body.const"
    metavariables :=
      [formal "S", formal "C", formal "XS", formal "YS"]
    premises :=
      [substBody (metavariable "S") (metavariable "XS")
        (metavariable "YS")]
    conclusion :=
      substBody (metavariable "S")
        (Builder.cons (Builder.constSym (metavariable "C"))
          (metavariable "XS"))
        (Builder.cons (Builder.constSym (metavariable "C"))
          (metavariable "YS")) }

private def substBodyVarSchema : RuleSchema :=
  { id := ruleId "$mm.subst-body.var"
    metavariables :=
      [ formal "S", formal "V", formal "TC", formal "Image"
      , formal "XS", formal "YS", formal "ZS" ]
    premises :=
      [ lookup (metavariable "S") (metavariable "V")
          (metavariable "TC") (metavariable "Image")
      , substBody (metavariable "S") (metavariable "XS")
          (metavariable "YS")
      , append (metavariable "Image") (metavariable "YS")
          (metavariable "ZS") ]
    conclusion :=
      substBody (metavariable "S")
        (Builder.cons (Builder.varSym (metavariable "V"))
          (metavariable "XS"))
        (metavariable "ZS") }

@[simp] private theorem substBodyNilRule_eq_schema :
    substBodyNilRule = substBodyNilSchema := by
  rfl

@[simp] private theorem substBodyConstRule_eq_schema :
    substBodyConstRule = substBodyConstSchema := by
  rfl

@[simp] private theorem substBodyVarRule_eq_schema :
    substBodyVarRule = substBodyVarSchema := by
  rfl

private theorem substBodyRules_filter :
    sideRules.filter (ruleConclusionIs substBodyHead) =
      [substBodyNilRule, substBodyConstRule, substBodyVarRule] := by
  rfl

@[simp] private theorem encodeSubstitution_isGroundAt (depth : Nat)
    (substitution : FiniteSubstitution) :
    (encodeSubstitution substitution).isGroundAt depth = true := by
  simp [encodeSubstitution, Builder.substitution, Pattern.isGroundAt,
    Pattern.isGroundListAt]

@[simp] private theorem encodeSubstitution_hasCanonicalBinderMetadata
    (substitution : FiniteSubstitution) :
    (encodeSubstitution substitution).hasCanonicalBinderMetadata = true := by
  simp [encodeSubstitution, Builder.substitution,
    Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList]

private theorem lookup_substBodyNilRule :
    validatedSidePresentation.1.lookupRule?
        (ruleId "$mm.subst-body.nil") = some substBodyNilRule := by
  simp [validatedSidePresentation, sidePresentation, sideRules,
    Presentation.lookupRule?, appendNilSchema, appendConsSchema,
    lookupHereSchema, lookupThereSchema, substBodyNilSchema, ruleId, formal,
    metavariable]

private theorem lookup_substBodyConstRule :
    validatedSidePresentation.1.lookupRule?
        (ruleId "$mm.subst-body.const") = some substBodyConstRule := by
  simp [validatedSidePresentation, sidePresentation, sideRules,
    Presentation.lookupRule?, appendNilSchema, appendConsSchema,
    lookupHereSchema, lookupThereSchema, substBodyNilSchema,
    substBodyConstSchema, ruleId, formal, metavariable]

private theorem lookup_substBodyVarRule :
    validatedSidePresentation.1.lookupRule?
        (ruleId "$mm.subst-body.var") = some substBodyVarRule := by
  simp [validatedSidePresentation, sidePresentation, sideRules,
    Presentation.lookupRule?, appendNilSchema, appendConsSchema,
    lookupHereSchema, lookupThereSchema, substBodyNilSchema,
    substBodyConstSchema, substBodyVarSchema, ruleId, formal, metavariable]

private theorem substBodyNil_instantiates
    (substitution : FiniteSubstitution) :
    instantiateRule? validatedSidePresentation
        { ruleId := ruleId "$mm.subst-body.nil"
          arguments := [encodeSubstitution substitution] } =
      some
        ([], substBody (encodeSubstitution substitution)
          (EncodedBody []) (EncodedBody [])) := by
  simp [instantiateRule?, lookup_substBodyNilRule,
    substBodyNilRule_eq_schema, substBodyNilSchema, formal, metavariable,
    argumentsValidAt, argumentValidAt, instantiateSchemas?,
    instantiateSchemasAt?, instantiateSchema?, instantiateSchemaAt?,
    lookupArgumentAt?, substBody, substBodyHead, EncodedBody, encodeListWith]

private theorem substBodyConst_instantiates
    (substitution : FiniteSubstitution) (name : String)
    (sourceTail resultTail : List RuntimeSym) :
    instantiateRule? validatedSidePresentation
        { ruleId := ruleId "$mm.subst-body.const"
          arguments :=
            [ encodeSubstitution substitution, encodeString name
            , EncodedBody sourceTail, EncodedBody resultTail ] } =
      some
        ( [substBody (encodeSubstitution substitution)
            (EncodedBody sourceTail) (EncodedBody resultTail)]
        , substBody (encodeSubstitution substitution)
            (EncodedBody (.const name :: sourceTail))
            (EncodedBody (.const name :: resultTail)) ) := by
  simp [instantiateRule?, lookup_substBodyConstRule,
    substBodyConstRule_eq_schema, substBodyConstSchema, formal, metavariable,
    argumentsValidAt, argumentValidAt, instantiateSchemas?,
    instantiateSchemasAt?, instantiateSchema?, instantiateSchemaAt?,
    lookupArgumentAt?, substBody, substBodyHead, EncodedBody, encodeListWith,
    encodeSym]

private theorem substBodyVar_instantiates
    (substitution : FiniteSubstitution) (name : String)
    (replacement : ConstantHeadedFormula)
    (sourceTail resultTail : List RuntimeSym) :
    instantiateRule? validatedSidePresentation
        { ruleId := ruleId "$mm.subst-body.var"
          arguments :=
            [ encodeSubstitution substitution, encodeString name
            , encodeString replacement.typecode
            , EncodedBody replacement.body, EncodedBody sourceTail
            , EncodedBody resultTail
            , EncodedBody (replacement.body ++ resultTail) ] } =
      some
        ( [ lookup (encodeSubstitution substitution) (encodeString name)
              (encodeString replacement.typecode)
              (EncodedBody replacement.body)
          , substBody (encodeSubstitution substitution)
              (EncodedBody sourceTail) (EncodedBody resultTail)
          , append (EncodedBody replacement.body) (EncodedBody resultTail)
              (EncodedBody (replacement.body ++ resultTail)) ]
        , substBody (encodeSubstitution substitution)
            (EncodedBody (.var name :: sourceTail))
            (EncodedBody (replacement.body ++ resultTail)) ) := by
  simp [instantiateRule?, lookup_substBodyVarRule,
    substBodyVarRule_eq_schema, substBodyVarSchema, formal, metavariable,
    argumentsValidAt, argumentValidAt, instantiateSchemas?,
    instantiateSchemasAt?, instantiateSchema?, instantiateSchemaAt?,
    lookupArgumentAt?, lookup, lookupHead, substBody, substBodyHead, append,
    appendHead, EncodedBody, encodeListWith, encodeSym]

/-- Independent semantic body substitution constructs a derivation of the
canonical encoded SubstBody judgment. -/
theorem substBody_derivable {substitution : FiniteSubstitution}
    {source result : List RuntimeSym}
    (semantics : BodySubstitution substitution source result) :
    Nonempty
      (Derivation validatedSidePresentation
        (substBody (encodeSubstitution substitution) (EncodedBody source)
          (EncodedBody result))) := by
  induction semantics with
  | nil =>
      let ruleInstance : RuleInstance :=
        { ruleId := ruleId "$mm.subst-body.nil"
          arguments := [encodeSubstitution substitution] }
      have happlication :
          RuleApplication validatedSidePresentation ruleInstance []
            (substBody (encodeSubstitution substitution)
              (EncodedBody []) (EncodedBody [])) :=
        instantiateRule?_eq_some_iff_application.mp
          (substBodyNil_instantiates substitution)
      exact ⟨Derivation.byRule ruleInstance happlication .nil⟩
  | @const name sourceTail resultTail tail ih =>
      rcases ih with ⟨tailChild⟩
      let ruleInstance : RuleInstance :=
        { ruleId := ruleId "$mm.subst-body.const"
          arguments :=
            [ encodeSubstitution substitution, encodeString name
            , EncodedBody sourceTail, EncodedBody resultTail ] }
      have happlication :
          RuleApplication validatedSidePresentation ruleInstance
            [substBody (encodeSubstitution substitution)
              (EncodedBody sourceTail) (EncodedBody resultTail)]
            (substBody (encodeSubstitution substitution)
              (EncodedBody (.const name :: sourceTail))
              (EncodedBody (.const name :: resultTail))) :=
        instantiateRule?_eq_some_iff_application.mp
          (substBodyConst_instantiates substitution name sourceTail resultTail)
      exact ⟨Derivation.byRule ruleInstance happlication
        (.cons tailChild .nil)⟩
  | @var name replacement sourceTail resultTail binding tail ih =>
      rcases lookup_derivable_of_mem substitution
          ({ variableName := name, replacement } : FormulaBinding) binding with
        ⟨lookupChild⟩
      rcases ih with ⟨tailChild⟩
      rcases append_derivable replacement.body resultTail with ⟨appendChild⟩
      let ruleInstance : RuleInstance :=
        { ruleId := ruleId "$mm.subst-body.var"
          arguments :=
            [ encodeSubstitution substitution, encodeString name
            , encodeString replacement.typecode
            , EncodedBody replacement.body, EncodedBody sourceTail
            , EncodedBody resultTail
            , EncodedBody (replacement.body ++ resultTail) ] }
      have happlication :
          RuleApplication validatedSidePresentation ruleInstance
            [ lookup (encodeSubstitution substitution) (encodeString name)
                (encodeString replacement.typecode)
                (EncodedBody replacement.body)
            , substBody (encodeSubstitution substitution)
                (EncodedBody sourceTail) (EncodedBody resultTail)
            , append (EncodedBody replacement.body) (EncodedBody resultTail)
                (EncodedBody (replacement.body ++ resultTail)) ]
            (substBody (encodeSubstitution substitution)
              (EncodedBody (.var name :: sourceTail))
              (EncodedBody (replacement.body ++ resultTail))) :=
        instantiateRule?_eq_some_iff_application.mp
          (substBodyVar_instantiates substitution name replacement sourceTail
            resultTail)
      exact ⟨Derivation.byRule ruleInstance happlication
        (.cons lookupChild (.cons tailChild (.cons appendChild .nil)))⟩

private theorem substBodyApplication_decompose
    {ruleInstance : RuleInstance} {premises : List Pattern}
    {substitutionPattern sourcePattern resultPattern : Pattern}
    (application :
      RuleApplication validatedSidePresentation ruleInstance premises
        (substBody substitutionPattern sourcePattern resultPattern)) :
    ∃ rule : RuleSchema,
      (rule = substBodyNilRule ∨ rule = substBodyConstRule ∨
        rule = substBodyVarRule) ∧
      validatedSidePresentation.1.lookupRule? ruleInstance.ruleId = some rule ∧
      argumentsValidAt rule.metavariables ruleInstance.arguments = true ∧
      InstantiatesList rule.metavariables ruleInstance.arguments
        rule.premises premises ∧
      Instantiates rule.metavariables ruleInstance.arguments rule.conclusion
        (substBody substitutionPattern sourcePattern resultPattern) := by
  cases application with
  | intro rule hlookup harguments hpremises hconclusion =>
      have hvalid := rule_isValidIn_of_lookup validatedSidePresentation hlookup
      have hshape := RuleSchema.conclusion_hasJudgmentShape_of_validIn hvalid
      have hmem : rule ∈ sideRules := by
        change rule ∈ validatedSidePresentation.1.rules
        exact List.mem_of_find?_eq_some hlookup
      have hrule :
          rule = substBodyNilRule ∨ rule = substBodyConstRule ∨
            rule = substBodyVarRule := by
        cases hconclusionRule : rule.conclusion with
        | apply sourceHead sourceArgs =>
            rw [hconclusionRule] at hconclusion
            have hhead : sourceHead = substBodyHead := by
              exact InstantiatesAt.apply_head_eq hconclusion
            have hselected : ruleConclusionIs substBodyHead rule = true := by
              simp [ruleConclusionIs, hconclusionRule, hhead]
            have hfiltered :
                rule ∈ sideRules.filter (ruleConclusionIs substBodyHead) :=
              List.mem_filter.mpr ⟨hmem, hselected⟩
            rw [substBodyRules_filter] at hfiltered
            simpa using hfiltered
        | bvar index =>
            rw [hconclusionRule] at hshape
            simp [Presentation.hasJudgmentShape] at hshape
        | fvar name =>
            rw [hconclusionRule] at hshape
            simp [Presentation.hasJudgmentShape] at hshape
        | lambda binder body =>
            rw [hconclusionRule] at hshape
            simp [Presentation.hasJudgmentShape] at hshape
        | multiLambda arity binders body =>
            rw [hconclusionRule] at hshape
            simp [Presentation.hasJudgmentShape] at hshape
        | subst body replacement =>
            rw [hconclusionRule] at hshape
            simp [Presentation.hasJudgmentShape] at hshape
        | collection collectionType elements rest =>
            rw [hconclusionRule] at hshape
            simp [Presentation.hasJudgmentShape] at hshape
      exact ⟨rule, hrule, hlookup, harguments, hpremises, hconclusion⟩

private theorem substBodyNil_raw_application_inv
    {ruleInstance : RuleInstance} {premises : List Pattern}
    {substitution : FiniteSubstitution} {resultPattern : Pattern}
    (application :
      RuleApplication validatedSidePresentation ruleInstance premises
        (substBody (encodeSubstitution substitution) (EncodedBody [])
          resultPattern)) :
    premises = [] ∧ resultPattern = EncodedBody [] := by
  rcases substBodyApplication_decompose application with
    ⟨rule, hrule, hlookup, harguments, hpremises, hconclusion⟩
  rcases hrule with rfl | rfl | rfl
  · have hlength := argumentsValidAt_length_eq harguments
    rw [substBodyNilRule_eq_schema] at hlength
    cases hargs : ruleInstance.arguments with
    | nil =>
        simp [hargs, substBodyNilSchema] at hlength
    | cons argument rest =>
        cases rest with
        | nil =>
            have hpremises' := instantiateSchemasAt?_complete hpremises
            have hconclusion' := instantiateSchemaAt?_complete hconclusion
            simp [hargs, substBodyNilRule_eq_schema, substBodyNilSchema,
              formal, metavariable, instantiateSchemasAt?,
              instantiateSchemaAt?, lookupArgumentAt?, substBody,
              EncodedBody, encodeListWith] at hpremises' hconclusion'
            exact ⟨hpremises', by simpa [EncodedBody, encodeListWith] using
              hconclusion'.2.symm⟩
        | cons extra extras =>
            simp [hargs, substBodyNilSchema] at hlength
  · have hlength := argumentsValidAt_length_eq harguments
    rw [substBodyConstRule_eq_schema] at hlength
    simp [substBodyConstSchema] at hlength
    rcases List.length_eq_four.mp hlength with
      ⟨first, second, third, fourth, hargs⟩
    have hconclusion' := instantiateSchemaAt?_complete hconclusion
    simp [hargs, substBodyConstRule_eq_schema, substBodyConstSchema, formal,
      metavariable, instantiateSchemaAt?, instantiateSchemasAt?,
      lookupArgumentAt?, substBody, EncodedBody, encodeListWith]
      at hconclusion'
  · have hlength := argumentsValidAt_length_eq harguments
    rw [substBodyVarRule_eq_schema] at hlength
    simp [substBodyVarSchema] at hlength
    rcases List.length_eq_seven.mp hlength with
      ⟨first, second, third, fourth, fifth, sixth, seventh, hargs⟩
    have hconclusion' := instantiateSchemaAt?_complete hconclusion
    simp [hargs, substBodyVarRule_eq_schema, substBodyVarSchema, formal,
      metavariable, instantiateSchemaAt?, instantiateSchemasAt?,
      lookupArgumentAt?, substBody, EncodedBody, encodeListWith]
      at hconclusion'

private theorem substBodyConst_raw_application_inv
    {ruleInstance : RuleInstance} {premises : List Pattern}
    {substitution : FiniteSubstitution} {name : String}
    {sourceTail : List RuntimeSym} {resultPattern : Pattern}
    (application :
      RuleApplication validatedSidePresentation ruleInstance premises
        (substBody (encodeSubstitution substitution)
          (EncodedBody (.const name :: sourceTail)) resultPattern)) :
    ∃ resultTailPattern : Pattern,
      resultPattern =
          Builder.cons (encodeSym (.const name)) resultTailPattern ∧
      premises =
        [substBody (encodeSubstitution substitution) (EncodedBody sourceTail)
          resultTailPattern] := by
  rcases substBodyApplication_decompose application with
    ⟨rule, hrule, hlookup, harguments, hpremises, hconclusion⟩
  rcases hrule with rfl | rfl | rfl
  · have hlength := argumentsValidAt_length_eq harguments
    rw [substBodyNilRule_eq_schema] at hlength
    cases hargs : ruleInstance.arguments with
    | nil =>
        simp [hargs, substBodyNilSchema] at hlength
    | cons argument rest =>
        cases rest with
        | nil =>
            have hconclusion' := instantiateSchemaAt?_complete hconclusion
            simp [hargs, substBodyNilRule_eq_schema, substBodyNilSchema,
              formal, metavariable, instantiateSchemaAt?,
              instantiateSchemasAt?, lookupArgumentAt?, substBody,
              EncodedBody, encodeListWith] at hconclusion'
        | cons extra extras =>
            simp [hargs, substBodyNilSchema] at hlength
  · have hlength := argumentsValidAt_length_eq harguments
    rw [substBodyConstRule_eq_schema] at hlength
    simp [substBodyConstSchema] at hlength
    rcases List.length_eq_four.mp hlength with
      ⟨first, second, third, fourth, hargs⟩
    have hpremises' := instantiateSchemasAt?_complete hpremises
    have hconclusion' := instantiateSchemaAt?_complete hconclusion
    simp [hargs, substBodyConstRule_eq_schema, substBodyConstSchema, formal,
      metavariable, instantiateSchemasAt?, instantiateSchemaAt?,
      lookupArgumentAt?, substBody, EncodedBody, encodeListWith, encodeSym]
      at hpremises' hconclusion'
    refine ⟨fourth, ?_, ?_⟩
    · exact hconclusion'.2.2.symm.trans
        (congrArg
          (fun value => Builder.cons (Builder.constSym value) fourth)
          hconclusion'.2.1.1)
    · simpa [substBody, hconclusion'.1, hconclusion'.2.1.2] using
        hpremises'.symm
  · have hlength := argumentsValidAt_length_eq harguments
    rw [substBodyVarRule_eq_schema] at hlength
    simp [substBodyVarSchema] at hlength
    rcases List.length_eq_seven.mp hlength with
      ⟨first, second, third, fourth, fifth, sixth, seventh, hargs⟩
    have hconclusion' := instantiateSchemaAt?_complete hconclusion
    simp [hargs, substBodyVarRule_eq_schema, substBodyVarSchema, formal,
      metavariable, instantiateSchemaAt?, instantiateSchemasAt?,
      lookupArgumentAt?, substBody, EncodedBody, encodeListWith, encodeSym,
      constSymHead, varSymHead] at hconclusion'

private theorem substBodyVar_raw_application_inv
    {ruleInstance : RuleInstance} {premises : List Pattern}
    {substitution : FiniteSubstitution} {name : String}
    {sourceTail : List RuntimeSym} {resultPattern : Pattern}
    (application :
      RuleApplication validatedSidePresentation ruleInstance premises
        (substBody (encodeSubstitution substitution)
          (EncodedBody (.var name :: sourceTail)) resultPattern)) :
    ∃ typecodePattern imagePattern resultTailPattern : Pattern,
      premises =
        [ lookup (encodeSubstitution substitution) (encodeString name)
            typecodePattern imagePattern
        , substBody (encodeSubstitution substitution) (EncodedBody sourceTail)
            resultTailPattern
        , append imagePattern resultTailPattern resultPattern ] := by
  rcases substBodyApplication_decompose application with
    ⟨rule, hrule, hlookup, harguments, hpremises, hconclusion⟩
  rcases hrule with rfl | rfl | rfl
  · have hlength := argumentsValidAt_length_eq harguments
    rw [substBodyNilRule_eq_schema] at hlength
    cases hargs : ruleInstance.arguments with
    | nil =>
        simp [hargs, substBodyNilSchema] at hlength
    | cons argument rest =>
        cases rest with
        | nil =>
            have hconclusion' := instantiateSchemaAt?_complete hconclusion
            simp [hargs, substBodyNilRule_eq_schema, substBodyNilSchema,
              formal, metavariable, instantiateSchemaAt?,
              instantiateSchemasAt?, lookupArgumentAt?, substBody,
              EncodedBody, encodeListWith] at hconclusion'
        | cons extra extras =>
            simp [hargs, substBodyNilSchema] at hlength
  · have hlength := argumentsValidAt_length_eq harguments
    rw [substBodyConstRule_eq_schema] at hlength
    simp [substBodyConstSchema] at hlength
    rcases List.length_eq_four.mp hlength with
      ⟨first, second, third, fourth, hargs⟩
    have hconclusion' := instantiateSchemaAt?_complete hconclusion
    simp [hargs, substBodyConstRule_eq_schema, substBodyConstSchema, formal,
      metavariable, instantiateSchemaAt?, instantiateSchemasAt?,
      lookupArgumentAt?, substBody, EncodedBody, encodeListWith, encodeSym,
      constSymHead, varSymHead] at hconclusion'
  · have hlength := argumentsValidAt_length_eq harguments
    rw [substBodyVarRule_eq_schema] at hlength
    simp [substBodyVarSchema] at hlength
    rcases List.length_eq_seven.mp hlength with
      ⟨first, second, third, fourth, fifth, sixth, seventh, hargs⟩
    have hpremises' := instantiateSchemasAt?_complete hpremises
    have hconclusion' := instantiateSchemaAt?_complete hconclusion
    simp [hargs, substBodyVarRule_eq_schema, substBodyVarSchema, formal,
      metavariable, instantiateSchemasAt?, instantiateSchemaAt?,
      lookupArgumentAt?, lookup, lookupHead, substBody, append, appendHead,
      EncodedBody, encodeListWith, encodeSym]
      at hpremises' hconclusion'
    refine ⟨third, fourth, sixth, ?_⟩
    simpa [lookup, lookupHead, substBody, append, appendHead, EncodedBody,
      hconclusion'.1,
      hconclusion'.2.1.1, hconclusion'.2.1.2, hconclusion'.2.2] using
      hpremises'.symm

/-- A derivation whose result argument was not assumed canonical decodes it
to an ordinary substituted body satisfying the independent semantics. -/
theorem substBody_derivation_decodes (substitution : FiniteSubstitution)
    (source : List RuntimeSym) (resultPattern : Pattern)
    (derivation :
      Derivation validatedSidePresentation
        (substBody (encodeSubstitution substitution) (EncodedBody source)
          resultPattern)) :
    ∃ result : List RuntimeSym,
      resultPattern = EncodedBody result ∧
      BodySubstitution substitution source result := by
  induction source generalizing resultPattern with
  | nil =>
      cases derivation with
      | byRule ruleInstance application children =>
          have hinversion := substBodyNil_raw_application_inv application
          exact ⟨[], hinversion.2, BodySubstitution.nil⟩
  | cons symbol sourceTail ih =>
      cases symbol with
      | const name =>
          cases derivation with
          | byRule ruleInstance application children =>
              rcases substBodyConst_raw_application_inv application with
                ⟨resultTailPattern, hresult, hpremises⟩
              rw [hpremises] at children
              cases children with
              | cons tailChild remaining =>
                  cases remaining with
                  | nil =>
                      rcases ih resultTailPattern tailChild with
                        ⟨resultTail, hresultTail, tailSemantics⟩
                      refine ⟨.const name :: resultTail, ?_,
                        BodySubstitution.const tailSemantics⟩
                      rw [hresult, hresultTail]
                      rfl
      | var name =>
          cases derivation with
          | byRule ruleInstance application children =>
              rcases substBodyVar_raw_application_inv application with
                ⟨typecodePattern, imagePattern, resultTailPattern,
                  hpremises⟩
              rw [hpremises] at children
              cases children with
              | cons lookupChild remaining =>
                  cases remaining with
                  | cons tailChild remaining =>
                      cases remaining with
                      | cons appendChild remaining =>
                          cases remaining with
                          | nil =>
                              rcases lookup_derivation_decodes substitution name
                                  typecodePattern imagePattern lookupChild with
                                ⟨replacement, binding, htypecode, himage⟩
                              rcases ih resultTailPattern tailChild with
                                ⟨resultTail, hresultTail, tailSemantics⟩
                              rw [himage, hresultTail] at appendChild
                              have hresult :=
                                append_derivation_decodes replacement.body
                                  resultTail resultPattern appendChild
                              exact ⟨replacement.body ++ resultTail, hresult,
                                BodySubstitution.var binding tailSemantics⟩

/-- Every canonical SubstBody derivation reflects the independent body
substitution semantics. -/
theorem substBody_derivation_sound (substitution : FiniteSubstitution)
    (source result : List RuntimeSym)
    (derivation :
      Derivation validatedSidePresentation
        (substBody (encodeSubstitution substitution) (EncodedBody source)
          (EncodedBody result))) :
    BodySubstitution substitution source result := by
  rcases substBody_derivation_decodes substitution source (EncodedBody result)
      derivation with ⟨decodedResult, hencoded, semantics⟩
  have hresult : result = decodedResult := encodedBody_injective hencoded
  subst decodedResult
  exact semantics

/-- SubstBody derivability on canonical encodings is exactly independent
ordinary-list body substitution. -/
theorem substBody_derivation_iff (substitution : FiniteSubstitution)
    (source result : List RuntimeSym) :
    Nonempty
        (Derivation validatedSidePresentation
          (substBody (encodeSubstitution substitution) (EncodedBody source)
            (EncodedBody result))) ↔
      BodySubstitution substitution source result := by
  constructor
  · rintro ⟨derivation⟩
    exact substBody_derivation_sound substitution source result derivation
  · exact substBody_derivable

/-- A body pair outside the independent substitution relation has no
SubstBody derivation. -/
theorem substBody_not_derivable_of_not_semantics
    (substitution : FiniteSubstitution) (source result : List RuntimeSym)
    (hnot : ¬BodySubstitution substitution source result) :
    ¬Nonempty
      (Derivation validatedSidePresentation
        (substBody (encodeSubstitution substitution) (EncodedBody source)
          (EncodedBody result))) := by
  intro derivable
  exact hnot ((substBody_derivation_iff substitution source result).mp derivable)

/-- Formula-level substitution semantics: preserve the source typecode and
substitute only its body. -/
def FormulaSubstitutionSemantics (substitution : FiniteSubstitution)
    (source result : ConstantHeadedFormula) : Prop :=
  source.typecode = result.typecode ∧
    BodySubstitution substitution source.body result.body

private def applySubstFormulaSchema : RuleSchema :=
  { id := ruleId "$mm.apply-subst.formula"
    metavariables :=
      [formal "S", formal "TC", formal "XS", formal "YS"]
    premises :=
      [substBody (metavariable "S") (metavariable "XS")
        (metavariable "YS")]
    conclusion :=
      applySubst (metavariable "S")
        (Builder.formula (metavariable "TC") (metavariable "XS"))
        (Builder.formula (metavariable "TC") (metavariable "YS")) }

@[simp] private theorem applySubstFormulaRule_eq_schema :
    applySubstFormulaRule = applySubstFormulaSchema := by
  rfl

private theorem applySubstRules_filter :
    sideRules.filter (ruleConclusionIs applySubstHead) =
      [applySubstFormulaRule] := by
  rfl

private theorem lookup_applySubstFormulaRule :
    validatedSidePresentation.1.lookupRule?
        (ruleId "$mm.apply-subst.formula") = some applySubstFormulaRule := by
  simp [validatedSidePresentation, sidePresentation, sideRules,
    Presentation.lookupRule?, appendNilSchema, appendConsSchema,
    lookupHereSchema, lookupThereSchema, substBodyNilSchema,
    substBodyConstSchema, substBodyVarSchema, applySubstFormulaSchema, ruleId,
    formal, metavariable]

private theorem applySubstFormula_instantiates
    (substitution : FiniteSubstitution) (typecode : String)
    (sourceBody resultBody : List RuntimeSym) :
    instantiateRule? validatedSidePresentation
        { ruleId := ruleId "$mm.apply-subst.formula"
          arguments :=
            [ encodeSubstitution substitution, encodeString typecode
            , EncodedBody sourceBody, EncodedBody resultBody ] } =
      some
        ( [substBody (encodeSubstitution substitution) (EncodedBody sourceBody)
            (EncodedBody resultBody)]
        , applySubst (encodeSubstitution substitution)
            (encodeFormula ⟨typecode, sourceBody⟩)
            (encodeFormula ⟨typecode, resultBody⟩) ) := by
  simp [instantiateRule?, lookup_applySubstFormulaRule,
    applySubstFormulaRule_eq_schema, applySubstFormulaSchema, formal,
    metavariable, argumentsValidAt, argumentValidAt, instantiateSchemas?,
    instantiateSchemasAt?, instantiateSchema?, instantiateSchemaAt?,
    lookupArgumentAt?, substBody, substBodyHead, applySubst, applySubstHead,
    encodeFormula, EncodedBody]

/-- Formula substitution semantics constructs a derivation of the canonical
ApplySubst judgment. -/
theorem applySubst_derivable {substitution : FiniteSubstitution}
    {source result : ConstantHeadedFormula}
    (semantics : FormulaSubstitutionSemantics substitution source result) :
    Nonempty
      (Derivation validatedSidePresentation
        (applySubst (encodeSubstitution substitution) (encodeFormula source)
          (encodeFormula result))) := by
  rcases source with ⟨sourceTypecode, sourceBody⟩
  rcases result with ⟨resultTypecode, resultBody⟩
  change sourceTypecode = resultTypecode ∧
      BodySubstitution substitution sourceBody resultBody at semantics
  rcases semantics with ⟨htypecode, bodySemantics⟩
  subst resultTypecode
  rcases substBody_derivable bodySemantics with ⟨bodyChild⟩
  let ruleInstance : RuleInstance :=
    { ruleId := ruleId "$mm.apply-subst.formula"
      arguments :=
        [ encodeSubstitution substitution, encodeString sourceTypecode
        , EncodedBody sourceBody, EncodedBody resultBody ] }
  have happlication :
      RuleApplication validatedSidePresentation ruleInstance
        [substBody (encodeSubstitution substitution) (EncodedBody sourceBody)
          (EncodedBody resultBody)]
        (applySubst (encodeSubstitution substitution)
          (encodeFormula ⟨sourceTypecode, sourceBody⟩)
          (encodeFormula ⟨sourceTypecode, resultBody⟩)) :=
    instantiateRule?_eq_some_iff_application.mp
      (applySubstFormula_instantiates substitution sourceTypecode sourceBody
        resultBody)
  exact ⟨Derivation.byRule ruleInstance happlication
    (.cons bodyChild .nil)⟩

private theorem applySubstApplication_decompose
    {ruleInstance : RuleInstance} {premises : List Pattern}
    {substitutionPattern sourcePattern resultPattern : Pattern}
    (application :
      RuleApplication validatedSidePresentation ruleInstance premises
        (applySubst substitutionPattern sourcePattern resultPattern)) :
    ∃ rule : RuleSchema,
      rule = applySubstFormulaRule ∧
      validatedSidePresentation.1.lookupRule? ruleInstance.ruleId = some rule ∧
      argumentsValidAt rule.metavariables ruleInstance.arguments = true ∧
      InstantiatesList rule.metavariables ruleInstance.arguments
        rule.premises premises ∧
      Instantiates rule.metavariables ruleInstance.arguments rule.conclusion
        (applySubst substitutionPattern sourcePattern resultPattern) := by
  cases application with
  | intro rule hlookup harguments hpremises hconclusion =>
      have hvalid := rule_isValidIn_of_lookup validatedSidePresentation hlookup
      have hshape := RuleSchema.conclusion_hasJudgmentShape_of_validIn hvalid
      have hmem : rule ∈ sideRules := by
        change rule ∈ validatedSidePresentation.1.rules
        exact List.mem_of_find?_eq_some hlookup
      have hrule : rule = applySubstFormulaRule := by
        cases hconclusionRule : rule.conclusion with
        | apply sourceHead sourceArgs =>
            rw [hconclusionRule] at hconclusion
            have hhead : sourceHead = applySubstHead := by
              exact InstantiatesAt.apply_head_eq hconclusion
            have hselected : ruleConclusionIs applySubstHead rule = true := by
              simp [ruleConclusionIs, hconclusionRule, hhead]
            have hfiltered :
                rule ∈ sideRules.filter (ruleConclusionIs applySubstHead) :=
              List.mem_filter.mpr ⟨hmem, hselected⟩
            rw [applySubstRules_filter] at hfiltered
            simpa using hfiltered
        | bvar index =>
            rw [hconclusionRule] at hshape
            simp [Presentation.hasJudgmentShape] at hshape
        | fvar name =>
            rw [hconclusionRule] at hshape
            simp [Presentation.hasJudgmentShape] at hshape
        | lambda binder body =>
            rw [hconclusionRule] at hshape
            simp [Presentation.hasJudgmentShape] at hshape
        | multiLambda arity binders body =>
            rw [hconclusionRule] at hshape
            simp [Presentation.hasJudgmentShape] at hshape
        | subst body replacement =>
            rw [hconclusionRule] at hshape
            simp [Presentation.hasJudgmentShape] at hshape
        | collection collectionType elements rest =>
            rw [hconclusionRule] at hshape
            simp [Presentation.hasJudgmentShape] at hshape
      exact ⟨rule, hrule, hlookup, harguments, hpremises, hconclusion⟩

private theorem applySubst_application_inv
    {ruleInstance : RuleInstance} {premises : List Pattern}
    {substitution : FiniteSubstitution}
    {sourceTypecode resultTypecode : String}
    {sourceBody resultBody : List RuntimeSym}
    (application :
      RuleApplication validatedSidePresentation ruleInstance premises
        (applySubst (encodeSubstitution substitution)
          (encodeFormula ⟨sourceTypecode, sourceBody⟩)
          (encodeFormula ⟨resultTypecode, resultBody⟩))) :
    sourceTypecode = resultTypecode ∧
      premises =
        [substBody (encodeSubstitution substitution) (EncodedBody sourceBody)
          (EncodedBody resultBody)] := by
  rcases applySubstApplication_decompose application with
    ⟨rule, rfl, hlookup, harguments, hpremises, hconclusion⟩
  have hlength := argumentsValidAt_length_eq harguments
  rw [applySubstFormulaRule_eq_schema] at hlength
  simp [applySubstFormulaSchema] at hlength
  rcases List.length_eq_four.mp hlength with
    ⟨first, second, third, fourth, hargs⟩
  have hpremises' := instantiateSchemasAt?_complete hpremises
  have hconclusion' := instantiateSchemaAt?_complete hconclusion
  simp [hargs, applySubstFormulaRule_eq_schema, applySubstFormulaSchema,
    formal, metavariable, instantiateSchemasAt?, instantiateSchemaAt?,
    lookupArgumentAt?, substBody, applySubst, encodeFormula]
    at hpremises' hconclusion'
  constructor
  · exact encodeString_injective
      (hconclusion'.2.1.1.symm.trans hconclusion'.2.2.1)
  · simpa [substBody, EncodedBody, hconclusion'.1,
      hconclusion'.2.1.2, hconclusion'.2.2.2] using hpremises'.symm

private theorem applySubst_raw_application_inv
    {ruleInstance : RuleInstance} {premises : List Pattern}
    {substitution : FiniteSubstitution} {sourceTypecode : String}
    {sourceBody : List RuntimeSym} {resultPattern : Pattern}
    (application :
      RuleApplication validatedSidePresentation ruleInstance premises
        (applySubst (encodeSubstitution substitution)
          (encodeFormula ⟨sourceTypecode, sourceBody⟩) resultPattern)) :
    ∃ resultBodyPattern : Pattern,
      resultPattern =
          Builder.formula (encodeString sourceTypecode) resultBodyPattern ∧
      premises =
        [substBody (encodeSubstitution substitution) (EncodedBody sourceBody)
          resultBodyPattern] := by
  rcases applySubstApplication_decompose application with
    ⟨rule, rfl, hlookup, harguments, hpremises, hconclusion⟩
  have hlength := argumentsValidAt_length_eq harguments
  rw [applySubstFormulaRule_eq_schema] at hlength
  simp [applySubstFormulaSchema] at hlength
  rcases List.length_eq_four.mp hlength with
    ⟨first, second, third, fourth, hargs⟩
  have hpremises' := instantiateSchemasAt?_complete hpremises
  have hconclusion' := instantiateSchemaAt?_complete hconclusion
  simp [hargs, applySubstFormulaRule_eq_schema, applySubstFormulaSchema,
    formal, metavariable, instantiateSchemasAt?, instantiateSchemaAt?,
    lookupArgumentAt?, substBody, applySubst, encodeFormula]
    at hpremises' hconclusion'
  refine ⟨fourth, ?_, ?_⟩
  · exact hconclusion'.2.2.symm.trans
      (congrArg (fun value => Builder.formula value fourth)
        hconclusion'.2.1.1)
  · simpa [substBody, EncodedBody, hconclusion'.1,
      hconclusion'.2.1.2] using hpremises'.symm

/-- An ApplySubst derivation whose result argument was not assumed canonical
forces that argument to decode as a constant-headed formula satisfying the
independent formula-substitution semantics. -/
theorem applySubst_derivation_decodes (substitution : FiniteSubstitution)
    (source : ConstantHeadedFormula) (resultPattern : Pattern)
    (derivation :
      Derivation validatedSidePresentation
        (applySubst (encodeSubstitution substitution) (encodeFormula source)
          resultPattern)) :
    ∃ result : ConstantHeadedFormula,
      resultPattern = encodeFormula result ∧
      FormulaSubstitutionSemantics substitution source result := by
  rcases source with ⟨sourceTypecode, sourceBody⟩
  cases derivation with
  | byRule ruleInstance application children =>
      rcases applySubst_raw_application_inv application with
        ⟨resultBodyPattern, hresult, hpremises⟩
      rw [hpremises] at children
      cases children with
      | cons bodyChild remaining =>
          cases remaining with
          | nil =>
              rcases substBody_derivation_decodes substitution sourceBody
                  resultBodyPattern bodyChild with
                ⟨resultBody, hresultBody, bodySemantics⟩
              refine ⟨⟨sourceTypecode, resultBody⟩, ?_, ?_⟩
              · rw [hresult, hresultBody]
                rfl
              · exact ⟨rfl, bodySemantics⟩

/-- A result pattern outside the image of the formula encoder cannot be the
result of an ApplySubst derivation. -/
theorem applySubst_not_derivable_of_result_not_encoded
    (substitution : FiniteSubstitution) (source : ConstantHeadedFormula)
    (resultPattern : Pattern)
    (hnotEncoded :
      ∀ result : ConstantHeadedFormula,
        resultPattern ≠ encodeFormula result) :
    ¬Nonempty
      (Derivation validatedSidePresentation
        (applySubst (encodeSubstitution substitution) (encodeFormula source)
          resultPattern)) := by
  rintro ⟨derivation⟩
  rcases applySubst_derivation_decodes substitution source resultPattern
      derivation with ⟨result, hresult, semantics⟩
  exact hnotEncoded result hresult

/-- The list nil constructor is a concrete malformed ApplySubst result: the
rule can only produce the structural formula constructor. -/
theorem applySubst_nil_result_not_derivable
    (substitution : FiniteSubstitution) (source : ConstantHeadedFormula) :
    ¬Nonempty
      (Derivation validatedSidePresentation
        (applySubst (encodeSubstitution substitution) (encodeFormula source)
          Builder.nil)) := by
  apply applySubst_not_derivable_of_result_not_encoded
  intro result hresult
  rcases result with ⟨typecode, body⟩
  simp [encodeFormula, Builder.nil, Builder.formula] at hresult

/-- A singleton substitution actively replaces a variable while preserving a
preceding constant and the source typecode. -/
theorem applySubst_const_then_single_variable_derivable
    (typecode constantName variableName : String)
    (replacement : ConstantHeadedFormula) :
    Nonempty
      (Derivation validatedSidePresentation
        (applySubst
          (encodeSubstitution
            [{ variableName := variableName, replacement := replacement }])
          (encodeFormula
            ⟨typecode, [.const constantName, .var variableName]⟩)
          (encodeFormula
            ⟨typecode, .const constantName :: replacement.body⟩))) := by
  apply applySubst_derivable
  have binding :
      LookupSemantics
        [{ variableName := variableName, replacement := replacement }]
        variableName replacement := by
    simp [LookupSemantics]
  have tail :
      BodySubstitution
        [{ variableName := variableName, replacement := replacement }]
        [] [] := BodySubstitution.nil
  have variableSemantics := BodySubstitution.var binding tail
  have bodySemantics :
      BodySubstitution
        [{ variableName := variableName, replacement := replacement }]
        [.const constantName, .var variableName]
        (.const constantName :: (replacement.body ++ [])) :=
    BodySubstitution.const (name := constantName) variableSemantics
  exact ⟨rfl, by simpa using bodySemantics⟩

/-- Every canonical ApplySubst derivation reflects formula-level
substitution semantics. -/
theorem applySubst_derivation_sound (substitution : FiniteSubstitution)
    (source result : ConstantHeadedFormula)
    (derivation :
      Derivation validatedSidePresentation
        (applySubst (encodeSubstitution substitution) (encodeFormula source)
          (encodeFormula result))) :
    FormulaSubstitutionSemantics substitution source result := by
  rcases source with ⟨sourceTypecode, sourceBody⟩
  rcases result with ⟨resultTypecode, resultBody⟩
  cases derivation with
  | byRule ruleInstance application children =>
      rcases applySubst_application_inv application with
        ⟨htypecode, hpremises⟩
      rw [hpremises] at children
      cases children with
      | cons bodyChild remaining =>
          cases remaining with
          | nil =>
              exact ⟨htypecode,
                substBody_derivation_sound substitution sourceBody resultBody
                  bodyChild⟩

/-- ApplySubst derivability on canonical formulas is exactly independent
formula substitution. -/
theorem applySubst_derivation_iff (substitution : FiniteSubstitution)
    (source result : ConstantHeadedFormula) :
    Nonempty
        (Derivation validatedSidePresentation
          (applySubst (encodeSubstitution substitution) (encodeFormula source)
            (encodeFormula result))) ↔
      FormulaSubstitutionSemantics substitution source result := by
  constructor
  · rintro ⟨derivation⟩
    exact applySubst_derivation_sound substitution source result derivation
  · exact applySubst_derivable

/-- A formula pair outside the independent substitution relation has no
ApplySubst derivation. -/
theorem applySubst_not_derivable_of_not_semantics
    (substitution : FiniteSubstitution)
    (source result : ConstantHeadedFormula)
    (hnot : ¬FormulaSubstitutionSemantics substitution source result) :
    ¬Nonempty
      (Derivation validatedSidePresentation
        (applySubst (encodeSubstitution substitution) (encodeFormula source)
          (encodeFormula result))) := by
  intro derivable
  exact hnot ((applySubst_derivation_iff substitution source result).mp derivable)

/-- Unique substitution keys make body substitution functional. -/
theorem bodySubstitution_functional
    {substitution : FiniteSubstitution}
    (hunique : SubstitutionKeysUnique substitution)
    {source first second : List RuntimeSym}
    (hfirst : BodySubstitution substitution source first)
    (hsecond : BodySubstitution substitution source second) :
    first = second := by
  induction hfirst generalizing second with
  | nil =>
      cases hsecond
      rfl
  | const firstTail ih =>
      cases hsecond with
      | const secondTail =>
          exact congrArg (List.cons (.const _)) (ih secondTail)
  | @var name firstReplacement sourceTail firstTail firstBinding firstSemantics ih =>
      cases hsecond with
      | @var _ secondReplacement _ secondTail secondBinding secondSemantics =>
          have hreplacement : firstReplacement = secondReplacement :=
            lookupSemantics_functional hunique firstBinding secondBinding
          subst secondReplacement
          exact congrArg (List.append firstReplacement.body)
            (ih secondSemantics)

/-- Under unique keys, formula substitution has at most one result. -/
theorem formulaSubstitutionSemantics_functional
    {substitution : FiniteSubstitution}
    (hunique : SubstitutionKeysUnique substitution)
    {source first second : ConstantHeadedFormula}
    (hfirst : FormulaSubstitutionSemantics substitution source first)
    (hsecond : FormulaSubstitutionSemantics substitution source second) :
    first = second := by
  rcases source with ⟨sourceTypecode, sourceBody⟩
  rcases first with ⟨firstTypecode, firstBody⟩
  rcases second with ⟨secondTypecode, secondBody⟩
  change sourceTypecode = firstTypecode ∧
      BodySubstitution substitution sourceBody firstBody at hfirst
  change sourceTypecode = secondTypecode ∧
      BodySubstitution substitution sourceBody secondBody at hsecond
  have htypecode : firstTypecode = secondTypecode :=
    hfirst.1.symm.trans hsecond.1
  have hbody : firstBody = secondBody :=
    bodySubstitution_functional hunique hfirst.2 hsecond.2
  subst secondTypecode
  subst secondBody
  rfl

/-- Under unique keys, two ApplySubst derivations from one formula have the
same canonical result. -/
theorem applySubst_derivation_functional
    {substitution : FiniteSubstitution}
    (hunique : SubstitutionKeysUnique substitution)
    {source first second : ConstantHeadedFormula}
    (hfirst :
      Nonempty
        (Derivation validatedSidePresentation
          (applySubst (encodeSubstitution substitution) (encodeFormula source)
            (encodeFormula first))))
    (hsecond :
      Nonempty
        (Derivation validatedSidePresentation
          (applySubst (encodeSubstitution substitution) (encodeFormula source)
            (encodeFormula second)))) :
    first = second :=
  formulaSubstitutionSemantics_functional hunique
    ((applySubst_derivation_iff substitution source first).mp hfirst)
    ((applySubst_derivation_iff substitution source second).mp hsecond)

/-- The source-level variable extractor used by Vars is the live Metamath
runtime's `Formula.varsList` on the corresponding constant-headed formula. -/
theorem bodyVariables_eq_runtime_varsList
    (formula : ConstantHeadedFormula) :
    BodyVariables formula.body = formula.toRuntime.varsList := by
  rcases formula with ⟨typecode, body⟩
  induction body with
  | nil =>
      simp [ConstantHeadedFormula.toRuntime,
        Metamath.Verify.Formula.varsList, BodyVariables]
  | cons symbol body ih =>
      cases symbol with
      | const name =>
          simp [ConstantHeadedFormula.toRuntime,
            Metamath.Verify.Formula.varsList, BodyVariables] at ih ⊢
          exact ih
      | var name =>
          simp [ConstantHeadedFormula.toRuntime,
            Metamath.Verify.Formula.varsList, BodyVariables] at ih ⊢
          exact ih

/-! ## Disjoint-variable conditions -/

private abbrev EncodedDVPairs (pairs : List (String × String)) : Pattern :=
  encodeListWith encodeDVPair pairs

/-- Symmetric membership semantics generated by the two DVRel rules.  The
separate source-validity layer rules out self-pairs. -/
def DVRelation (pairs : List (String × String)) (left right : String) : Prop :=
  (left, right) ∈ pairs ∨ (right, left) ∈ pairs

/-- Every name in `rights` is related to `left`. -/
def AllWithSemantics (pairs : List (String × String)) (left : String)
    (rights : List String) : Prop :=
  ∀ right ∈ rights, DVRelation pairs left right

/-- Every cross-product pair from two name lists is DV-related. -/
def AllPairsSemantics (pairs : List (String × String))
    (lefts rights : List String) : Prop :=
  ∀ left ∈ lefts, ∀ right ∈ rights, DVRelation pairs left right

/-- Ordinary finite-substitution semantics of the generated DV-list check.
Each callee pair chooses matching bindings from the relational substitution,
extracts their ordered variable occurrences, and requires the full cross
product to occur in the caller DV relation. -/
def DVListsSemantics (substitution : FiniteSubstitution)
    (callerDV calleeDV : List (String × String)) : Prop :=
  ∀ pair ∈ calleeDV,
    ∃ leftReplacement rightReplacement : ConstantHeadedFormula,
      LookupSemantics substitution pair.1 leftReplacement ∧
      LookupSemantics substitution pair.2 rightReplacement ∧
      AllPairsSemantics callerDV
        (BodyVariables leftReplacement.body)
        (BodyVariables rightReplacement.body)

/-- Frame-level semantics of DVOK.  Hypothesis labels are intentionally
irrelevant because the generated wrapper rule passes only the two DV lists to
its premise. -/
def DVOKSemantics (substitution : FiniteSubstitution)
    (callerFrame calleeFrame : RuntimeFrame) : Prop :=
  DVListsSemantics substitution callerFrame.dj.toList calleeFrame.dj.toList

private def memberHereSchema : RuleSchema :=
  { id := ruleId "$mm.member.here"
    metavariables := [formal "X", formal "XS"]
    premises := []
    conclusion :=
      member (metavariable "X")
        (Builder.cons (metavariable "X") (metavariable "XS")) }

private def memberThereSchema : RuleSchema :=
  { id := ruleId "$mm.member.there"
    metavariables := [formal "X", formal "Y", formal "YS"]
    premises := [member (metavariable "X") (metavariable "YS")]
    conclusion :=
      member (metavariable "X")
        (Builder.cons (metavariable "Y") (metavariable "YS")) }

private def dvRelForwardSchema : RuleSchema :=
  { id := ruleId "$mm.dv-rel.forward"
    metavariables := [formal "D", formal "X", formal "Y"]
    premises :=
      [member (Builder.dvPair (metavariable "X") (metavariable "Y"))
        (metavariable "D")]
    conclusion :=
      dvRel (metavariable "D") (metavariable "X") (metavariable "Y") }

private def dvRelReverseSchema : RuleSchema :=
  { id := ruleId "$mm.dv-rel.reverse"
    metavariables := [formal "D", formal "X", formal "Y"]
    premises :=
      [member (Builder.dvPair (metavariable "Y") (metavariable "X"))
        (metavariable "D")]
    conclusion :=
      dvRel (metavariable "D") (metavariable "X") (metavariable "Y") }

private def allWithNilSchema : RuleSchema :=
  { id := ruleId "$mm.all-with.nil"
    metavariables := [formal "D", formal "X"]
    premises := []
    conclusion :=
      allWith (metavariable "D") (metavariable "X") Builder.nil }

private def allWithConsSchema : RuleSchema :=
  { id := ruleId "$mm.all-with.cons"
    metavariables :=
      [formal "D", formal "X", formal "Y", formal "YS"]
    premises :=
      [ dvRel (metavariable "D") (metavariable "X") (metavariable "Y")
      , allWith (metavariable "D") (metavariable "X")
          (metavariable "YS") ]
    conclusion :=
      allWith (metavariable "D") (metavariable "X")
        (Builder.cons (metavariable "Y") (metavariable "YS")) }

private def allPairsNilSchema : RuleSchema :=
  { id := ruleId "$mm.all-pairs.nil"
    metavariables := [formal "D", formal "YS"]
    premises := []
    conclusion :=
      allPairs (metavariable "D") Builder.nil (metavariable "YS") }

private def allPairsConsSchema : RuleSchema :=
  { id := ruleId "$mm.all-pairs.cons"
    metavariables :=
      [formal "D", formal "X", formal "XS", formal "YS"]
    premises :=
      [ allWith (metavariable "D") (metavariable "X")
          (metavariable "YS")
      , allPairs (metavariable "D") (metavariable "XS")
          (metavariable "YS") ]
    conclusion :=
      allPairs (metavariable "D")
        (Builder.cons (metavariable "X") (metavariable "XS"))
        (metavariable "YS") }

private def dvListsNilSchema : RuleSchema :=
  { id := ruleId "$mm.dv-lists.nil"
    metavariables := [formal "S", formal "CallerDV"]
    premises := []
    conclusion :=
      dvLists (metavariable "S") (metavariable "CallerDV") Builder.nil }

private def dvListsConsSchema : RuleSchema :=
  { id := ruleId "$mm.dv-lists.cons"
    metavariables :=
      [ formal "S", formal "CallerDV", formal "V", formal "W"
      , formal "Rest", formal "TC1", formal "B1", formal "TC2"
      , formal "B2", formal "VS1", formal "VS2" ]
    premises :=
      [ lookup (metavariable "S") (metavariable "V")
          (metavariable "TC1") (metavariable "B1")
      , lookup (metavariable "S") (metavariable "W")
          (metavariable "TC2") (metavariable "B2")
      , vars (metavariable "B1") (metavariable "VS1")
      , vars (metavariable "B2") (metavariable "VS2")
      , allPairs (metavariable "CallerDV") (metavariable "VS1")
          (metavariable "VS2")
      , dvLists (metavariable "S") (metavariable "CallerDV")
          (metavariable "Rest") ]
    conclusion :=
      dvLists (metavariable "S") (metavariable "CallerDV")
        (Builder.cons
          (Builder.dvPair (metavariable "V") (metavariable "W"))
          (metavariable "Rest")) }

private def dvOKSchema : RuleSchema :=
  { id := ruleId "$mm.dv-ok.frames"
    metavariables :=
      [ formal "S", formal "CallerDV", formal "CallerHyps"
      , formal "CalleeDV", formal "CalleeHyps" ]
    premises :=
      [dvLists (metavariable "S") (metavariable "CallerDV")
        (metavariable "CalleeDV")]
    conclusion :=
      dvOK (metavariable "S")
        (Builder.frame (metavariable "CallerDV")
          (metavariable "CallerHyps"))
        (Builder.frame (metavariable "CalleeDV")
          (metavariable "CalleeHyps")) }

@[simp] private theorem memberHereRule_eq_schema :
    memberHereRule = memberHereSchema := by rfl

@[simp] private theorem memberThereRule_eq_schema :
    memberThereRule = memberThereSchema := by rfl

@[simp] private theorem dvRelForwardRule_eq_schema :
    dvRelForwardRule = dvRelForwardSchema := by rfl

@[simp] private theorem dvRelReverseRule_eq_schema :
    dvRelReverseRule = dvRelReverseSchema := by rfl

@[simp] private theorem allWithNilRule_eq_schema :
    allWithNilRule = allWithNilSchema := by rfl

@[simp] private theorem allWithConsRule_eq_schema :
    allWithConsRule = allWithConsSchema := by rfl

@[simp] private theorem allPairsNilRule_eq_schema :
    allPairsNilRule = allPairsNilSchema := by rfl

@[simp] private theorem allPairsConsRule_eq_schema :
    allPairsConsRule = allPairsConsSchema := by rfl

@[simp] private theorem dvListsNilRule_eq_schema :
    dvListsNilRule = dvListsNilSchema := by rfl

@[simp] private theorem dvListsConsRule_eq_schema :
    dvListsConsRule = dvListsConsSchema := by rfl

@[simp] private theorem dvOKRule_eq_schema :
    dvOKRule = dvOKSchema := by rfl

private theorem memberRules_filter :
    sideRules.filter (ruleConclusionIs memberHead) =
      [memberHereRule, memberThereRule] := by rfl

private theorem dvRelRules_filter :
    sideRules.filter (ruleConclusionIs dvRelHead) =
      [dvRelForwardRule, dvRelReverseRule] := by rfl

private theorem allWithRules_filter :
    sideRules.filter (ruleConclusionIs allWithHead) =
      [allWithNilRule, allWithConsRule] := by rfl

private theorem allPairsRules_filter :
    sideRules.filter (ruleConclusionIs allPairsHead) =
      [allPairsNilRule, allPairsConsRule] := by rfl

private theorem dvListsRules_filter :
    sideRules.filter (ruleConclusionIs dvListsHead) =
      [dvListsNilRule, dvListsConsRule] := by rfl

private theorem dvOKRules_filter :
    sideRules.filter (ruleConclusionIs dvOKHead) = [dvOKRule] := by rfl

private theorem lookup_memberHereRule :
    validatedSidePresentation.1.lookupRule? (ruleId "$mm.member.here") =
      some memberHereRule := by
  rfl

private theorem lookup_memberThereRule :
    validatedSidePresentation.1.lookupRule? (ruleId "$mm.member.there") =
      some memberThereRule := by rfl

private theorem lookup_dvRelForwardRule :
    validatedSidePresentation.1.lookupRule? (ruleId "$mm.dv-rel.forward") =
      some dvRelForwardRule := by rfl

private theorem lookup_dvRelReverseRule :
    validatedSidePresentation.1.lookupRule? (ruleId "$mm.dv-rel.reverse") =
      some dvRelReverseRule := by rfl

private theorem lookup_allWithNilRule :
    validatedSidePresentation.1.lookupRule? (ruleId "$mm.all-with.nil") =
      some allWithNilRule := by rfl

private theorem lookup_allWithConsRule :
    validatedSidePresentation.1.lookupRule? (ruleId "$mm.all-with.cons") =
      some allWithConsRule := by rfl

private theorem lookup_allPairsNilRule :
    validatedSidePresentation.1.lookupRule? (ruleId "$mm.all-pairs.nil") =
      some allPairsNilRule := by rfl

private theorem lookup_allPairsConsRule :
    validatedSidePresentation.1.lookupRule? (ruleId "$mm.all-pairs.cons") =
      some allPairsConsRule := by rfl

private theorem lookup_dvListsNilRule :
    validatedSidePresentation.1.lookupRule? (ruleId "$mm.dv-lists.nil") =
      some dvListsNilRule := by rfl

private theorem lookup_dvListsConsRule :
    validatedSidePresentation.1.lookupRule? (ruleId "$mm.dv-lists.cons") =
      some dvListsConsRule := by rfl

private theorem lookup_dvOKRule :
    validatedSidePresentation.1.lookupRule? (ruleId "$mm.dv-ok.frames") =
      some dvOKRule := by rfl

@[simp] private theorem encodeDVPair_isGroundAt (depth : Nat)
    (pair : String × String) :
    (encodeDVPair pair).isGroundAt depth = true := by
  rcases pair with ⟨left, right⟩
  simp [encodeDVPair, Builder.dvPair, Pattern.isGroundAt,
    Pattern.isGroundListAt]

@[simp] private theorem encodeDVPair_hasCanonicalBinderMetadata
    (pair : String × String) :
    (encodeDVPair pair).hasCanonicalBinderMetadata = true := by
  rcases pair with ⟨left, right⟩
  simp [encodeDVPair, Builder.dvPair,
    Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList]

@[simp] private theorem encodedDVPairs_isGroundAt (depth : Nat)
    (pairs : List (String × String)) :
    (EncodedDVPairs pairs).isGroundAt depth = true := by
  induction pairs with
  | nil =>
      simp [EncodedDVPairs, encodeListWith, Pattern.isGroundAt,
        Pattern.isGroundListAt]
  | cons pair pairs ih =>
      simp [EncodedDVPairs, encodeListWith, Pattern.isGroundAt,
        Pattern.isGroundListAt, ih]

@[simp] private theorem encodedDVPairs_hasCanonicalBinderMetadata
    (pairs : List (String × String)) :
    (EncodedDVPairs pairs).hasCanonicalBinderMetadata = true := by
  induction pairs with
  | nil =>
      simp [EncodedDVPairs, encodeListWith,
        Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList]
  | cons pair pairs ih =>
      simp [EncodedDVPairs, encodeListWith,
        Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList, ih]

private theorem encodedDVPairs_injective :
    Function.Injective EncodedDVPairs := by
  intro left right hencoded
  have hdecoded := congrArg (decodeListWith decodeDVPair) hencoded
  simpa using hdecoded

private theorem memberHere_instantiates (target : String × String)
    (rest : List (String × String)) :
    instantiateRule? validatedSidePresentation
        { ruleId := ruleId "$mm.member.here"
          arguments := [encodeDVPair target, EncodedDVPairs rest] } =
      some
        ([], member (encodeDVPair target) (EncodedDVPairs (target :: rest))) := by
  simp [instantiateRule?, lookup_memberHereRule, memberHereRule_eq_schema,
    memberHereSchema, formal, metavariable, argumentsValidAt,
    argumentValidAt, instantiateSchemas?, instantiateSchemasAt?,
    instantiateSchema?, instantiateSchemaAt?, lookupArgumentAt?, member,
    memberHead, EncodedDVPairs, encodeListWith]

private theorem memberThere_instantiates (target head : String × String)
    (rest : List (String × String)) :
    instantiateRule? validatedSidePresentation
        { ruleId := ruleId "$mm.member.there"
          arguments :=
            [encodeDVPair target, encodeDVPair head, EncodedDVPairs rest] } =
      some
        ( [member (encodeDVPair target) (EncodedDVPairs rest)]
        , member (encodeDVPair target) (EncodedDVPairs (head :: rest)) ) := by
  simp [instantiateRule?, lookup_memberThereRule, memberThereRule_eq_schema,
    memberThereSchema, formal, metavariable, argumentsValidAt,
    argumentValidAt, instantiateSchemas?, instantiateSchemasAt?,
    instantiateSchema?, instantiateSchemaAt?, lookupArgumentAt?, member,
    memberHead, EncodedDVPairs, encodeListWith]

private theorem member_pair_derivable_of_mem
    (target : String × String) (pairs : List (String × String))
    (hmem : target ∈ pairs) :
    Nonempty
      (Derivation validatedSidePresentation
        (member (encodeDVPair target) (EncodedDVPairs pairs))) := by
  induction pairs with
  | nil => simp at hmem
  | cons head rest ih =>
      by_cases hhead : head = target
      · subst head
        let ruleInstance : RuleInstance :=
          { ruleId := ruleId "$mm.member.here"
            arguments := [encodeDVPair target, EncodedDVPairs rest] }
        have happlication :
            RuleApplication validatedSidePresentation ruleInstance []
              (member (encodeDVPair target)
                (EncodedDVPairs (target :: rest))) :=
          instantiateRule?_eq_some_iff_application.mp
            (memberHere_instantiates target rest)
        exact ⟨Derivation.byRule ruleInstance happlication .nil⟩
      · have htail : target ∈ rest := by
          have htarget : target ≠ head := fun h => hhead h.symm
          simpa [htarget] using hmem
        rcases ih htail with ⟨child⟩
        let ruleInstance : RuleInstance :=
          { ruleId := ruleId "$mm.member.there"
            arguments :=
              [encodeDVPair target, encodeDVPair head, EncodedDVPairs rest] }
        have happlication :
            RuleApplication validatedSidePresentation ruleInstance
              [member (encodeDVPair target) (EncodedDVPairs rest)]
              (member (encodeDVPair target)
                (EncodedDVPairs (head :: rest))) :=
          instantiateRule?_eq_some_iff_application.mp
            (memberThere_instantiates target head rest)
        exact ⟨Derivation.byRule ruleInstance happlication
          (.cons child .nil)⟩

private theorem memberApplication_decompose
    {ruleInstance : RuleInstance} {premises : List Pattern}
    {valuePattern valuesPattern : Pattern}
    (application :
      RuleApplication validatedSidePresentation ruleInstance premises
        (member valuePattern valuesPattern)) :
    ∃ rule : RuleSchema,
      (rule = memberHereRule ∨ rule = memberThereRule) ∧
      validatedSidePresentation.1.lookupRule? ruleInstance.ruleId = some rule ∧
      argumentsValidAt rule.metavariables ruleInstance.arguments = true ∧
      InstantiatesList rule.metavariables ruleInstance.arguments
        rule.premises premises ∧
      Instantiates rule.metavariables ruleInstance.arguments rule.conclusion
        (member valuePattern valuesPattern) := by
  cases application with
  | intro rule hlookup harguments hpremises hconclusion =>
      have hvalid := rule_isValidIn_of_lookup validatedSidePresentation hlookup
      have hshape := RuleSchema.conclusion_hasJudgmentShape_of_validIn hvalid
      have hmem : rule ∈ sideRules := by
        change rule ∈ validatedSidePresentation.1.rules
        exact List.mem_of_find?_eq_some hlookup
      have hrule : rule = memberHereRule ∨ rule = memberThereRule := by
        cases hconclusionRule : rule.conclusion with
        | apply sourceHead sourceArgs =>
            rw [hconclusionRule] at hconclusion
            have hhead : sourceHead = memberHead :=
              InstantiatesAt.apply_head_eq hconclusion
            have hselected : ruleConclusionIs memberHead rule = true := by
              simp [ruleConclusionIs, hconclusionRule, hhead]
            have hfiltered :
                rule ∈ sideRules.filter (ruleConclusionIs memberHead) :=
              List.mem_filter.mpr ⟨hmem, hselected⟩
            rw [memberRules_filter] at hfiltered
            simpa using hfiltered
        | bvar index =>
            rw [hconclusionRule] at hshape
            simp [Presentation.hasJudgmentShape] at hshape
        | fvar name =>
            rw [hconclusionRule] at hshape
            simp [Presentation.hasJudgmentShape] at hshape
        | lambda binder body =>
            rw [hconclusionRule] at hshape
            simp [Presentation.hasJudgmentShape] at hshape
        | multiLambda arity binders body =>
            rw [hconclusionRule] at hshape
            simp [Presentation.hasJudgmentShape] at hshape
        | subst body replacement =>
            rw [hconclusionRule] at hshape
            simp [Presentation.hasJudgmentShape] at hshape
        | collection collectionType elements rest =>
            rw [hconclusionRule] at hshape
            simp [Presentation.hasJudgmentShape] at hshape
      exact ⟨rule, hrule, hlookup, harguments, hpremises, hconclusion⟩

private theorem memberNil_application_false
    {ruleInstance : RuleInstance} {premises : List Pattern}
    {target : String × String}
    (application :
      RuleApplication validatedSidePresentation ruleInstance premises
        (member (encodeDVPair target) (EncodedDVPairs []))) : False := by
  rcases memberApplication_decompose application with
    ⟨rule, hrule, hlookup, harguments, hpremises, hconclusion⟩
  rcases hrule with rfl | rfl
  · have hlength := argumentsValidAt_length_eq harguments
    rw [memberHereRule_eq_schema] at hlength
    simp [memberHereSchema] at hlength
    rcases List.length_eq_two.mp hlength with ⟨first, second, hargs⟩
    have hconclusion' := instantiateSchemaAt?_complete hconclusion
    simp [hargs, memberHereRule_eq_schema, memberHereSchema, formal,
      metavariable, instantiateSchemaAt?, instantiateSchemasAt?,
      lookupArgumentAt?, member, EncodedDVPairs, encodeListWith]
      at hconclusion'
  · have hlength := argumentsValidAt_length_eq harguments
    rw [memberThereRule_eq_schema] at hlength
    simp [memberThereSchema] at hlength
    rcases List.length_eq_three.mp hlength with
      ⟨first, second, third, hargs⟩
    have hconclusion' := instantiateSchemaAt?_complete hconclusion
    simp [hargs, memberThereRule_eq_schema, memberThereSchema, formal,
      metavariable, instantiateSchemaAt?, instantiateSchemasAt?,
      lookupArgumentAt?, member, EncodedDVPairs, encodeListWith]
      at hconclusion'

private theorem memberCons_application_inv
    {ruleInstance : RuleInstance} {premises : List Pattern}
    {target head : String × String} {rest : List (String × String)}
    (application :
      RuleApplication validatedSidePresentation ruleInstance premises
        (member (encodeDVPair target) (EncodedDVPairs (head :: rest)))) :
    (head = target ∧ premises = []) ∨
      premises = [member (encodeDVPair target) (EncodedDVPairs rest)] := by
  rcases memberApplication_decompose application with
    ⟨rule, hrule, hlookup, harguments, hpremises, hconclusion⟩
  rcases hrule with rfl | rfl
  · have hlength := argumentsValidAt_length_eq harguments
    rw [memberHereRule_eq_schema] at hlength
    simp [memberHereSchema] at hlength
    rcases List.length_eq_two.mp hlength with ⟨first, second, hargs⟩
    have hpremises' := instantiateSchemasAt?_complete hpremises
    have hconclusion' := instantiateSchemaAt?_complete hconclusion
    simp [hargs, memberHereRule_eq_schema, memberHereSchema, formal,
      metavariable, instantiateSchemasAt?, instantiateSchemaAt?,
      lookupArgumentAt?, member, EncodedDVPairs, encodeListWith]
      at hpremises' hconclusion'
    left
    refine ⟨?_, hpremises'⟩
    exact encodeDVPair_injective
      (hconclusion'.1.symm.trans hconclusion'.2.1).symm
  · have hlength := argumentsValidAt_length_eq harguments
    rw [memberThereRule_eq_schema] at hlength
    simp [memberThereSchema] at hlength
    rcases List.length_eq_three.mp hlength with
      ⟨first, second, third, hargs⟩
    have hpremises' := instantiateSchemasAt?_complete hpremises
    have hconclusion' := instantiateSchemaAt?_complete hconclusion
    simp [hargs, memberThereRule_eq_schema, memberThereSchema, formal,
      metavariable, instantiateSchemasAt?, instantiateSchemaAt?,
      lookupArgumentAt?, member, EncodedDVPairs, encodeListWith]
      at hpremises' hconclusion'
    right
    simpa [member, EncodedDVPairs, hconclusion'.1,
      hconclusion'.2.2] using hpremises'.symm

private theorem member_pair_derivation_sound
    (target : String × String) (pairs : List (String × String))
    (derivation :
      Derivation validatedSidePresentation
        (member (encodeDVPair target) (EncodedDVPairs pairs))) :
    target ∈ pairs := by
  induction pairs with
  | nil =>
      cases derivation with
      | byRule ruleInstance application children =>
          exact False.elim (memberNil_application_false application)
  | cons head rest ih =>
      cases derivation with
      | byRule ruleInstance application children =>
          rcases memberCons_application_inv application with hhere | hthere
          · simp [hhere.1]
          · rw [hthere] at children
            cases children with
            | cons child remaining =>
                cases remaining with
                | nil => exact List.mem_cons_of_mem head (ih child)

/-- Member derivability for canonical DV-pair lists is exactly ordinary list
membership. -/
theorem member_pair_derivation_iff (target : String × String)
    (pairs : List (String × String)) :
    Nonempty
        (Derivation validatedSidePresentation
          (member (encodeDVPair target) (EncodedDVPairs pairs))) ↔
      target ∈ pairs := by
  constructor
  · rintro ⟨derivation⟩
    exact member_pair_derivation_sound target pairs derivation
  · exact member_pair_derivable_of_mem target pairs

private theorem dvRelForward_instantiates
    (pairs : List (String × String)) (left right : String) :
    instantiateRule? validatedSidePresentation
        { ruleId := ruleId "$mm.dv-rel.forward"
          arguments :=
            [EncodedDVPairs pairs, encodeString left, encodeString right] } =
      some
        ( [member (encodeDVPair (left, right)) (EncodedDVPairs pairs)]
        , dvRel (EncodedDVPairs pairs) (encodeString left)
            (encodeString right) ) := by
  simp [instantiateRule?, lookup_dvRelForwardRule,
    dvRelForwardRule_eq_schema, dvRelForwardSchema, formal, metavariable,
    argumentsValidAt, argumentValidAt, instantiateSchemas?,
    instantiateSchemasAt?, instantiateSchema?, instantiateSchemaAt?,
    lookupArgumentAt?, member, memberHead, dvRel, dvRelHead, encodeDVPair]

private theorem dvRelReverse_instantiates
    (pairs : List (String × String)) (left right : String) :
    instantiateRule? validatedSidePresentation
        { ruleId := ruleId "$mm.dv-rel.reverse"
          arguments :=
            [EncodedDVPairs pairs, encodeString left, encodeString right] } =
      some
        ( [member (encodeDVPair (right, left)) (EncodedDVPairs pairs)]
        , dvRel (EncodedDVPairs pairs) (encodeString left)
            (encodeString right) ) := by
  simp [instantiateRule?, lookup_dvRelReverseRule,
    dvRelReverseRule_eq_schema, dvRelReverseSchema, formal, metavariable,
    argumentsValidAt, argumentValidAt, instantiateSchemas?,
    instantiateSchemasAt?, instantiateSchema?, instantiateSchemaAt?,
    lookupArgumentAt?, member, memberHead, dvRel, dvRelHead, encodeDVPair]

private theorem dvRel_derivable (pairs : List (String × String))
    (left right : String) (semantics : DVRelation pairs left right) :
    Nonempty
      (Derivation validatedSidePresentation
        (dvRel (EncodedDVPairs pairs) (encodeString left)
          (encodeString right))) := by
  rcases semantics with hforward | hreverse
  · rcases member_pair_derivable_of_mem (left, right) pairs hforward with
      ⟨child⟩
    let ruleInstance : RuleInstance :=
      { ruleId := ruleId "$mm.dv-rel.forward"
        arguments :=
          [EncodedDVPairs pairs, encodeString left, encodeString right] }
    have happlication :
        RuleApplication validatedSidePresentation ruleInstance
          [member (encodeDVPair (left, right)) (EncodedDVPairs pairs)]
          (dvRel (EncodedDVPairs pairs) (encodeString left)
            (encodeString right)) :=
      instantiateRule?_eq_some_iff_application.mp
        (dvRelForward_instantiates pairs left right)
    exact ⟨Derivation.byRule ruleInstance happlication (.cons child .nil)⟩
  · rcases member_pair_derivable_of_mem (right, left) pairs hreverse with
      ⟨child⟩
    let ruleInstance : RuleInstance :=
      { ruleId := ruleId "$mm.dv-rel.reverse"
        arguments :=
          [EncodedDVPairs pairs, encodeString left, encodeString right] }
    have happlication :
        RuleApplication validatedSidePresentation ruleInstance
          [member (encodeDVPair (right, left)) (EncodedDVPairs pairs)]
          (dvRel (EncodedDVPairs pairs) (encodeString left)
            (encodeString right)) :=
      instantiateRule?_eq_some_iff_application.mp
        (dvRelReverse_instantiates pairs left right)
    exact ⟨Derivation.byRule ruleInstance happlication (.cons child .nil)⟩

private theorem dvRelApplication_decompose
    {ruleInstance : RuleInstance} {premises : List Pattern}
    {pairsPattern leftPattern rightPattern : Pattern}
    (application :
      RuleApplication validatedSidePresentation ruleInstance premises
        (dvRel pairsPattern leftPattern rightPattern)) :
    ∃ rule : RuleSchema,
      (rule = dvRelForwardRule ∨ rule = dvRelReverseRule) ∧
      validatedSidePresentation.1.lookupRule? ruleInstance.ruleId = some rule ∧
      argumentsValidAt rule.metavariables ruleInstance.arguments = true ∧
      InstantiatesList rule.metavariables ruleInstance.arguments
        rule.premises premises ∧
      Instantiates rule.metavariables ruleInstance.arguments rule.conclusion
        (dvRel pairsPattern leftPattern rightPattern) := by
  cases application with
  | intro rule hlookup harguments hpremises hconclusion =>
      have hvalid := rule_isValidIn_of_lookup validatedSidePresentation hlookup
      have hshape := RuleSchema.conclusion_hasJudgmentShape_of_validIn hvalid
      have hmem : rule ∈ sideRules := by
        change rule ∈ validatedSidePresentation.1.rules
        exact List.mem_of_find?_eq_some hlookup
      have hrule : rule = dvRelForwardRule ∨ rule = dvRelReverseRule := by
        cases hconclusionRule : rule.conclusion with
        | apply sourceHead sourceArgs =>
            rw [hconclusionRule] at hconclusion
            have hhead : sourceHead = dvRelHead :=
              InstantiatesAt.apply_head_eq hconclusion
            have hselected : ruleConclusionIs dvRelHead rule = true := by
              simp [ruleConclusionIs, hconclusionRule, hhead]
            have hfiltered :
                rule ∈ sideRules.filter (ruleConclusionIs dvRelHead) :=
              List.mem_filter.mpr ⟨hmem, hselected⟩
            rw [dvRelRules_filter] at hfiltered
            simpa using hfiltered
        | bvar index =>
            rw [hconclusionRule] at hshape
            simp [Presentation.hasJudgmentShape] at hshape
        | fvar name =>
            rw [hconclusionRule] at hshape
            simp [Presentation.hasJudgmentShape] at hshape
        | lambda binder body =>
            rw [hconclusionRule] at hshape
            simp [Presentation.hasJudgmentShape] at hshape
        | multiLambda arity binders body =>
            rw [hconclusionRule] at hshape
            simp [Presentation.hasJudgmentShape] at hshape
        | subst body replacement =>
            rw [hconclusionRule] at hshape
            simp [Presentation.hasJudgmentShape] at hshape
        | collection collectionType elements rest =>
            rw [hconclusionRule] at hshape
            simp [Presentation.hasJudgmentShape] at hshape
      exact ⟨rule, hrule, hlookup, harguments, hpremises, hconclusion⟩

private theorem dvRel_application_inv
    {ruleInstance : RuleInstance} {premises : List Pattern}
    {pairs : List (String × String)} {left right : String}
    (application :
      RuleApplication validatedSidePresentation ruleInstance premises
        (dvRel (EncodedDVPairs pairs) (encodeString left)
          (encodeString right))) :
    premises = [member (encodeDVPair (left, right)) (EncodedDVPairs pairs)] ∨
      premises =
        [member (encodeDVPair (right, left)) (EncodedDVPairs pairs)] := by
  rcases dvRelApplication_decompose application with
    ⟨rule, hrule, hlookup, harguments, hpremises, hconclusion⟩
  rcases hrule with rfl | rfl
  · have hlength := argumentsValidAt_length_eq harguments
    rw [dvRelForwardRule_eq_schema] at hlength
    simp [dvRelForwardSchema] at hlength
    rcases List.length_eq_three.mp hlength with
      ⟨first, second, third, hargs⟩
    have hpremises' := instantiateSchemasAt?_complete hpremises
    have hconclusion' := instantiateSchemaAt?_complete hconclusion
    simp [hargs, dvRelForwardRule_eq_schema, dvRelForwardSchema, formal,
      metavariable, instantiateSchemasAt?, instantiateSchemaAt?,
      lookupArgumentAt?, member, dvRel]
      at hpremises' hconclusion'
    left
    simpa [member, encodeDVPair, hconclusion'.1, hconclusion'.2.1,
      hconclusion'.2.2] using hpremises'.symm
  · have hlength := argumentsValidAt_length_eq harguments
    rw [dvRelReverseRule_eq_schema] at hlength
    simp [dvRelReverseSchema] at hlength
    rcases List.length_eq_three.mp hlength with
      ⟨first, second, third, hargs⟩
    have hpremises' := instantiateSchemasAt?_complete hpremises
    have hconclusion' := instantiateSchemaAt?_complete hconclusion
    simp [hargs, dvRelReverseRule_eq_schema, dvRelReverseSchema, formal,
      metavariable, instantiateSchemasAt?, instantiateSchemaAt?,
      lookupArgumentAt?, member, dvRel]
      at hpremises' hconclusion'
    right
    simpa [member, encodeDVPair, hconclusion'.1, hconclusion'.2.1,
      hconclusion'.2.2] using hpremises'.symm

/-- DVRel derivability is exactly symmetric membership in the ordinary caller
DV-pair list. -/
theorem dvRel_derivation_iff (pairs : List (String × String))
    (left right : String) :
    Nonempty
        (Derivation validatedSidePresentation
          (dvRel (EncodedDVPairs pairs) (encodeString left)
            (encodeString right))) ↔
      DVRelation pairs left right := by
  constructor
  · rintro ⟨derivation⟩
    cases derivation with
    | byRule ruleInstance application children =>
        rcases dvRel_application_inv application with hforward | hreverse
        · rw [hforward] at children
          cases children with
          | cons child remaining =>
              cases remaining with
              | nil =>
                  exact Or.inl
                    (member_pair_derivation_sound (left, right) pairs child)
        · rw [hreverse] at children
          cases children with
          | cons child remaining =>
              cases remaining with
              | nil =>
                  exact Or.inr
                    (member_pair_derivation_sound (right, left) pairs child)
  · exact dvRel_derivable pairs left right

private theorem allWithNil_instantiates
    (pairs : List (String × String)) (left : String) :
    instantiateRule? validatedSidePresentation
        { ruleId := ruleId "$mm.all-with.nil"
          arguments := [EncodedDVPairs pairs, encodeString left] } =
      some
        ([], allWith (EncodedDVPairs pairs) (encodeString left)
          (EncodedNames [])) := by
  simp [instantiateRule?, lookup_allWithNilRule,
    allWithNilRule_eq_schema, allWithNilSchema, formal, metavariable,
    argumentsValidAt, argumentValidAt, instantiateSchemas?,
    instantiateSchemasAt?, instantiateSchema?, instantiateSchemaAt?,
    lookupArgumentAt?, allWith, allWithHead, EncodedNames, encodeListWith]

private theorem allWithCons_instantiates
    (pairs : List (String × String)) (left right : String)
    (rights : List String) :
    instantiateRule? validatedSidePresentation
        { ruleId := ruleId "$mm.all-with.cons"
          arguments :=
            [ EncodedDVPairs pairs, encodeString left, encodeString right
            , EncodedNames rights ] } =
      some
        ( [ dvRel (EncodedDVPairs pairs) (encodeString left)
              (encodeString right)
          , allWith (EncodedDVPairs pairs) (encodeString left)
              (EncodedNames rights) ]
        , allWith (EncodedDVPairs pairs) (encodeString left)
            (EncodedNames (right :: rights)) ) := by
  simp [instantiateRule?, lookup_allWithConsRule,
    allWithConsRule_eq_schema, allWithConsSchema, formal, metavariable,
    argumentsValidAt, argumentValidAt, instantiateSchemas?,
    instantiateSchemasAt?, instantiateSchema?, instantiateSchemaAt?,
    lookupArgumentAt?, dvRel, dvRelHead, allWith, allWithHead, EncodedNames,
    encodeListWith]

private theorem allWith_derivable (pairs : List (String × String))
    (left : String) (rights : List String)
    (semantics : AllWithSemantics pairs left rights) :
    Nonempty
      (Derivation validatedSidePresentation
        (allWith (EncodedDVPairs pairs) (encodeString left)
          (EncodedNames rights))) := by
  induction rights with
  | nil =>
      let ruleInstance : RuleInstance :=
        { ruleId := ruleId "$mm.all-with.nil"
          arguments := [EncodedDVPairs pairs, encodeString left] }
      have happlication :
          RuleApplication validatedSidePresentation ruleInstance []
            (allWith (EncodedDVPairs pairs) (encodeString left)
              (EncodedNames [])) :=
        instantiateRule?_eq_some_iff_application.mp
          (allWithNil_instantiates pairs left)
      exact ⟨Derivation.byRule ruleInstance happlication .nil⟩
  | cons right rights ih =>
      have hrelation : DVRelation pairs left right :=
        semantics right (by simp)
      have htail : AllWithSemantics pairs left rights := by
        intro other hmem
        exact semantics other (by simp [hmem])
      rcases dvRel_derivable pairs left right hrelation with ⟨relationChild⟩
      rcases ih htail with ⟨tailChild⟩
      let ruleInstance : RuleInstance :=
        { ruleId := ruleId "$mm.all-with.cons"
          arguments :=
            [ EncodedDVPairs pairs, encodeString left, encodeString right
            , EncodedNames rights ] }
      have happlication :
          RuleApplication validatedSidePresentation ruleInstance
            [ dvRel (EncodedDVPairs pairs) (encodeString left)
                (encodeString right)
            , allWith (EncodedDVPairs pairs) (encodeString left)
                (EncodedNames rights) ]
            (allWith (EncodedDVPairs pairs) (encodeString left)
              (EncodedNames (right :: rights))) :=
        instantiateRule?_eq_some_iff_application.mp
          (allWithCons_instantiates pairs left right rights)
      exact ⟨Derivation.byRule ruleInstance happlication
        (.cons relationChild (.cons tailChild .nil))⟩

private theorem allWithApplication_decompose
    {ruleInstance : RuleInstance} {premises : List Pattern}
    {pairsPattern leftPattern rightsPattern : Pattern}
    (application :
      RuleApplication validatedSidePresentation ruleInstance premises
        (allWith pairsPattern leftPattern rightsPattern)) :
    ∃ rule : RuleSchema,
      (rule = allWithNilRule ∨ rule = allWithConsRule) ∧
      validatedSidePresentation.1.lookupRule? ruleInstance.ruleId = some rule ∧
      argumentsValidAt rule.metavariables ruleInstance.arguments = true ∧
      InstantiatesList rule.metavariables ruleInstance.arguments
        rule.premises premises ∧
      Instantiates rule.metavariables ruleInstance.arguments rule.conclusion
        (allWith pairsPattern leftPattern rightsPattern) := by
  cases application with
  | intro rule hlookup harguments hpremises hconclusion =>
      have hvalid := rule_isValidIn_of_lookup validatedSidePresentation hlookup
      have hshape := RuleSchema.conclusion_hasJudgmentShape_of_validIn hvalid
      have hmem : rule ∈ sideRules := by
        change rule ∈ validatedSidePresentation.1.rules
        exact List.mem_of_find?_eq_some hlookup
      have hrule : rule = allWithNilRule ∨ rule = allWithConsRule := by
        cases hconclusionRule : rule.conclusion with
        | apply sourceHead sourceArgs =>
            rw [hconclusionRule] at hconclusion
            have hhead : sourceHead = allWithHead :=
              InstantiatesAt.apply_head_eq hconclusion
            have hselected : ruleConclusionIs allWithHead rule = true := by
              simp [ruleConclusionIs, hconclusionRule, hhead]
            have hfiltered :
                rule ∈ sideRules.filter (ruleConclusionIs allWithHead) :=
              List.mem_filter.mpr ⟨hmem, hselected⟩
            rw [allWithRules_filter] at hfiltered
            simpa using hfiltered
        | bvar index =>
            rw [hconclusionRule] at hshape
            simp [Presentation.hasJudgmentShape] at hshape
        | fvar name =>
            rw [hconclusionRule] at hshape
            simp [Presentation.hasJudgmentShape] at hshape
        | lambda binder body =>
            rw [hconclusionRule] at hshape
            simp [Presentation.hasJudgmentShape] at hshape
        | multiLambda arity binders body =>
            rw [hconclusionRule] at hshape
            simp [Presentation.hasJudgmentShape] at hshape
        | subst body replacement =>
            rw [hconclusionRule] at hshape
            simp [Presentation.hasJudgmentShape] at hshape
        | collection collectionType elements rest =>
            rw [hconclusionRule] at hshape
            simp [Presentation.hasJudgmentShape] at hshape
      exact ⟨rule, hrule, hlookup, harguments, hpremises, hconclusion⟩

private theorem allWithNil_application_inv
    {ruleInstance : RuleInstance} {premises : List Pattern}
    {pairs : List (String × String)} {left : String}
    (application :
      RuleApplication validatedSidePresentation ruleInstance premises
        (allWith (EncodedDVPairs pairs) (encodeString left)
          (EncodedNames []))) :
    premises = [] := by
  rcases allWithApplication_decompose application with
    ⟨rule, hrule, hlookup, harguments, hpremises, hconclusion⟩
  rcases hrule with rfl | rfl
  · have hlength := argumentsValidAt_length_eq harguments
    rw [allWithNilRule_eq_schema] at hlength
    simp [allWithNilSchema] at hlength
    rcases List.length_eq_two.mp hlength with ⟨first, second, hargs⟩
    have hpremises' := instantiateSchemasAt?_complete hpremises
    simpa [hargs, allWithNilRule_eq_schema, allWithNilSchema, formal,
      metavariable, instantiateSchemasAt?] using hpremises'
  · have hlength := argumentsValidAt_length_eq harguments
    rw [allWithConsRule_eq_schema] at hlength
    simp [allWithConsSchema] at hlength
    rcases List.length_eq_four.mp hlength with
      ⟨first, second, third, fourth, hargs⟩
    have hconclusion' := instantiateSchemaAt?_complete hconclusion
    simp [hargs, allWithConsRule_eq_schema, allWithConsSchema, formal,
      metavariable, instantiateSchemaAt?, instantiateSchemasAt?,
      lookupArgumentAt?, allWith, EncodedNames, encodeListWith]
      at hconclusion'

private theorem allWithCons_application_inv
    {ruleInstance : RuleInstance} {premises : List Pattern}
    {pairs : List (String × String)} {left right : String}
    {rights : List String}
    (application :
      RuleApplication validatedSidePresentation ruleInstance premises
        (allWith (EncodedDVPairs pairs) (encodeString left)
          (EncodedNames (right :: rights)))) :
    premises =
      [ dvRel (EncodedDVPairs pairs) (encodeString left) (encodeString right)
      , allWith (EncodedDVPairs pairs) (encodeString left)
          (EncodedNames rights) ] := by
  rcases allWithApplication_decompose application with
    ⟨rule, hrule, hlookup, harguments, hpremises, hconclusion⟩
  rcases hrule with rfl | rfl
  · have hlength := argumentsValidAt_length_eq harguments
    rw [allWithNilRule_eq_schema] at hlength
    simp [allWithNilSchema] at hlength
    rcases List.length_eq_two.mp hlength with ⟨first, second, hargs⟩
    have hconclusion' := instantiateSchemaAt?_complete hconclusion
    simp [hargs, allWithNilRule_eq_schema, allWithNilSchema, formal,
      metavariable, instantiateSchemaAt?, instantiateSchemasAt?,
      lookupArgumentAt?, allWith, EncodedNames, encodeListWith]
      at hconclusion'
  · have hlength := argumentsValidAt_length_eq harguments
    rw [allWithConsRule_eq_schema] at hlength
    simp [allWithConsSchema] at hlength
    rcases List.length_eq_four.mp hlength with
      ⟨first, second, third, fourth, hargs⟩
    have hpremises' := instantiateSchemasAt?_complete hpremises
    have hconclusion' := instantiateSchemaAt?_complete hconclusion
    simp [hargs, allWithConsRule_eq_schema, allWithConsSchema, formal,
      metavariable, instantiateSchemasAt?, instantiateSchemaAt?,
      lookupArgumentAt?, dvRel, allWith, EncodedNames, encodeListWith]
      at hpremises' hconclusion'
    simpa [dvRel, allWith, EncodedNames, hconclusion'.1,
      hconclusion'.2.1, hconclusion'.2.2.1,
      hconclusion'.2.2.2] using hpremises'.symm

/-- AllWith derivability is exactly universal DV-relatedness over the
ordinary right-hand name list. -/
theorem allWith_derivation_iff (pairs : List (String × String))
    (left : String) (rights : List String) :
    Nonempty
        (Derivation validatedSidePresentation
          (allWith (EncodedDVPairs pairs) (encodeString left)
            (EncodedNames rights))) ↔
      AllWithSemantics pairs left rights := by
  constructor
  · rintro ⟨derivation⟩
    induction rights with
    | nil =>
        intro right hmem
        simp at hmem
    | cons right rights ih =>
        cases derivation with
        | byRule ruleInstance application children =>
            have hpremises := allWithCons_application_inv application
            rw [hpremises] at children
            cases children with
            | cons relationChild remaining =>
                cases remaining with
                | cons tailChild remaining =>
                    cases remaining with
                    | nil =>
                        intro other hmem
                        rcases List.mem_cons.mp hmem with rfl | htail
                        · exact (dvRel_derivation_iff pairs left other).mp
                            ⟨relationChild⟩
                        · exact ih tailChild other htail
  · exact allWith_derivable pairs left rights

private theorem allPairsNil_instantiates
    (pairs : List (String × String)) (rights : List String) :
    instantiateRule? validatedSidePresentation
        { ruleId := ruleId "$mm.all-pairs.nil"
          arguments := [EncodedDVPairs pairs, EncodedNames rights] } =
      some
        ([], allPairs (EncodedDVPairs pairs) (EncodedNames [])
          (EncodedNames rights)) := by
  simp [instantiateRule?, lookup_allPairsNilRule,
    allPairsNilRule_eq_schema, allPairsNilSchema, formal, metavariable,
    argumentsValidAt, argumentValidAt, instantiateSchemas?,
    instantiateSchemasAt?, instantiateSchema?, instantiateSchemaAt?,
    lookupArgumentAt?, allPairs, allPairsHead, EncodedNames, encodeListWith]

private theorem allPairsCons_instantiates
    (pairs : List (String × String)) (left : String)
    (lefts rights : List String) :
    instantiateRule? validatedSidePresentation
        { ruleId := ruleId "$mm.all-pairs.cons"
          arguments :=
            [ EncodedDVPairs pairs, encodeString left, EncodedNames lefts
            , EncodedNames rights ] } =
      some
        ( [ allWith (EncodedDVPairs pairs) (encodeString left)
              (EncodedNames rights)
          , allPairs (EncodedDVPairs pairs) (EncodedNames lefts)
              (EncodedNames rights) ]
        , allPairs (EncodedDVPairs pairs) (EncodedNames (left :: lefts))
            (EncodedNames rights) ) := by
  simp [instantiateRule?, lookup_allPairsConsRule,
    allPairsConsRule_eq_schema, allPairsConsSchema, formal, metavariable,
    argumentsValidAt, argumentValidAt, instantiateSchemas?,
    instantiateSchemasAt?, instantiateSchema?, instantiateSchemaAt?,
    lookupArgumentAt?, allWith, allWithHead, allPairs, allPairsHead,
    EncodedNames, encodeListWith]

private theorem allPairs_derivable (pairs : List (String × String))
    (lefts rights : List String)
    (semantics : AllPairsSemantics pairs lefts rights) :
    Nonempty
      (Derivation validatedSidePresentation
        (allPairs (EncodedDVPairs pairs) (EncodedNames lefts)
          (EncodedNames rights))) := by
  induction lefts with
  | nil =>
      let ruleInstance : RuleInstance :=
        { ruleId := ruleId "$mm.all-pairs.nil"
          arguments := [EncodedDVPairs pairs, EncodedNames rights] }
      have happlication :
          RuleApplication validatedSidePresentation ruleInstance []
            (allPairs (EncodedDVPairs pairs) (EncodedNames [])
              (EncodedNames rights)) :=
        instantiateRule?_eq_some_iff_application.mp
          (allPairsNil_instantiates pairs rights)
      exact ⟨Derivation.byRule ruleInstance happlication .nil⟩
  | cons left lefts ih =>
      have hwith : AllWithSemantics pairs left rights := by
        intro right hright
        exact semantics left (by simp) right hright
      have htail : AllPairsSemantics pairs lefts rights := by
        intro other hmem
        exact semantics other (by simp [hmem])
      rcases allWith_derivable pairs left rights hwith with ⟨withChild⟩
      rcases ih htail with ⟨tailChild⟩
      let ruleInstance : RuleInstance :=
        { ruleId := ruleId "$mm.all-pairs.cons"
          arguments :=
            [ EncodedDVPairs pairs, encodeString left, EncodedNames lefts
            , EncodedNames rights ] }
      have happlication :
          RuleApplication validatedSidePresentation ruleInstance
            [ allWith (EncodedDVPairs pairs) (encodeString left)
                (EncodedNames rights)
            , allPairs (EncodedDVPairs pairs) (EncodedNames lefts)
                (EncodedNames rights) ]
            (allPairs (EncodedDVPairs pairs) (EncodedNames (left :: lefts))
              (EncodedNames rights)) :=
        instantiateRule?_eq_some_iff_application.mp
          (allPairsCons_instantiates pairs left lefts rights)
      exact ⟨Derivation.byRule ruleInstance happlication
        (.cons withChild (.cons tailChild .nil))⟩

private theorem allPairsApplication_decompose
    {ruleInstance : RuleInstance} {premises : List Pattern}
    {pairsPattern leftsPattern rightsPattern : Pattern}
    (application :
      RuleApplication validatedSidePresentation ruleInstance premises
        (allPairs pairsPattern leftsPattern rightsPattern)) :
    ∃ rule : RuleSchema,
      (rule = allPairsNilRule ∨ rule = allPairsConsRule) ∧
      validatedSidePresentation.1.lookupRule? ruleInstance.ruleId = some rule ∧
      argumentsValidAt rule.metavariables ruleInstance.arguments = true ∧
      InstantiatesList rule.metavariables ruleInstance.arguments
        rule.premises premises ∧
      Instantiates rule.metavariables ruleInstance.arguments rule.conclusion
        (allPairs pairsPattern leftsPattern rightsPattern) := by
  cases application with
  | intro rule hlookup harguments hpremises hconclusion =>
      have hvalid := rule_isValidIn_of_lookup validatedSidePresentation hlookup
      have hshape := RuleSchema.conclusion_hasJudgmentShape_of_validIn hvalid
      have hmem : rule ∈ sideRules := by
        change rule ∈ validatedSidePresentation.1.rules
        exact List.mem_of_find?_eq_some hlookup
      have hrule : rule = allPairsNilRule ∨ rule = allPairsConsRule := by
        cases hconclusionRule : rule.conclusion with
        | apply sourceHead sourceArgs =>
            rw [hconclusionRule] at hconclusion
            have hhead : sourceHead = allPairsHead :=
              InstantiatesAt.apply_head_eq hconclusion
            have hselected : ruleConclusionIs allPairsHead rule = true := by
              simp [ruleConclusionIs, hconclusionRule, hhead]
            have hfiltered :
                rule ∈ sideRules.filter (ruleConclusionIs allPairsHead) :=
              List.mem_filter.mpr ⟨hmem, hselected⟩
            rw [allPairsRules_filter] at hfiltered
            simpa using hfiltered
        | bvar index =>
            rw [hconclusionRule] at hshape
            simp [Presentation.hasJudgmentShape] at hshape
        | fvar name =>
            rw [hconclusionRule] at hshape
            simp [Presentation.hasJudgmentShape] at hshape
        | lambda binder body =>
            rw [hconclusionRule] at hshape
            simp [Presentation.hasJudgmentShape] at hshape
        | multiLambda arity binders body =>
            rw [hconclusionRule] at hshape
            simp [Presentation.hasJudgmentShape] at hshape
        | subst body replacement =>
            rw [hconclusionRule] at hshape
            simp [Presentation.hasJudgmentShape] at hshape
        | collection collectionType elements rest =>
            rw [hconclusionRule] at hshape
            simp [Presentation.hasJudgmentShape] at hshape
      exact ⟨rule, hrule, hlookup, harguments, hpremises, hconclusion⟩

private theorem allPairsNil_application_inv
    {ruleInstance : RuleInstance} {premises : List Pattern}
    {pairs : List (String × String)} {rights : List String}
    (application :
      RuleApplication validatedSidePresentation ruleInstance premises
        (allPairs (EncodedDVPairs pairs) (EncodedNames [])
          (EncodedNames rights))) :
    premises = [] := by
  rcases allPairsApplication_decompose application with
    ⟨rule, hrule, hlookup, harguments, hpremises, hconclusion⟩
  rcases hrule with rfl | rfl
  · have hlength := argumentsValidAt_length_eq harguments
    rw [allPairsNilRule_eq_schema] at hlength
    simp [allPairsNilSchema] at hlength
    rcases List.length_eq_two.mp hlength with ⟨first, second, hargs⟩
    have hpremises' := instantiateSchemasAt?_complete hpremises
    simpa [hargs, allPairsNilRule_eq_schema, allPairsNilSchema, formal,
      metavariable, instantiateSchemasAt?] using hpremises'
  · have hlength := argumentsValidAt_length_eq harguments
    rw [allPairsConsRule_eq_schema] at hlength
    simp [allPairsConsSchema] at hlength
    rcases List.length_eq_four.mp hlength with
      ⟨first, second, third, fourth, hargs⟩
    have hconclusion' := instantiateSchemaAt?_complete hconclusion
    simp [hargs, allPairsConsRule_eq_schema, allPairsConsSchema, formal,
      metavariable, instantiateSchemaAt?, instantiateSchemasAt?,
      lookupArgumentAt?, allPairs, EncodedNames, encodeListWith]
      at hconclusion'

private theorem allPairsCons_application_inv
    {ruleInstance : RuleInstance} {premises : List Pattern}
    {pairs : List (String × String)} {left : String}
    {lefts rights : List String}
    (application :
      RuleApplication validatedSidePresentation ruleInstance premises
        (allPairs (EncodedDVPairs pairs) (EncodedNames (left :: lefts))
          (EncodedNames rights))) :
    premises =
      [ allWith (EncodedDVPairs pairs) (encodeString left)
          (EncodedNames rights)
      , allPairs (EncodedDVPairs pairs) (EncodedNames lefts)
          (EncodedNames rights) ] := by
  rcases allPairsApplication_decompose application with
    ⟨rule, hrule, hlookup, harguments, hpremises, hconclusion⟩
  rcases hrule with rfl | rfl
  · have hlength := argumentsValidAt_length_eq harguments
    rw [allPairsNilRule_eq_schema] at hlength
    simp [allPairsNilSchema] at hlength
    rcases List.length_eq_two.mp hlength with ⟨first, second, hargs⟩
    have hconclusion' := instantiateSchemaAt?_complete hconclusion
    simp [hargs, allPairsNilRule_eq_schema, allPairsNilSchema, formal,
      metavariable, instantiateSchemaAt?, instantiateSchemasAt?,
      lookupArgumentAt?, allPairs, EncodedNames, encodeListWith]
      at hconclusion'
  · have hlength := argumentsValidAt_length_eq harguments
    rw [allPairsConsRule_eq_schema] at hlength
    simp [allPairsConsSchema] at hlength
    rcases List.length_eq_four.mp hlength with
      ⟨first, second, third, fourth, hargs⟩
    have hpremises' := instantiateSchemasAt?_complete hpremises
    have hconclusion' := instantiateSchemaAt?_complete hconclusion
    simp [hargs, allPairsConsRule_eq_schema, allPairsConsSchema, formal,
      metavariable, instantiateSchemasAt?, instantiateSchemaAt?,
      lookupArgumentAt?, allWith, allPairs, EncodedNames, encodeListWith]
      at hpremises' hconclusion'
    simpa [allWith, allPairs, EncodedNames, hconclusion'.1,
      hconclusion'.2.1.1, hconclusion'.2.1.2,
      hconclusion'.2.2] using hpremises'.symm

/-- AllPairs derivability is exactly the universal cross-product condition on
ordinary name lists. -/
theorem allPairs_derivation_iff (pairs : List (String × String))
    (lefts rights : List String) :
    Nonempty
        (Derivation validatedSidePresentation
          (allPairs (EncodedDVPairs pairs) (EncodedNames lefts)
            (EncodedNames rights))) ↔
      AllPairsSemantics pairs lefts rights := by
  constructor
  · rintro ⟨derivation⟩
    induction lefts with
    | nil =>
        intro left hmem
        simp at hmem
    | cons left lefts ih =>
        cases derivation with
        | byRule ruleInstance application children =>
            have hpremises := allPairsCons_application_inv application
            rw [hpremises] at children
            cases children with
            | cons withChild remaining =>
                cases remaining with
                | cons tailChild remaining =>
                    cases remaining with
                    | nil =>
                        intro other hmem
                        rcases List.mem_cons.mp hmem with rfl | htail
                        · exact (allWith_derivation_iff pairs other rights).mp
                            ⟨withChild⟩
                        · exact ih tailChild other htail
  · exact allPairs_derivable pairs lefts rights

private theorem List.length_eq_five {alpha : Type} {values : List alpha} :
    values.length = 5 ↔
      ∃ a b c d e, values = [a, b, c, d, e] := by
  constructor
  · intro hlength
    rcases values with _ | ⟨a, values⟩ <;> simp at hlength
    rcases values with _ | ⟨b, values⟩ <;> simp at hlength
    rcases values with _ | ⟨c, values⟩ <;> simp at hlength
    rcases values with _ | ⟨d, values⟩ <;> simp at hlength
    rcases values with _ | ⟨e, values⟩ <;> simp at hlength
    cases values <;> simp at hlength
    exact ⟨a, b, c, d, e, rfl⟩
  · rintro ⟨a, b, c, d, e, rfl⟩
    rfl

private theorem List.length_eq_eleven {alpha : Type} {values : List alpha} :
    values.length = 11 ↔
      ∃ a b c d e f g h i j k,
        values = [a, b, c, d, e, f, g, h, i, j, k] := by
  constructor
  · intro hlength
    rcases values with _ | ⟨a, values⟩ <;> simp at hlength
    rcases values with _ | ⟨b, values⟩ <;> simp at hlength
    rcases values with _ | ⟨c, values⟩ <;> simp at hlength
    rcases values with _ | ⟨d, values⟩ <;> simp at hlength
    rcases values with _ | ⟨e, values⟩ <;> simp at hlength
    rcases values with _ | ⟨f, values⟩ <;> simp at hlength
    rcases values with _ | ⟨g, values⟩ <;> simp at hlength
    rcases values with _ | ⟨h, values⟩ <;> simp at hlength
    rcases values with _ | ⟨i, values⟩ <;> simp at hlength
    rcases values with _ | ⟨j, values⟩ <;> simp at hlength
    rcases values with _ | ⟨k, values⟩ <;> simp at hlength
    cases values <;> simp at hlength
    exact ⟨a, b, c, d, e, f, g, h, i, j, k, rfl⟩
  · rintro ⟨a, b, c, d, e, f, g, h, i, j, k, rfl⟩
    rfl

private theorem dvListsNil_instantiates
    (substitution : FiniteSubstitution)
    (callerDV : List (String × String)) :
    instantiateRule? validatedSidePresentation
        { ruleId := ruleId "$mm.dv-lists.nil"
          arguments := [encodeSubstitution substitution, EncodedDVPairs callerDV] } =
      some
        ([], dvLists (encodeSubstitution substitution) (EncodedDVPairs callerDV)
          (EncodedDVPairs [])) := by
  simp [instantiateRule?, lookup_dvListsNilRule,
    dvListsNilRule_eq_schema, dvListsNilSchema, formal, metavariable,
    argumentsValidAt, argumentValidAt, instantiateSchemas?,
    instantiateSchemasAt?, instantiateSchema?, instantiateSchemaAt?,
    lookupArgumentAt?, dvLists, dvListsHead, EncodedDVPairs, encodeListWith]

private theorem dvListsCons_instantiates
    (substitution : FiniteSubstitution)
    (callerDV rest : List (String × String)) (left right : String)
    (leftReplacement rightReplacement : ConstantHeadedFormula) :
    instantiateRule? validatedSidePresentation
        { ruleId := ruleId "$mm.dv-lists.cons"
          arguments :=
            [ encodeSubstitution substitution, EncodedDVPairs callerDV
            , encodeString left, encodeString right, EncodedDVPairs rest
            , encodeString leftReplacement.typecode
            , EncodedBody leftReplacement.body
            , encodeString rightReplacement.typecode
            , EncodedBody rightReplacement.body
            , EncodedNames (BodyVariables leftReplacement.body)
            , EncodedNames (BodyVariables rightReplacement.body) ] } =
      some
        ( [ lookup (encodeSubstitution substitution) (encodeString left)
              (encodeString leftReplacement.typecode)
              (EncodedBody leftReplacement.body)
          , lookup (encodeSubstitution substitution) (encodeString right)
              (encodeString rightReplacement.typecode)
              (EncodedBody rightReplacement.body)
          , vars (EncodedBody leftReplacement.body)
              (EncodedNames (BodyVariables leftReplacement.body))
          , vars (EncodedBody rightReplacement.body)
              (EncodedNames (BodyVariables rightReplacement.body))
          , allPairs (EncodedDVPairs callerDV)
              (EncodedNames (BodyVariables leftReplacement.body))
              (EncodedNames (BodyVariables rightReplacement.body))
          , dvLists (encodeSubstitution substitution) (EncodedDVPairs callerDV)
              (EncodedDVPairs rest) ]
        , dvLists (encodeSubstitution substitution) (EncodedDVPairs callerDV)
            (EncodedDVPairs ((left, right) :: rest)) ) := by
  simp [instantiateRule?, lookup_dvListsConsRule,
    dvListsConsRule_eq_schema, dvListsConsSchema, formal, metavariable,
    argumentsValidAt, argumentValidAt, instantiateSchemas?,
    instantiateSchemasAt?, instantiateSchema?, instantiateSchemaAt?,
    lookupArgumentAt?, lookup, lookupHead, vars, varsHead, allPairs,
    allPairsHead, dvLists, dvListsHead, EncodedDVPairs, EncodedNames,
    encodeListWith, encodeDVPair]

private theorem dvLists_derivable (substitution : FiniteSubstitution)
    (callerDV calleeDV : List (String × String))
    (semantics : DVListsSemantics substitution callerDV calleeDV) :
    Nonempty
      (Derivation validatedSidePresentation
        (dvLists (encodeSubstitution substitution) (EncodedDVPairs callerDV)
          (EncodedDVPairs calleeDV))) := by
  induction calleeDV with
  | nil =>
      let ruleInstance : RuleInstance :=
        { ruleId := ruleId "$mm.dv-lists.nil"
          arguments := [encodeSubstitution substitution, EncodedDVPairs callerDV] }
      have happlication :
          RuleApplication validatedSidePresentation ruleInstance []
            (dvLists (encodeSubstitution substitution) (EncodedDVPairs callerDV)
              (EncodedDVPairs [])) :=
        instantiateRule?_eq_some_iff_application.mp
          (dvListsNil_instantiates substitution callerDV)
      exact ⟨Derivation.byRule ruleInstance happlication .nil⟩
  | cons pair rest ih =>
      rcases pair with ⟨left, right⟩
      rcases semantics (left, right) (by simp) with
        ⟨leftReplacement, rightReplacement, leftLookup, rightLookup,
          hpairs⟩
      have htail : DVListsSemantics substitution callerDV rest := by
        intro pair hmem
        exact semantics pair (by simp [hmem])
      rcases lookup_derivable_of_mem substitution
          ({ variableName := left, replacement := leftReplacement } :
            FormulaBinding) leftLookup with ⟨leftLookupChild⟩
      rcases lookup_derivable_of_mem substitution
          ({ variableName := right, replacement := rightReplacement } :
            FormulaBinding) rightLookup with ⟨rightLookupChild⟩
      rcases vars_derivable leftReplacement.body with ⟨leftVarsChild⟩
      rcases vars_derivable rightReplacement.body with ⟨rightVarsChild⟩
      rcases allPairs_derivable callerDV
          (BodyVariables leftReplacement.body)
          (BodyVariables rightReplacement.body) hpairs with ⟨pairsChild⟩
      rcases ih htail with ⟨tailChild⟩
      let ruleInstance : RuleInstance :=
        { ruleId := ruleId "$mm.dv-lists.cons"
          arguments :=
            [ encodeSubstitution substitution, EncodedDVPairs callerDV
            , encodeString left, encodeString right, EncodedDVPairs rest
            , encodeString leftReplacement.typecode
            , EncodedBody leftReplacement.body
            , encodeString rightReplacement.typecode
            , EncodedBody rightReplacement.body
            , EncodedNames (BodyVariables leftReplacement.body)
            , EncodedNames (BodyVariables rightReplacement.body) ] }
      have happlication :
          RuleApplication validatedSidePresentation ruleInstance
            [ lookup (encodeSubstitution substitution) (encodeString left)
                (encodeString leftReplacement.typecode)
                (EncodedBody leftReplacement.body)
            , lookup (encodeSubstitution substitution) (encodeString right)
                (encodeString rightReplacement.typecode)
                (EncodedBody rightReplacement.body)
            , vars (EncodedBody leftReplacement.body)
                (EncodedNames (BodyVariables leftReplacement.body))
            , vars (EncodedBody rightReplacement.body)
                (EncodedNames (BodyVariables rightReplacement.body))
            , allPairs (EncodedDVPairs callerDV)
                (EncodedNames (BodyVariables leftReplacement.body))
                (EncodedNames (BodyVariables rightReplacement.body))
            , dvLists (encodeSubstitution substitution)
                (EncodedDVPairs callerDV) (EncodedDVPairs rest) ]
            (dvLists (encodeSubstitution substitution)
              (EncodedDVPairs callerDV)
              (EncodedDVPairs ((left, right) :: rest))) :=
        instantiateRule?_eq_some_iff_application.mp
          (dvListsCons_instantiates substitution callerDV rest left right
            leftReplacement rightReplacement)
      exact ⟨Derivation.byRule ruleInstance happlication
        (.cons leftLookupChild
          (.cons rightLookupChild
            (.cons leftVarsChild
              (.cons rightVarsChild
                (.cons pairsChild (.cons tailChild .nil))))))⟩

private theorem dvListsApplication_decompose
    {ruleInstance : RuleInstance} {premises : List Pattern}
    {substitutionPattern callerPattern calleePattern : Pattern}
    (application :
      RuleApplication validatedSidePresentation ruleInstance premises
        (dvLists substitutionPattern callerPattern calleePattern)) :
    ∃ rule : RuleSchema,
      (rule = dvListsNilRule ∨ rule = dvListsConsRule) ∧
      validatedSidePresentation.1.lookupRule? ruleInstance.ruleId = some rule ∧
      argumentsValidAt rule.metavariables ruleInstance.arguments = true ∧
      InstantiatesList rule.metavariables ruleInstance.arguments
        rule.premises premises ∧
      Instantiates rule.metavariables ruleInstance.arguments rule.conclusion
        (dvLists substitutionPattern callerPattern calleePattern) := by
  cases application with
  | intro rule hlookup harguments hpremises hconclusion =>
      have hvalid := rule_isValidIn_of_lookup validatedSidePresentation hlookup
      have hshape := RuleSchema.conclusion_hasJudgmentShape_of_validIn hvalid
      have hmem : rule ∈ sideRules := by
        change rule ∈ validatedSidePresentation.1.rules
        exact List.mem_of_find?_eq_some hlookup
      have hrule : rule = dvListsNilRule ∨ rule = dvListsConsRule := by
        cases hconclusionRule : rule.conclusion with
        | apply sourceHead sourceArgs =>
            rw [hconclusionRule] at hconclusion
            have hhead : sourceHead = dvListsHead :=
              InstantiatesAt.apply_head_eq hconclusion
            have hselected : ruleConclusionIs dvListsHead rule = true := by
              simp [ruleConclusionIs, hconclusionRule, hhead]
            have hfiltered :
                rule ∈ sideRules.filter (ruleConclusionIs dvListsHead) :=
              List.mem_filter.mpr ⟨hmem, hselected⟩
            rw [dvListsRules_filter] at hfiltered
            simpa using hfiltered
        | bvar index =>
            rw [hconclusionRule] at hshape
            simp [Presentation.hasJudgmentShape] at hshape
        | fvar name =>
            rw [hconclusionRule] at hshape
            simp [Presentation.hasJudgmentShape] at hshape
        | lambda binder body =>
            rw [hconclusionRule] at hshape
            simp [Presentation.hasJudgmentShape] at hshape
        | multiLambda arity binders body =>
            rw [hconclusionRule] at hshape
            simp [Presentation.hasJudgmentShape] at hshape
        | subst body replacement =>
            rw [hconclusionRule] at hshape
            simp [Presentation.hasJudgmentShape] at hshape
        | collection collectionType elements rest =>
            rw [hconclusionRule] at hshape
            simp [Presentation.hasJudgmentShape] at hshape
      exact ⟨rule, hrule, hlookup, harguments, hpremises, hconclusion⟩

private theorem dvListsNil_application_inv
    {ruleInstance : RuleInstance} {premises : List Pattern}
    {substitution : FiniteSubstitution}
    {callerDV : List (String × String)}
    (application :
      RuleApplication validatedSidePresentation ruleInstance premises
        (dvLists (encodeSubstitution substitution) (EncodedDVPairs callerDV)
          (EncodedDVPairs []))) :
    premises = [] := by
  rcases dvListsApplication_decompose application with
    ⟨rule, hrule, hlookup, harguments, hpremises, hconclusion⟩
  rcases hrule with rfl | rfl
  · have hlength := argumentsValidAt_length_eq harguments
    rw [dvListsNilRule_eq_schema] at hlength
    simp [dvListsNilSchema] at hlength
    rcases List.length_eq_two.mp hlength with ⟨first, second, hargs⟩
    have hpremises' := instantiateSchemasAt?_complete hpremises
    simpa [hargs, dvListsNilRule_eq_schema, dvListsNilSchema, formal,
      metavariable, instantiateSchemasAt?] using hpremises'
  · have hlength := argumentsValidAt_length_eq harguments
    rw [dvListsConsRule_eq_schema] at hlength
    simp [dvListsConsSchema] at hlength
    rcases List.length_eq_eleven.mp hlength with
      ⟨first, second, third, fourth, fifth, sixth, seventh, eighth, ninth,
        tenth, eleventh, hargs⟩
    have hconclusion' := instantiateSchemaAt?_complete hconclusion
    simp [hargs, dvListsConsRule_eq_schema, dvListsConsSchema, formal,
      metavariable, instantiateSchemaAt?, instantiateSchemasAt?,
      lookupArgumentAt?, dvLists, EncodedDVPairs, encodeListWith]
      at hconclusion'

private theorem dvListsCons_application_inv
    {ruleInstance : RuleInstance} {premises : List Pattern}
    {substitution : FiniteSubstitution}
    {callerDV rest : List (String × String)} {left right : String}
    (application :
      RuleApplication validatedSidePresentation ruleInstance premises
        (dvLists (encodeSubstitution substitution) (EncodedDVPairs callerDV)
          (EncodedDVPairs ((left, right) :: rest)))) :
    ∃ typecode1 body1 typecode2 body2 variables1 variables2 : Pattern,
      premises =
        [ lookup (encodeSubstitution substitution) (encodeString left)
            typecode1 body1
        , lookup (encodeSubstitution substitution) (encodeString right)
            typecode2 body2
        , vars body1 variables1
        , vars body2 variables2
        , allPairs (EncodedDVPairs callerDV) variables1 variables2
        , dvLists (encodeSubstitution substitution) (EncodedDVPairs callerDV)
            (EncodedDVPairs rest) ] := by
  rcases dvListsApplication_decompose application with
    ⟨rule, hrule, hlookup, harguments, hpremises, hconclusion⟩
  rcases hrule with rfl | rfl
  · have hlength := argumentsValidAt_length_eq harguments
    rw [dvListsNilRule_eq_schema] at hlength
    simp [dvListsNilSchema] at hlength
    rcases List.length_eq_two.mp hlength with ⟨first, second, hargs⟩
    have hconclusion' := instantiateSchemaAt?_complete hconclusion
    simp [hargs, dvListsNilRule_eq_schema, dvListsNilSchema, formal,
      metavariable, instantiateSchemaAt?, instantiateSchemasAt?,
      lookupArgumentAt?, dvLists, EncodedDVPairs, encodeListWith]
      at hconclusion'
  · have hlength := argumentsValidAt_length_eq harguments
    rw [dvListsConsRule_eq_schema] at hlength
    simp [dvListsConsSchema] at hlength
    rcases List.length_eq_eleven.mp hlength with
      ⟨first, second, third, fourth, fifth, sixth, seventh, eighth, ninth,
        tenth, eleventh, hargs⟩
    have hpremises' := instantiateSchemasAt?_complete hpremises
    have hconclusion' := instantiateSchemaAt?_complete hconclusion
    simp [hargs, dvListsConsRule_eq_schema, dvListsConsSchema, formal,
      metavariable, instantiateSchemasAt?, instantiateSchemaAt?,
      lookupArgumentAt?, lookup, vars, allPairs, dvLists, EncodedDVPairs,
      encodeListWith, encodeDVPair] at hpremises' hconclusion'
    refine ⟨sixth, seventh, eighth, ninth, tenth, eleventh, ?_⟩
    simpa [lookup, vars, allPairs, dvLists, EncodedDVPairs,
      hconclusion'.1, hconclusion'.2.1, hconclusion'.2.2.1.1,
      hconclusion'.2.2.1.2, hconclusion'.2.2.2] using hpremises'.symm

private theorem dvLists_derivation_sound
    (substitution : FiniteSubstitution)
    (callerDV calleeDV : List (String × String))
    (derivation :
      Derivation validatedSidePresentation
        (dvLists (encodeSubstitution substitution) (EncodedDVPairs callerDV)
          (EncodedDVPairs calleeDV))) :
    DVListsSemantics substitution callerDV calleeDV := by
  induction calleeDV with
  | nil =>
      intro pair hmem
      simp at hmem
  | cons pair rest ih =>
      rcases pair with ⟨left, right⟩
      cases derivation with
      | byRule ruleInstance application children =>
          rcases dvListsCons_application_inv application with
            ⟨typecode1, body1, typecode2, body2, variables1, variables2,
              hpremises⟩
          rw [hpremises] at children
          cases children with
          | cons leftLookupChild remaining =>
              cases remaining with
              | cons rightLookupChild remaining =>
                  cases remaining with
                  | cons leftVarsChild remaining =>
                      cases remaining with
                      | cons rightVarsChild remaining =>
                          cases remaining with
                          | cons pairsChild remaining =>
                              cases remaining with
                              | cons tailChild remaining =>
                                  cases remaining with
                                  | nil =>
                                      rcases lookup_derivation_decodes
                                          substitution left typecode1 body1
                                          leftLookupChild with
                                        ⟨leftReplacement, leftLookup, _,
                                          leftBody⟩
                                      rcases lookup_derivation_decodes
                                          substitution right typecode2 body2
                                          rightLookupChild with
                                        ⟨rightReplacement, rightLookup, _,
                                          rightBody⟩
                                      rw [leftBody] at leftVarsChild
                                      rw [rightBody] at rightVarsChild
                                      have leftVariables :=
                                        vars_derivation_decodes
                                          leftReplacement.body variables1
                                          leftVarsChild
                                      have rightVariables :=
                                        vars_derivation_decodes
                                          rightReplacement.body variables2
                                          rightVarsChild
                                      rw [leftVariables, rightVariables]
                                        at pairsChild
                                      have pairSemantics :=
                                        (allPairs_derivation_iff callerDV
                                          (BodyVariables leftReplacement.body)
                                          (BodyVariables rightReplacement.body)).mp
                                            ⟨pairsChild⟩
                                      have tailSemantics := ih tailChild
                                      intro queriedPair hmem
                                      rcases List.mem_cons.mp hmem with
                                        hhead | htail
                                      · subst queriedPair
                                        exact ⟨leftReplacement,
                                          rightReplacement, leftLookup,
                                          rightLookup, pairSemantics⟩
                                      · exact tailSemantics queriedPair htail

/-- DVLists derivability is exactly the independent ordinary-list DV
substitution condition. -/
theorem dvLists_derivation_iff (substitution : FiniteSubstitution)
    (callerDV calleeDV : List (String × String)) :
    Nonempty
        (Derivation validatedSidePresentation
          (dvLists (encodeSubstitution substitution) (EncodedDVPairs callerDV)
            (EncodedDVPairs calleeDV))) ↔
      DVListsSemantics substitution callerDV calleeDV := by
  constructor
  · rintro ⟨derivation⟩
    exact dvLists_derivation_sound substitution callerDV calleeDV derivation
  · exact dvLists_derivable substitution callerDV calleeDV

private theorem dvOK_instantiates (substitution : FiniteSubstitution)
    (callerFrame calleeFrame : RuntimeFrame) :
    instantiateRule? validatedSidePresentation
        { ruleId := ruleId "$mm.dv-ok.frames"
          arguments :=
            [ encodeSubstitution substitution
            , EncodedDVPairs callerFrame.dj.toList
            , EncodedNames callerFrame.hyps.toList
            , EncodedDVPairs calleeFrame.dj.toList
            , EncodedNames calleeFrame.hyps.toList ] } =
      some
        ( [dvLists (encodeSubstitution substitution)
            (EncodedDVPairs callerFrame.dj.toList)
            (EncodedDVPairs calleeFrame.dj.toList)]
        , dvOK (encodeSubstitution substitution) (encodeFrame callerFrame)
            (encodeFrame calleeFrame) ) := by
  simp [instantiateRule?, lookup_dvOKRule, dvOKRule_eq_schema, dvOKSchema,
    formal, metavariable, argumentsValidAt, argumentValidAt,
    instantiateSchemas?, instantiateSchemasAt?, instantiateSchema?,
    instantiateSchemaAt?, lookupArgumentAt?, dvLists, dvListsHead, dvOK,
    dvOKHead, encodeFrame, EncodedDVPairs, EncodedNames]

private theorem dvOK_derivable (substitution : FiniteSubstitution)
    (callerFrame calleeFrame : RuntimeFrame)
    (semantics : DVOKSemantics substitution callerFrame calleeFrame) :
    Nonempty
      (Derivation validatedSidePresentation
        (dvOK (encodeSubstitution substitution) (encodeFrame callerFrame)
          (encodeFrame calleeFrame))) := by
  rcases dvLists_derivable substitution callerFrame.dj.toList
      calleeFrame.dj.toList semantics with ⟨child⟩
  let ruleInstance : RuleInstance :=
    { ruleId := ruleId "$mm.dv-ok.frames"
      arguments :=
        [ encodeSubstitution substitution
        , EncodedDVPairs callerFrame.dj.toList
        , EncodedNames callerFrame.hyps.toList
        , EncodedDVPairs calleeFrame.dj.toList
        , EncodedNames calleeFrame.hyps.toList ] }
  have happlication :
      RuleApplication validatedSidePresentation ruleInstance
        [dvLists (encodeSubstitution substitution)
          (EncodedDVPairs callerFrame.dj.toList)
          (EncodedDVPairs calleeFrame.dj.toList)]
        (dvOK (encodeSubstitution substitution) (encodeFrame callerFrame)
          (encodeFrame calleeFrame)) :=
    instantiateRule?_eq_some_iff_application.mp
      (dvOK_instantiates substitution callerFrame calleeFrame)
  exact ⟨Derivation.byRule ruleInstance happlication (.cons child .nil)⟩

private theorem dvOKApplication_decompose
    {ruleInstance : RuleInstance} {premises : List Pattern}
    {substitutionPattern callerPattern calleePattern : Pattern}
    (application :
      RuleApplication validatedSidePresentation ruleInstance premises
        (dvOK substitutionPattern callerPattern calleePattern)) :
    ∃ rule : RuleSchema,
      rule = dvOKRule ∧
      validatedSidePresentation.1.lookupRule? ruleInstance.ruleId = some rule ∧
      argumentsValidAt rule.metavariables ruleInstance.arguments = true ∧
      InstantiatesList rule.metavariables ruleInstance.arguments
        rule.premises premises ∧
      Instantiates rule.metavariables ruleInstance.arguments rule.conclusion
        (dvOK substitutionPattern callerPattern calleePattern) := by
  cases application with
  | intro rule hlookup harguments hpremises hconclusion =>
      have hvalid := rule_isValidIn_of_lookup validatedSidePresentation hlookup
      have hshape := RuleSchema.conclusion_hasJudgmentShape_of_validIn hvalid
      have hmem : rule ∈ sideRules := by
        change rule ∈ validatedSidePresentation.1.rules
        exact List.mem_of_find?_eq_some hlookup
      have hrule : rule = dvOKRule := by
        cases hconclusionRule : rule.conclusion with
        | apply sourceHead sourceArgs =>
            rw [hconclusionRule] at hconclusion
            have hhead : sourceHead = dvOKHead :=
              InstantiatesAt.apply_head_eq hconclusion
            have hselected : ruleConclusionIs dvOKHead rule = true := by
              simp [ruleConclusionIs, hconclusionRule, hhead]
            have hfiltered :
                rule ∈ sideRules.filter (ruleConclusionIs dvOKHead) :=
              List.mem_filter.mpr ⟨hmem, hselected⟩
            rw [dvOKRules_filter] at hfiltered
            simpa using hfiltered
        | bvar index =>
            rw [hconclusionRule] at hshape
            simp [Presentation.hasJudgmentShape] at hshape
        | fvar name =>
            rw [hconclusionRule] at hshape
            simp [Presentation.hasJudgmentShape] at hshape
        | lambda binder body =>
            rw [hconclusionRule] at hshape
            simp [Presentation.hasJudgmentShape] at hshape
        | multiLambda arity binders body =>
            rw [hconclusionRule] at hshape
            simp [Presentation.hasJudgmentShape] at hshape
        | subst body replacement =>
            rw [hconclusionRule] at hshape
            simp [Presentation.hasJudgmentShape] at hshape
        | collection collectionType elements rest =>
            rw [hconclusionRule] at hshape
            simp [Presentation.hasJudgmentShape] at hshape
      exact ⟨rule, hrule, hlookup, harguments, hpremises, hconclusion⟩

private theorem dvOK_application_inv
    {ruleInstance : RuleInstance} {premises : List Pattern}
    {substitution : FiniteSubstitution}
    {callerFrame calleeFrame : RuntimeFrame}
    (application :
      RuleApplication validatedSidePresentation ruleInstance premises
        (dvOK (encodeSubstitution substitution) (encodeFrame callerFrame)
          (encodeFrame calleeFrame))) :
    premises =
      [dvLists (encodeSubstitution substitution)
        (EncodedDVPairs callerFrame.dj.toList)
        (EncodedDVPairs calleeFrame.dj.toList)] := by
  rcases dvOKApplication_decompose application with
    ⟨rule, rfl, hlookup, harguments, hpremises, hconclusion⟩
  have hlength := argumentsValidAt_length_eq harguments
  rw [dvOKRule_eq_schema] at hlength
  simp [dvOKSchema] at hlength
  rcases List.length_eq_five.mp hlength with
    ⟨first, second, third, fourth, fifth, hargs⟩
  have hpremises' := instantiateSchemasAt?_complete hpremises
  have hconclusion' := instantiateSchemaAt?_complete hconclusion
  simp [hargs, dvOKRule_eq_schema, dvOKSchema, formal, metavariable,
    instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?,
    dvLists, dvOK, encodeFrame] at hpremises' hconclusion'
  simpa [dvLists, EncodedDVPairs, hconclusion'.1,
    hconclusion'.2.1.1, hconclusion'.2.2.1] using hpremises'.symm

/-- DVOK derivability on canonical substitutions and frames is exactly the
independent ordinary-list DV semantics. -/
theorem dvOK_derivation_iff (substitution : FiniteSubstitution)
    (callerFrame calleeFrame : RuntimeFrame) :
    Nonempty
        (Derivation validatedSidePresentation
          (dvOK (encodeSubstitution substitution) (encodeFrame callerFrame)
            (encodeFrame calleeFrame))) ↔
      DVOKSemantics substitution callerFrame calleeFrame := by
  constructor
  · rintro ⟨derivation⟩
    cases derivation with
    | byRule ruleInstance application children =>
        have hpremises := dvOK_application_inv application
        rw [hpremises] at children
        cases children with
        | cons child remaining =>
            cases remaining with
            | nil =>
                exact dvLists_derivation_sound substitution
                  callerFrame.dj.toList calleeFrame.dj.toList child
  · exact dvOK_derivable substitution callerFrame calleeFrame

/-- A nonempty singleton callee DV constraint is derivable whenever the two
bindings exist and their extracted variable cross-product is caller-disjoint. -/
theorem dvOK_singleton_derivable (substitution : FiniteSubstitution)
    (callerFrame : RuntimeFrame) (calleeHypotheses : List String)
    (left right : String)
    (leftReplacement rightReplacement : ConstantHeadedFormula)
    (leftLookup : LookupSemantics substitution left leftReplacement)
    (rightLookup : LookupSemantics substitution right rightReplacement)
    (pairSemantics :
      AllPairsSemantics callerFrame.dj.toList
        (BodyVariables leftReplacement.body)
        (BodyVariables rightReplacement.body)) :
    Nonempty
      (Derivation validatedSidePresentation
        (dvOK (encodeSubstitution substitution) (encodeFrame callerFrame)
          (encodeFrame
            { dj := [(left, right)].toArray
              hyps := calleeHypotheses.toArray }))) := by
  apply (dvOK_derivation_iff substitution callerFrame
    { dj := [(left, right)].toArray
      hyps := calleeHypotheses.toArray }).mpr
  intro pair hmem
  have hpair : pair = (left, right) := by simpa using hmem
  subst pair
  exact ⟨leftReplacement, rightReplacement, leftLookup, rightLookup,
    pairSemantics⟩

/-- Missing either endpoint binding prevents a singleton DVOK derivation. -/
theorem dvOK_missing_left_binding_not_derivable
    (substitution : FiniteSubstitution) (callerFrame : RuntimeFrame)
    (calleeHypotheses : List String) (left right : String)
    (hmissing :
      ∀ replacement : ConstantHeadedFormula,
        ¬LookupSemantics substitution left replacement) :
    ¬Nonempty
      (Derivation validatedSidePresentation
        (dvOK (encodeSubstitution substitution) (encodeFrame callerFrame)
          (encodeFrame
            { dj := [(left, right)].toArray
              hyps := calleeHypotheses.toArray }))) := by
  intro derivable
  have semantics :=
    (dvOK_derivation_iff substitution callerFrame
      { dj := [(left, right)].toArray
        hyps := calleeHypotheses.toArray }).mp derivable
  rcases semantics (left, right) (by simp) with
    ⟨leftReplacement, rightReplacement, leftLookup, rightLookup,
      pairSemantics⟩
  exact hmissing leftReplacement leftLookup

/-- The caller-pair invariant needed to add the inequality omitted by the
generated symmetric-membership rules. -/
def DVPairNamesDistinct (pairs : List (String × String)) : Prop :=
  ∀ pair ∈ pairs, pair.1 ≠ pair.2

/-- The strict-orientation Boolean established by parser/projection
well-scopedness is sufficient for the no-self bridge invariant. -/
theorem dvPairNamesDistinct_of_strictOrderAll
    (pairs : List (String × String))
    (hstrict :
      pairs.all (fun pair => decide (pair.1 < pair.2)) = true) :
    DVPairNamesDistinct pairs := by
  intro pair hmem
  have hlt : pair.1 < pair.2 := by
    simpa using (List.all_eq_true.mp hstrict) pair hmem
  exact ne_of_lt hlt

/-- Convert the string-pair carrier used by inference encodings to the live
declarative Metamath variable-pair carrier. -/
def ToSpecDVPairs (pairs : List (String × String)) :
    List (Metamath.Spec.Variable × Metamath.Spec.Variable) :=
  pairs.map fun pair => (⟨pair.1⟩, ⟨pair.2⟩)

@[simp] theorem mem_toSpecDVPairs_iff (pairs : List (String × String))
    (left right : String) :
    ((⟨left⟩, ⟨right⟩) :
        Metamath.Spec.Variable × Metamath.Spec.Variable) ∈
        ToSpecDVPairs pairs ↔
      (left, right) ∈ pairs := by
  simp [ToSpecDVPairs]

/-- Under the source-validity no-self invariant, the generated DV relation is
exactly the live declarative Metamath `dvRel`. -/
theorem dvRelation_iff_spec_dvRel
    (pairs : List (String × String))
    (hdistinct : DVPairNamesDistinct pairs) (left right : String) :
    DVRelation pairs left right ↔
      Metamath.Spec.dvRel (ToSpecDVPairs pairs) ⟨left⟩ ⟨right⟩ := by
  constructor
  · intro relation
    have hnames : left ≠ right := by
      intro heq
      subst right
      rcases relation with hforward | hreverse
      · exact hdistinct (left, left) hforward rfl
      · exact hdistinct (left, left) hreverse rfl
    constructor
    · intro hvariables
      exact hnames (congrArg Metamath.Spec.Variable.v hvariables)
    · rcases relation with hforward | hreverse
      · exact Or.inl ((mem_toSpecDVPairs_iff pairs left right).mpr hforward)
      · exact Or.inr ((mem_toSpecDVPairs_iff pairs right left).mpr hreverse)
  · intro relation
    rcases relation.2 with hforward | hreverse
    · exact Or.inl ((mem_toSpecDVPairs_iff pairs left right).mp hforward)
    · exact Or.inr ((mem_toSpecDVPairs_iff pairs right left).mp hreverse)

/-- The DV-list semantics already supplies the pointwise live declarative DV
relation once caller pairs are known to exclude self-pairs.  Relating this to
`Spec.dvOK` additionally requires a total substitution and the runtime
variable-classification invariant. -/
theorem dvListsSemantics_implies_spec_dvRel
    (substitution : FiniteSubstitution)
    (callerDV calleeDV : List (String × String))
    (hdistinct : DVPairNamesDistinct callerDV)
    (semantics : DVListsSemantics substitution callerDV calleeDV)
    (pair : String × String) (hpair : pair ∈ calleeDV) :
    ∃ leftReplacement rightReplacement : ConstantHeadedFormula,
      LookupSemantics substitution pair.1 leftReplacement ∧
      LookupSemantics substitution pair.2 rightReplacement ∧
      ∀ left ∈ BodyVariables leftReplacement.body,
        ∀ right ∈ BodyVariables rightReplacement.body,
          Metamath.Spec.dvRel (ToSpecDVPairs callerDV) ⟨left⟩ ⟨right⟩ := by
  rcases semantics pair hpair with
    ⟨leftReplacement, rightReplacement, leftLookup, rightLookup,
      allPairsSemantics⟩
  refine ⟨leftReplacement, rightReplacement, leftLookup, rightLookup, ?_⟩
  intro left hleft right hright
  exact (dvRelation_iff_spec_dvRel callerDV hdistinct left right).mp
    (allPairsSemantics left hleft right hright)

/-- A full bridge from the independent side semantics to declarative
Metamath `dvOK`.  The explicit classification hypothesis is the exact missing
link between tagged runtime symbols and `Spec.varsInExpr`'s active-name
classification. -/
theorem dvOKSemantics_implies_spec_dvOK
    (substitution : FiniteSubstitution)
    (callerFrame calleeFrame : RuntimeFrame)
    (activeVariables : List Metamath.Spec.Variable)
    (specSubstitution : Metamath.Spec.Subst)
    (hdistinct : DVPairNamesDistinct callerFrame.dj.toList)
    (hclassification :
      ∀ name replacement,
        LookupSemantics substitution name replacement →
        Metamath.Spec.varsInExpr activeVariables
            (specSubstitution ⟨name⟩) =
          (BodyVariables replacement.body).map fun variableName =>
            (⟨variableName⟩ : Metamath.Spec.Variable))
    (semantics : DVOKSemantics substitution callerFrame calleeFrame) :
    Metamath.Spec.dvOK activeVariables
      (ToSpecDVPairs calleeFrame.dj.toList)
      (ToSpecDVPairs callerFrame.dj.toList) specSubstitution := by
  unfold Metamath.Spec.dvOK
  intro leftVariable rightVariable hpair
  rcases leftVariable with ⟨left⟩
  rcases rightVariable with ⟨right⟩
  have hpairNames : (left, right) ∈ calleeFrame.dj.toList :=
    (mem_toSpecDVPairs_iff calleeFrame.dj.toList left right).mp hpair
  rcases semantics (left, right) hpairNames with
    ⟨leftReplacement, rightReplacement, leftLookup, rightLookup,
      pairSemantics⟩
  dsimp only
  rw [hclassification left leftReplacement leftLookup,
    hclassification right rightReplacement rightLookup]
  intro leftResult hleft rightResult hright
  rcases List.mem_map.mp hleft with
    ⟨leftName, hleftName, hleftResult⟩
  rcases List.mem_map.mp hright with
    ⟨rightName, hrightName, hrightResult⟩
  subst leftResult
  subst rightResult
  exact (dvRelation_iff_spec_dvRel callerFrame.dj.toList hdistinct
    leftName rightName).mp
      (pairSemantics leftName hleftName rightName hrightName)

/-- Canonical DVOK derivations therefore imply declarative Metamath `dvOK`
under the same explicit projection invariants. -/
theorem dvOK_derivation_implies_spec_dvOK
    (substitution : FiniteSubstitution)
    (callerFrame calleeFrame : RuntimeFrame)
    (activeVariables : List Metamath.Spec.Variable)
    (specSubstitution : Metamath.Spec.Subst)
    (hdistinct : DVPairNamesDistinct callerFrame.dj.toList)
    (hclassification :
      ∀ name replacement,
        LookupSemantics substitution name replacement →
        Metamath.Spec.varsInExpr activeVariables
            (specSubstitution ⟨name⟩) =
          (BodyVariables replacement.body).map fun variableName =>
            (⟨variableName⟩ : Metamath.Spec.Variable))
    (derivable :
      Nonempty
        (Derivation validatedSidePresentation
          (dvOK (encodeSubstitution substitution) (encodeFrame callerFrame)
            (encodeFrame calleeFrame)))) :
    Metamath.Spec.dvOK activeVariables
      (ToSpecDVPairs calleeFrame.dj.toList)
      (ToSpecDVPairs callerFrame.dj.toList) specSubstitution :=
  dvOKSemantics_implies_spec_dvOK substitution callerFrame calleeFrame
    activeVariables specSubstitution hdistinct hclassification
    ((dvOK_derivation_iff substitution callerFrame calleeFrame).mp derivable)

end Mettapedia.Languages.Metamath.InferenceSideConditionsSemantics
