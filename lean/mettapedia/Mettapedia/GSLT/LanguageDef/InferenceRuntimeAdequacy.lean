import Mettapedia.GSLT.LanguageDef.InferenceLanguageWireFormat

/-!
# Adequacy of the closed-payload inference runtime

The catalog runtime checks one property beyond the foundation-neutral
inference checker: every fixed application appearing in an article argument
must belong to the catalog's declared constructor vocabulary at the declared
arity.  This module makes that restriction explicit and proves that it is the
only acceptance gap.

Consequently, a proof whose complete argument payload is closed under the
catalog vocabulary is accepted by runtime replay exactly when it is accepted
by the validated generic definition.
-/

namespace Mettapedia.GSLT.LanguageDef.InferenceLanguageWire

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.InferenceLanguageWire

namespace RuntimeInferenceLanguage

mutual

/-- Every rule argument in a raw article uses only constructors admitted by
the runtime catalog. -/
def proofPayloadsValid (definition : RuntimeInferenceLanguage) :
    RawProof → Bool
  | .node ruleInstance children =>
      definition.fixedConstructorListsValid ruleInstance.arguments &&
        definition.proofPayloadListsValid children
termination_by proof => sizeOf proof

def proofPayloadListsValid (definition : RuntimeInferenceLanguage) :
    List RawProof → Bool
  | [] => true
  | proof :: proofs =>
      definition.proofPayloadsValid proof &&
        definition.proofPayloadListsValid proofs
termination_by proofs => sizeOf proofs

end

/-- Generic binder validity plus closed constructor vocabulary is exactly the
runtime argument profile. -/
theorem argumentsValidAt_complete (definition : RuntimeInferenceLanguage) :
    ∀ (formals : List (String × Nat)) (arguments : List Pattern),
      InferenceChecker.argumentsValidAt formals arguments = true →
      definition.fixedConstructorListsValid arguments = true →
      definition.argumentsValidAt formals arguments = true := by
  intro formals
  induction formals with
  | nil =>
      intro arguments genericValid constructorsValid
      cases arguments with
      | nil => rfl
      | cons argument arguments =>
          simp [InferenceChecker.argumentsValidAt] at genericValid
  | cons formal formals inductionHypothesis =>
      intro arguments genericValid constructorsValid
      cases arguments with
      | nil =>
          simp [InferenceChecker.argumentsValidAt] at genericValid
      | cons argument arguments =>
          simp only [InferenceChecker.argumentsValidAt, Bool.and_eq_true]
            at genericValid
          simp only [RuntimeInferenceLanguage.fixedConstructorListsValid,
            Bool.and_eq_true] at constructorsValid
          simp only [RuntimeInferenceLanguage.argumentsValidAt,
            RuntimeInferenceLanguage.argumentValidAt, Bool.and_eq_true]
          exact
            ⟨⟨genericValid.1, constructorsValid.1⟩,
              inductionHypothesis arguments genericValid.2
                constructorsValid.2⟩

/-- A generic local rule application whose payload is vocabulary-closed is
replayed identically by the stricter runtime projection. -/
theorem instantiateRule?_complete
    (definition : ValidatedCalculusLanguageDef) (ruleInstance : RuleInstance)
    (premises : List Pattern) (conclusion : Pattern)
    (genericResult :
      InferenceChecker.instantiateRule? definition ruleInstance =
        some (premises, conclusion))
    (payloadValid :
      (RuntimeInferenceLanguage.ofDefinition definition.1).fixedConstructorListsValid
        ruleInstance.arguments = true) :
    (RuntimeInferenceLanguage.ofDefinition definition.1).instantiateRule?
        ruleInstance = some (premises, conclusion) := by
  simp only [InferenceChecker.instantiateRule?] at genericResult
  cases lookup : definition.1.lookupRule? ruleInstance.ruleId with
  | none => simp [lookup] at genericResult
  | some rule =>
      rw [lookup] at genericResult
      cases genericArguments :
          InferenceChecker.argumentsValidAt
            rule.metavariables ruleInstance.arguments with
      | false => simp [genericArguments] at genericResult
      | true =>
          have runtimeArguments :
              (RuntimeInferenceLanguage.ofDefinition definition.1).argumentsValidAt
                  rule.metavariables ruleInstance.arguments = true :=
            RuntimeInferenceLanguage.argumentsValidAt_complete
              (RuntimeInferenceLanguage.ofDefinition definition.1)
              rule.metavariables ruleInstance.arguments genericArguments
              payloadValid
          simpa [RuntimeInferenceLanguage.instantiateRule?,
            RuntimeInferenceLanguage.ofDefinition_lookupRule?, lookup,
            genericArguments, runtimeArguments] using genericResult

mutual

/-- On a vocabulary-closed article, generic acceptance is complete for the
closed-payload runtime checker. -/
theorem checkRaw_complete
    (definition : ValidatedCalculusLanguageDef) (goal : Pattern) (proof : RawProof)
    (genericAccepted :
      InferenceChecker.checkRaw definition goal proof = true)
    (payloadValid :
      (RuntimeInferenceLanguage.ofDefinition definition.1).proofPayloadsValid
        proof = true) :
    (RuntimeInferenceLanguage.ofDefinition definition.1).checkRaw
        goal proof = true := by
  cases proof with
  | node ruleInstance children =>
      simp only [InferenceChecker.checkRaw] at genericAccepted
      simp only [RuntimeInferenceLanguage.proofPayloadsValid, Bool.and_eq_true]
        at payloadValid
      cases genericResult :
          InferenceChecker.instantiateRule? definition ruleInstance with
      | none => simp [genericResult] at genericAccepted
      | some result =>
          rcases result with ⟨premises, conclusion⟩
          simp only [genericResult, Bool.and_eq_true, decide_eq_true_eq]
            at genericAccepted
          have runtimeResult := RuntimeInferenceLanguage.instantiateRule?_complete
            definition ruleInstance premises conclusion genericResult
              payloadValid.1
          simp only [RuntimeInferenceLanguage.checkRaw, runtimeResult,
            Bool.and_eq_true, decide_eq_true_eq]
          exact
            ⟨genericAccepted.1,
              RuntimeInferenceLanguage.checkRawChildren_complete definition
                premises children genericAccepted.2 payloadValid.2⟩
termination_by sizeOf proof

theorem checkRawChildren_complete
    (definition : ValidatedCalculusLanguageDef) (premises : List Pattern)
    (proofs : List RawProof)
    (genericAccepted :
      InferenceChecker.checkRawChildren definition premises proofs = true)
    (payloadValid :
      (RuntimeInferenceLanguage.ofDefinition definition.1).proofPayloadListsValid
        proofs = true) :
    (RuntimeInferenceLanguage.ofDefinition definition.1).checkRawChildren
        premises proofs = true := by
  cases premises with
  | nil =>
      cases proofs with
      | nil => simp [RuntimeInferenceLanguage.checkRawChildren]
      | cons proof proofs =>
          simp [InferenceChecker.checkRawChildren] at genericAccepted
  | cons premise premises =>
      cases proofs with
      | nil =>
          simp [InferenceChecker.checkRawChildren] at genericAccepted
      | cons proof proofs =>
          simp only [InferenceChecker.checkRawChildren, Bool.and_eq_true]
            at genericAccepted
          simp only [RuntimeInferenceLanguage.proofPayloadListsValid,
            Bool.and_eq_true] at payloadValid
          simp only [RuntimeInferenceLanguage.checkRawChildren, Bool.and_eq_true]
          exact
            ⟨RuntimeInferenceLanguage.checkRaw_complete definition premise proof
                genericAccepted.1 payloadValid.1,
              RuntimeInferenceLanguage.checkRawChildren_complete definition
                premises proofs genericAccepted.2 payloadValid.2⟩
termination_by sizeOf proofs

end


/-- The closed-payload runtime and generic NIK replay agree exactly whenever
the article carries only declared fixed constructors. -/
theorem checkRaw_iff_generic_of_payloadsValid
    (definition : ValidatedCalculusLanguageDef) (goal : Pattern) (proof : RawProof)
    (payloadValid :
      (RuntimeInferenceLanguage.ofDefinition definition.1).proofPayloadsValid
        proof = true) :
    (RuntimeInferenceLanguage.ofDefinition definition.1).checkRaw
          goal proof = true ↔
      InferenceChecker.checkRaw definition goal proof = true := by
  constructor
  · exact RuntimeInferenceLanguage.checkRaw_sound definition goal proof
  · intro genericAccepted
    exact RuntimeInferenceLanguage.checkRaw_complete definition goal proof
      genericAccepted payloadValid

private def payloadCanaryPresentation : RuntimeInferenceLanguage :=
  { constructors :=
      [{ head := "Declared", arity := 0 }, { head := "Unary", arity := 1 }]
    judgments := []
    rules := []
    conversion := none }

private def payloadCanaryProof (constructor : String) : RawProof :=
  .node ⟨⟨"canary"⟩, [.apply constructor []]⟩ []

/-- A declared nullary atom is retained by the closed-payload profile. -/
theorem declared_payload_is_valid :
    payloadCanaryPresentation.proofPayloadsValid
      (payloadCanaryProof "Declared") = true := by
  simp [payloadCanaryPresentation, payloadCanaryProof,
    RuntimeInferenceLanguage.proofPayloadsValid,
    RuntimeInferenceLanguage.proofPayloadListsValid,
    RuntimeInferenceLanguage.fixedConstructorListsValid,
    RuntimeInferenceLanguage.fixedConstructorsValid,
    RuntimeInferenceLanguage.constructorApplicationValid]

/-- Open atom data does not enlarge the authority's structural vocabulary. -/
theorem opaque_nullary_payload_is_valid :
    payloadCanaryPresentation.proofPayloadsValid
      (payloadCanaryProof "OpaqueAtom") = true := by
  simp [payloadCanaryPresentation, payloadCanaryProof,
    RuntimeInferenceLanguage.proofPayloadsValid,
    RuntimeInferenceLanguage.proofPayloadListsValid,
    RuntimeInferenceLanguage.fixedConstructorListsValid,
    RuntimeInferenceLanguage.fixedConstructorsValid,
    RuntimeInferenceLanguage.constructorApplicationValid]

/-- A declared structural head cannot be reinterpreted as nullary atom data. -/
theorem declared_wrong_arity_payload_is_invalid :
    payloadCanaryPresentation.proofPayloadsValid
      (payloadCanaryProof "Unary") = false := by
  simp [payloadCanaryPresentation, payloadCanaryProof,
    RuntimeInferenceLanguage.proofPayloadsValid,
    RuntimeInferenceLanguage.proofPayloadListsValid,
    RuntimeInferenceLanguage.fixedConstructorListsValid,
    RuntimeInferenceLanguage.fixedConstructorsValid,
    RuntimeInferenceLanguage.constructorApplicationValid]

private def payloadCanaryStructuralProof : RawProof :=
  .node ⟨⟨"canary"⟩,
    [.apply "Undeclared" [.apply "OpaqueAtom" []]]⟩ []

/-- The extra runtime premise remains substantive: an undeclared structural
constructor is rejected before rule replay. -/
theorem undeclared_structural_payload_is_invalid :
    payloadCanaryPresentation.proofPayloadsValid
      payloadCanaryStructuralProof = false := by
  simp [payloadCanaryPresentation, payloadCanaryStructuralProof,
    RuntimeInferenceLanguage.proofPayloadsValid,
    RuntimeInferenceLanguage.proofPayloadListsValid,
    RuntimeInferenceLanguage.fixedConstructorListsValid,
    RuntimeInferenceLanguage.fixedConstructorsValid,
    RuntimeInferenceLanguage.constructorApplicationValid]

end RuntimeInferenceLanguage

end Mettapedia.GSLT.LanguageDef.InferenceLanguageWire
