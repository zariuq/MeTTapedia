import Mettapedia.GSLT.LanguageDef.InferencePresentationWireFormat

/-!
# Adequacy of the closed-payload inference runtime

The catalog runtime checks one property beyond the foundation-neutral
inference checker: every fixed application appearing in an article argument
must belong to the catalog's declared constructor vocabulary at the declared
arity.  This module makes that restriction explicit and proves that it is the
only acceptance gap.

Consequently, a proof whose complete argument payload is closed under the
catalog vocabulary is accepted by runtime replay exactly when it is accepted
by the validated generic presentation.
-/

namespace Mettapedia.GSLT.LanguageDef.InferencePresentationWire

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.InferencePresentationWire

namespace RuntimePresentation

mutual

/-- Every rule argument in a raw article uses only constructors admitted by
the runtime catalog. -/
def proofPayloadsValid (presentation : RuntimePresentation) :
    RawProof → Bool
  | .node ruleInstance children =>
      presentation.fixedConstructorListsValid ruleInstance.arguments &&
        presentation.proofPayloadListsValid children
termination_by proof => sizeOf proof

def proofPayloadListsValid (presentation : RuntimePresentation) :
    List RawProof → Bool
  | [] => true
  | proof :: proofs =>
      presentation.proofPayloadsValid proof &&
        presentation.proofPayloadListsValid proofs
termination_by proofs => sizeOf proofs

end

/-- Generic binder validity plus closed constructor vocabulary is exactly the
runtime argument profile. -/
theorem argumentsValidAt_complete (presentation : RuntimePresentation) :
    ∀ (formals : List (String × Nat)) (arguments : List Pattern),
      InferenceChecker.argumentsValidAt formals arguments = true →
      presentation.fixedConstructorListsValid arguments = true →
      presentation.argumentsValidAt formals arguments = true := by
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
          simp only [RuntimePresentation.fixedConstructorListsValid,
            Bool.and_eq_true] at constructorsValid
          simp only [RuntimePresentation.argumentsValidAt,
            RuntimePresentation.argumentValidAt, Bool.and_eq_true]
          exact
            ⟨⟨genericValid.1, constructorsValid.1⟩,
              inductionHypothesis arguments genericValid.2
                constructorsValid.2⟩

/-- A generic local rule application whose payload is vocabulary-closed is
replayed identically by the stricter runtime projection. -/
theorem instantiateRule?_complete
    (presentation : ValidatedPresentation) (ruleInstance : RuleInstance)
    (premises : List Pattern) (conclusion : Pattern)
    (genericResult :
      InferenceChecker.instantiateRule? presentation ruleInstance =
        some (premises, conclusion))
    (payloadValid :
      (RuntimePresentation.ofPresentation presentation.1).fixedConstructorListsValid
        ruleInstance.arguments = true) :
    (RuntimePresentation.ofPresentation presentation.1).instantiateRule?
        ruleInstance = some (premises, conclusion) := by
  simp only [InferenceChecker.instantiateRule?] at genericResult
  cases lookup : presentation.1.lookupRule? ruleInstance.ruleId with
  | none => simp [lookup] at genericResult
  | some rule =>
      rw [lookup] at genericResult
      cases genericArguments :
          InferenceChecker.argumentsValidAt
            rule.metavariables ruleInstance.arguments with
      | false => simp [genericArguments] at genericResult
      | true =>
          have runtimeArguments :
              (RuntimePresentation.ofPresentation presentation.1).argumentsValidAt
                  rule.metavariables ruleInstance.arguments = true :=
            RuntimePresentation.argumentsValidAt_complete
              (RuntimePresentation.ofPresentation presentation.1)
              rule.metavariables ruleInstance.arguments genericArguments
              payloadValid
          simpa [RuntimePresentation.instantiateRule?,
            RuntimePresentation.ofPresentation_lookupRule?, lookup,
            genericArguments, runtimeArguments] using genericResult

mutual

/-- On a vocabulary-closed article, generic acceptance is complete for the
closed-payload runtime checker. -/
theorem checkRaw_complete
    (presentation : ValidatedPresentation) (goal : Pattern) (proof : RawProof)
    (genericAccepted :
      InferenceChecker.checkRaw presentation goal proof = true)
    (payloadValid :
      (RuntimePresentation.ofPresentation presentation.1).proofPayloadsValid
        proof = true) :
    (RuntimePresentation.ofPresentation presentation.1).checkRaw
        goal proof = true := by
  cases proof with
  | node ruleInstance children =>
      simp only [InferenceChecker.checkRaw] at genericAccepted
      simp only [RuntimePresentation.proofPayloadsValid, Bool.and_eq_true]
        at payloadValid
      cases genericResult :
          InferenceChecker.instantiateRule? presentation ruleInstance with
      | none => simp [genericResult] at genericAccepted
      | some result =>
          rcases result with ⟨premises, conclusion⟩
          simp only [genericResult, Bool.and_eq_true, decide_eq_true_eq]
            at genericAccepted
          have runtimeResult := RuntimePresentation.instantiateRule?_complete
            presentation ruleInstance premises conclusion genericResult
              payloadValid.1
          simp only [RuntimePresentation.checkRaw, runtimeResult,
            Bool.and_eq_true, decide_eq_true_eq]
          exact
            ⟨genericAccepted.1,
              RuntimePresentation.checkRawChildren_complete presentation
                premises children genericAccepted.2 payloadValid.2⟩
termination_by sizeOf proof

theorem checkRawChildren_complete
    (presentation : ValidatedPresentation) (premises : List Pattern)
    (proofs : List RawProof)
    (genericAccepted :
      InferenceChecker.checkRawChildren presentation premises proofs = true)
    (payloadValid :
      (RuntimePresentation.ofPresentation presentation.1).proofPayloadListsValid
        proofs = true) :
    (RuntimePresentation.ofPresentation presentation.1).checkRawChildren
        premises proofs = true := by
  cases premises with
  | nil =>
      cases proofs with
      | nil => simp [RuntimePresentation.checkRawChildren]
      | cons proof proofs =>
          simp [InferenceChecker.checkRawChildren] at genericAccepted
  | cons premise premises =>
      cases proofs with
      | nil =>
          simp [InferenceChecker.checkRawChildren] at genericAccepted
      | cons proof proofs =>
          simp only [InferenceChecker.checkRawChildren, Bool.and_eq_true]
            at genericAccepted
          simp only [RuntimePresentation.proofPayloadListsValid,
            Bool.and_eq_true] at payloadValid
          simp only [RuntimePresentation.checkRawChildren, Bool.and_eq_true]
          exact
            ⟨RuntimePresentation.checkRaw_complete presentation premise proof
                genericAccepted.1 payloadValid.1,
              RuntimePresentation.checkRawChildren_complete presentation
                premises proofs genericAccepted.2 payloadValid.2⟩
termination_by sizeOf proofs

end


/-- The closed-payload runtime and generic NIK replay agree exactly whenever
the article carries only declared fixed constructors. -/
theorem checkRaw_iff_generic_of_payloadsValid
    (presentation : ValidatedPresentation) (goal : Pattern) (proof : RawProof)
    (payloadValid :
      (RuntimePresentation.ofPresentation presentation.1).proofPayloadsValid
        proof = true) :
    (RuntimePresentation.ofPresentation presentation.1).checkRaw
          goal proof = true ↔
      InferenceChecker.checkRaw presentation goal proof = true := by
  constructor
  · exact RuntimePresentation.checkRaw_sound presentation goal proof
  · intro genericAccepted
    exact RuntimePresentation.checkRaw_complete presentation goal proof
      genericAccepted payloadValid

private def payloadCanaryPresentation : RuntimePresentation :=
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
    RuntimePresentation.proofPayloadsValid,
    RuntimePresentation.proofPayloadListsValid,
    RuntimePresentation.fixedConstructorListsValid,
    RuntimePresentation.fixedConstructorsValid,
    RuntimePresentation.constructorApplicationValid]

/-- Open atom data does not enlarge the authority's structural vocabulary. -/
theorem opaque_nullary_payload_is_valid :
    payloadCanaryPresentation.proofPayloadsValid
      (payloadCanaryProof "OpaqueAtom") = true := by
  simp [payloadCanaryPresentation, payloadCanaryProof,
    RuntimePresentation.proofPayloadsValid,
    RuntimePresentation.proofPayloadListsValid,
    RuntimePresentation.fixedConstructorListsValid,
    RuntimePresentation.fixedConstructorsValid,
    RuntimePresentation.constructorApplicationValid]

/-- A declared structural head cannot be reinterpreted as nullary atom data. -/
theorem declared_wrong_arity_payload_is_invalid :
    payloadCanaryPresentation.proofPayloadsValid
      (payloadCanaryProof "Unary") = false := by
  simp [payloadCanaryPresentation, payloadCanaryProof,
    RuntimePresentation.proofPayloadsValid,
    RuntimePresentation.proofPayloadListsValid,
    RuntimePresentation.fixedConstructorListsValid,
    RuntimePresentation.fixedConstructorsValid,
    RuntimePresentation.constructorApplicationValid]

private def payloadCanaryStructuralProof : RawProof :=
  .node ⟨⟨"canary"⟩,
    [.apply "Undeclared" [.apply "OpaqueAtom" []]]⟩ []

/-- The extra runtime premise remains substantive: an undeclared structural
constructor is rejected before rule replay. -/
theorem undeclared_structural_payload_is_invalid :
    payloadCanaryPresentation.proofPayloadsValid
      payloadCanaryStructuralProof = false := by
  simp [payloadCanaryPresentation, payloadCanaryStructuralProof,
    RuntimePresentation.proofPayloadsValid,
    RuntimePresentation.proofPayloadListsValid,
    RuntimePresentation.fixedConstructorListsValid,
    RuntimePresentation.fixedConstructorsValid,
    RuntimePresentation.constructorApplicationValid]

end RuntimePresentation

end Mettapedia.GSLT.LanguageDef.InferencePresentationWire
