import Mettapedia.Languages.VibeITP.Presentation.DefinitionGeneration

/-!
# Exact supplied definition operands and claims

Parameter-information construction does not admit a definition by itself.
The definition query checks the full submitted body and hint conditions;
claimed-result checking compares with that query's actual result. Completed
refusal remains distinct from exhaustion.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Presentation.ComputationalDefinitions

open ComputationalData ComputationalShift ComputationalInference ComputationalLiterals
open Mettapedia.GSLT.LanguageDef.DeterministicEquations

local notation "P" => definitionProgram
local notation "A" => definitionEquations
local notation "H" => productDivisionHost

theorem encodeBinders_injective : Function.Injective encodeBinders := by
  intro first second same
  exact List.map_injective_iff.mpr natural_injective (Term.list.inj same)

theorem encodeInfo_injective : Function.Injective encodeInfo := by
  intro first second same
  rcases first with ⟨firstKind, firstBinders⟩
  rcases second with ⟨secondKind, secondBinders⟩
  have contents := Term.expr.inj same
  simp only [List.cons.injEq, true_and, and_true] at contents
  have binders : firstBinders = secondBinders := encodeBinders_injective contents.2
  have kind : firstKind = secondKind := by
    cases firstKind <;> cases secondKind <;> simp_all [encodeKind]
  cases kind
  cases binders
  rfl

theorem encodeInfoResult_injective : Function.Injective encodeInfoResult := by
  intro first second same
  cases first with
  | none =>
      cases second with
      | none => rfl
      | some second => cases same
  | some first =>
      cases second with
      | none => cases same
      | some second =>
          have contents : encodeInfo first = encodeInfo second := by simpa [encodeInfoResult] using same
          exact congrArg some (encodeInfo_injective contents)

theorem definitionInfo_result_exact (table : SignatureTable) (parameters : List Spec.SymId) (result : Term) :
    Applies P H "vibe:def-info" [encodeTable table, encodeSymbols parameters] result ↔
      result = encodeInfoResult (if parameters.all (Spec.isFvarSym (signatureOf table)) then
        some (Spec.definitionInfo (signatureOf table) parameters) else none) := by
  constructor
  · exact fun run => run.deterministic (definitionInfo_computes table parameters)
  · rintro rfl
    exact definitionInfo_computes table parameters

theorem definitionInfo_accepts_iff (table : SignatureTable) (parameters : List Spec.SymId) (info : Spec.SymInfo) :
    Applies P H "vibe:def-info" [encodeTable table, encodeSymbols parameters] (encodeInfoResult (some info)) ↔
      parameters.all (Spec.isFvarSym (signatureOf table)) = true ∧
        info = Spec.definitionInfo (signatureOf table) parameters := by
  rw [definitionInfo_result_exact]
  have encoded : ∀ result, encodeInfoResult (some info) = encodeInfoResult result ↔ some info = result :=
    fun result => ⟨fun same => encodeInfoResult_injective same, congrArg encodeInfoResult⟩
  rw [encoded]
  cases parameters.all (Spec.isFvarSym (signatureOf table)) <;> simp

theorem definitionQuery_result_exact (table : SignatureTable) (request : DefinitionRequest) (result : Term) :
    Applies P H "vibe:definition-query" [encodeTable table, encodeSymbol request.constant,
      encodeSymbols request.parameters, encodeBinders request.hints, encode request.body] result ↔
      result = encodeResult (request.result (signatureOf table)) := by
  constructor
  · exact fun run => run.deterministic (definitionQuery_computes table request)
  · rintro rfl
    exact definitionQuery_computes table request

theorem definitionQuery_accepts_iff (table : SignatureTable) (request : DefinitionRequest) (claimed : Spec.Term) :
    Applies P H "vibe:definition-query" [encodeTable table, encodeSymbol request.constant,
      encodeSymbols request.parameters, encodeBinders request.hints, encode request.body]
      (encodeResult (some claimed)) ↔ request.result (signatureOf table) = some claimed := by
  rw [definitionQuery_result_exact]
  exact ⟨fun same => (encodeResult_injective same).symm, fun same => congrArg encodeResult same.symm⟩

theorem definitionQuery_refuses_iff (table : SignatureTable) (request : DefinitionRequest) :
    Applies P H "vibe:definition-query" [encodeTable table, encodeSymbol request.constant,
      encodeSymbols request.parameters, encodeBinders request.hints, encode request.body]
      (.sym "None") ↔ request.result (signatureOf table) = none := by
  rw [definitionQuery_result_exact]
  change encodeResult none = encodeResult (request.result (signatureOf table)) ↔ _
  exact ⟨fun same => (encodeResult_injective same).symm, fun same => congrArg encodeResult same.symm⟩

theorem definitionQuery_completed_exact (table : SignatureTable) (request : DefinitionRequest) (fuel : Nat)
    (finished : apply P H fuel "vibe:definition-query" [encodeTable table, encodeSymbol request.constant,
      encodeSymbols request.parameters, encodeBinders request.hints, encode request.body] ≠ .exhausted) :
    apply P H fuel "vibe:definition-query" [encodeTable table, encodeSymbol request.constant,
      encodeSymbols request.parameters, encodeBinders request.hints, encode request.body] =
      .value (encodeResult (request.result (signatureOf table))) :=
  (definitionQuery_computes table request).completed fuel finished

private theorem definition_check_result (result : Option Spec.Term) (claimed : Spec.Term) :
    Applies P H "vibe:check-result" [encodeResult result, encode claimed]
      (boolean (decide (result = some claimed))) := by
  apply reuse_literal_call (by decide +kernel)
  apply reuse_inference_call (by decide +kernel)
  cases result with
  | none => exact ⟨1, by rw [inference_apply _ (by decide +kernel)]; rfl⟩
  | some actual =>
      refine inference_equation (equation := inferenceEquations[35])
        (environment := [("actual", encode actual), ("claimed", encode claimed)])
        (by decide +kernel) (by rfl) (by rfl) ?_
      exact Evaluates.call (by simp [Special])
        (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))
        (by simpa only [Option.some.injEq] using term_equality_computes actual claimed)

theorem checkDefinition_computes (table : SignatureTable) (request : DefinitionRequest) (claimed : Spec.Term) :
    Applies P H "vibe:check-definition" [encodeTable table, encodeSymbol request.constant,
      encodeSymbols request.parameters, encodeBinders request.hints, encode request.body, encode claimed]
      (boolean (decide (request.result (signatureOf table) = some claimed))) := by
  refine definition_equation (equation := A[55])
    (environment := [("table", encodeTable table), ("constant", encodeSymbol request.constant),
      ("parameters", encodeSymbols request.parameters), ("hints", encodeBinders request.hints),
      ("body", encode request.body), ("claimed", encode claimed)])
    (by decide +kernel) (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special]) (.cons ?_ (.cons (.variable (by rfl)) .nil))
    (definition_check_result (request.result (signatureOf table)) claimed)
  exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
    (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))))
      (definitionQuery_computes table request)

theorem checkDefinition_result_exact (table : SignatureTable) (request : DefinitionRequest)
    (claimed : Spec.Term) (result : Term) :
    Applies P H "vibe:check-definition" [encodeTable table, encodeSymbol request.constant,
      encodeSymbols request.parameters, encodeBinders request.hints, encode request.body, encode claimed] result ↔
      result = boolean (decide (request.result (signatureOf table) = some claimed)) := by
  constructor
  · exact fun run => run.deterministic (checkDefinition_computes table request claimed)
  · rintro rfl
    exact checkDefinition_computes table request claimed

theorem checkDefinition_accepts_iff (table : SignatureTable) (request : DefinitionRequest) (claimed : Spec.Term) :
    Applies P H "vibe:check-definition" [encodeTable table, encodeSymbol request.constant,
      encodeSymbols request.parameters, encodeBinders request.hints, encode request.body, encode claimed]
      (.sym "True") ↔ request.result (signatureOf table) = some claimed := by
  rw [checkDefinition_result_exact]
  by_cases valid : request.result (signatureOf table) = some claimed <;> simp [valid, boolean]

theorem checkDefinition_refuses_iff (table : SignatureTable) (request : DefinitionRequest) (claimed : Spec.Term) :
    Applies P H "vibe:check-definition" [encodeTable table, encodeSymbol request.constant,
      encodeSymbols request.parameters, encodeBinders request.hints, encode request.body, encode claimed]
      (.sym "False") ↔ request.result (signatureOf table) ≠ some claimed := by
  rw [checkDefinition_result_exact]
  by_cases valid : request.result (signatureOf table) = some claimed <;> simp [valid, boolean]

theorem checkDefinition_completed_exact (table : SignatureTable) (request : DefinitionRequest)
    (claimed : Spec.Term) (fuel : Nat)
    (finished : apply P H fuel "vibe:check-definition" [encodeTable table, encodeSymbol request.constant,
      encodeSymbols request.parameters, encodeBinders request.hints, encode request.body, encode claimed] ≠ .exhausted) :
    apply P H fuel "vibe:check-definition" [encodeTable table, encodeSymbol request.constant,
      encodeSymbols request.parameters, encodeBinders request.hints, encode request.body, encode claimed] =
      .value (boolean (decide (request.result (signatureOf table) = some claimed))) :=
  (checkDefinition_computes table request claimed).completed fuel finished

theorem definitionWitness_exists (table : SignatureTable) (request : DefinitionRequest) (claimed : Spec.Term)
    (authorized : request.result (signatureOf table) = some claimed) :
    ∃ fuel, apply P H fuel "vibe:check-definition" [encodeTable table, encodeSymbol request.constant,
      encodeSymbols request.parameters, encodeBinders request.hints, encode request.body, encode claimed] =
      .value (.sym "True") := by
  have checked := checkDefinition_computes table request claimed
  simp only [authorized, decide_true, boolean, ↓reduceIte] at checked
  exact checked

end Mettapedia.Languages.VibeITP.Presentation.ComputationalDefinitions
