import Mettapedia.Languages.VibeITP.Presentation.LiteralGeneration

/-!
# Exact submitted literal checks and independent derivability

Completed queries preserve and reflect the specified operand/result relation.
The check compares the actual produced statement with the submitted claim.
Its soundness uses the seven independent derivation constructors, rather than
an unrelated proof of the same claim. Exhaustion is not refusal.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Presentation.ComputationalLiterals

open ComputationalData ComputationalShift ComputationalInference
open Mettapedia.GSLT.LanguageDef.DeterministicEquations

local notation "P" => literalProgram
local notation "A" => literalEquations
local notation "H" => productDivisionHost

theorem literalQuery_result_exact (request : LiteralRequest) (result : Term) :
    Applies P H "vibe:literal-query" [encodeRequest request] result ↔
      result = encodeResult request.result := by
  constructor
  · intro computed
    exact computed.deterministic (literalQuery_computes request)
  · intro same
    subst result
    exact literalQuery_computes request

theorem literalQuery_accepts_iff (request : LiteralRequest) (claimed : Spec.Term) :
    Applies P H "vibe:literal-query" [encodeRequest request] (encodeResult (some claimed)) ↔
      request.result = some claimed := by
  rw [literalQuery_result_exact]
  exact ⟨fun same => (encodeResult_injective same).symm, fun same => congrArg encodeResult same.symm⟩

theorem literalQuery_refuses_iff (request : LiteralRequest) :
    Applies P H "vibe:literal-query" [encodeRequest request] (.sym "None") ↔ request.result = none := by
  rw [literalQuery_result_exact]
  change encodeResult none = encodeResult request.result ↔ request.result = none
  exact ⟨fun same => (encodeResult_injective same).symm, fun same => congrArg encodeResult same.symm⟩

theorem literalQuery_completed_exact (request : LiteralRequest) (fuel : Nat)
    (finished : apply P H fuel "vibe:literal-query" [encodeRequest request] ≠ .exhausted) :
    apply P H fuel "vibe:literal-query" [encodeRequest request] = .value (encodeResult request.result) :=
  (literalQuery_computes request).completed fuel finished

private theorem check_result (result : Option Spec.Term) (claimed : Spec.Term) :
    Applies P H "vibe:check-result" [encodeResult result, encode claimed]
      (boolean (decide (result = some claimed))) := by
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

theorem checkLiteral_computes (request : LiteralRequest) (claimed : Spec.Term) :
    Applies P H "vibe:check-literal" [encodeRequest request, encode claimed]
      (boolean (decide (request.result = some claimed))) := by
  refine literal_equation (equation := A[45])
    (environment := [("request", encodeRequest request), ("claimed", encode claimed)])
    (by decide +kernel) (by rfl) (by rfl) ?_
  refine Evaluates.call (values := [encodeResult request.result, encode claimed]) (by simp [Special])
    (.cons ?_ (.cons (.variable (by rfl)) .nil)) (check_result request.result claimed)
  exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil) (literalQuery_computes request)

theorem checkLiteral_result_exact (request : LiteralRequest) (claimed : Spec.Term) (result : Term) :
    Applies P H "vibe:check-literal" [encodeRequest request, encode claimed] result ↔
      result = boolean (decide (request.result = some claimed)) := by
  constructor
  · intro computed
    exact computed.deterministic (checkLiteral_computes request claimed)
  · intro same
    subst result
    exact checkLiteral_computes request claimed

theorem checkLiteral_accepts_iff (request : LiteralRequest) (claimed : Spec.Term) :
    Applies P H "vibe:check-literal" [encodeRequest request, encode claimed] (.sym "True") ↔
      request.result = some claimed := by
  rw [checkLiteral_result_exact]
  by_cases valid : request.result = some claimed <;> simp [valid, boolean]

theorem checkLiteral_refuses_iff (request : LiteralRequest) (claimed : Spec.Term) :
    Applies P H "vibe:check-literal" [encodeRequest request, encode claimed] (.sym "False") ↔
      request.result ≠ some claimed := by
  rw [checkLiteral_result_exact]
  by_cases valid : request.result = some claimed <;> simp [valid, boolean]

theorem checkLiteral_completed_exact (request : LiteralRequest) (claimed : Spec.Term) (fuel : Nat)
    (finished : apply P H fuel "vibe:check-literal" [encodeRequest request, encode claimed] ≠ .exhausted) :
    apply P H fuel "vibe:check-literal" [encodeRequest request, encode claimed] =
      .value (boolean (decide (request.result = some claimed))) :=
  (checkLiteral_computes request claimed).completed fuel finished

theorem LiteralRequest.derivable (theory : Spec.Theory) (request : LiteralRequest) {claimed : Spec.Term}
    (authorized : request.result = some claimed) : Spec.Derives theory claimed := by
  cases request with
  | isNat value =>
      simp only [LiteralRequest.result] at authorized
      split at authorized
      next bound => cases Option.some.inj authorized; exact .litIsNat bound
      next => cases authorized
  | lessThan left right =>
      simp only [LiteralRequest.result] at authorized
      split at authorized
      next guard => cases Option.some.inj authorized; exact .litLt guard.1 guard.2
      next => cases authorized
  | addition left right =>
      simp only [LiteralRequest.result] at authorized
      split at authorized
      next guard => cases Option.some.inj authorized; exact .litAdd guard.1 guard.2
      next => cases authorized
  | multiplication left right =>
      simp only [LiteralRequest.result] at authorized
      split at authorized
      next guard => cases Option.some.inj authorized; exact .litMul guard.1 guard.2
      next => cases authorized
  | division left right =>
      simp only [LiteralRequest.result] at authorized
      split at authorized
      next guard => cases Option.some.inj authorized; exact .litDiv guard.1 guard.2.1 guard.2.2
      next => cases authorized
  | length value =>
      cases value with
      | bvar _ => cases authorized
      | app _ _ => cases authorized
      | lit bytes =>
          simp only [LiteralRequest.result] at authorized
          split at authorized
          next guard =>
            cases Option.some.inj authorized
            exact .litLength (by simp [Spec.WellFormed, guard])
          next => cases authorized
  | get value index =>
      cases value with
      | bvar _ => cases authorized
      | app _ _ => cases authorized
      | lit bytes =>
          simp only [LiteralRequest.result] at authorized
          split at authorized
          next guard =>
            cases Option.some.inj authorized
            exact .litGet (by simp [Spec.WellFormed, guard.1]) guard.2
          next => cases authorized

theorem checkLiteral_derived (theory : Spec.Theory) (request : LiteralRequest) (claimed : Spec.Term)
    (checked : Applies P H "vibe:check-literal" [encodeRequest request, encode claimed] (.sym "True")) :
    Spec.Derives theory claimed :=
  request.derivable theory ((checkLiteral_accepts_iff request claimed).mp checked)

/-- The supplied literal request's authorized output always has a finite
checked witness. This is completeness for the seven literal constructors,
not completeness for arbitrary derivability through other proof rules. -/
theorem literalWitness_exists (request : LiteralRequest) (claimed : Spec.Term)
    (authorized : request.result = some claimed) :
    ∃ fuel, apply P H fuel "vibe:check-literal" [encodeRequest request, encode claimed] = .value (.sym "True") :=
  (checkLiteral_accepts_iff request claimed).mpr authorized

end Mettapedia.Languages.VibeITP.Presentation.ComputationalLiterals
