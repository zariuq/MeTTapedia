import Mettapedia.Languages.MeTTa.Prime.NativeInteraction

/-!
# Judgmental conservativity of Prime-native interaction

Prime adds proof-relevant rho interaction as a displayed judgment fibre.  It
does not add rho paths to native conversion and it does not use an interaction
derivation as a static typing derivation.

`PrimeJudgment` makes the separation explicit.  Its three indices retain the
existing native conversion and typing judgments verbatim and add the exact
endpoint-indexed interaction carrier as a third case.  The restriction
theorems below prove both preservation and reflection for the two static
judgments.  The COMM witness proves that the interaction case is genuinely
inhabited, while endpoint inversion proves that it remains confined to the
runtime-pattern image.

This is a direct-internalization result.  It does not exclude an explicitly
authored interpreter or another computational encoding of dependent syntax as
rho data.
-/

namespace Mettapedia.Languages.MeTTa.Prime.NativeInteractionConservativity

open Mettapedia.Languages.MeTTa.NativeTypeTheory
open Mettapedia.Languages.MeTTa.NativeTypeTheory.NativeModalTyping
open Mettapedia.Languages.MeTTa.Prime.NativeInteraction
open Mettapedia.Languages.MeTTa.Prime.RhoNonCollapse
open Mettapedia.Languages.MeTTa.PureKernel.Syntax
open Mettapedia.OSLF.MeTTaIL.Syntax

/-! ## Exact endpoint inversion -/

/-- A closed native term is a rho endpoint exactly when it is a first-class
runtime pattern.  Endpoint admission therefore has no hidden coercion from
the dependent core. -/
theorem rhoEndpoint_nonempty_iff (term : NativeRawTm 0 0) :
    Nonempty (RhoEndpoint term) ↔
      ∃ pattern : Pattern, term = (.pattern pattern : NativeRawTm 0 0) := by
  constructor
  · rintro ⟨endpoint⟩
    exact ⟨endpoint.pattern, endpoint.term_eq⟩
  · rintro ⟨pattern, equal⟩
    subst term
    exact ⟨patternEndpoint pattern⟩

/-- Endpoint admission implies membership in the direct rho-bearing fragment. -/
theorem directRho_of_rhoEndpoint {term : NativeRawTm 0 0}
    (endpoint : RhoEndpoint term) :
    DirectRhoFragment term := by
  rw [endpoint.term_eq]
  exact .pattern endpoint.pattern

/-- No embedded dependent-core term is admitted as a direct rho endpoint. -/
theorem pureImage_has_no_rhoEndpoint (term : PureTm 0) :
    ¬ Nonempty (RhoEndpoint (embedPure 0 term)) := by
  rintro ⟨endpoint⟩
  exact pureImage_disjoint_directRho term (directRho_of_rhoEndpoint endpoint)

/-- A rho computation cannot use an embedded dependent-core term as its
source endpoint. -/
theorem pureImage_has_no_outgoing_rhoComputation (term : PureTm 0)
    (target : NativeRawTm 0 0) :
    ¬ Nonempty
      ((nativeRhoComputationTy (embedPure 0 term) target) PUnit.unit) := by
  rintro ⟨sourceEndpoint, _targetEndpoint, _path⟩
  exact pureImage_has_no_rhoEndpoint term ⟨sourceEndpoint⟩

/-- A rho computation cannot use an embedded dependent-core term as its
target endpoint. -/
theorem pureImage_has_no_incoming_rhoComputation (source : NativeRawTm 0 0)
    (term : PureTm 0) :
    ¬ Nonempty
      ((nativeRhoComputationTy source (embedPure 0 term)) PUnit.unit) := by
  rintro ⟨_sourceEndpoint, targetEndpoint, _path⟩
  exact pureImage_has_no_rhoEndpoint term ⟨targetEndpoint⟩

/-! ## The displayed total judgment -/

/-- The three judgment classes of the integrated theory.  Conversion and
static typing keep their original indices; interaction is indexed by exact
closed native endpoints. -/
inductive PrimeJudgmentIndex where
  | conversion (stage binders : Nat)
      (left right : NativeRawTm stage binders)
  | typing (stage binders : Nat) (context : Context binders)
      (term type : NativeRawTm stage binders)
  | interaction (source target : NativeRawTm 0 0)

/-- Evidence for the integrated judgment space.  Interaction adds one new
proof-relevant fibre and no constructor whose conclusion is a conversion or
static typing index. -/
inductive PrimeJudgment (conversion : ConversionPolicy) :
    PrimeJudgmentIndex → Type 1 where
  | converted {stage binders : Nat}
      {left right : NativeRawTm stage binders}
      (related : conversion.Rel left right) :
      PrimeJudgment conversion (.conversion stage binders left right)
  | typed {stage binders : Nat} {context : Context binders}
      {term type : NativeRawTm stage binders}
      (derivation : HasType conversion context term type) :
      PrimeJudgment conversion (.typing stage binders context term type)
  | interacted {source target : NativeRawTm 0 0}
      (path : (nativeRhoComputationTy source target) PUnit.unit) :
      PrimeJudgment conversion (.interaction source target)

/-- Adding the interaction fibre preserves and reflects native conversion
exactly. -/
theorem conversion_conservative (conversion : ConversionPolicy)
    {stage binders : Nat} (left right : NativeRawTm stage binders) :
    Nonempty
        (PrimeJudgment conversion
          (.conversion stage binders left right)) ↔
      conversion.Rel left right := by
  constructor
  · rintro ⟨evidence⟩
    cases evidence with
    | converted related => exact related
  · intro related
    exact ⟨.converted related⟩

/-- Adding the interaction fibre preserves and reflects native static typing
exactly. -/
theorem typing_conservative (conversion : ConversionPolicy)
    {stage binders : Nat} (context : Context binders)
    (term type : NativeRawTm stage binders) :
    Nonempty
        (PrimeJudgment conversion
          (.typing stage binders context term type)) ↔
      HasType conversion context term type := by
  constructor
  · rintro ⟨evidence⟩
    cases evidence with
    | typed derivation => exact derivation
  · intro derivation
    exact ⟨.typed derivation⟩

/-- The new interaction judgment is neither weakened nor quotient-erased by
the totalization: it retains the exact endpoint admissions and event path. -/
theorem interaction_exact (conversion : ConversionPolicy)
    (source target : NativeRawTm 0 0) :
    Nonempty
        (PrimeJudgment conversion (.interaction source target)) ↔
      Nonempty
        ((nativeRhoComputationTy source target) PUnit.unit) := by
  constructor
  · rintro ⟨evidence⟩
    cases evidence with
    | interacted path => exact ⟨path⟩
  · rintro ⟨path⟩
    exact ⟨.interacted path⟩

/-- Any integrated interaction judgment exposes direct rho endpoints on both
sides. -/
theorem interaction_has_direct_endpoints
    {conversion : ConversionPolicy} {source target : NativeRawTm 0 0}
    (evidence : PrimeJudgment conversion (.interaction source target)) :
    DirectRhoFragment source ∧ DirectRhoFragment target := by
  cases evidence with
  | interacted path =>
      exact ⟨directRho_of_rhoEndpoint path.1,
        directRho_of_rhoEndpoint path.2.1⟩

/-! ## Positive and negative controls -/

/-- The extension is strict: the concrete COMM path inhabits the new
interaction judgment. -/
def internalCommJudgment :
    PrimeJudgment syntacticConversion
      (.interaction (.pattern commSource) (.pattern commTarget)) :=
  .interacted (internalNativeComm PUnit.unit)

/-- Direct interaction does not span the closed native core. -/
def DirectInteractionSpansClosedNative : Prop :=
  ∀ term : NativeRawTm 0 0, Nonempty (RhoEndpoint term)

theorem directInteraction_does_not_span_closed_native_core :
    ¬ DirectInteractionSpansClosedNative := by
  intro spans
  exact nativeDependentFunctionType_has_no_rhoEndpoint
    (spans nativeDependentFunctionType)

/-- Even after totalization, an interaction judgment cannot be constructed
with an embedded dependent function as its source. -/
theorem dependentFunction_has_no_interaction_judgment
    (conversion : ConversionPolicy) (target : NativeRawTm 0 0) :
    ¬ Nonempty
      (PrimeJudgment conversion
        (.interaction nativeDependentFunctionType target)) := by
  intro evidence
  have computation :=
    (interaction_exact conversion nativeDependentFunctionType target).mp
      evidence
  exact nativeDependentFunctionType_has_no_outgoing_rhoComputation target
    computation

#print axioms rhoEndpoint_nonempty_iff
#print axioms pureImage_has_no_rhoEndpoint
#print axioms conversion_conservative
#print axioms typing_conservative
#print axioms interaction_exact
#print axioms interaction_has_direct_endpoints
#print axioms directInteraction_does_not_span_closed_native_core
#print axioms dependentFunction_has_no_interaction_judgment

end Mettapedia.Languages.MeTTa.Prime.NativeInteractionConservativity
