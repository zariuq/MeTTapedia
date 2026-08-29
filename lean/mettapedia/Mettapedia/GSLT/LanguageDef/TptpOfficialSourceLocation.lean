import Mettapedia.GSLT.LanguageDef.TptpOfficialAbstractSyntax
import Std.Data.String.ToInt

/-!
# Source-location refinement for official TPTP abstract syntax

The generated TPTP abstract syntax makes a source span mandatory on each
top-level input.  This module gives that extension an explicit view and proves
that forgetting the location recovers exactly the corresponding unlocated
input.  The statements use the generated constructor names directly, so an
arity or constructor change must update this refinement boundary.
-/

set_option autoImplicit false
set_option maxRecDepth 10000

namespace Mettapedia.GSLT.LanguageDef.TptpOfficialSourceLocation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.CarrierWellSorted
open Mettapedia.GSLT.LanguageDef.WellSorted

private def a (name : String) (arguments : List Pattern := []) : Pattern :=
  .apply name arguments

def symbolicInputContext : WellSorted.FreeTypeContext := fun name =>
  if name = "formula" then
    some (.base "Tptp92Ast:annotated-formula")
  else if name = "directive" then
    some (.base "Tptp92Ast:include")
  else
    none

def symbolicLocatedInput : Pattern :=
  a "tptp92-ast:tptp-input:alt-1" [
    .fvar "formula",
    a "tptp92-ast:source-span"
      [a (toString (4 : Nat)), a (toString (23 : Nat))]]

def symbolicUnlocatedInput : Pattern :=
  a "tptp92-ast:tptp-input:alt-1" [.fvar "formula"]

def symbolicLocatedInclude : Pattern :=
  a "tptp92-ast:tptp-input:alt-2" [
    .fvar "directive",
    a "tptp92-ast:source-span"
      [a (toString (4 : Nat)), a (toString (23 : Nat))]]

def symbolicUnlocatedInclude : Pattern :=
  a "tptp92-ast:tptp-input:alt-2" [.fvar "directive"]

private theorem natAtomAccepted (value : Nat) :
    CarrierWellSorted.carrierAcceptsAtom .builtinInt
      (toString value) = true := by
  simp [CarrierWellSorted.carrierAcceptsAtom, Nat.toInt?_repr]

private theorem integerAtomTyped (value : Nat) :
    CarrierWellSorted.HasType TptpOfficialAbstractSyntax.language
      symbolicInputContext [] (a (toString value)) (.base "Integer") := by
  apply CarrierWellSorted.HasType.builtinAtom
  refine ⟨TptpOfficialAbstractSyntax.integerTypeDeclaration,
    TptpOfficialAbstractSyntax.integerTypeDeclaration_mem_language, ?_, ?_⟩
  · rw [TptpOfficialAbstractSyntax.integerTypeDeclaration_shape]
  · rw [TptpOfficialAbstractSyntax.integerTypeDeclaration_shape]
    exact natAtomAccepted value

private theorem symbolicSpanTyped :
    CarrierWellSorted.HasType TptpOfficialAbstractSyntax.language
      symbolicInputContext []
      (a "tptp92-ast:source-span"
        [a (toString (4 : Nat)), a (toString (23 : Nat))])
      (.base "Tptp92Ast:source-span") := by
  have argumentsTyped :
      CarrierWellSorted.ArgumentsHaveTypes
        TptpOfficialAbstractSyntax.language symbolicInputContext []
        [a (toString (4 : Nat)), a (toString (23 : Nat))]
        TptpOfficialAbstractSyntax.sourceSpanRule.params := by
    rw [TptpOfficialAbstractSyntax.sourceSpanRule_shape]
    exact .cons (by trivial) rfl
      (integerAtomTyped 4)
      (.cons (by trivial) rfl
        (integerAtomTyped 23) .nil)
  have typed := CarrierWellSorted.HasType.constructor
    TptpOfficialAbstractSyntax.sourceSpanRule_mem_language
    (by
      rw [TptpOfficialAbstractSyntax.sourceSpanRule_shape]
      simp [WellSorted.UsesBareCollection])
    argumentsTyped
  simpa [TptpOfficialAbstractSyntax.sourceSpanRule_shape, a] using typed

theorem symbolic_located_input_has_type :
    CarrierWellSorted.HasType TptpOfficialAbstractSyntax.language
      symbolicInputContext [] symbolicLocatedInput
      (.base "Tptp92Ast:tptp-input") := by
  have argumentsTyped :
      CarrierWellSorted.ArgumentsHaveTypes
        TptpOfficialAbstractSyntax.language symbolicInputContext []
        [.fvar "formula",
          a "tptp92-ast:source-span"
            [a (toString (4 : Nat)), a (toString (23 : Nat))]]
        TptpOfficialAbstractSyntax.annotatedInputRule.params := by
    rw [TptpOfficialAbstractSyntax.annotatedInputRule_shape]
    exact .cons (by trivial) rfl
      (.fvar (by simp [symbolicInputContext]))
      (.cons (by trivial) rfl symbolicSpanTyped .nil)
  have typed := CarrierWellSorted.HasType.constructor
    TptpOfficialAbstractSyntax.annotatedInputRule_mem_language
    (by
      rw [TptpOfficialAbstractSyntax.annotatedInputRule_shape]
      simp [WellSorted.UsesBareCollection])
    argumentsTyped
  simpa [TptpOfficialAbstractSyntax.annotatedInputRule_shape,
    symbolicLocatedInput, a] using typed

theorem symbolic_located_input_is_admitted :
    CarrierWellSorted.checkHasType TptpOfficialAbstractSyntax.language
      symbolicInputContext []
      symbolicLocatedInput (.base "Tptp92Ast:tptp-input") = true := by
  exact CarrierWellSorted.checkHasType_complete_of_object
    symbolic_located_input_has_type (by decide)

theorem symbolic_located_include_has_type :
    CarrierWellSorted.HasType TptpOfficialAbstractSyntax.language
      symbolicInputContext [] symbolicLocatedInclude
      (.base "Tptp92Ast:tptp-input") := by
  have argumentsTyped :
      CarrierWellSorted.ArgumentsHaveTypes
        TptpOfficialAbstractSyntax.language symbolicInputContext []
        [.fvar "directive",
          a "tptp92-ast:source-span"
            [a (toString (4 : Nat)), a (toString (23 : Nat))]]
        TptpOfficialAbstractSyntax.includeInputRule.params := by
    rw [TptpOfficialAbstractSyntax.includeInputRule_shape]
    exact .cons (by trivial) rfl
      (.fvar (by simp [symbolicInputContext]))
      (.cons (by trivial) rfl symbolicSpanTyped .nil)
  have typed := CarrierWellSorted.HasType.constructor
    TptpOfficialAbstractSyntax.includeInputRule_mem_language
    (by
      rw [TptpOfficialAbstractSyntax.includeInputRule_shape]
      simp [WellSorted.UsesBareCollection])
    argumentsTyped
  simpa [TptpOfficialAbstractSyntax.includeInputRule_shape,
    symbolicLocatedInclude, a] using typed

theorem symbolic_located_include_is_admitted :
    CarrierWellSorted.checkHasType TptpOfficialAbstractSyntax.language
      symbolicInputContext []
      symbolicLocatedInclude (.base "Tptp92Ast:tptp-input") = true := by
  exact CarrierWellSorted.checkHasType_complete_of_object
    symbolic_located_include_has_type (by decide)

/-- Syntactic source boundaries as they occur in a MeTTaIL pattern. -/
structure SourceSpanSyntax where
  start : Pattern
  stop : Pattern
  deriving DecidableEq

/-- The source-independent payload of a top-level TPTP input. -/
inductive InputPayload where
  | annotatedFormula (formula : Pattern)
  | includeDirective (directive : Pattern)
  deriving DecidableEq

/-- A top-level TPTP input together with its source boundaries. -/
structure LocatedInputView where
  payload : InputPayload
  span : SourceSpanSyntax
  deriving DecidableEq

def encodeSourceSpan (span : SourceSpanSyntax) : Pattern :=
  a "tptp92-ast:source-span" [span.start, span.stop]

def encodePayload : InputPayload → Pattern
  | .annotatedFormula formula =>
      a "tptp92-ast:tptp-input:alt-1" [formula]
  | .includeDirective directive =>
      a "tptp92-ast:tptp-input:alt-2" [directive]

def encodeLocatedInput (input : LocatedInputView) : Pattern :=
  match input.payload with
  | .annotatedFormula formula =>
      a "tptp92-ast:tptp-input:alt-1"
        [formula, encodeSourceSpan input.span]
  | .includeDirective directive =>
      a "tptp92-ast:tptp-input:alt-2"
        [directive, encodeSourceSpan input.span]

def decodeLocatedInput? : Pattern → Option LocatedInputView
  | .apply "tptp92-ast:tptp-input:alt-1"
      [formula, .apply "tptp92-ast:source-span" [start, stop]] =>
      some {
        payload := .annotatedFormula formula
        span := { start, stop }
      }
  | .apply "tptp92-ast:tptp-input:alt-2"
      [directive, .apply "tptp92-ast:source-span" [start, stop]] =>
      some {
        payload := .includeDirective directive
        span := { start, stop }
      }
  | _ => none

theorem symbolic_unlocated_input_has_no_location_view :
    decodeLocatedInput? symbolicUnlocatedInput = none := by
  rfl

theorem symbolic_unlocated_include_has_no_location_view :
    decodeLocatedInput? symbolicUnlocatedInclude = none := by
  rfl

theorem decode_encode (input : LocatedInputView) :
    decodeLocatedInput? (encodeLocatedInput input) = some input := by
  cases input with
  | mk payload span =>
      cases payload <;> rfl

theorem encodeLocatedInput_injective :
    Function.Injective encodeLocatedInput := by
  intro left right equality
  have decoded := congrArg decodeLocatedInput? equality
  simpa only [decode_encode, Option.some.injEq] using decoded

/-- Forget only the source-location field, retaining the input alternative and
its complete semantic payload. -/
def eraseSourceLocation? (pattern : Pattern) : Option Pattern := do
  let input ← decodeLocatedInput? pattern
  pure (encodePayload input.payload)

theorem erase_encode (input : LocatedInputView) :
    eraseSourceLocation? (encodeLocatedInput input) =
      some (encodePayload input.payload) := by
  cases input with
  | mk payload span =>
      cases payload <;> rfl

/-- Numeric view used to state source-boundary well-formedness. -/
structure SourceSpan where
  start : Nat
  stop : Nat
  deriving DecidableEq

def SourceSpan.WellFormed (span : SourceSpan) : Prop :=
  span.start ≤ span.stop

def SourceSpan.toSyntax (span : SourceSpan) : SourceSpanSyntax := {
  start := a (toString span.start)
  stop := a (toString span.stop)
}

def locate (payload : InputPayload) (span : SourceSpan) : LocatedInputView := {
  payload
  span := span.toSyntax
}

theorem erase_locate (payload : InputPayload) (span : SourceSpan) :
    eraseSourceLocation? (encodeLocatedInput (locate payload span)) =
      some (encodePayload payload) := by
  cases payload <;> rfl

def unicodeCanarySpan : SourceSpan := ⟨4, 23⟩
def reversedCanarySpan : SourceSpan := ⟨23, 4⟩

theorem unicode_canary_span_well_formed :
    unicodeCanarySpan.WellFormed := by
  simp [SourceSpan.WellFormed, unicodeCanarySpan]

theorem reversed_canary_span_not_well_formed :
    ¬ reversedCanarySpan.WellFormed := by
  simp [SourceSpan.WellFormed, reversedCanarySpan]

def annotatedFormulaExample : Pattern :=
  a "tptp92-ast:annotated-formula:alt-4"
    [TptpOfficialAbstractSyntax.fofAnnotatedExample]

def locatedFofInputExample : Pattern :=
  encodeLocatedInput
    (locate (.annotatedFormula annotatedFormulaExample) unicodeCanarySpan)

def unlocatedFofInputExample : Pattern :=
  encodePayload (.annotatedFormula annotatedFormulaExample)

theorem located_example_is_refinement_encoding :
    locatedFofInputExample =
      encodeLocatedInput
        (locate (.annotatedFormula annotatedFormulaExample)
          unicodeCanarySpan) := by
  rfl

theorem unlocated_example_is_erasure_target :
    unlocatedFofInputExample =
      encodePayload (.annotatedFormula annotatedFormulaExample) := by
  rfl

#print axioms decode_encode
#print axioms symbolic_located_input_has_type
#print axioms symbolic_located_input_is_admitted
#print axioms symbolic_located_include_has_type
#print axioms symbolic_located_include_is_admitted
#print axioms symbolic_unlocated_input_has_no_location_view
#print axioms symbolic_unlocated_include_has_no_location_view
#print axioms encodeLocatedInput_injective
#print axioms erase_encode
#print axioms erase_locate
#print axioms unicode_canary_span_well_formed
#print axioms reversed_canary_span_not_well_formed
#print axioms located_example_is_refinement_encoding
#print axioms unlocated_example_is_erasure_target

end Mettapedia.GSLT.LanguageDef.TptpOfficialSourceLocation
