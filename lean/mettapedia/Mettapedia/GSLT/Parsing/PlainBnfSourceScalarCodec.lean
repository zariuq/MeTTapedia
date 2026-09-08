import Mettapedia.GSLT.Parsing.HornIntegerProvider
import Mettapedia.GSLT.Parsing.PlainBnfStructuredValueCodec

/-!
# Authored scalar lists and their existing structured wire representation

The source graph uses the existing ground equation carrier: its empty scalar
list is `metta-nullary` applied to the `bnf-v1:scalars-nil` symbol, while each
cons contains an integer and the next source list. The decoder below accepts
exactly lists of nonnegative integers in this source shape.

The separate structural lowering maps this family into the existing CeTTa
wire term. It unwraps the source nil and represents nonnegative integers as
wire naturals. Its result is proved equal to the existing structured-value
encoder; it is not defined by invoking that encoder or the source decoder.
No text rendering, host reading, SWI codec, or physical C correspondence is
claimed here. Unicode validity, ordering, and grammar admission remain separate.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.PlainBnfSourceScalarCodec

open HornCertificate HornIntegerProvider

def encodeScalars : List Nat → GroundTerm
  | [] => .app "metta-nullary" (.cons (.atom "bnf-v1:scalars-nil") .nil)
  | scalar :: rest => .app "bnf-v1:scalars-cons"
      (.cons (.integer scalar) (.cons (encodeScalars rest) .nil))

def decodeScalars : GroundTerm → Option (List Nat)
  | .app "metta-nullary" (.cons (.atom "bnf-v1:scalars-nil") .nil) => some []
  | .app "bnf-v1:scalars-cons" (.cons (.integer scalar) (.cons rest .nil)) =>
      if 0 ≤ scalar then do
        let decodedRest ← decodeScalars rest
        pure (scalar.toNat :: decodedRest)
      else none
  | _ => none
termination_by term => sizeOf term

@[simp] theorem decodeScalars_encodeScalars (scalars : List Nat) :
    decodeScalars (encodeScalars scalars) = some scalars := by
  induction scalars with
  | nil => simp [encodeScalars, decodeScalars]
  | cons scalar rest ih => simp [encodeScalars, decodeScalars, ih]

theorem decodeScalars_reflects (term : GroundTerm) (scalars : List Nat)
    (decoded : decodeScalars term = some scalars) : term = encodeScalars scalars := by
  unfold decodeScalars at decoded
  split at decoded
  · cases decoded
    rfl
  · rename_i scalar rest
    split at decoded
    · rename_i nonnegative
      cases tailDecoded : decodeScalars rest with
      | none => simp [tailDecoded] at decoded
      | some tail =>
        have output : scalar.toNat :: tail = scalars := by
          simpa [tailDecoded] using decoded
        subst scalars
        have sourceTail := decodeScalars_reflects rest tail tailDecoded
        simp [encodeScalars, sourceTail, Int.toNat_of_nonneg nonnegative]
    · simp at decoded
  · simp at decoded
termination_by sizeOf term

theorem decodeScalars_iff (term : GroundTerm) (scalars : List Nat) :
    decodeScalars term = some scalars ↔ term = encodeScalars scalars := by
  constructor
  · exact decodeScalars_reflects term scalars
  · rintro rfl
    exact decodeScalars_encodeScalars scalars

theorem encodeScalars_injective : Function.Injective encodeScalars := by
  intro left right same
  have decoded := congrArg decodeScalars same
  simpa using decoded

theorem encodeScalars_aliasFree (scalars : List Nat) : AliasFree (encodeScalars scalars) := by
  induction scalars with
  | nil => exact .app (by decide) (.cons (.atom (by decide)) .nil)
  | cons scalar rest ih => exact .app (by decide) (.cons (.integer _) (.cons ih .nil))

/-- Structural lowering for the scalar-list family only. -/
def lowerScalars : GroundTerm → Option Mettapedia.GSLT.LanguageDef.CettaWire.Term
  | .app "metta-nullary" (.cons (.atom "bnf-v1:scalars-nil") .nil) =>
      some (.application "bnf-v1:scalars-nil" [])
  | .app "bnf-v1:scalars-cons" (.cons (.integer scalar) (.cons rest .nil)) =>
      if 0 ≤ scalar then do
        let loweredRest ← lowerScalars rest
        pure (.application "bnf-v1:scalars-cons" [.natural scalar.toNat, loweredRest])
      else none
  | _ => none
termination_by term => sizeOf term

@[simp] theorem lowerScalars_encodeScalars (scalars : List Nat) :
    lowerScalars (encodeScalars scalars) =
      some (PlainBnfStructuredValueCodec.encodeScalars scalars) := by
  induction scalars with
  | nil => simp [encodeScalars, lowerScalars, PlainBnfStructuredValueCodec.encodeScalars]
  | cons scalar rest ih =>
    simp [encodeScalars, lowerScalars, PlainBnfStructuredValueCodec.encodeScalars, ih]

theorem lowerScalars_reflects (term : GroundTerm)
    (wire : Mettapedia.GSLT.LanguageDef.CettaWire.Term)
    (lowered : lowerScalars term = some wire) :
    ∃ scalars, term = encodeScalars scalars ∧
      wire = PlainBnfStructuredValueCodec.encodeScalars scalars := by
  unfold lowerScalars at lowered
  split at lowered
  · cases lowered
    exact ⟨[], rfl, rfl⟩
  · rename_i scalar rest
    split at lowered
    · rename_i nonnegative
      cases tailLowered : lowerScalars rest with
      | none => simp [tailLowered] at lowered
      | some wireTail =>
        obtain ⟨tail, sourceTail, targetTail⟩ := lowerScalars_reflects rest wireTail tailLowered
        have output :
            Mettapedia.GSLT.LanguageDef.CettaWire.Term.application "bnf-v1:scalars-cons"
              [.natural scalar.toNat, wireTail] = wire := by
          simpa [tailLowered] using lowered
        refine ⟨scalar.toNat :: tail, ?_, ?_⟩
        · simp [encodeScalars, sourceTail, Int.toNat_of_nonneg nonnegative]
        · rw [← output, targetTail]
          rfl
    · simp at lowered
  · simp at lowered
termination_by sizeOf term

theorem lowerScalars_iff (term : GroundTerm)
    (wire : Mettapedia.GSLT.LanguageDef.CettaWire.Term) :
    lowerScalars term = some wire ↔
      ∃ scalars, term = encodeScalars scalars ∧
        wire = PlainBnfStructuredValueCodec.encodeScalars scalars := by
  constructor
  · exact lowerScalars_reflects term wire
  · rintro ⟨scalars, rfl, rfl⟩
    exact lowerScalars_encodeScalars scalars

theorem lowerScalars_decode_agreement (term : GroundTerm) :
    (lowerScalars term).bind PlainBnfStructuredValueCodec.decodeScalars =
      decodeScalars term := by
  cases lowered : lowerScalars term with
  | some wire =>
    obtain ⟨scalars, rfl, rfl⟩ := lowerScalars_reflects term wire lowered
    simp
  | none =>
    cases decoded : decodeScalars term with
    | none => rfl
    | some scalars =>
      have source := decodeScalars_reflects term scalars decoded
      simp [source] at lowered

/-! ## Source-shape and preservation controls -/

theorem source_nil_is_wrapped :
    encodeScalars [] = .app "metta-nullary" (.cons (.atom "bnf-v1:scalars-nil") .nil) := rfl

theorem empty_list_lowers :
    lowerScalars (encodeScalars []) = some (.application "bnf-v1:scalars-nil" []) := by
  simp [PlainBnfStructuredValueCodec.encodeScalars]

theorem zero_and_duplicate_scalars_are_preserved :
    decodeScalars (encodeScalars [0, 0, 1114111]) = some [0, 0, 1114111] ∧
      lowerScalars (encodeScalars [0, 0, 1114111]) =
        some (PlainBnfStructuredValueCodec.encodeScalars [0, 0, 1114111]) := by simp

theorem reordered_lists_are_distinct : encodeScalars [0, 1] ≠ encodeScalars [1, 0] := by
  intro same
  have values := encodeScalars_injective same
  cases values

theorem negative_scalar_is_rejected :
    decodeScalars (.app "bnf-v1:scalars-cons"
      (.cons (.integer (-1)) (.cons (encodeScalars []) .nil))) = none ∧
      lowerScalars (.app "bnf-v1:scalars-cons"
        (.cons (.integer (-1)) (.cons (encodeScalars []) .nil))) = none := by
  simp [decodeScalars, lowerScalars]

theorem non_list_tail_is_rejected :
    decodeScalars (.app "bnf-v1:scalars-cons"
      (.cons (.integer 0) (.cons (.atom "not-a-list") .nil))) = none ∧
      lowerScalars (.app "bnf-v1:scalars-cons"
        (.cons (.integer 0) (.cons (.atom "not-a-list") .nil))) = none := by
  simp [decodeScalars, lowerScalars]

theorem bare_and_unwrapped_nil_are_not_source_lists :
    decodeScalars (.atom "bnf-v1:scalars-nil") = none ∧
      decodeScalars (.app "bnf-v1:scalars-nil" .nil) = none ∧
      lowerScalars (.app "bnf-v1:scalars-nil" .nil) = none := by
  simp [decodeScalars, lowerScalars]

/-- Structural decoding deliberately does not perform Unicode admission. -/
theorem scalar_admission_is_separate :
    decodeScalars (encodeScalars [55296, 1114112]) = some [55296, 1114112] := by simp

#print axioms decodeScalars_iff
#print axioms encodeScalars_injective
#print axioms encodeScalars_aliasFree
#print axioms lowerScalars_iff
#print axioms lowerScalars_decode_agreement

end Mettapedia.GSLT.Parsing.PlainBnfSourceScalarCodec
