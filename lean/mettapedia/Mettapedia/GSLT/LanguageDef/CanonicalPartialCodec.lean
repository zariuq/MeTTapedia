import Mettapedia.GSLT.LanguageDef.KernelAuthority

/-!
# Exact-image restriction for partial codecs

A `PartialCodec` requires every canonical encoding to decode, but permits a
decoder to recognize additional aliases.  That is appropriate for tolerant
ingress and insufficient for identity-sensitive proof replay.

`canonicalize` retains the original encoder and restricts decoding to wire
values that re-encode byte-for-byte (structurally, at this symbolic layer) to
the supplied value.  Its accepted wires are therefore exactly the image of
the canonical encoder.
-/

namespace Mettapedia.GSLT.LanguageDef.CanonicalPartialCodec

open Mettapedia.GSLT.LanguageDef.KernelAuthority.Checker

universe uCertificate uWire

/-- Decode only when the decoded certificate re-encodes to the exact input. -/
def decodeCanonical? {Certificate : Type uCertificate} {Wire : Type uWire}
    [DecidableEq Wire] (codec : PartialCodec Certificate Wire)
    (wire : Wire) : Option Certificate := do
  let certificate ← codec.decode wire
  if codec.encode certificate = wire then
    pure certificate
  else
    none

@[simp] theorem decodeCanonical?_encode
    {Certificate : Type uCertificate} {Wire : Type uWire}
    [DecidableEq Wire] (codec : PartialCodec Certificate Wire)
    (certificate : Certificate) :
    decodeCanonical? codec (codec.encode certificate) = some certificate := by
  simp [decodeCanonical?, codec.decode_encode]

/-- Restrict a tolerant partial codec to its exact canonical image. -/
def canonicalize {Certificate : Type uCertificate} {Wire : Type uWire}
    [DecidableEq Wire] (codec : PartialCodec Certificate Wire) :
    PartialCodec Certificate Wire where
  encode := codec.encode
  decode := decodeCanonical? codec
  decode_encode := decodeCanonical?_encode codec

theorem decodeCanonical?_eq_some_iff
    {Certificate : Type uCertificate} {Wire : Type uWire}
    [DecidableEq Wire] (codec : PartialCodec Certificate Wire)
    (wire : Wire) (certificate : Certificate) :
    decodeCanonical? codec wire = some certificate ↔
      codec.decode wire = some certificate ∧ codec.encode certificate = wire := by
  unfold decodeCanonical?
  cases decoded : codec.decode wire with
  | none => simp
  | some value =>
      by_cases canonical : codec.encode value = wire
      · constructor
        · intro accepted
          have valueEquals : value = certificate := by
            simpa [canonical] using accepted
          subst certificate
          exact ⟨rfl, canonical⟩
        · rintro ⟨sameDecode, sameEncoding⟩
          have valueEquals : value = certificate :=
            Option.some.inj sameDecode
          subst certificate
          simp [canonical]
      · constructor
        · intro accepted
          simp [canonical] at accepted
        · rintro ⟨sameDecode, sameEncoding⟩
          have valueEquals : value = certificate :=
            Option.some.inj sameDecode
          subst certificate
          exact (canonical sameEncoding).elim

/-- The restricted decoder succeeds exactly on the encoder image. -/
theorem decodeCanonical?_isSome_iff_exists_encode_eq
    {Certificate : Type uCertificate} {Wire : Type uWire}
    [DecidableEq Wire] (codec : PartialCodec Certificate Wire)
    (wire : Wire) :
    (decodeCanonical? codec wire).isSome = true ↔
      ∃ certificate, codec.encode certificate = wire := by
  constructor
  · intro accepted
    cases decoded : decodeCanonical? codec wire with
    | none => simp [decoded] at accepted
    | some certificate =>
        exact ⟨certificate,
          (decodeCanonical?_eq_some_iff codec wire certificate).mp decoded |>.2⟩
  · rintro ⟨certificate, rfl⟩
    simp

/-! ## Disjoint coproducts of canonical images -/

/-- Two wire encoders have disjoint canonical images.  This condition is
about identity, not tolerant decoding: a decoder may recognize aliases, but
no canonical encoding from the left may equal one from the right. -/
def EncoderImagesDisjoint
    {Left : Type uCertificate} {Right : Type uCertificate}
    {Wire : Type uWire}
    (left : PartialCodec Left Wire) (right : PartialCodec Right Wire) : Prop :=
  ∀ leftValue rightValue,
    left.encode leftValue ≠ right.encode rightValue

/-- Exact-image decoding on one side rejects every canonical encoding from a
disjoint side, even if the original tolerant decoder recognized it as an
alias. -/
theorem decodeCanonical?_eq_none_of_disjoint_right
    {Left : Type uCertificate} {Right : Type uCertificate}
    {Wire : Type uWire} [DecidableEq Wire]
    (left : PartialCodec Left Wire) (right : PartialCodec Right Wire)
    (disjoint : EncoderImagesDisjoint left right) (rightValue : Right) :
    decodeCanonical? left (right.encode rightValue) = none := by
  cases decoded : decodeCanonical? left (right.encode rightValue) with
  | none => rfl
  | some leftValue =>
      have sameEncoding :=
        (decodeCanonical?_eq_some_iff left (right.encode rightValue)
          leftValue).mp decoded |>.2
      exact False.elim (disjoint leftValue rightValue sameEncoding)

/-- Coproduct of two partial codecs with disjoint canonical images.  Both
inputs are canonicalized at the branch boundary, preventing a tolerant alias
from changing which summand owns a wire. -/
def sumOfDisjoint
    {Left : Type uCertificate} {Right : Type uCertificate}
    {Wire : Type uWire} [DecidableEq Wire]
    (left : PartialCodec Left Wire) (right : PartialCodec Right Wire)
    (disjoint : EncoderImagesDisjoint left right) :
    PartialCodec (Left ⊕ Right) Wire where
  encode
    | .inl leftValue => left.encode leftValue
    | .inr rightValue => right.encode rightValue
  decode wire :=
    match decodeCanonical? left wire with
    | some leftValue => some (.inl leftValue)
    | none => (decodeCanonical? right wire).map Sum.inr
  decode_encode := by
    intro value
    cases value with
    | inl leftValue =>
        simp [decodeCanonical?_encode]
    | inr rightValue =>
        rw [decodeCanonical?_eq_none_of_disjoint_right
          left right disjoint rightValue]
        simp

@[simp] theorem sumOfDisjoint_encode_inl
    {Left : Type uCertificate} {Right : Type uCertificate}
    {Wire : Type uWire} [DecidableEq Wire]
    (left : PartialCodec Left Wire) (right : PartialCodec Right Wire)
    (disjoint : EncoderImagesDisjoint left right) (value : Left) :
    (sumOfDisjoint left right disjoint).encode (.inl value) =
      left.encode value :=
  rfl

@[simp] theorem sumOfDisjoint_encode_inr
    {Left : Type uCertificate} {Right : Type uCertificate}
    {Wire : Type uWire} [DecidableEq Wire]
    (left : PartialCodec Left Wire) (right : PartialCodec Right Wire)
    (disjoint : EncoderImagesDisjoint left right) (value : Right) :
    (sumOfDisjoint left right disjoint).encode (.inr value) =
      right.encode value :=
  rfl

/-- Disjoint coproduct encoding preserves the identity of both summands. -/
theorem sumOfDisjoint_encode_injective
    {Left : Type uCertificate} {Right : Type uCertificate}
    {Wire : Type uWire} [DecidableEq Wire]
    (left : PartialCodec Left Wire) (right : PartialCodec Right Wire)
    (disjoint : EncoderImagesDisjoint left right) :
    Function.Injective (sumOfDisjoint left right disjoint).encode :=
  (sumOfDisjoint left right disjoint).encode_injective

/-- Exact-image restriction never changes canonical identity. -/
@[simp] theorem canonicalize_encode
    {Certificate : Type uCertificate} {Wire : Type uWire}
    [DecidableEq Wire] (codec : PartialCodec Certificate Wire)
    (certificate : Certificate) :
    (canonicalize codec).encode certificate = codec.encode certificate :=
  rfl

namespace Canary

def zeroUnit : PartialCodec Unit Nat where
  encode _ := 0
  decode
    | 0 => some ()
    | _ => none
  decode_encode := by intro value; cases value; rfl

def oneUnit : PartialCodec Unit Nat where
  encode _ := 1
  decode
    | 1 => some ()
    | _ => none
  decode_encode := by intro value; cases value; rfl

theorem zero_one_disjoint : EncoderImagesDisjoint zeroUnit oneUnit := by
  intro left right
  cases left
  cases right
  decide

def unitChoice : PartialCodec (Unit ⊕ Unit) Nat :=
  sumOfDisjoint zeroUnit oneUnit zero_one_disjoint

theorem unitChoice_preserves_summands :
    unitChoice.decode 0 = some (.inl ()) ∧
      unitChoice.decode 1 = some (.inr ()) := by
  decide

/-- The disjointness premise is substantive: two codecs with the same
canonical wire cannot form this identity-preserving coproduct. -/
theorem zero_self_not_disjoint :
    ¬ EncoderImagesDisjoint zeroUnit zeroUnit := by
  intro disjoint
  exact disjoint () () rfl

/-- A tolerant decoder with one noncanonical alias for `false`. -/
def tolerantBool : PartialCodec Bool Nat where
  encode
    | false => 0
    | true => 1
  decode
    | 0 => some false
    | 1 => some true
    | 2 => some false
    | _ => none
  decode_encode := by
    intro value
    cases value <;> rfl

theorem tolerant_decoder_accepts_alias :
    tolerantBool.decode 2 = some false := by
  rfl

theorem canonical_decoder_rejects_alias :
    decodeCanonical? tolerantBool 2 = none := by
  rfl

theorem canonical_decoder_preserves_true :
    decodeCanonical? tolerantBool (tolerantBool.encode true) = some true := by
  simp

theorem alias_is_not_in_encoder_image :
    ¬ ∃ value, tolerantBool.encode value = 2 := by
  intro image
  rcases image with ⟨value, equality⟩
  cases value <;> simp [tolerantBool] at equality

end Canary

#print axioms decodeCanonical?_eq_some_iff
#print axioms decodeCanonical?_isSome_iff_exists_encode_eq
#print axioms decodeCanonical?_eq_none_of_disjoint_right
#print axioms sumOfDisjoint_encode_injective
#print axioms Canary.unitChoice_preserves_summands
#print axioms Canary.zero_self_not_disjoint
#print axioms Canary.alias_is_not_in_encoder_image

end Mettapedia.GSLT.LanguageDef.CanonicalPartialCodec
