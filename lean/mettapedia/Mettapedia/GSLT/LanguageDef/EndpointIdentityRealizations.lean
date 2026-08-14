import Mettapedia.GSLT.LanguageDef.ExactEndpointCodec

/-!
# Exact endpoint identity realizations

NIK replay needs exact equality for semantic endpoints.  This module gives
three representations and states their different proof obligations:

* a canonical left-invertible codec is exact directly;
* a revisioned registry is exact when every issued key resolves back to its
  source term;
* a content envelope is exact because it retains canonical content and
  validates its digest, whereas a digest alone is exact only under an
  explicit injectivity hypothesis.

The last distinction keeps cryptographic addressing outside the logical
equality trusted by a checker.
-/

namespace Mettapedia.GSLT.LanguageDef.EndpointIdentityRealizations

open Mettapedia.GSLT.LanguageDef.ExactEndpointCodec
open Mettapedia.GSLT.LanguageDef.InteractionEventAuthority
open Mettapedia.GSLT.LanguageDef.KernelAuthority.Checker

universe uTerm uWire uRevision uKey uDigest

/-! ## Revision-bound local identities -/

/-- A compact local key is meaningful only at the revision that issued it. -/
structure RevisionedKey (Revision : Type uRevision) (Key : Type uKey) where
  revision : Revision
  key : Key
deriving DecidableEq, Repr

/-- A registry is exact when resolving every key it issues recovers the
original semantic term.  Unknown and stale keys may fail to resolve. -/
structure RevisionedRegistry (Term : Type uTerm) (Revision : Type uRevision)
    (Key : Type uKey) where
  revision : Revision
  keyOf : Term -> Key
  resolve : RevisionedKey Revision Key -> Option Term
  resolve_keyOf : forall term,
    resolve { revision := revision, key := keyOf term } = some term

namespace RevisionedRegistry

variable {Term : Type uTerm} {Revision : Type uRevision} {Key : Type uKey}

/-- The registry law is exactly the left-inverse law required at a wire
boundary. -/
def codec (registry : RevisionedRegistry Term Revision Key) :
    PartialCodec Term (RevisionedKey Revision Key) where
  encode term :=
    { revision := registry.revision
      key := registry.keyOf term }
  decode := registry.resolve
  decode_encode := registry.resolve_keyOf

/-- Revisioned local identifiers are exact endpoint identities, provided
their registry has the stated resolver law. -/
def identity [DecidableEq Revision] [DecidableEq Key]
    (registry : RevisionedRegistry Term Revision Key) :
    ExactEndpointIdentity Term :=
  ofPartialCodec registry.codec

/-- A registry satisfying the resolver law cannot issue one key for two
different terms. -/
theorem keyOf_injective (registry : RevisionedRegistry Term Revision Key) :
    Function.Injective registry.keyOf := by
  intro left right sameKey
  apply registry.codec.encode_injective
  simp [codec, sameKey]

end RevisionedRegistry

/-! ## Content-addressed publication envelopes -/

/-- A published object may carry both its compact address and the canonical
content from which that address was computed. -/
structure ContentEnvelope (Wire : Type uWire) (Digest : Type uDigest) where
  digest : Digest
  content : Wire
deriving DecidableEq, Repr

/-- The cryptographic operation is abstract here.  Exactness below never
assumes that it is injective. -/
structure ContentAddressing (Wire : Type uWire) (Digest : Type uDigest) where
  digest : Wire -> Digest

namespace ContentAddressing

variable {Term : Type uTerm} {Wire : Type uWire} {Digest : Type uDigest}

/-- Canonical content together with a recomputed digest is a fail-closed
wire codec.  The content, rather than collision resistance, supplies the
left inverse. -/
def envelopeCodec [DecidableEq Digest]
    (codec : PartialCodec Term Wire)
    (addressing : ContentAddressing Wire Digest) :
    PartialCodec Term (ContentEnvelope Wire Digest) where
  encode term :=
    let content := codec.encode term
    { digest := addressing.digest content, content := content }
  decode envelope :=
    if addressing.digest envelope.content = envelope.digest then
      codec.decode envelope.content
    else
      none
  decode_encode := by
    intro term
    simp [codec.decode_encode]

/-- A verified content envelope gives exact endpoint identity with no
collision-freedom premise. -/
def envelopeIdentity [DecidableEq Wire] [DecidableEq Digest]
    (codec : PartialCodec Term Wire)
    (addressing : ContentAddressing Wire Digest) :
    ExactEndpointIdentity Term :=
  ofPartialCodec (envelopeCodec codec addressing)

/-- Digest-only addressing is the compact projection used by publication
systems. -/
def digestOnly (codec : PartialCodec Term Wire)
    (addressing : ContentAddressing Wire Digest) (term : Term) : Digest :=
  addressing.digest (codec.encode term)

/-- Exact logical equality from a digest alone requires an explicit
collision-freedom theorem on the encoded semantic domain. -/
def digestIdentity [DecidableEq Digest]
    (codec : PartialCodec Term Wire)
    (addressing : ContentAddressing Wire Digest)
    (collisionFree : Function.Injective (digestOnly codec addressing)) :
    ExactEndpointIdentity Term where
  Identity := Digest
  decEq := inferInstance
  identify := digestOnly codec addressing
  identify_injective := collisionFree

/-- A mismatched digest is rejected before canonical content is decoded. -/
theorem mismatched_digest_rejected [DecidableEq Digest]
    (codec : PartialCodec Term Wire)
    (addressing : ContentAddressing Wire Digest)
    (envelope : ContentEnvelope Wire Digest)
    (mismatch : addressing.digest envelope.content ≠ envelope.digest) :
    (envelopeCodec codec addressing).decode envelope = none := by
  simp [envelopeCodec, mismatch]

end ContentAddressing

/-! ## Positive and negative canaries -/

namespace Canary

def boolRegistry : RevisionedRegistry Bool Bool Bool where
  revision := false
  keyOf := id
  resolve issued :=
    if issued.revision = false then some issued.key else none
  resolve_keyOf := by
    intro term
    rfl

theorem current_revision_round_trip :
    boolRegistry.resolve (boolRegistry.codec.encode true) = some true := by
  rfl

/-- Negative canary: a key from another revision is not silently reused. -/
theorem stale_revision_rejected :
    boolRegistry.resolve { revision := true, key := true } = none := by
  rfl

def constantDigest : ContentAddressing Nat Bool where
  digest := fun _ => false

abbrev boolCodec := ExactEndpointCodec.Canary.boolNatCodec

/-- Negative canary: a digest function can identify distinct canonical
contents. -/
theorem digest_collision :
    constantDigest.digest (boolCodec.encode false) =
      constantDigest.digest (boolCodec.encode true) := by
  rfl

/-- Therefore a digest alone does not automatically provide exact endpoint
identity. -/
theorem digest_only_not_injective :
    Not (Function.Injective
      (ContentAddressing.digestOnly boolCodec constantDigest)) := by
  intro injective
  have equalTerms : false = true := injective digest_collision
  cases equalTerms

def boolEnvelopeIdentity : ExactEndpointIdentity Bool :=
  ContentAddressing.envelopeIdentity boolCodec constantDigest

/-- Retaining canonical content preserves exactness even for the deliberately
colliding digest function. -/
theorem colliding_digest_envelopes_remain_distinct :
    boolEnvelopeIdentity.identify false ≠
      boolEnvelopeIdentity.identify true := by
  intro sameEnvelope
  have equalTerms := boolEnvelopeIdentity.identify_injective sameEnvelope
  cases equalTerms

/-- A forged digest field is rejected even when its canonical content is
otherwise decodable. -/
theorem forged_digest_rejected :
    (ContentAddressing.envelopeCodec boolCodec constantDigest).decode
      { digest := true, content := 0 } = none := by
  rfl

end Canary

end Mettapedia.GSLT.LanguageDef.EndpointIdentityRealizations
