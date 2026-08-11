import Mettapedia.GSLT.LanguageDef.InteractionEventAuthority
import Mettapedia.GSLT.LanguageDef.KernelAuthority

/-!
# Exact endpoint identity from a fail-closed codec

Interaction-event replay requires executable endpoint identity whose equality
cannot conflate distinct semantic terms.  Kernel wire boundaries already use
a partial decoder with a left-inverse law.  This module connects those two
interfaces: the canonical encoder of any such codec is an exact endpoint
identity.

The result is independent of the guest language, interaction presentation,
and physical wire representation.  Malformed wire values may still fail to
decode; they never participate in the identity of a semantic endpoint.
-/

namespace Mettapedia.GSLT.LanguageDef.ExactEndpointCodec

open Mettapedia.GSLT.LanguageDef.KernelAuthority
open Mettapedia.GSLT.LanguageDef.KernelAuthority.Checker
open Mettapedia.GSLT.LanguageDef.InteractionEventAuthority

universe uTerm uWire

/-- A left-invertible canonical wire encoding is an exact executable identity
for semantic endpoints. -/
def ofPartialCodec {Term : Type uTerm} {Wire : Type uWire}
    [DecidableEq Wire] (codec : PartialCodec Term Wire) :
    ExactEndpointIdentity.{uWire} Term where
  Identity := Wire
  decEq := inferInstance
  identify := codec.encode
  identify_injective := codec.encode_injective

namespace Canary

/-- A small codec with one deliberately malformed wire value. -/
def boolNatCodec : PartialCodec Bool Nat where
  encode
    | false => 0
    | true => 1
  decode
    | 0 => some false
    | 1 => some true
    | _ => none
  decode_encode := by
    intro value
    cases value <;> rfl

def boolNatIdentity : ExactEndpointIdentity Bool :=
  ofPartialCodec boolNatCodec

/-- Positive canary: canonical endpoint identity preserves a valid endpoint. -/
theorem canonical_endpoint_round_trip :
    boolNatCodec.decode (boolNatIdentity.identify true) = some true := by
  rfl

/-- Negative canary: distinct semantic endpoints cannot share an identity. -/
theorem distinct_endpoints_remain_distinct :
    boolNatIdentity.identify false ≠ boolNatIdentity.identify true := by
  change (0 : Nat) ≠ 1
  decide

def equalityChecker : Checker Bool Bool where
  check claim certificate := decide (claim = certificate)

/-- Negative canary: a noncanonical wire value remains rejected at replay. -/
theorem malformed_wire_is_rejected :
    (onWire equalityChecker boolNatCodec).check true 2 = false := by
  rfl

end Canary

end Mettapedia.GSLT.LanguageDef.ExactEndpointCodec
