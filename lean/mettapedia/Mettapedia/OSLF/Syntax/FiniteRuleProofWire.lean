import Mettapedia.OSLF.Syntax.FiniteRuleLabelledProofWire

/-!
# Natural-number labels for the shared finite-rule proof wire

This is the Nat specialization of the arbitrary-label engine. Executable use
requires an effective shape codec, judgment equality, and ordered premises.
All checking and proof reconstruction execute the shared implementation.
The round trips retain the supplied ordered proof history; rejecting a wire
does not refute its judgment.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.FiniteRuleProofWire
open Mettapedia.OSLF.Binding.FiniteRulePremiseLists

universe u v
variable {J : Type u} (F : FinitePresentation.{0,u,v} Unit (fun _ => J))

abbrev PackedShape := FiniteRuleLabelledProofWire.PackedShape F
abbrev Packed := FiniteRuleLabelledProofWire.Packed F
abbrev ShapeCodec := FiniteRuleLabelledProofWire.ShapeCodec F Nat
abbrev Wire := FiniteRuleLabelledProofWire.Wire Nat

@[match_pattern] abbrev Wire.node (label : Nat) (children : List Wire) : Wire :=
  FiniteRuleLabelledProofWire.Wire.node label children

noncomputable abbrev Wire.rec := @FiniteRuleLabelledProofWire.Wire.rec Nat
noncomputable abbrev Wire.recOn := @FiniteRuleLabelledProofWire.Wire.recOn Nat
abbrev Wire.casesOn := @FiniteRuleLabelledProofWire.Wire.casesOn Nat
abbrev instReprWire : Repr Wire := inferInstanceAs (Repr (FiniteRuleLabelledProofWire.Wire Nat))

namespace ShapeCodec
variable {F}

@[match_pattern] abbrev mk
    (encode : PackedShape F → Nat) (decode : Nat → Option (PackedShape F))
    (roundtrip : ∀ shape, decode (encode shape) = some shape)
    (canonical : ∀ label shape, decode label = some shape → encode shape = label) :
    ShapeCodec F := ⟨encode, decode, roundtrip, canonical⟩

abbrev encode (codec : ShapeCodec F) := FiniteRuleLabelledProofWire.ShapeCodec.encode codec
abbrev decode (codec : ShapeCodec F) := FiniteRuleLabelledProofWire.ShapeCodec.decode codec
abbrev roundtrip (codec : ShapeCodec F) := FiniteRuleLabelledProofWire.ShapeCodec.roundtrip codec
abbrev canonical (codec : ShapeCodec F) := FiniteRuleLabelledProofWire.ShapeCodec.canonical codec
end ShapeCodec

variable (codec : ShapeCodec F)

def encode {j : J} (tree : F.Derivation () j) : Wire :=
  FiniteRuleLabelledProofWire.encode F codec tree

variable [DecidableEq J]

def atIndex (j : J) (packet : Packed F) : Option (F.Derivation () j) :=
  FiniteRuleLabelledProofWire.atIndex F j packet

def assemble (indices : List J) (children : List (Option (Packed F))) :
    Option (Evidence (F.Derivation ()) indices) :=
  FiniteRuleLabelledProofWire.assemble F indices children

def decode (wire : Wire) : Option (Packed F) := FiniteRuleLabelledProofWire.decode F codec wire

@[simp] theorem atIndex_self {j : J} (tree : F.Derivation () j) :
    atIndex F j ⟨j, tree⟩ = some tree := FiniteRuleLabelledProofWire.atIndex_self F tree

theorem assemble_ofFn (indices : List J) (children : Evidence (F.Derivation ()) indices) :
    assemble F indices (List.ofFn fun p => some ⟨indices.get p, children p⟩) = some children :=
  FiniteRuleLabelledProofWire.assemble_ofFn F indices children

theorem decode_encode {j : J} (tree : F.Derivation () j) :
    decode F codec (encode F codec tree) = some ⟨j, tree⟩ :=
  FiniteRuleLabelledProofWire.decode_encode F codec tree

def encodePacked (tree : Packed F) : Wire := FiniteRuleLabelledProofWire.encodePacked F codec tree

@[simp] theorem decode_encodePacked (tree : Packed F) :
    decode F codec (encodePacked F codec tree) = some tree :=
  FiniteRuleLabelledProofWire.decode_encodePacked F codec tree

theorem encodePacked_injective : Function.Injective (encodePacked F codec) :=
  FiniteRuleLabelledProofWire.encodePacked_injective F codec

theorem atIndex_eq_some {j : J} {packet : Packed F} {tree : F.Derivation () j}
    (accepted : atIndex F j packet = some tree) : packet = ⟨j, tree⟩ :=
  FiniteRuleLabelledProofWire.atIndex_eq_some F accepted

theorem assemble_eq_some (indices : List J) (packets : List (Option (Packed F)))
    (children : Evidence (F.Derivation ()) indices)
    (accepted : assemble F indices packets = some children) :
    packets = List.ofFn fun p => some ⟨indices.get p, children p⟩ :=
  FiniteRuleLabelledProofWire.assemble_eq_some F indices packets children accepted

theorem list_decode_inverse (wires : List Wire) (packets : List (Packed F))
    (matched : wires.map (decode F codec) = packets.map some)
    (inverse : ∀ wire ∈ wires, ∀ packet, decode F codec wire = some packet →
      encodePacked F codec packet = wire) :
    packets.map (encodePacked F codec) = wires :=
  FiniteRuleLabelledProofWire.list_decode_inverse F codec wires packets matched inverse

theorem encode_decode (wire : Wire) (packet : Packed F)
    (accepted : decode F codec wire = some packet) : encodePacked F codec packet = wire :=
  FiniteRuleLabelledProofWire.encode_decode F codec wire packet accepted

def decodeAt (j : J) (wire : Wire) : Option (F.Derivation () j) :=
  FiniteRuleLabelledProofWire.decodeAt F codec j wire

theorem decodeAt_encode {j : J} (tree : F.Derivation () j) :
    decodeAt F codec j (encode F codec tree) = some tree :=
  FiniteRuleLabelledProofWire.decodeAt_encode F codec tree

theorem decodeAt_exact {j : J} {wire : Wire} {tree : F.Derivation () j}
    (accepted : decodeAt F codec j wire = some tree) : encode F codec tree = wire :=
  FiniteRuleLabelledProofWire.decodeAt_exact F codec accepted

theorem decodeAt_iff {j : J} {wire : Wire} {tree : F.Derivation () j} :
    decodeAt F codec j wire = some tree ↔ encode F codec tree = wire :=
  FiniteRuleLabelledProofWire.decodeAt_iff F codec

def check (j : J) (wire : Wire) : Bool := FiniteRuleLabelledProofWire.check F codec j wire

theorem check_iff (j : J) (wire : Wire) :
    check F codec j wire = true ↔ ∃ tree : F.Derivation () j, encode F codec tree = wire :=
  FiniteRuleLabelledProofWire.check_iff F codec j wire

def acceptedEquiv : Packed F ≃ { wire : Wire // (decode F codec wire).isSome } :=
  FiniteRuleLabelledProofWire.acceptedEquiv F codec

end Mettapedia.OSLF.Binding.FiniteRuleProofWire
