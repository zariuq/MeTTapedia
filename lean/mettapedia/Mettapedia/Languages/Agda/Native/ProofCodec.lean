import Mettapedia.Languages.Agda.Native.RuleCodec
import Mettapedia.OSLF.Syntax.FiniteRuleLabelledProofWire

/-! Concrete native administrative rule-instance and proof decoding.
The presentation's ordered premises are executable data. No input typing
verdict is trusted: the shared decoder reconstructs all indexed children.
Data labels avoid expanding syntax into deeply nested natural pairing codes. -/

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.Native.Codec
open Mettapedia.OSLF.Binding.WireCodec Mettapedia.Languages.Agda.Structural

abbrev NativeTree := AdministrativeStatics.Derivation
abbrev PackedTree := Mettapedia.OSLF.Binding.FiniteRuleLabelledProofWire.Packed AdministrativeStatics.presentation
abbrev ProofWire := Mettapedia.OSLF.Binding.FiniteRuleLabelledProofWire.Wire Data

def dataShapeCodec : Mettapedia.OSLF.Binding.FiniteRuleLabelledProofWire.ShapeCodec AdministrativeStatics.presentation Data where
  encode := ruleShape.put
  decode := ruleShape.canonicalGet
  roundtrip := ruleShape.canonicalGet_put
  canonical := ruleShape.put_of_canonicalGet

/-- Return the actual ordered premise judgments required by the decoded
native rule. This function is ordinary computable rule data. -/
def expectedPremises (label : Data) : Option (List AdministrativeStatics.Judgment) := do
  let ⟨_, shape⟩ ← dataShapeCodec.decode label
  return AdministrativeStatics.premises shape

def encode {j : AdministrativeStatics.Judgment} (tree : NativeTree j) : ProofWire :=
  Mettapedia.OSLF.Binding.FiniteRuleLabelledProofWire.encode AdministrativeStatics.presentation dataShapeCodec tree

def encodePacked (tree : PackedTree) : ProofWire := encode tree.2

def decode (wire : ProofWire) : Option PackedTree :=
  Mettapedia.OSLF.Binding.FiniteRuleLabelledProofWire.decode AdministrativeStatics.presentation dataShapeCodec wire

def decodeAt (j : AdministrativeStatics.Judgment) (wire : ProofWire) : Option (NativeTree j) :=
  Mettapedia.OSLF.Binding.FiniteRuleLabelledProofWire.decodeAt AdministrativeStatics.presentation dataShapeCodec j wire

def check (j : AdministrativeStatics.Judgment) (wire : ProofWire) : Bool :=
  Mettapedia.OSLF.Binding.FiniteRuleLabelledProofWire.check AdministrativeStatics.presentation dataShapeCodec j wire

theorem decode_encode {j : AdministrativeStatics.Judgment} (tree : NativeTree j) :
    decode (encode tree) = some ⟨j, tree⟩ :=
  Mettapedia.OSLF.Binding.FiniteRuleLabelledProofWire.decode_encode AdministrativeStatics.presentation dataShapeCodec tree

theorem encode_decode (wire : ProofWire) (tree : PackedTree)
    (accepted : decode wire = some tree) : encodePacked tree = wire :=
  Mettapedia.OSLF.Binding.FiniteRuleLabelledProofWire.encode_decode AdministrativeStatics.presentation dataShapeCodec wire tree accepted

theorem decodeAt_encode {j : AdministrativeStatics.Judgment} (tree : NativeTree j) :
    decodeAt j (encode tree) = some tree :=
  Mettapedia.OSLF.Binding.FiniteRuleLabelledProofWire.decodeAt_encode AdministrativeStatics.presentation dataShapeCodec tree

theorem decodeAt_exact {j : AdministrativeStatics.Judgment} {wire : ProofWire}
    {tree : NativeTree j} (accepted : decodeAt j wire = some tree) : encode tree = wire :=
  Mettapedia.OSLF.Binding.FiniteRuleLabelledProofWire.decodeAt_exact
    AdministrativeStatics.presentation dataShapeCodec accepted

theorem encodePacked_injective : Function.Injective encodePacked :=
  Mettapedia.OSLF.Binding.FiniteRuleLabelledProofWire.encodePacked_injective AdministrativeStatics.presentation dataShapeCodec

theorem check_iff (j : AdministrativeStatics.Judgment) (wire : ProofWire) :
    check j wire = true ↔ ∃ tree : NativeTree j, encode tree = wire :=
  Mettapedia.OSLF.Binding.FiniteRuleLabelledProofWire.check_iff AdministrativeStatics.presentation dataShapeCodec j wire

/-- Every accepted wire determines one exact proof history, and every native
history is accepted as itself. This is not a derivability decision procedure. -/
def acceptedEquiv : PackedTree ≃ { wire : ProofWire // (decode wire).isSome } :=
  Mettapedia.OSLF.Binding.FiniteRuleLabelledProofWire.acceptedEquiv AdministrativeStatics.presentation dataShapeCodec

theorem expectedPremises_encode {j : AdministrativeStatics.Judgment}
    (shape : AdministrativeStatics.RuleShape j) :
    expectedPremises (dataShapeCodec.encode ⟨j, shape⟩) =
      some (AdministrativeStatics.premises shape) := by
  rw [expectedPremises, dataShapeCodec.roundtrip]
  rfl

end Mettapedia.Languages.Agda.Native.Codec
