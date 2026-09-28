import Mettapedia.Languages.Agda.Native.CoreRuleCodec

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.Native.Codec
open Mettapedia.OSLF.Binding.WireCodec Mettapedia.Languages.Agda.Structural

abbrev PackedSpineShape := Sigma SpineStatics.RuleShape

def putSpineShape : PackedSpineShape → Data
  | ⟨_, .core shape⟩ => .pair (.atom 0) (coreShape.put ⟨_, shape⟩)
  | ⟨_, @SpineStatics.RuleShape.nil n Γ A⟩ =>
      .pair (.atom 1) (.pair (context.put ⟨n, Γ⟩) (.pair ((rawTerm n .type).put A) (.atom 0)))
  | ⟨_, @SpineStatics.RuleShape.cons n Γ A B argument rest C⟩ =>
      .pair (.atom 2) (.pair (context.put ⟨n, Γ⟩) (.pair ((typeParameter n).put A) (.pair ((typeBody n).put B) (.pair ((rawTerm n .term).put argument) (.pair ((rawTerm n .spine).put rest) (.pair ((rawTerm n .type).put C) (.atom 0)))))))
  | ⟨_, @SpineStatics.RuleShape.append n Γ A first B second C⟩ =>
      .pair (.atom 3) (.pair (context.put ⟨n, Γ⟩) (.pair ((rawTerm n .type).put A) (.pair ((rawTerm n .spine).put first) (.pair ((rawTerm n .type).put B) (.pair ((rawTerm n .spine).put second) (.pair ((rawTerm n .type).put C) (.atom 0)))))))
  | ⟨_, @SpineStatics.RuleShape.inputConversion n Γ A2 A spine B⟩ =>
      .pair (.atom 4) (.pair (context.put ⟨n, Γ⟩) (.pair ((rawTerm n .type).put A2) (.pair ((rawTerm n .type).put A) (.pair ((rawTerm n .spine).put spine) (.pair ((rawTerm n .type).put B) (.atom 0))))))
  | ⟨_, @SpineStatics.RuleShape.outputConversion n Γ A spine B B2⟩ =>
      .pair (.atom 5) (.pair (context.put ⟨n, Γ⟩) (.pair ((rawTerm n .type).put A) (.pair ((rawTerm n .spine).put spine) (.pair ((rawTerm n .type).put B) (.pair ((rawTerm n .type).put B2) (.atom 0))))))
  | ⟨_, @SpineStatics.RuleShape.elimination n Γ head A spine B⟩ =>
      .pair (.atom 6) (.pair (context.put ⟨n, Γ⟩) (.pair ((rawTerm n .term).put head) (.pair ((rawTerm n .type).put A) (.pair ((rawTerm n .spine).put spine) (.pair ((rawTerm n .type).put B) (.atom 0))))))

def getSpineShape : Data → Option PackedSpineShape
  | .pair (.atom 0) payload => do
      let ⟨_, shape⟩ ← coreShape.get payload
      return ⟨_, .core shape⟩
  | .pair (.atom 1) (.pair Γwire (.pair Awire (.atom 0))) => do
      let ⟨n, Γ⟩ ← context.get Γwire
      let A ← (rawTerm n .type).get Awire
      return ⟨_, .nil Γ A⟩
  | .pair (.atom 2) (.pair Γwire (.pair Awire (.pair Bwire (.pair argumentwire (.pair restwire (.pair Cwire (.atom 0))))))) => do
      let ⟨n, Γ⟩ ← context.get Γwire
      let A ← (typeParameter n).get Awire
      let B ← (typeBody n).get Bwire
      let argument ← (rawTerm n .term).get argumentwire
      let rest ← (rawTerm n .spine).get restwire
      let C ← (rawTerm n .type).get Cwire
      return ⟨_, .cons Γ A B argument rest C⟩
  | .pair (.atom 3) (.pair Γwire (.pair Awire (.pair firstwire (.pair Bwire (.pair secondwire (.pair Cwire (.atom 0))))))) => do
      let ⟨n, Γ⟩ ← context.get Γwire
      let A ← (rawTerm n .type).get Awire
      let first ← (rawTerm n .spine).get firstwire
      let B ← (rawTerm n .type).get Bwire
      let second ← (rawTerm n .spine).get secondwire
      let C ← (rawTerm n .type).get Cwire
      return ⟨_, .append Γ A first B second C⟩
  | .pair (.atom 4) (.pair Γwire (.pair A2wire (.pair Awire (.pair spinewire (.pair Bwire (.atom 0)))))) => do
      let ⟨n, Γ⟩ ← context.get Γwire
      let A2 ← (rawTerm n .type).get A2wire
      let A ← (rawTerm n .type).get Awire
      let spine ← (rawTerm n .spine).get spinewire
      let B ← (rawTerm n .type).get Bwire
      return ⟨_, .inputConversion Γ A2 A spine B⟩
  | .pair (.atom 5) (.pair Γwire (.pair Awire (.pair spinewire (.pair Bwire (.pair B2wire (.atom 0)))))) => do
      let ⟨n, Γ⟩ ← context.get Γwire
      let A ← (rawTerm n .type).get Awire
      let spine ← (rawTerm n .spine).get spinewire
      let B ← (rawTerm n .type).get Bwire
      let B2 ← (rawTerm n .type).get B2wire
      return ⟨_, .outputConversion Γ A spine B B2⟩
  | .pair (.atom 6) (.pair Γwire (.pair headwire (.pair Awire (.pair spinewire (.pair Bwire (.atom 0)))))) => do
      let ⟨n, Γ⟩ ← context.get Γwire
      let head ← (rawTerm n .term).get headwire
      let A ← (rawTerm n .type).get Awire
      let spine ← (rawTerm n .spine).get spinewire
      let B ← (rawTerm n .type).get Bwire
      return ⟨_, .elimination Γ head A spine B⟩
  | _ => none

theorem get_putSpineShape (value : PackedSpineShape) :
    getSpineShape (putSpineShape value) = some value := by
  rcases value with ⟨j, shape⟩
  cases shape <;> simp only [putSpineShape, getSpineShape, Codec.get_put, rawTerm_roundtrip, Bind.bind, Option.bind] <;> rfl

def spineShape : Codec PackedSpineShape := ⟨putSpineShape, getSpineShape, get_putSpineShape⟩

end Mettapedia.Languages.Agda.Native.Codec
