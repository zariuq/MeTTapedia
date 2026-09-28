import Mettapedia.Languages.Agda.Native.JudgmentCodec

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.Native.Codec
open Mettapedia.OSLF.Binding.WireCodec Mettapedia.Languages.Agda.Structural

abbrev PackedCoreShape := Sigma Statics.RuleShape

def putCoreShape : PackedCoreShape → Data
  | ⟨_, .empty⟩ => .atom 0
  | ⟨_, @Statics.RuleShape.extend n Γ A⟩ =>
      .pair (.atom 1) (.pair (context.put ⟨n, Γ⟩) (.pair ((rawTerm n .type).put A) (.atom 0)))
  | ⟨_, @Statics.RuleShape.formation n Γ k a⟩ =>
      .pair (.atom 2) (.pair (context.put ⟨n, Γ⟩) (.pair ((Codec.nat).put k) (.pair ((rawTerm n .term).put a) (.atom 0))))
  | ⟨_, @Statics.RuleShape.sort n Γ k⟩ =>
      .pair (.atom 3) (.pair (context.put ⟨n, Γ⟩) (.pair ((Codec.nat).put k) (.atom 0)))
  | ⟨_, @Statics.RuleShape.variable n Γ v⟩ =>
      .pair (.atom 4) (.pair (context.put ⟨n, Γ⟩) (.pair ((Mettapedia.OSLF.Binding.WireCodec.varCodec (S := sig) (scope n) .term).put v) (.atom 0)))
  | ⟨_, @Statics.RuleShape.pi n Γ A B⟩ =>
      .pair (.atom 5) (.pair (context.put ⟨n, Γ⟩) (.pair ((typeParameter n).put A) (.pair ((typeBody n).put B) (.atom 0))))
  | ⟨_, @Statics.RuleShape.lambda n Γ A B body⟩ =>
      .pair (.atom 6) (.pair (context.put ⟨n, Γ⟩) (.pair ((typeParameter n).put A) (.pair ((typeBody n).put B) (.pair ((termBody n).put body) (.atom 0)))))
  | ⟨_, @Statics.RuleShape.application n Γ A B f a⟩ =>
      .pair (.atom 7) (.pair (context.put ⟨n, Γ⟩) (.pair ((typeParameter n).put A) (.pair ((typeBody n).put B) (.pair ((rawTerm n .term).put f) (.pair ((rawTerm n .term).put a) (.atom 0))))))
  | ⟨_, @Statics.RuleShape.conversion n Γ t A B⟩ =>
      .pair (.atom 8) (.pair (context.put ⟨n, Γ⟩) (.pair ((rawTerm n .term).put t) (.pair ((rawTerm n .type).put A) (.pair ((rawTerm n .type).put B) (.atom 0)))))
  | ⟨_, @Statics.RuleShape.typeEquality n Γ k a b⟩ =>
      .pair (.atom 9) (.pair (context.put ⟨n, Γ⟩) (.pair ((Codec.nat).put k) (.pair ((rawTerm n .term).put a) (.pair ((rawTerm n .term).put b) (.atom 0)))))
  | ⟨_, @Statics.RuleShape.reflexivity n Γ t A⟩ =>
      .pair (.atom 10) (.pair (context.put ⟨n, Γ⟩) (.pair ((rawTerm n .term).put t) (.pair ((rawTerm n .type).put A) (.atom 0))))
  | ⟨_, @Statics.RuleShape.symmetry n Γ t u A⟩ =>
      .pair (.atom 11) (.pair (context.put ⟨n, Γ⟩) (.pair ((rawTerm n .term).put t) (.pair ((rawTerm n .term).put u) (.pair ((rawTerm n .type).put A) (.atom 0)))))
  | ⟨_, @Statics.RuleShape.transitivity n Γ t u v A⟩ =>
      .pair (.atom 12) (.pair (context.put ⟨n, Γ⟩) (.pair ((rawTerm n .term).put t) (.pair ((rawTerm n .term).put u) (.pair ((rawTerm n .term).put v) (.pair ((rawTerm n .type).put A) (.atom 0))))))
  | ⟨_, @Statics.RuleShape.equalityConversion n Γ t u A B⟩ =>
      .pair (.atom 13) (.pair (context.put ⟨n, Γ⟩) (.pair ((rawTerm n .term).put t) (.pair ((rawTerm n .term).put u) (.pair ((rawTerm n .type).put A) (.pair ((rawTerm n .type).put B) (.atom 0))))))
  | ⟨_, @Statics.RuleShape.piCongruence n Γ A A2 B B2⟩ =>
      .pair (.atom 14) (.pair (context.put ⟨n, Γ⟩) (.pair ((typeParameter n).put A) (.pair ((typeParameter n).put A2) (.pair ((typeBody n).put B) (.pair ((typeBody n).put B2) (.atom 0))))))
  | ⟨_, @Statics.RuleShape.applicationCongruence n Γ A B f g a b⟩ =>
      .pair (.atom 15) (.pair (context.put ⟨n, Γ⟩) (.pair ((typeParameter n).put A) (.pair ((typeBody n).put B) (.pair ((rawTerm n .term).put f) (.pair ((rawTerm n .term).put g) (.pair ((rawTerm n .term).put a) (.pair ((rawTerm n .term).put b) (.atom 0))))))))
  | ⟨_, @Statics.RuleShape.beta n Γ A B body a⟩ =>
      .pair (.atom 16) (.pair (context.put ⟨n, Γ⟩) (.pair ((typeParameter n).put A) (.pair ((typeBody n).put B) (.pair ((termBody n).put body) (.pair ((rawTerm n .term).put a) (.atom 0))))))
  | ⟨_, @Statics.RuleShape.eta n Γ A B f g⟩ =>
      .pair (.atom 17) (.pair (context.put ⟨n, Γ⟩) (.pair ((typeParameter n).put A) (.pair ((typeBody n).put B) (.pair ((rawTerm n .term).put f) (.pair ((rawTerm n .term).put g) (.atom 0))))))

def getCoreShape : Data → Option PackedCoreShape
  | .atom 0 => some ⟨_, .empty⟩
  | .pair (.atom 1) (.pair Γwire (.pair Awire (.atom 0))) => do
      let ⟨n, Γ⟩ ← context.get Γwire
      let A ← (rawTerm n .type).get Awire
      return ⟨_, .extend Γ A⟩
  | .pair (.atom 2) (.pair Γwire (.pair kwire (.pair awire (.atom 0)))) => do
      let ⟨n, Γ⟩ ← context.get Γwire
      let k ← (Codec.nat).get kwire
      let a ← (rawTerm n .term).get awire
      return ⟨_, .formation Γ k a⟩
  | .pair (.atom 3) (.pair Γwire (.pair kwire (.atom 0))) => do
      let ⟨_n, Γ⟩ ← context.get Γwire
      let k ← (Codec.nat).get kwire
      return ⟨_, .sort Γ k⟩
  | .pair (.atom 4) (.pair Γwire (.pair vwire (.atom 0))) => do
      let ⟨n, Γ⟩ ← context.get Γwire
      let v ← (Mettapedia.OSLF.Binding.WireCodec.varCodec (S := sig) (scope n) .term).get vwire
      return ⟨_, .variable Γ v⟩
  | .pair (.atom 5) (.pair Γwire (.pair Awire (.pair Bwire (.atom 0)))) => do
      let ⟨n, Γ⟩ ← context.get Γwire
      let A ← (typeParameter n).get Awire
      let B ← (typeBody n).get Bwire
      return ⟨_, .pi Γ A B⟩
  | .pair (.atom 6) (.pair Γwire (.pair Awire (.pair Bwire (.pair bodywire (.atom 0))))) => do
      let ⟨n, Γ⟩ ← context.get Γwire
      let A ← (typeParameter n).get Awire
      let B ← (typeBody n).get Bwire
      let body ← (termBody n).get bodywire
      return ⟨_, .lambda Γ A B body⟩
  | .pair (.atom 7) (.pair Γwire (.pair Awire (.pair Bwire (.pair fwire (.pair awire (.atom 0)))))) => do
      let ⟨n, Γ⟩ ← context.get Γwire
      let A ← (typeParameter n).get Awire
      let B ← (typeBody n).get Bwire
      let f ← (rawTerm n .term).get fwire
      let a ← (rawTerm n .term).get awire
      return ⟨_, .application Γ A B f a⟩
  | .pair (.atom 8) (.pair Γwire (.pair twire (.pair Awire (.pair Bwire (.atom 0))))) => do
      let ⟨n, Γ⟩ ← context.get Γwire
      let t ← (rawTerm n .term).get twire
      let A ← (rawTerm n .type).get Awire
      let B ← (rawTerm n .type).get Bwire
      return ⟨_, .conversion Γ t A B⟩
  | .pair (.atom 9) (.pair Γwire (.pair kwire (.pair awire (.pair bwire (.atom 0))))) => do
      let ⟨n, Γ⟩ ← context.get Γwire
      let k ← (Codec.nat).get kwire
      let a ← (rawTerm n .term).get awire
      let b ← (rawTerm n .term).get bwire
      return ⟨_, .typeEquality Γ k a b⟩
  | .pair (.atom 10) (.pair Γwire (.pair twire (.pair Awire (.atom 0)))) => do
      let ⟨n, Γ⟩ ← context.get Γwire
      let t ← (rawTerm n .term).get twire
      let A ← (rawTerm n .type).get Awire
      return ⟨_, .reflexivity Γ t A⟩
  | .pair (.atom 11) (.pair Γwire (.pair twire (.pair uwire (.pair Awire (.atom 0))))) => do
      let ⟨n, Γ⟩ ← context.get Γwire
      let t ← (rawTerm n .term).get twire
      let u ← (rawTerm n .term).get uwire
      let A ← (rawTerm n .type).get Awire
      return ⟨_, .symmetry Γ t u A⟩
  | .pair (.atom 12) (.pair Γwire (.pair twire (.pair uwire (.pair vwire (.pair Awire (.atom 0)))))) => do
      let ⟨n, Γ⟩ ← context.get Γwire
      let t ← (rawTerm n .term).get twire
      let u ← (rawTerm n .term).get uwire
      let v ← (rawTerm n .term).get vwire
      let A ← (rawTerm n .type).get Awire
      return ⟨_, .transitivity Γ t u v A⟩
  | .pair (.atom 13) (.pair Γwire (.pair twire (.pair uwire (.pair Awire (.pair Bwire (.atom 0)))))) => do
      let ⟨n, Γ⟩ ← context.get Γwire
      let t ← (rawTerm n .term).get twire
      let u ← (rawTerm n .term).get uwire
      let A ← (rawTerm n .type).get Awire
      let B ← (rawTerm n .type).get Bwire
      return ⟨_, .equalityConversion Γ t u A B⟩
  | .pair (.atom 14) (.pair Γwire (.pair Awire (.pair A2wire (.pair Bwire (.pair B2wire (.atom 0)))))) => do
      let ⟨n, Γ⟩ ← context.get Γwire
      let A ← (typeParameter n).get Awire
      let A2 ← (typeParameter n).get A2wire
      let B ← (typeBody n).get Bwire
      let B2 ← (typeBody n).get B2wire
      return ⟨_, .piCongruence Γ A A2 B B2⟩
  | .pair (.atom 15) (.pair Γwire (.pair Awire (.pair Bwire (.pair fwire (.pair gwire (.pair awire (.pair bwire (.atom 0)))))))) => do
      let ⟨n, Γ⟩ ← context.get Γwire
      let A ← (typeParameter n).get Awire
      let B ← (typeBody n).get Bwire
      let f ← (rawTerm n .term).get fwire
      let g ← (rawTerm n .term).get gwire
      let a ← (rawTerm n .term).get awire
      let b ← (rawTerm n .term).get bwire
      return ⟨_, .applicationCongruence Γ A B f g a b⟩
  | .pair (.atom 16) (.pair Γwire (.pair Awire (.pair Bwire (.pair bodywire (.pair awire (.atom 0)))))) => do
      let ⟨n, Γ⟩ ← context.get Γwire
      let A ← (typeParameter n).get Awire
      let B ← (typeBody n).get Bwire
      let body ← (termBody n).get bodywire
      let a ← (rawTerm n .term).get awire
      return ⟨_, .beta Γ A B body a⟩
  | .pair (.atom 17) (.pair Γwire (.pair Awire (.pair Bwire (.pair fwire (.pair gwire (.atom 0)))))) => do
      let ⟨n, Γ⟩ ← context.get Γwire
      let A ← (typeParameter n).get Awire
      let B ← (typeBody n).get Bwire
      let f ← (rawTerm n .term).get fwire
      let g ← (rawTerm n .term).get gwire
      return ⟨_, .eta Γ A B f g⟩
  | _ => none

theorem get_putCoreShape (value : PackedCoreShape) :
    getCoreShape (putCoreShape value) = some value := by
  rcases value with ⟨j, shape⟩
  cases shape <;> simp only [putCoreShape, getCoreShape, Codec.get_put, Bind.bind, Option.bind] <;> rfl

def coreShape : Codec PackedCoreShape := ⟨putCoreShape, getCoreShape, get_putCoreShape⟩

end Mettapedia.Languages.Agda.Native.Codec
