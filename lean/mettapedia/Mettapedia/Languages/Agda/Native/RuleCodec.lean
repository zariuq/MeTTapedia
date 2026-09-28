import Mettapedia.Languages.Agda.Native.SpineRuleCodec

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.Native.Codec
open Mettapedia.OSLF.Binding.WireCodec Mettapedia.Languages.Agda.Structural

abbrev PackedRuleShape := Sigma AdministrativeStatics.RuleShape

def putRuleShape : PackedRuleShape → Data
  | ⟨_, .prior shape⟩ => .pair (.atom 0) (spineShape.put ⟨_, shape⟩)
  | ⟨_, @AdministrativeStatics.RuleShape.spineRefl n Γ A es B⟩ =>
      .pair (.atom 1) (.pair (context.put ⟨n, Γ⟩) (.pair ((rawTerm n .type).put A) (.pair ((rawTerm n .spine).put es) (.pair ((rawTerm n .type).put B) (.atom 0)))))
  | ⟨_, @AdministrativeStatics.RuleShape.spineSymm n Γ A es fs B⟩ =>
      .pair (.atom 2) (.pair (context.put ⟨n, Γ⟩) (.pair ((rawTerm n .type).put A) (.pair ((rawTerm n .spine).put es) (.pair ((rawTerm n .spine).put fs) (.pair ((rawTerm n .type).put B) (.atom 0))))))
  | ⟨_, @AdministrativeStatics.RuleShape.spineTrans n Γ A es fs gs B⟩ =>
      .pair (.atom 3) (.pair (context.put ⟨n, Γ⟩) (.pair ((rawTerm n .type).put A) (.pair ((rawTerm n .spine).put es) (.pair ((rawTerm n .spine).put fs) (.pair ((rawTerm n .spine).put gs) (.pair ((rawTerm n .type).put B) (.atom 0)))))))
  | ⟨_, @AdministrativeStatics.RuleShape.spineCons n Γ A B u v es fs C⟩ =>
      .pair (.atom 4) (.pair (context.put ⟨n, Γ⟩) (.pair ((typeParameter n).put A) (.pair ((typeBody n).put B) (.pair ((rawTerm n .term).put u) (.pair ((rawTerm n .term).put v) (.pair ((rawTerm n .spine).put es) (.pair ((rawTerm n .spine).put fs) (.pair ((rawTerm n .type).put C) (.atom 0)))))))))
  | ⟨_, @AdministrativeStatics.RuleShape.spineAppend n Γ A es fs B gs hs C⟩ =>
      .pair (.atom 5) (.pair (context.put ⟨n, Γ⟩) (.pair ((rawTerm n .type).put A) (.pair ((rawTerm n .spine).put es) (.pair ((rawTerm n .spine).put fs) (.pair ((rawTerm n .type).put B) (.pair ((rawTerm n .spine).put gs) (.pair ((rawTerm n .spine).put hs) (.pair ((rawTerm n .type).put C) (.atom 0)))))))))
  | ⟨_, @AdministrativeStatics.RuleShape.spineInputConversion n Γ A2 A es fs B⟩ =>
      .pair (.atom 6) (.pair (context.put ⟨n, Γ⟩) (.pair ((rawTerm n .type).put A2) (.pair ((rawTerm n .type).put A) (.pair ((rawTerm n .spine).put es) (.pair ((rawTerm n .spine).put fs) (.pair ((rawTerm n .type).put B) (.atom 0)))))))
  | ⟨_, @AdministrativeStatics.RuleShape.spineOutputConversion n Γ A es fs B B2⟩ =>
      .pair (.atom 7) (.pair (context.put ⟨n, Γ⟩) (.pair ((rawTerm n .type).put A) (.pair ((rawTerm n .spine).put es) (.pair ((rawTerm n .spine).put fs) (.pair ((rawTerm n .type).put B) (.pair ((rawTerm n .type).put B2) (.atom 0)))))))
  | ⟨_, @AdministrativeStatics.RuleShape.appendEmpty n Γ A es B⟩ =>
      .pair (.atom 8) (.pair (context.put ⟨n, Γ⟩) (.pair ((rawTerm n .type).put A) (.pair ((rawTerm n .spine).put es) (.pair ((rawTerm n .type).put B) (.atom 0)))))
  | ⟨_, @AdministrativeStatics.RuleShape.appendCons n Γ A u es fs B⟩ =>
      .pair (.atom 9) (.pair (context.put ⟨n, Γ⟩) (.pair ((rawTerm n .type).put A) (.pair ((rawTerm n .term).put u) (.pair ((rawTerm n .spine).put es) (.pair ((rawTerm n .spine).put fs) (.pair ((rawTerm n .type).put B) (.atom 0)))))))
  | ⟨_, @AdministrativeStatics.RuleShape.eliminationCongruence n Γ f g A es fs B⟩ =>
      .pair (.atom 10) (.pair (context.put ⟨n, Γ⟩) (.pair ((rawTerm n .term).put f) (.pair ((rawTerm n .term).put g) (.pair ((rawTerm n .type).put A) (.pair ((rawTerm n .spine).put es) (.pair ((rawTerm n .spine).put fs) (.pair ((rawTerm n .type).put B) (.atom 0))))))))
  | ⟨_, @AdministrativeStatics.RuleShape.emptyElimination n Γ f A⟩ =>
      .pair (.atom 11) (.pair (context.put ⟨n, Γ⟩) (.pair ((rawTerm n .term).put f) (.pair ((rawTerm n .type).put A) (.atom 0))))
  | ⟨_, @AdministrativeStatics.RuleShape.nestedElimination n Γ f A es B fs C⟩ =>
      .pair (.atom 12) (.pair (context.put ⟨n, Γ⟩) (.pair ((rawTerm n .term).put f) (.pair ((rawTerm n .type).put A) (.pair ((rawTerm n .spine).put es) (.pair ((rawTerm n .type).put B) (.pair ((rawTerm n .spine).put fs) (.pair ((rawTerm n .type).put C) (.atom 0))))))))

def getRuleShape : Data → Option PackedRuleShape
  | .pair (.atom 0) payload => do
      let ⟨_, shape⟩ ← spineShape.get payload
      return ⟨_, .prior shape⟩
  | .pair (.atom 1) (.pair Γwire (.pair Awire (.pair eswire (.pair Bwire (.atom 0))))) => do
      let ⟨n, Γ⟩ ← context.get Γwire
      let A ← (rawTerm n .type).get Awire
      let es ← (rawTerm n .spine).get eswire
      let B ← (rawTerm n .type).get Bwire
      return ⟨_, .spineRefl Γ A es B⟩
  | .pair (.atom 2) (.pair Γwire (.pair Awire (.pair eswire (.pair fswire (.pair Bwire (.atom 0)))))) => do
      let ⟨n, Γ⟩ ← context.get Γwire
      let A ← (rawTerm n .type).get Awire
      let es ← (rawTerm n .spine).get eswire
      let fs ← (rawTerm n .spine).get fswire
      let B ← (rawTerm n .type).get Bwire
      return ⟨_, .spineSymm Γ A es fs B⟩
  | .pair (.atom 3) (.pair Γwire (.pair Awire (.pair eswire (.pair fswire (.pair gswire (.pair Bwire (.atom 0))))))) => do
      let ⟨n, Γ⟩ ← context.get Γwire
      let A ← (rawTerm n .type).get Awire
      let es ← (rawTerm n .spine).get eswire
      let fs ← (rawTerm n .spine).get fswire
      let gs ← (rawTerm n .spine).get gswire
      let B ← (rawTerm n .type).get Bwire
      return ⟨_, .spineTrans Γ A es fs gs B⟩
  | .pair (.atom 4) (.pair Γwire (.pair Awire (.pair Bwire (.pair uwire (.pair vwire (.pair eswire (.pair fswire (.pair Cwire (.atom 0))))))))) => do
      let ⟨n, Γ⟩ ← context.get Γwire
      let A ← (typeParameter n).get Awire
      let B ← (typeBody n).get Bwire
      let u ← (rawTerm n .term).get uwire
      let v ← (rawTerm n .term).get vwire
      let es ← (rawTerm n .spine).get eswire
      let fs ← (rawTerm n .spine).get fswire
      let C ← (rawTerm n .type).get Cwire
      return ⟨_, .spineCons Γ A B u v es fs C⟩
  | .pair (.atom 5) (.pair Γwire (.pair Awire (.pair eswire (.pair fswire (.pair Bwire (.pair gswire (.pair hswire (.pair Cwire (.atom 0))))))))) => do
      let ⟨n, Γ⟩ ← context.get Γwire
      let A ← (rawTerm n .type).get Awire
      let es ← (rawTerm n .spine).get eswire
      let fs ← (rawTerm n .spine).get fswire
      let B ← (rawTerm n .type).get Bwire
      let gs ← (rawTerm n .spine).get gswire
      let hs ← (rawTerm n .spine).get hswire
      let C ← (rawTerm n .type).get Cwire
      return ⟨_, .spineAppend Γ A es fs B gs hs C⟩
  | .pair (.atom 6) (.pair Γwire (.pair A2wire (.pair Awire (.pair eswire (.pair fswire (.pair Bwire (.atom 0))))))) => do
      let ⟨n, Γ⟩ ← context.get Γwire
      let A2 ← (rawTerm n .type).get A2wire
      let A ← (rawTerm n .type).get Awire
      let es ← (rawTerm n .spine).get eswire
      let fs ← (rawTerm n .spine).get fswire
      let B ← (rawTerm n .type).get Bwire
      return ⟨_, .spineInputConversion Γ A2 A es fs B⟩
  | .pair (.atom 7) (.pair Γwire (.pair Awire (.pair eswire (.pair fswire (.pair Bwire (.pair B2wire (.atom 0))))))) => do
      let ⟨n, Γ⟩ ← context.get Γwire
      let A ← (rawTerm n .type).get Awire
      let es ← (rawTerm n .spine).get eswire
      let fs ← (rawTerm n .spine).get fswire
      let B ← (rawTerm n .type).get Bwire
      let B2 ← (rawTerm n .type).get B2wire
      return ⟨_, .spineOutputConversion Γ A es fs B B2⟩
  | .pair (.atom 8) (.pair Γwire (.pair Awire (.pair eswire (.pair Bwire (.atom 0))))) => do
      let ⟨n, Γ⟩ ← context.get Γwire
      let A ← (rawTerm n .type).get Awire
      let es ← (rawTerm n .spine).get eswire
      let B ← (rawTerm n .type).get Bwire
      return ⟨_, .appendEmpty Γ A es B⟩
  | .pair (.atom 9) (.pair Γwire (.pair Awire (.pair uwire (.pair eswire (.pair fswire (.pair Bwire (.atom 0))))))) => do
      let ⟨n, Γ⟩ ← context.get Γwire
      let A ← (rawTerm n .type).get Awire
      let u ← (rawTerm n .term).get uwire
      let es ← (rawTerm n .spine).get eswire
      let fs ← (rawTerm n .spine).get fswire
      let B ← (rawTerm n .type).get Bwire
      return ⟨_, .appendCons Γ A u es fs B⟩
  | .pair (.atom 10) (.pair Γwire (.pair fwire (.pair gwire (.pair Awire (.pair eswire (.pair fswire (.pair Bwire (.atom 0)))))))) => do
      let ⟨n, Γ⟩ ← context.get Γwire
      let f ← (rawTerm n .term).get fwire
      let g ← (rawTerm n .term).get gwire
      let A ← (rawTerm n .type).get Awire
      let es ← (rawTerm n .spine).get eswire
      let fs ← (rawTerm n .spine).get fswire
      let B ← (rawTerm n .type).get Bwire
      return ⟨_, .eliminationCongruence Γ f g A es fs B⟩
  | .pair (.atom 11) (.pair Γwire (.pair fwire (.pair Awire (.atom 0)))) => do
      let ⟨n, Γ⟩ ← context.get Γwire
      let f ← (rawTerm n .term).get fwire
      let A ← (rawTerm n .type).get Awire
      return ⟨_, .emptyElimination Γ f A⟩
  | .pair (.atom 12) (.pair Γwire (.pair fwire (.pair Awire (.pair eswire (.pair Bwire (.pair fswire (.pair Cwire (.atom 0)))))))) => do
      let ⟨n, Γ⟩ ← context.get Γwire
      let f ← (rawTerm n .term).get fwire
      let A ← (rawTerm n .type).get Awire
      let es ← (rawTerm n .spine).get eswire
      let B ← (rawTerm n .type).get Bwire
      let fs ← (rawTerm n .spine).get fswire
      let C ← (rawTerm n .type).get Cwire
      return ⟨_, .nestedElimination Γ f A es B fs C⟩
  | _ => none

theorem get_putRuleShape (value : PackedRuleShape) :
    getRuleShape (putRuleShape value) = some value := by
  rcases value with ⟨j, shape⟩
  cases shape <;> simp only [putRuleShape, getRuleShape, Codec.get_put, rawTerm_roundtrip, Bind.bind, Option.bind] <;> rfl

def ruleShape : Codec PackedRuleShape := ⟨putRuleShape, getRuleShape, get_putRuleShape⟩

end Mettapedia.Languages.Agda.Native.Codec
