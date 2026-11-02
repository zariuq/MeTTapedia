import Mettapedia.Computability.KolmogorovComplexity.FeatureBPredicates
import Mettapedia.Computability.KolmogorovComplexity.ConditionalPlainComplexity

/-!
# Conditional-interpreter adapter controls

The shared model is checked independently of any particular program decoder.
The original interpreter supplies its concrete instance in the separate
original-toolchain client. These controls expose why a one-sided word-codec
round trip is insufficient for the exact execution correspondence.
-/

set_option autoImplicit false

namespace Mettapedia.Examples.Compression.InterpreterCorrespondenceControls

open KolmogorovComplexity

theorem natural_roundtrip_alone_can_lose_symbols :
    (∀ count : Nat, (List.replicate count false).length = count) ∧
      List.replicate ([true] : List Bool).length false ≠ [true] := by
  exact ⟨fun count => List.length_replicate, by decide⟩

theorem word_roundtrip_alone_can_miss_natural_outputs (codec : NaturalWordCodec) :
    (∀ word, codec.decode ((2 * codec.encode word) / 2) = word) ∧
      2 * codec.encode (codec.decode (1 / 2)) ≠ 1 := by
  constructor
  · intro word
    rw [Nat.mul_comm 2, Nat.mul_div_left _ (by decide)]
    exact codec.decode_encode word
  · norm_num [codec.encode_decode]

end Mettapedia.Examples.Compression.InterpreterCorrespondenceControls

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Quot.sound, ``Classical.choice]
  let modules := #[`Mettapedia.Computability.KolmogorovComplexity.ConditionalProgramModel,
    `Mettapedia.Computability.KolmogorovComplexity.FeaturePredicates,
    `Mettapedia.Computability.KolmogorovComplexity.FeatureBPredicates]
  let mut names : Array Name := #[]
  let mut regular : NameSet := {}
  let mut seen : NameSet := {}
  for moduleName in modules do
    let some index := env.header.moduleNames.toList.idxOf? moduleName | throwError "missing interface module {moduleName}"
    let data := env.header.moduleData[index]!
    names := names ++ data.constNames ++ data.extraConstNames
    for name in data.constNames do regular := regular.insert name
  for (name, _) in env.constants.toList do
    if (`Mettapedia.Examples.Compression.InterpreterCorrespondenceControls).isPrefixOf name then
      names := names.push name
      regular := regular.insert name
  let mut safe := 0
  let mut theorems := 0
  let mut audited : Array Json := #[]
  for name in names do
    if seen.contains name then continue
    seen := seen.insert name
    let some info := env.checked.get.find? name | do
      if regular.contains name then throwError "missing interface declaration {name}"
      continue
    if info.isUnsafe || info.isPartial then throwError "nonlogical interface declaration {name}"
    if info matches .axiomInfo _ then throwError "new interface axiom {name}"
    let dependencies ← liftCoreM <| collectAxioms name
    for dependency in dependencies do
      unless allowed.contains dependency do throwError "unpermitted interface dependency {name}: {dependency}"
    safe := safe + 1
    if info matches .thmInfo _ then
      theorems := theorems + 1
      audited := audited.push (Json.mkObj [("name", toJson name.toString),
        ("axioms", toJson (dependencies.map Name.toString))])
  liftIO <| IO.println (Json.mkObj [("sharedInterpreterInterfaceDeclarations", toJson safe),
    ("theorems", toJson theorems), ("auditedTheorems", toJson audited)]).compress
