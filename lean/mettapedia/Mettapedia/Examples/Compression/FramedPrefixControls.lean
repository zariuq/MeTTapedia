import Mettapedia.Computability.KolmogorovComplexity.FramedPrefixMachine

/-!
# Concrete framed-prefix admission and reference-comparison controls

Both shared stream codes are actual self-delimiting encoders and decoders.
The canonical source interpreter and prefix reference machine discharge the
computability and universality premises on all finite outputs. The complete
frame guard retains noncanonical and incomplete-code refusals.
-/

set_option autoImplicit false

namespace Mettapedia.Examples.Compression.FramedPrefixControls

open KolmogorovComplexity

def codes : PairedWordCode where
  head := ⟨e1encode, e1decode, e1decode_e1encode_append, e1encode_primrec, e1decode_primrec⟩
  payload := ⟨e2encode, e2decode, e2decode_e2encode_append, e2encode_primrec, e2decode_primrec⟩

def pairing : ConditionPairing := codes.head.conditionPairing

theorem two_fields_roundtrip (head payload : BinString) :
    codes.read (codes.encode head payload) = some (head, payload) :=
  codes.read_encoded head payload

theorem every_nonempty_suffix_refused (head payload suffix : BinString) (nonempty : suffix ≠ []) :
    codes.read (codes.encode head payload ++ suffix) = none :=
  codes.read_rejects_extension head payload suffix nonempty

theorem incomplete_frame_refused : codes.read [] = none ∧ codes.read [false] = none := by decide

theorem empty_fields_still_pay_headers : (codes.encode [] []).length = 2 := by decide

theorem noncanonical_payload_length_refused :
    codes.read (e1encode [] ++ e1encode [false, true] ++ [true]) = none := by decide

theorem canonical_machine_is_effective :
    Effective (codes.prefixMachine universalConditionalAlgorithm pairing) :=
  codes.prefixMachine_effective universalConditionalAlgorithm_partrec pairing

theorem canonical_machine_represents_all_outputs (condition output : BinString) :
    HasProgram (codes.prefixMachine universalConditionalAlgorithm pairing) condition output :=
  codes.prefixMachine_hasProgram universalConditionalAlgorithm universalConditionalAlgorithm_isUniversal pairing condition output

theorem canonical_reference_comparison :
    ∃ overhead : Nat, ∀ condition output,
      conditionalComplexity trimmedIndexedHost output condition ≤
          plainConditionalComplexity (codes.execute universalConditionalAlgorithm pairing.pack) output condition + overhead ∧
      plainConditionalComplexity (codes.execute universalConditionalAlgorithm pairing.pack) output condition ≤
        conditionalComplexity trimmedIndexedHost output condition +
          2 * Nat.log 2 (conditionalComplexity trimmedIndexedHost output condition + 1) + overhead :=
  codes.reference_two_sided universalConditionalAlgorithm universalConditionalAlgorithm_isUniversal
    universalConditionalAlgorithm_partrec pairing trimmedIndexedHost isReferenceMachine_trimmedIndexedHost
    3 e2encode_length_le_log

end Mettapedia.Examples.Compression.FramedPrefixControls

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let modules := #[`Mettapedia.Computability.KolmogorovComplexity.ConditionalProgramModel,
    `Mettapedia.Computability.KolmogorovComplexity.FramedProgramModel,
    `Mettapedia.Computability.KolmogorovComplexity.FramedPrefixMachine]
  let allowed := #[``propext, ``Quot.sound, ``Classical.choice]
  let mut names : Array Name := #[]
  let mut regular : NameSet := {}
  let mut seen : NameSet := {}
  for moduleName in modules do
    let some index := env.header.moduleNames.toList.idxOf? moduleName | throwError "missing framed-prefix module {moduleName}"
    let data := env.header.moduleData[index]!
    names := names ++ data.constNames ++ data.extraConstNames
    for name in data.constNames do regular := regular.insert name
  for (name, _) in env.constants.toList do
    if (`Mettapedia.Examples.Compression.FramedPrefixControls).isPrefixOf name then
      names := names.push name
      regular := regular.insert name
  let mut safe := 0
  let mut theorems := 0
  let mut audited : Array Json := #[]
  for name in names do
    if seen.contains name then continue
    seen := seen.insert name
    let some info := env.checked.get.find? name | do
      if regular.contains name then throwError "missing framed-prefix declaration {name}"
      continue
    if info.isUnsafe || info.isPartial then throwError "nonlogical framed-prefix declaration {name}"
    if info matches .axiomInfo _ then throwError "new framed-prefix axiom {name}"
    let dependencies ← liftCoreM <| collectAxioms name
    for dependency in dependencies do
      unless allowed.contains dependency do throwError "unpermitted framed-prefix dependency {name}: {dependency}"
    safe := safe + 1
    if info matches .thmInfo _ then
      theorems := theorems + 1
      audited := audited.push (Json.mkObj [("name", toJson name.toString),
        ("axioms", toJson (dependencies.map Name.toString))])
  liftIO <| IO.println (Json.mkObj [("framedPrefixDeclarations", toJson safe),
    ("theorems", toJson theorems), ("auditedTheorems", toJson audited)]).compress
