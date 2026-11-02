import Mettapedia.Computability.KolmogorovComplexity.RandomnessLevelSearch

/-!
# From unbounded finite-string tests to one shared compressive feature

The converse uses the existing effective prefix-machine host and its actual
compiler-prefix simulations. Arbitrary ignored trailing bits would violate
prefix freeness. Instead the threshold header is followed by one complete
unary padding word. Every padding bit is charged; the padded program family
is itself prefix-free. The threshold is binary, not unary encoded.
-/

set_option autoImplicit false

namespace KolmogorovComplexity.FeatureTheory.Randomness

open Mettapedia.UniversalAI.TimeBoundedAIXI
open FiniteBitStrings
open scoped Classical

def paddingTest (word : BinString) : Bool := if word.dropWhile id = [false] then true else false

theorem paddingTest_primrec : Primrec paddingTest :=
  Primrec.ite (Primrec.eq.comp (Primrec.list_dropWhile Primrec.id) (Primrec.const [false]))
    (Primrec.const true) (Primrec.const false)

theorem machinePrefix_eq_replicate (count : Nat) : machinePrefix count = List.replicate count true ++ [false] := by
  induction count with
  | zero => rfl
  | succ count ih => simp [machinePrefix, List.replicate_succ, ih]

theorem paddingTest_machinePrefix (count : Nat) : paddingTest (machinePrefix count) = true := by
  induction count with
  | zero => rfl
  | succ count ih => simpa [paddingTest, machinePrefix] using ih

theorem paddingTest_sound {word : BinString} (accepted : paddingTest word = true) :
    ∃ count, word = machinePrefix count := by
  have tail : word.dropWhile id = [false] := by simpa [paddingTest] using accepted
  refine ⟨(word.takeWhile id).length, ?_⟩
  have counted : countLeadingTrues word = ((word.takeWhile id).length, [false]) := by
    rw [countLeadingTrues_eq_takeWhile_dropWhile]
    exact congrArg (Prod.mk _) tail
  rw [machinePrefix_eq_replicate]
  exact countLeadingTrues_decompose counted

def parseThreshold (program : BinString) : Option Nat :=
  (e1decode program).bind fun fields => if paddingTest fields.2 then some (ofBinaryBits fields.1) else none

theorem parseThreshold_primrec : Primrec parseThreshold := by
  have body : Primrec₂ fun (_program : BinString) (fields : BinString × BinString) =>
      if paddingTest fields.2 then some (ofBinaryBits fields.1) else none :=
    (Primrec.ite
      (Primrec.eq.comp (paddingTest_primrec.comp (Primrec.snd.comp Primrec.snd)) (Primrec.const true))
      (Primrec.option_some.comp (ofBinaryBits_primrec.comp (Primrec.fst.comp Primrec.snd)))
      (Primrec.const none)).to₂
  exact Primrec.option_bind e1decode_primrec body

theorem parseThreshold_encoded (threshold padding : Nat) :
    parseThreshold (e1encode (binaryBits threshold) ++ machinePrefix padding) = some threshold := by
  simp [parseThreshold, e1decode_e1encode_append, paddingTest_machinePrefix, ofBinaryBits_binaryBits]

theorem parseThreshold_prefix_free : PrefixFree {program | (parseThreshold program).isSome = true} := by
  intro first accepted second acceptedSecond different isPrefix
  obtain ⟨threshold, parsed⟩ := Option.isSome_iff_exists.mp accepted
  obtain ⟨otherThreshold, parsedSecond⟩ := Option.isSome_iff_exists.mp acceptedSecond
  unfold parseThreshold at parsed parsedSecond
  obtain ⟨fields, decoded, checked⟩ := Option.bind_eq_some_iff.mp parsed
  obtain ⟨otherFields, decodedSecond, otherChecked⟩ := Option.bind_eq_some_iff.mp parsedSecond
  have padding : paddingTest fields.2 = true := by
    split at checked <;> simp_all
  have otherPadding : paddingTest otherFields.2 = true := by
    split at otherChecked <;> simp_all
  obtain ⟨paddingCount, paddingWord⟩ := paddingTest_sound padding
  obtain ⟨otherCount, otherWord⟩ := paddingTest_sound otherPadding
  obtain ⟨suffix, extended⟩ := isPrefix
  have later := e1decode_append_of_success decoded suffix
  rw [extended, decodedSecond] at later
  have tails : fields.2 ++ suffix = otherFields.2 := (congrArg Prod.snd (Option.some.inj later)).symm
  rw [paddingWord, otherWord] at tails
  have counted := congrArg decodeMachinePrefix tails
  have emptyEnd : decodeMachinePrefix (machinePrefix otherCount) = some (otherCount, []) := by
    simpa using decodeMachinePrefix_machinePrefix otherCount []
  rw [decodeMachinePrefix_machinePrefix, emptyEnd] at counted
  have empty : suffix = [] := congrArg Prod.snd (Option.some.inj counted)
  exact different (by simpa [empty] using extended)

theorem parseThreshold_rejects_extension {program : BinString} {threshold : Nat}
    (parsed : parseThreshold program = some threshold) (suffix : BinString) (nonempty : suffix ≠ []) :
    parseThreshold (program ++ suffix) = none := by
  cases extended : parseThreshold (program ++ suffix) with
  | none => rfl
  | some other =>
      have different : program ≠ program ++ suffix := by
        intro same
        have sizes := congrArg List.length same
        cases suffix with
        | nil => exact nonempty rfl
        | cons bit rest =>
            simp only [List.length_append, List.length_cons] at sizes
            omega
      exact False.elim (parseThreshold_prefix_free program (by simp [parsed])
        (program ++ suffix) (by simp [extended]) different ⟨suffix, rfl⟩)

def thresholdAlgorithm (operation : Nat → BinString → Part BinString) : ConditionalAlgorithm :=
  fun program condition => (Part.ofOption (parseThreshold program)).bind fun threshold => operation threshold condition

theorem thresholdAlgorithm_partrec (operation : Nat → BinString → Part BinString) (effective : Partrec₂ operation) :
    Partrec₂ (thresholdAlgorithm operation) := by
  have parsed : Partrec fun input : BinString × BinString => Part.ofOption (parseThreshold input.1) :=
    (parseThreshold_primrec.comp Primrec.fst).to_comp.ofOption
  have continued : Partrec fun input : (BinString × BinString) × Nat => operation input.2 input.1.2 :=
    effective.comp Computable.snd (Computable.snd.comp Computable.fst)
  exact parsed.bind continued.to₂

noncomputable def thresholdPrefixMachine (operation : Nat → BinString → Part BinString) : ConditionalPrefixFreeMachine where
  compute := fun program condition => (parseThreshold program).bind fun threshold => (operation threshold condition).toOption
  prefix_free := by
    intro condition program extension isPrefix different halts
    cases found : (parseThreshold program).bind (fun threshold => (operation threshold condition).toOption) with
    | none => exact False.elim (halts found)
    | some source =>
        obtain ⟨threshold, parsed, _computed⟩ := Option.bind_eq_some_iff.mp found
        cases next : (parseThreshold extension).bind (fun threshold => (operation threshold condition).toOption) with
        | none => rfl
        | some other =>
            obtain ⟨otherThreshold, otherParsed, _computed⟩ := Option.bind_eq_some_iff.mp next
            exact False.elim (parseThreshold_prefix_free program (by simp [parsed]) extension
              (by simp [otherParsed]) different isPrefix)

theorem thresholdPrefixMachine_part (operation : Nat → BinString → Part BinString) (program condition : BinString) :
    Part.ofOption ((thresholdPrefixMachine operation).compute program condition) = thresholdAlgorithm operation program condition := by
  cases parsed : parseThreshold program <;>
    simp [thresholdPrefixMachine, thresholdAlgorithm, parsed, Part.of_toOption]

theorem thresholdPrefixMachine_effective (operation : Nat → BinString → Part BinString) (effective : Partrec₂ operation) :
    Effective (thresholdPrefixMachine operation) :=
  (thresholdAlgorithm_partrec operation effective).of_eq fun input => (thresholdPrefixMachine_part operation input.1 input.2).symm

noncomputable def levelPrefixMachine (code : Nat.Partrec.Code) : ConditionalPrefixFreeMachine :=
  thresholdPrefixMachine (decodeLevel code)

noncomputable def encoderPrefixMachine (code : Nat.Partrec.Code) : ConditionalPrefixFreeMachine :=
  thresholdPrefixMachine (encodeLevel code)

theorem levelPrefixMachine_effective (code : Nat.Partrec.Code) : Effective (levelPrefixMachine code) :=
  thresholdPrefixMachine_effective _ (decodeLevel_partrec code)

theorem encoderPrefixMachine_effective (code : Nat.Partrec.Code) : Effective (encoderPrefixMachine code) :=
  thresholdPrefixMachine_effective _ (encodeLevel_partrec code)

theorem levelPrefixMachine_program {code : Nat.Partrec.Code} {threshold padding : Nat} {residual source : BinString}
    (produces : source ∈ decodeLevel code threshold residual) :
    IsProgram (levelPrefixMachine code) (e1encode (binaryBits threshold) ++ machinePrefix padding) residual source := by
  simpa [IsProgram, levelPrefixMachine, thresholdPrefixMachine, parseThreshold_encoded] using produces

theorem encoderPrefixMachine_program {code : Nat.Partrec.Code} {threshold padding : Nat} {source residual : BinString}
    (produces : residual ∈ encodeLevel code threshold source) :
    IsProgram (encoderPrefixMachine code) (e1encode (binaryBits threshold) ++ machinePrefix padding) source residual := by
  simpa [IsProgram, encoderPrefixMachine, thresholdPrefixMachine, parseThreshold_encoded] using produces

/-- A singleton literal prefix domain witnesses the output-completeness of
a compiler-universal host without an unrestricted constant-output domain. -/
def literalPrefixMachine (output : BinString) : ConditionalPrefixFreeMachine where
  compute := fun program _condition => if program = [] then some output else none
  prefix_free := by
    intro condition program extension isPrefix different halts
    have empty : program = [] := by simpa using halts
    have nonempty : extension ≠ [] := by simpa [empty] using different.symm
    simp [nonempty]

theorem literalPrefixMachine_effective (output : BinString) : Effective (literalPrefixMachine output) := by
  have compute : Primrec₂ fun (program condition : BinString) => if program = [] then some output else none :=
    (Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const [])) (Primrec.const (some output)) (Primrec.const none)).to₂
  exact compute.to_comp.ofOption

theorem compiler_universal_hasProgram (U : ConditionalPrefixFreeMachine)
    (universal : ∀ machine, Effective machine → Nonempty (UniformlySimulates U machine))
    (condition output : BinString) : HasProgram U condition output := by
  obtain ⟨simulation⟩ := universal (literalPrefixMachine output) (literalPrefixMachine_effective output)
  exact ⟨simulation.compilerPrefix, by
    simpa using simulation.program (p := []) (condition := condition) (x := output)
      (by simp [IsProgram, literalPrefixMachine])⟩

theorem normalization_threshold_bound (cost : Nat) : 3 * cost + 13 ≤ 2 ^ (cost + 4) := by
  induction cost with
  | zero => decide
  | succ cost ih =>
      have power : (2 : Nat) ^ (cost + 1 + 4) = 2 ^ (cost + 4) * 2 := by
        rw [show cost + 1 + 4 = (cost + 4) + 1 by omega, pow_succ]
      rw [power]
      omega

/-- A real prefix padding word realizes the exact normalization `|f|=m-1`.
The threshold remains binary encoded, with all header and padding bits paid. -/
theorem exists_normalized_program (compiler : BinString) :
    ∃ threshold padding : Nat, 0 < threshold ∧
      (compiler ++ (e1encode (binaryBits threshold) ++ machinePrefix padding)).length = threshold - 1 := by
  let threshold := 2 ^ (compiler.length + 4)
  let base := compiler.length + 2 * (binaryBits threshold).length + 2
  have binaryLength : (binaryBits threshold).length ≤ compiler.length + 5 := by
    have length := binaryBits_length threshold
    simpa only [threshold, Nat.log_pow (b := 2) (by decide : 1 < (2 : Nat))] using length
  have baseBound : base ≤ threshold - 1 := by
    have gap := normalization_threshold_bound compiler.length
    dsimp only [base, threshold] at *
    omega
  refine ⟨threshold, threshold - 1 - base, Nat.two_pow_pos _, ?_⟩
  simp only [List.length_append, e1encode_length, machinePrefix_length]
  omega

theorem uniform_test_prefix_autoencoder (U : ConditionalPrefixFreeMachine)
    (universal : ∀ machine, Effective machine → Nonempty (UniformlySimulates U machine))
    (value : BinString → Nat) (test : UniformTest value) :
    ∃ feature descriptive : BinString, ∃ threshold : Nat, feature.length = threshold - 1 ∧ 0 < threshold ∧
      ∀ source, threshold ≤ value source → ∃ residual, residual.length = source.length - threshold ∧
        IsProgram U descriptive source residual ∧ IsProgram U feature residual source := by
  obtain ⟨approximation, effective, monotone, settles⟩ := test.lowerSemicomputable
  obtain ⟨code, codeSpec⟩ := exists_approximation_code effective
  obtain ⟨decoder⟩ := universal (levelPrefixMachine code) (levelPrefixMachine_effective code)
  obtain ⟨encoder⟩ := universal (encoderPrefixMachine code) (encoderPrefixMachine_effective code)
  obtain ⟨threshold, padding, positive, length⟩ := exists_normalized_program decoder.compilerPrefix
  refine ⟨decoder.compilerPrefix ++ (e1encode (binaryBits threshold) ++ machinePrefix padding),
    encoder.compilerPrefix ++ (e1encode (binaryBits threshold) ++ machinePrefix 0),
    threshold, length, positive, fun source high => ?_⟩
  obtain ⟨residual, extracts⟩ := encodeLevel_complete codeSpec
    (lower_approximation_le monotone settles) settles test source threshold high
  obtain ⟨width, reconstructs⟩ := encodeLevel_sound code threshold source residual (test.length_ge_of_high source threshold high) extracts
  exact ⟨residual, width, encoder.program (encoderPrefixMachine_program extracts),
    decoder.program (levelPrefixMachine_program reconstructs)⟩

theorem uniform_test_prefix_decoder (U : ConditionalPrefixFreeMachine)
    (universal : ∀ machine, Effective machine → Nonempty (UniformlySimulates U machine))
    (value : BinString → Nat) (test : UniformTest value) :
    ∃ feature : BinString, ∃ threshold : Nat, feature.length = threshold - 1 ∧ 0 < threshold ∧
      ∀ source, threshold ≤ value source → ∃ residual, residual.length = source.length - threshold ∧
        IsProgram U feature residual source := by
  obtain ⟨feature, descriptive, threshold, length, positive, both⟩ := uniform_test_prefix_autoencoder U universal value test
  refine ⟨feature, threshold, length, positive, fun source high => ?_⟩
  obtain ⟨residual, width, _extracts, reconstructs⟩ := both source high
  exact ⟨residual, width, reconstructs⟩

/-- Both programs precede the source quantifier. One actual search encodes
the whole qualifying class; no source-specific literal extractor is needed. -/
theorem unbounded_test_shared_autoencoder (U : ConditionalPrefixFreeMachine)
    (universal : ∀ machine, Effective machine → Nonempty (UniformlySimulates U machine))
    (value : BinString → Nat) (test : UniformTest value)
    (unbounded : ∀ bound, ∃ source, bound < value source) :
    ∃ feature descriptive : BinString, (∃ source, feature.length < value source) ∧
      ∀ source, feature.length < value source → DescriptiveMap (prefixAlgorithm U) feature descriptive source := by
  obtain ⟨feature, descriptive, threshold, length, positive, both⟩ := uniform_test_prefix_autoencoder U universal value test
  refine ⟨feature, descriptive, unbounded feature.length, fun source high => ?_⟩
  have highLevel : threshold ≤ value source := by omega
  have enoughLength := test.length_ge_of_high source threshold highLevel
  obtain ⟨residual, width, extracts, reconstructs⟩ := both source highLevel
  refine ⟨residual, (prefixAlgorithm_runs _ _ _ _).mpr extracts,
    (prefixAlgorithm_runs _ _ _ _).mpr reconstructs, ?_⟩
  omega

/-- IC Theorem 5.2 with an explicit nonvacuity witness. No ideal shortest
feature assumption is supplied by the test or by executable cost descent. -/
theorem unbounded_test_common_feature (U : ConditionalPrefixFreeMachine)
    (universal : ∀ machine, Effective machine → Nonempty (UniformlySimulates U machine))
    (value : BinString → Nat) (test : UniformTest value)
    (unbounded : ∀ bound, ∃ source, bound < value source) :
    ∃ feature : BinString, (∃ source, feature.length < value source) ∧
      ∀ source, feature.length < value source → Feature (prefixAlgorithm U) feature source := by
  obtain ⟨feature, descriptive, present, shared⟩ := unbounded_test_shared_autoencoder U universal value test unbounded
  exact ⟨feature, present, fun source high => ⟨descriptive, shared source high⟩⟩

/-- The shared concrete effective prefix interpreter supplies the compiler
universality required above; it is not an extra unconstructed machine axiom. -/
theorem trimmed_host_unbounded_test_common_feature (value : BinString → Nat) (test : UniformTest value)
    (unbounded : ∀ bound, ∃ source, bound < value source) :
    ∃ feature : BinString, (∃ source, feature.length < value source) ∧
      ∀ source, feature.length < value source → Feature (prefixAlgorithm trimmedIndexedHost) feature source :=
  unbounded_test_common_feature trimmedIndexedHost trimmedIndexedHost_simulates_effective value test unbounded

theorem trimmed_host_unbounded_test_autoencoder (value : BinString → Nat) (test : UniformTest value)
    (unbounded : ∀ bound, ∃ source, bound < value source) :
    ∃ feature descriptive : BinString, (∃ source, feature.length < value source) ∧
      ∀ source, feature.length < value source → DescriptiveMap (prefixAlgorithm trimmedIndexedHost) feature descriptive source :=
  unbounded_test_shared_autoencoder trimmedIndexedHost trimmedIndexedHost_simulates_effective value test unbounded

end KolmogorovComplexity.FeatureTheory.Randomness
