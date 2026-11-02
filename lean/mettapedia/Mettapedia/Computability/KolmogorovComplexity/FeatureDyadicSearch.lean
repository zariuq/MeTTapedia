import Mettapedia.Computability.KolmogorovComplexity.FeatureResidualSearch
import Mettapedia.Algorithms.Compression.Framing
import Mettapedia.Machines.PrefixMachine

/-!
# Prefix-coded checked autoencoder search in machine-transition units

Franz, Antonenko and Soletskyi, "A theory of incremental compression",
Information Sciences 547 (2021), Section 4, doi:10.1016/j.ins.2020.08.035.
The separate ic-theory Section4 and Theorem41 developments informed the
allocation audit; the construction below uses the shared foundations.

Program pairs use the existing canonical two-field record. Every header is
charged. A compiled four-stack machine performs extraction, reconstruction
and the shortening check; the retained dyadic portfolio allocates its actual
TM2 transitions. This is a one-step search, not the paper's full hierarchical
ALICE machine or a native-learner running-time correspondence.
-/

set_option autoImplicit false

namespace KolmogorovComplexity.FeatureTheory.DyadicSearch

open Mettapedia.Algorithms.Compression
open Mettapedia.Machines

def pairCode (descriptive feature : BinString) : BinString :=
  Framing.encode [descriptive, feature]

theorem pairCode_primrec : Primrec₂ pairCode := by
  have front : Primrec fun fields : BinString × BinString =>
      e2encode (binaryBits 2) ++ e2encode fields.1 :=
    Primrec.list_append.comp (Primrec.const _) (e2encode_primrec.comp Primrec.fst)
  exact (Primrec.list_append.comp front (e2encode_primrec.comp Primrec.snd)).to₂.of_eq
    (fun descriptive feature => by simp [pairCode, Framing.encode, Framing.writeNat, Framing.writeFields, List.append_assoc])

def decodedFields (input : BinString) : Option (BinString × BinString) :=
  (e2decode input).bind fun first =>
    (e2decode first.2).map fun second => (first.1, second.1)

theorem decodedFields_primrec : Primrec decodedFields := by
  have following : Primrec₂ fun (_input : BinString) (first : BinString × BinString) =>
      (e2decode first.2).map fun second => (first.1, second.1) := by
    apply Primrec₂.mk
    exact Primrec.option_map (e2decode_primrec.comp (Primrec.snd.comp Primrec.snd))
      ((Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).pair (Primrec.fst.comp Primrec.snd)).to₂
  exact Primrec.option_bind e2decode_primrec following

def parsePair (input : BinString) : Option (BinString × BinString) :=
  ((e2decode input).bind fun count => decodedFields count.2).bind fun fields =>
    if pairCode fields.1 fields.2 = input then some fields else none

theorem parsePair_primrec : Primrec parsePair := by
  have decoded : Primrec fun input : BinString =>
      (e2decode input).bind fun count => decodedFields count.2 :=
    Primrec.option_bind e2decode_primrec (decodedFields_primrec.comp (Primrec.snd.comp Primrec.snd)).to₂
  have canonical : Primrec₂ fun (input : BinString) (fields : BinString × BinString) =>
      if pairCode fields.1 fields.2 = input then some fields else none := by
    apply Primrec₂.mk
    exact Primrec.ite
      (Primrec.eq.comp
        (pairCode_primrec.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)) Primrec.fst)
      (Primrec.option_some.comp Primrec.snd) (Primrec.const none)
  exact Primrec.option_bind decoded canonical

theorem parsePair_pairCode (descriptive feature : BinString) :
    parsePair (pairCode descriptive feature) = some (descriptive, feature) := by
  have finalField : e2decode (e2encode feature) = some (feature, []) := by
    simpa using e2decode_e2encode_append feature []
  simp [parsePair, decodedFields, pairCode, Framing.encode, Framing.writeNat, Framing.writeFields,
    e2decode_e2encode_append, finalField]

theorem parsePair_sound {input descriptive feature : BinString}
    (parsed : parsePair input = some (descriptive, feature)) : pairCode descriptive feature = input := by
  unfold parsePair at parsed
  obtain ⟨fields, _computed, canonical⟩ := Option.bind_eq_some_iff.mp parsed
  split at canonical
  · rename_i same
    cases Option.some.inj canonical
    exact same
  · cases canonical

def pairCodeTest (input : BinString) : Bool := (parsePair input).isSome

theorem pairCodeTest_primrec : Primrec pairCodeTest :=
  Primrec.option_isSome.comp parsePair_primrec

theorem pairCodeTest_prefixFree : PrefixFree {word | pairCodeTest word = true} := by
  intro first one second two different isPrefix
  obtain ⟨left, parsedLeft⟩ := Option.isSome_iff_exists.mp one
  obtain ⟨right, parsedRight⟩ := Option.isSome_iff_exists.mp two
  have leftCode := parsePair_sound parsedLeft
  have rightCode := parsePair_sound parsedRight
  exact Framing.record_prefixFree first ⟨[left.1, left.2], leftCode⟩
    second ⟨[right.1, right.2], rightCode⟩ different isPrefix

theorem pairCode_length (descriptive feature : BinString) :
    (pairCode descriptive feature).length =
      (Framing.writeNat 2).length +
        (descriptive.length + 2 * (binaryBits descriptive.length).length + 1) +
        (feature.length + 2 * (binaryBits feature.length).length + 1) := by
  simp [pairCode, Framing.encoded_length, Nat.add_assoc]

theorem pairCode_header_bound (descriptive feature : BinString) :
    (pairCode descriptive feature).length ≤
      descriptive.length + feature.length + (Framing.writeNat 2).length +
        2 * Nat.log 2 (descriptive.length + 1) + 2 * Nat.log 2 (feature.length + 1) + 6 := by
  have left := e2encode_length_le_log descriptive
  have right := e2encode_length_le_log feature
  rw [e2encode_length] at left right
  rw [pairCode_length]
  omega

theorem pairCode_length_framed_components (descriptive feature : BinString) :
    (pairCode descriptive feature).length = 7 + (e2encode descriptive).length + (e2encode feature).length := by
  rw [pairCode_length, e2encode_length, e2encode_length]
  have countLength : (Framing.writeNat 2).length = 7 := by decide
  omega

/-- Arbitrary plain programs do not acquire self-delimiting pair frames
with one uniform additive overhead. The header cost is part of the exponent
in the dyadic bound, not an unproved constant hidden by notation. -/
theorem pairCode_overhead_unbounded (overhead : Nat) :
    ∃ descriptive feature : BinString,
      descriptive.length + feature.length + overhead < (pairCode descriptive feature).length := by
  have nonzero : (2 : Nat) ^ (overhead + 1) ≠ 0 := (Nat.two_pow_pos _).ne'
  have digits : (binaryBits ((2 : Nat) ^ (overhead + 1))).length = overhead + 2 := by
    simp only [binaryBits, List.length_map, List.length_reverse,
      Nat.length_digits 2 _ (by decide) nonzero, Nat.log_pow (b := 2) (by decide : 1 < (2 : Nat))]
  refine ⟨List.replicate (2 ^ (overhead + 1)) true, [], ?_⟩
  rw [pairCode_length]
  simp only [List.length_replicate, List.length_nil, digits]
  omega

theorem pairCodeTest_pairCode (descriptive feature : BinString) :
    pairCodeTest (pairCode descriptive feature) = true := by
  simp [pairCodeTest, parsePair_pairCode]

theorem pairCodeTest_rejects_extension (descriptive feature suffix : BinString) (nonempty : suffix ≠ []) :
    pairCodeTest (pairCode descriptive feature ++ suffix) = false := by
  cases tested : pairCodeTest (pairCode descriptive feature ++ suffix) with
  | false => rfl
  | true =>
      have different : pairCode descriptive feature ≠ pairCode descriptive feature ++ suffix := by
        intro same
        have lengths := congrArg List.length same
        cases suffix with
        | nil => exact nonempty rfl
        | cons bit tail =>
            simp only [List.length_append, List.length_cons] at lengths
            omega
      exact False.elim (pairCodeTest_prefixFree _ (pairCodeTest_pairCode _ _) _ tested different ⟨suffix, rfl⟩)

abbrev Candidate := BinString × BinString
abbrev DecodedInput := (BinString × BinString) × BinString

def executePair (U : ConditionalAlgorithm) (input : DecodedInput) : Part (Option Candidate) :=
  (U input.1.1 input.2).bind fun residual =>
    (U input.1.2 residual).map fun rebuilt =>
      if rebuilt = input.2 ∧ input.1.2.length + residual.length < input.2.length
      then some (residual, input.1.2) else none

theorem executePair_partrec {U : ConditionalAlgorithm} (effective : Partrec₂ U) : Partrec (executePair U) := by
  have extraction : Partrec fun input : DecodedInput => U input.1.1 input.2 :=
    effective.comp (Computable.fst.comp Computable.fst) Computable.snd
  have rebuild : Partrec fun input : DecodedInput × BinString => U input.1.1.2 input.2 :=
    effective.comp (Computable.snd.comp (Computable.fst.comp Computable.fst)) Computable.snd
  have publication : Computable₂ fun (input : DecodedInput × BinString) (rebuilt : BinString) =>
      if rebuilt = input.1.2 ∧ input.1.1.2.length + input.2.length < input.1.2.length
      then some (input.2, input.1.1.2) else none := by
    apply Computable₂.mk
    have source : Primrec fun input : (DecodedInput × BinString) × BinString => input.1.1.2 :=
      Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
    have feature : Primrec fun input : (DecodedInput × BinString) × BinString => input.1.1.1.2 :=
      Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
    have residual : Primrec fun input : (DecodedInput × BinString) × BinString => input.1.2 :=
      Primrec.snd.comp Primrec.fst
    exact (Primrec.ite
      ((Primrec.eq.comp Primrec.snd source).and
        (Primrec.nat_lt.comp
          (Primrec.nat_add.comp (Primrec.list_length.comp feature) (Primrec.list_length.comp residual))
          (Primrec.list_length.comp source)))
      (Primrec.option_some.comp (residual.pair feature)) (Primrec.const none)).to_comp
  exact extraction.bind (rebuild.map publication).to₂

def autoencoder (U : ConditionalAlgorithm) (word source : BinString) : Part (Option Candidate) :=
  (Part.ofOption (parsePair word)).bind fun fields => executePair U (fields, source)

theorem autoencoder_partrec {U : ConditionalAlgorithm} (effective : Partrec₂ U) : Partrec₂ (autoencoder U) := by
  have parsed : Partrec fun input : BinString × BinString => Part.ofOption (parsePair input.1) :=
    (parsePair_primrec.comp Primrec.fst).to_comp.ofOption
  have executed : Partrec fun input : (BinString × BinString) × (BinString × BinString) =>
      executePair U (input.2, input.1.2) :=
    (executePair_partrec effective).comp (Computable.snd.pair (Computable.snd.comp Computable.fst))
  exact parsed.bind executed.to₂

theorem autoencoder_complete {U : ConditionalAlgorithm} {source : BinString}
    (step : CompressionStep U source) :
    some (step.residual, step.featureProgram) ∈
      autoencoder U (pairCode step.descriptiveProgram step.featureProgram) source := by
  simp only [autoencoder, parsePair_pairCode, Part.coe_some, Part.bind_some]
  unfold executePair
  apply Part.mem_bind step.extracts
  have computed := Part.mem_map (fun rebuilt =>
    if rebuilt = source ∧ step.featureProgram.length + step.residual.length < source.length
    then some (step.residual, step.featureProgram) else none) step.reconstructs
  simpa [step.compresses] using computed

theorem autoencoder_sound {U : ConditionalAlgorithm} {word source residual feature : BinString}
    (computed : some (residual, feature) ∈ autoencoder U word source) :
    ∃ descriptive, parsePair word = some (descriptive, feature) ∧
      residual ∈ U descriptive source ∧ source ∈ U feature residual ∧
      feature.length + residual.length < source.length := by
  obtain ⟨fields, parsed, execute⟩ := Part.mem_bind_iff.mp computed
  have decoded : parsePair word = some fields := Option.mem_def.mp (Part.mem_ofOption.mp parsed)
  obtain ⟨remaining, extracts, rebuilt⟩ := Part.mem_bind_iff.mp execute
  obtain ⟨output, reconstructs, returned⟩ := (Part.mem_map_iff _).mp rebuilt
  by_cases accepted : output = source ∧ fields.2.length + remaining.length < source.length
  · rw [if_pos accepted] at returned
    obtain ⟨sameResidual, sameFeature⟩ := Prod.mk.inj (Option.some.inj returned)
    subst residual
    subst feature
    exact ⟨fields.1, decoded, extracts, by simpa only [accepted.1] using reconstructs, accepted.2⟩
  · simp [accepted] at returned

def encodedAutoencoder (U : ConditionalAlgorithm) (input : Nat) : Part Nat :=
  (Part.ofOption (Encodable.decode (α := BinString × BinString) input)).bind fun fields =>
    (autoencoder U fields.1 fields.2).map Encodable.encode

/-- A single finite compiled program is selected before all sources and
program pairs. Its four-stack machine output is the encoded checked result. -/
theorem exists_compiled_autoencoder {U : ConditionalAlgorithm} (effective : Partrec₂ U) :
    ∃ code : Turing.ToPartrec.Code, ∀ word source,
      code.eval [Encodable.encode (word, source)] =
        (autoencoder U word source).map fun candidate => [Encodable.encode candidate] := by
  have recursive : Nat.Partrec (encodedAutoencoder U) := autoencoder_partrec effective
  have vectorRecursive : Nat.Partrec' (fun input : List.Vector Nat 1 => encodedAutoencoder U input.head) :=
    Nat.Partrec'.part_iff₁.mpr (Partrec.nat_iff.mpr recursive)
  obtain ⟨code, codeSpec⟩ := Turing.ToPartrec.Code.exists_code vectorRecursive
  refine ⟨code, fun word source => ?_⟩
  have runs := codeSpec (⟨[Encodable.encode (word, source)], rfl⟩ : List.Vector Nat 1)
  change code.eval [Encodable.encode (word, source)] =
    (encodedAutoencoder U (Encodable.encode (word, source))).map (fun encoded => [encoded]) at runs
  simpa only [encodedAutoencoder, Encodable.encodek, Part.coe_some, Part.bind_some, Part.map_map,
    Function.comp_def] using runs

def checkedWorker (code : Turing.ToPartrec.Code) (source : BinString) :
    PrefixPortfolio.Worker Turing.PartrecToTM2.Cfg' Candidate :=
  (PrefixMachine.worker (α := Option Candidate) code (fun word => Encodable.encode (word, source))).filterMap id

theorem checkedWorker_sound {U : ConditionalAlgorithm} {code : Turing.ToPartrec.Code}
    (codeSpec : ∀ word source, code.eval [Encodable.encode (word, source)] =
      (autoencoder U word source).map fun candidate => [Encodable.encode candidate])
    (source word : BinString) (work : Nat) (candidate : Candidate)
    (found : ((checkedWorker code source).searcher word).result work = some candidate) :
    some candidate ∈ autoencoder U word source := by
  rw [checkedWorker, PrefixPortfolio.Worker.filterMap_result] at found
  obtain ⟨value, read, same⟩ := Option.bind_eq_some_iff.mp found
  change value = some candidate at same
  subst value
  have computes := PrefixMachine.worker_sound code (fun word => Encodable.encode (word, source)) word work _ read
  rw [codeSpec] at computes
  obtain ⟨output, runs, same⟩ := (Part.mem_map_iff _).mp computes
  have equal : output = some candidate := Encodable.encode_injective (List.cons.inj same).1
  simpa only [equal] using runs

theorem checkedWorker_complete {U : ConditionalAlgorithm} {code : Turing.ToPartrec.Code}
    (codeSpec : ∀ word source, code.eval [Encodable.encode (word, source)] =
      (autoencoder U word source).map fun candidate => [Encodable.encode candidate])
    {source : BinString} (step : CompressionStep U source) :
    ∃ work, ((checkedWorker code source).searcher (pairCode step.descriptiveProgram step.featureProgram)).result work =
      some (step.residual, step.featureProgram) := by
  have computes : [Encodable.encode (some (step.residual, step.featureProgram))] ∈
      code.eval [Encodable.encode (pairCode step.descriptiveProgram step.featureProgram, source)] := by
    rw [codeSpec]
    exact Part.mem_map _ (autoencoder_complete step)
  obtain ⟨work, read⟩ := PrefixMachine.worker_complete code
    (fun word => Encodable.encode (word, source)) _ _ computes
  refine ⟨work, ?_⟩
  rw [checkedWorker, PrefixPortfolio.Worker.filterMap_result, read]
  rfl

theorem emitted_reconstructs {U : ConditionalAlgorithm} {code : Turing.ToPartrec.Code}
    (codeSpec : ∀ word source, code.eval [Encodable.encode (word, source)] =
      (autoencoder U word source).map fun candidate => [Encodable.encode candidate])
    (source : BinString) (count phase : Nat) {word residual feature : BinString}
    (emitted : (word, (residual, feature)) ∈ PrefixPortfolio.observations (checkedWorker code source)
      pairCodeTest phase (PrefixPortfolio.runFrom pairCodeTest (checkedWorker code source).step 0 count
        (checkedWorker code source).initial)) :
    ∃ descriptive, parsePair word = some (descriptive, feature) ∧
      residual ∈ U descriptive source ∧ source ∈ U feature residual ∧
      feature.length + residual.length < source.length := by
  obtain ⟨actualWord, _eligible, published⟩ := List.mem_filterMap.mp emitted
  obtain ⟨candidate, read, same⟩ := Option.map_eq_some_iff.mp published
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
  rw [PrefixPortfolio.runFrom_at] at read
  exact autoencoder_sound (checkedWorker_sound codeSpec source _ _ _ read)

/-- One compiled machine works for every source and every real two-way
compression step. Its retained dyadic search reaches that candidate with a
Levin bound in actual TM2 transition-allocation units. The exponent is the
complete prefix record length, not unframed component lengths plus a silently
assumed constant. No ideal shortest-feature hypothesis is introduced. -/
theorem exists_transition_bounded_search {U : ConditionalAlgorithm} (effective : Partrec₂ U) :
    ∃ code : Turing.ToPartrec.Code,
      (∀ word source, code.eval [Encodable.encode (word, source)] =
        (autoencoder U word source).map fun candidate => [Encodable.encode candidate]) ∧
      ∀ source (step : CompressionStep U source), ∃ work,
        let word := pairCode step.descriptiveProgram step.featureProgram
        let phase := word.length + Nat.clog 2 work
        let worker := checkedWorker code source
        (word, (step.residual, step.featureProgram)) ∈ PrefixPortfolio.observations worker pairCodeTest phase
          (PrefixPortfolio.runFrom pairCodeTest worker.step 0 (phase + 1) worker.initial) ∧
        (PrefixPortfolio.family pairCodeTest pairCodeTest_prefixFree worker.searcher).cost (phase + 1) ≤
          4 * 2 ^ word.length * max work 1 := by
  obtain ⟨code, codeSpec⟩ := exists_compiled_autoencoder effective
  refine ⟨code, codeSpec, fun source step => ?_⟩
  obtain ⟨work, computed⟩ := checkedWorker_complete codeSpec step
  exact ⟨work, PrefixPortfolio.retained_finds (checkedWorker code source) pairCodeTest pairCodeTest_prefixFree
    (pairCode step.descriptiveProgram step.featureProgram) (pairCodeTest_pairCode _ _)
    work (step.residual, step.featureProgram) computed⟩

#print axioms pairCode_primrec
#print axioms decodedFields_primrec
#print axioms parsePair_primrec
#print axioms parsePair_pairCode
#print axioms parsePair_sound
#print axioms pairCodeTest_primrec
#print axioms pairCodeTest_prefixFree
#print axioms pairCode_length
#print axioms pairCode_header_bound
#print axioms pairCode_length_framed_components
#print axioms pairCode_overhead_unbounded
#print axioms pairCodeTest_pairCode
#print axioms pairCodeTest_rejects_extension
#print axioms executePair_partrec
#print axioms autoencoder_partrec
#print axioms autoencoder_complete
#print axioms autoencoder_sound
#print axioms exists_compiled_autoencoder
#print axioms checkedWorker_sound
#print axioms checkedWorker_complete
#print axioms emitted_reconstructs
#print axioms exists_transition_bounded_search

end KolmogorovComplexity.FeatureTheory.DyadicSearch
