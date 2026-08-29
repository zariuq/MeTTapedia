import Mettapedia.Computability.KolmogorovComplexity.ConditionalPlainComplexity
import Mettapedia.Computability.KolmogorovComplexity.LogarithmicBounds
import Mettapedia.Computability.KolmogorovComplexity.SelfDelimitingCode

/-!
# From plain to self-delimiting conditional programs

A plain conditional algorithm becomes a conditional prefix-free machine by
accepting exactly one complete `e2encode` field as its program.  The
construction preserves and reflects successful computations, is effective
when the source algorithm is partial recursive, and has a uniform logarithmic
program-length overhead.

This is a machine-relative statement.  It does not compare unrelated choices
of plain and prefix-free universal machines.  The explicit construction is the
relationship that makes both directions of the complexity comparison valid.

The `E2` program framing and the paper-facing plain/prefix distinction follow
Franz, Antonenko, and Soletskyi (2021).  The `dmacd/ic-theory` and
`af271/ic-theory` formalization lineage helped make the missing bridge visible.
Mettapedia keeps the names `ConditionalAlgorithm` and
`ConditionalPrefixFreeMachine` at this boundary because they state the two
machine contracts explicitly.
-/

namespace KolmogorovComplexity

open scoped Classical

/-! ## Exact self-delimiting payloads -/

/-- Decode one `e2` field and accept it only when it consumes the complete
input. -/
def exactE2Payload (input : BinString) : Option BinString :=
  (e2decode input).bind fun fields =>
    if fields.2 = [] then some fields.1 else none

theorem exactE2Payload_primrec : Primrec exactE2Payload := by
  unfold exactE2Payload
  have hBranch : Primrec₂ fun (_input : BinString)
      (fields : BinString × BinString) =>
      if fields.2 = [] then some fields.1 else none := by
    apply Primrec₂.mk
    exact Primrec.ite
      (Primrec.eq.comp (Primrec.snd.comp Primrec.snd) (Primrec.const []))
      (Primrec.option_some.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.const none)
  exact Primrec.option_bind e2decode_primrec hBranch

@[simp] theorem exactE2Payload_e2encode (payload : BinString) :
    exactE2Payload (e2encode payload) = some payload := by
  have hDecode : e2decode (e2encode payload) = some (payload, []) := by
    simpa using e2decode_e2encode_append payload []
  simp [exactE2Payload, hDecode]

/-- A nonempty extension of a complete `e2` field is not itself one complete
field.  This is the negative control for exact program framing. -/
theorem exactE2Payload_e2encode_append_eq_none
    (payload suffix : BinString) (hSuffix : suffix ≠ []) :
    exactE2Payload (e2encode payload ++ suffix) = none := by
  simp [exactE2Payload, e2decode_e2encode_append, hSuffix]

/-- If an exact field is extended strictly, the extension is rejected. -/
theorem exactE2Payload_strict_extension_eq_none
    {program payload extension : BinString}
    (hPayload : exactE2Payload program = some payload)
    (hPrefix : program <+: extension) (hNe : program ≠ extension) :
    exactE2Payload extension = none := by
  obtain ⟨suffix, rfl⟩ := hPrefix
  have hSuffix : suffix ≠ [] := by
    intro hEmpty
    apply hNe
    simp [hEmpty]
  unfold exactE2Payload at hPayload ⊢
  cases hDecode : e2decode program with
  | none => simp [hDecode] at hPayload
  | some fields =>
      obtain ⟨head, rest⟩ := fields
      simp only [hDecode, Option.bind_some] at hPayload
      by_cases hRest : rest = []
      · rw [if_pos hRest] at hPayload
        have hHead : head = payload := Option.some.inj hPayload
        rw [e2decode_append_of_success hDecode suffix]
        simp [hRest, hSuffix]
      · rw [if_neg hRest] at hPayload
        simp at hPayload

/-! ## The induced prefix-free machine -/

/-- Run a plain conditional algorithm only after decoding one exact
self-delimiting program field. -/
noncomputable def selfDelimitingConditionalCompute
    (source : ConditionalAlgorithm) (program condition : BinString) :
    Option BinString :=
  match exactE2Payload program with
  | none => none
  | some payload => (source payload condition).toOption

/-- The prefix-free machine induced by exact self-delimiting framing of a
plain conditional algorithm. -/
noncomputable def selfDelimitingConditionalMachine
    (source : ConditionalAlgorithm) : ConditionalPrefixFreeMachine where
  compute := selfDelimitingConditionalCompute source
  prefix_free := by
    intro condition program extension hPrefix hNe hProgram
    unfold selfDelimitingConditionalCompute at hProgram ⊢
    cases hPayload : exactE2Payload program with
    | none => simp [hPayload] at hProgram
    | some payload =>
        have hExtension := exactE2Payload_strict_extension_eq_none
          hPayload hPrefix hNe
        simp [hExtension]

@[simp] theorem selfDelimitingConditionalMachine_compute_e2encode
    (source : ConditionalAlgorithm) (payload condition : BinString) :
    (selfDelimitingConditionalMachine source).compute
      (e2encode payload) condition = (source payload condition).toOption := by
  simp [selfDelimitingConditionalMachine, selfDelimitingConditionalCompute]

/-- A successful source computation remains successful after self-delimiting
program encoding. -/
theorem selfDelimitingConditionalMachine_isProgram
    (source : ConditionalAlgorithm) {payload condition output : BinString}
    (hOutput : output ∈ source payload condition) :
    IsProgram (selfDelimitingConditionalMachine source)
      (e2encode payload) condition output := by
  unfold IsProgram
  rw [selfDelimitingConditionalMachine_compute_e2encode]
  exact Part.toOption_eq_some_iff.mpr hOutput

/-- Any successful induced-machine program decodes to a source program for
the same output. -/
theorem source_program_of_selfDelimitingConditionalMachine
    (source : ConditionalAlgorithm) {program condition output : BinString}
    (hProgram : IsProgram (selfDelimitingConditionalMachine source)
      program condition output) :
    ∃ payload, e2decode program = some (payload, []) ∧
      output ∈ source payload condition := by
  change selfDelimitingConditionalCompute source program condition =
    some output at hProgram
  unfold selfDelimitingConditionalCompute at hProgram
  cases hExact : exactE2Payload program with
  | none => simp [hExact] at hProgram
  | some payload =>
      rw [hExact] at hProgram
      refine ⟨payload, ?_, Part.toOption_eq_some_iff.mp hProgram⟩
      unfold exactE2Payload at hExact
      cases hDecode : e2decode program with
      | none => simp [hDecode] at hExact
      | some fields =>
          obtain ⟨head, rest⟩ := fields
          simp only [hDecode, Option.bind_some] at hExact
          by_cases hRest : rest = []
          · rw [if_pos hRest] at hExact
            have hHead : head = payload := Option.some.inj hExact
            subst rest
            subst head
            rfl
          · rw [if_neg hRest] at hExact
            simp at hExact

/-- The explicit negative machine example: a nonempty suffix after a complete
program is rejected, independently of the source algorithm and condition. -/
theorem selfDelimitingConditionalMachine_rejects_extension
    (source : ConditionalAlgorithm) (payload suffix condition : BinString)
    (hSuffix : suffix ≠ []) :
    (selfDelimitingConditionalMachine source).compute
      (e2encode payload ++ suffix) condition = none := by
  simp [selfDelimitingConditionalMachine, selfDelimitingConditionalCompute,
    exactE2Payload_e2encode_append_eq_none payload suffix hSuffix]

/-! ## Effectivity -/

/-- Partial algorithm denoted by the self-delimiting machine. -/
noncomputable def selfDelimitingConditionalAlgorithm
    (source : ConditionalAlgorithm) (program condition : BinString) :
    Part BinString :=
  (Part.ofOption (exactE2Payload program)).bind fun payload =>
    source payload condition

theorem selfDelimitingConditionalAlgorithm_partrec
    (source : ConditionalAlgorithm) (hSource : Partrec₂ source) :
    Partrec₂ (selfDelimitingConditionalAlgorithm source) := by
  unfold Partrec₂
  have hPayload : Partrec fun input : BinString × BinString =>
      Part.ofOption (exactE2Payload input.1) :=
    Computable.ofOption
      (exactE2Payload_primrec.to_comp.comp Computable.fst)
  have hRun : Partrec₂ fun (input : BinString × BinString)
      (payload : BinString) => source payload input.2 := by
    unfold Partrec₂ at hSource ⊢
    exact hSource.comp
      (Computable.snd.pair (Computable.snd.comp Computable.fst))
  exact hPayload.bind hRun

theorem selfDelimitingConditionalMachine_part_eq_algorithm
    (source : ConditionalAlgorithm) (program condition : BinString) :
    Part.ofOption ((selfDelimitingConditionalMachine source).compute
      program condition) =
      selfDelimitingConditionalAlgorithm source program condition := by
  change Part.ofOption
      (selfDelimitingConditionalCompute source program condition) =
    selfDelimitingConditionalAlgorithm source program condition
  unfold selfDelimitingConditionalCompute selfDelimitingConditionalAlgorithm
  cases hPayload : exactE2Payload program with
  | none => simp [Part.ofOption]
  | some payload =>
      calc
        Part.ofOption
            (match some payload with
            | none => none
            | some payload => (source payload condition).toOption) =
            Part.ofOption ((source payload condition).toOption) := rfl
        _ = source payload condition :=
          Part.of_toOption (source payload condition)
        _ = (Part.ofOption (some payload)).bind fun payload =>
            source payload condition := by
          simp [Part.ofOption, Part.bind_some]

theorem selfDelimitingConditionalMachine_effective
    (source : ConditionalAlgorithm) (hSource : Partrec₂ source) :
    Partrec₂ fun program condition =>
      Part.ofOption ((selfDelimitingConditionalMachine source).compute
        program condition) := by
  exact (selfDelimitingConditionalAlgorithm_partrec source hSource).of_eq
    fun input =>
      (selfDelimitingConditionalMachine_part_eq_algorithm
        source input.1 input.2).symm

/-! ## Uniform complexity bounds -/

/-- Self-delimiting conditional complexity is at most plain conditional
complexity plus the binary length header. -/
theorem selfDelimitingConditionalComplexity_le_plain_plus_log
    (source : ConditionalAlgorithm) (condition output : BinString)
    (hRepresented : ∃ payload, output ∈ source payload condition) :
    Kc[selfDelimitingConditionalMachine source](output | condition) ≤
      Cc[source](output | condition) +
        2 * Nat.log 2 (Cc[source](output | condition) + 1) + 3 := by
  obtain ⟨payload, hOutput, hLength⟩ :=
    exists_program_of_plainConditionalComplexity source condition output hRepresented
  have hProgram := selfDelimitingConditionalMachine_isProgram source hOutput
  calc
    Kc[selfDelimitingConditionalMachine source](output | condition) ≤
        (e2encode payload).length :=
      conditionalComplexity_le_program_length _ _ _ _ hProgram
    _ ≤ payload.length + 2 * Nat.log 2 (payload.length + 1) + 3 :=
      e2encode_length_le_log payload
    _ = Cc[source](output | condition) +
        2 * Nat.log 2 (Cc[source](output | condition) + 1) + 3 := by
      rw [hLength]

/-- Exact framing also reflects programs, so the induced prefix-free
complexity cannot be smaller than source plain complexity. -/
theorem plainConditionalComplexity_le_selfDelimiting
    (source : ConditionalAlgorithm) (condition output : BinString)
    (hRepresented : ∃ payload, output ∈ source payload condition) :
    Cc[source](output | condition) ≤
      Kc[selfDelimitingConditionalMachine source](output | condition) := by
  obtain ⟨sourcePayload, hSourcePayload⟩ := hRepresented
  have hHasProgram : HasProgram (selfDelimitingConditionalMachine source)
      condition output :=
    ⟨e2encode sourcePayload,
      selfDelimitingConditionalMachine_isProgram source hSourcePayload⟩
  obtain ⟨program, hProgram, hLength⟩ :=
    exists_program_of_conditionalComplexity
      (selfDelimitingConditionalMachine source) condition output hHasProgram
  obtain ⟨payload, hDecode, hOutput⟩ :=
    source_program_of_selfDelimitingConditionalMachine source hProgram
  calc
    Cc[source](output | condition) ≤ payload.length :=
      plainConditionalComplexity_le_of_program source condition output payload hOutput
    _ ≤ program.length := e2decode_head_length_le hDecode
    _ = Kc[selfDelimitingConditionalMachine source](output | condition) := hLength

/-- The complete machine-relative plain/prefix comparison. -/
theorem plain_selfDelimiting_complexity_bounds
    (source : ConditionalAlgorithm) (condition output : BinString)
    (hRepresented : ∃ payload, output ∈ source payload condition) :
    Cc[source](output | condition) ≤
        Kc[selfDelimitingConditionalMachine source](output | condition) ∧
      Kc[selfDelimitingConditionalMachine source](output | condition) ≤
        Cc[source](output | condition) +
          2 * Nat.log 2 (Cc[source](output | condition) + 1) + 3 :=
  ⟨plainConditionalComplexity_le_selfDelimiting source condition output hRepresented,
    selfDelimitingConditionalComplexity_le_plain_plus_log
      source condition output hRepresented⟩

/-- The logarithmic constants are chosen once for every represented
condition/output pair, rather than separately for each pair. -/
theorem plain_selfDelimiting_uniform_logarithmic_bound
    (source : ConditionalAlgorithm) :
    UniformLogarithmicUpperBound
      (fun pair : {pair : BinString × BinString //
          ∃ payload, pair.2 ∈ source payload pair.1} =>
        Kc[selfDelimitingConditionalMachine source](pair.1.2 | pair.1.1))
      (fun pair => Cc[source](pair.1.2 | pair.1.1))
      (fun pair => Cc[source](pair.1.2 | pair.1.1)) := by
  refine ⟨2, 3, ?_⟩
  intro pair
  exact selfDelimitingConditionalComplexity_le_plain_plus_log
    source pair.1.1 pair.1.2 pair.2

/-- Positive control: the canonical universal plain conditional interpreter
represents every output, so the two-sided bound applies without an extra
range premise. -/
theorem canonicalPlain_selfDelimiting_complexity_bounds
    (condition output : BinString) :
    Cc[universalConditionalAlgorithm](output | condition) ≤
        Kc[(selfDelimitingConditionalMachine universalConditionalAlgorithm)](output | condition) ∧
      Kc[(selfDelimitingConditionalMachine universalConditionalAlgorithm)](output | condition) ≤
        Cc[universalConditionalAlgorithm](output | condition) +
          2 * Nat.log 2
            (Cc[universalConditionalAlgorithm](output | condition) + 1) + 3 :=
  plain_selfDelimiting_complexity_bounds universalConditionalAlgorithm
    condition output (canonicalPlainConditional_hasProgram condition output)

#print axioms exactE2Payload_primrec
#print axioms selfDelimitingConditionalMachine_effective
#print axioms plain_selfDelimiting_complexity_bounds
#print axioms plain_selfDelimiting_uniform_logarithmic_bound
#print axioms canonicalPlain_selfDelimiting_complexity_bounds

end KolmogorovComplexity
