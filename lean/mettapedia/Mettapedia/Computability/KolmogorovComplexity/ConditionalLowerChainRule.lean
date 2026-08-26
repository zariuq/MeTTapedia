import Mettapedia.Computability.KolmogorovComplexity.ConditionalChainRule
import Mettapedia.Computability.KolmogorovComplexity.ConditionalOutputSemimeasure
import Mettapedia.Computability.KolmogorovComplexity.SaturatedKraftChaitin

/-!
# Effective lower conditional chain rule

This file builds the concrete machinery required by the lower half of the
conditional prefix-complexity chain rule.  The construction is deliberately
staged:

1. decode the condition-side pairing effectively;
2. project paired outputs to their head component;
3. apply the effective output-mass coder to obtain a uniform concentration
   bound for programs producing a fixed head;
4. use that bound to finance the outer tail coder.

The first three stages are completed below.  They isolate the inner coding
machine and its exact additive constant before the outer Kraft--Chaitin
allocation is introduced.
-/

namespace KolmogorovComplexity

open scoped Classical
open Mettapedia.UniversalAI.TimeBoundedAIXI

namespace KraftChaitin

/-! ## Effective condition pairing -/

/-- The unary machine prefix is a run of `true` bits followed by `false`. -/
theorem machinePrefix_eq_replicate (n : Nat) :
    machinePrefix n = List.replicate n true ++ [false] := by
  induction n with
  | zero => rfl
  | succ n ih => simp [machinePrefix, ih, List.replicate_succ]

/-- The condition pairing is exactly an `e1`-encoded head followed by the
second component. -/
theorem pairCondition_eq_e1encode_append (left right : BinString) :
    pairCondition left right = e1encode left ++ right := by
  simp [pairCondition, e1encode, machinePrefix_eq_replicate,
    List.append_assoc]

/-- The recursive unary-prefix decoder agrees with the leading-run view used
by `e1decode`. -/
theorem decodeMachinePrefix_eq_countLeadingTrues (input : BinString) :
    decodeMachinePrefix input =
      match countLeadingTrues input with
      | (n, false :: rest) => some (n, rest)
      | _ => none := by
  induction input with
  | nil => rfl
  | cons bit rest ih =>
      cases bit with
      | false => rfl
      | true =>
          rw [countLeadingTrues_true]
          generalize hrest : countLeadingTrues rest = fields
          obtain ⟨n, tail⟩ := fields
          rw [hrest] at ih
          simp only [decodeMachinePrefix]
          cases tail with
          | nil => rw [ih]; rfl
          | cons marker suffix =>
              cases marker <;> rw [ih] <;> rfl

/-- The two condition decoders are extensionally identical. -/
theorem unpairCondition_eq_e1decode (input : BinString) :
    unpairCondition input = e1decode input := by
  unfold unpairCondition e1decode
  rw [decodeMachinePrefix_eq_countLeadingTrues]
  generalize hrun : countLeadingTrues input = fields
  obtain ⟨n, tail⟩ := fields
  cases tail with
  | nil => rfl
  | cons marker body => cases marker <;> rfl

/-- Condition-side unpairing is primitive recursive. -/
theorem unpairCondition_primrec : Primrec unpairCondition :=
  e1decode_primrec.of_eq fun input => (unpairCondition_eq_e1decode input).symm

/-! ## Effective chain-condition decoding -/

/-- Decoded fields of `chainCondition`: head, supplied complexity index, and
the original auxiliary condition. -/
abbrev ChainConditionFields := (BinString × Nat) × BinString

/-- Decode the nested condition-side pairing used by the conditional chain
rule. -/
def decodeChainCondition (condition : BinString) :
    Option ChainConditionFields :=
  (unpairCondition condition).bind fun outer =>
    (unpairCondition outer.2).map fun inner =>
      ((outer.1, ofBinaryBits inner.1), inner.2)

@[simp] theorem decodeChainCondition_chainCondition
    (condition head : BinString) (complexityIndex : Nat) :
    decodeChainCondition (chainCondition condition head complexityIndex) =
      some ((head, complexityIndex), condition) := by
  simp [decodeChainCondition, chainCondition, unpairCondition_pairCondition,
    ofBinaryBits_binaryBits]

/-- The complete chain-condition parser is primitive recursive. -/
theorem decodeChainCondition_primrec : Primrec decodeChainCondition := by
  have hOuter : Primrec fun condition : BinString =>
      unpairCondition condition := unpairCondition_primrec
  have hInnerBranch : Primrec₂ fun (_condition : BinString)
      (outer : BinString × BinString) =>
      (unpairCondition outer.2).map fun inner =>
        ((outer.1, ofBinaryBits inner.1), inner.2) := by
    apply Primrec₂.mk
    have hInnerDecode : Primrec fun input :
        (BinString × (BinString × BinString)) =>
        unpairCondition input.2.2 :=
      unpairCondition_primrec.comp (Primrec.snd.comp Primrec.snd)
    have hBuild : Primrec₂ fun
        (input : BinString × (BinString × BinString))
        (inner : BinString × BinString) =>
        ((input.2.1, ofBinaryBits inner.1), inner.2) := by
      exact Primrec₂.pair.comp₂
        (Primrec₂.pair.comp₂
          (Primrec.fst.comp₂ (Primrec.snd.comp₂ Primrec₂.left))
          (ofBinaryBits_primrec.comp₂
            (Primrec.fst.comp₂ Primrec₂.right)))
        (Primrec.snd.comp₂ Primrec₂.right)
    exact Primrec.option_map hInnerDecode hBuild
  exact (Primrec.option_bind hOuter hInnerBranch).of_eq fun condition => by
    unfold decodeChainCondition
    cases houter : unpairCondition condition with
    | none => rfl
    | some outer => rfl

/-! ## Tail extraction and output composition -/

/-- Retain the tail of a paired output exactly when its head agrees with the
expected head. -/
def selectChainTail (expectedHead output : BinString) : Option BinString :=
  (unpairCondition output).bind fun fields =>
    if fields.1 = expectedHead then some fields.2 else none

@[simp] theorem selectChainTail_pairCondition
    (head tail : BinString) :
    selectChainTail head (pairCondition head tail) = some tail := by
  simp [selectChainTail, unpairCondition_pairCondition]

/-- Tail selection is primitive recursive. -/
theorem selectChainTail_primrec : Primrec₂ selectChainTail := by
  apply Primrec₂.mk
  have hDecode : Primrec fun input : BinString × BinString =>
      unpairCondition input.2 :=
    unpairCondition_primrec.comp Primrec.snd
  have hBranch : Primrec₂ fun (input : BinString × BinString)
      (fields : BinString × BinString) =>
      if fields.1 = input.1 then some fields.2 else none := by
    apply Primrec₂.mk
    apply Primrec.ite
    · exact Primrec.eq.comp
        (Primrec.fst.comp Primrec.snd)
        (Primrec.fst.comp Primrec.fst)
    · exact Primrec.option_some.comp (Primrec.snd.comp Primrec.snd)
    · exact Primrec.const none
  exact (Primrec.option_bind hDecode hBranch).of_eq fun input => by
    unfold selectChainTail
    cases hdecode : unpairCondition input.2 <;> rfl

/-- Execute a source program under the base condition carried by a chain
condition and retain the tail only when the resulting pair has the advertised
head.  The numerical index is data for the coding theorem, not an instruction
to compute a complexity. -/
def chainTailMachine (U : ConditionalPrefixFreeMachine) :
    ConditionalPrefixFreeMachine where
  compute := fun program condition =>
    match decodeChainCondition condition with
    | none => none
    | some fields =>
        (U.compute program fields.2).bind
          (selectChainTail fields.1.1)
  prefix_free := by
    intro condition program extension hprefix hne hhalts
    cases hfields : decodeChainCondition condition with
    | none => simp [hfields] at hhalts
    | some fields =>
        have hSourceHalts : U.compute program fields.2 ≠ none := by
          cases hcompute : U.compute program fields.2 with
          | none => simp [hfields, hcompute] at hhalts
          | some _ => simp
        have hSourceNone := U.prefix_free fields.2 program extension
          hprefix hne hSourceHalts
        simp [hSourceNone]

theorem chainTailMachine_program
    {U : ConditionalPrefixFreeMachine}
    {program condition head tail : BinString} {complexityIndex : Nat}
    (h : IsProgram U program condition (pairCondition head tail)) :
    IsProgram (chainTailMachine U) program
      (chainCondition condition head complexityIndex) tail := by
  unfold IsProgram at h ⊢
  simp [chainTailMachine, h, selectChainTail_pairCondition]

abbrev ChainTailInput := BinString × BinString
abbrev ChainTailContext := ChainTailInput × ChainConditionFields

/-- Pack the source program with the decoded base condition. -/
def chainTailSourceArguments
    (input : ChainTailContext) : BinString × BinString :=
  (input.1.1, input.2.2)

theorem chainTailSourceArguments_primrec :
    Primrec chainTailSourceArguments := by
  unfold chainTailSourceArguments
  exact (Primrec.fst.comp Primrec.fst).pair
    (Primrec.snd.comp Primrec.snd)

/-- Pack the expected head with one source-machine output. -/
def chainTailSelectArguments
    (input : ChainTailContext × BinString) : BinString × BinString :=
  (input.1.2.1.1, input.2)

theorem chainTailSelectArguments_primrec :
    Primrec chainTailSelectArguments := by
  unfold chainTailSelectArguments
  exact (Primrec.fst.comp (Primrec.fst.comp
    (Primrec.snd.comp Primrec.fst))).pair Primrec.snd

/-- Partial algorithm underlying `chainTailMachine`. -/
noncomputable def chainTailAlgorithm
    (U : ConditionalPrefixFreeMachine) (input : ChainTailInput) :
    Part BinString :=
  (Part.ofOption (decodeChainCondition input.2)).bind fun fields =>
    (Part.ofOption (U.compute input.1 fields.2)).bind fun output =>
      Part.ofOption (selectChainTail fields.1.1 output)

/-- The named tail algorithm is partial recursive whenever the source machine
is. -/
theorem chainTailAlgorithm_partrec
    (U : ConditionalPrefixFreeMachine)
    (hEffective : Partrec₂ fun program condition =>
      Part.ofOption (U.compute program condition)) :
    Partrec (chainTailAlgorithm U) := by
  unfold Partrec₂ at hEffective
  have hDecode : Computable fun input : ChainTailInput =>
      decodeChainCondition input.2 :=
    decodeChainCondition_primrec.to_comp.comp Computable.snd
  have hParsed : Partrec fun input : ChainTailInput =>
      Part.ofOption (decodeChainCondition input.2) :=
    Computable.ofOption hDecode
  have hSource : Partrec₂ fun (input : ChainTailInput)
      (fields : ChainConditionFields) =>
      Part.ofOption (U.compute input.1 fields.2) := by
    exact hEffective.comp chainTailSourceArguments_primrec.to_comp
  have hSelect : Partrec₂ fun
      (context : ChainTailContext) (output : BinString) =>
      Part.ofOption (selectChainTail context.2.1.1 output) := by
    have hPrimitive : Primrec fun pair : ChainTailContext × BinString =>
        selectChainTail (chainTailSelectArguments pair).1
          (chainTailSelectArguments pair).2 :=
      selectChainTail_primrec.comp
        (Primrec.fst.comp chainTailSelectArguments_primrec)
        (Primrec.snd.comp chainTailSelectArguments_primrec)
    exact (Computable.ofOption hPrimitive.to_comp).to₂
  have hRun : Partrec₂ fun (input : ChainTailInput)
      (fields : ChainConditionFields) =>
      (Part.ofOption (U.compute input.1 fields.2)).bind fun output =>
        Part.ofOption (selectChainTail fields.1.1 output) := by
    exact hSource.bind hSelect
  exact hParsed.bind hRun

/-- The option-valued machine and the named partial algorithm agree. -/
theorem chainTailMachine_part_eq_algorithm
    (U : ConditionalPrefixFreeMachine) (program condition : BinString) :
    Part.ofOption ((chainTailMachine U).compute program condition) =
      chainTailAlgorithm U (program, condition) := by
  unfold chainTailAlgorithm
  cases hfields : decodeChainCondition condition with
  | none => simp [chainTailMachine, hfields, Part.ofOption]
  | some fields =>
      cases hcompute : U.compute program fields.2 with
      | none => simp [chainTailMachine, hfields, hcompute, Part.ofOption]
      | some output =>
          simp [chainTailMachine, hfields, hcompute, Part.ofOption,
            Part.bind_some]

/-- Tail extraction preserves effectivity. -/
theorem chainTailMachine_effective
    (U : ConditionalPrefixFreeMachine)
    (hEffective : Partrec₂ fun program condition =>
      Part.ofOption (U.compute program condition)) :
    Partrec₂ fun program condition =>
      Part.ofOption ((chainTailMachine U).compute program condition) := by
  unfold Partrec₂
  exact (chainTailAlgorithm_partrec U hEffective).of_eq fun input =>
    (chainTailMachine_part_eq_algorithm U input.1 input.2).symm

/-- Compose a prefix-free producer with a condition-preserving output
transformer.  Prefix-freeness is inherited from the producer. -/
def outputCompositionMachine (producer transformer : ConditionalPrefixFreeMachine) :
    ConditionalPrefixFreeMachine where
  compute := fun program condition =>
    (producer.compute program condition).bind fun intermediate =>
      transformer.compute intermediate condition
  prefix_free := by
    intro condition program extension hprefix hne hhalts
    have hProducerHalts : producer.compute program condition ≠ none := by
      cases hcompute : producer.compute program condition with
      | none => simp [hcompute] at hhalts
      | some _ => simp
    have hProducerNone := producer.prefix_free condition program extension
      hprefix hne hProducerHalts
    simp [hProducerNone]

theorem outputCompositionMachine_program
    {producer transformer : ConditionalPrefixFreeMachine}
    {program condition intermediate output : BinString}
    (hProducer : IsProgram producer program condition intermediate)
    (hTransformer : IsProgram transformer intermediate condition output) :
    IsProgram (outputCompositionMachine producer transformer)
      program condition output := by
  unfold IsProgram at hProducer hTransformer ⊢
  simp [outputCompositionMachine, hProducer, hTransformer]

/-- Effective producer and transformer machines have an effective output
composition. -/
theorem outputCompositionMachine_effective
    (producer transformer : ConditionalPrefixFreeMachine)
    (hProducer : Partrec₂ fun program condition =>
      Part.ofOption (producer.compute program condition))
    (hTransformer : Partrec₂ fun program condition =>
      Part.ofOption (transformer.compute program condition)) :
    Partrec₂ fun program condition =>
      Part.ofOption
        ((outputCompositionMachine producer transformer).compute
          program condition) := by
  unfold Partrec₂ at hProducer hTransformer ⊢
  let Input := BinString × BinString
  have hRun : Partrec₂ fun (input : Input) (intermediate : BinString) =>
      Part.ofOption (transformer.compute intermediate input.2) := by
    exact hTransformer.comp
      (Computable.snd.pair (Computable.snd.comp Computable.fst))
  exact (hProducer.bind hRun).of_eq fun input => by
    cases hcompute : producer.compute input.1 input.2 with
    | none => simp [outputCompositionMachine, hcompute, Part.ofOption]
    | some intermediate =>
        simp [outputCompositionMachine, hcompute, Part.ofOption,
          Part.bind_some]

/-! ## Head projection machine -/

/-- Project the first component of a paired output produced by `U`.  Outputs
that are not in the condition-pair encoding are ignored. -/
def firstOutputMachine (U : ConditionalPrefixFreeMachine) :
    ConditionalPrefixFreeMachine where
  compute := fun program condition =>
    match U.compute program condition with
    | none => none
    | some output => (unpairCondition output).map Prod.fst
  prefix_free := by
    intro condition program extension hprefix hne hhalts
    have hSourceHalts : U.compute program condition ≠ none := by
      cases hcompute : U.compute program condition with
      | none => simp [hcompute] at hhalts
      | some _ => simp
    have hSourceNone := U.prefix_free condition program extension
      hprefix hne hSourceHalts
    simp [hSourceNone]

theorem firstOutputMachine_program
    {U : ConditionalPrefixFreeMachine}
    {program condition first second : BinString}
    (h : IsProgram U program condition (pairCondition first second)) :
    IsProgram (firstOutputMachine U) program condition first := by
  unfold IsProgram at h ⊢
  simp [firstOutputMachine, h, unpairCondition_pairCondition]

/-- The head projection preserves effectivity. -/
theorem firstOutputMachine_effective
    (U : ConditionalPrefixFreeMachine)
    (hEffective : Partrec₂ fun program condition =>
      Part.ofOption (U.compute program condition)) :
    Partrec₂ fun program condition =>
      Part.ofOption ((firstOutputMachine U).compute program condition) := by
  unfold Partrec₂ at hEffective ⊢
  have hProjection : Primrec fun output : BinString =>
      (unpairCondition output).map Prod.fst := by
    exact Primrec.option_map unpairCondition_primrec
      (Primrec.fst.comp₂ Primrec₂.right)
  have hProjected : Partrec₂ fun (_input : BinString × BinString)
      (output : BinString) =>
      Part.ofOption ((unpairCondition output).map Prod.fst) := by
    exact (Computable.ofOption
      (hProjection.to_comp.comp Computable.snd)).to₂
  exact (hEffective.bind hProjected).of_eq fun input => by
    cases hcompute : U.compute input.1 input.2 with
    | none => simp [firstOutputMachine, hcompute, Part.ofOption]
    | some output =>
      simp [firstOutputMachine, hcompute, Part.ofOption, Part.bind_some]

/-- A fixed simulation of direct head projection by the concrete host.  Its
compiler cost controls the subtraction used by the outer chain requests. -/
noncomputable def trimmedHeadProjectionSimulation :
    UniformlySimulates trimmedIndexedHost
      (firstOutputMachine trimmedIndexedHost) :=
  Classical.choice (trimmedIndexedHost_simulates_effective _
    (firstOutputMachine_effective trimmedIndexedHost
      trimmedIndexedHost_effective))

theorem trimmedHeadComplexity_le_sourceProgram
    {program condition head : BinString}
    (hProgram : IsProgram (firstOutputMachine trimmedIndexedHost)
      program condition head) :
    Kc[trimmedIndexedHost](head | condition) ≤
      program.length +
        trimmedHeadProjectionSimulation.compilerPrefix.length := by
  have hCompiled := trimmedHeadProjectionSimulation.program hProgram
  have hBound := conditionalComplexity_le_program_length trimmedIndexedHost
    condition head
    (trimmedHeadProjectionSimulation.compilerPrefix ++ program) hCompiled
  simpa [List.length_append, Nat.add_comm] using hBound

/-! ## Concrete inner concentration machine -/

/-- A fixed evaluator code for the effective head-projection machine over the
trimmed indexed host. -/
noncomputable def trimmedHeadOutputCode : Nat.Partrec.Code :=
  Classical.choose (exists_code_of_conditionalMachine_effective
    (firstOutputMachine trimmedIndexedHost)
    (firstOutputMachine_effective trimmedIndexedHost
      trimmedIndexedHost_effective))

theorem trimmedHeadOutputCode_spec :
    Nat.Partrec.Code.eval trimmedHeadOutputCode =
      encodedConditionalCompute (firstOutputMachine trimmedIndexedHost) :=
  Classical.choose_spec (exists_code_of_conditionalMachine_effective
    (firstOutputMachine trimmedIndexedHost)
    (firstOutputMachine_effective trimmedIndexedHost
      trimmedIndexedHost_effective))

/-- The concrete host uniformly simulates its effective inner output coder. -/
noncomputable def trimmedHeadOutputSimulation :
    UniformlySimulates trimmedIndexedHost
      (conditionalOutputCodingMachine
        (firstOutputMachine trimmedIndexedHost)
        trimmedHeadOutputCode trimmedHeadOutputCode_spec) :=
  Classical.choice (trimmedIndexedHost_simulates_effective _
    (conditionalOutputCodingMachine_effective
      (firstOutputMachine trimmedIndexedHost)
      trimmedHeadOutputCode trimmedHeadOutputCode_spec))

/-- Explicit inner concentration bound for programs of the concrete trimmed
host whose outputs share a fixed paired head. -/
theorem trimmedHeadOutputNumerator_concentration
    (condition head : BinString) (stage : Nat) :
    conditionalOutputNumerator trimmedHeadOutputCode condition stage
        (Encodable.encode head) ≤
      2 ^ (stage + (trimmedHeadOutputSimulation.compilerPrefix.length + 3) -
        Kc[trimmedIndexedHost](head | condition)) := by
  exact conditionalOutputNumerator_concentration
    (firstOutputMachine trimmedIndexedHost) trimmedIndexedHost
    trimmedHeadOutputCode trimmedHeadOutputCode_spec
    trimmedHeadOutputSimulation condition head stage

/-! ## Unique outer source-program events -/

/-- One outer enumeration slot carries an evaluator stage and a canonical
program code. -/
def lowerChainCandidate (index : Nat) : Nat × Nat := index.unpair

theorem lowerChainCandidate_primrec : Primrec lowerChainCandidate := by
  exact Primrec.unpair

theorem lowerChainCandidate_injective : Function.Injective lowerChainCandidate := by
  intro left right h
  have hPair := congrArg (fun candidate => Nat.pair candidate.1 candidate.2) h
  simpa [lowerChainCandidate, Nat.pair_unpair] using hPair

abbrev LowerChainEventInput := BinString × Nat
abbrev LowerChainFieldContext := LowerChainEventInput × ChainConditionFields
abbrev LowerChainProgramContext := LowerChainFieldContext × BinString

/-- Pack the base condition, candidate stage, and decoded source program for
the first-observation test. -/
def lowerChainObservationArguments
    (context : LowerChainProgramContext) : BoundedConditionalOutputInput :=
  ((context.1.2.2, (lowerChainCandidate context.1.1.2).1), context.2)

theorem lowerChainObservationArguments_primrec :
    Primrec lowerChainObservationArguments := by
  unfold lowerChainObservationArguments
  have hStage : Primrec fun context : LowerChainProgramContext =>
      (lowerChainCandidate context.1.1.2).1 :=
    Primrec.fst.comp (lowerChainCandidate_primrec.comp
      (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
  have hBase : Primrec fun context : LowerChainProgramContext =>
      context.1.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  exact (hBase.pair hStage).pair Primrec.snd

/-- Emit a source program exactly when the indexed slot is its first eligible
bounded observation and the observed head matches the chain condition. -/
noncomputable def lowerChainProgramEvent (condition : BinString) (index : Nat) :
    Option BinString :=
  let candidate := lowerChainCandidate index
  (decodeChainCondition condition).bind fun fields =>
    (canonicalDecode candidate.2).bind fun program =>
      if firstEligibleBoundedConditionalOutputAt trimmedHeadOutputCode
          fields.2 candidate.1 program = some fields.1.1 then
        some program
      else none

theorem lowerChainProgramEvent_primrec :
    Primrec₂ lowerChainProgramEvent := by
  apply Primrec₂.mk
  have hFields : Primrec fun input : LowerChainEventInput =>
      decodeChainCondition input.1 :=
    decodeChainCondition_primrec.comp Primrec.fst
  have hFieldBranch : Primrec₂ fun (input : LowerChainEventInput)
      (fields : ChainConditionFields) =>
      (canonicalDecode (lowerChainCandidate input.2).2).bind fun program =>
        if firstEligibleBoundedConditionalOutputAt trimmedHeadOutputCode
            fields.2 (lowerChainCandidate input.2).1 program = some fields.1.1 then
          some program
        else none := by
    apply Primrec₂.mk
    have hProgram : Primrec fun context : LowerChainFieldContext =>
        canonicalDecode (lowerChainCandidate context.1.2).2 :=
      canonicalDecode_primrec.comp
        (Primrec.snd.comp (lowerChainCandidate_primrec.comp
          (Primrec.snd.comp Primrec.fst)))
    have hProgramBranch : Primrec₂ fun (context : LowerChainFieldContext)
        (program : BinString) =>
        if firstEligibleBoundedConditionalOutputAt trimmedHeadOutputCode
            context.2.2 (lowerChainCandidate context.1.2).1 program =
              some context.2.1.1 then
          some program
        else none := by
      apply Primrec.ite
      · exact Primrec.eq.comp
          ((firstEligibleBoundedConditionalOutputAt_primrec
            trimmedHeadOutputCode).comp lowerChainObservationArguments_primrec)
          (Primrec.option_some.comp
            (Primrec.fst.comp
              (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))))
      · exact Primrec.option_some.comp Primrec.snd
      · exact Primrec.const none
    exact Primrec.option_bind hProgram hProgramBranch
  exact (Primrec.option_bind hFields hFieldBranch).of_eq fun input => by
    unfold lowerChainProgramEvent
    cases hFieldsAt : decodeChainCondition input.1 with
    | none => rfl
    | some fields =>
        cases hProgramAt : canonicalDecode (lowerChainCandidate input.2).2 <;>
          simp [hProgramAt]

theorem lowerChainProgramEvent_some
    {condition program : BinString} {index : Nat}
    (h : lowerChainProgramEvent condition index = some program) :
    ∃ fields : ChainConditionFields,
      decodeChainCondition condition = some fields ∧
      canonicalDecode (lowerChainCandidate index).2 = some program ∧
      firstEligibleBoundedConditionalOutputAt trimmedHeadOutputCode
        fields.2 (lowerChainCandidate index).1 program = some fields.1.1 := by
  unfold lowerChainProgramEvent at h
  cases hFields : decodeChainCondition condition with
  | none => simp [hFields] at h
  | some fields =>
      cases hProgram : canonicalDecode (lowerChainCandidate index).2 with
      | none => simp [hFields, hProgram] at h
      | some decoded =>
          rw [hFields, Option.bind_some, hProgram, Option.bind_some] at h
          by_cases hFirst : firstEligibleBoundedConditionalOutputAt
              trimmedHeadOutputCode fields.2 (lowerChainCandidate index).1
                decoded = some fields.1.1
          · rw [if_pos hFirst] at h
            have hDecoded : decoded = program := Option.some.inj h
            subst decoded
            exact ⟨fields, rfl, rfl, hFirst⟩
          · rw [if_neg hFirst] at h
            contradiction

/-- A source program cannot be emitted by two distinct outer slots. -/
theorem lowerChainProgramEvent_index_injective
    {condition program : BinString} {left right : Nat}
    (hLeft : lowerChainProgramEvent condition left = some program)
    (hRight : lowerChainProgramEvent condition right = some program) :
    left = right := by
  unfold lowerChainProgramEvent at hLeft hRight
  cases hFields : decodeChainCondition condition with
  | none => simp [hFields] at hLeft
  | some fields =>
      cases hLeftProgram : canonicalDecode (lowerChainCandidate left).2 with
      | none => simp [hFields, hLeftProgram] at hLeft
      | some leftProgram =>
          cases hRightProgram : canonicalDecode (lowerChainCandidate right).2 with
          | none => simp [hFields, hRightProgram] at hRight
          | some rightProgram =>
              rw [hFields, Option.bind_some, hLeftProgram,
                Option.bind_some] at hLeft
              rw [hFields, Option.bind_some, hRightProgram,
                Option.bind_some] at hRight
              split at hLeft <;> try contradiction
              rename_i hLeftFirst
              split at hRight <;> try contradiction
              rename_i hRightFirst
              have hLeftProgramEq : leftProgram = program := Option.some.inj hLeft
              have hRightProgramEq : rightProgram = program := Option.some.inj hRight
              subst leftProgram
              subst rightProgram
              have hLeftCode : Encodable.encode program =
                  (lowerChainCandidate left).2 := by
                unfold canonicalDecode at hLeftProgram
                cases hDecode : Encodable.decode
                    (α := BinString) (lowerChainCandidate left).2 with
                | none => simp [hDecode] at hLeftProgram
                | some decoded =>
                    by_cases hCanonical : Encodable.encode decoded =
                        (lowerChainCandidate left).2
                    · simp [hDecode, hCanonical] at hLeftProgram
                      subst decoded
                      exact hCanonical
                    · simp [hDecode, hCanonical] at hLeftProgram
              have hRightCode : Encodable.encode program =
                  (lowerChainCandidate right).2 := by
                unfold canonicalDecode at hRightProgram
                cases hDecode : Encodable.decode
                    (α := BinString) (lowerChainCandidate right).2 with
                | none => simp [hDecode] at hRightProgram
                | some decoded =>
                    by_cases hCanonical : Encodable.encode decoded =
                        (lowerChainCandidate right).2
                    · simp [hDecode, hCanonical] at hRightProgram
                      subst decoded
                      exact hCanonical
                    · simp [hDecode, hCanonical] at hRightProgram
              have hStage : (lowerChainCandidate left).1 =
                  (lowerChainCandidate right).1 :=
                firstEligibleBoundedConditionalOutputAt_stage_unique
                  hLeftFirst hRightFirst
              apply lowerChainCandidate_injective
              exact Prod.ext hStage (hLeftCode.symm.trans hRightCode)

/-- Genuine source programs among the first `count` enumeration slots. -/
noncomputable def lowerChainProgramsUpTo
    (condition : BinString) (count : Nat) : List BinString :=
  (List.range count).filterMap (lowerChainProgramEvent condition)

theorem lowerChainProgramsUpTo_nodup
    (condition : BinString) (count : Nat) :
    (lowerChainProgramsUpTo condition count).Nodup := by
  unfold lowerChainProgramsUpTo
  apply List.Nodup.filterMap
  · intro left right program hLeft hRight
    exact lowerChainProgramEvent_index_injective hLeft hRight
  · exact List.nodup_range

theorem mem_lowerChainProgramsUpTo
    {condition program : BinString} {count : Nat} :
    program ∈ lowerChainProgramsUpTo condition count ↔
      ∃ index < count, lowerChainProgramEvent condition index = some program := by
  simp [lowerChainProgramsUpTo]

/-- Summing a weight over the emitted program list is the same as summing the
corresponding optional event weight over the enumeration indices. -/
theorem sum_lowerChainProgramsUpTo_eq_sum_range
    (condition : BinString) (count : Nat) (weight : BinString → Nat) :
    ((lowerChainProgramsUpTo condition count).map weight).sum =
      ∑ index ∈ Finset.range count,
        match lowerChainProgramEvent condition index with
        | none => 0
        | some program => weight program := by
  unfold lowerChainProgramsUpTo
  induction count with
  | zero => simp
  | succ count ih =>
      simp only [List.range_succ, List.filterMap_append, List.map_append,
        List.sum_append, Finset.sum_range_succ, ih]
      cases hEvent : lowerChainProgramEvent condition count <;>
        simp [hEvent, add_comm]

theorem lowerChainProgramsUpTo_subperm_bitstrings
    (condition : BinString) (count : Nat) :
    List.Subperm (lowerChainProgramsUpTo condition count)
      (bitstringsUpTo count) := by
  apply (lowerChainProgramsUpTo_nodup condition count).subperm
  intro program hProgram
  obtain ⟨index, hIndex, hEvent⟩ :=
    mem_lowerChainProgramsUpTo.mp hProgram
  obtain ⟨fields, _hFields, _hCanonical, hFirst⟩ :=
    lowerChainProgramEvent_some hEvent
  have hEligible :=
    eligible_of_firstEligibleBoundedConditionalOutputAt hFirst
  have hLength : program.length ≤ (lowerChainCandidate index).1 := by
    unfold eligibleBoundedConditionalOutputAt at hEligible
    by_cases hFits : program.length ≤ (lowerChainCandidate index).1
    · exact hFits
    · rw [if_neg hFits] at hEligible
      contradiction
  have hStageIndex : (lowerChainCandidate index).1 ≤ index := by
    exact Nat.unpair_left_le index
  exact mem_bitstringsUpTo_of_length_le (by omega)

/-- Every genuine source program emitted before `count` has length at most
`count`. -/
theorem length_le_count_of_mem_lowerChainProgramsUpTo
    {condition program : BinString} {count : Nat}
    (hProgram : program ∈ lowerChainProgramsUpTo condition count) :
    program.length ≤ count := by
  have hMember : program ∈ bitstringsUpTo count :=
    (lowerChainProgramsUpTo_subperm_bitstrings condition count).subset hProgram
  exact length_le_of_mem_bitstringsUpTo hMember

/-- Every genuine event on a canonical chain condition is still visible at
any later stage bounding its enumeration index. -/
theorem boundedHead_of_lowerChainProgramEvent
    {base head program : BinString} {complexityIndex index count : Nat}
    (hIndex : index < count)
    (hEvent : lowerChainProgramEvent
      (chainCondition base head complexityIndex) index = some program) :
    program.length ≤ count ∧
      boundedConditionalOutputAt trimmedHeadOutputCode base count program =
        some head := by
  obtain ⟨fields, hFields, _hCanonical, hFirst⟩ :=
    lowerChainProgramEvent_some hEvent
  rw [decodeChainCondition_chainCondition] at hFields
  have hFieldsEq : fields = ((head, complexityIndex), base) :=
    Option.some.inj hFields.symm
  subst fields
  have hEligible :=
    eligible_of_firstEligibleBoundedConditionalOutputAt hFirst
  have hStageIndex : (lowerChainCandidate index).1 ≤ index :=
    Nat.unpair_left_le index
  have hStageCount : (lowerChainCandidate index).1 ≤ count := by omega
  unfold eligibleBoundedConditionalOutputAt at hEligible
  by_cases hLength : program.length ≤ (lowerChainCandidate index).1
  · rw [if_pos hLength] at hEligible
    have hLater :
        boundedConditionalOutputAt trimmedHeadOutputCode base count program =
          some head :=
      Nat.le_induction (m := (lowerChainCandidate index).1)
        (P := fun stage _ =>
          boundedConditionalOutputAt trimmedHeadOutputCode base stage program =
            some head)
        hEligible
        (fun _stage _hLe hAt => boundedConditionalOutputAt_succ hAt)
        count hStageCount
    exact ⟨hLength.trans hStageCount, hLater⟩
  · rw [if_neg hLength] at hEligible
    contradiction

/-- On a genuine event, the finite contribution is its exact dyadic source
weight. -/
theorem conditionalOutputContribution_of_lowerChainProgramEvent
    {base head program : BinString} {complexityIndex index count : Nat}
    (hIndex : index < count)
    (hEvent : lowerChainProgramEvent
      (chainCondition base head complexityIndex) index = some program) :
    conditionalOutputContribution trimmedHeadOutputCode base count
        (Encodable.encode head) program = 2 ^ (count - program.length) := by
  obtain ⟨_hLength, hBounded⟩ :=
    boundedHead_of_lowerChainProgramEvent hIndex hEvent
  unfold conditionalOutputContribution
  simp [hBounded]

/-- Removing natural-number summands along a sub-permutation cannot increase
their total. -/
theorem natSum_map_le_of_subperm {α : Type*} {left right : List α}
    (h : List.Subperm left right) (weight : α → Nat) :
    (left.map weight).sum ≤ (right.map weight).sum := by
  rcases List.subperm_iff.mp h with ⟨middle, hPerm, hSublist⟩
  have hSublistWeight := hSublist.map weight
  have hLe := hSublistWeight.sum_le_sum
    (fun _value _hValue => Nat.zero_le _)
  have hEq : (middle.map weight).sum = (right.map weight).sum :=
    (hPerm.map weight).sum_eq
  exact hLe.trans_eq hEq

/-- The source mass of genuine events in a finite prefix is bounded by the
complete inner output numerator at that stage. -/
theorem lowerChainEventMass_le_innerNumerator
    (base head : BinString) (complexityIndex count : Nat) :
    ((lowerChainProgramsUpTo (chainCondition base head complexityIndex) count).map
      fun program => 2 ^ (count - program.length)).sum ≤
      conditionalOutputNumerator trimmedHeadOutputCode base count
        (Encodable.encode head) := by
  let condition := chainCondition base head complexityIndex
  let contribution := conditionalOutputContribution trimmedHeadOutputCode base
    count (Encodable.encode head)
  have hSubperm := lowerChainProgramsUpTo_subperm_bitstrings condition count
  have hLe := natSum_map_le_of_subperm hSubperm contribution
  have hLeft :
      ((lowerChainProgramsUpTo condition count).map contribution).sum =
        ((lowerChainProgramsUpTo condition count).map
          fun program => 2 ^ (count - program.length)).sum := by
    apply congrArg List.sum
    apply List.map_congr_left
    intro program hProgram
    obtain ⟨index, hIndex, hEvent⟩ :=
      mem_lowerChainProgramsUpTo.mp hProgram
    exact conditionalOutputContribution_of_lowerChainProgramEvent
      hIndex hEvent
  rw [hLeft] at hLe
  simpa [conditionalOutputNumerator, contribution, condition] using hLe

/-! ## Total outer request stream -/

/-- Fixed outer cost.  It dominates both the inner concentration compiler
and direct head projection, so every genuine request has an honest natural-
number subtraction while retaining the concentration bound. -/
noncomputable def lowerChainInnerCost : Nat :=
  max (trimmedHeadOutputSimulation.compilerPrefix.length + 3)
    trimmedHeadProjectionSimulation.compilerPrefix.length

theorem lowerChainConcentrationCost_le_innerCost :
    trimmedHeadOutputSimulation.compilerPrefix.length + 3 ≤
      lowerChainInnerCost := by
  exact Nat.le_max_left _ _

theorem lowerChainProjectionCost_le_innerCost :
    trimmedHeadProjectionSimulation.compilerPrefix.length ≤
      lowerChainInnerCost := by
  exact Nat.le_max_right _ _

/-- At the true head-complexity index, the finite source-program event mass is
bounded by the concentration power using the common outer cost. -/
theorem lowerChainEventMass_le_concentrationPow
    (base head : BinString) (count : Nat) :
    ((lowerChainProgramsUpTo
        (chainCondition base head Kc[trimmedIndexedHost](head | base)) count).map
      fun program => 2 ^ (count - program.length)).sum ≤
      2 ^ (count + lowerChainInnerCost -
        Kc[trimmedIndexedHost](head | base)) := by
  calc
    ((lowerChainProgramsUpTo
        (chainCondition base head Kc[trimmedIndexedHost](head | base)) count).map
      fun program => 2 ^ (count - program.length)).sum ≤
        conditionalOutputNumerator trimmedHeadOutputCode base count
          (Encodable.encode head) :=
      lowerChainEventMass_le_innerNumerator base head _ count
    _ ≤ 2 ^ (count +
          (trimmedHeadOutputSimulation.compilerPrefix.length + 3) -
          Kc[trimmedIndexedHost](head | base)) :=
      trimmedHeadOutputNumerator_concentration base head count
    _ ≤ 2 ^ (count + lowerChainInnerCost -
          Kc[trimmedIndexedHost](head | base)) := by
      apply Nat.pow_le_pow_right
      · omega
      · exact Nat.sub_le_sub_right
          (Nat.add_le_add_left lowerChainConcentrationCost_le_innerCost count)
          Kc[trimmedIndexedHost](head | base)

/-- Requested length after subtracting the supplied head-complexity index. -/
def subtractedRequestLength
    (sourceLength compilerCost complexityIndex : Nat) : Nat :=
  sourceLength + compilerCost - complexityIndex + 1

/-- When the supplied complexity does not exceed the fixed cost, the source
mass is exactly the request mass scaled by the saved bits plus the reserve
bit. -/
theorem sourceMass_eq_lowScale_mul_requestMass
    (lengths : List Nat) {level compilerCost complexityIndex : Nat}
    (hComplexity : complexityIndex ≤ compilerCost)
    (hFits : ∀ n ∈ lengths,
      subtractedRequestLength n compilerCost complexityIndex ≤ level) :
    (lengths.map fun n => 2 ^ (level - n)).sum =
      2 ^ (compilerCost - complexityIndex + 1) *
        (lengths.map fun n =>
          2 ^ (level -
            subtractedRequestLength n compilerCost complexityIndex)).sum := by
  induction lengths with
  | nil => simp
  | cons n rest ih =>
      have hFitsN := hFits n List.mem_cons_self
      have hFitsRest : ∀ k ∈ rest,
          subtractedRequestLength k compilerCost complexityIndex ≤ level := by
        intro k hk
        exact hFits k (List.mem_cons_of_mem _ hk)
      have hRequestGe : n + 1 ≤
          subtractedRequestLength n compilerCost complexityIndex := by
        unfold subtractedRequestLength
        omega
      have hRequestEq :
          subtractedRequestLength n compilerCost complexityIndex =
            n + (compilerCost - complexityIndex) + 1 := by
        unfold subtractedRequestLength
        omega
      have hExponent : level - n =
          (compilerCost - complexityIndex + 1) +
            (level - subtractedRequestLength n compilerCost
              complexityIndex) := by
        rw [hRequestEq] at hFitsN ⊢
        omega
      have hPoint : 2 ^ (level - n) =
          2 ^ (compilerCost - complexityIndex + 1) *
            2 ^ (level - subtractedRequestLength n compilerCost
              complexityIndex) := by
        rw [hExponent, pow_add]
      simp only [List.map_cons, List.sum_cons]
      rw [hPoint, ih hFitsRest]
      ring

/-- Above the fixed cost, every honest request shifts its source mass upward
by exactly the excess complexity minus the reserve bit. -/
theorem requestMass_eq_highScale_mul_sourceMass
    (lengths : List Nat) {level compilerCost complexityIndex : Nat}
    (hCostLt : compilerCost < complexityIndex)
    (hComplexity : ∀ n ∈ lengths,
      complexityIndex ≤ n + compilerCost)
    (hSourceFits : ∀ n ∈ lengths, n ≤ level) :
    (lengths.map fun n =>
        2 ^ (level -
          subtractedRequestLength n compilerCost complexityIndex)).sum =
      2 ^ (complexityIndex - compilerCost - 1) *
        (lengths.map fun n => 2 ^ (level - n)).sum := by
  induction lengths with
  | nil => simp
  | cons n rest ih =>
      have hComplexityN := hComplexity n List.mem_cons_self
      have hSourceFitsN := hSourceFits n List.mem_cons_self
      have hComplexityRest : ∀ k ∈ rest,
          complexityIndex ≤ k + compilerCost := by
        intro k hk
        exact hComplexity k (List.mem_cons_of_mem _ hk)
      have hSourceFitsRest : ∀ k ∈ rest, k ≤ level := by
        intro k hk
        exact hSourceFits k (List.mem_cons_of_mem _ hk)
      have hExponent : level -
          subtractedRequestLength n compilerCost complexityIndex =
          (complexityIndex - compilerCost - 1) + (level - n) := by
        unfold subtractedRequestLength
        omega
      have hPoint :
          2 ^ (level -
            subtractedRequestLength n compilerCost complexityIndex) =
            2 ^ (complexityIndex - compilerCost - 1) *
              2 ^ (level - n) := by
        rw [hExponent, pow_add]
      simp only [List.map_cons, List.sum_cons]
      rw [hPoint, ih hComplexityRest hSourceFitsRest]
      ring

/-- Raising the common denominator from `small` to `large` scales every
request mass by the same power of two. -/
theorem requestMass_scale_level
    (lengths : List Nat) {small large compilerCost complexityIndex : Nat}
    (hLevels : small ≤ large)
    (hFits : ∀ n ∈ lengths,
      subtractedRequestLength n compilerCost complexityIndex ≤ small) :
    (lengths.map fun n =>
        2 ^ (large -
          subtractedRequestLength n compilerCost complexityIndex)).sum =
      2 ^ (large - small) *
        (lengths.map fun n =>
          2 ^ (small -
            subtractedRequestLength n compilerCost complexityIndex)).sum := by
  induction lengths with
  | nil => simp
  | cons n rest ih =>
      have hFitsN := hFits n List.mem_cons_self
      have hFitsRest : ∀ k ∈ rest,
          subtractedRequestLength k compilerCost complexityIndex ≤ small := by
        intro k hk
        exact hFits k (List.mem_cons_of_mem _ hk)
      have hExponent : large -
          subtractedRequestLength n compilerCost complexityIndex =
          (large - small) +
            (small - subtractedRequestLength n compilerCost
              complexityIndex) := by
        omega
      have hPoint :
          2 ^ (large -
            subtractedRequestLength n compilerCost complexityIndex) =
            2 ^ (large - small) *
              2 ^ (small -
                subtractedRequestLength n compilerCost complexityIndex) := by
        rw [hExponent, pow_add]
      simp only [List.map_cons, List.sum_cons]
      rw [hPoint, ih hFitsRest]
      ring

/-- Raising the common denominator also scales ordinary source-program mass
uniformly. -/
theorem sourceMass_scale_level
    (lengths : List Nat) {small large : Nat}
    (hLevels : small ≤ large)
    (hFits : ∀ n ∈ lengths, n ≤ small) :
    (lengths.map fun n => 2 ^ (large - n)).sum =
      2 ^ (large - small) *
        (lengths.map fun n => 2 ^ (small - n)).sum := by
  induction lengths with
  | nil => simp
  | cons n rest ih =>
      have hFitsN := hFits n List.mem_cons_self
      have hFitsRest : ∀ k ∈ rest, k ≤ small := by
        intro k hk
        exact hFits k (List.mem_cons_of_mem _ hk)
      have hExponent : large - n = (large - small) + (small - n) := by
        omega
      have hPoint : 2 ^ (large - n) =
          2 ^ (large - small) * 2 ^ (small - n) := by
        rw [hExponent, pow_add]
      simp only [List.map_cons, List.sum_cons]
      rw [hPoint, ih hFitsRest]
      ring

/-- A one-bit reserve turns the inner concentration bound into a half-tree
bound for the corresponding outer requests.  The split at
`complexityIndex ≤ compilerCost` is only natural-number bookkeeping: below
the cost, source mass is a multiple of request mass; above it, request mass is
a multiple of source mass. -/
theorem requestMass_le_half_of_sourceMassBound
    (lengths : List Nat) {level compilerCost complexityIndex : Nat}
    (hNonempty : lengths ≠ [])
    (hSourceFits : ∀ n ∈ lengths, n ≤ level)
    (hRequestFits : ∀ n ∈ lengths,
      subtractedRequestLength n compilerCost complexityIndex ≤ level)
    (hComplexity : ∀ n ∈ lengths,
      complexityIndex ≤ n + compilerCost)
    (hSourceBound :
      (lengths.map fun n => 2 ^ (level - n)).sum ≤
        2 ^ (level + compilerCost - complexityIndex)) :
    (lengths.map fun n =>
        2 ^ (level -
          subtractedRequestLength n compilerCost complexityIndex)).sum ≤
      2 ^ (level - 1) := by
  obtain ⟨n, hN⟩ := List.exists_mem_of_ne_nil lengths hNonempty
  have hLevelPositive : 1 ≤ level := by
    have hRequest := hRequestFits n hN
    have hPositive : 1 ≤
        subtractedRequestLength n compilerCost complexityIndex := by
      unfold subtractedRequestLength
      omega
    omega
  have hComplexityLevel : complexityIndex ≤ level + compilerCost := by
    exact (hComplexity n hN).trans
      (Nat.add_le_add_right (hSourceFits n hN) compilerCost)
  by_cases hLow : complexityIndex ≤ compilerCost
  · have hScale := sourceMass_eq_lowScale_mul_requestMass lengths hLow
      hRequestFits
    have hTarget : 2 ^ (level + compilerCost - complexityIndex) =
        2 ^ (compilerCost - complexityIndex + 1) * 2 ^ (level - 1) := by
      have hExponent : level + compilerCost - complexityIndex =
          (compilerCost - complexityIndex + 1) + (level - 1) := by
        omega
      rw [hExponent, pow_add]
    apply Nat.le_of_mul_le_mul_left
        (c := 2 ^ (compilerCost - complexityIndex + 1))
    · rw [← hScale, ← hTarget]
      exact hSourceBound
    · positivity
  · have hCostLt : compilerCost < complexityIndex := by omega
    rw [requestMass_eq_highScale_mul_sourceMass lengths hCostLt
      hComplexity hSourceFits]
    have hScaled := Nat.mul_le_mul_left
      (2 ^ (complexityIndex - compilerCost - 1)) hSourceBound
    have hTarget :
        2 ^ (complexityIndex - compilerCost - 1) *
            2 ^ (level + compilerCost - complexityIndex) =
          2 ^ (level - 1) := by
      rw [← pow_add]
      congr 1
      omega
    rw [hTarget] at hScaled
    exact hScaled

/-- Every genuine event has enough source-program length to finance the
complexity subtraction in its request. -/
theorem lowerChainComplexity_le_program_add_cost
    {base head program : BinString} {complexityIndex index : Nat}
    (hEvent : lowerChainProgramEvent
      (chainCondition base head complexityIndex) index = some program) :
    Kc[trimmedIndexedHost](head | base) ≤
      program.length + lowerChainInnerCost := by
  obtain ⟨fields, hFields, _hCanonical, hFirst⟩ :=
    lowerChainProgramEvent_some hEvent
  rw [decodeChainCondition_chainCondition] at hFields
  have hFieldsEq : fields = ((head, complexityIndex), base) :=
    Option.some.inj hFields.symm
  subst fields
  have hEligible := eligible_of_firstEligibleBoundedConditionalOutputAt hFirst
  unfold eligibleBoundedConditionalOutputAt at hEligible
  by_cases hLength : program.length ≤ (lowerChainCandidate index).1
  · rw [if_pos hLength] at hEligible
    have hSource : IsProgram (firstOutputMachine trimmedIndexedHost)
        program base head :=
      source_compute_of_boundedConditionalOutputAt
        (firstOutputMachine trimmedIndexedHost) trimmedHeadOutputCode
        trimmedHeadOutputCode_spec hEligible
    exact (trimmedHeadComplexity_le_sourceProgram hSource).trans
      (Nat.add_le_add_left lowerChainProjectionCost_le_innerCost _)
  · rw [if_neg hLength] at hEligible
    contradiction

/-- Raising the source-program denominator to `max count L` preserves the
inner concentration bound.  The nonempty branch uses one emitted program to
show that the true head complexity lies below `count + lowerChainInnerCost`,
which makes the natural-number exponent arithmetic exact. -/
theorem lowerChainEventSourceMassAtMax_le
    (base head : BinString) (count L : Nat) :
    ((lowerChainProgramsUpTo
        (chainCondition base head Kc[trimmedIndexedHost](head | base)) count).map
      fun program => 2 ^ (max count L - program.length)).sum ≤
      2 ^ (max count L + lowerChainInnerCost -
        Kc[trimmedIndexedHost](head | base)) := by
  let condition :=
    chainCondition base head Kc[trimmedIndexedHost](head | base)
  let programs := lowerChainProgramsUpTo condition count
  by_cases hEmpty : programs = []
  · simp [programs, condition, hEmpty]
  · have hSourceFits : ∀ n ∈ programs.map List.length, n ≤ count := by
      intro n hN
      obtain ⟨program, hProgram, rfl⟩ := List.mem_map.mp hN
      exact length_le_count_of_mem_lowerChainProgramsUpTo hProgram
    have hScale := sourceMass_scale_level (programs.map List.length)
      (Nat.le_max_left count L) hSourceFits
    have hScale' :
        (programs.map fun program =>
            2 ^ (max count L - program.length)).sum =
          2 ^ (max count L - count) *
            (programs.map fun program =>
              2 ^ (count - program.length)).sum := by
      simpa [List.map_map, Function.comp_def] using hScale
    have hAtCount :
        (programs.map fun program => 2 ^ (count - program.length)).sum ≤
          2 ^ (count + lowerChainInnerCost -
            Kc[trimmedIndexedHost](head | base)) := by
      simpa [programs, condition] using
        lowerChainEventMass_le_concentrationPow base head count
    obtain ⟨program, hProgram⟩ :=
      List.exists_mem_of_ne_nil programs hEmpty
    obtain ⟨index, _hIndex, hEvent⟩ :=
      mem_lowerChainProgramsUpTo.mp hProgram
    have hComplexity := lowerChainComplexity_le_program_add_cost hEvent
    have hProgramLength :=
      length_le_count_of_mem_lowerChainProgramsUpTo hProgram
    have hComplexityCount :
        Kc[trimmedIndexedHost](head | base) ≤
          count + lowerChainInnerCost := by
      omega
    calc
      (programs.map fun program =>
          2 ^ (max count L - program.length)).sum =
          2 ^ (max count L - count) *
            (programs.map fun program =>
              2 ^ (count - program.length)).sum := hScale'
      _ ≤ 2 ^ (max count L - count) *
          2 ^ (count + lowerChainInnerCost -
            Kc[trimmedIndexedHost](head | base)) :=
        Nat.mul_le_mul_left _ hAtCount
      _ = 2 ^ (max count L + lowerChainInnerCost -
          Kc[trimmedIndexedHost](head | base)) := by
        rw [← pow_add]
        congr 1
        omega

/-- Every paired source computation appears as one genuine outer request
event at a canonical enumeration index. -/
theorem exists_lowerChainProgramEvent_of_pairProgram
    {base head tail program : BinString}
    (hProgram : IsProgram trimmedIndexedHost program base
      (pairCondition head tail)) :
    ∃ index, lowerChainProgramEvent
      (chainCondition base head Kc[trimmedIndexedHost](head | base)) index =
        some program := by
  have hHead : IsProgram (firstOutputMachine trimmedIndexedHost)
      program base head := firstOutputMachine_program hProgram
  obtain ⟨stage, hLength, _hOutputCode, hBounded⟩ :=
    exists_boundedConditionalOutputAt_of_source_compute
      (firstOutputMachine trimmedIndexedHost) trimmedHeadOutputCode
      trimmedHeadOutputCode_spec hHead
  have hEligible : eligibleBoundedConditionalOutputAt trimmedHeadOutputCode
      base stage program = some head := by
    unfold eligibleBoundedConditionalOutputAt
    rw [if_pos hLength]
    exact hBounded
  obtain ⟨first, _hFirstLe, hFirst⟩ :=
    exists_firstEligibleBoundedConditionalOutputAt hEligible
  refine ⟨Nat.pair first (Encodable.encode program), ?_⟩
  simp [lowerChainProgramEvent, lowerChainCandidate,
    decodeChainCondition_chainCondition, hFirst]

/-- Every enumeration slot is a total request.  A genuine first-observation
event requests its source program at the chain-rule length, plus one reserve
bit.  A non-event uses the summable geometric fallback length `index + 2`.
The fallback keeps the request generator total without repeatedly charging a
source program. -/
noncomputable def lowerChainRequests
    (condition : BinString) (index : Nat) : Request BinString :=
  match decodeChainCondition condition,
      lowerChainProgramEvent condition index with
  | some fields, some program =>
      ⟨program, program.length + lowerChainInnerCost - fields.1.2 + 1⟩
  | _, _ => ⟨[], index + 2⟩

theorem lowerChainRequests_of_event
    {condition program : BinString} {index : Nat}
    {fields : ChainConditionFields}
    (hFields : decodeChainCondition condition = some fields)
    (hEvent : lowerChainProgramEvent condition index = some program) :
    lowerChainRequests condition index =
      ⟨program, program.length + lowerChainInnerCost - fields.1.2 + 1⟩ := by
  simp [lowerChainRequests, hFields, hEvent]

theorem lowerChainRequests_of_no_event
    {condition : BinString} {index : Nat}
    (hEvent : lowerChainProgramEvent condition index = none) :
    lowerChainRequests condition index = ⟨[], index + 2⟩ := by
  simp [lowerChainRequests, hEvent]

theorem lowerChainRequests_requestedLength_pos
    (condition : BinString) (index : Nat) :
    0 < (lowerChainRequests condition index).requestedLength := by
  unfold lowerChainRequests
  cases decodeChainCondition condition <;>
    cases lowerChainProgramEvent condition index <;> simp

/-- If all requests in a canonical finite prefix fit level `L`, then the
request generated by every genuine source-program event in that prefix fits
`L` as well. -/
theorem lowerChainActualRequestLength_le
    {base head program : BinString} {count L : Nat}
    (hLengths : ∀ n ∈ requestedLengthsUpTo lowerChainRequests
        (chainCondition base head Kc[trimmedIndexedHost](head | base)) count,
      n ≤ L)
    (hProgram : program ∈ lowerChainProgramsUpTo
      (chainCondition base head Kc[trimmedIndexedHost](head | base)) count) :
    subtractedRequestLength program.length lowerChainInnerCost
        Kc[trimmedIndexedHost](head | base) ≤ L := by
  obtain ⟨index, hIndex, hEvent⟩ :=
    mem_lowerChainProgramsUpTo.mp hProgram
  have hBound := hLengths _
    (requestedLength_mem_requestedLengthsUpTo hIndex)
  have hRequest := lowerChainRequests_of_event
    (decodeChainCondition_chainCondition base head
      Kc[trimmedIndexedHost](head | base)) hEvent
  rw [hRequest] at hBound
  simpa [subtractedRequestLength] using hBound

/-- Genuine chain events use at most one half of the code tree at every
finite request prefix.  The proof raises both source and request masses to the
common level `max count L`, applies inner concentration there, and then
cancels the common denominator scale back down to `L`. -/
theorem lowerChainActualRequestMass_le_half
    (base head : BinString) (count L : Nat)
    (hLengths : ∀ n ∈ requestedLengthsUpTo lowerChainRequests
        (chainCondition base head Kc[trimmedIndexedHost](head | base)) count,
      n ≤ L) :
    ((lowerChainProgramsUpTo
        (chainCondition base head Kc[trimmedIndexedHost](head | base)) count).map
      fun program =>
        2 ^ (L - subtractedRequestLength program.length lowerChainInnerCost
          Kc[trimmedIndexedHost](head | base))).sum ≤
      2 ^ (L - 1) := by
  let condition :=
    chainCondition base head Kc[trimmedIndexedHost](head | base)
  let programs := lowerChainProgramsUpTo condition count
  let lengths := programs.map List.length
  by_cases hEmpty : programs = []
  · simp [programs, condition, hEmpty]
  · have hLengthsNonempty : lengths ≠ [] := by
      simp [lengths, hEmpty]
    have hSourceFitsMax : ∀ n ∈ lengths, n ≤ max count L := by
      intro n hN
      obtain ⟨program, hProgram, rfl⟩ := List.mem_map.mp hN
      exact (length_le_count_of_mem_lowerChainProgramsUpTo hProgram).trans
        (Nat.le_max_left _ _)
    have hRequestFitsL : ∀ n ∈ lengths,
        subtractedRequestLength n lowerChainInnerCost
          Kc[trimmedIndexedHost](head | base) ≤ L := by
      intro n hN
      obtain ⟨program, hProgram, rfl⟩ := List.mem_map.mp hN
      exact lowerChainActualRequestLength_le hLengths hProgram
    have hRequestFitsMax : ∀ n ∈ lengths,
        subtractedRequestLength n lowerChainInnerCost
          Kc[trimmedIndexedHost](head | base) ≤ max count L := by
      intro n hN
      exact (hRequestFitsL n hN).trans (Nat.le_max_right _ _)
    have hComplexity : ∀ n ∈ lengths,
        Kc[trimmedIndexedHost](head | base) ≤ n + lowerChainInnerCost := by
      intro n hN
      obtain ⟨program, hProgram, rfl⟩ := List.mem_map.mp hN
      obtain ⟨index, _hIndex, hEvent⟩ :=
        mem_lowerChainProgramsUpTo.mp hProgram
      exact lowerChainComplexity_le_program_add_cost hEvent
    have hSourceBound :
        (lengths.map fun n => 2 ^ (max count L - n)).sum ≤
          2 ^ (max count L + lowerChainInnerCost -
            Kc[trimmedIndexedHost](head | base)) := by
      simpa [lengths, programs, condition, List.map_map, Function.comp_def]
        using lowerChainEventSourceMassAtMax_le base head count L
    have hAtMax := requestMass_le_half_of_sourceMassBound lengths
      hLengthsNonempty hSourceFitsMax hRequestFitsMax hComplexity hSourceBound
    have hScale := requestMass_scale_level lengths
      (Nat.le_max_right count L) hRequestFitsL
    have hScale' :
        (programs.map fun program =>
            2 ^ (max count L -
              subtractedRequestLength program.length lowerChainInnerCost
                Kc[trimmedIndexedHost](head | base))).sum =
          2 ^ (max count L - L) *
            (programs.map fun program =>
              2 ^ (L -
                subtractedRequestLength program.length lowerChainInnerCost
                  Kc[trimmedIndexedHost](head | base))).sum := by
      simpa [lengths, List.map_map, Function.comp_def] using hScale
    have hLevelPositive : 1 ≤ L := by
      obtain ⟨n, hN⟩ := List.exists_mem_of_ne_nil lengths hLengthsNonempty
      have hFit := hRequestFitsL n hN
      have hPositive : 1 ≤ subtractedRequestLength n lowerChainInnerCost
          Kc[trimmedIndexedHost](head | base) := by
        unfold subtractedRequestLength
        omega
      omega
    have hTarget : 2 ^ (max count L - 1) =
        2 ^ (max count L - L) * 2 ^ (L - 1) := by
      rw [← pow_add]
      congr 1
      omega
    apply Nat.le_of_mul_le_mul_left
        (c := 2 ^ (max count L - L))
    · rw [← hScale', ← hTarget]
      simpa [lengths, List.map_map, Function.comp_def] using hAtMax
    · positivity

/-- Indices in a finite request prefix that use the geometric fallback. -/
noncomputable def lowerChainFallbackIndices
    (condition : BinString) (count : Nat) : Finset Nat :=
  (Finset.range count).filter fun index =>
    lowerChainProgramEvent condition index = none

/-- Exact mass of a complete fallback range.  The extra fallback bit reserves
one half of the binary code tree for genuine chain events. -/
theorem lowerChainFallbackRange_mass (L : Nat) :
    (∑ index ∈ Finset.range (L - 1), 2 ^ (L - (index + 2))) =
      2 ^ (L - 1) - 1 := by
  have hGeometric := geometricRequests_mass ([] : BinString)
    (L - 1) (L - 1) (Nat.le_refl _)
  rw [sum_map_requestedLengthsUpTo_eq_sum_range] at hGeometric
  simp only [geometricRequests] at hGeometric
  calc
    (∑ index ∈ Finset.range (L - 1), 2 ^ (L - (index + 2))) =
        ∑ index ∈ Finset.range (L - 1),
          2 ^ ((L - 1) - (index + 1)) := by
      apply Finset.sum_congr rfl
      intro index hIndex
      rw [Finset.mem_range] at hIndex
      congr 1
      omega
    _ = 2 ^ (L - 1) - 2 ^ ((L - 1) - (L - 1)) := hGeometric
    _ = 2 ^ (L - 1) - 1 := by simp

/-- If every request in the finite prefix fits level `L`, every fallback
index lies in the complete range of the previous theorem. -/
theorem lowerChainFallbackIndices_subset_range
    {condition : BinString} {count L : Nat}
    (hLengths : ∀ n ∈ requestedLengthsUpTo lowerChainRequests condition count,
      n ≤ L) :
    lowerChainFallbackIndices condition count ⊆ Finset.range (L - 1) := by
  intro index hIndex
  rw [lowerChainFallbackIndices, Finset.mem_filter] at hIndex
  have hIndexLt : index < count := Finset.mem_range.mp hIndex.1
  have hLength := hLengths _
    (requestedLength_mem_requestedLengthsUpTo hIndexLt)
  have hRequest := lowerChainRequests_of_no_event hIndex.2
  have hRequestedLength := congrArg Request.requestedLength hRequest
  simp only at hRequestedLength
  rw [hRequestedLength] at hLength
  rw [Finset.mem_range]
  omega

/-- The total fallback mass uses strictly less than one half of the available
binary code capacity. -/
theorem lowerChainFallbackMass_le
    {condition : BinString} {count L : Nat}
    (hLengths : ∀ n ∈ requestedLengthsUpTo lowerChainRequests condition count,
      n ≤ L) :
    (∑ index ∈ lowerChainFallbackIndices condition count,
        2 ^ (L - (index + 2))) ≤ 2 ^ (L - 1) - 1 := by
  calc
    (∑ index ∈ lowerChainFallbackIndices condition count,
        2 ^ (L - (index + 2))) ≤
        ∑ index ∈ Finset.range (L - 1),
          2 ^ (L - (index + 2)) :=
      Finset.sum_le_sum_of_subset
        (lowerChainFallbackIndices_subset_range hLengths)
    _ = 2 ^ (L - 1) - 1 := lowerChainFallbackRange_mass L

/-- At the true head-complexity condition, the finite request mass splits
exactly into genuine source-program requests and geometric fallbacks. -/
theorem lowerChainRequestMass_eq_actual_add_fallback
    (base head : BinString) (count L : Nat) :
    ((requestedLengthsUpTo lowerChainRequests
        (chainCondition base head Kc[trimmedIndexedHost](head | base)) count).map
      fun n => 2 ^ (L - n)).sum =
      ((lowerChainProgramsUpTo
          (chainCondition base head Kc[trimmedIndexedHost](head | base)) count).map
        fun program =>
          2 ^ (L - subtractedRequestLength program.length lowerChainInnerCost
            Kc[trimmedIndexedHost](head | base))).sum +
      ∑ index ∈ lowerChainFallbackIndices
          (chainCondition base head Kc[trimmedIndexedHost](head | base)) count,
        2 ^ (L - (index + 2)) := by
  let condition :=
    chainCondition base head Kc[trimmedIndexedHost](head | base)
  rw [sum_map_requestedLengthsUpTo_eq_sum_range,
    sum_lowerChainProgramsUpTo_eq_sum_range]
  rw [lowerChainFallbackIndices, Finset.sum_filter,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro index _hIndex
  cases hEvent : lowerChainProgramEvent condition index with
  | none =>
      have hRequest := lowerChainRequests_of_no_event hEvent
      rw [hRequest]
      simp
  | some program =>
      have hRequest := lowerChainRequests_of_event
        (decodeChainCondition_chainCondition base head
          Kc[trimmedIndexedHost](head | base)) hEvent
      rw [hRequest]
      simp [subtractedRequestLength]

/-- The true head-complexity slice satisfies the complete condition-local
Kraft budget.  Genuine events and totality fallbacks each occupy a disjoint
half-budget, with the fallback side leaving one integer unit unused. -/
theorem lowerChainRequests_kraftBudgetAt (base head : BinString) :
    KraftBudgetAt lowerChainRequests
      (chainCondition base head Kc[trimmedIndexedHost](head | base)) := by
  intro count L hLengths
  rw [lowerChainRequestMass_eq_actual_add_fallback base head count L]
  have hActual :=
    lowerChainActualRequestMass_le_half base head count L hLengths
  have hFallback := lowerChainFallbackMass_le hLengths
  by_cases hZero : L = 0
  · subst L
    have hCountZero : count = 0 := by
      by_contra hCount
      have hIndex : 0 < count := Nat.pos_of_ne_zero hCount
      have hBound := hLengths _
        (requestedLength_mem_requestedLengthsUpTo hIndex)
      have hPositive := lowerChainRequests_requestedLength_pos
        (chainCondition base head Kc[trimmedIndexedHost](head | base)) 0
      omega
    subst count
    simp [lowerChainProgramsUpTo, lowerChainFallbackIndices]
  · have hPower := Nat.two_pow_pred_add_two_pow_pred
      (Nat.pos_of_ne_zero hZero)
    omega

theorem lowerChainRequests_effective :
    EffectiveRequestStream lowerChainRequests := by
  have hEvent : Primrec fun input : LowerChainEventInput =>
      lowerChainProgramEvent input.1 input.2 :=
    lowerChainProgramEvent_primrec.comp Primrec.fst Primrec.snd
  constructor
  · apply Primrec₂.mk
    exact (Primrec.option_getD.comp hEvent (Primrec.const [])).of_eq
      fun input => by
        unfold lowerChainRequests
        cases hFields : decodeChainCondition input.1 with
        | none =>
            have hEventNone : lowerChainProgramEvent input.1 input.2 = none := by
              simp [lowerChainProgramEvent, hFields]
            rw [hEventNone]
            rfl
        | some fields =>
            cases hEventAt : lowerChainProgramEvent input.1 input.2 <;> rfl
  · apply Primrec₂.mk
    have hFields : Primrec fun input : LowerChainEventInput =>
        decodeChainCondition input.1 :=
      decodeChainCondition_primrec.comp Primrec.fst
    have hFallback : Primrec fun input : LowerChainEventInput => input.2 + 2 :=
      Primrec.nat_add.comp Primrec.snd (Primrec.const 2)
    have hFieldsBranch : Primrec₂ fun (input : LowerChainEventInput)
        (fields : ChainConditionFields) =>
        match lowerChainProgramEvent input.1 input.2 with
        | none => input.2 + 2
        | some program =>
            program.length + lowerChainInnerCost - fields.1.2 + 1 := by
      apply Primrec₂.mk
      have hContextEvent : Primrec fun context : LowerChainFieldContext =>
          lowerChainProgramEvent context.1.1 context.1.2 :=
        hEvent.comp Primrec.fst
      have hActual : Primrec₂ fun (context : LowerChainFieldContext)
          (program : BinString) =>
          program.length + lowerChainInnerCost - context.2.1.2 + 1 := by
        have hProgramLength : Primrec fun pair :
            LowerChainFieldContext × BinString => pair.2.length :=
          Primrec.list_length.comp Primrec.snd
        have hIndex : Primrec fun pair :
            LowerChainFieldContext × BinString => pair.1.2.1.2 :=
          Primrec.snd.comp (Primrec.fst.comp
            (Primrec.snd.comp Primrec.fst))
        exact (Primrec.succ.comp
          (Primrec.nat_sub.comp
            (Primrec.nat_add.comp hProgramLength
              (Primrec.const lowerChainInnerCost)) hIndex)).to₂
      exact (Primrec.option_casesOn hContextEvent
        (hFallback.comp Primrec.fst) hActual).of_eq fun context => by
          cases lowerChainProgramEvent context.1.1 context.1.2 <;> rfl
    exact (Primrec.option_casesOn hFields hFallback hFieldsBranch).of_eq
      fun input => by
        unfold lowerChainRequests
        cases hFieldsAt : decodeChainCondition input.1 with
        | none => rfl
        | some fields =>
            cases hEventAt : lowerChainProgramEvent input.1 input.2 <;> rfl

/-- The safe outer program coder.  Incorrect numerical indices can cause
requests to be rejected, but cannot compromise prefix-freeness. -/
noncomputable def lowerChainProgramMachine : ConditionalPrefixFreeMachine :=
  saturatedKcMachine lowerChainRequests

/-- Every paired source program receives an outer code of exactly the repaired
chain-rule request length. -/
theorem exists_lowerChainProgramCode_of_pairProgram
    {base head tail program : BinString}
    (hProgram : IsProgram trimmedIndexedHost program base
      (pairCondition head tail)) :
    ∃ code,
      code.length = subtractedRequestLength program.length lowerChainInnerCost
        Kc[trimmedIndexedHost](head | base) ∧
      IsProgram lowerChainProgramMachine code
        (chainCondition base head Kc[trimmedIndexedHost](head | base)) program := by
  obtain ⟨index, hEvent⟩ :=
    exists_lowerChainProgramEvent_of_pairProgram hProgram
  obtain ⟨code, hLength, hCompute⟩ :=
    saturatedKcMachine_realizes_request_at
      (lowerChainRequests_kraftBudgetAt base head) index
  have hRequest := lowerChainRequests_of_event
    (decodeChainCondition_chainCondition base head
      Kc[trimmedIndexedHost](head | base)) hEvent
  rw [hRequest] at hLength hCompute
  refine ⟨code, ?_, hCompute⟩
  simpa [subtractedRequestLength] using hLength

theorem lowerChainProgramMachine_effective :
    Partrec₂ fun program condition =>
      Part.ofOption (lowerChainProgramMachine.compute program condition) := by
  exact saturatedKcMachine_effective lowerChainRequests_effective

/-- The final outer machine turns an assigned source-program value into the
tail selected by the chain condition. -/
noncomputable def lowerChainTailMachine : ConditionalPrefixFreeMachine :=
  outputCompositionMachine lowerChainProgramMachine
    (chainTailMachine trimmedIndexedHost)

/-- The same allocated code reconstructs the advertised tail through the
source program carried by its request. -/
theorem exists_lowerChainTailCode_of_pairProgram
    {base head tail program : BinString}
    (hProgram : IsProgram trimmedIndexedHost program base
      (pairCondition head tail)) :
    ∃ code,
      code.length = subtractedRequestLength program.length lowerChainInnerCost
        Kc[trimmedIndexedHost](head | base) ∧
      IsProgram lowerChainTailMachine code
        (chainCondition base head Kc[trimmedIndexedHost](head | base)) tail := by
  obtain ⟨code, hLength, hProducer⟩ :=
    exists_lowerChainProgramCode_of_pairProgram hProgram
  have hTransformer := chainTailMachine_program
    (complexityIndex := Kc[trimmedIndexedHost](head | base)) hProgram
  exact ⟨code, hLength,
    outputCompositionMachine_program hProducer hTransformer⟩

theorem lowerChainTailMachine_effective :
    Partrec₂ fun program condition =>
      Part.ofOption (lowerChainTailMachine.compute program condition) := by
  exact outputCompositionMachine_effective _ _
    lowerChainProgramMachine_effective
    (chainTailMachine_effective trimmedIndexedHost
      trimmedIndexedHost_effective)

/-- A fixed simulation of the effective outer tail machine by the concrete
trimmed indexed host. -/
noncomputable def trimmedLowerChainTailSimulation :
    UniformlySimulates trimmedIndexedHost lowerChainTailMachine :=
  Classical.choice (trimmedIndexedHost_simulates_effective _
    lowerChainTailMachine_effective)

/-- Compiling the effective outer machine back into the reference host adds
only its fixed compiler prefix. -/
theorem exists_trimmedLowerChainTailCode_of_pairProgram
    {base head tail program : BinString}
    (hProgram : IsProgram trimmedIndexedHost program base
      (pairCondition head tail)) :
    ∃ code,
      code.length =
        trimmedLowerChainTailSimulation.compilerPrefix.length +
          subtractedRequestLength program.length lowerChainInnerCost
            Kc[trimmedIndexedHost](head | base) ∧
      IsProgram trimmedIndexedHost code
        (chainCondition base head Kc[trimmedIndexedHost](head | base)) tail := by
  obtain ⟨innerCode, hLength, hInner⟩ :=
    exists_lowerChainTailCode_of_pairProgram hProgram
  refine ⟨trimmedLowerChainTailSimulation.compilerPrefix ++ innerCode, ?_,
    trimmedLowerChainTailSimulation.program hInner⟩
  simp [List.length_append, hLength]

/-- Pointwise lower-chain coding bound from any represented pair program. -/
theorem lowerChainTailComplexity_le_of_pairProgram
    {base head tail program : BinString}
    (hProgram : IsProgram trimmedIndexedHost program base
      (pairCondition head tail)) :
    Kc[trimmedIndexedHost](tail |
        chainCondition base head Kc[trimmedIndexedHost](head | base)) ≤
      subtractedRequestLength program.length lowerChainInnerCost
          Kc[trimmedIndexedHost](head | base) +
        trimmedLowerChainTailSimulation.compilerPrefix.length := by
  obtain ⟨code, hLength, hCode⟩ :=
    exists_trimmedLowerChainTailCode_of_pairProgram hProgram
  have hBound := conditionalComplexity_le_program_length trimmedIndexedHost
    (chainCondition base head Kc[trimmedIndexedHost](head | base)) tail code hCode
  rw [hLength] at hBound
  simpa [Nat.add_comm] using hBound

/-- The lower-chain inequality already holds relative to the length of every
concrete pair program. -/
theorem lowerChainInequality_of_pairProgram
    {base head tail program : BinString}
    (hProgram : IsProgram trimmedIndexedHost program base
      (pairCondition head tail)) :
    Kc[trimmedIndexedHost](head | base) +
        Kc[trimmedIndexedHost](tail |
          chainCondition base head Kc[trimmedIndexedHost](head | base)) ≤
      program.length +
        (lowerChainInnerCost + 1 +
          trimmedLowerChainTailSimulation.compilerPrefix.length) := by
  have hTail := lowerChainTailComplexity_le_of_pairProgram hProgram
  have hHead : IsProgram (firstOutputMachine trimmedIndexedHost)
      program base head := firstOutputMachine_program hProgram
  have hFinance := (trimmedHeadComplexity_le_sourceProgram hHead).trans
    (Nat.add_le_add_left lowerChainProjectionCost_le_innerCost _)
  unfold subtractedRequestLength at hTail
  omega

/-- Pair representability is the only remaining premise needed to package
the proved coding construction as a lower conditional chain rule. -/
noncomputable def lowerConditionalChainRuleOfPairRepresentability
    (pairHasProgram : ∀ base head tail,
      HasProgram trimmedIndexedHost base head →
      HasProgram trimmedIndexedHost
        (chainCondition base head Kc[trimmedIndexedHost](head | base)) tail →
      HasProgram trimmedIndexedHost base (pairCondition head tail)) :
    LowerConditionalChainRule trimmedIndexedHost where
  constant := lowerChainInnerCost + 1 +
    trimmedLowerChainTailSimulation.compilerPrefix.length
  lower := by
    intro base head tail headHas tailHas
    obtain ⟨program, hProgram, hLength⟩ :=
      exists_program_of_conditionalComplexity trimmedIndexedHost base
        (pairCondition head tail) (pairHasProgram base head tail headHas tailHas)
    have hBound := lowerChainInequality_of_pairProgram hProgram
    rw [hLength] at hBound
    exact hBound

/-! ## Positive and negative controls -/

/-- A paired source output is visible to the inner head machine. -/
example {program condition head tail : BinString}
    (h : IsProgram trimmedIndexedHost program condition
      (pairCondition head tail)) :
    IsProgram (firstOutputMachine trimmedIndexedHost) program condition head :=
  firstOutputMachine_program h

/-- A malformed output does not become a head value. -/
example (U : ConditionalPrefixFreeMachine) (program condition : BinString)
    (h : U.compute program condition = some []) :
    (firstOutputMachine U).compute program condition = none := by
  simp [firstOutputMachine, h, unpairCondition, decodeMachinePrefix]

#print axioms unpairCondition_primrec
#print axioms decodeChainCondition_primrec
#print axioms chainTailMachine_effective
#print axioms outputCompositionMachine_effective
#print axioms firstOutputMachine_effective
#print axioms trimmedHeadOutputNumerator_concentration
#print axioms lowerChainProgramEvent_primrec
#print axioms lowerChainProgramEvent_index_injective
#print axioms lowerChainRequests_kraftBudgetAt
#print axioms lowerChainRequests_effective
#print axioms lowerChainTailMachine_effective
#print axioms lowerChainInequality_of_pairProgram
#print axioms lowerConditionalChainRuleOfPairRepresentability

end KraftChaitin

end KolmogorovComplexity
