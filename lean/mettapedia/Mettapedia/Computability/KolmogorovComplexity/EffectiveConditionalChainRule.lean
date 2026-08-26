import Mettapedia.Computability.KolmogorovComplexity.ConditionalLowerChainRule

/-!
# Effective conditional prefix-complexity chain rule

This file supplies the executable upper pairing machine needed to close the
conditional chain rule for `trimmedIndexedHost`.  A search rank encodes a fuel
stage and a split point in the concatenated program.  At each rank, bounded
evaluation checks the candidate head prefix and tail suffix.  Unbounded search
over those total checks is partial recursive; prefix-freeness makes any
successful split unique.
-/

namespace KolmogorovComplexity

open scoped Classical

namespace KraftChaitin

/-- A concrete evaluator code for the trimmed indexed host. -/
noncomputable def trimmedIndexedHostCode : Nat.Partrec.Code :=
  Classical.choose (exists_code_of_conditionalMachine_effective
    trimmedIndexedHost trimmedIndexedHost_effective)

theorem trimmedIndexedHostCode_spec :
    Nat.Partrec.Code.eval trimmedIndexedHostCode =
      encodedConditionalCompute trimmedIndexedHost :=
  Classical.choose_spec (exists_code_of_conditionalMachine_effective
    trimmedIndexedHost trimmedIndexedHost_effective)

abbrev ChainPairSearchStepInput := (BinString × BinString) × Nat
abbrev ChainPairTailContext := ChainPairSearchStepInput × BinString

def chainPairSearchCandidate (input : ChainPairSearchStepInput) : Nat × Nat :=
  input.2.unpair

def chainPairHeadArguments
    (input : ChainPairSearchStepInput) : BoundedConditionalOutputInput :=
  ((input.1.2, (chainPairSearchCandidate input).1),
    input.1.1.take (chainPairSearchCandidate input).2)

def chainPairTailArguments
    (context : ChainPairTailContext) : BoundedConditionalOutputInput :=
  let input := context.1
  let head := context.2
  let split := (chainPairSearchCandidate input).2
  ((chainCondition input.1.2 head split,
      (chainPairSearchCandidate input).1),
    input.1.1.drop split)

/-- One total search check for an effective concatenated pair program. -/
def chainPairSearchStep (code : Nat.Partrec.Code)
    (input : ChainPairSearchStepInput) : Option BinString :=
  if (chainPairSearchCandidate input).2 ≤ input.1.1.length then
    (boundedConditionalOutputAt code
      (chainPairHeadArguments input).1.1
      (chainPairHeadArguments input).1.2
      (chainPairHeadArguments input).2).bind fun head =>
        (boundedConditionalOutputAt code
          (chainPairTailArguments (input, head)).1.1
          (chainPairTailArguments (input, head)).1.2
          (chainPairTailArguments (input, head)).2).map fun tail =>
            pairCondition head tail
  else none

theorem chainPairSearchCandidate_primrec : Primrec chainPairSearchCandidate := by
  exact Primrec.unpair.comp Primrec.snd

theorem chainPairHeadArguments_primrec : Primrec chainPairHeadArguments := by
  have hStage : Primrec fun input : ChainPairSearchStepInput =>
      (chainPairSearchCandidate input).1 :=
    Primrec.fst.comp chainPairSearchCandidate_primrec
  have hSplit : Primrec fun input : ChainPairSearchStepInput =>
      (chainPairSearchCandidate input).2 :=
    Primrec.snd.comp chainPairSearchCandidate_primrec
  exact ((Primrec.snd.comp Primrec.fst).pair hStage).pair
    (Primrec.list_take.comp hSplit (Primrec.fst.comp Primrec.fst))

theorem chainPairTailArguments_primrec : Primrec chainPairTailArguments := by
  have hInput : Primrec fun context : ChainPairTailContext => context.1 :=
    Primrec.fst
  have hStage : Primrec fun context : ChainPairTailContext =>
      (chainPairSearchCandidate context.1).1 :=
    (Primrec.fst.comp chainPairSearchCandidate_primrec).comp hInput
  have hSplit : Primrec fun context : ChainPairTailContext =>
      (chainPairSearchCandidate context.1).2 :=
    (Primrec.snd.comp chainPairSearchCandidate_primrec).comp hInput
  have hCondition : Primrec fun context : ChainPairTailContext =>
      context.1.1.2 :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have hChain : Primrec fun context : ChainPairTailContext =>
      chainCondition context.1.1.2 context.2
        (chainPairSearchCandidate context.1).2 :=
    chainCondition_primrec.comp
      ((hCondition.pair Primrec.snd).pair hSplit)
  have hTail : Primrec fun context : ChainPairTailContext =>
      context.1.1.1.drop (chainPairSearchCandidate context.1).2 :=
    Primrec.list_drop.comp hSplit
      (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
  exact (hChain.pair hStage).pair hTail

theorem chainPairSearchStep_primrec (code : Nat.Partrec.Code) :
    Primrec (chainPairSearchStep code) := by
  have hCandidate := chainPairSearchCandidate_primrec
  have hFits : PrimrecPred fun input : ChainPairSearchStepInput =>
      (chainPairSearchCandidate input).2 ≤ input.1.1.length :=
    Primrec.nat_le.comp
      (Primrec.snd.comp hCandidate)
      (Primrec.list_length.comp (Primrec.fst.comp Primrec.fst))
  have hHead : Primrec fun input : ChainPairSearchStepInput =>
      boundedConditionalOutputAt code
        (chainPairHeadArguments input).1.1
        (chainPairHeadArguments input).1.2
        (chainPairHeadArguments input).2 :=
    (boundedConditionalOutputAt_primrec code).comp
      chainPairHeadArguments_primrec
  have hTail : Primrec fun context : ChainPairTailContext =>
      boundedConditionalOutputAt code
        (chainPairTailArguments context).1.1
        (chainPairTailArguments context).1.2
        (chainPairTailArguments context).2 :=
    (boundedConditionalOutputAt_primrec code).comp
      chainPairTailArguments_primrec
  have hPair : Primrec₂ fun (context : ChainPairTailContext)
      (tail : BinString) => pairCondition context.2 tail :=
    pairCondition_primrec.comp₂
      (Primrec.snd.comp₂ Primrec₂.left) Primrec₂.right
  have hTailMapped : Primrec fun context : ChainPairTailContext =>
      (boundedConditionalOutputAt code
        (chainPairTailArguments context).1.1
        (chainPairTailArguments context).1.2
        (chainPairTailArguments context).2).map fun tail =>
          pairCondition context.2 tail :=
    Primrec.option_map hTail hPair
  have hBody : Primrec fun input : ChainPairSearchStepInput =>
      (boundedConditionalOutputAt code
        (chainPairHeadArguments input).1.1
        (chainPairHeadArguments input).1.2
        (chainPairHeadArguments input).2).bind fun head =>
          (boundedConditionalOutputAt code
            (chainPairTailArguments (input, head)).1.1
            (chainPairTailArguments (input, head)).1.2
            (chainPairTailArguments (input, head)).2).map fun tail =>
              pairCondition head tail :=
    Primrec.option_bind hHead hTailMapped.to₂
  exact Primrec.ite hFits hBody (Primrec.const none)

theorem chainPairRun_of_searchStep
    {program condition output : BinString} {rank : Nat}
    (hStep : chainPairSearchStep trimmedIndexedHostCode
      ((program, condition), rank) = some output) :
    ChainPairRun trimmedIndexedHost program condition output := by
  unfold chainPairSearchStep at hStep
  by_cases hFits : (chainPairSearchCandidate ((program, condition), rank)).2 ≤
      program.length
  · rw [if_pos hFits] at hStep
    cases hHead : boundedConditionalOutputAt trimmedIndexedHostCode
        (chainPairHeadArguments ((program, condition), rank)).1.1
        (chainPairHeadArguments ((program, condition), rank)).1.2
        (chainPairHeadArguments ((program, condition), rank)).2 with
    | none => simp [hHead] at hStep
    | some head =>
        rw [hHead, Option.bind_some] at hStep
        cases hTail : boundedConditionalOutputAt trimmedIndexedHostCode
            (chainPairTailArguments (((program, condition), rank), head)).1.1
            (chainPairTailArguments (((program, condition), rank), head)).1.2
            (chainPairTailArguments (((program, condition), rank), head)).2 with
        | none => simp [hTail] at hStep
        | some tail =>
            rw [hTail] at hStep
            have hOutput : pairCondition head tail = output :=
              Option.some.inj hStep
            let split :=
              (chainPairSearchCandidate ((program, condition), rank)).2
            let headProgram := program.take split
            let tailProgram := program.drop split
            have hProgramEq : program = headProgram ++ tailProgram := by
              exact (List.take_append_drop split program).symm
            have hHeadSource : IsProgram trimmedIndexedHost headProgram
                condition head := by
              exact source_compute_of_boundedConditionalOutputAt
                trimmedIndexedHost trimmedIndexedHostCode
                trimmedIndexedHostCode_spec hHead
            have hTailSource : IsProgram trimmedIndexedHost tailProgram
                (chainCondition condition head split) tail := by
              exact source_compute_of_boundedConditionalOutputAt
                trimmedIndexedHost trimmedIndexedHostCode
                trimmedIndexedHostCode_spec hTail
            have hHeadLength : headProgram.length = split := by
              simp only [headProgram, List.length_take]
              exact min_eq_left hFits
            refine ⟨headProgram, tailProgram, head, tail, hProgramEq,
              hHeadSource, ?_, hOutput.symm⟩
            simpa [hHeadLength] using hTailSource
  · rw [if_neg hFits] at hStep
    contradiction

theorem exists_chainPairSearchStep_of_run
    {program condition output : BinString}
    (hRun : ChainPairRun trimmedIndexedHost program condition output) :
    ∃ rank, chainPairSearchStep trimmedIndexedHostCode
      ((program, condition), rank) = some output := by
  rcases hRun with
    ⟨headProgram, tailProgram, head, tail, hProgramEq, hHead, hTail,
      hOutputEq⟩
  obtain ⟨headStage, _hHeadLength, _hHeadOutput, hHeadBounded⟩ :=
    exists_boundedConditionalOutputAt_of_source_compute
      trimmedIndexedHost trimmedIndexedHostCode trimmedIndexedHostCode_spec hHead
  obtain ⟨tailStage, _hTailLength, _hTailOutput, hTailBounded⟩ :=
    exists_boundedConditionalOutputAt_of_source_compute
      trimmedIndexedHost trimmedIndexedHostCode trimmedIndexedHostCode_spec hTail
  let stage := max headStage tailStage
  have hHeadAt : boundedConditionalOutputAt trimmedIndexedHostCode condition
      stage headProgram = some head :=
    boundedConditionalOutputAt_mono hHeadBounded (Nat.le_max_left _ _)
  have hTailAt : boundedConditionalOutputAt trimmedIndexedHostCode
      (chainCondition condition head headProgram.length) stage tailProgram =
        some tail :=
    boundedConditionalOutputAt_mono hTailBounded (Nat.le_max_right _ _)
  subst output
  refine ⟨Nat.pair stage headProgram.length, ?_⟩
  simp [chainPairSearchStep, chainPairSearchCandidate,
    chainPairHeadArguments, chainPairTailArguments, hProgramEq,
    hHeadAt, hTailAt]

/-- Partial search over all bounded fuel/split candidates. -/
def chainPairSearchAlgorithm (code : Nat.Partrec.Code)
    (program condition : BinString) : Part BinString :=
  Nat.rfindOpt fun rank =>
    chainPairSearchStep code ((program, condition), rank)

theorem chainPairSearchAlgorithm_partrec (code : Nat.Partrec.Code) :
    Partrec fun input : BinString × BinString =>
      chainPairSearchAlgorithm code input.1 input.2 := by
  exact Partrec.rfindOpt (chainPairSearchStep_primrec code).to_comp

theorem chainPairSearchAlgorithm_mem_iff
    {program condition output : BinString} :
    output ∈ chainPairSearchAlgorithm trimmedIndexedHostCode program condition ↔
      ChainPairRun trimmedIndexedHost program condition output := by
  constructor
  · intro hOutput
    obtain ⟨rank, hStep⟩ := Nat.rfindOpt_spec hOutput
    exact chainPairRun_of_searchStep (by simpa using hStep)
  · intro hRun
    obtain ⟨rank, hStep⟩ := exists_chainPairSearchStep_of_run hRun
    have hDom :
        (chainPairSearchAlgorithm trimmedIndexedHostCode program condition).Dom :=
      Nat.rfindOpt_dom.mpr ⟨rank, output, by simpa using hStep⟩
    let found :=
      (chainPairSearchAlgorithm trimmedIndexedHostCode program condition).get hDom
    have hFoundMem : found ∈
        chainPairSearchAlgorithm trimmedIndexedHostCode program condition :=
      Part.get_mem hDom
    obtain ⟨foundRank, hFoundStep⟩ := Nat.rfindOpt_spec hFoundMem
    have hFoundRun : ChainPairRun trimmedIndexedHost program condition found :=
      chainPairRun_of_searchStep (by simpa using hFoundStep)
    have hFoundEq : found = output :=
      chainPairRun_output_unique hFoundRun hRun
    simpa [hFoundEq] using hFoundMem

/-- Classical `Option` interface to the effective partial search. -/
noncomputable def effectiveChainPairCompute
    (program condition : BinString) : Option BinString :=
  (chainPairSearchAlgorithm trimmedIndexedHostCode program condition).toOption

theorem effectiveChainPairCompute_eq_some_iff
    {program condition output : BinString} :
    effectiveChainPairCompute program condition = some output ↔
      ChainPairRun trimmedIndexedHost program condition output := by
  rw [effectiveChainPairCompute, Part.toOption_eq_some_iff,
    chainPairSearchAlgorithm_mem_iff]

theorem effectiveChainPairCompute_eq_chainPairCompute
    (program condition : BinString) :
    effectiveChainPairCompute program condition =
      chainPairCompute trimmedIndexedHost program condition := by
  apply Option.ext
  intro output
  rw [effectiveChainPairCompute_eq_some_iff,
    chainPairCompute_eq_some_iff]

/-- Executable presentation of the constant-overhead concatenating pair
machine. -/
noncomputable def effectiveChainPairMachine : ConditionalPrefixFreeMachine where
  compute := effectiveChainPairCompute
  prefix_free := by
    intro condition program extension hPrefix hNe hHalts
    rw [effectiveChainPairCompute_eq_chainPairCompute] at hHalts
    rw [effectiveChainPairCompute_eq_chainPairCompute]
    exact (chainPairMachine trimmedIndexedHost).prefix_free condition program
      extension hPrefix hNe hHalts

theorem effectiveChainPairMachine_program
    {headProgram tailProgram condition head tail : BinString}
    (hHead : IsProgram trimmedIndexedHost headProgram condition head)
    (hTail : IsProgram trimmedIndexedHost tailProgram
      (chainCondition condition head headProgram.length) tail) :
    IsProgram effectiveChainPairMachine (headProgram ++ tailProgram) condition
      (pairCondition head tail) := by
  unfold IsProgram
  change effectiveChainPairCompute (headProgram ++ tailProgram) condition =
    some (pairCondition head tail)
  rw [effectiveChainPairCompute_eq_chainPairCompute]
  exact chainPairMachine_program hHead hTail

theorem effectiveChainPairCompute_partrec :
    Partrec fun input : BinString × BinString =>
      Part.ofOption (effectiveChainPairCompute input.1 input.2) := by
  exact chainPairSearchAlgorithm_partrec trimmedIndexedHostCode |>.of_eq
    fun input =>
      (Part.of_toOption
        (chainPairSearchAlgorithm trimmedIndexedHostCode input.1 input.2)).symm

theorem effectiveChainPairMachine_effective :
    Partrec₂ fun program condition =>
      Part.ofOption (effectiveChainPairMachine.compute program condition) := by
  exact effectiveChainPairCompute_partrec

/-- The concrete trimmed host compiles the effective pair machine with one
fixed prefix. -/
noncomputable def trimmedEffectiveChainPairSimulation :
    UniformlySimulates trimmedIndexedHost effectiveChainPairMachine :=
  Classical.choice (trimmedIndexedHost_simulates_effective _
    effectiveChainPairMachine_effective)

/-- The same compiler prefix simulates the extensional `chainPairMachine`
interface consumed by the generic upper-rule constructor. -/
noncomputable def trimmedChainPairSimulation :
    UniformlySimulates trimmedIndexedHost (chainPairMachine trimmedIndexedHost) where
  compilerPrefix := trimmedEffectiveChainPairSimulation.compilerPrefix
  compute_eq := by
    intro program condition
    rw [trimmedEffectiveChainPairSimulation.compute_eq]
    exact effectiveChainPairCompute_eq_chainPairCompute program condition

noncomputable def trimmedIndexedHostUpperConditionalChainRule :
    UpperConditionalChainRule trimmedIndexedHost :=
  UpperConditionalChainRule.ofPairSimulation trimmedChainPairSimulation

noncomputable def trimmedIndexedHostLowerConditionalChainRule :
    LowerConditionalChainRule trimmedIndexedHost :=
  lowerConditionalChainRuleOfPairRepresentability
    trimmedIndexedHostUpperConditionalChainRule.pair_hasProgram

noncomputable def trimmedIndexedHostStrongConditionalChainRule :
    StrongConditionalChainRule trimmedIndexedHost :=
  StrongConditionalChainRule.ofUpperLower
    trimmedIndexedHostUpperConditionalChainRule
    trimmedIndexedHostLowerConditionalChainRule

#print axioms chainPairSearchStep_primrec
#print axioms effectiveChainPairMachine_effective
#print axioms trimmedIndexedHostUpperConditionalChainRule
#print axioms trimmedIndexedHostLowerConditionalChainRule
#print axioms trimmedIndexedHostStrongConditionalChainRule

end KraftChaitin

end KolmogorovComplexity
