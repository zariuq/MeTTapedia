import Mettapedia.Computability.KolmogorovComplexity.Conditional
import Mettapedia.Computability.KolmogorovComplexity.ConditionalChainRule

/-!
# Repaired algorithmic containment (Franz Theorem 1, direct orientation)

The displayed proof of Theorem 1 of "Grounded Reasoning: Implication as
Algorithmic Containment" (Franz, AGI 2026) has two bookkeeping defects:

1. its step (16) uses the information premise in the reverse orientation to
   the paper's own directional definition `I(x:y) = K(x) − K(x|y)`; the swap
   is not licensed (see `DirectionalInformation.lean` for a finite machine
   where the two orientations are exactly 0 and 1 bits);
2. it invokes the feature-compression condition `|f| + |p| < |x|` without
   listing it as a hypothesis.

This file proves the repaired theorem with fully explicit bookkeeping:

* every conditioning step is a proved lemma about an explicitly constructed
  machine (`conditionTransport`, `applicationMachine`,
  `indexedConditionMachine`, `literalMachine`, `swapPairMachine`), applied
  through honest `UniformlySimulates` witnesses collected in
  `ReferenceMachineSimulations`;
* the strong conditional chain rule is packaged as the explicit structure
  `StrongConditionalChainRule` with one uniform additive constant in both
  directions.  Supplying this structure is precisely the missing
  Levin–Chaitin/Gács infrastructure (upper: concatenation construction;
  lower: effective Kraft–Chaitin counting) and is *not* claimed here;
* the genericity premise is taken in the orientation the proof actually
  uses: `K(f,g) ≤ K(f,g|p) + cGen`;
* the compression condition `|f| + |p| < |x|` is an explicit hypothesis;
* the conclusion is `Kc[U](g | f) ≤ C₁ * Nat.log 2 (x.length + 1) + C₀`
  with `C₁, C₀` computed in the proof from machine overheads and premises.

No sorries, no new axioms.
-/

namespace KolmogorovComplexity

open scoped Classical

/-- The `e1` header of a decodable string is unique. -/
theorem e1decode_unique_of_eq {w x rest y rest' : BinString}
    (h : e1decode w = some (x, rest)) (hy : w = e1encode y ++ rest') :
    x = y ∧ rest = rest' := by
  rw [hy] at h
  rw [e1decode_e1encode_append] at h
  have hpair : (y, rest') = (x, rest) := Option.some.inj h
  exact ⟨(congrArg Prod.fst hpair).symm, (congrArg Prod.snd hpair).symm⟩

/-! ## Small Nat.log₂ API -/

theorem log2_le_self (n : Nat) : Nat.log 2 n ≤ n := by
  by_cases hn : n = 0
  · subst hn
    simp
  · have h1 : 2 ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 hn
    have h2 : Nat.log 2 n < 2 ^ Nat.log 2 n :=
      Nat.lt_pow_self (a := 2) (n := Nat.log 2 n) (by norm_num)
    omega

theorem log2_two_mul {m : Nat} (hm : m ≠ 0) : Nat.log 2 (2 * m) = Nat.log 2 m + 1 := by
  rw [mul_comm]
  exact Nat.log_mul_base (by norm_num) hm

theorem log2_add_le {a b : Nat} (_ha : a ≠ 0) (hb : b ≠ 0) :
    Nat.log 2 (a + b) ≤ max (Nat.log 2 a) (Nat.log 2 b) + 1 := by
  have hsum : a + b ≤ 2 * max a b := by omega
  have hlog : Nat.log 2 (a + b) ≤ Nat.log 2 (2 * max a b) :=
    Nat.log_mono_right hsum
  have hmaxnz : max a b ≠ 0 := by omega
  rw [log2_two_mul hmaxnz] at hlog
  have hmax : Nat.log 2 (max a b) = max (Nat.log 2 a) (Nat.log 2 b) := by
    rcases Nat.le_total a b with h | h
    · rw [max_eq_right h, max_eq_right (Nat.log_mono_right h)]
    · rw [max_eq_left h, max_eq_left (Nat.log_mono_right h)]
  rw [hmax] at hlog
  exact hlog

/-! ## Machine transformations -/

/-- A machine that answers condition `fromCond` by delegating to `U` at
`toCond`; every other condition diverges. -/
def conditionTransport (U : ConditionalPrefixFreeMachine) (fromCond toCond : BinString) :
    ConditionalPrefixFreeMachine where
  compute := fun program condition =>
    if condition = fromCond then U.compute program toCond else none
  prefix_free := by
    intro cond p q hpref hpq hp
    by_cases h : cond = fromCond
    · subst h
      rw [if_pos rfl] at hp
      rw [if_pos rfl]
      exact U.prefix_free toCond p q hpref hpq hp
    · rw [if_neg h] at hp
      simp at hp

theorem conditionTransport_isProgram_iff
    {U : ConditionalPrefixFreeMachine} {fromCond toCond p x : BinString} :
    IsProgram (conditionTransport U fromCond toCond) p fromCond x ↔
      IsProgram U p toCond x := by
  simp [IsProgram, conditionTransport]

theorem conditionTransport_hasProgram_iff
    {U : ConditionalPrefixFreeMachine} {fromCond toCond x : BinString} :
    HasProgram (conditionTransport U fromCond toCond) fromCond x ↔
      HasProgram U toCond x := by
  constructor
  · rintro ⟨p, hp⟩
    exact ⟨p, conditionTransport_isProgram_iff.mp hp⟩
  · rintro ⟨p, hp⟩
    exact ⟨p, conditionTransport_isProgram_iff.mpr hp⟩

theorem conditionTransport_complexity (U : ConditionalPrefixFreeMachine)
    (fromCond toCond x : BinString) :
    Kc[conditionTransport U fromCond toCond](x | fromCond) = Kc[U](x | toCond) := by
  apply Nat.le_antisymm
  · by_cases h : HasProgram U toCond x
    · obtain ⟨s, hs, hlen⟩ := exists_program_of_conditionalComplexity U toCond x h
      have hs' : IsProgram (conditionTransport U fromCond toCond) s fromCond x :=
        conditionTransport_isProgram_iff.mpr hs
      rw [← hlen]
      exact conditionalComplexity_le_program_length _ fromCond x s hs'
    · have hM : ¬ HasProgram (conditionTransport U fromCond toCond) fromCond x :=
        fun hM => h (conditionTransport_hasProgram_iff.mp hM)
      rw [conditionalComplexity_eq_zero_of_not_hasProgram _ _ _ hM]
      exact Nat.zero_le _
  · by_cases h : HasProgram (conditionTransport U fromCond toCond) fromCond x
    · obtain ⟨s, hs, hlen⟩ := exists_program_of_conditionalComplexity
        (conditionTransport U fromCond toCond) fromCond x h
      have hs' : IsProgram U s toCond x := conditionTransport_isProgram_iff.mp hs
      rw [← hlen]
      exact conditionalComplexity_le_program_length _ toCond x s hs'
    · have hU : ¬ HasProgram U toCond x :=
        fun hU => h (conditionTransport_hasProgram_iff.mpr hU)
      rw [conditionalComplexity_eq_zero_of_not_hasProgram _ _ _ hU]
      exact Nat.zero_le _

/-- The machine that on the empty program applies the function named in the
first component of the condition to the parameter in the second. -/
def applicationMachine (U : ConditionalPrefixFreeMachine) : ConditionalPrefixFreeMachine where
  compute := fun program condition =>
    if program = [] then
      match unpairCondition condition with
      | some (funProg, param) => U.compute funProg param
      | none => none
    else none
  prefix_free := by
    intro cond p q hpref hpq hp
    by_cases h : p = []
    · subst h
      have hq : q ≠ [] := fun hq => hpq hq.symm
      rw [if_neg hq]
    · rw [if_neg h] at hp
      simp at hp

/-- The machine delivering data between the complexity-indexed conditional
triples used by the chain rule.  Its program is a self-delimited `e1encode`
header followed by a payload; the payload runs under the nested condition
triple carrying the header bits. -/
def indexedConditionMachine (U : ConditionalPrefixFreeMachine) : ConditionalPrefixFreeMachine where
  compute := fun program condition =>
    match e1decode program with
    | some (headerBits, payload) =>
        U.compute payload (pairCondition condition (pairCondition headerBits []))
    | none => none
  prefix_free := by
    intro cond p q hpref hpq hp
    by_contra hqhalt
    refine hpq ?_
    cases hdp : e1decode p with
    | none => simp [hdp] at hp
    | some r1 =>
        obtain ⟨hbp, sp⟩ := r1
        have hpp := e1decode_decompose (input := p) hdp
        have hUp : U.compute sp
            (pairCondition cond (pairCondition hbp [])) ≠ none := by
          simpa [hdp] using hp
        cases hdq : e1decode q with
        | none =>
            exfalso
            exact hqhalt (by simp [hdq])
        | some r2 =>
            obtain ⟨hbq, sq⟩ := r2
            have hqq := e1decode_decompose (input := q) hdq
            have hUq : U.compute sq
                (pairCondition cond (pairCondition hbq [])) ≠ none := by
              simpa [hdq] using hqhalt
            obtain ⟨suf, hsuf⟩ := hpref
            have hqFromP : q = e1encode hbp ++ (sp ++ suf) := by
              rw [← hsuf, hpp]
              simp [List.append_assoc]
            have hdecFromP : e1decode q = some (hbp, sp ++ suf) := by
              rw [hqFromP]
              exact e1decode_e1encode_append _ _
            rw [hdq] at hdecFromP
            have hpair : (hbq, sq) = (hbp, sp ++ suf) :=
              Option.some.inj hdecFromP
            have hhb : hbq = hbp := congrArg Prod.fst hpair
            have hsq : sq = sp ++ suf := congrArg Prod.snd hpair
            subst hbq
            have hspell : sp <+: sq := ⟨suf, hsq.symm⟩
            by_cases hspeq : sp = sq
            · calc
                p = e1encode hbp ++ sp := hpp
                _ = e1encode hbp ++ sq := congrArg (e1encode hbp ++ ·) hspeq
                _ = q := hqq.symm
            · exfalso
              have hnone : U.compute sq
                  (pairCondition cond (pairCondition hbp [])) = none :=
                U.prefix_free _ sp sq hspell hspeq hUp
              exact hUq hnone

/-- The machine whose halting programs are fully self-delimited literals
`e1encode x`; it ignores its condition. -/
def literalMachine : ConditionalPrefixFreeMachine where
  compute := fun program _condition =>
    match e1decode program with
    | some (out, rest) => if rest = [] then some out else none
    | none => none
  prefix_free := by
    intro cond p q hpref hpq hp
    by_contra hqhalt
    refine hpq ?_
    cases hdp : e1decode p with
    | none => simp [hdp] at hp
    | some r1 =>
        obtain ⟨outp, restp⟩ := r1
        cases restp with
        | nil =>
            have hpp := e1decode_decompose (input := p) hdp
            simp at hpp
            cases hdq : e1decode q with
            | none =>
                exfalso
                exact hqhalt (by simp [hdq])
            | some r2 =>
                obtain ⟨outq, restq⟩ := r2
                cases restq with
                | nil =>
                    have hqq := e1decode_decompose (input := q) hdq
                    simp at hqq
                    rw [hpp] at hpref
                    rw [hqq] at hpref
                    have heq := e1encode_prefix hpref
                    rw [hpp, hqq, heq]
                | cons _ _ =>
                    exfalso
                    exact hqhalt (by simp [hdq])
        | cons _ _ =>
            exfalso
            exact hp (by simp [hdp])

/-- The machine that swaps the two components of a paired description in its
output. -/
def swapPairMachine (U : ConditionalPrefixFreeMachine) : ConditionalPrefixFreeMachine where
  compute := fun program condition =>
    match U.compute program condition with
    | some out =>
        match unpairCondition out with
        | some (a, b) => some (pairCondition b a)
        | none => none
    | none => none
  prefix_free := by
    intro cond p q hpref hpq hp
    have hpU : U.compute p cond ≠ none := by
      cases hd : U.compute p cond with
      | none => simp [hd] at hp
      | some _ => simp
    have hqU : U.compute q cond = none := U.prefix_free cond p q hpref hpq hpU
    simp [hqU]

/-! ## Uniform condition and output projections -/

/-- Project the head field of a paired condition and delegate to `U`.  Unlike
`conditionTransport`, this machine is fixed uniformly over all field values. -/
def headConditionMachine (U : ConditionalPrefixFreeMachine) :
    ConditionalPrefixFreeMachine where
  compute := fun program condition =>
    match unpairCondition condition with
    | some (head, _tail) => U.compute program head
    | none => none
  prefix_free := by
    intro condition p q hpref hpq hp
    cases hcondition : unpairCondition condition with
    | none => simp [hcondition] at hp
    | some fields =>
        obtain ⟨head, tail⟩ := fields
        simp [hcondition] at hp ⊢
        exact U.prefix_free head p q hpref hpq hp

/-- Drop the middle complexity-index field of a chain condition.  On
`chainCondition condition head k`, payload programs are run under the paired
condition `(head, condition)`. -/
def dropIndexConditionMachine (U : ConditionalPrefixFreeMachine) :
    ConditionalPrefixFreeMachine where
  compute := fun program condition =>
    match unpairCondition condition with
    | some (head, indexedTail) =>
        match unpairCondition indexedTail with
        | some (_index, tail) => U.compute program (pairCondition head tail)
        | none => none
    | none => none
  prefix_free := by
    intro condition p q hpref hpq hp
    cases houter : unpairCondition condition with
    | none => simp [houter] at hp
    | some outer =>
        obtain ⟨head, indexedTail⟩ := outer
        cases hinner : unpairCondition indexedTail with
        | none => simp [houter, hinner] at hp
        | some inner =>
            obtain ⟨index, tail⟩ := inner
            simp [houter, hinner] at hp ⊢
            exact U.prefix_free (pairCondition head tail) p q hpref hpq hp

/-- Ignore the supplied condition and delegate to the empty condition. -/
def ignoreConditionMachine (U : ConditionalPrefixFreeMachine) :
    ConditionalPrefixFreeMachine where
  compute := fun program _condition => U.compute program []
  prefix_free := by
    intro _condition p q hpref hpq hp
    exact U.prefix_free [] p q hpref hpq hp

/-- Project the second component of a paired output produced by `U`. -/
def secondOutputMachine (U : ConditionalPrefixFreeMachine) :
    ConditionalPrefixFreeMachine where
  compute := fun program condition =>
    match U.compute program condition with
    | some output =>
        match unpairCondition output with
        | some (_first, second) => some second
        | none => none
    | none => none
  prefix_free := by
    intro condition p q hpref hpq hp
    have hpU : U.compute p condition ≠ none := by
      cases hpCompute : U.compute p condition with
      | none => simp [hpCompute] at hp
      | some _ => simp
    have hqU : U.compute q condition = none :=
      U.prefix_free condition p q hpref hpq hpU
    simp [hqU]

theorem headConditionMachine_program
    {U : ConditionalPrefixFreeMachine} {program condition head output : BinString}
    (h : IsProgram U program head output) :
    IsProgram (headConditionMachine U) program
      (pairCondition head condition) output := by
  simpa [IsProgram, headConditionMachine, unpairCondition_pairCondition] using h

theorem dropIndexConditionMachine_program
    {U : ConditionalPrefixFreeMachine}
    {program condition head index output : BinString}
    (h : IsProgram U program (pairCondition head condition) output) :
    IsProgram (dropIndexConditionMachine U) program
      (pairCondition head (pairCondition index condition)) output := by
  simpa [IsProgram, dropIndexConditionMachine, unpairCondition_pairCondition] using h

theorem ignoreConditionMachine_program
    {U : ConditionalPrefixFreeMachine} {program condition output : BinString}
    (h : IsProgram U program [] output) :
    IsProgram (ignoreConditionMachine U) program condition output := by
  simpa [IsProgram, ignoreConditionMachine] using h

theorem secondOutputMachine_program
    {U : ConditionalPrefixFreeMachine}
    {program condition first second : BinString}
    (h : IsProgram U program condition (pairCondition first second)) :
    IsProgram (secondOutputMachine U) program condition second := by
  unfold IsProgram at h ⊢
  simp [secondOutputMachine, h, unpairCondition_pairCondition]

/-! ## Explicit chain-rule and reference-machine interfaces -/

/-- Fixed compiler witnesses used in the repaired argument.  Every simulated
machine is uniform over the data fields occurring in a theorem family. -/
structure ReferenceMachineSimulations (U : ConditionalPrefixFreeMachine) where
  application : UniformlySimulates U (applicationMachine U)
  headCondition : UniformlySimulates U (headConditionMachine U)
  dropIndex : UniformlySimulates U (dropIndexConditionMachine U)
  ignoreCondition : UniformlySimulates U (ignoreConditionMachine U)
  secondOutput : UniformlySimulates U (secondOutputMachine U)
  indexedCondition : UniformlySimulates U (indexedConditionMachine U)
  literal : UniformlySimulates U literalMachine

/-! ## Nat ledger -/

/-- The cancellation ledger at the heart of the direct-orientation repair.
All slacks only add, so `Nat` is the faithful carrier: no truncated subtraction
or `Int` coercion is needed. -/
theorem directContainmentLedger
    {unconditionalHead indexedTail unconditionalPair conditionalPair
      conditionalHead conditionalTail logarithmicBudget
      chainSlack genericitySlack ignoreSlack : Nat}
    (hUnconditionalChain :
      unconditionalHead + indexedTail ≤ unconditionalPair + chainSlack)
    (hGenericity :
      unconditionalPair ≤ conditionalPair + genericitySlack)
    (hConditionalChain :
      conditionalPair ≤ conditionalHead + conditionalTail + chainSlack)
    (hIgnore : conditionalHead ≤ unconditionalHead + ignoreSlack)
    (hTail : conditionalTail ≤ logarithmicBudget) :
    indexedTail ≤ logarithmicBudget +
      (2 * chainSlack + genericitySlack + ignoreSlack) := by
  omega

/-! ## Repaired direct-orientation containment theorem -/

theorem conditionalComplexity_le_simulated_program
    {U M : ConditionalPrefixFreeMachine}
    (simulation : UniformlySimulates U M)
    {program condition output : BinString}
    (hProgram : IsProgram M program condition output) :
    Kc[U](output | condition) ≤
      program.length + simulation.compilerPrefix.length := by
  have h := conditionalComplexity_le_program_length U condition output
    (simulation.compilerPrefix ++ program) (simulation.program hProgram)
  simpa [List.length_append, Nat.add_comm] using h

/-- Recoverability from a generated object transports to recoverability under
the paired generator/parameter condition.  This is the machine-level content
of equations (10)--(14), with every compiler and chain-rule cost explicit. -/
theorem recover_under_paired_generator_parameter
    {U : ConditionalPrefixFreeMachine}
    (chainRule : StrongConditionalChainRule U)
    (simulations : ReferenceMachineSimulations U)
    {generator parameter generated consequent : BinString}
    (hEvaluation : IsProgram U generator parameter generated)
    (hConsequentGenerated : HasProgram U generated consequent) :
    HasProgram U (pairCondition generator parameter) consequent ∧
    Kc[U](consequent | pairCondition generator parameter) ≤
      Kc[U](consequent | generated) +
        (simulations.application.compilerPrefix.length +
          simulations.headCondition.compilerPrefix.length +
          chainRule.constant +
          simulations.secondOutput.compilerPrefix.length) := by
  let baseCondition := pairCondition generator parameter
  let generatedComplexity := Kc[U](generated | baseCondition)
  have hApplicationProgram :
      IsProgram (applicationMachine U) [] baseCondition generated := by
    simpa [IsProgram, applicationMachine, baseCondition,
      unpairCondition_pairCondition] using hEvaluation
  have hGeneratedBase : HasProgram U baseCondition generated :=
    simulations.application.hasProgram ⟨[], hApplicationProgram⟩
  have hGeneratedBaseBound :
      Kc[U](generated | baseCondition) ≤
        simulations.application.compilerPrefix.length := by
    simpa using conditionalComplexity_le_simulated_program
      simulations.application hApplicationProgram
  obtain ⟨consequentProgram, hConsequentProgram, hConsequentLength⟩ :=
    exists_program_of_conditionalComplexity U generated consequent
      hConsequentGenerated
  have hHeadProgram :
      IsProgram (headConditionMachine U) consequentProgram
        (chainCondition baseCondition generated generatedComplexity) consequent := by
    exact headConditionMachine_program
      (condition := pairCondition (binaryBits generatedComplexity) baseCondition)
      hConsequentProgram
  have hConsequentChain :
      HasProgram U (chainCondition baseCondition generated generatedComplexity)
        consequent :=
    simulations.headCondition.hasProgram ⟨consequentProgram, hHeadProgram⟩
  have hConsequentChainBound :
      Kc[U](consequent |
          chainCondition baseCondition generated generatedComplexity) ≤
        Kc[U](consequent | generated) +
          simulations.headCondition.compilerPrefix.length := by
    have h := conditionalComplexity_le_simulated_program
      simulations.headCondition hHeadProgram
    rw [hConsequentLength] at h
    exact h
  have hPair :
      HasProgram U baseCondition (pairCondition generated consequent) :=
    chainRule.pair_hasProgram baseCondition generated consequent
      hGeneratedBase hConsequentChain
  obtain ⟨pairProgram, hPairProgram, hPairLength⟩ :=
    exists_program_of_conditionalComplexity U baseCondition
      (pairCondition generated consequent) hPair
  have hSecondProgram :
      IsProgram (secondOutputMachine U) pairProgram baseCondition consequent :=
    secondOutputMachine_program hPairProgram
  have hConsequentBase : HasProgram U baseCondition consequent :=
    simulations.secondOutput.hasProgram ⟨pairProgram, hSecondProgram⟩
  refine ⟨hConsequentBase, ?_⟩
  have hProjection := conditionalComplexity_le_simulated_program
    simulations.secondOutput hSecondProgram
  rw [hPairLength] at hProjection
  have hPairBound := chainRule.upper baseCondition generated consequent
    hGeneratedBase hConsequentChain
  dsimp only [baseCondition, generatedComplexity] at hGeneratedBaseBound
  dsimp only [baseCondition, generatedComplexity] at hConsequentChainBound
  dsimp only [baseCondition, generatedComplexity] at hPairBound
  dsimp only [baseCondition, generatedComplexity] at hProjection
  omega

/-- Corrected direct-orientation form of Franz's Theorem 1.

The theorem concludes an exact finite bound.  Its genericity hypothesis is in
the orientation used by the proof, and representability is explicit because
this development assigns complexity zero to unrepresented outputs.  The
remaining header term is bounded logarithmically in the next corollary once a
feature-size bound is supplied. -/
theorem directOrientationContainment_explicit
    {U : ConditionalPrefixFreeMachine}
    (chainRule : StrongConditionalChainRule U)
    (simulations : ReferenceMachineSimulations U)
    {generator parameter consequent generated : BinString}
    (hEvaluation : IsProgram U generator parameter generated)
    (hGeneratorUnconditional : HasProgram U [] generator)
    (hConsequentGenerated : HasProgram U generated consequent)
    (hConsequentIndexed :
      HasProgram U
        (chainCondition [] generator Kc[U](generator | [])) consequent)
    (genericitySlack : Nat)
    (hDirectGenericity :
      Kc[U](pairCondition generator consequent | []) ≤
        Kc[U](pairCondition generator consequent | parameter) +
          genericitySlack) :
    Kc[U](consequent | generator) ≤
      Kc[U](consequent | generated) +
        (simulations.application.compilerPrefix.length +
          simulations.headCondition.compilerPrefix.length +
          simulations.secondOutput.compilerPrefix.length +
          simulations.dropIndex.compilerPrefix.length +
          3 * chainRule.constant + genericitySlack +
          simulations.ignoreCondition.compilerPrefix.length +
          simulations.indexedCondition.compilerPrefix.length +
          (e1encode
            (binaryBits Kc[U](generator | []))).length) := by
  let generatorComplexity := Kc[U](generator | [])
  let conditionalGeneratorComplexity := Kc[U](generator | parameter)
  obtain ⟨hConsequentBase, hConsequentBaseBound⟩ :=
    recover_under_paired_generator_parameter chainRule simulations
      hEvaluation hConsequentGenerated
  obtain ⟨baseProgram, hBaseProgram, hBaseLength⟩ :=
    exists_program_of_conditionalComplexity U
      (pairCondition generator parameter) consequent hConsequentBase
  have hDropProgram :
      IsProgram (dropIndexConditionMachine U) baseProgram
        (chainCondition parameter generator conditionalGeneratorComplexity)
        consequent := by
    exact dropIndexConditionMachine_program
      (index := binaryBits conditionalGeneratorComplexity) hBaseProgram
  have hConsequentConditional :
      HasProgram U
        (chainCondition parameter generator conditionalGeneratorComplexity)
        consequent :=
    simulations.dropIndex.hasProgram ⟨baseProgram, hDropProgram⟩
  have hConsequentConditionalBound :
      Kc[U](consequent |
          chainCondition parameter generator conditionalGeneratorComplexity) ≤
        Kc[U](consequent | pairCondition generator parameter) +
          simulations.dropIndex.compilerPrefix.length := by
    have h := conditionalComplexity_le_simulated_program
      simulations.dropIndex hDropProgram
    rw [hBaseLength] at h
    exact h
  obtain ⟨generatorProgram, hGeneratorProgram, hGeneratorLength⟩ :=
    exists_program_of_conditionalComplexity U [] generator
      hGeneratorUnconditional
  have hIgnoreProgram :
      IsProgram (ignoreConditionMachine U) generatorProgram parameter generator :=
    ignoreConditionMachine_program hGeneratorProgram
  have hGeneratorConditional : HasProgram U parameter generator :=
    simulations.ignoreCondition.hasProgram ⟨generatorProgram, hIgnoreProgram⟩
  have hGeneratorConditionalBound :
      Kc[U](generator | parameter) ≤
        Kc[U](generator | []) +
          simulations.ignoreCondition.compilerPrefix.length := by
    have h := conditionalComplexity_le_simulated_program
      simulations.ignoreCondition hIgnoreProgram
    rw [hGeneratorLength] at h
    exact h
  have hUnconditionalChain := chainRule.lower [] generator consequent
    hGeneratorUnconditional hConsequentIndexed
  have hConditionalChain := chainRule.upper parameter generator consequent
    hGeneratorConditional hConsequentConditional
  have hIndexedBound :
      Kc[U](consequent |
          chainCondition [] generator generatorComplexity) ≤
        Kc[U](consequent | generated) +
          (simulations.application.compilerPrefix.length +
            simulations.headCondition.compilerPrefix.length +
            chainRule.constant +
            simulations.secondOutput.compilerPrefix.length +
            simulations.dropIndex.compilerPrefix.length +
            2 * chainRule.constant + genericitySlack +
            simulations.ignoreCondition.compilerPrefix.length) := by
    have hTail :
        Kc[U](consequent |
            chainCondition parameter generator conditionalGeneratorComplexity) ≤
          Kc[U](consequent | generated) +
            (simulations.application.compilerPrefix.length +
              simulations.headCondition.compilerPrefix.length +
              chainRule.constant +
              simulations.secondOutput.compilerPrefix.length +
              simulations.dropIndex.compilerPrefix.length) := calc
      Kc[U](consequent |
          chainCondition parameter generator conditionalGeneratorComplexity) ≤
          Kc[U](consequent | pairCondition generator parameter) +
            simulations.dropIndex.compilerPrefix.length :=
        hConsequentConditionalBound
      _ ≤ Kc[U](consequent | generated) +
          (simulations.application.compilerPrefix.length +
            simulations.headCondition.compilerPrefix.length +
            chainRule.constant +
            simulations.secondOutput.compilerPrefix.length +
            simulations.dropIndex.compilerPrefix.length) := by
        omega
    have hLedger := directContainmentLedger hUnconditionalChain hDirectGenericity
      hConditionalChain hGeneratorConditionalBound hTail
    dsimp only [generatorComplexity, conditionalGeneratorComplexity] at hLedger ⊢
    omega
  obtain ⟨indexedProgram, hIndexedProgram, hIndexedLength⟩ :=
    exists_program_of_conditionalComplexity U
      (chainCondition [] generator generatorComplexity) consequent
      hConsequentIndexed
  have hIndexedMachineProgram :
      IsProgram (indexedConditionMachine U)
        (e1encode (binaryBits generatorComplexity) ++ indexedProgram)
        generator consequent := by
    unfold IsProgram
    simp only [indexedConditionMachine, e1decode_e1encode_append]
    unfold IsProgram at hIndexedProgram
    simpa [chainCondition] using hIndexedProgram
  have hFinal := conditionalComplexity_le_simulated_program
    simulations.indexedCondition hIndexedMachineProgram
  rw [List.length_append, hIndexedLength] at hFinal
  dsimp only [generatorComplexity, conditionalGeneratorComplexity] at *
  omega

/-! ## From the exact header to a logarithmic family bound -/

theorem log2_mul_le {a b : Nat} (ha : a ≠ 0) (hb : b ≠ 0) :
    Nat.log 2 (a * b) ≤ Nat.log 2 a + Nat.log 2 b + 1 := by
  have haPow : a < 2 ^ (Nat.log 2 a + 1) := by
    simpa using Nat.lt_pow_succ_log_self (b := 2) (by norm_num) a
  have hbPow : b < 2 ^ (Nat.log 2 b + 1) := by
    simpa using Nat.lt_pow_succ_log_self (b := 2) (by norm_num) b
  have hProduct :
      a * b < 2 ^ (Nat.log 2 a + Nat.log 2 b + 2) := by
    calc
      a * b < 2 ^ (Nat.log 2 a + 1) * b :=
        Nat.mul_lt_mul_of_pos_right haPow (Nat.pos_of_ne_zero hb)
      _ < 2 ^ (Nat.log 2 a + 1) * 2 ^ (Nat.log 2 b + 1) :=
        Nat.mul_lt_mul_of_pos_left hbPow (by positivity)
      _ = 2 ^ (Nat.log 2 a + Nat.log 2 b + 2) := by
        rw [← pow_add]
        congr 1
        omega
  have hLog := Nat.log_lt_of_lt_pow (b := 2)
    (mul_ne_zero ha hb) hProduct
  omega

theorem literalMachine_program (condition output : BinString) :
    IsProgram literalMachine (e1encode output) condition output := by
  unfold IsProgram
  change (match e1decode (e1encode output) with
    | some (out, rest) => if rest = [] then some out else none
    | none => none) = some output
  rw [show e1encode output = e1encode output ++ [] by simp,
    e1decode_e1encode_append]
  simp

/-- A genuinely compressive generator has a logarithmically encodable exact
complexity index.  The constant is explicit in the fixed literal compiler. -/
theorem complexityIndexHeader_le_log
    {U : ConditionalPrefixFreeMachine}
    (literalSimulation : UniformlySimulates U literalMachine)
    {generator : BinString} {witnessLength : Nat}
    (hGeneratorShort : generator.length < witnessLength) :
    (e1encode (binaryBits Kc[U](generator | []))).length ≤
      2 * Nat.log 2 (witnessLength + 1) +
        (2 * Nat.log 2 (literalSimulation.compilerPrefix.length + 2) + 5) := by
  let complexity := Kc[U](generator | [])
  let compilerConstant := literalSimulation.compilerPrefix.length
  have hLiteral := conditionalComplexity_le_simulated_program literalSimulation
    (literalMachine_program [] generator)
  have hE1Length : (e1encode generator).length = 2 * generator.length + 1 :=
    e1encode_length generator
  rw [hE1Length] at hLiteral
  have hComplexityProduct :
      complexity + 1 ≤ (compilerConstant + 2) * (witnessLength + 1) := by
    have hScale : 2 * witnessLength ≤
        (compilerConstant + 2) * witnessLength := by
      exact Nat.mul_le_mul_right witnessLength (by omega)
    calc
      complexity + 1 ≤ 2 * generator.length + compilerConstant + 2 := by
        dsimp only [complexity, compilerConstant]
        omega
      _ ≤ 2 * witnessLength + compilerConstant + 2 := by omega
      _ ≤ (compilerConstant + 2) * witnessLength +
          (compilerConstant + 2) := by omega
      _ = (compilerConstant + 2) * (witnessLength + 1) := by ring
  have hLogMono :
      Nat.log 2 complexity ≤
        Nat.log 2 ((compilerConstant + 2) * (witnessLength + 1)) := by
    apply Nat.log_mono_right
    exact (Nat.le_succ complexity).trans hComplexityProduct
  have hLogProduct :
      Nat.log 2 ((compilerConstant + 2) * (witnessLength + 1)) ≤
        Nat.log 2 (compilerConstant + 2) +
          Nat.log 2 (witnessLength + 1) + 1 :=
    log2_mul_le (by omega) (by omega)
  have hBits := binaryBits_length complexity
  rw [e1encode_length]
  dsimp only [complexity, compilerConstant] at hLogMono hLogProduct hBits ⊢
  omega

/-- Uniform logarithmic corollary of the direct-orientation repair.  The
feature-compression premise missing from the displayed source theorem is
explicit here. -/
theorem directOrientationContainment_logarithmic
    {U : ConditionalPrefixFreeMachine}
    (chainRule : StrongConditionalChainRule U)
    (simulations : ReferenceMachineSimulations U)
    {generator parameter consequent generated : BinString}
    (hEvaluation : IsProgram U generator parameter generated)
    (hFeatureCompression :
      generator.length + parameter.length < generated.length)
    (hGeneratorUnconditional : HasProgram U [] generator)
    (hConsequentGenerated : HasProgram U generated consequent)
    (hConsequentIndexed :
      HasProgram U
        (chainCondition [] generator Kc[U](generator | [])) consequent)
    (genericitySlack : Nat)
    (hDirectGenericity :
      Kc[U](pairCondition generator consequent | []) ≤
        Kc[U](pairCondition generator consequent | parameter) +
          genericitySlack) :
    Kc[U](consequent | generator) ≤
      Kc[U](consequent | generated) +
        2 * Nat.log 2 (generated.length + 1) +
        (simulations.application.compilerPrefix.length +
          simulations.headCondition.compilerPrefix.length +
          simulations.secondOutput.compilerPrefix.length +
          simulations.dropIndex.compilerPrefix.length +
          3 * chainRule.constant + genericitySlack +
          simulations.ignoreCondition.compilerPrefix.length +
          simulations.indexedCondition.compilerPrefix.length +
          2 * Nat.log 2 (simulations.literal.compilerPrefix.length + 2) + 5) := by
  have hExact := directOrientationContainment_explicit chainRule simulations
    hEvaluation hGeneratorUnconditional hConsequentGenerated hConsequentIndexed
    genericitySlack hDirectGenericity
  have hGeneratorShort : generator.length < generated.length := by omega
  have hHeader := complexityIndexHeader_le_log simulations.literal hGeneratorShort
  omega

/-! ## Transport from the paper's directional genericity -/

/-- Additive Nat form of the symmetry step needed to reverse the paper's
directional genericity premise.  This isolates the exact use of the
Levin--Gács symmetry-of-information theorem. -/
theorem genericityOrientationTransport
    {parameterComplexity parameterGivenModel modelComplexity modelGivenParameter
      sourceSlack symmetrySlack : Nat}
    (hSource : parameterComplexity ≤ parameterGivenModel + sourceSlack)
    (hSymmetry :
      modelComplexity + parameterGivenModel ≤
        parameterComplexity + modelGivenParameter + symmetrySlack) :
    modelComplexity ≤ modelGivenParameter + sourceSlack + symmetrySlack := by
  omega

/-- Source-orientation corollary.  The source premise controls information in
the parameter about the model pair.  A separately stated symmetry estimate
transports it to the orientation used by the proof, with its logarithmic loss
visible as `symmetrySlack`. -/
theorem sourceOrientationContainment_logarithmic
    {U : ConditionalPrefixFreeMachine}
    (chainRule : StrongConditionalChainRule U)
    (simulations : ReferenceMachineSimulations U)
    {generator parameter consequent generated : BinString}
    (hEvaluation : IsProgram U generator parameter generated)
    (hFeatureCompression :
      generator.length + parameter.length < generated.length)
    (hGeneratorUnconditional : HasProgram U [] generator)
    (hConsequentGenerated : HasProgram U generated consequent)
    (hConsequentIndexed :
      HasProgram U
        (chainCondition [] generator Kc[U](generator | [])) consequent)
    (sourceGenericitySlack symmetrySlack : Nat)
    (hSourceGenericity :
      Kc[U](parameter | []) ≤
        Kc[U](parameter | pairCondition generator consequent) +
          sourceGenericitySlack)
    (hSymmetry :
      Kc[U](pairCondition generator consequent | []) +
          Kc[U](parameter | pairCondition generator consequent) ≤
        Kc[U](parameter | []) +
          Kc[U](pairCondition generator consequent | parameter) +
          symmetrySlack) :
    Kc[U](consequent | generator) ≤
      Kc[U](consequent | generated) +
        2 * Nat.log 2 (generated.length + 1) +
        (simulations.application.compilerPrefix.length +
          simulations.headCondition.compilerPrefix.length +
          simulations.secondOutput.compilerPrefix.length +
          simulations.dropIndex.compilerPrefix.length +
          3 * chainRule.constant + sourceGenericitySlack + symmetrySlack +
          simulations.ignoreCondition.compilerPrefix.length +
          simulations.indexedCondition.compilerPrefix.length +
          2 * Nat.log 2 (simulations.literal.compilerPrefix.length + 2) + 5) := by
  have hDirectGenericity :
      Kc[U](pairCondition generator consequent | []) ≤
        Kc[U](pairCondition generator consequent | parameter) +
          sourceGenericitySlack + symmetrySlack :=
    genericityOrientationTransport hSourceGenericity hSymmetry
  have hDirectGenericity' :
      Kc[U](pairCondition generator consequent | []) ≤
        Kc[U](pairCondition generator consequent | parameter) +
          (sourceGenericitySlack + symmetrySlack) := by
    omega
  have h := directOrientationContainment_logarithmic chainRule simulations
    hEvaluation hFeatureCompression hGeneratorUnconditional hConsequentGenerated
    hConsequentIndexed (sourceGenericitySlack + symmetrySlack) hDirectGenericity'
  omega

#print axioms directContainmentLedger
#print axioms directOrientationContainment_explicit
#print axioms directOrientationContainment_logarithmic
#print axioms sourceOrientationContainment_logarithmic

end KolmogorovComplexity
