import Mettapedia.Computability.KolmogorovComplexity.ContainmentRepair
import Mettapedia.Computability.KolmogorovComplexity.EffectiveConditionalChainRule

/-!
# Effective realization of repaired algorithmic containment

`ContainmentRepair` isolates the exact finite bookkeeping needed by the
direct-orientation containment result.  This file discharges its two machine
interfaces for the concrete effective indexed host:

* the strong conditional chain rule is supplied by the effective bounded
  search and Kraft--Chaitin construction;
* each fixed condition/output transformation used by the proof is shown
  partial recursive, hence receives a compiler prefix from indexed
  universality.

The resulting corollaries retain only the semantic hypotheses of the repaired
containment statement.  In particular, no unrestricted universal-machine
assumption is introduced.
-/

namespace KolmogorovComplexity

open scoped Classical

/-! ## Effective condition transformations -/

/-- The optional source arguments selected by `applicationMachine`. -/
def applicationMachineArguments
    (input : BinString × BinString) : Option (BinString × BinString) :=
  if input.1 = [] then unpairCondition input.2 else none

theorem applicationMachineArguments_primrec :
    Primrec applicationMachineArguments := by
  unfold applicationMachineArguments
  exact Primrec.ite
    (Primrec.eq.comp Primrec.fst (Primrec.const []))
    (KraftChaitin.unpairCondition_primrec.comp Primrec.snd)
    (Primrec.const none)

noncomputable def applicationMachineAlgorithm
    (U : ConditionalPrefixFreeMachine) (input : BinString × BinString) :
    Part BinString :=
  (Part.ofOption (applicationMachineArguments input)).bind fun arguments =>
    Part.ofOption (U.compute arguments.1 arguments.2)

theorem applicationMachine_effective
    (U : ConditionalPrefixFreeMachine)
    (hEffective : Partrec₂ fun program condition =>
      Part.ofOption (U.compute program condition)) :
    Partrec₂ fun program condition =>
      Part.ofOption ((applicationMachine U).compute program condition) := by
  unfold Partrec₂ at hEffective ⊢
  have hArguments : Partrec fun input : BinString × BinString =>
      Part.ofOption (applicationMachineArguments input) :=
    Computable.ofOption applicationMachineArguments_primrec.to_comp
  have hRun : Partrec₂ fun (_input : BinString × BinString)
      (arguments : BinString × BinString) =>
      Part.ofOption (U.compute arguments.1 arguments.2) := by
    exact hEffective.comp Computable.snd
  exact (hArguments.bind hRun).of_eq fun input => by
    unfold applicationMachineArguments
    by_cases hProgram : input.1 = []
    · rw [if_pos hProgram]
      cases hFields : unpairCondition input.2 with
      | none => simp [applicationMachine, hProgram, hFields, Part.ofOption]
      | some fields =>
          simp [applicationMachine, hProgram, hFields, Part.ofOption,
            Part.bind_some]
    · simp [applicationMachine, hProgram, Part.ofOption]

/-- Select the head field consumed by `headConditionMachine`. -/
def headConditionTarget (condition : BinString) : Option BinString :=
  (unpairCondition condition).map Prod.fst

theorem headConditionTarget_primrec : Primrec headConditionTarget := by
  unfold headConditionTarget
  exact Primrec.option_map KraftChaitin.unpairCondition_primrec
    (Primrec.fst.comp₂ Primrec₂.right)

noncomputable def headConditionMachineAlgorithm
    (U : ConditionalPrefixFreeMachine) (input : BinString × BinString) :
    Part BinString :=
  (Part.ofOption (headConditionTarget input.2)).bind fun target =>
    Part.ofOption (U.compute input.1 target)

theorem headConditionMachine_effective
    (U : ConditionalPrefixFreeMachine)
    (hEffective : Partrec₂ fun program condition =>
      Part.ofOption (U.compute program condition)) :
    Partrec₂ fun program condition =>
      Part.ofOption ((headConditionMachine U).compute program condition) := by
  unfold Partrec₂ at hEffective ⊢
  have hTarget : Partrec fun input : BinString × BinString =>
      Part.ofOption (headConditionTarget input.2) :=
    Computable.ofOption
      (headConditionTarget_primrec.to_comp.comp Computable.snd)
  have hRun : Partrec₂ fun (input : BinString × BinString)
      (target : BinString) => Part.ofOption (U.compute input.1 target) := by
    exact hEffective.comp (Computable.fst.comp Computable.fst |>.pair Computable.snd)
  exact (hTarget.bind hRun).of_eq fun input => by
    unfold headConditionTarget
    cases hFields : unpairCondition input.2 with
    | none => simp [headConditionMachine, hFields, Part.ofOption]
    | some fields =>
        simp [headConditionMachine, hFields, Part.ofOption, Part.bind_some]

/-- Remove the numeric middle field of a chain condition. -/
def dropIndexConditionTarget (condition : BinString) : Option BinString :=
  (unpairCondition condition).bind fun outer =>
    (unpairCondition outer.2).map fun inner =>
      pairCondition outer.1 inner.2

theorem dropIndexConditionTarget_primrec :
    Primrec dropIndexConditionTarget := by
  unfold dropIndexConditionTarget
  have hOuter : Primrec unpairCondition :=
    KraftChaitin.unpairCondition_primrec
  have hInner : Primrec fun outer : BinString × BinString =>
      unpairCondition outer.2 :=
    KraftChaitin.unpairCondition_primrec.comp Primrec.snd
  have hPair : Primrec₂ fun (outer : BinString × BinString)
      (inner : BinString × BinString) => pairCondition outer.1 inner.2 := by
    exact pairCondition_primrec.comp₂
      (Primrec.fst.comp₂ Primrec₂.left)
      (Primrec.snd.comp₂ Primrec₂.right)
  have hMapped : Primrec fun outer : BinString × BinString =>
      (unpairCondition outer.2).map fun inner =>
        pairCondition outer.1 inner.2 :=
    Primrec.option_map hInner hPair
  exact Primrec.option_bind hOuter
    (hMapped.comp₂ Primrec₂.right)

noncomputable def dropIndexConditionMachineAlgorithm
    (U : ConditionalPrefixFreeMachine) (input : BinString × BinString) :
    Part BinString :=
  (Part.ofOption (dropIndexConditionTarget input.2)).bind fun target =>
    Part.ofOption (U.compute input.1 target)

theorem dropIndexConditionMachine_effective
    (U : ConditionalPrefixFreeMachine)
    (hEffective : Partrec₂ fun program condition =>
      Part.ofOption (U.compute program condition)) :
    Partrec₂ fun program condition =>
      Part.ofOption ((dropIndexConditionMachine U).compute program condition) := by
  unfold Partrec₂ at hEffective ⊢
  have hTarget : Partrec fun input : BinString × BinString =>
      Part.ofOption (dropIndexConditionTarget input.2) :=
    Computable.ofOption
      (dropIndexConditionTarget_primrec.to_comp.comp Computable.snd)
  have hRun : Partrec₂ fun (input : BinString × BinString)
      (target : BinString) => Part.ofOption (U.compute input.1 target) := by
    exact hEffective.comp (Computable.fst.comp Computable.fst |>.pair Computable.snd)
  exact (hTarget.bind hRun).of_eq fun input => by
    unfold dropIndexConditionTarget
    cases hOuter : unpairCondition input.2 with
    | none => simp [dropIndexConditionMachine, hOuter, Part.ofOption]
    | some outer =>
        cases hInner : unpairCondition outer.2 with
        | none =>
            simp [dropIndexConditionMachine, hOuter, hInner, Part.ofOption]
        | some inner =>
            simp [dropIndexConditionMachine, hOuter, hInner, Part.ofOption,
              Part.bind_some]

theorem ignoreConditionMachine_effective
    (U : ConditionalPrefixFreeMachine)
    (hEffective : Partrec₂ fun program condition =>
      Part.ofOption (U.compute program condition)) :
    Partrec₂ fun program condition =>
      Part.ofOption ((ignoreConditionMachine U).compute program condition) := by
  unfold Partrec₂ at hEffective ⊢
  exact (hEffective.comp
    (Computable.fst.pair (Computable.const []))).of_eq fun _ => rfl

/-! ## Effective output and indexed-program transformations -/

theorem secondOutputMachine_effective
    (U : ConditionalPrefixFreeMachine)
    (hEffective : Partrec₂ fun program condition =>
      Part.ofOption (U.compute program condition)) :
    Partrec₂ fun program condition =>
      Part.ofOption ((secondOutputMachine U).compute program condition) := by
  unfold Partrec₂ at hEffective ⊢
  have hProjection : Primrec fun output : BinString =>
      (unpairCondition output).map Prod.snd := by
    exact Primrec.option_map KraftChaitin.unpairCondition_primrec
      (Primrec.snd.comp₂ Primrec₂.right)
  have hProjected : Partrec₂ fun (_input : BinString × BinString)
      (output : BinString) =>
      Part.ofOption ((unpairCondition output).map Prod.snd) := by
    exact (Computable.ofOption
      (hProjection.to_comp.comp Computable.snd)).to₂
  exact (hEffective.bind hProjected).of_eq fun input => by
    cases hCompute : U.compute input.1 input.2 with
    | none => simp [secondOutputMachine, hCompute, Part.ofOption]
    | some output =>
        cases hDecode : unpairCondition output with
        | none =>
            simp [secondOutputMachine, hCompute, hDecode, Part.ofOption,
              Part.bind_some]
        | some fields =>
            simp [secondOutputMachine, hCompute, hDecode, Part.ofOption,
              Part.bind_some]

/-- Decode an indexed payload and build the condition used by its source run. -/
def indexedConditionArguments
    (input : BinString × BinString) : Option (BinString × BinString) :=
  (e1decode input.1).map fun fields =>
    (fields.2, pairCondition input.2 (pairCondition fields.1 []))

theorem indexedConditionArguments_primrec :
    Primrec indexedConditionArguments := by
  unfold indexedConditionArguments
  have hDecode : Primrec fun input : BinString × BinString =>
      e1decode input.1 := e1decode_primrec.comp Primrec.fst
  have hArguments : Primrec₂ fun (input : BinString × BinString)
      (fields : BinString × BinString) =>
      (fields.2, pairCondition input.2 (pairCondition fields.1 [])) := by
    apply Primrec₂.mk
    have hInner : Primrec (fun context :
        (BinString × BinString) × (BinString × BinString) =>
        pairCondition context.2.1 []) :=
      pairCondition_primrec.comp
        (Primrec.fst.comp Primrec.snd)
        (Primrec.const ([] : BinString))
    have hCondition : Primrec (fun context :
        (BinString × BinString) × (BinString × BinString) =>
        pairCondition context.1.2
          (pairCondition context.2.1 [])) :=
      pairCondition_primrec.comp
        (Primrec.snd.comp Primrec.fst) hInner
    exact (Primrec.snd.comp Primrec.snd).pair hCondition
  exact Primrec.option_map hDecode hArguments

noncomputable def indexedConditionMachineAlgorithm
    (U : ConditionalPrefixFreeMachine) (input : BinString × BinString) :
    Part BinString :=
  (Part.ofOption (indexedConditionArguments input)).bind fun arguments =>
    Part.ofOption (U.compute arguments.1 arguments.2)

theorem indexedConditionMachine_effective
    (U : ConditionalPrefixFreeMachine)
    (hEffective : Partrec₂ fun program condition =>
      Part.ofOption (U.compute program condition)) :
    Partrec₂ fun program condition =>
      Part.ofOption ((indexedConditionMachine U).compute program condition) := by
  unfold Partrec₂ at hEffective ⊢
  have hArguments : Partrec fun input : BinString × BinString =>
      Part.ofOption (indexedConditionArguments input) :=
    Computable.ofOption indexedConditionArguments_primrec.to_comp
  have hRun : Partrec₂ fun (_input : BinString × BinString)
      (arguments : BinString × BinString) =>
      Part.ofOption (U.compute arguments.1 arguments.2) := by
    exact hEffective.comp Computable.snd
  exact (hArguments.bind hRun).of_eq fun input => by
    unfold indexedConditionArguments
    cases hDecode : e1decode input.1 with
    | none => simp [indexedConditionMachine, hDecode, Part.ofOption]
    | some fields =>
        simp [indexedConditionMachine, hDecode, Part.ofOption, Part.bind_some]

/-- Total decoder underlying `literalMachine`. -/
def literalMachineOutput (program : BinString) : Option BinString :=
  (e1decode program).bind fun fields =>
    if fields.2 = [] then some fields.1 else none

theorem literalMachineOutput_primrec : Primrec literalMachineOutput := by
  unfold literalMachineOutput
  have hBranch : Primrec₂ fun (_program : BinString)
      (fields : BinString × BinString) =>
      if fields.2 = [] then some fields.1 else none := by
    apply Primrec₂.mk
    exact Primrec.ite
      (Primrec.eq.comp (Primrec.snd.comp Primrec.snd) (Primrec.const []))
      (Primrec.option_some.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.const none)
  exact Primrec.option_bind e1decode_primrec hBranch

theorem literalMachine_effective :
    Partrec₂ fun program condition =>
      Part.ofOption (literalMachine.compute program condition) := by
  unfold Partrec₂
  exact (Computable.ofOption
    (literalMachineOutput_primrec.to_comp.comp Computable.fst)).of_eq
      fun input => by
        unfold literalMachineOutput
        cases hDecode : e1decode input.1 with
        | none => simp [literalMachine, hDecode]
        | some fields => simp [literalMachine, hDecode]

/-! ## Concrete simulation bundle and containment corollaries -/

noncomputable def trimmedReferenceMachineSimulations :
    ReferenceMachineSimulations trimmedIndexedHost where
  application := Classical.choice
    (trimmedIndexedHost_simulates_effective _
      (applicationMachine_effective _ trimmedIndexedHost_effective))
  headCondition := Classical.choice
    (trimmedIndexedHost_simulates_effective _
      (headConditionMachine_effective _ trimmedIndexedHost_effective))
  dropIndex := Classical.choice
    (trimmedIndexedHost_simulates_effective _
      (dropIndexConditionMachine_effective _ trimmedIndexedHost_effective))
  ignoreCondition := Classical.choice
    (trimmedIndexedHost_simulates_effective _
      (ignoreConditionMachine_effective _ trimmedIndexedHost_effective))
  secondOutput := Classical.choice
    (trimmedIndexedHost_simulates_effective _
      (secondOutputMachine_effective _ trimmedIndexedHost_effective))
  indexedCondition := Classical.choice
    (trimmedIndexedHost_simulates_effective _
      (indexedConditionMachine_effective _ trimmedIndexedHost_effective))
  literal := Classical.choice
    (trimmedIndexedHost_simulates_effective _ literalMachine_effective)

theorem trimmedDirectOrientationContainment_logarithmic
    {generator parameter consequent generated : BinString}
    (hEvaluation : IsProgram trimmedIndexedHost
      generator parameter generated)
    (hFeatureCompression :
      generator.length + parameter.length < generated.length)
    (hGeneratorUnconditional :
      HasProgram trimmedIndexedHost [] generator)
    (hConsequentGenerated :
      HasProgram trimmedIndexedHost generated consequent)
    (hConsequentIndexed :
      HasProgram trimmedIndexedHost
        (chainCondition [] generator
          Kc[trimmedIndexedHost](generator | [])) consequent)
    (genericitySlack : Nat)
    (hDirectGenericity :
      Kc[trimmedIndexedHost](pairCondition generator consequent | []) ≤
        Kc[trimmedIndexedHost](pairCondition generator consequent |
          parameter) + genericitySlack) :
    Kc[trimmedIndexedHost](consequent | generator) ≤
      Kc[trimmedIndexedHost](consequent | generated) +
        2 * Nat.log 2 (generated.length + 1) +
        (trimmedReferenceMachineSimulations.application.compilerPrefix.length +
          trimmedReferenceMachineSimulations.headCondition.compilerPrefix.length +
          trimmedReferenceMachineSimulations.secondOutput.compilerPrefix.length +
          trimmedReferenceMachineSimulations.dropIndex.compilerPrefix.length +
          3 * KraftChaitin.trimmedIndexedHostStrongConditionalChainRule.constant +
          genericitySlack +
          trimmedReferenceMachineSimulations.ignoreCondition.compilerPrefix.length +
          trimmedReferenceMachineSimulations.indexedCondition.compilerPrefix.length +
          2 * Nat.log 2
            (trimmedReferenceMachineSimulations.literal.compilerPrefix.length + 2) +
          5) := by
  exact directOrientationContainment_logarithmic
    KraftChaitin.trimmedIndexedHostStrongConditionalChainRule
    trimmedReferenceMachineSimulations hEvaluation hFeatureCompression
    hGeneratorUnconditional hConsequentGenerated hConsequentIndexed
    genericitySlack hDirectGenericity

theorem trimmedSourceOrientationContainment_logarithmic
    {generator parameter consequent generated : BinString}
    (hEvaluation : IsProgram trimmedIndexedHost
      generator parameter generated)
    (hFeatureCompression :
      generator.length + parameter.length < generated.length)
    (hGeneratorUnconditional :
      HasProgram trimmedIndexedHost [] generator)
    (hConsequentGenerated :
      HasProgram trimmedIndexedHost generated consequent)
    (hConsequentIndexed :
      HasProgram trimmedIndexedHost
        (chainCondition [] generator
          Kc[trimmedIndexedHost](generator | [])) consequent)
    (sourceGenericitySlack symmetrySlack : Nat)
    (hSourceGenericity :
      Kc[trimmedIndexedHost](parameter | []) ≤
        Kc[trimmedIndexedHost](parameter |
          pairCondition generator consequent) + sourceGenericitySlack)
    (hSymmetry :
      Kc[trimmedIndexedHost](pairCondition generator consequent | []) +
          Kc[trimmedIndexedHost](parameter |
            pairCondition generator consequent) ≤
        Kc[trimmedIndexedHost](parameter | []) +
          Kc[trimmedIndexedHost](pairCondition generator consequent |
            parameter) + symmetrySlack) :
    Kc[trimmedIndexedHost](consequent | generator) ≤
      Kc[trimmedIndexedHost](consequent | generated) +
        2 * Nat.log 2 (generated.length + 1) +
        (trimmedReferenceMachineSimulations.application.compilerPrefix.length +
          trimmedReferenceMachineSimulations.headCondition.compilerPrefix.length +
          trimmedReferenceMachineSimulations.secondOutput.compilerPrefix.length +
          trimmedReferenceMachineSimulations.dropIndex.compilerPrefix.length +
          3 * KraftChaitin.trimmedIndexedHostStrongConditionalChainRule.constant +
          sourceGenericitySlack + symmetrySlack +
          trimmedReferenceMachineSimulations.ignoreCondition.compilerPrefix.length +
          trimmedReferenceMachineSimulations.indexedCondition.compilerPrefix.length +
          2 * Nat.log 2
            (trimmedReferenceMachineSimulations.literal.compilerPrefix.length + 2) +
          5) := by
  exact sourceOrientationContainment_logarithmic
    KraftChaitin.trimmedIndexedHostStrongConditionalChainRule
    trimmedReferenceMachineSimulations hEvaluation hFeatureCompression
    hGeneratorUnconditional hConsequentGenerated hConsequentIndexed
    sourceGenericitySlack symmetrySlack hSourceGenericity hSymmetry

#print axioms applicationMachine_effective
#print axioms indexedConditionMachine_effective
#print axioms trimmedReferenceMachineSimulations
#print axioms trimmedDirectOrientationContainment_logarithmic
#print axioms trimmedSourceOrientationContainment_logarithmic

end KolmogorovComplexity
