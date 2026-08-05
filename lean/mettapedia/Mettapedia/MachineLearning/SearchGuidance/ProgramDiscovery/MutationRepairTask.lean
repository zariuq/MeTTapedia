import Mettapedia.GSLT.LanguageDef.Gauthier.Adjudications33

/-!
# Definition-guided OEIS repair tasks

A repair task starts from a parser-authenticated one-token mutation, contains a
kernel-checked counterexample against a pinned OEIS specification, and ends at
a frozen candidate with an extensional correctness proof.  The specification
also serves as an executable source of arbitrarily many reference terms.
-/

namespace Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery.OEISDefinitionRepair

open Mettapedia.GSLT.LanguageDef.GauthierAdjudications33
open Mettapedia.GSLT.LanguageDef.GauthierE2
open Mettapedia.GSLT.LanguageDef.GauthierE2ScalarSemantics
open Mettapedia.GSLT.LanguageDef.GauthierFrozenCandidates49
open Mettapedia.GSLT.LanguageDef.GauthierOEISSequenceSemantics
open Mettapedia.Sequences.OEIS
open Mettapedia.Sequences.OEIS.Elementary49

/-- An exact, position-preserving one-token edit. -/
structure OneTokenMutation (original mutated : List Nat) where
  leading : List Nat
  beforeToken : Nat
  afterToken : Nat
  trailing : List Nat
  changed : beforeToken ≠ afterToken
  original_eq : original = leading ++ (beforeToken :: trailing)
  mutated_eq : mutated = leading ++ (afterToken :: trailing)

/-- A complete repair obligation with both negative and positive certificates. -/
structure DefinitionGuidedRepairTask where
  formalization : Formalization
  broken : FrozenCandidate
  repaired : FrozenCandidate
  mutation : OneTokenMutation repaired.tokens broken.tokens
  counterexample : Counterexample formalization.spec broken.program
  repairedCorrect : CandidateRealizes formalization.spec repaired

def referencePrefix (task : DefinitionGuidedRepairTask) (length : Nat) : List Int :=
  (List.range length).map
    (fun position => task.formalization.spec.value
      (task.formalization.spec.index position))

theorem referencePrefix_length (task : DefinitionGuidedRepairTask) (length : Nat) :
    (referencePrefix task length).length = length := by
  simp [referencePrefix]

theorem broken_is_refuted (task : DefinitionGuidedRepairTask) :
    ¬ CandidateRealizes task.formalization.spec task.broken :=
  task.counterexample.not_realizes

theorem repaired_is_correct (task : DefinitionGuidedRepairTask) :
    CandidateRealizes task.formalization.spec task.repaired :=
  task.repairedCorrect

/-! ## A002063: mutate the inner-loop initial value from three to two -/

def A002063_broken : FrozenCandidate where
  programSha256 := "83305428d26b5c5f7124a47a9c1241c6813e50f1a11f630c39154b147252cedd"
  tokens := [10, 10, 5, 1, 10, 10, 3, 10, 0, 2, 3, 9, 9]
  program :=
    P.loop (P.mult P.X P.X) P.o
      (P.loop (P.addi P.X P.X) P.X (P.addi P.z P.tw))
  recognized := rfl

theorem A002063_mutation_at_zero :
    ScalarEval A002063_broken.program 0 0 4 := by
  have innerInitial := scalar_addi (scalar_zero 0 0) (scalar_two 0 0)
  have innerRaw := scalar_loop (x := 0) (y := 0)
    (fun accumulator _ => accumulator + accumulator)
    (scalar_x 0 0) innerInitial
    (fun accumulator counter =>
      scalar_addi (scalar_x accumulator counter) (scalar_x accumulator counter))
  have inner : ScalarEval
      (P.loop (P.addi P.X P.X) P.X (P.addi P.z P.tw)) 0 0 2 := by
    simpa [iterateWithCounter] using innerRaw
  have outerRaw := scalar_loop (x := 0) (y := 0)
    (fun accumulator _ => accumulator * accumulator)
    (scalar_one 0 0) inner
    (fun accumulator counter =>
      scalar_mult (scalar_x accumulator counter) (scalar_x accumulator counter))
  simpa [A002063_broken, iterateWithCounter] using outerRaw

def A002063_counterexample :
    Counterexample A002063.spec A002063_broken.program where
  probe :=
    { position := 0
      indexInDomain := by
        simp [A002063.spec, specOf, SequenceSpec.index] }
  actual := 4
  actualResult := emits_implies_eventuallyEmits (scalarEval_emits A002063_mutation_at_zero)
  differs := by
    norm_num [Probe.expected, A002063.spec, specOf, SequenceSpec.index]

def A002063_mutation : OneTokenMutation candidate00.tokens A002063_broken.tokens where
  leading := [10, 10, 5, 1, 10, 10, 3, 10]
  beforeToken := 1
  afterToken := 0
  trailing := [2, 3, 9, 9]
  changed := by decide
  original_eq := rfl
  mutated_eq := rfl

def A002063_repairTask : DefinitionGuidedRepairTask where
  formalization := A002063.formalization
  broken := A002063_broken
  repaired := candidate00
  mutation := A002063_mutation
  counterexample := A002063_counterexample
  repairedCorrect := A002063_candidate00_correct

def repairBenchmarkSeed : List DefinitionGuidedRepairTask :=
  [A002063_repairTask]

theorem repairBenchmarkSeed_count : repairBenchmarkSeed.length = 1 := by
  rfl

theorem A002063_referencePrefix_eight :
    referencePrefix A002063_repairTask 8 =
      [9, 36, 144, 576, 2304, 9216, 36864, 147456] := by
  decide

#print axioms referencePrefix_length
#print axioms broken_is_refuted
#print axioms repaired_is_correct
#print axioms A002063_mutation_at_zero
#print axioms A002063_counterexample
#print axioms A002063_repairTask
#print axioms A002063_referencePrefix_eight

end Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery.OEISDefinitionRepair
