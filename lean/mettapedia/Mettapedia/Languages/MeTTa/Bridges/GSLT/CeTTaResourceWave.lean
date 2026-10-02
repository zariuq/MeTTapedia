import Mettapedia.GSLT.Causality.ResourceWaves
import Mettapedia.GSLT.LanguageDef.NativeOpsCNormalization
import Mettapedia.GSLT.LanguageDef.NativeOpsCFunctionComposition
import Mettapedia.GSLT.LanguageDef.NativeOpsScalarLowering
import Mettapedia.GSLT.LanguageDef.NativeOpsInstructionComposition
import Mettapedia.GSLT.LanguageDef.NativeOpsFiniteStorage
import Mettapedia.GSLT.LanguageDef.NativeOpsTargetParameterFacts
import Mathlib.Data.BitVec

/-!
# CeTTa resource-wave guard and the common native operation semantics

The complete ordinary C function is admitted by the shared lexer, parser and
immutable-parameter profile. Its guarded unsigned subtraction implements the
independent natural-number resource demand inequality. The boundary is the
sequential scalar profile; source identity, the selector loop, matching and
concurrent commit have separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaResourceWave

open Mettapedia.GSLT.LanguageDef.NativeOps
open NativeIR (Instruction)

def demandSource : List Char := "static inline bool resource_demand_fits(uint64_t available, uint64_t read,\n                                      uint64_t consumed, uint64_t added) {\n    if (read > available)\n        return false;\n    if (consumed > available - read)\n        return false;\n    return added <= available - read - consumed;\n}".toList

private def demandTokens : List NativeC.Token := [.identifier ['s', 't', 'a', 't', 'i', 'c'],
 .identifier ['i', 'n', 'l', 'i', 'n', 'e'],
 .identifier ['b', 'o', 'o', 'l'],
 .identifier ['r', 'e', 's', 'o', 'u', 'r', 'c', 'e', '_', 'd', 'e', 'm', 'a', 'n', 'd', '_', 'f', 'i', 't', 's'],
 .punctuation ['('],
 .identifier ['u', 'i', 'n', 't', '6', '4', '_', 't'],
 .identifier ['a', 'v', 'a', 'i', 'l', 'a', 'b', 'l', 'e'],
 .punctuation [','],
 .identifier ['u', 'i', 'n', 't', '6', '4', '_', 't'],
 .identifier ['r', 'e', 'a', 'd'],
 .punctuation [','],
 .identifier ['u', 'i', 'n', 't', '6', '4', '_', 't'],
 .identifier ['c', 'o', 'n', 's', 'u', 'm', 'e', 'd'],
 .punctuation [','],
 .identifier ['u', 'i', 'n', 't', '6', '4', '_', 't'],
 .identifier ['a', 'd', 'd', 'e', 'd'],
 .punctuation [')'],
 .punctuation ['{'],
 .identifier ['i', 'f'],
 .punctuation ['('],
 .identifier ['r', 'e', 'a', 'd'],
 .punctuation ['>'],
 .identifier ['a', 'v', 'a', 'i', 'l', 'a', 'b', 'l', 'e'],
 .punctuation [')'],
 .identifier ['r', 'e', 't', 'u', 'r', 'n'],
 .identifier ['f', 'a', 'l', 's', 'e'],
 .punctuation [';'],
 .identifier ['i', 'f'],
 .punctuation ['('],
 .identifier ['c', 'o', 'n', 's', 'u', 'm', 'e', 'd'],
 .punctuation ['>'],
 .identifier ['a', 'v', 'a', 'i', 'l', 'a', 'b', 'l', 'e'],
 .punctuation ['-'],
 .identifier ['r', 'e', 'a', 'd'],
 .punctuation [')'],
 .identifier ['r', 'e', 't', 'u', 'r', 'n'],
 .identifier ['f', 'a', 'l', 's', 'e'],
 .punctuation [';'],
 .identifier ['r', 'e', 't', 'u', 'r', 'n'],
 .identifier ['a', 'd', 'd', 'e', 'd'],
 .punctuation ['<', '='],
 .identifier ['a', 'v', 'a', 'i', 'l', 'a', 'b', 'l', 'e'],
 .punctuation ['-'],
 .identifier ['r', 'e', 'a', 'd'],
 .punctuation ['-'],
 .identifier ['c', 'o', 'n', 's', 'u', 'm', 'e', 'd'],
 .punctuation [';'],
 .punctuation ['}']]

private def demandStatements : List NativeC.CStatement :=
  [.branch (.binary .gt (.identifier "read".toList) (.identifier "available".toList))
     [.return (some (.bool false))] [],
   .branch (.binary .gt (.identifier "consumed".toList)
     (.binary .sub (.identifier "available".toList) (.identifier "read".toList)))
     [.return (some (.bool false))] [],
   .return (some (.binary .le (.identifier "added".toList)
     (.binary .sub
       (.binary .sub (.identifier "available".toList) (.identifier "read".toList))
       (.identifier "consumed".toList))))]

def demandHeader : Header :=
  ⟨"resource_demand_fits", [⟨"available", .word⟩, ⟨"read", .word⟩,
    ⟨"consumed", .word⟩, ⟨"added", .word⟩], .bool⟩

def demandCode : List Instruction :=
  [.temporary 1 .word (.readLocal "available"),
   .temporary 2 .word (.readLocal "read"),
   .temporary 3 .word (.readLocal "consumed"),
   .temporary 4 .word (.readLocal "added"),
   .temporary 5 .bool (.binary (.compare .gt) (.temporary 2 .word) (.temporary 1 .word)),
   .branch (.value (.temporary 5 .bool))
     [.temporary 6 .bool (.bool false), .return (.temporary 6 .bool)] [],
   .temporary 7 .word (.binary (.word .sub) (.temporary 1 .word) (.temporary 2 .word)),
   .temporary 8 .bool (.binary (.compare .gt) (.temporary 3 .word) (.temporary 7 .word)),
   .branch (.value (.temporary 8 .bool))
     [.temporary 9 .bool (.bool false), .return (.temporary 9 .bool)] [],
   .temporary 10 .word (.binary (.word .sub) (.temporary 1 .word) (.temporary 2 .word)),
   .temporary 11 .word (.binary (.word .sub) (.temporary 10 .word) (.temporary 3 .word)),
   .temporary 12 .bool (.binary (.compare .le) (.temporary 4 .word) (.temporary 11 .word)),
   .return (.temporary 12 .bool)]

def demandFunction : NativeIR.Function := ⟨demandHeader, demandCode, 12⟩

private def representation : NativeC.Representation := ⟨"CeTTaResourceWave", ⟨[], [], [], []⟩, []⟩

private def demandParsed : NativeC.CFunction :=
  ⟨⟨"bool".toList, 0⟩, "resource_demand_fits".toList,
    [⟨⟨"uint64_t".toList, 0⟩, "available".toList⟩,
     ⟨⟨"uint64_t".toList, 0⟩, "read".toList⟩,
     ⟨⟨"uint64_t".toList, 0⟩, "consumed".toList⟩,
     ⟨⟨"uint64_t".toList, 0⟩, "added".toList⟩], demandStatements⟩

private theorem demand_lexed : NativeC.lex demandSource = .ok demandTokens := by decide +kernel

private theorem demand_parsed : NativeC.function? (2 * demandTokens.length + 4)
    ["uint64_t".toList, "bool".toList] (NativeC.ordinaryFunctionTokens demandTokens) =
      some (demandParsed, []) := by rfl

/-- Whole-function admission checks the actual four-parameter prototype,
local linkage, inline spelling and every statement, with no omitted suffix. -/
theorem demand_function_source_admitted : NativeC.primitiveFunctionText? representation
    ["uint64_t".toList, "bool".toList] demandHeader [] demandSource = some demandFunction := by
  rw [NativeC.primitive_function_text_of_parts representation
    ["uint64_t".toList, "bool".toList] demandHeader [] demandSource demandTokens demandParsed
    demand_lexed demand_parsed]
  have normalized : NativeC.primitiveStatements?
      (NativeC.primitiveParameterBindings demandHeader.parameters ++ []) .bool
      (demandSource.length + 1) demandParsed.body ⟨demandHeader.parameters.length⟩ =
      some (demandCode.drop 4, ⟨12⟩) := by
    have length : demandSource.length + 1 = 308 := by decide +kernel
    rw [length]
    simp only [demandParsed, demandStatements, NativeC.primitiveStatements?,
      NativeC.primitiveStatement?, NativeC.primitiveExpression?]
    rfl
  have admitted := NativeC.primitive_function_of_parts representation demandHeader []
    (demandSource.length + 1) demandParsed .bool (demandCode.drop 4) ⟨12⟩
    (by rfl) (by decide +kernel) (by decide +kernel) normalized
  exact admitted

/-- This mirrors the admitted guarded unsigned operations, independently of
native memory, parameter binding and function execution. -/
def wordDemandFits {width : Nat} (available read consumed added : BitVec width) : Bool :=
  if read > available then false
  else if consumed > available - read then false
  else decide (added ≤ available - read - consumed)

/-- Guarded subtraction decides collective demand over natural numbers.
There is no modular addition in the independently stated specification. -/
theorem wordDemandFits_correspondence {width : Nat}
    (available read consumed added : BitVec width) :
    wordDemandFits available read consumed added =
      decide (read.toNat + consumed.toNat + added.toNat ≤ available.toNat) := by
  unfold wordDemandFits
  by_cases readTooLarge : read > available
  · have short : available.toNat < read.toNat := BitVec.lt_def.mp readTooLarge
    rw [if_pos readTooLarge]
    symm
    apply decide_eq_false
    omega
  · have readFits : read ≤ available := by
      rw [BitVec.le_def]
      have short : ¬ available.toNat < read.toNat := by
        simpa only [GT.gt, BitVec.lt_def] using readTooLarge
      omega
    have subtractRead : (available - read).toNat = available.toNat - read.toNat :=
      BitVec.toNat_sub_of_le readFits
    rw [if_neg readTooLarge]
    by_cases consumedTooLarge : consumed > available - read
    · have short : available.toNat - read.toNat < consumed.toNat := by
        rw [← subtractRead]
        exact BitVec.lt_def.mp consumedTooLarge
      rw [if_pos consumedTooLarge]
      symm
      apply decide_eq_false
      omega
    · have consumedFits : consumed ≤ available - read := by
        rw [BitVec.le_def]
        have short : ¬ (available - read).toNat < consumed.toNat := by
          simpa only [GT.gt, BitVec.lt_def] using consumedTooLarge
        omega
      have subtractConsumed : (available - read - consumed).toNat =
          available.toNat - read.toNat - consumed.toNat := by
        rw [BitVec.toNat_sub_of_le consumedFits, subtractRead]
      rw [if_neg consumedTooLarge]
      have fits := BitVec.le_def.mp readFits
      have consumedNatFits := BitVec.le_def.mp consumedFits
      rw [subtractRead] at consumedNatFits
      by_cases enough : read.toNat + consumed.toNat + added.toNat ≤ available.toNat
      · have addedFits : added ≤ available - read - consumed := by
          rw [BitVec.le_def, subtractConsumed]
          omega
        simp only [addedFits, enough, decide_true]
      · have addedDoesNotFit : ¬ added ≤ available - read - consumed := by
          rw [BitVec.le_def, subtractConsumed]
          omega
        simp only [addedDoesNotFit, enough, decide_false]

private def demandBound {World : Type} (state : TargetState World) (storage : Nat)
    (available read consumed added : BitVec 64) : TargetFrame × TargetState World :=
  let first := targetDeclareLocal (targetEmptyFrame storage) state "available" .word (.word available)
  let second := targetDeclareLocal first.1 first.2 "read" .word (.word read)
  let third := targetDeclareLocal second.1 second.2 "consumed" .word (.word consumed)
  targetDeclareLocal third.1 third.2 "added" .word (.word added)

private abbrev demandCaptured (base : TargetFrame)
    (available read consumed added : BitVec 64) : TargetFrame :=
  targetDeclareTemporary (targetDeclareTemporary (targetDeclareTemporary
    (targetDeclareTemporary base 1 (.word available)) 2 (.word read))
    3 (.word consumed)) 4 (.word added)

private abbrev demandFirstGuard (base : TargetFrame)
    (available read consumed added : BitVec 64) : TargetFrame :=
  targetDeclareTemporary (demandCaptured base available read consumed added)
    5 (.bool (decide (read > available)))

private abbrev demandSecondGuard (base : TargetFrame)
    (available read consumed added : BitVec 64) : TargetFrame :=
  targetDeclareTemporary
    (targetDeclareTemporary (demandFirstGuard base available read consumed added)
      7 (.word (available - read))) 8 (.bool (decide (consumed > available - read)))

private abbrev demandFinalFrame (base : TargetFrame)
    (available read consumed added : BitVec 64) : TargetFrame :=
  targetDeclareTemporary (targetDeclareTemporary
    (targetDeclareTemporary (demandSecondGuard base available read consumed added)
      10 (.word (available - read))) 11 (.word (available - read - consumed)))
    12 (.bool (decide (added ≤ available - read - consumed)))

private def demandOutcome {World : Type} (base : TargetFrame) (state : TargetState World)
    (available read consumed added : BitVec 64) : TargetBlockOutcome World :=
  if read > available then
    ⟨.returned (.bool false), demandFirstGuard base available read consumed added, state⟩
  else if consumed > available - read then
    ⟨.returned (.bool false), demandSecondGuard base available read consumed added, state⟩
  else
    ⟨.returned (.bool (decide (added ≤ available - read - consumed))),
      demandFinalFrame base available read consumed added, state⟩

private theorem demand_parameters_readback {World : Type} (state : TargetState World)
    (storage : Nat) (available read consumed added : BitVec 64) :
    let bound := demandBound state storage available read consumed added
    targetLocalValue bound.1 bound.2 "available" = some (.word available) ∧
    targetLocalValue bound.1 bound.2 "read" = some (.word read) ∧
    targetLocalValue bound.1 bound.2 "consumed" = some (.word consumed) ∧
    targetLocalValue bound.1 bound.2 "added" = some (.word added) := by
  simp [demandBound, targetDeclareLocal, targetEmptyFrame, targetLocalValue,
    targetLocalAddress, targetRead, targetStoreCell, targetReadPath]

private theorem demand_body_exact {World : Type} (interface : Interface)
    (heap : TargetHeapSemantics World) (calls : TargetCalls World)
    (state : TargetState World) (storage : Nat) (available read consumed added : BitVec 64)
    (root : List Instruction) (out : TargetBlockOutcome World) :
    let bound := demandBound state storage available read consumed added
    TargetRun interface heap calls .bool root demandCode bound.1 bound.2 out ↔
      out = demandOutcome bound.1 bound.2 available read consumed added := by
  let bound := demandBound state storage available read consumed added
  let captured := demandCaptured bound.1 available read consumed added
  let first := demandFirstGuard bound.1 available read consumed added
  let sub := targetDeclareTemporary first 7 (.word (available - read))
  let second := demandSecondGuard bound.1 available read consumed added
  obtain ⟨availableRead, readRead, consumedRead, addedRead⟩ :=
    demand_parameters_readback state storage available read consumed added
  change TargetRun interface heap calls .bool root demandCode bound.1 bound.2 out ↔ _
  unfold demandCode
  rw [target_normal_then_exact (target_temporary_instruction_exact
    (by rfl : bound.1.temporaryNames.contains 1 = false) (.local availableRead))]
  rw [target_normal_then_exact (target_temporary_instruction_exact
    (by rfl : (targetDeclareTemporary bound.1 1 (.word available)).temporaryNames.contains 2 = false)
    (.local readRead))]
  rw [target_normal_then_exact (target_temporary_instruction_exact
    (by rfl : (targetDeclareTemporary (targetDeclareTemporary bound.1 1 (.word available))
      2 (.word read)).temporaryNames.contains 3 = false) (.local consumedRead))]
  rw [target_normal_then_exact (target_temporary_instruction_exact
    (by rfl : (targetDeclareTemporary (targetDeclareTemporary
      (targetDeclareTemporary bound.1 1 (.word available)) 2 (.word read))
      3 (.word consumed)).temporaryNames.contains 4 = false) (.local addedRead))]
  have availableCaptured : TargetAtomEval interface captured bound.2
      (.temporary 1 .word) (.word available) :=
    .temporary (by simp [captured, targetDeclareTemporary]) (by rfl)
  have readCaptured : TargetAtomEval interface captured bound.2 (.temporary 2 .word) (.word read) :=
    .temporary (by simp [captured, targetDeclareTemporary]) (by rfl)
  have compared : TargetPureEval interface captured bound.2
      (.binary (.compare .gt) (.temporary 2 .word) (.temporary 1 .word))
      (.bool (decide (read > available))) := .binary readCaptured availableCaptured (by rfl)
  rw [target_normal_then_exact (target_temporary_instruction_exact
    (by rfl : captured.temporaryNames.contains 5 = false) compared)]
  have firstScoped : ∀ identity, first.temporaryNames.contains identity = false →
      first.temporaries identity = none := by
    apply declare_temporary_scoped
    apply declare_temporary_scoped
    apply declare_temporary_scoped
    apply declare_temporary_scoped
    apply declare_temporary_scoped
    intro identity _
    rfl
  have firstTest : TargetConditionEval interface first bound.2 (.value (.temporary 5 .bool))
      (decide (read > available)) :=
    .value (.temporary (declare_temporary_read _ _ _) (by rfl))
  rw [target_early_return_then_exact firstTest
    (by rfl : first.temporaryNames.contains 6 = false) (.bool false) firstScoped]
  by_cases readTooLarge : read > available
  · simp only [readTooLarge, decide_true, if_true, demandOutcome]
    rfl
  · simp only [readTooLarge, decide_false, Bool.false_eq_true, if_false, demandOutcome]
    have availableFirst : TargetAtomEval interface first bound.2
        (.temporary 1 .word) (.word available) :=
      .temporary (by simp [first, demandCaptured, targetDeclareTemporary]) (by rfl)
    have readFirst : TargetAtomEval interface first bound.2 (.temporary 2 .word) (.word read) :=
      .temporary (by simp [first, demandCaptured, targetDeclareTemporary]) (by rfl)
    rw [target_normal_then_exact (target_temporary_instruction_exact
      (by rfl : first.temporaryNames.contains 7 = false)
      (.binary availableFirst readFirst (by rfl)))]
    have consumedSub : TargetAtomEval interface sub bound.2
        (.temporary 3 .word) (.word consumed) :=
      .temporary (by simp [sub, first, demandCaptured, targetDeclareTemporary]) (by rfl)
    have subtraction : TargetAtomEval interface sub bound.2
        (.temporary 7 .word) (.word (available - read)) :=
      .temporary (declare_temporary_read _ _ _) (by rfl)
    have secondComparison : TargetPureEval interface sub bound.2
        (.binary (.compare .gt) (.temporary 3 .word) (.temporary 7 .word))
        (.bool (decide (consumed > available - read))) :=
      .binary consumedSub subtraction (by rfl)
    rw [target_normal_then_exact (target_temporary_instruction_exact
      (by rfl : sub.temporaryNames.contains 8 = false) secondComparison)]
    have secondScoped : ∀ identity, second.temporaryNames.contains identity = false →
        second.temporaries identity = none :=
      declare_temporary_scoped sub 8 _ (declare_temporary_scoped first 7 _ firstScoped)
    have secondTest : TargetConditionEval interface second bound.2 (.value (.temporary 8 .bool))
        (decide (consumed > available - read)) :=
      .value (.temporary (declare_temporary_read _ _ _) (by rfl))
    rw [target_early_return_then_exact secondTest
      (by rfl : second.temporaryNames.contains 9 = false) (.bool false) secondScoped]
    by_cases consumedTooLarge : consumed > available - read
    · simp only [consumedTooLarge, decide_true, if_true]
      rfl
    · simp only [consumedTooLarge, decide_false, Bool.false_eq_true, if_false]
      have availableSecond : TargetAtomEval interface second bound.2
          (.temporary 1 .word) (.word available) :=
        .temporary (by simp [second, demandFirstGuard,
          demandCaptured, targetDeclareTemporary]) (by rfl)
      have readSecond : TargetAtomEval interface second bound.2 (.temporary 2 .word) (.word read) :=
        .temporary (by simp [second, demandFirstGuard,
          demandCaptured, targetDeclareTemporary]) (by rfl)
      rw [target_normal_then_exact (target_temporary_instruction_exact
        (by rfl : second.temporaryNames.contains 10 = false)
        (.binary availableSecond readSecond (by rfl)))]
      let next := targetDeclareTemporary second 10 (.word (available - read))
      have subNext : TargetAtomEval interface next bound.2 (.temporary 10 .word)
          (.word (available - read)) :=
        .temporary (declare_temporary_read _ _ _) (by rfl)
      have consumedNext : TargetAtomEval interface next bound.2
          (.temporary 3 .word) (.word consumed) :=
        .temporary (by simp [next, second, demandFirstGuard,
          demandCaptured, targetDeclareTemporary]) (by rfl)
      rw [target_normal_then_exact (target_temporary_instruction_exact
        (by rfl : next.temporaryNames.contains 11 = false)
        (.binary subNext consumedNext (by rfl)))]
      let finalSub := targetDeclareTemporary next 11 (.word (available - read - consumed))
      have addedFinal : TargetAtomEval interface finalSub bound.2
          (.temporary 4 .word) (.word added) :=
        .temporary (by simp [finalSub, next, second, demandFirstGuard,
          demandCaptured, targetDeclareTemporary]) (by rfl)
      have subFinal : TargetAtomEval interface finalSub bound.2 (.temporary 11 .word)
          (.word (available - read - consumed)) :=
        .temporary (declare_temporary_read _ _ _) (by rfl)
      rw [target_normal_then_exact (target_temporary_instruction_exact
        (by rfl : finalSub.temporaryNames.contains 12 = false)
        (.binary addedFinal subFinal (by rfl)))]
      exact target_return_then_exact
        (.temporary (declare_temporary_read _ _ _) (by rfl)) _ _ _

private theorem demand_outcome_properties {World : Type} (base : TargetFrame)
    (state : TargetState World) (available read consumed added : BitVec 64) :
    let out := demandOutcome base state available read consumed added
    out.flow = .returned (.bool (wordDemandFits available read consumed added)) ∧
    out.frame.storage = base.storage ∧ out.frame.nextLocal = base.nextLocal ∧
    out.state = state := by
  have storageKept (frame : TargetFrame) (identity : Nat) (value : TargetValue) :
      (targetDeclareTemporary frame identity value).storage = frame.storage :=
    (declare_temporary_is_private frame identity value).1
  have firstLayout : (demandFirstGuard base available read consumed added).storage = base.storage ∧
      (demandFirstGuard base available read consumed added).nextLocal = base.nextLocal := by
    simp only [demandFirstGuard, demandCaptured, storageKept, target_temporary_next_local,
      and_self]
  have secondLayout : (demandSecondGuard base available read consumed added).storage = base.storage ∧
      (demandSecondGuard base available read consumed added).nextLocal = base.nextLocal := by
    simp only [demandSecondGuard, storageKept, target_temporary_next_local]
    trivial
  have finalLayout : (demandFinalFrame base available read consumed added).storage = base.storage ∧
      (demandFinalFrame base available read consumed added).nextLocal = base.nextLocal := by
    simp only [demandFinalFrame, storageKept, target_temporary_next_local]
    trivial
  by_cases readTooLarge : read > available
  · simp only [demandOutcome, wordDemandFits, if_pos readTooLarge]
    exact ⟨True.intro, firstLayout.1, firstLayout.2, True.intro⟩
  · simp only [demandOutcome, wordDemandFits, if_neg readTooLarge]
    by_cases consumedTooLarge : consumed > available - read
    · simp only [if_pos consumedTooLarge]
      exact ⟨True.intro, secondLayout.1, secondLayout.2, True.intro⟩
    · simp only [if_neg consumedTooLarge]
      exact ⟨True.intro, finalLayout.1, finalLayout.2, True.intro⟩

private def demandParameterMemory (memory : TargetMemory) (storage : Nat)
    (available read consumed added : BitVec 64) : TargetMemory :=
  targetParameterMemory memory storage 0
    [.word available, .word read, .word consumed, .word added]

private theorem demand_bound_state {World : Type} (state : TargetState World)
    (storage : Nat) (available read consumed added : BitVec 64) :
    (demandBound state storage available read consumed added).2 =
      { state with memory := demandParameterMemory state.memory storage available read consumed added } := rfl

private theorem demand_parameters_release (memory : TargetMemory) (storage : Nat)
    (available read consumed added : BitVec 64) (fresh : targetFreshFrame memory storage) :
    targetDropLocals (demandParameterMemory memory storage available read consumed added)
      storage 0 4 = memory := by
  exact target_parameter_memory_release memory storage
    [.word available, .word read, .word consumed, .word added] fresh

private theorem demand_function_teardown {World : Type} (state : TargetState World)
    (storage : Nat) (available read consumed added : BitVec 64)
    (fresh : targetFreshFrame state.memory storage) (out : TargetBlockOutcome World)
    (outExact : out = demandOutcome (demandBound state storage available read consumed added).1
      (demandBound state storage available read consumed added).2 available read consumed added) :
    (targetLeaveScope (targetEmptyFrame storage) out.frame out.state).2 = state := by
  let bound := demandBound state storage available read consumed added
  have properties := demand_outcome_properties bound.1 bound.2 available read consumed added
  have sameStorage : out.frame.storage = storage :=
    (congrArg (fun result => result.frame.storage) outExact).trans properties.2.1
  have sameExtent : out.frame.nextLocal = 4 :=
    (congrArg (fun result => result.frame.nextLocal) outExact).trans properties.2.2.1
  have stateExact : out.state =
      { state with memory := demandParameterMemory state.memory storage available read consumed added } :=
    ((congrArg TargetBlockOutcome.state outExact).trans properties.2.2.2).trans
      (demand_bound_state state storage available read consumed added)
  rw [stateExact]
  exact target_invocation_teardown state storage 4 out.frame
    (demandParameterMemory state.memory storage available read consumed added) state.memory
    sameStorage sameExtent (demand_parameters_release _ _ _ _ _ _ fresh)

/-- Complete invocation of the admitted C function returns the independent
natural-number admission decision and retains the entire caller state.
Fresh invocation storage is both necessary in the target calling convention
and sufficient; all four parameter cells are released on every return path. -/
theorem demand_function_exact {World : Type} (interface : Interface)
    (heap : TargetHeapSemantics World) (calls : TargetCalls World)
    (available read consumed added : BitVec 64) (state : TargetState World)
    (result : TargetRawResult World) :
    TargetFunctionBody interface heap calls demandFunction
      [.word available, .word read, .word consumed, .word added] state result ↔
      (∃ storage, targetFreshFrame state.memory storage) ∧
      result = ⟨.bool (decide (read.toNat + consumed.toNat + added.toNat ≤ available.toNat)), state⟩ := by
  constructor
  · intro ran
    cases ran with
    | @run storage frame bound out raw fresh parameters body returned =>
      have parameterPair : (frame, bound) = demandBound state storage available read consumed added :=
        (Option.some.inj parameters).symm
      have frameEq : frame = (demandBound state storage available read consumed added).1 :=
        congrArg Prod.fst parameterPair
      have stateEq : bound = (demandBound state storage available read consumed added).2 :=
        congrArg Prod.snd parameterPair
      subst frame
      subst bound
      have executed := (demand_body_exact interface heap calls state storage available read consumed
        added demandFunction.body out).mp body
      have properties := demand_outcome_properties
        (demandBound state storage available read consumed added).1
        (demandBound state storage available read consumed added).2 available read consumed added
      have valueExact : raw = .bool (wordDemandFits available read consumed added) :=
        TargetFlow.returned.inj
          (returned.symm.trans ((congrArg TargetBlockOutcome.flow executed).trans properties.1))
      rw [wordDemandFits_correspondence] at valueExact
      refine ⟨⟨storage, fresh⟩, ?_⟩
      rw [valueExact, demand_function_teardown state storage available read consumed added fresh out executed]
  · rintro ⟨⟨storage, fresh⟩, rfl⟩
    let bound := demandBound state storage available read consumed added
    let out := demandOutcome bound.1 bound.2 available read consumed added
    have properties := demand_outcome_properties bound.1 bound.2 available read consumed added
    have returned : out.flow =
        .returned (.bool (decide (read.toNat + consumed.toNat + added.toNat ≤ available.toNat))) := by
      rw [wordDemandFits_correspondence] at properties
      exact properties.1
    have executed : TargetFunctionBody interface heap calls demandFunction
        [.word available, .word read, .word consumed, .word added] state
        ⟨.bool (decide (read.toNat + consumed.toNat + added.toNat ≤ available.toNat)),
          (targetLeaveScope (targetEmptyFrame storage) out.frame out.state).2⟩ :=
      .run fresh (by rfl)
        ((demand_body_exact interface heap calls state storage available read consumed added
          demandFunction.body out).mpr rfl) returned
    rw [demand_function_teardown state storage available read consumed added fresh out rfl] at executed
    exact executed

/-- Finite caller storage supplies an actual invocation for every demand;
the interface's result is not assumed as an input to this existence law. -/
theorem demand_function_exists {World : Type} (interface : Interface)
    (heap : TargetHeapSemantics World) (calls : TargetCalls World)
    (available read consumed added : BitVec 64) (state : TargetState World)
    (finite : TargetFiniteStorage state.memory) :
    ∃ result, TargetFunctionBody interface heap calls demandFunction
      [.word available, .word read, .word consumed, .word added] state result := by
  exact ⟨_, (demand_function_exact interface heap calls available read consumed added state _).mpr
    ⟨target_finite_fresh finite, rfl⟩⟩

/-- Given exact count encodings, executing the actual guard once per
resource agrees with the common step contract. This theorem does not assume
that the C selector's resource table has already been proved to encode it. -/
theorem demand_function_checks_resource_step {R World : Type} [DecidableEq R]
    (system : Mettapedia.GSLT.Causality.ResourceInteraction.System R)
    (available : Multiset R) (reserved candidate : Multiset system.Entry)
    (supply reads consumed added : R → BitVec 64)
    (encoding : ∀ resource,
      (supply resource).toNat = available.count resource ∧
      (reads resource).toNat = max ((system.stepRead reserved).count resource)
        ((system.stepRead candidate).count resource) ∧
      (consumed resource).toNat = (system.stepConsume reserved).count resource ∧
      (added resource).toNat = (system.stepConsume candidate).count resource)
    (interface : Interface) (heap : TargetHeapSemantics World) (calls : TargetCalls World)
    (state : TargetState World) (finite : TargetFiniteStorage state.memory) :
    (∀ resource, TargetFunctionBody interface heap calls demandFunction
      [.word (supply resource), .word (reads resource), .word (consumed resource),
        .word (added resource)] state ⟨.bool true, state⟩) ↔
      system.StepEnables available (reserved + candidate) := by
  rw [system.stepEnables_add_iff_count]
  constructor
  · intro ran resource
    have returned := (demand_function_exact interface heap calls (supply resource)
      (reads resource) (consumed resource) (added resource) state _).mp (ran resource) |>.2
    have decision := TargetValue.bool.inj (congrArg TargetRawResult.value returned)
    obtain ⟨supplyExact, readExact, consumeExact, addExact⟩ := encoding resource
    rw [supplyExact, readExact, consumeExact, addExact] at decision
    exact of_decide_eq_true decision.symm
  · intro admitted resource
    apply (demand_function_exact interface heap calls (supply resource)
      (reads resource) (consumed resource) (added resource) state _).mpr
    refine ⟨target_finite_fresh finite, ?_⟩
    obtain ⟨supplyExact, readExact, consumeExact, addExact⟩ := encoding resource
    simp only [supplyExact, readExact, consumeExact, addExact, admitted resource, decide_true]

theorem demand_function_wrong_arity_refused {World : Type} (interface : Interface)
    (heap : TargetHeapSemantics World) (calls : TargetCalls World)
    (available read consumed : BitVec 64) (state : TargetState World)
    (result : TargetRawResult World) :
    ¬ TargetFunctionBody interface heap calls demandFunction
      [.word available, .word read, .word consumed] state result := by
  intro ran
  cases ran with
  | run _ parameters _ _ => cases parameters

theorem exact_resource_boundary_admitted :
    wordDemandFits (10 : BitVec 64) 4 5 1 = true := by decide +kernel

theorem excess_resource_boundary_refused :
    wordDemandFits (10 : BitVec 64) 4 5 2 = false := by decide +kernel

theorem full_width_read_is_admitted :
    wordDemandFits (BitVec.allOnes 64) (BitVec.allOnes 64) 0 0 = true := by decide +kernel

/-- Modular addition would falsely authorize this demand by wrapping to
zero. The admitted guard checks the independent natural-number sum. -/
theorem wrapping_read_consume_refused :
    wordDemandFits (BitVec.allOnes 64) (BitVec.allOnes 64) 1 0 = false := by decide +kernel

theorem read_underflow_refused :
    wordDemandFits (0 : BitVec 64) 1 0 0 = false := by decide +kernel

end Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaResourceWave
