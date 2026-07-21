import Mathlib.Tactic
import Mettapedia.GSLT.LanguageDef.Gauthier.E2ListSemantics
import Mettapedia.Sequences.OEIS.HofstadterConway
import Mettapedia.Sequences.OEIS.Kolakoski
import Mettapedia.Sequences.OEIS.CyclotomicSieve

/-!
# Reported sequence programs

This module authenticates and studies program transcriptions reported in the
integer-sequence synthesis work of Thibault Gauthier, Miroslav Olšák, and
Josef Urban.  The digests below authenticate these transcriptions; they do not
claim byte identity with an unavailable original artifact.
-/

namespace Mettapedia.GSLT.LanguageDef.GauthierReportedSequencePrograms

open Mettapedia.GSLT.LanguageDef.GauthierE2
open Mettapedia.GSLT.LanguageDef.GauthierE2ListSemantics
open Mettapedia.GSLT.LanguageDef.GauthierOEISSequenceSemantics
open Mettapedia.Sequences.OEIS
open Mettapedia.Sequences.OEIS.HofstadterConway

/-- Reported program for OEIS A004001. -/
def reportedA004001 : FrozenCandidate where
  programSha256 := "7520be9f41f5ef978fb00080a0130143616cadef82c39163b08276a081e5f23b"
  tokens := [10, 15, 11, 10, 4, 10, 15, 9, 10, 14, 10, 15, 10, 1, 4,
    10, 9, 3, 10, 1, 4, 1, 9]
  program := P.loop
    (P.addi
      (P.push (P.loop (P.pop P.X) (P.diff P.Y P.X) (P.pop P.X)) P.X)
      (P.loop (P.pop P.X) (P.diff P.X P.o) P.X))
    (P.diff P.X P.o) P.o
  recognized := rfl

/-- Reported program for OEIS A004074. -/
def reportedA004074 : FrozenCandidate where
  programSha256 := "5d0a2d05c698935364899e73b16259ecc7c12a6319bd5a0fbc497ed6f3b90c51"
  tokens := [2, 10, 15, 10, 1, 4, 10, 9, 10, 14, 10, 15, 11, 10, 4,
    10, 15, 9, 3, 10, 1, 4, 1, 9, 5, 1, 4, 10, 4]
  program := P.diff
    (P.diff
      (P.mult P.tw
        (P.loop
          (P.addi
            (P.push (P.loop (P.pop P.X) (P.diff P.X P.o) P.X) P.X)
            (P.loop (P.pop P.X) (P.diff P.Y P.X) (P.pop P.X)))
          (P.diff P.X P.o) P.o))
      P.o)
    P.X
  recognized := rfl

/-- Reported program for the Kolakoski sequence, OEIS A000002. -/
def reportedA000002 : FrozenCandidate where
  programSha256 := "b6765feccadb491981a6a8a087ac78ebe98071e6b25f002f10364a7576b6ac6c"
  tokens := [1, 10, 15, 10, 2, 6, 10, 9, 10, 10, 15, 3, 2, 7, 14, 10,
    3, 10, 1, 0, 14, 9, 15, 3]
  program := P.addi P.o
    (P.pop
      (P.loop
        (P.addi
          (P.push
            (P.loop (P.pop P.X) (P.divi P.X P.tw) P.X)
            (P.modu (P.addi P.X (P.pop P.X)) P.tw))
          P.X)
        P.X
        (P.push P.o P.z)))
  recognized := rfl

/-- Reported program for the cyclotomic-value sequence, OEIS A070526. -/
def reportedA070526 : FrozenCandidate where
  programSha256 := "fee6555f282bf4b068dfdc305e404b04b72698a754aa4daed754ed1aaf7e8717"
  tokens := [10, 11, 7, 10, 11, 6, 10, 8, 11, 15, 11, 1, 10, 10, 3, 3,
    11, 1, 9, 10, 14, 10, 13, 2, 10, 3, 10, 5, 1, 9]
  program := P.loop
    (P.loop2
      (P.cond (P.modu P.X P.Y) (P.divi P.X P.Y) P.X)
      (P.pop P.Y)
      P.Y
      (P.push (P.loop (P.addi P.o (P.addi P.X P.X)) P.Y P.o) P.X)
      P.X)
    (P.mult (P.addi P.tw P.X) P.X)
    P.o
  recognized := rfl

/-- Reverse chronological history `[a(k+1), ..., a(2)]`. -/
def conwayHistory : Nat → List Int
  | 0 => []
  | k + 1 => Int.ofNat (value (k + 2)) :: conwayHistory k

@[simp] theorem conwayHistory_length (k : Nat) :
    (conwayHistory k).length = k := by
  induction k with
  | zero => rfl
  | succ k inductionHypothesis =>
      simp [conwayHistory, inductionHypothesis]

theorem conwayHistory_nonempty {k : Nat} (positive : 1 ≤ k) :
    conwayHistory k ≠ [] := by
  intro empty
  have := congrArg List.length empty
  simp at this
  omega

theorem conwayHistory_drop : ∀ {k drop : Nat}, drop ≤ k →
    (conwayHistory k).drop drop = conwayHistory (k - drop) := by
  intro k drop bound
  induction drop generalizing k with
  | zero => simp
  | succ drop inductionHypothesis =>
      cases k with
      | zero => omega
      | succ k =>
          simp only [conwayHistory, List.drop_succ_cons]
          rw [inductionHypothesis (by omega)]
          rw [Nat.succ_sub_succ_eq_sub]

@[simp] theorem conwayHistory_head (k : Nat) :
    (conwayHistory (k + 1)).head? = some (Int.ofNat (value (k + 2))) := by
  simp [conwayHistory]

theorem conwayHistory_eq_cons {k : Nat} (positive : 1 ≤ k) :
    conwayHistory k =
      Int.ofNat (value (k + 1)) :: conwayHistory (k - 1) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  simp [conwayHistory]

theorem stickyDrop_conwayHistory_length {k : Nat} (positive : 1 ≤ k) :
    stickyDrop k (conwayHistory k) = [1] := by
  induction k with
  | zero => omega
  | succ k inductionHypothesis =>
      cases k with
      | zero => simp [conwayHistory, value_two]
      | succ k =>
          simp only [conwayHistory, stickyDrop]
          exact inductionHypothesis (by omega)

private def firstLookup : GauthierE2ListSemantics.Program :=
  P.loop (P.pop P.X) (P.diff P.Y P.X) (P.pop P.X)

private def secondLookup : GauthierE2ListSemantics.Program :=
  P.loop (P.pop P.X) (P.diff P.X P.o) P.X

private def conwayBody : GauthierE2ListSemantics.Program :=
  P.addi (P.push firstLookup P.X) secondLookup

private def conwayBodySwapped : GauthierE2ListSemantics.Program :=
  P.addi (P.push secondLookup P.X) firstLookup

private theorem firstLookup_eval (k : Nat) (positive : 1 ≤ k) :
    ∃ tail, ListEval firstLookup (conwayHistory k) [Int.ofNat k]
      (Int.ofNat (value (value (k + 1))) :: tail) := by
  let previous := value (k + 1)
  have previousPositive : 1 ≤ previous := value_positive _
  have previousUpper : previous ≤ k := by
    simpa [previous] using value_le_pred (k + 1) (by omega)
  have historyShape := conwayHistory_eq_cons positive
  have xResult : ListEval P.X (conwayHistory k) [Int.ofNat k]
      (Int.ofNat previous :: conwayHistory (k - 1)) := by
    simpa [previous, historyShape] using
      (list_x (conwayHistory k) [Int.ofNat k])
  have countRaw := list_diff
    (list_y (conwayHistory k) [Int.ofNat k])
    xResult
  have countResult : ListEval (P.diff P.Y P.X)
      (conwayHistory k) [Int.ofNat k] [Int.ofNat (k - previous)] := by
    simpa [previous, Int.ofNat_sub previousUpper] using countRaw
  have initialResult : ListEval (P.pop P.X)
      (conwayHistory k) [Int.ofNat k] (stickyDrop 1 (conwayHistory k)) :=
    list_pop_x (conwayHistory_nonempty positive)
  have initialNonempty : stickyDrop 1 (conwayHistory k) ≠ [] :=
    stickyDrop_nonempty (conwayHistory_nonempty positive)
  have execution := pop_iterates (iterations := k - previous)
    (counter := 1) initialNonempty
  have loopResult := list_loop countResult initialResult execution
  have combinedDrop :
      stickyDrop (k - previous) (stickyDrop 1 (conwayHistory k)) =
        stickyDrop (k - previous + 1) (conwayHistory k) :=
    stickyDrop_add (k - previous) 1 (conwayHistory k)
  by_cases previousOne : previous = 1
  · have finalAtEnd : k - previous + 1 = k := by omega
    refine ⟨[], ?_⟩
    rw [combinedDrop, finalAtEnd, stickyDrop_conwayHistory_length positive] at loopResult
    simpa [firstLookup, previous, previousOne, value_one] using loopResult
  · have previousTwo : 2 ≤ previous := by omega
    have beforeLast : k - previous + 1 < (conwayHistory k).length := by
      simp only [conwayHistory_length]
      omega
    have dropBound : k - previous + 1 ≤ k := by omega
    have finalHistory :
        stickyDrop (k - previous) (stickyDrop 1 (conwayHistory k)) =
          conwayHistory (previous - 1) := by
      rw [combinedDrop, stickyDrop_eq_drop beforeLast,
        conwayHistory_drop dropBound]
      have restored := Nat.sub_add_cancel previousUpper
      have remaining : k - (k - previous + 1) = previous - 1 := by
        omega
      exact congrArg conwayHistory remaining
    refine ⟨conwayHistory (previous - 2), ?_⟩
    rw [finalHistory] at loopResult
    rw [conwayHistory_eq_cons (k := previous - 1) (by omega)] at loopResult
    have previousIndex : previous - 1 + 1 = previous := by omega
    have previousTail : previous - 1 - 1 = previous - 2 := by omega
    rw [previousIndex, previousTail] at loopResult
    simpa [firstLookup, previous] using loopResult

private theorem secondLookup_eval (k : Nat) (positive : 1 ≤ k) :
    ∃ tail, ListEval secondLookup (conwayHistory k) [Int.ofNat k]
      (Int.ofNat (value (k + 2 - value (k + 1))) :: tail) := by
  let previous := value (k + 1)
  have previousPositive : 1 ≤ previous := value_positive _
  have previousUpper : previous ≤ k := by
    simpa [previous] using value_le_pred (k + 1) (by omega)
  have historyShape := conwayHistory_eq_cons positive
  have xResult : ListEval P.X (conwayHistory k) [Int.ofNat k]
      (Int.ofNat previous :: conwayHistory (k - 1)) := by
    simpa [previous, historyShape] using
      (list_x (conwayHistory k) [Int.ofNat k])
  have countRaw := list_diff xResult
    (list_one (conwayHistory k) [Int.ofNat k])
  have countResult : ListEval (P.diff P.X P.o)
      (conwayHistory k) [Int.ofNat k]
      (Int.ofNat (previous - 1) :: conwayHistory (k - 1)) := by
    simpa [Int.ofNat_sub previousPositive] using countRaw
  have execution := pop_iterates (iterations := previous - 1)
    (counter := 1) (conwayHistory_nonempty positive)
  have loopResult := list_loop countResult
    (list_x (conwayHistory k) [Int.ofNat k]) execution
  have beforeLast : previous - 1 < (conwayHistory k).length := by
    simp only [conwayHistory_length]
    omega
  have dropBound : previous - 1 ≤ k := by omega
  have finalHistory : stickyDrop (previous - 1) (conwayHistory k) =
      conwayHistory (k + 1 - previous) := by
    rw [stickyDrop_eq_drop beforeLast, conwayHistory_drop dropBound]
    have restored := Nat.sub_add_cancel previousUpper
    have indexEquality : k - (previous - 1) = k + 1 - previous := by
      omega
    exact congrArg conwayHistory indexEquality
  have finalPositive : 1 ≤ k + 1 - previous := by omega
  refine ⟨conwayHistory (k - previous), ?_⟩
  rw [finalHistory] at loopResult
  rw [conwayHistory_eq_cons (k := k + 1 - previous) finalPositive] at loopResult
  have indexEquality : k + 1 - previous + 1 = k + 2 - previous := by omega
  have tailEquality : k + 1 - previous - 1 = k - previous := by omega
  rw [indexEquality, tailEquality] at loopResult
  simpa [secondLookup, previous] using loopResult

private theorem conwayBody_eval (k : Nat) (positive : 1 ≤ k) :
    ListEval conwayBody (conwayHistory k) [Int.ofNat k]
      (conwayHistory (k + 1)) := by
  obtain ⟨firstTail, firstResult⟩ := firstLookup_eval k positive
  obtain ⟨secondTail, secondResult⟩ := secondLookup_eval k positive
  have pushed := list_push firstResult
    (list_x (conwayHistory k) [Int.ofNat k])
  have combined := list_addi pushed secondResult
  change ListEval conwayBody (conwayHistory k) [Int.ofNat k]
    (Int.ofNat (value (k + 2)) :: conwayHistory k)
  rw [value_recurrence (n := k + 2) (by omega)]
  simpa [conwayBody, conwayHistory, add_comm] using combined

private theorem conwayBodySwapped_eval (k : Nat) (positive : 1 ≤ k) :
    ListEval conwayBodySwapped (conwayHistory k) [Int.ofNat k]
      (conwayHistory (k + 1)) := by
  obtain ⟨firstTail, firstResult⟩ := firstLookup_eval k positive
  obtain ⟨secondTail, secondResult⟩ := secondLookup_eval k positive
  have pushed := list_push secondResult
    (list_x (conwayHistory k) [Int.ofNat k])
  have combined := list_addi pushed firstResult
  change ListEval conwayBodySwapped (conwayHistory k) [Int.ofNat k]
    (Int.ofNat (value (k + 2)) :: conwayHistory k)
  rw [value_recurrence (n := k + 2) (by omega)]
  simpa [conwayBodySwapped, conwayHistory, add_comm] using combined

private theorem conwayBody_iterates : ∀ (iterations k : Nat), 1 ≤ k →
    Iterates conwayBody iterations (conwayHistory k) (Int.ofNat k)
      (conwayHistory (k + iterations)) := by
  intro iterations
  induction iterations with
  | zero =>
      intro k positive
      simpa using Iterates.zero (conwayHistory k) (Int.ofNat k)
  | succ iterations inductionHypothesis =>
      intro k positive
      have step := conwayBody_eval k positive
      have rest := inductionHypothesis (k + 1) (by omega)
      have execution := Iterates.succ step rest
      simpa [add_assoc, add_comm, add_left_comm] using execution

private theorem conwayBodySwapped_iterates : ∀ (iterations k : Nat), 1 ≤ k →
    Iterates conwayBodySwapped iterations (conwayHistory k) (Int.ofNat k)
      (conwayHistory (k + iterations)) := by
  intro iterations
  induction iterations with
  | zero =>
      intro k positive
      simpa using Iterates.zero (conwayHistory k) (Int.ofNat k)
  | succ iterations inductionHypothesis =>
      intro k positive
      have step := conwayBodySwapped_eval k positive
      have rest := inductionHypothesis (k + 1) (by omega)
      have execution := Iterates.succ step rest
      simpa [add_assoc, add_comm, add_left_comm] using execution

private theorem conwayLoop_eval (position : Nat) :
    ∃ tail, ListEval (P.loop conwayBody (P.diff P.X P.o) P.o)
      [Int.ofNat position] [0]
      (Int.ofNat (value (position + 1)) :: tail) := by
  cases position with
  | zero =>
      have countResult := list_diff (list_x [0] [0]) (list_one [0] [0])
      have loopResult := list_loop_negative (body := conwayBody)
        countResult (by norm_num)
        (list_one [0] [0])
      exact ⟨[], by simpa [conwayBody, value_one] using loopResult⟩
  | succ position =>
      have countRaw := list_diff
        (list_x [Int.ofNat (position + 1)] [0])
        (list_one [Int.ofNat (position + 1)] [0])
      have countResult : ListEval (P.diff P.X P.o)
          [Int.ofNat (position + 1)] [0] [Int.ofNat position] := by
        simpa using countRaw
      have initialResult : ListEval P.o [Int.ofNat (position + 1)] [0]
          (conwayHistory 1) := by
        simpa [conwayHistory, value_two] using
          (list_one [Int.ofNat (position + 1)] [0])
      have execution := conwayBody_iterates position 1 (by omega)
      have loopResult := list_loop countResult initialResult execution
      refine ⟨conwayHistory position, ?_⟩
      simpa [conwayHistory, add_assoc, add_comm, add_left_comm] using loopResult

private theorem conwayLoopSwapped_eval (position : Nat) :
    ∃ tail, ListEval (P.loop conwayBodySwapped (P.diff P.X P.o) P.o)
      [Int.ofNat position] [0]
      (Int.ofNat (value (position + 1)) :: tail) := by
  cases position with
  | zero =>
      have countResult := list_diff (list_x [0] [0]) (list_one [0] [0])
      have loopResult := list_loop_negative (body := conwayBodySwapped)
        countResult (by norm_num)
        (list_one [0] [0])
      exact ⟨[], by simpa [conwayBodySwapped, value_one] using loopResult⟩
  | succ position =>
      have countRaw := list_diff
        (list_x [Int.ofNat (position + 1)] [0])
        (list_one [Int.ofNat (position + 1)] [0])
      have countResult : ListEval (P.diff P.X P.o)
          [Int.ofNat (position + 1)] [0] [Int.ofNat position] := by
        simpa using countRaw
      have initialResult : ListEval P.o [Int.ofNat (position + 1)] [0]
          (conwayHistory 1) := by
        simpa [conwayHistory, value_two] using
          (list_one [Int.ofNat (position + 1)] [0])
      have execution := conwayBodySwapped_iterates position 1 (by omega)
      have loopResult := list_loop countResult initialResult execution
      refine ⟨conwayHistory position, ?_⟩
      simpa [conwayHistory, add_assoc, add_comm, add_left_comm] using loopResult

private theorem realizes_of_list {spec : SequenceSpec} {candidate : FrozenCandidate}
    (result : ∀ position, spec.Domain (spec.index position) →
      ∃ tail, ListEval candidate.program [Int.ofNat position] [0]
        (spec.value (spec.index position) :: tail)) :
    CandidateRealizes spec candidate := by
  intro position indexInDomain
  obtain ⟨tail, execution⟩ := result position indexInDomain
  exact emits_implies_eventuallyEmits
    (listEval_head_emits execution)

/-- The reported A004001 program realizes the recurrence at every index. -/
theorem reportedA004001_correct :
    CandidateRealizes specA004001 reportedA004001 := by
  apply realizes_of_list
  intro position indexInDomain
  obtain ⟨tail, result⟩ := conwayLoop_eval position
  have indexNat : (1 + Int.ofNat position).toNat = position + 1 := by
    rw [Int.ofNat_eq_natCast, add_comm]
    exact Int.toNat_natCast_add_one
  have expectedValue : specA004001.value (specA004001.index position) =
      Int.ofNat (value (position + 1)) := by
    change Int.ofNat (value ((1 + Int.ofNat position).toNat)) = _
    rw [indexNat]
  refine ⟨tail, ?_⟩
  rw [expectedValue]
  simpa [reportedA004001, conwayBody, firstLookup, secondLookup] using result

/-- The reported A004074 program realizes the centered Conway transform. -/
theorem reportedA004074_correct :
    CandidateRealizes specA004074 reportedA004074 := by
  apply realizes_of_list
  intro position indexInDomain
  obtain ⟨tail, loopResult⟩ := conwayLoopSwapped_eval position
  have doubled := list_mult
    (list_two [Int.ofNat position] [0]) loopResult
  have decremented := list_diff doubled
    (list_one [Int.ofNat position] [0])
  have centered := list_diff decremented
    (list_x [Int.ofNat position] [0])
  have indexNat : (1 + Int.ofNat position).toNat = position + 1 := by
    rw [Int.ofNat_eq_natCast, add_comm]
    exact Int.toNat_natCast_add_one
  have expectedValue : specA004074.value (specA004074.index position) =
      2 * Int.ofNat (value (position + 1)) - 1 - Int.ofNat position := by
    change 2 * Int.ofNat (value ((1 + Int.ofNat position).toNat)) -
      (1 + Int.ofNat position) = _
    rw [indexNat]
    ring_nf
  refine ⟨[], ?_⟩
  rw [expectedValue]
  simpa [reportedA004074, conwayBodySwapped, firstLookup, secondLookup] using centered

private def kolakoskiHistory (step : Nat) : List Int :=
  reverseHistory
    (fun index => Int.ofNat (Mettapedia.Sequences.OEIS.Kolakoski.bit index))
    step

private def kolakoskiState (step : Nat) : List Int :=
  Int.ofNat (Mettapedia.Sequences.OEIS.Kolakoski.packedCursor step) ::
    kolakoskiHistory step

@[simp] private theorem kolakoskiHistory_length (step : Nat) :
    (kolakoskiHistory step).length = step + 1 := by
  simp [kolakoskiHistory]

private theorem kolakoskiHistory_shape (step : Nat) :
    kolakoskiHistory step =
      Int.ofNat (Mettapedia.Sequences.OEIS.Kolakoski.bit step) ::
        (kolakoskiHistory step).tail := by
  cases step <;> rfl

@[simp] private theorem kolakoskiState_length (step : Nat) :
    (kolakoskiState step).length = step + 2 := by
  simp [kolakoskiState]

private theorem kolakoskiState_nonempty (step : Nat) :
    kolakoskiState step ≠ [] := by
  simp [kolakoskiState]

/-- The inner pop loop selects exactly the increment encoded by the cursor. -/
private theorem kolakoskiSelectedState (step : Nat) :
    ∃ tail,
      stickyDrop
          (Mettapedia.Sequences.OEIS.Kolakoski.packedCursor step / 2)
          (kolakoskiState step) =
        Int.ofNat (Mettapedia.Sequences.OEIS.Kolakoski.cursorIncrement step) :: tail := by
  by_cases stepZero : step = 0
  · subst step
    exact ⟨[0], rfl⟩
  · let run := (Mettapedia.Sequences.OEIS.Kolakoski.cursor step).run
    let count :=
      Mettapedia.Sequences.OEIS.Kolakoski.packedCursor step / 2
    have runPositive : 1 ≤ run :=
      (Mettapedia.Sequences.OEIS.Kolakoski.cursor step).runPositive
    have runBound : run ≤ step := by
      simpa [run] using
        Mettapedia.Sequences.OEIS.Kolakoski.cursor_run_le_current
          (step := step) (by omega)
    have countEquation : count = step + 1 - run := by
      simpa [count, run] using
        Mettapedia.Sequences.OEIS.Kolakoski.packedCursor_div_two step
    have countPositive : 1 ≤ count := by omega
    have countBound : count ≤ step := by omega
    have beforeLast : count < (kolakoskiState step).length := by
      simp only [kolakoskiState_length]
      omega
    rw [stickyDrop_eq_drop beforeLast]
    have dropState :
        (kolakoskiState step).drop count =
          (kolakoskiHistory step).drop (count - 1) := by
      obtain ⟨previous, countShape⟩ :=
        Nat.exists_eq_succ_of_ne_zero (by omega : count ≠ 0)
      rw [countShape]
      simp [kolakoskiState]
    rw [dropState]
    have historyDrop := reverseHistory_drop
      (stream := fun index =>
        Int.ofNat (Mettapedia.Sequences.OEIS.Kolakoski.bit index))
      (last := step) (count := count - 1) (by omega)
    have historyDrop' :
        (kolakoskiHistory step).drop (count - 1) =
          kolakoskiHistory (step - (count - 1)) := by
      simpa [kolakoskiHistory] using historyDrop
    rw [historyDrop']
    have remaining : step - (count - 1) = run := by omega
    rw [remaining]
    refine ⟨(kolakoskiHistory run).tail, ?_⟩
    rw [kolakoskiHistory_shape run]
    simp [kolakoskiHistory,
      Mettapedia.Sequences.OEIS.Kolakoski.cursorIncrement, stepZero, run]

private def kolakoskiInnerLookup : GauthierE2ListSemantics.Program :=
  P.loop (P.pop P.X) (P.divi P.X P.tw) P.X

private def kolakoskiBitUpdate : GauthierE2ListSemantics.Program :=
  P.modu (P.addi P.X (P.pop P.X)) P.tw

private def kolakoskiBody : GauthierE2ListSemantics.Program :=
  P.addi (P.push kolakoskiInnerLookup kolakoskiBitUpdate) P.X

private theorem kolakoskiInnerLookup_eval (step : Nat) (counter : Int) :
    ∃ tail, ListEval kolakoskiInnerLookup (kolakoskiState step) [counter]
      (Int.ofNat
          (Mettapedia.Sequences.OEIS.Kolakoski.cursorIncrement step) :: tail) := by
  let iterations :=
    Mettapedia.Sequences.OEIS.Kolakoski.packedCursor step / 2
  have countRaw := list_divi
    (list_x (kolakoskiState step) [counter])
    (list_two (kolakoskiState step) [counter]) (by norm_num)
  have quotientEquality :
      Int.fdiv
          (Int.ofNat
            (Mettapedia.Sequences.OEIS.Kolakoski.packedCursor step)) 2 =
        Int.ofNat iterations := by
    simpa [iterations] using
      (Int.ofNat_fdiv
        (Mettapedia.Sequences.OEIS.Kolakoski.packedCursor step) 2).symm
  rw [quotientEquality] at countRaw
  have countResult : ListEval (P.divi P.X P.tw)
      (kolakoskiState step) [counter]
      (Int.ofNat iterations :: kolakoskiHistory step) := by
    simpa only [kolakoskiState] using countRaw
  have execution := pop_iterates (iterations := iterations)
    (counter := 1) (kolakoskiState_nonempty step)
  have loopResult := list_loop countResult
    (list_x (kolakoskiState step) [counter]) execution
  obtain ⟨tail, selected⟩ := kolakoskiSelectedState step
  refine ⟨tail, ?_⟩
  rw [← selected]
  simpa [kolakoskiInnerLookup, iterations] using loopResult

private theorem kolakoskiBitUpdate_eval (step : Nat) (counter : Int) :
    ListEval kolakoskiBitUpdate (kolakoskiState step) [counter]
      (Int.ofNat (Mettapedia.Sequences.OEIS.Kolakoski.bit (step + 1)) ::
        kolakoskiHistory step) := by
  let packed := Mettapedia.Sequences.OEIS.Kolakoski.packedCursor step
  let currentBit := Mettapedia.Sequences.OEIS.Kolakoski.bit step
  have stateShape : kolakoskiState step =
      Int.ofNat packed :: Int.ofNat currentBit :: (kolakoskiHistory step).tail := by
    rw [kolakoskiState, kolakoskiHistory_shape]
    rfl
  have xResult : ListEval P.X (kolakoskiState step) [counter]
      (Int.ofNat packed :: Int.ofNat currentBit ::
        (kolakoskiHistory step).tail) := by
    rw [← stateShape]
    exact list_x (kolakoskiState step) [counter]
  have popped := list_pop_cons xResult
  have added := list_addi xResult popped
  have reduced := list_modu added
    (list_two (kolakoskiState step) [counter]) (by norm_num)
  have headEquality :
      Int.fmod (Int.ofNat packed + Int.ofNat currentBit) 2 =
        Int.ofNat (Mettapedia.Sequences.OEIS.Kolakoski.bit (step + 1)) := by
    have transition :=
      Mettapedia.Sequences.OEIS.Kolakoski.packedCursor_add_bit_mod_two step
    simp only [Int.ofNat_eq_natCast]
    rw [← Int.natCast_add]
    rw [Int.fmod_eq_emod]
    simp only [show (0 : Int) ≤ 2 by norm_num, true_or, if_true, add_zero]
    change Int.ofNat ((packed + currentBit) % 2) = _
    exact congrArg Int.ofNat (by simpa [packed, currentBit] using transition)
  rw [headEquality] at reduced
  rw [stateShape] at reduced
  rw [stateShape, kolakoskiHistory_shape step]
  simpa [kolakoskiBitUpdate, currentBit] using reduced

private theorem kolakoskiBody_eval (step : Nat) (counter : Int) :
    ListEval kolakoskiBody (kolakoskiState step) [counter]
      (kolakoskiState (step + 1)) := by
  obtain ⟨innerTail, innerResult⟩ :=
    kolakoskiInnerLookup_eval step counter
  have bitResult := kolakoskiBitUpdate_eval step counter
  have pushed := list_push innerResult bitResult
  have advanced := list_addi pushed
    (list_x (kolakoskiState step) [counter])
  have cursorTransition :=
    Mettapedia.Sequences.OEIS.Kolakoski.packedCursor_succ step
  have castTransition :
      Int.ofNat
          (Mettapedia.Sequences.OEIS.Kolakoski.cursorIncrement step) +
        Int.ofNat
          (Mettapedia.Sequences.OEIS.Kolakoski.packedCursor step) =
      Int.ofNat
          (Mettapedia.Sequences.OEIS.Kolakoski.packedCursor (step + 1)) := by
    have naturalTransition :
        Mettapedia.Sequences.OEIS.Kolakoski.cursorIncrement step +
            Mettapedia.Sequences.OEIS.Kolakoski.packedCursor step =
          Mettapedia.Sequences.OEIS.Kolakoski.packedCursor (step + 1) :=
      (add_comm _ _).trans cursorTransition.symm
    simpa only [Int.ofNat_eq_natCast, Int.natCast_add] using
      congrArg Int.ofNat naturalTransition
  rw [castTransition] at advanced
  simpa [kolakoskiBody, kolakoskiState, kolakoskiHistory, reverseHistory]
    using advanced

private theorem kolakoskiBody_iterates : ∀ (iterations step : Nat)
    (counter : Int),
    Iterates kolakoskiBody iterations (kolakoskiState step) counter
      (kolakoskiState (step + iterations)) := by
  intro iterations
  induction iterations with
  | zero =>
      intro step counter
      simpa using Iterates.zero (kolakoskiState step) counter
  | succ iterations inductionHypothesis =>
      intro step counter
      have first := kolakoskiBody_eval step counter
      have rest := inductionHypothesis (step + 1) (counter + 1)
      have execution := Iterates.succ first rest
      simpa [add_assoc, add_comm, add_left_comm] using execution

private theorem kolakoskiLoop_eval (position : Nat) :
    ∃ tail,
      ListEval
        (P.loop kolakoskiBody P.X (P.push P.o P.z))
        [Int.ofNat position] [0]
        (Int.ofNat
            (Mettapedia.Sequences.OEIS.Kolakoski.packedCursor position) ::
          Int.ofNat (Mettapedia.Sequences.OEIS.Kolakoski.bit position) :: tail) := by
  have initialResult :
      ListEval (P.push P.o P.z) [Int.ofNat position] [0]
        (kolakoskiState 0) := by
    have pushed := list_push
      (list_one [Int.ofNat position] [0])
      (list_zero [Int.ofNat position] [0])
    simpa [kolakoskiState, kolakoskiHistory, reverseHistory,
      Mettapedia.Sequences.OEIS.Kolakoski.packedCursor,
      Mettapedia.Sequences.OEIS.Kolakoski.boundaryBit,
      Mettapedia.Sequences.OEIS.Kolakoski.cursor,
      Mettapedia.Sequences.OEIS.Kolakoski.bit,
      Mettapedia.Sequences.OEIS.Kolakoski.value] using pushed
  have execution := kolakoskiBody_iterates position 0 1
  have loopResult := list_loop
    (list_x [Int.ofNat position] [0]) initialResult execution
  rw [show 0 + position = position by omega] at loopResult
  rw [kolakoskiState, kolakoskiHistory_shape position] at loopResult
  exact ⟨(kolakoskiHistory position).tail, loopResult⟩

/-- The reported Kolakoski program realizes A000002 at every positive index. -/
theorem reportedA000002_correct :
    CandidateRealizes
      Mettapedia.Sequences.OEIS.Kolakoski.specA000002 reportedA000002 := by
  apply realizes_of_list
  intro position indexInDomain
  obtain ⟨loopTail, loopResult⟩ := kolakoskiLoop_eval position
  have popped := list_pop_cons loopResult
  have output := list_addi
    (list_one [Int.ofNat position] [0]) popped
  have outputValue :
      1 + Int.ofNat (Mettapedia.Sequences.OEIS.Kolakoski.bit position) =
        Int.ofNat (Mettapedia.Sequences.OEIS.Kolakoski.value position) := by
    have naturalOutput :
        1 + Mettapedia.Sequences.OEIS.Kolakoski.bit position =
          Mettapedia.Sequences.OEIS.Kolakoski.value position :=
      (add_comm _ _).trans
        (Mettapedia.Sequences.OEIS.Kolakoski.bit_add_one position)
    simpa only [Int.ofNat_eq_natCast, Int.natCast_one, Int.natCast_add] using
      congrArg Int.ofNat naturalOutput
  rw [outputValue] at output
  have indexNat : (1 + Int.ofNat position).toNat - 1 = position := by
    rw [Int.ofNat_eq_natCast, add_comm]
    rw [Int.toNat_natCast_add_one]
    omega
  have expectedValue :
      Mettapedia.Sequences.OEIS.Kolakoski.specA000002.value
          (Mettapedia.Sequences.OEIS.Kolakoski.specA000002.index position) =
        Int.ofNat (Mettapedia.Sequences.OEIS.Kolakoski.value position) := by
    change Int.ofNat
      (Mettapedia.Sequences.OEIS.Kolakoski.value
        ((1 + Int.ofNat position).toNat - 1)) = _
    rw [indexNat]
  refine ⟨[], ?_⟩
  rw [expectedValue]
  simpa [reportedA000002, kolakoskiBody, kolakoskiInnerLookup,
    kolakoskiBitUpdate] using output

private def cyclotomicPowerBody : GauthierE2ListSemantics.Program :=
  P.addi P.o (P.addi P.X P.X)

private def cyclotomicStripBody : GauthierE2ListSemantics.Program :=
  P.cond (P.modu P.X P.Y) (P.divi P.X P.Y) P.X

private def cyclotomicOuterBody : GauthierE2ListSemantics.Program :=
  P.loop2 cyclotomicStripBody (P.pop P.Y) P.Y
    (P.push (P.loop cyclotomicPowerBody P.Y P.o) P.X) P.X

private theorem cyclotomicPowerBody_eval (exponent : Nat) (counter : Int) :
    ListEval cyclotomicPowerBody [Int.ofNat (2 ^ (exponent + 1) - 1)]
      [counter] [Int.ofNat (2 ^ (exponent + 2) - 1)] := by
  have doubled := list_addi
    (list_x [Int.ofNat (2 ^ (exponent + 1) - 1)] [counter])
    (list_x [Int.ofNat (2 ^ (exponent + 1) - 1)] [counter])
  have incremented := list_addi
    (list_one [Int.ofNat (2 ^ (exponent + 1) - 1)] [counter]) doubled
  have arithmetic :=
    Mettapedia.Sequences.OEIS.CyclotomicSieve.two_pow_sub_one_step exponent
  have castArithmetic :
      1 + (Int.ofNat (2 ^ (exponent + 1) - 1) +
        Int.ofNat (2 ^ (exponent + 1) - 1)) =
          Int.ofNat (2 ^ (exponent + 2) - 1) := by
    simpa only [Int.ofNat_eq_natCast, Int.natCast_one, Int.natCast_add] using
      congrArg Int.ofNat arithmetic
  rw [castArithmetic] at incremented
  simpa [cyclotomicPowerBody] using incremented

private theorem cyclotomicPowerBody_iterates_from : ∀ (iterations exponent : Nat)
    (counter : Int),
    Iterates cyclotomicPowerBody iterations
      [Int.ofNat (2 ^ (exponent + 1) - 1)] counter
      [Int.ofNat (2 ^ (exponent + iterations + 1) - 1)] := by
  intro iterations
  induction iterations with
  | zero =>
      intro exponent counter
      simpa using Iterates.zero
        [Int.ofNat (2 ^ (exponent + 1) - 1)] counter
  | succ iterations inductionHypothesis =>
      intro exponent counter
      have first := cyclotomicPowerBody_eval exponent counter
      have rest := inductionHypothesis (exponent + 1) (counter + 1)
      have execution := Iterates.succ first rest
      simpa [add_assoc, add_comm, add_left_comm] using execution

private theorem cyclotomicPowerBody_iterates (iterations : Nat) (counter : Int) :
    Iterates cyclotomicPowerBody iterations [1] counter
      [Int.ofNat (2 ^ (iterations + 1) - 1)] := by
  simpa using cyclotomicPowerBody_iterates_from iterations 0 counter

private theorem cyclotomicStripBody_eval
    (candidate divisor : Nat) (archive divisorTail : List Nat)
    (divisorPositive : 0 < divisor) :
    ListEval cyclotomicStripBody
      (Int.ofNat candidate :: archive.map Int.ofNat)
      (Int.ofNat divisor :: divisorTail.map Int.ofNat)
      (Int.ofNat
          (Mettapedia.Sequences.OEIS.CyclotomicSieve.removeIfDivides
            candidate divisor) :: archive.map Int.ofNat) := by
  have xResult := list_x
    (Int.ofNat candidate :: archive.map Int.ofNat)
    (Int.ofNat divisor :: divisorTail.map Int.ofNat)
  have yResult := list_y
    (Int.ofNat candidate :: archive.map Int.ofNat)
    (Int.ofNat divisor :: divisorTail.map Int.ofNat)
  have divisorNonzero : Int.ofNat divisor ≠ 0 :=
    Int.ofNat_ne_zero.mpr divisorPositive.ne'
  have modulus := list_modu xResult yResult divisorNonzero
  have modulusEquality :
      Int.fmod (Int.ofNat candidate) (Int.ofNat divisor) =
        Int.ofNat (candidate % divisor) := by
    simp only [Int.ofNat_eq_natCast]
    rw [Int.fmod_eq_emod]
    simp
  rw [modulusEquality] at modulus
  by_cases divides : candidate % divisor = 0
  · have quotient := list_divi xResult yResult divisorNonzero
    have quotientEquality :
        Int.fdiv (Int.ofNat candidate) (Int.ofNat divisor) =
          Int.ofNat (candidate / divisor) := by
      simpa using (Int.ofNat_fdiv candidate divisor).symm
    rw [quotientEquality] at quotient
    have selected := list_cond_nonpositive (elseBranch := P.X) modulus
      (by simp [divides]) quotient
    simpa [cyclotomicStripBody,
      Mettapedia.Sequences.OEIS.CyclotomicSieve.removeIfDivides, divides]
      using selected
  · have remainderPositive : 0 < candidate % divisor :=
      Nat.pos_of_ne_zero divides
    have selected := list_cond_positive (thenBranch := P.divi P.X P.Y) modulus
      (by
        rw [Int.ofNat_eq_natCast]
        exact Int.natCast_pos.mpr remainderPositive) xResult
    simpa [cyclotomicStripBody,
      Mettapedia.Sequences.OEIS.CyclotomicSieve.removeIfDivides, divides]
      using selected

private theorem cyclotomicStrip_iterates : ∀ (divisors archive : List Nat)
    (candidate : Nat),
    (∀ divisor ∈ divisors, 0 < divisor) →
    Iterates2 cyclotomicStripBody (P.pop P.Y) divisors.length
      (Int.ofNat candidate :: archive.map Int.ofNat)
      (divisors.map Int.ofNat)
      (Int.ofNat
          (Mettapedia.Sequences.OEIS.CyclotomicSieve.scan divisors candidate) ::
        archive.map Int.ofNat) := by
  intro divisors
  induction divisors with
  | nil =>
      intro archive candidate divisorsPositive
      simpa using Iterates2.zero
        (Int.ofNat candidate :: archive.map Int.ofNat) []
  | cons divisor divisors inductionHypothesis =>
      intro archive candidate divisorsPositive
      have divisorPositive : 0 < divisor :=
        divisorsPositive divisor (by simp)
      have firstStep := cyclotomicStripBody_eval
        candidate divisor archive divisors divisorPositive
      cases divisors with
      | nil =>
          have secondStep := list_pop_singleton
            (list_y
              (Int.ofNat candidate :: archive.map Int.ofNat)
              [Int.ofNat divisor])
          have rest := Iterates2.zero
            (first := cyclotomicStripBody) (second := P.pop P.Y)
            (Int.ofNat
                (Mettapedia.Sequences.OEIS.CyclotomicSieve.removeIfDivides
                  candidate divisor) :: archive.map Int.ofNat)
            [Int.ofNat divisor]
          have execution := Iterates2.succ firstStep secondStep rest
          simpa using execution
      | cons next tail =>
          have secondStep := list_pop_cons
            (list_y
              (Int.ofNat candidate :: archive.map Int.ofNat)
              (Int.ofNat divisor :: Int.ofNat next :: tail.map Int.ofNat))
          have tailPositive : ∀ value ∈ next :: tail, 0 < value := by
            intro value membership
            exact divisorsPositive value (by simp [membership])
          have rest := inductionHypothesis archive
            (Mettapedia.Sequences.OEIS.CyclotomicSieve.removeIfDivides
              candidate divisor) tailPositive
          have execution := Iterates2.succ firstStep secondStep rest
          simpa using execution

private def cyclotomicHistory (step : Nat) : List Int :=
  (Mettapedia.Sequences.OEIS.CyclotomicSieve.build step).history.map Int.ofNat

@[simp] private theorem cyclotomicHistory_length (step : Nat) :
    (cyclotomicHistory step).length = step + 1 := by
  simp [cyclotomicHistory]

private theorem cyclotomicHistory_shape (step : Nat) :
    cyclotomicHistory step =
      Int.ofNat (Mettapedia.Sequences.OEIS.CyclotomicSieve.value step) ::
        (cyclotomicHistory step).tail := by
  have sourceShape :=
    Mettapedia.Sequences.OEIS.CyclotomicSieve.build_history_head step
  have mapped := congrArg (List.map Int.ofNat) sourceShape
  simpa [cyclotomicHistory] using mapped

private theorem cyclotomicOuterBody_eval (step : Nat) :
    ListEval cyclotomicOuterBody (cyclotomicHistory step)
      [Int.ofNat (step + 1)] (cyclotomicHistory (step + 1)) := by
  have countResult := list_y (cyclotomicHistory step) [Int.ofNat (step + 1)]
  have powerExecution := cyclotomicPowerBody_iterates (step + 1) 1
  have powerResult := list_loop countResult
    (list_one (cyclotomicHistory step) [Int.ofNat (step + 1)])
    powerExecution
  have firstInitial := list_push powerResult
    (list_x (cyclotomicHistory step) [Int.ofNat (step + 1)])
  let history :=
    (Mettapedia.Sequences.OEIS.CyclotomicSieve.build step).history
  have historyPositive : ∀ value ∈ history, 0 < value :=
    (Mettapedia.Sequences.OEIS.CyclotomicSieve.build step).positive
  have stripExecution := cyclotomicStrip_iterates history history
    (2 ^ (step + 2) - 1) historyPositive
  have stripExecution' :
      Iterates2 cyclotomicStripBody (P.pop P.Y) (step + 1)
        (Int.ofNat (2 ^ (step + 1 + 1) - 1) :: cyclotomicHistory step)
        (cyclotomicHistory step)
        (Int.ofNat
            (Mettapedia.Sequences.OEIS.CyclotomicSieve.scan history
              (2 ^ (step + 2) - 1)) :: cyclotomicHistory step) := by
    simpa [history, cyclotomicHistory, add_assoc] using stripExecution
  have loopResult := list_loop2 countResult firstInitial
    (list_x (cyclotomicHistory step) [Int.ofNat (step + 1)])
    stripExecution'
  have nextHistory :=
    Mettapedia.Sequences.OEIS.CyclotomicSieve.build_succ_history step
  have mappedNext := congrArg (List.map Int.ofNat) nextHistory
  have targetHistory : cyclotomicHistory (step + 1) =
      Int.ofNat
          (Mettapedia.Sequences.OEIS.CyclotomicSieve.scan history
            (2 ^ (step + 2) - 1)) :: cyclotomicHistory step := by
    simpa [cyclotomicHistory, history] using mappedNext
  rw [targetHistory]
  simpa [cyclotomicOuterBody, cyclotomicHistory, history, add_assoc,
    add_comm, add_left_comm] using loopResult

private theorem cyclotomicOuterBody_iterates : ∀ (iterations step : Nat),
    Iterates cyclotomicOuterBody iterations (cyclotomicHistory step)
      (Int.ofNat (step + 1)) (cyclotomicHistory (step + iterations)) := by
  intro iterations
  induction iterations with
  | zero =>
      intro step
      simpa using Iterates.zero (cyclotomicHistory step) (Int.ofNat (step + 1))
  | succ iterations inductionHypothesis =>
      intro step
      have first := cyclotomicOuterBody_eval step
      have rest := inductionHypothesis (step + 1)
      have counterEquality : Int.ofNat (step + 1) + 1 =
          Int.ofNat (step + 1 + 1) := by
        simp only [Int.ofNat_eq_natCast]
        push_cast
        ring
      rw [← counterEquality] at rest
      have execution := Iterates.succ first rest
      simpa [add_assoc, add_comm, add_left_comm] using execution

/-- The reported A070526 program computes the divisibility sieve at every input. -/
theorem reportedA070526_computes_sieve (position : Nat) :
    ∃ tail, ListEval reportedA070526.program [Int.ofNat position] [0]
      (Int.ofNat
          (Mettapedia.Sequences.OEIS.CyclotomicSieve.value
            (Mettapedia.Sequences.OEIS.CyclotomicSieve.outerIterations position)) ::
        tail) := by
  have sumResult := list_addi
    (list_two [Int.ofNat position] [0])
    (list_x [Int.ofNat position] [0])
  have countRaw := list_mult sumResult
    (list_x [Int.ofNat position] [0])
  have countEquality :
      (2 + Int.ofNat position) * Int.ofNat position =
        Int.ofNat
          (Mettapedia.Sequences.OEIS.CyclotomicSieve.outerIterations position) := by
    simp only [Mettapedia.Sequences.OEIS.CyclotomicSieve.outerIterations,
      Int.ofNat_eq_natCast]
    push_cast
    ring
  rw [countEquality] at countRaw
  have initialResult : ListEval P.o [Int.ofNat position] [0]
      (cyclotomicHistory 0) := by
    simpa [cyclotomicHistory] using list_one [Int.ofNat position] [0]
  have execution := cyclotomicOuterBody_iterates
    (Mettapedia.Sequences.OEIS.CyclotomicSieve.outerIterations position) 0
  have loopResult := list_loop countRaw initialResult execution
  rw [show 0 + Mettapedia.Sequences.OEIS.CyclotomicSieve.outerIterations position =
      Mettapedia.Sequences.OEIS.CyclotomicSieve.outerIterations position by omega]
    at loopResult
  rw [cyclotomicHistory_shape] at loopResult
  refine ⟨(cyclotomicHistory
    (Mettapedia.Sequences.OEIS.CyclotomicSieve.outerIterations position)).tail, ?_⟩
  simpa [reportedA070526, cyclotomicOuterBody, cyclotomicStripBody,
    cyclotomicPowerBody] using loopResult

/-- The reported nested-loop program realizes OEIS A070526 at every
positive index. -/
theorem reportedA070526_correct :
    CandidateRealizes
      Mettapedia.Sequences.OEIS.CyclotomicSieve.specA070526
      reportedA070526 := by
  apply realizes_of_list
  intro position indexInDomain
  obtain ⟨tail, execution⟩ := reportedA070526_computes_sieve position
  have sieveValue :
      Int.ofNat
          (Mettapedia.Sequences.OEIS.CyclotomicSieve.value
            (Mettapedia.Sequences.OEIS.CyclotomicSieve.outerIterations
              position)) =
        Mettapedia.Sequences.OEIS.CyclotomicSieve.cyclotomicValue
          (position + 1) := by
    rw [Mettapedia.Sequences.OEIS.CyclotomicSieve.value_outerIterations_eq_target]
    rw [Int.ofNat_eq_natCast,
      Mettapedia.Sequences.OEIS.CyclotomicSieve.cyclotomicAtTwo_cast]
    exact
      (Mettapedia.Sequences.OEIS.CyclotomicSieve.cyclotomicValue_eq_target_eval
        position).symm
  have indexNat : (1 + Int.ofNat position).toNat = position + 1 := by
    rw [Int.ofNat_eq_natCast, add_comm]
    exact Int.toNat_natCast_add_one
  have expectedValue :
      Mettapedia.Sequences.OEIS.CyclotomicSieve.specA070526.value
          (Mettapedia.Sequences.OEIS.CyclotomicSieve.specA070526.index
            position) =
        Int.ofNat
          (Mettapedia.Sequences.OEIS.CyclotomicSieve.value
            (Mettapedia.Sequences.OEIS.CyclotomicSieve.outerIterations
              position)) := by
    change Mettapedia.Sequences.OEIS.CyclotomicSieve.cyclotomicValue
      ((1 + Int.ofNat position).toNat) = _
    rw [indexNat, sieveValue]
  refine ⟨tail, ?_⟩
  rw [expectedValue]
  exact execution
#print axioms conwayHistory_drop
#print axioms stickyDrop_conwayHistory_length
#print axioms reportedA004001_correct
#print axioms reportedA004074_correct
#print axioms reportedA000002_correct
#print axioms reportedA070526_computes_sieve
#print axioms reportedA070526_correct

end Mettapedia.GSLT.LanguageDef.GauthierReportedSequencePrograms
