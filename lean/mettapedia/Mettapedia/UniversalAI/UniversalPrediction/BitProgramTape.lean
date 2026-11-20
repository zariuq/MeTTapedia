import Mettapedia.UniversalAI.UniversalPrediction.BitProgramMixture

/-!
# Programmer descriptions and random input on one tape

A run first reads a self-delimiting description and then passes the unread
input to the selected generator. Counting a finite tape once by this
interpreter gives exactly the diagonal numerator of the countable mixture.
-/

set_option autoImplicit false

namespace Mettapedia.UniversalAI.UniversalPrediction.BitProgramMixture

open Filter Mettapedia.Computability Mettapedia.Computability.BitGenerator
open Mettapedia.Computability.Hutter
open Mettapedia.UniversalAI.TimeBoundedAIXI (bitstringsOfLength length_eq_of_mem_bitstringsOfLength)
open scoped ENNReal

def description : Nat → List Bool
  | 0 => [false]
  | index + 1 => true :: description index

@[simp] theorem description_length (index : Nat) :
    (description index).length = index + 1 := by
  induction index with
  | zero => rfl
  | succ index ih => simp [description, ih]

def readDescriptionFrom (start : Nat) : List Bool → Option (Nat × List Bool)
  | [] => none
  | false :: rest => some (start, rest)
  | true :: rest => readDescriptionFrom (start + 1) rest

theorem readDescriptionFrom_append (start index : Nat) (suffix : List Bool) :
    readDescriptionFrom start (description index ++ suffix) = some (start + index, suffix) := by
  induction index generalizing start with
  | zero => rfl
  | succ index ih =>
    rw [description, List.cons_append, readDescriptionFrom, ih]
    congr 2
    omega

theorem description_prefix_free {first second : Nat}
    (contained : description first <+: description second) : first = second := by
  obtain ⟨suffix, same⟩ := contained
  have left := readDescriptionFrom_append 0 first suffix
  have right := readDescriptionFrom_append 0 second []
  rw [same] at left
  simp only [List.append_nil, Nat.zero_add] at left right
  have pair := Option.some.inj (left.symm.trans right)
  exact congrArg Prod.fst pair

/-- One tape interpretation of a mixture stage. The evaluator's cutoff is
the number of bits remaining after the description. An unfinished
description contributes no established mass. -/
def tapeAcceptsFrom (start : Nat) (history : List Bool) (tape : List Bool) : Bool :=
  match readDescriptionFrom start tape with
  | none => false
  | some (index, rest) => history.isPrefixOf ((programAt index).cut rest.length rest)

private theorem sumRange_succ_head (f : Nat → Nat) (n : Nat) :
    sumRange f (n + 1) = f 0 + sumRange (fun i => f (i + 1)) n := by
  induction n with
  | zero => simp
  | succ n ih =>
    change sumRange f (n + 1) + f (n + 1) = f 0 + sumRange (fun i => f (i + 1)) (n + 1)
    rw [ih, sumRange_succ, Nat.add_assoc]

private theorem count_tapes (start stage : Nat) (history : List Bool) :
    (bitstringsOfLength stage).countP (tapeAcceptsFrom start history) =
      sumRange (fun index => (programAt (start + index)).count history (stage - (index + 1))) stage := by
  induction stage generalizing start with
  | zero => simp [bitstringsOfLength, tapeAcceptsFrom, readDescriptionFrom]
  | succ stage ih =>
    rw [Generator.countP_bitstrings_succ, sumRange_succ_head]
    have falseBranch :
        (bitstringsOfLength stage).countP (fun tape => tapeAcceptsFrom start history (false :: tape)) =
          (programAt start).count history stage := by
      rw [List.countP_eq_length_filter, Generator.count_eq_filter]
      congr 1
      apply List.filter_congr
      intro tape present
      simp [tapeAcceptsFrom, readDescriptionFrom, length_eq_of_mem_bitstringsOfLength present]
    have trueBranch : (fun tape => tapeAcceptsFrom start history (true :: tape)) =
        tapeAcceptsFrom (start + 1) history := rfl
    rw [falseBranch, trueBranch, ih (start + 1)]
    simp only [Nat.add_zero, Nat.add_sub_cancel]
    congr 1
    apply congrArg (fun f => sumRange f stage)
    funext index
    have sameIndex : start + 1 + index = start + (index + 1) := by omega
    have sameBudget : stage - (index + 1) = stage + 1 - (index + 1 + 1) := by omega
    rw [sameIndex, sameBudget]

/-- The uniform mass is obtained by one sequential reading of the model
description and its random input, with no double counting of extensions. -/
theorem stageNumerator_eq_tape_count (history : List Bool) (stage : Nat) :
    stageNumerator history stage =
      (bitstringsOfLength stage).countP (tapeAcceptsFrom 0 history) := by
  simpa only [stageNumerator, Nat.zero_add] using (count_tapes 0 stage history).symm

abbrev TapeState := Nat ⊕ (Nat × Nat)

private def withIndex (index : Nat) : Instruction Nat Bool → Instruction TapeState Bool
  | .silent next => .silent (.inr (index, next))
  | .read no yes => .read (.inr (index, no)) (.inr (index, yes))
  | .emit bit next => .emit bit (.inr (index, next))

private def tapeStep (stage : Nat) : Transition TapeState Bool
  | .inl index => some (.read (.inr (index, 0)) (.inl (index + 1)))
  | .inr (index, state) =>
    ((programAt index).atStage (stage - (index + 1)) state).map (withIndex index)

/-- Read the header incrementally, then run the indicated transition code
on the same one-way tape. Reading a header never emits output. -/
def tapeGenerator : Generator TapeState Bool where
  initial := .inl 0
  atStage := tapeStep
  stable := by
    intro first later state action order found
    cases state with
    | inl index => exact found
    | inr body =>
      rcases body with ⟨index, pc⟩
      cases observed : (programAt index).atStage (first - (index + 1)) pc with
      | none => simp [tapeStep, observed] at found
      | some inst =>
        have still := (programAt index).stable (Nat.sub_le_sub_right order (index + 1)) observed
        simpa only [tapeStep, still, observed] using found

private theorem output_body (stage index fuel pc : Nat) (tape : List Bool) :
    output (tapeStep stage) fuel (.inr (index, pc)) tape =
      output ((programAt index).atStage (stage - (index + 1))) fuel pc tape := by
  induction fuel generalizing pc tape with
  | zero => rfl
  | succ fuel ih =>
    cases found : (programAt index).atStage (stage - (index + 1)) pc with
    | none => simp [output, tapeStep, found]
    | some inst =>
      cases inst with
      | silent next => simp [output, tapeStep, found, withIndex, ih]
      | read no yes =>
        cases tape with
        | nil => simp [output, tapeStep, found, withIndex]
        | cons bit rest => cases bit <;> simp [output, tapeStep, found, withIndex, ih]
      | emit bit next => simp [output, tapeStep, found, withIndex, ih]

private theorem output_header (stage start : Nat) (tape : List Bool)
    (budget : stage = start + tape.length) :
    output (tapeStep stage) tape.length (.inl start) tape =
      match readDescriptionFrom start tape with
      | none => []
      | some (index, rest) => (programAt index).cut rest.length rest := by
  induction tape generalizing start with
  | nil => rfl
  | cons bit rest ih =>
    cases bit with
    | false =>
      have remaining : stage - (start + 1) = rest.length := by
        simp only [List.length_cons] at budget
        omega
      have initial : (programAt start).initial = 0 := rfl
      simp only [List.length_cons, output, tapeStep, Bool.false_eq_true, if_false,
        readDescriptionFrom, output_body, Generator.cut, remaining, initial]
    | true =>
      simpa only [List.length_cons, output, tapeStep, if_true, readDescriptionFrom] using
        ih (start + 1) (by simp at budget ⊢; omega)

/-- For a nonempty history the two ways of evaluating the same bounded
observer agree exactly. The empty history holds even before a header is read. -/
theorem stageMass_eq_tapeGenerator (history : List Bool) (nonempty : history ≠ []) (stage : Nat) :
    stageMass history stage = tapeGenerator.stageMass history stage := by
  have counts : tapeGenerator.count history stage = stageNumerator history stage := by
    rw [stageNumerator_eq_tape_count, Generator.count_eq_filter, List.countP_eq_length_filter]
    congr 1
    apply List.filter_congr
    intro tape present
    have length := length_eq_of_mem_bitstringsOfLength present
    have run := output_header stage 0 tape (by simpa only [Nat.zero_add] using length.symm)
    have cut : tapeGenerator.cut stage tape =
        match readDescriptionFrom 0 tape with
        | none => []
        | some (index, rest) => (programAt index).cut rest.length rest := by
      simpa only [Generator.cut, tapeGenerator, length] using run
    rw [cut]
    cases h : readDescriptionFrom 0 tape with
    | none =>
      cases history with
      | nil => exact (nonempty rfl).elim
      | cons bit rest => simp [tapeAcceptsFrom, h]
    | some body => rcases body with ⟨index, rest⟩; simp [tapeAcceptsFrom, h]
  simp only [stageMass, Generator.stageMass, counts]

/-- The countable Bayesian mixture is the emitted-prefix law of a single
generator on the fair tape. -/
theorem mixture_eq_tapeGenerator (history : List Bool) :
    mixture history = tapeGenerator.semimeasure history := by
  cases history with
  | nil => rw [mixture_nil, Generator.semimeasure_nil]
  | cons bit rest =>
    rw [← ENNReal.toReal_eq_toReal_iff' (mixture.ne_top _) (tapeGenerator.semimeasure.ne_top _)]
    have limit := stageMass_tendsto (bit :: rest)
    simp only [stageMass_eq_tapeGenerator (bit :: rest) (by simp)] at limit
    exact tendsto_nhds_unique limit (tapeGenerator.toReal_stageMass_tendsto (bit :: rest))

end Mettapedia.UniversalAI.UniversalPrediction.BitProgramMixture
