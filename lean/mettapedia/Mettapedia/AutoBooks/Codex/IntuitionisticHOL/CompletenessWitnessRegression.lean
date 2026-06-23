import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.Completeness

namespace Mettapedia.AutoBooks.Codex.IntuitionisticHOL.CompletenessWitnessRegression

open Mettapedia.Logic.HOL

inductive BaseSort where
  | atom
  deriving DecidableEq

inductive DemoConst : Ty BaseSort → Type where
  | left : DemoConst (.base .atom)
  | right : DemoConst (.base .atom)
  deriving DecidableEq

def atomTy : Ty BaseSort := .base .atom

def witnessBody : Formula DemoConst [atomTy] :=
  .eq (.var .vz) (.var .vz)

def leftTerm : Term DemoConst [] atomTy :=
  .const DemoConst.left

def rightTerm : Term DemoConst [] atomTy :=
  .const DemoConst.right

def leftWitnessFormula : Formula DemoConst [] :=
  instantiate (Base := BaseSort) leftTerm witnessBody

def rightWitnessFormula : Formula DemoConst [] :=
  instantiate (Base := BaseSort) rightTerm witnessBody

def witnessConflictState : SaturationSearchState DemoConst [] where
  frontier :=
    { antecedents := [(.ex witnessBody : Formula DemoConst [])]
      succedent := leftWitnessFormula }
  hintikka :=
    { formulas :=
        [ (Sign.trueE, (.ex witnessBody : Formula DemoConst []))
        , (Sign.falseE, leftWitnessFormula)
        , (Sign.falseE, rightWitnessFormula) ] }
  agenda := []

def witnessOpenState : SaturationSearchState DemoConst [] where
  frontier :=
    { antecedents := [(.ex witnessBody : Formula DemoConst [])]
      succedent := leftWitnessFormula }
  hintikka :=
    { formulas := [(Sign.trueE, (.ex witnessBody : Formula DemoConst []))] }
  agenda := []

def positiveWitnessConflictState : SaturationSearchState DemoConst [] where
  frontier :=
    { antecedents := [(.all witnessBody : Formula DemoConst [])]
      succedent := leftWitnessFormula }
  hintikka :=
    { formulas :=
        [ (Sign.falseE, (.all witnessBody : Formula DemoConst []))
        , (Sign.trueE, leftWitnessFormula)
        , (Sign.trueE, rightWitnessFormula) ] }
  agenda := []

def positiveWitnessOpenState : SaturationSearchState DemoConst [] where
  frontier :=
    { antecedents := [(.all witnessBody : Formula DemoConst [])]
      succedent := leftWitnessFormula }
  hintikka :=
    { formulas := [(Sign.falseE, (.all witnessBody : Formula DemoConst []))] }
  agenda := []

theorem leftWitnessFormula_mem_closed :
    (Sign.falseE, leftWitnessFormula) ∈ witnessConflictState.hintikka.close.formulas := by
  exact HintikkaSet.mem_close_of_mem (by simp [witnessConflictState])

theorem rightWitnessFormula_mem_closed :
    (Sign.falseE, rightWitnessFormula) ∈ witnessConflictState.hintikka.close.formulas := by
  exact HintikkaSet.mem_close_of_mem (by simp [witnessConflictState])

theorem leftWitnessFormula_true_mem_closed :
    (Sign.trueE, leftWitnessFormula) ∈ positiveWitnessConflictState.hintikka.close.formulas := by
  exact HintikkaSet.mem_close_of_mem (by simp [positiveWitnessConflictState])

theorem rightWitnessFormula_true_mem_closed :
    (Sign.trueE, rightWitnessFormula) ∈ positiveWitnessConflictState.hintikka.close.formulas := by
  exact HintikkaSet.mem_close_of_mem (by simp [positiveWitnessConflictState])

theorem leftWitnessFormula_ne_bot :
    leftWitnessFormula ≠ (.bot : Formula DemoConst []) := by
  intro h
  cases h

theorem rightWitnessFormula_ne_bot :
    rightWitnessFormula ≠ (.bot : Formula DemoConst []) := by
  intro h
  cases h

theorem leftWitnessFormula_ne_top :
    leftWitnessFormula ≠ (.top : Formula DemoConst []) := by
  intro h
  cases h

theorem rightWitnessFormula_ne_top :
    rightWitnessFormula ≠ (.top : Formula DemoConst []) := by
  intro h
  cases h

theorem left_trueAll_not_compatible :
    ¬ witnessConflictState.DeterministicAdditionCompatible
      (.trueAll witnessBody leftTerm) := by
  exact SaturationSearchState.not_deterministicAdditionCompatible_trueAll
    witnessConflictState leftWitnessFormula_mem_closed

theorem left_trueAll_compatible_in_open_state :
    witnessOpenState.DeterministicAdditionCompatible
      (.trueAll witnessBody leftTerm) := by
  exact SaturationSearchState.deterministicAdditionCompatible_trueAll
    witnessOpenState (by
      change (Sign.falseE, leftWitnessFormula) ∉ witnessOpenState.hintikka.close.formulas
      intro h
      rw [HintikkaSet.close] at h
      simp [witnessOpenState] at h
      nomatch h)

theorem left_trueExWitness_not_compatible :
    ¬ witnessConflictState.DeterministicAdditionCompatible
      (.trueExWitness witnessBody leftTerm) := by
  exact SaturationSearchState.not_deterministicAdditionCompatible_trueExWitness
    witnessConflictState leftWitnessFormula_mem_closed

theorem right_trueExWitness_not_compatible :
    ¬ witnessConflictState.DeterministicAdditionCompatible
      (.trueExWitness witnessBody rightTerm) := by
  exact SaturationSearchState.not_deterministicAdditionCompatible_trueExWitness
    witnessConflictState rightWitnessFormula_mem_closed

theorem no_demo_constant_trueExWitness_compatible
    (c : DemoConst atomTy) :
    ¬ witnessConflictState.DeterministicAdditionCompatible
      (.trueExWitness witnessBody (.const c)) := by
  cases c with
  | left =>
      simpa [leftTerm] using left_trueExWitness_not_compatible
  | right =>
      simpa [rightTerm] using right_trueExWitness_not_compatible

theorem left_trueExWitness_compatible_in_open_state :
    witnessOpenState.DeterministicAdditionCompatible
      (.trueExWitness witnessBody leftTerm) := by
  exact SaturationSearchState.deterministicAdditionCompatible_trueExWitness
    witnessOpenState (by
      change (Sign.falseE, leftWitnessFormula) ∉ witnessOpenState.hintikka.close.formulas
      intro h
      rw [HintikkaSet.close] at h
      simp [witnessOpenState] at h
      nomatch h)

theorem right_trueExWitness_compatible_in_open_state :
    witnessOpenState.DeterministicAdditionCompatible
      (.trueExWitness witnessBody rightTerm) := by
  exact SaturationSearchState.deterministicAdditionCompatible_trueExWitness
    witnessOpenState (by
      change (Sign.falseE, rightWitnessFormula) ∉ witnessOpenState.hintikka.close.formulas
      intro h
      rw [HintikkaSet.close] at h
      simp [witnessOpenState] at h
      nomatch h)

theorem demo_constant_trueExWitness_compatible_in_open_state
    (c : DemoConst atomTy) :
    witnessOpenState.DeterministicAdditionCompatible
      (.trueExWitness witnessBody (.const c)) := by
  cases c with
  | left =>
      change witnessOpenState.DeterministicAdditionCompatible
        (.trueExWitness witnessBody leftTerm)
      exact left_trueExWitness_compatible_in_open_state
  | right =>
      change witnessOpenState.DeterministicAdditionCompatible
        (.trueExWitness witnessBody rightTerm)
      exact right_trueExWitness_compatible_in_open_state

theorem left_falseAllWitness_not_compatible :
    ¬ positiveWitnessConflictState.DeterministicAdditionCompatible
      (.falseAllWitness witnessBody leftTerm) := by
  exact SaturationSearchState.not_deterministicAdditionCompatible_falseAllWitness
    positiveWitnessConflictState leftWitnessFormula_true_mem_closed

theorem left_falseAllWitness_compatible_in_open_state :
    positiveWitnessOpenState.DeterministicAdditionCompatible
      (.falseAllWitness witnessBody leftTerm) := by
  exact SaturationSearchState.deterministicAdditionCompatible_falseAllWitness
    positiveWitnessOpenState (by
      change (Sign.trueE, leftWitnessFormula) ∉ positiveWitnessOpenState.hintikka.close.formulas
      intro h
      rw [HintikkaSet.close] at h
      simp [positiveWitnessOpenState] at h
      nomatch h)

theorem right_falseAllWitness_not_compatible :
    ¬ positiveWitnessConflictState.DeterministicAdditionCompatible
      (.falseAllWitness witnessBody rightTerm) := by
  exact SaturationSearchState.not_deterministicAdditionCompatible_falseAllWitness
    positiveWitnessConflictState rightWitnessFormula_true_mem_closed

theorem right_falseAllWitness_compatible_in_open_state :
    positiveWitnessOpenState.DeterministicAdditionCompatible
      (.falseAllWitness witnessBody rightTerm) := by
  exact SaturationSearchState.deterministicAdditionCompatible_falseAllWitness
    positiveWitnessOpenState (by
      change (Sign.trueE, rightWitnessFormula) ∉ positiveWitnessOpenState.hintikka.close.formulas
      intro h
      rw [HintikkaSet.close] at h
      simp [positiveWitnessOpenState] at h
      nomatch h)

theorem left_falseEx_not_compatible :
    ¬ positiveWitnessConflictState.DeterministicAdditionCompatible
      (.falseEx witnessBody leftTerm) := by
  exact SaturationSearchState.not_deterministicAdditionCompatible_falseEx
    positiveWitnessConflictState leftWitnessFormula_true_mem_closed

theorem left_falseEx_compatible_in_open_state :
    positiveWitnessOpenState.DeterministicAdditionCompatible
      (.falseEx witnessBody leftTerm) := by
  exact SaturationSearchState.deterministicAdditionCompatible_falseEx
    positiveWitnessOpenState (by
      change (Sign.trueE, leftWitnessFormula) ∉ positiveWitnessOpenState.hintikka.close.formulas
      intro h
      rw [HintikkaSet.close] at h
      simp [positiveWitnessOpenState] at h
      nomatch h)

theorem right_falseEx_not_compatible :
    ¬ positiveWitnessConflictState.DeterministicAdditionCompatible
      (.falseEx witnessBody rightTerm) := by
  exact SaturationSearchState.not_deterministicAdditionCompatible_falseEx
    positiveWitnessConflictState rightWitnessFormula_true_mem_closed

theorem right_falseEx_compatible_in_open_state :
    positiveWitnessOpenState.DeterministicAdditionCompatible
      (.falseEx witnessBody rightTerm) := by
  exact SaturationSearchState.deterministicAdditionCompatible_falseEx
    positiveWitnessOpenState (by
      change (Sign.trueE, rightWitnessFormula) ∉ positiveWitnessOpenState.hintikka.close.formulas
      intro h
      rw [HintikkaSet.close] at h
      simp [positiveWitnessOpenState] at h
      nomatch h)

end Mettapedia.AutoBooks.Codex.IntuitionisticHOL.CompletenessWitnessRegression
