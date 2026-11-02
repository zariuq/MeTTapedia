import Mettapedia.GSLT.Dynamics.RegionPortfolio
import Mettapedia.Logic.BDD.SymbolicCTL

/-!
# Symbolic fixed-point pages as certified regions

The reference executes set operations and tests equality of sets. The worker
executes the independently defined BDD operator and diagram equality test.
Decoding preserves whether the page paused or completed, the approximation
and its exact solver-pass count. Pausing is an ordinary resumable result here,
never a decline or a negative CTL answer.

This adapter preserves the existing finite symbolic solver's semantics. It
does not yet extract nested CTL formulas from PeTTa source, certify native
diagram memory or identify solver passes with source-language rounds.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.ObservationQualified.Symbolic

open Mettapedia.Logic.BDDCore
open StatePredicates FixedPointSolver

abbrev SetFrame (n : Nat) := Set (State n) × Nat

/-- Left is paused; right is completed. Both retain the current set and the
number of operator applications already performed. -/
abbrev SetResult (n : Nat) := Sum (SetFrame n) (SetFrame n)

def decodeFrame {n : Nat} (frame : Frame n) : SetFrame n :=
  (denote frame.current, frame.passes)

def decodeResult {n : Nat} : FixedPointSolver.Result n → SetResult n
  | .paused frame => .inl (decodeFrame frame)
  | .done frame => .inr (decodeFrame frame)

/-- Representation-independent set iteration, with a semantic equality test.
The reference is mathematical; the executable worker decides equality by the
BDD theorem. -/
noncomputable def referenceAdvance {n : Nat} (meaning : Set (State n) → Set (State n)) :
    Nat → SetFrame n → SetResult n := by
  classical
  exact fun fuel initial => match fuel with
    | 0 => .inl initial
    | fuel + 1 =>
        let next := meaning initial.1
        if initial.1 = next then .inr (initial.1, initial.2 + 1)
        else referenceAdvance meaning fuel (next, initial.2 + 1)

theorem advance_refines {n : Nat} (operator : Operator n) (fuel : Nat) (initial : Frame n) :
    decodeResult (advance operator fuel initial) =
      referenceAdvance operator.meaning fuel (decodeFrame initial) := by
  induction fuel generalizing initial with
  | zero => rfl
  | succ fuel ih =>
      have equal : equivalent initial.current (operator.step initial.current) = true ↔
          denote initial.current = operator.meaning (denote initial.current) := by
        rw [equivalent_denote, operator.refines]
      by_cases stable : equivalent initial.current (operator.step initial.current) = true
      · rw [advance, if_pos stable, referenceAdvance]
        change Sum.inr (denote initial.current, initial.passes + 1) =
          if denote initial.current = operator.meaning (denote initial.current) then
            Sum.inr (denote initial.current, initial.passes + 1)
          else referenceAdvance operator.meaning fuel
            (operator.meaning (denote initial.current), initial.passes + 1)
        rw [if_pos (equal.mp stable)]
      · have unequal : denote initial.current ≠ operator.meaning (denote initial.current) :=
          fun same => stable (equal.mpr same)
        rw [advance, if_neg stable, ih, referenceAdvance]
        simp only [decodeFrame, operator.refines, unequal, ↓reduceIte]

def questions (n : Nat) : RegionObservations.Family (SetResult n) where
  Question := SetResult n → Bool
  Answer _ := Bool
  read question result := question result

noncomputable def boundary {n : Nat} (operator : Operator n) :
    Boundary (Frame n × Nat) (SetResult n) (SetResult n) where
  source input := referenceAdvance operator.meaning input.2 (decodeFrame input.1)
  summarize := id
  future := questions n
  sufficient _ _ same _ := congrArg _ same

noncomputable def region {n : Nat} (operator : Operator n) :
    CertifiedRegion (boundary operator) Nat where
  regime := 0
  Artifact := FixedPointSolver.Result n
  attempt input := .committed (advance operator input.2 input.1)
  decode := decodeResult
  restores _ _ impossible := by cases impossible
  exact input _ committed := by
    cases committed
    exact advance_refines operator input.2 input.1

/-- Reaching the page boundary returns the actual partial diagram and count;
it neither restarts nor pretends to have decided the fixed point. -/
theorem paused_page_is_not_refusal {n : Nat} (operator : Operator n) (frame : Frame n) :
    (region operator).attempt (frame, 0) = .committed (.paused frame) := rfl

theorem split_keeps_residual_and_count {n : Nat} (operator : Operator n)
    (first later : Nat) (frame : Frame n) :
    decodeResult (resume operator later (advance operator first frame)) =
      referenceAdvance operator.meaning (first + later) (decodeFrame frame) := by
  rw [resume_split, advance_refines]

/-- The generic page certificate includes the temporal until operator and its
independently defined finite-path semantics, without specializing its syntax. -/
theorem until_completed_path {n : Nat} {domain : Diagram n} (program : StateTransducer.Certified n domain)
    (holds goal : Diagram n) (fuel : Nat) (final : Frame n)
    (completed : SymbolicCTL.untilRun program holds goal fuel = .done final) (state : State n) :
    state ∈ (decodeFrame final).1 ↔
      Mettapedia.Logic.CTLFixedPoints.Until (StateTransducer.Relation domain program.rules)
        (denote (StateTransducer.within domain holds))
        (denote (StateTransducer.within domain goal)) state :=
  SymbolicCTL.until_complete_iff_path program holds goal fuel final completed state

theorem globally_completed_path {n : Nat} {domain : Diagram n}
    (program : StateTransducer.Certified n domain) (holds : Diagram n)
    (fuel : Nat) (final : Frame n)
    (completed : SymbolicCTL.globallyRun program holds fuel = .done final) (state : State n) :
    state ∈ (decodeFrame final).1 ↔
      Mettapedia.Logic.CTLFixedPoints.Globally (StateTransducer.Relation domain program.rules)
        (denote (StateTransducer.within domain holds)) state :=
  SymbolicCTL.globally_complete_iff_path program holds fuel final completed state

namespace Controls

/-- The operator adds every state in one iteration, then stabilizes. -/
def fill : Operator 1 where
  step _ := truth 1
  meaning := ⟨fun _ => Set.univ, fun _ _ _ => le_rfl⟩
  refines _ := by
    change denote (truth 1) = Set.univ
    ext state
    simp [denote, truth, BDD.satSet]

def initial : Frame 1 := ⟨falsity 1, 7⟩

theorem first_page : advance fill 1 initial = .paused ⟨truth 1, 8⟩ := by
  simp [advance, fill, initial, equivalent, falsity, truth, Mettapedia.Logic.BDDCore.apply]

theorem second_page : resume fill 1 (advance fill 1 initial) = .done ⟨truth 1, 9⟩ := by
  rw [first_page]
  simp [resume, advance, fill, equivalent, truth, Mettapedia.Logic.BDDCore.apply]

theorem first_page_pauses :
    (advance fill 1 initial).finished = false ∧
      (advance fill 1 initial).frame.passes = 8 := by rw [first_page]; exact ⟨rfl, rfl⟩

theorem second_page_finishes :
    (resume fill 1 (advance fill 1 initial)).finished = true ∧
      (resume fill 1 (advance fill 1 initial)).frame.passes = 9 := by
  rw [second_page]
  exact ⟨rfl, rfl⟩

theorem same_set_is_not_same_completion :
    (decodeFrame (advance fill 1 initial).frame).1 =
      (decodeFrame (resume fill 1 (advance fill 1 initial)).frame).1 ∧
      decodeResult (advance fill 1 initial) ≠
        decodeResult (resume fill 1 (advance fill 1 initial)) := by
  rw [second_page, first_page]
  constructor
  · rfl
  · intro impossible
    cases impossible

end Controls

#print axioms advance_refines
#print axioms region
#print axioms split_keeps_residual_and_count
#print axioms until_completed_path
#print axioms globally_completed_path

end Mettapedia.GSLT.Dynamics.ObservationQualified.Symbolic
