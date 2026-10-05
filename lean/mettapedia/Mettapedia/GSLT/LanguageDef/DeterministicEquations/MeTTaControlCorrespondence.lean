import Mettapedia.GSLT.LanguageDef.DeterministicEquations.MeTTaEmit
import Mettapedia.Languages.MeTTa.HE.Spec.Eval

/-!
# Generated control in the independent minimal MeTTa semantics

The emitter uses explicit sequencing and first-match selection. These laws
connect those instructions to the existing evaluator and ordered switch
relations. Guest computations, host primitives, and equation-query freshness
are separate premises when composing a complete execution theorem.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.DeterministicEquations.MeTTaEmit.Control

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE (Space Bindings ResultPair)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Minimal
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Steps

variable {space : Space} {dispatch : GroundedDispatch} {live : List Atom}
  {typing : EvalTypeService}

theorem body_terminal_iff {atom : Atom} {incoming : Bindings} {result : ResultPair}
    (terminal : embeddedInstruction atom = false) :
    CoreFunctionBodyRel space dispatch live atom incoming result (typing := typing) ↔
      result = (atom, incoming) := by
  constructor
  · intro execution
    cases execution with
    | terminal => rfl
    | resume _ _ _ _ _ instruction => simp [terminal] at instruction
  · rintro rfl
    exact .terminal space atom incoming terminal

theorem body_returned_iff (atom : Atom) (incoming : Bindings) (result : ResultPair) :
    CoreFunctionBodyRel space dispatch live (returned atom) incoming result (typing := typing) ↔
      result = (returned atom, incoming) := by
  apply body_terminal_iff
  simp [returned, call, embeddedInstruction]

theorem function_returns {body atom : Atom} {incoming output : Bindings}
    (shape : ∃ items, body = .expression items)
    (execution : CoreFunctionBodyRel space dispatch live body incoming
      (returned atom, output) (typing := typing)) :
    CoreRunRel space dispatch live (call "function" [body]) incoming (atom, output)
      (typing := typing) := by
  apply CoreRunRel.instruction
  · simp [call, embeddedInstruction]
  · simp [call, Minimal.IsChain]
  · exact .functionReturn space body atom incoming output shape execution

/-- A completed instruction can be followed by the rest of a function body. -/
theorem body_of_run {atom : Atom} {incoming : Bindings} {middle result : ResultPair}
    (execution : CoreRunRel space dispatch live atom incoming middle (typing := typing))
    (continuation : CoreFunctionBodyRel space dispatch live middle.1 middle.2 result
      (typing := typing)) :
    CoreFunctionBodyRel space dispatch live atom incoming result (typing := typing) := by
  cases execution with
  | data => exact continuation
  | instruction _ _ _ _ embedded nonchain step =>
      exact .resume space _ _ _ _ embedded (.instruction _ _ _ _ embedded nonchain step)
        continuation
  | chain _ _ _ _ _ chain step rest =>
      have embedded : embeddedInstruction atom = true := by
        obtain ⟨tail, rfl⟩ := chain
        simp [embeddedInstruction]
      exact .resume space _ _ _ _ embedded (.chain _ _ _ _ _ chain step rest) continuation

theorem body_decompose {atom : Atom} {incoming : Bindings} {result : ResultPair}
    (execution : CoreFunctionBodyRel space dispatch live atom incoming result
      (typing := typing)) :
    ∃ middle, CoreRunRel space dispatch live atom incoming middle (typing := typing) ∧
      CoreFunctionBodyRel space dispatch live middle.1 middle.2 result (typing := typing) := by
  cases execution with
  | terminal _ _ _ terminal =>
      exact ⟨_, .data _ _ _ terminal, .terminal _ _ _ terminal⟩
  | resume _ _ _ middle _ _ execution continuation =>
      exact ⟨middle, execution, continuation⟩

/-- Sequencing runs its operand once, substitutes that result, and continues. -/
theorem body_chain_iff (source : Atom) (name : String) (template : Atom)
    (incoming : Bindings) (result : ResultPair) :
    CoreFunctionBodyRel space dispatch live (call "chain" [source, .var name, template])
      incoming result (typing := typing) ↔
      ∃ value output,
        CoreRunRel space dispatch live source incoming (value, output) (typing := typing) ∧
        CoreFunctionBodyRel space dispatch live (substituteName name value template)
          output result (typing := typing) := by
  constructor
  · intro execution
    cases execution with
    | terminal _ _ _ terminal => simp [call, embeddedInstruction] at terminal
    | resume _ _ _ middle _ _ execution continuation =>
        cases execution with
        | data _ _ _ terminal => simp [call, embeddedInstruction] at terminal
        | instruction _ _ _ _ _ nonchain => simp [call, Minimal.IsChain] at nonchain
        | chain _ _ _ _ _ _ step rest =>
            generalize sourceCode : call "chain" [source, .var name, template] = code at step
            cases step <;> simp_all [call]
            exact ⟨_, _, by assumption, body_of_run rest continuation⟩
  · rintro ⟨value, output, execution, continuation⟩
    obtain ⟨middle, run, rest⟩ := body_decompose continuation
    apply CoreFunctionBodyRel.resume space _ incoming middle result
    · simp [call, embeddedInstruction]
    · apply CoreRunRel.chain
      · exact ⟨_, rfl⟩
      · exact .chain space source name template incoming (value, output) execution
      · exact run
    · exact rest

theorem run_unify_iff (target pattern yes no : Atom) (incoming : Bindings)
    (result : ResultPair) :
    CoreRunRel space dispatch live (call "unify" [target, pattern, yes, no]) incoming
      result (typing := typing) ↔
      UnifyStep target pattern yes no incoming result.1 result.2 := by
  constructor
  · intro execution
    cases execution with
    | data _ _ _ terminal => simp [call, embeddedInstruction] at terminal
    | instruction _ _ _ _ _ _ step =>
        generalize sourceCode : call "unify" [target, pattern, yes, no] = code at step
        cases step <;> simp_all [call]
    | chain _ _ _ _ _ chain => simp [call, Minimal.IsChain] at chain
  · intro selected
    apply CoreRunRel.instruction
    · simp [call, embeddedInstruction]
    · simp [call, Minimal.IsChain]
    · exact .unify space target pattern yes no result.1 incoming result.2 selected

theorem body_unify_iff (target pattern yes no : Atom) (incoming : Bindings)
    (result : ResultPair) :
    CoreFunctionBodyRel space dispatch live (call "unify" [target, pattern, yes, no])
      incoming result (typing := typing) ↔
      ∃ emitted output, UnifyStep target pattern yes no incoming emitted output ∧
        CoreFunctionBodyRel space dispatch live emitted output result (typing := typing) := by
  constructor
  · intro execution
    cases execution with
    | terminal _ _ _ terminal => simp [call, embeddedInstruction] at terminal
    | resume _ _ _ middle _ _ execution continuation =>
        exact ⟨middle.1, middle.2, (run_unify_iff _ _ _ _ _ _).mp execution, continuation⟩
  · rintro ⟨emitted, output, selected, continuation⟩
    exact body_of_run ((run_unify_iff target pattern yes no incoming (emitted, output)).mpr selected) continuation

/-- Exact operational meaning of the emitter's shared ordered branch scan.
The scan relation predates this emitter and does not refer to its syntax. -/
theorem body_select_iff (target : Atom) (branches : List (Atom × Atom)) (otherwise : Atom)
    (incoming : Bindings) (result : ResultPair) :
    CoreFunctionBodyRel space dispatch live (selectBranches target branches otherwise)
      incoming result (typing := typing) ↔
      (SwitchRawRel target incoming (branches.map fun (pattern, body) =>
        .expression [pattern, body]) .noMatch ∧
        CoreFunctionBodyRel space dispatch live otherwise incoming result (typing := typing)) ∨
      ∃ emitted output,
        SwitchRawRel target incoming (branches.map fun (pattern, body) =>
          .expression [pattern, body]) (.selected emitted output) ∧
        CoreFunctionBodyRel space dispatch live emitted output result (typing := typing) := by
  induction branches with
  | nil =>
      simp only [selectBranches, List.foldr_nil, List.map_nil]
      constructor
      · intro execution
        exact Or.inl ⟨.nil, execution⟩
      · rintro (⟨_, execution⟩ | ⟨_, _, impossible, _⟩)
        · exact execution
        · cases impossible
  | cons row rest ih =>
      rcases row with ⟨pattern, body⟩
      simp only [selectBranches, List.foldr_cons, List.map_cons]
      rw [body_unify_iff]
      constructor
      · rintro ⟨emitted, output, step, execution⟩
        cases step with
        | success selected => exact Or.inr ⟨emitted, output, .hit selected, execution⟩
        | noMatch refused =>
            rcases ih.mp execution with ⟨none, run⟩ | ⟨chosen, frame, scan, run⟩
            · exact Or.inl ⟨.miss refused none, run⟩
            · exact Or.inr ⟨chosen, frame, .miss refused scan, run⟩
      · rintro (⟨scan, run⟩ | ⟨chosen, frame, scan, run⟩)
        · cases scan with
          | malformed bad => exact False.elim (bad pattern body rfl)
          | miss refused rest => exact ⟨_, _, .noMatch refused, ih.mpr (Or.inl ⟨rest, run⟩)⟩
        · cases scan with
          | malformed bad => exact False.elim (bad pattern body rfl)
          | hit selected => exact ⟨chosen, frame, .success selected, run⟩
          | miss refused rest =>
              exact ⟨_, _, .noMatch refused, ih.mpr (Or.inr ⟨chosen, frame, rest, run⟩)⟩

/-- Once a row is viable, later rows cannot be retried because of its result. -/
theorem body_first_viable_iff (target pattern body : Atom) (rest : List (Atom × Atom))
    (otherwise : Atom) (incoming : Bindings) (result : ResultPair)
    (viable : ∃ output, UnifyCandidateRel target pattern incoming output) :
    CoreFunctionBodyRel space dispatch live
      (selectBranches target ((pattern, body) :: rest) otherwise)
      incoming result (typing := typing) ↔
      ∃ emitted output, UnifySuccessRel target pattern body incoming emitted output ∧
        CoreFunctionBodyRel space dispatch live emitted output result (typing := typing) := by
  simp only [selectBranches, List.foldr_cons, body_unify_iff]
  constructor
  · rintro ⟨emitted, output, selected, execution⟩
    cases selected with
    | success selected => exact ⟨emitted, output, selected, execution⟩
    | noMatch refused =>
        obtain ⟨output, candidate⟩ := viable
        exact False.elim (refused output candidate)
  · rintro ⟨emitted, output, selected, execution⟩
    exact ⟨emitted, output, .success selected, execution⟩

/-- Returned expressions are data, even when their head names a recursive call. -/
theorem returns_callable_data (head : String) (arguments : List Atom) (incoming : Bindings) :
    CoreRunRel space dispatch live
      (call "function" [returned (call head arguments)]) incoming
      (call head arguments, incoming) (typing := typing) := by
  apply function_returns ⟨_, rfl⟩
  exact (body_returned_iff _ _ _).mpr rfl

/-- Sequencing can return its input without interpreting that input as code. -/
theorem sequence_returned_data (head : String) (arguments : List Atom) (name : String)
    (incoming : Bindings) :
    CoreFunctionBodyRel space dispatch live
      (call "chain" [call "function" [returned (call head arguments)], .var name,
        returned (.var name)]) incoming
      (returned (call head arguments), incoming) (typing := typing) := by
  rw [body_chain_iff]
  refine ⟨call head arguments, incoming, returns_callable_data head arguments incoming, ?_⟩
  simpa [returned, call, substituteName] using
    (body_returned_iff (space := space) (dispatch := dispatch) (live := live) (typing := typing)
      (call head arguments) incoming (returned (call head arguments), incoming)).mpr rfl

/-- Absence of a syntactic return cannot be repaired by treating data as code. -/
theorem bare_data_is_not_a_return (head : String) (arguments : List Atom)
    (incoming output : Bindings) (value : Atom)
    (data : embeddedInstruction (call head arguments) = false)
    (notReturn : head ≠ "return") :
    ¬ CoreFunctionBodyRel space dispatch live (call head arguments) incoming
      (returned value, output) (typing := typing) := by
  rw [body_terminal_iff data]
  simp [returned, call, Ne.symm notReturn]

end Mettapedia.GSLT.LanguageDef.DeterministicEquations.MeTTaEmit.Control
