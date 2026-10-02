import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

/-!
# Induction and composition for recursive synthesis

Public source: Petra Hozzova, Daneshvar Amrollahi, Marton Hajdu, Laura Kovacs,
Andrei Voronkov, and Eva Maria Wagner, *Synthesis of Recursive Programs in
Saturation*, IJCAR 2024, https://doi.org/10.1007/978-3-031-63498-7_10.

This Lean reconstruction proves the natural-number magic induction formula
(Section 5, equation 6), the constructive witness principle for Definition 1,
the double/half example from Section 1, and the conditional-program composition
result of Theorem 10. The programs and branch tests are executable Lean data.
Clausification, rec-symbols, and the saturation search procedure are not modeled.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.Saturation.RecursiveSynthesis

universe u v

variable {Output : Type u}

/-- Equation 6 is a theorem of structural induction, not an added axiom. -/
theorem magic_nat (G : Nat -> Output -> Prop)
    (base : exists output, G 0 output)
    (step : forall n, (exists output, G n output) -> exists output, G (n + 1) output) :
    forall n, exists output, G n output := by
  intro n
  induction n with
  | zero => exact base
  | succ n ih => exact step n ih

/-- The primitive recursion operator of Definition 1. -/
def primitiveRecursion (base : Output) (step : Nat -> Output -> Output) :
    Nat -> Output
  | 0 => base
  | n + 1 => step n (primitiveRecursion base step n)

/-- Explicit base and step programs supply a correct executable witness. -/
theorem primitiveRecursion_correct (G : Nat -> Output -> Prop)
    (base : Output) (step : Nat -> Output -> Output)
    (base_correct : G 0 base)
    (step_correct : forall n output, G n output -> G (n + 1) (step n output)) :
    forall n, G n (primitiveRecursion base step n) := by
  intro n
  induction n with
  | zero => exact base_correct
  | succ n ih => exact step_correct n _ ih

/-- The natural-number interpretation of the public half specification. -/
def half (n : Nat) : Nat := n / 2

/-- The program from Section 1, equation 1, built with Definition 1. -/
def double : Nat -> Nat := primitiveRecursion 0 (fun _ output => output + 2)

theorem half_zero : half 0 = 0 := rfl

theorem half_one : half 1 = 0 := rfl

theorem half_step (n : Nat) : half (n + 2) = half n + 1 := by
  unfold half
  omega

theorem double_correct : forall n, half (double n) = n := by
  apply primitiveRecursion_correct (fun n output => half output = n)
  · rfl
  · intro n output h
    rw [half_step, h]

theorem double_eq (n : Nat) : double n = 2 * n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change double n + 2 = 2 * (n + 1)
    omega

/-- The specification is a right inverse; it does not imply a left inverse. -/
theorem half_double_not_left_inverse : double (half 1) ≠ 1 := by
  decide

variable {Input : Type v}

/-- A recorded conditional program: its witness applies when its clause is false. -/
structure Branch (Input : Type v) (Output : Type u) where
  clause : Input -> Bool
  program : Input -> Output

/-- The nested conditional program in Theorem 10; the final branch is a default. -/
def compose (branches : List (Branch Input Output)) (last : Branch Input Output)
    (input : Input) : Output :=
  match branches with
  | [] => last.program input
  | first :: rest =>
    if first.clause input then compose rest last input else first.program input

def AllClauses (branches : List (Branch Input Output)) (input : Input) : Prop :=
  forall branch, branch ∈ branches -> branch.clause input = true

/-- Each branch is correct under the clauses of all earlier branches. -/
inductive BranchChain (spec : Input -> Output -> Prop) :
    (Input -> Prop) -> List (Branch Input Output) -> Branch Input Output -> Prop where
  | last {assumptions : Input -> Prop} {branch : Branch Input Output}
      (correct : forall input, assumptions input -> branch.clause input = false ->
        spec input (branch.program input)) : BranchChain spec assumptions [] branch
  | next {assumptions : Input -> Prop} {first last : Branch Input Output}
      {rest : List (Branch Input Output)}
      (correct : forall input, assumptions input -> first.clause input = false ->
        spec input (first.program input))
      (tail : BranchChain spec
        (fun input => assumptions input /\ first.clause input = true) rest last) :
      BranchChain spec assumptions (first :: rest) last

/-- Theorem 10: branch correctness and joint clause inconsistency imply correctness
of the composed program. No correctness premise for the composed program is assumed. -/
theorem compose_correct {spec : Input -> Output -> Prop}
    {assumptions : Input -> Prop} {branches : List (Branch Input Output)}
    {last : Branch Input Output} (chain : BranchChain spec assumptions branches last)
    (coverage : forall input, assumptions input -> AllClauses branches input ->
      last.clause input ≠ true) :
    forall input, assumptions input -> spec input (compose branches last input) := by
  induction chain with
  | @last assumptions branch correct =>
    intro input h
    have notTrue := coverage input h (by simp [AllClauses])
    cases test : branch.clause input with
    | false => exact correct input h test
    | true => exact False.elim (notTrue test)
  | @next assumptions first last rest correct tail ih =>
    intro input h
    cases test : first.clause input with
    | false => simpa [compose, test] using correct input h test
    | true =>
      have restCoverage : forall input,
          assumptions input /\ first.clause input = true -> AllClauses rest input ->
            last.clause input ≠ true := by
        intro next hn clauses
        apply coverage next hn.1
        intro branch member
        rcases List.mem_cons.mp member with equal | member
        · subst branch
          exact hn.2
        · exact clauses branch member
      simpa [compose, test] using ih restCoverage input ⟨h, test⟩

namespace MaximumExample

def first : Branch (Nat × Nat) Nat where
  clause input := decide (input.1 < input.2)
  program input := input.1

def last : Branch (Nat × Nat) Nat where
  clause input := decide (input.2 < input.1)
  program input := input.2

def spec (input : Nat × Nat) (output : Nat) : Prop :=
  input.1 <= output /\ input.2 <= output /\
    (output = input.1 \/ output = input.2)

theorem correct (input : Nat × Nat) : spec input (compose [first] last input) := by
  by_cases bound : input.1 < input.2
  · simpa [compose, first, last, bound, spec] using Nat.le_of_lt bound
  · simpa [compose, first, last, bound, spec] using Nat.le_of_not_gt bound

def uncovered : Branch Nat Nat where
  clause input := decide (input = 1)
  program input := if input = 1 then 0 else input

/-- A conditional branch can be correct whenever its condition applies, yet
produce a wrong default at an input that its condition leaves uncovered. -/
theorem default_needs_coverage :
    (forall input, uncovered.clause input = false -> uncovered.program input = input) /\
      compose ([] : List (Branch Nat Nat)) uncovered 1 ≠ 1 := by
  constructor
  · intro input condition
    have different : input ≠ 1 := by simpa [uncovered] using condition
    simp [uncovered, different]
  · decide

end MaximumExample

end Mettapedia.Logic.Saturation.RecursiveSynthesis
