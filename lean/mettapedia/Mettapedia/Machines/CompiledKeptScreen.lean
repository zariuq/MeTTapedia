import Mathlib.Tactic

/-!
# Compiling conservative tests on kept-row coordinates

The source classifies the resolved pattern at each candidate. The compiler
keeps only constrained coordinates, recording a typed key once. Applying that
program is the same conservative test. A bounded prefix of the program can
only admit more candidates. This concerns tests within one fetch: resolved
syntax must remain live and unchanged until that fetch returns.

Native constructor recognition, coordinate projection and correspondence to
unification remain obligations of the adapter using these tests.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.CompiledKeptScreen

inductive Pattern where
  | variable
  | symbol (name : ℕ)
  | integer (value : ℤ)
  | arity (length : ℕ)
  | other
  deriving DecidableEq

inductive Header where
  | symbol (name : ℕ)
  | integer (value : ℤ)
  | ordinary (length : ℕ)
  | unknown
  deriving DecidableEq

inductive Key where
  | symbol (name : ℕ)
  | integer (value : ℤ)
  | arity (length : ℕ)
  deriving DecidableEq

def sourceMay : Pattern → Header → Bool
  | .symbol a, .symbol b => a == b
  | .integer a, .integer b => a == b
  | .arity a, .ordinary b => a == b
  | _, _ => true

def compileKey : Pattern → Option Key
  | .symbol name => some (.symbol name)
  | .integer value => some (.integer value)
  | .arity length => some (.arity length)
  | _ => none

def applyKey : Key → Header → Bool
  | .symbol a, .symbol b => a == b
  | .integer a, .integer b => a == b
  | .arity a, .ordinary b => a == b
  | _, _ => true

abbrev Field := ℕ × Pattern
abbrev Probe := ℕ × Key

def source (fields : List Field) (row : ℕ → Header) : Bool :=
  fields.all (fun field => sourceMay field.2 (row field.1))

def compile (fields : List Field) : List Probe :=
  fields.filterMap (fun field => (compileKey field.2).map (field.1, ·))

def apply (probes : List Probe) (row : ℕ → Header) : Bool :=
  probes.all (fun probe => applyKey probe.2 (row probe.1))

theorem compile_correct (fields : List Field) (row : ℕ → Header) :
    apply (compile fields) row = source fields row := by
  induction fields with
  | nil => rfl
  | cons field fields ih =>
    obtain ⟨position, pattern⟩ := field
    cases pattern <;>
      simp [compile, compileKey, apply, source, sourceMay, applyKey] at ih ⊢ <;>
      rw [ih] <;> cases row position <;> rfl

theorem prefix_conservative (fields : List Field) (row : ℕ → Header) (budget : ℕ)
    (passes : source fields row = true) :
    apply ((compile fields).take budget) row = true := by
  rw [← compile_correct] at passes
  rw [apply, List.all_eq_true] at passes ⊢
  intro probe member
  exact passes probe (List.mem_of_mem_take member)

theorem compiled_length_le (fields : List Field) :
    (compile fields).length ≤ fields.length :=
  List.length_filterMap_le ..

theorem inspections_le (fields : List Field) (compileBudget probeBudget : ℕ) :
    ((compile (fields.take compileBudget)).take probeBudget).length ≤ probeBudget := by
  simp only [List.length_take]
  exact Nat.min_le_left _ _

example : apply (compile [(0, .variable), (1, .symbol 3)])
    (fun _ => .symbol 3) = true := by decide

example : apply (compile [(0, .variable), (1, .symbol 3)])
    (fun _ => .symbol 4) = false := by decide

/-- An unavailable header remains a candidate; the tests grant no equality. -/
example : apply (compile [(1, .integer 3), (2, .arity 2)])
    (fun _ => .unknown) = true := by decide

end Mettapedia.Machines.CompiledKeptScreen
