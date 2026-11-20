import Mettapedia.Logic.WorldModel.Basic
import Mathlib.Data.NNRat.Defs
import Mathlib.Tactic

/-!
# Finite probabilistic programs and likelihood world states

A finite rational fragment with return, failure, probabilistic choice and
nonnegative scoring. Its expectation interpreter is exact and executable.
For a fixed generator, accumulated likelihoods form a monoidal world model.
Extraction is unnormalized expectation; normalized queries are partial at zero
mass. This multiplicative revision does not satisfy additive extraction.

This is a finite fragment, with no claim of recursion, continuous sampling,
universal program inference, or compilation to BN/BDD representations.
-/

set_option autoImplicit false

namespace Mettapedia.PLN.WorldModel.FiniteProbabilisticPrograms

inductive Program (α : Type) where
  | pure (value : α)
  | fail
  | choice (probability : ℚ≥0) (bounded : probability ≤ 1)
      (yes no : Program α)
  | score (weight : ℚ≥0) (body : Program α)

namespace Program

variable {α β : Type}

def expect : Program α → (α → ℚ≥0) → ℚ≥0
  | .pure value, f => f value
  | .fail, _ => 0
  | .choice p _ yes no, f => p * yes.expect f + (1 - p) * no.expect f
  | .score weight body, f => weight * body.expect f

def bind : Program α → (α → Program β) → Program β
  | .pure value, f => f value
  | .fail, _ => .fail
  | .choice p bounded yes no, f => .choice p bounded (yes.bind f) (no.bind f)
  | .score weight body, f => .score weight (body.bind f)

theorem expect_bind (program : Program α) (next : α → Program β) (f : β → ℚ≥0) :
    (program.bind next).expect f = program.expect (fun value => (next value).expect f) := by
  induction program with
  | pure value => rfl
  | fail => rfl
  | choice p bounded yes no iy ino => simp only [bind, expect, iy, ino]
  | score weight body ih => simp only [bind, expect, ih]

/-- Attach a likelihood to the generated value. -/
def observe (program : Program α) (likelihood : α → ℚ≥0) : Program α :=
  program.bind (fun value => .score (likelihood value) (.pure value))

theorem expect_observe (program : Program α) (likelihood f : α → ℚ≥0) :
    (program.observe likelihood).expect f =
      program.expect (fun value => likelihood value * f value) := by
  simp only [observe, expect_bind, expect]

theorem observe_sequence (program : Program α) (first second f : α → ℚ≥0) :
    ((program.observe first).observe second).expect f =
      (program.observe (fun value => first value * second value)).expect f := by
  simp only [expect_observe, mul_assoc]

theorem expect_add (program : Program α) (f g : α → ℚ≥0) :
    program.expect (fun value => f value + g value) = program.expect f + program.expect g := by
  induction program with
  | pure value => rfl
  | fail => simp [expect]
  | choice p bounded yes no iy ino => simp only [expect, iy, ino]; ring
  | score weight body ih => simp only [expect, ih]; ring

/-- Zero likelihood is an impossible observation, not a probability of zero
for every possible subsequent query. -/
def posterior (program : Program α) (likelihood query : α → ℚ≥0) : Option ℚ≥0 :=
  let mass := program.expect likelihood
  if mass = 0 then none
  else some (program.expect (fun value => likelihood value * query value) / mass)

end Program

/-- A generator is held fixed while the revisable state accumulates
likelihood factors. Queries are nonnegative observables. -/
@[instance_reducible] def likelihoodWorldModel {α : Type} (prior : Program α) :
    MonoidalWorldModel (α → ℚ≥0) (α → ℚ≥0) ℚ≥0 where
  revise first second := fun value => first value * second value
  empty := fun _ => 1
  extract likelihood query := prior.expect (fun value => likelihood value * query value)
  revise_assoc first second third := by funext value; exact mul_assoc _ _ _
  revise_empty_left state := by funext value; exact one_mul _
  revise_empty_right state := by funext value; exact mul_one _

def fairCoin : Program Bool := .choice (1 / 2) (by norm_num) (.pure true) (.pure false)
def heads : Bool → ℚ≥0 := fun value => if value then 1 else 0
def report : Bool → ℚ≥0 := fun value => if value then 3 / 4 else 1 / 4

/-- A report with likelihood ratio three changes even odds to three-to-one. -/
theorem posterior_report : fairCoin.posterior report heads = some (3 / 4) := by
  decide +kernel

/-- Repeated factors represent independent reports only when the model
justifies their factorization. Numerically the second factor matters. -/
theorem posterior_two_reports :
    fairCoin.posterior (fun value => report value * report value) heads = some (9 / 10) := by
  decide +kernel

theorem impossible_observation :
    fairCoin.posterior (fun _ => 0) heads = none := by
  decide +kernel

/-- Multiplying likelihoods is not the additive WM calculus's revision law. -/
theorem likelihood_extraction_not_additive :
    (likelihoodWorldModel fairCoin).toWorldModel.extract
      ((likelihoodWorldModel fairCoin).toWorldModel.revise report report) heads ≠
      (likelihoodWorldModel fairCoin).toWorldModel.extract report heads +
        (likelihoodWorldModel fairCoin).toWorldModel.extract report heads := by
  decide +kernel

#guard fairCoin.posterior report heads == some (3 / 4)
#guard fairCoin.posterior (fun value => report value * report value) heads == some (9 / 10)
#guard fairCoin.posterior (fun _ => 0) heads == none

#print axioms Program.expect_bind
#print axioms Program.observe_sequence
#print axioms likelihood_extraction_not_additive

end Mettapedia.PLN.WorldModel.FiniteProbabilisticPrograms
