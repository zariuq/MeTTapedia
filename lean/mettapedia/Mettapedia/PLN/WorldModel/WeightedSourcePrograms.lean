import Mettapedia.Logic.BDD.StatePredicates
import Mettapedia.Logic.BDD.WMPLNBDDWMCExact
import Mathlib.Algebra.BigOperators.Group.Finset.Pi

/-!
# Weighted finite source computations with shared random names

A finite vector of independent draws is sampled once. Boolean expressions
refer to its coordinates, so repeated occurrences share the same draw.
The body supports return, failure, likelihood scoring, observation and
conditional execution. The compiler emits a finite sum of weighted ordered
BDDs, retaining arbitrary nonnegative scores rather than interpreting them
as Boolean probabilities. Numerator and normalizer are compiled separately.

`WeightedSourceExecution` connects this finite specialization to the actual
source `Comp` and constrained answer collector. This finite compiler may
specialize exponentially many source branches; no efficiency claim is made.
-/

set_option autoImplicit false

namespace Mettapedia.PLN.WorldModel.WeightedSourcePrograms

open scoped ENNReal
open Mettapedia.Logic.BDDCore
open Mettapedia.Logic.BDDCore.StatePredicates
open Mettapedia.Machines.GuardConjunctionCompiler (Guard)
open Mettapedia.Machines.GuardEvaluationRegimes (scalar)

abbrev Expr (n : Nat) := Guard (Fin n)

inductive Body (n : Nat) where
  | ret (value : Expr n)
  | fail
  | score (weight : ℝ≥0∞) (body : Body n)
  | observe (test : Expr n) (body : Body n)
  | branch (test : Expr n) (yes no : Body n)

namespace Body

variable {n : Nat}

/-- Deterministic result on one complete draw assignment. -/
def result : Body n → State n → Option Bool
  | .ret value, state => some (scalar state value)
  | .fail, _ => none
  | .score _ body, state => body.result state
  | .observe test body, state => if scalar state test then body.result state else none
  | .branch test yes no, state => if scalar state test then yes.result state else no.result state

/-- The accumulated score on one assignment; failed paths carry zero mass. -/
noncomputable def weight : Body n → State n → ℝ≥0∞
  | .ret _, _ => 1
  | .fail, _ => 0
  | .score factor body, state => factor * body.weight state
  | .observe test body, state => if scalar state test then body.weight state else 0
  | .branch test yes no, state => if scalar state test then yes.weight state else no.weight state

/-- Pathwise query mass. `query := fun _ => true` gives normalization mass. -/
noncomputable def density (body : Body n) (query : Bool → Bool) (state : State n) : ℝ≥0∞ :=
  match body.result state with
  | none => 0
  | some value => if query value then body.weight state else 0

@[simp] theorem density_ret (value : Expr n) (query : Bool → Bool) (state : State n) :
    (ret value).density query state = if query (scalar state value) then 1 else 0 := rfl

@[simp] theorem density_fail (query : Bool → Bool) (state : State n) :
    (fail : Body n).density query state = 0 := rfl

@[simp] theorem density_score (factor : ℝ≥0∞) (body : Body n) (query : Bool → Bool) (state : State n) :
    (score factor body).density query state = factor * body.density query state := by
  change (match body.result state with
    | none => 0
    | some value => if query value then factor * body.weight state else 0) = _
  cases h : body.result state with
  | none => simp [density, h]
  | some value => by_cases yes : query value <;> simp [density, h, yes]

@[simp] theorem density_observe (test : Expr n) (body : Body n) (query : Bool → Bool) (state : State n) :
    (observe test body).density query state =
      if scalar state test then body.density query state else 0 := by
  cases h : scalar state test <;> simp [density, result, weight, h]

@[simp] theorem density_branch (test : Expr n) (yes no : Body n) (query : Bool → Bool) (state : State n) :
    (branch test yes no).density query state =
      if scalar state test then yes.density query state else no.density query state := by
  cases h : scalar state test <;> simp [density, result, weight, h]

noncomputable def mass (body : Body n) (probability : Fin n → ℝ≥0∞) (query : Bool → Bool) : ℝ≥0∞ :=
  ∑ state : State n, assignmentWeight probability state * body.density query state

noncomputable def posterior (body : Body n) (probability : Fin n → ℝ≥0∞) (query : Bool → Bool) :
    Option ℝ≥0∞ :=
  let normalizer := body.mass probability (fun _ => true)
  if normalizer = 0 ∨ normalizer = ⊤ then none
  else some (body.mass probability query / normalizer)

end Body

/-- A scored Boolean region. Multiplicities and coefficients are retained. -/
abbrev Circuit (n : Nat) := List (ℝ≥0∞ × Diagram n)

noncomputable def Circuit.denote {n : Nat} (circuit : Circuit n) (state : State n) : ℝ≥0∞ :=
  (circuit.map fun (weight, region) => if region.val.eval state then weight else 0).sum

noncomputable def Circuit.count {n : Nat} (circuit : Circuit n) (probability : Fin n → ℝ≥0∞) : ℝ≥0∞ :=
  (circuit.map fun (weight, region) => weight * bdd_wmc region.val probability).sum

def Circuit.restrict {n : Nat} (test : Diagram n) (circuit : Circuit n) : Circuit n :=
  circuit.map fun (weight, region) => (weight, conj test region)

noncomputable def Circuit.scale {n : Nat} (factor : ℝ≥0∞) (circuit : Circuit n) : Circuit n :=
  circuit.map fun (weight, region) => (factor * weight, region)

@[simp] theorem Circuit.denote_append {n : Nat} (left right : Circuit n) (state : State n) :
    (left ++ right).denote state = left.denote state + right.denote state := by
  simp [Circuit.denote]

@[simp] theorem Circuit.denote_restrict {n : Nat} (test : Diagram n) (circuit : Circuit n) (state : State n) :
    (circuit.restrict test).denote state = if test.val.eval state then circuit.denote state else 0 := by
  unfold Circuit.restrict Circuit.denote
  cases h : test.val.eval state <;> simp [conj, Function.comp_def, h]

@[simp] theorem Circuit.denote_scale {n : Nat} (factor : ℝ≥0∞) (circuit : Circuit n) (state : State n) :
    (circuit.scale factor).denote state = factor * circuit.denote state := by
  induction circuit with
  | nil => simp [Circuit.denote, Circuit.scale]
  | cons entry rest ih =>
    rcases entry with ⟨weight, region⟩
    simp only [Circuit.scale, List.map_cons, Circuit.denote, List.sum_cons, List.map_map] at ih ⊢
    rw [ih]
    cases region.val.eval state <;> simp [mul_add]

/-- Query tests are compiled compositionally from the return expression. -/
def resultDiagram {n : Nat} (value : Expr n) (query : Bool → Bool) : Diagram n :=
  choose (compileGuard value)
    (if query true then truth n else falsity n)
    (if query false then truth n else falsity n)

theorem resultDiagram_eval {n : Nat} (value : Expr n) (query : Bool → Bool) (state : State n) :
    (resultDiagram value query).val.eval state = query (scalar state value) := by
  rw [resultDiagram, choose_eval, compileGuard_eval]
  cases scalar state value <;> cases query true <;> cases query false <;> rfl

/-- Structural compilation uses existing BDD operations, not a supplied equivalence certificate. -/
noncomputable def compile {n : Nat} : Body n → (Bool → Bool) → Circuit n
  | .ret value, query => [(1, resultDiagram value query)]
  | .fail, _ => []
  | .score factor body, query => (compile body query).scale factor
  | .observe test body, query => (compile body query).restrict (compileGuard test)
  | .branch test yes no, query =>
      (compile yes query).restrict (compileGuard test) ++
        (compile no query).restrict (neg (compileGuard test))

theorem compile_density {n : Nat} (body : Body n) (query : Bool → Bool) (state : State n) :
    (compile body query).denote state = body.density query state := by
  induction body with
  | ret value => simp [compile, Circuit.denote, resultDiagram_eval]
  | fail => simp [compile, Circuit.denote]
  | score factor body ih => simp [compile, ih]
  | observe test body ih => simp [compile, ih, compileGuard_eval]
  | branch test yes no iy ino =>
    simp only [compile, Circuit.denote_append, Circuit.denote_restrict, compileGuard_eval,
      Body.density_branch, iy, ino, neg, bddNot_eval]
    cases scalar state test <;> simp

/-- The existing ordered-BDD WMC theorem evaluates the compiled circuit. -/
theorem Circuit.count_eq_sum {n : Nat} (circuit : Circuit n) (probability : Fin n → ℝ≥0∞)
    (bounded : ∀ i, probability i ≤ 1) :
    circuit.count probability = ∑ state : State n, assignmentWeight probability state * circuit.denote state := by
  induction circuit with
  | nil => simp [Circuit.count, Circuit.denote]
  | cons entry rest ih =>
    rcases entry with ⟨weight, region⟩
    simp only [Circuit.count, List.map_cons, List.sum_cons] at ih ⊢
    rw [bdd_wmc_correct region.val region.property probability bounded, ih]
    unfold weightedSat
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro state _
    simp only [Circuit.denote, List.map_cons, List.sum_cons]
    cases region.val.eval state <;> simp [mul_add, mul_comm]

/-- Numerators, including arbitrary finite scoring, agree before normalization. -/
theorem compile_mass {n : Nat} (body : Body n) (probability : Fin n → ℝ≥0∞)
    (bounded : ∀ i, probability i ≤ 1) (query : Bool → Bool) :
    (compile body query).count probability = body.mass probability query := by
  rw [Circuit.count_eq_sum _ _ bounded]
  simp only [compile_density, Body.mass]

noncomputable def compiledPosterior {n : Nat} (body : Body n) (probability : Fin n → ℝ≥0∞)
    (query : Bool → Bool) : Option ℝ≥0∞ :=
  let normalizer := (compile body (fun _ => true)).count probability
  if normalizer = 0 ∨ normalizer = ⊤ then none
  else some ((compile body query).count probability / normalizer)

/-- Both denominator and numerator are earned by `compile_mass`. -/
theorem compiledPosterior_eq {n : Nat} (body : Body n) (probability : Fin n → ℝ≥0∞)
    (bounded : ∀ i, probability i ≤ 1) (query : Bool → Bool) :
    compiledPosterior body probability query = body.posterior probability query := by
  simp only [compiledPosterior, Body.posterior, compile_mass body probability bounded]

open Mettapedia.PLN.Evidence.PLNJointEvidence
open Mettapedia.PLN.Evidence.PLNJointEvidence.JointEvidence
open WMPLNBDDWMCExact

/-- Compile the same scored source to the existing world-indexed evidence carrier. -/
noncomputable def joint {n : Nat} (body : Body n) (probability : Fin n → ℝ≥0∞) : JointEvidence n :=
  fun world => assignmentWeight probability (worldAssignmentEquiv n world) *
    body.density (fun _ => true) (worldAssignmentEquiv n world)

def worldQuery {n : Nat} (body : Body n) (query : Bool → Bool) (world : Fin (2 ^ n)) : Bool :=
  ((body.result (worldAssignmentEquiv n world)).map query).getD false

/-- World-mass extraction is the independently defined operational-tape mass. -/
theorem countWorld_joint {n : Nat} (body : Body n) (probability : Fin n → ℝ≥0∞) (query : Bool → Bool) :
    countWorld (joint body probability) (worldQuery body query) = body.mass probability query := by
  unfold countWorld joint worldQuery Body.mass
  calc
    (∑ world : Fin (2 ^ n),
      if ((body.result (worldAssignmentEquiv n world)).map query).getD false then
        assignmentWeight probability (worldAssignmentEquiv n world) *
          body.density (fun _ => true) (worldAssignmentEquiv n world) else 0) =
      ∑ state : State n, if ((body.result state).map query).getD false then
        assignmentWeight probability state * body.density (fun _ => true) state else 0 := by
          exact Equiv.sum_comp (worldAssignmentEquiv n) (fun state : State n =>
            if ((body.result state).map query).getD false then
              assignmentWeight probability state * body.density (fun _ => true) state else 0)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro state _
      cases h : body.result state with
      | none => simp [Body.density, h]
      | some value => cases hq : query value <;> simp [Body.density, h, hq]

/-- The actual BDD circuit and joint evidence agree on every output query. -/
theorem compile_countWorld {n : Nat} (body : Body n) (probability : Fin n → ℝ≥0∞)
    (bounded : ∀ i, probability i ≤ 1) (query : Bool → Bool) :
    (compile body query).count probability =
      countWorld (joint body probability) (worldQuery body query) := by
  rw [compile_mass body probability bounded, countWorld_joint]

/-- Normalization is independently preserved, rather than asserted as probability additivity. -/
theorem total_joint {n : Nat} (body : Body n) (probability : Fin n → ℝ≥0∞) :
    total (joint body probability) = body.mass probability (fun _ => true) := by
  unfold total joint Body.mass
  exact Equiv.sum_comp (worldAssignmentEquiv n) (fun state : State n =>
    assignmentWeight probability state * body.density (fun _ => true) state)

/-- A Boolean query can select only part of the successful mass. -/
theorem Body.density_le_total {n : Nat} (body : Body n) (query : Bool → Bool) (state : State n) :
    body.density query state ≤ body.density (fun _ => true) state := by
  cases h : body.result state with
  | none => simp [Body.density, h]
  | some value => cases hq : query value <;> simp [Body.density, h, hq]

noncomputable def knownMass {n : Nat} (body : Body n) (probability : Fin n → ℝ≥0∞)
    (seen : Finset (State n)) (query : Bool → Bool) : ℝ≥0∞ :=
  ∑ state ∈ seen, assignmentWeight probability state * body.density query state

noncomputable def remainingMass {n : Nat} (body : Body n) (probability : Fin n → ℝ≥0∞)
    (seen : Finset (State n)) (query : Bool → Bool) : ℝ≥0∞ :=
  ∑ state ∈ seenᶜ, assignmentWeight probability state * body.density query state

theorem mass_split {n : Nat} (body : Body n) (probability : Fin n → ℝ≥0∞)
    (seen : Finset (State n)) (query : Bool → Bool) :
    knownMass body probability seen query + remainingMass body probability seen query =
      body.mass probability query := by
  exact Finset.sum_add_sum_compl seen _

theorem remaining_query_le_total {n : Nat} (body : Body n) (probability : Fin n → ℝ≥0∞)
    (seen : Finset (State n)) (query : Bool → Bool) :
    remainingMass body probability seen query ≤ remainingMass body probability seen (fun _ => true) := by
  apply Finset.sum_le_sum
  intro state _
  exact mul_le_mul_right (body.density_le_total query state) _

/-- A bound on unexplored query mass is derived only after supplying a bound
on remaining normalization mass; pending branches alone supply no such number. -/
theorem certified_mass_bound {n : Nat} (body : Body n) (probability : Fin n → ℝ≥0∞)
    (seen : Finset (State n)) (query : Bool → Bool) (bound : ℝ≥0∞)
    (certificate : remainingMass body probability seen (fun _ => true) ≤ bound) :
    knownMass body probability seen query ≤ body.mass probability query ∧
      body.mass probability query ≤ knownMass body probability seen query + bound := by
  rw [← mass_split body probability seen query]
  constructor
  · exact le_add_right le_rfl
  · exact add_le_add le_rfl ((remaining_query_le_total body probability seen query).trans certificate)

#print axioms compile_mass
#print axioms compiledPosterior_eq
#print axioms compile_countWorld

end Mettapedia.PLN.WorldModel.WeightedSourcePrograms
