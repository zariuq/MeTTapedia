import Mettapedia.ProbabilityTheory.BayesianNetworks.ScopedFactorReadout
import Mettapedia.ProbabilityTheory.BayesianNetworks.FactorMasses

/-!
# Exact conditional factor queries and factor-slot replacement

The reference interpreter supplies the evidence-and-query mass and the
evidence mass as separate rational numbers. A zero normalizer is an
executed mass, and normalization requires positive evidence.
-/

set_option autoImplicit false

namespace Mettapedia.ProbabilityTheory.BayesianNetworks.ScopedFactorReadout

open Mettapedia.OSLF.MeTTaIL.Syntax
open ExecutableFactorTable

variable {n m : Nat} {domains : Fin n → Nat}

/-- A complete elimination order yields a scalar readout at any assignment.
This reference uses the zero assignment to read the retained table. -/
def compileWeight (positive : ∀ v, 0 < domains v) (tables : Fin m → Table domains)
    (order : List (Fin n)) : Pattern :=
  let scopes := fun i => (tables i).scope
  lower scopes (EliminationPlan.compile scopes order) (fun v => ⟨0, positive v⟩)

theorem execute_weight (positive : ∀ v, 0 < domains v) (tables : List (Table domains))
    (order : List (Fin n)) :
    execute? tables.get (compileWeight positive tables.get order) =
      some (weight domains positive tables order) := by
  unfold compileWeight
  rw [execute_lower positive _ _ (fun _ => rfl), EliminationPlan.evaluate_compile positive _ _ (fun _ => rfl),
    List.ofFn_get]
  rfl

def queryMass? (positive : ∀ v, 0 < domains v) (tables : List (Table domains))
    (constraints : List (Constraint domains)) (order : List (Fin n)) : Option ℚ :=
  let inputs := queryTables domains positive tables constraints
  execute? inputs.get (compileWeight positive inputs.get order)

theorem queryMass_eq_weight (positive : ∀ v, 0 < domains v) (tables : List (Table domains))
    (constraints : List (Constraint domains)) (order : List (Fin n)) :
    queryMass? positive tables constraints order =
      some (queryWeight domains positive tables constraints order) :=
  execute_weight positive (queryTables domains positive tables constraints) order

def completeOrder (order : List (Fin n)) : Bool :=
  (List.finRange n).all fun v => decide (v ∈ order)

theorem completeOrder_iff (order : List (Fin n)) :
    completeOrder order = true ↔ ∀ v, v ∈ order := by
  simp [completeOrder]

def conditionalMasses? (positive : ∀ v, 0 < domains v) (tables : List (Table domains))
    (evidence query : List (Constraint domains)) (order : List (Fin n)) : Option Masses :=
  if completeOrder order then
    do
      let numerator ← queryMass? positive tables (evidence ++ query) order
      let denominator ← queryMass? positive tables evidence order
      pure ⟨numerator, denominator⟩
  else none

theorem conditionalMasses_incomplete (positive : ∀ v, 0 < domains v) (tables : List (Table domains))
    (evidence query : List (Constraint domains)) (order : List (Fin n))
    (missing : ∃ v, v ∉ order) :
    conditionalMasses? positive tables evidence query order = none := by
  obtain ⟨v, hv⟩ := missing
  have invalid : completeOrder order ≠ true := fun complete => hv ((completeOrder_iff order).mp complete v)
  simp [conditionalMasses?, invalid]

theorem conditionalMasses_eq_weights (positive : ∀ v, 0 < domains v)
    (tables : List (Table domains)) (evidence query : List (Constraint domains))
    (order : List (Fin n)) (covers : ∀ v, v ∈ order) :
    conditionalMasses? positive tables evidence query order =
      some ⟨queryWeight domains positive tables (evidence ++ query) order,
        queryWeight domains positive tables evidence order⟩ := by
  simp [conditionalMasses?, (completeOrder_iff order).mpr covers, queryMass_eq_weight]

/-- Both compiled masses agree with the joint-world sums. -/
theorem conditionalMasses_exact (positive : ∀ v, 0 < domains v) (tables : List (Table domains))
    (evidence query : List (Constraint domains)) (order : List (Fin n))
    (covers : ∀ v, v ∈ order) :
    conditionalMasses? positive tables evidence query order =
      some ⟨∑ x : Config domains,
          if satisfies domains (evidence ++ query) x then
            (ExecutableFactorTable.combineAll domains positive tables).value domains positive x else 0,
        ∑ x : Config domains,
          if satisfies domains evidence x then
            (ExecutableFactorTable.combineAll domains positive tables).value domains positive x else 0⟩ := by
  rw [conditionalMasses_eq_weights positive tables evidence query order covers,
    queryWeight_correct domains positive tables _ order covers,
    queryWeight_correct domains positive tables _ order covers]

theorem conditionalMasses_bounds (positive : ∀ v, 0 < domains v) (tables : List (Table domains))
    (evidence query : List (Constraint domains)) (order : List (Fin n)) (covers : ∀ v, v ∈ order)
    (nonneg : ∀ table ∈ tables, ∀ x, 0 ≤ table.value domains positive x)
    (masses : Masses) (computed : conditionalMasses? positive tables evidence query order = some masses) :
    0 ≤ masses.joint ∧ masses.joint ≤ masses.evidence := by
  rw [conditionalMasses_exact positive tables evidence query order covers] at computed
  have equal := Option.some.inj computed
  subst masses
  have nonnegative (x : Config domains) :
      0 ≤ (ExecutableFactorTable.combineAll domains positive tables).value domains positive x := by
    rw [combineAll_value]
    apply List.prod_nonneg
    intro value member
    obtain ⟨table, included, rfl⟩ := List.mem_map.mp member
    exact nonneg table included x
  constructor
  · exact Finset.sum_nonneg fun x _ => by split <;> first | exact nonnegative x | exact le_rfl
  · apply Finset.sum_le_sum
    intro x _
    by_cases fits : satisfies domains (evidence ++ query) x
    · have before : satisfies domains evidence x :=
        fun c member => fits c (List.mem_append_left query member)
      simp only [if_pos fits, if_pos before]
      exact le_rfl
    · simp only [if_neg fits]
      split <;> first | exact nonnegative x | exact le_rfl

theorem conditionalMasses_posterior (positive : ∀ v, 0 < domains v) (tables : List (Table domains))
    (evidence query : List (Constraint domains)) (order : List (Fin n)) (covers : ∀ v, v ∈ order) :
    (conditionalMasses? positive tables evidence query order).bind Masses.posterior? =
      conditionalQuery domains positive tables evidence query order := by
  rw [conditionalMasses_eq_weights positive tables evidence query order covers]
  rfl

section Edits

variable {positive : ∀ v, 0 < domains v} {scopes : Fin m → List (Fin n)} {order : List (Fin n)}
local notation "State" => EliminationPlan.Runtime positive scopes order

/-- An accepted edit preserves the provider response at every other slot. -/
theorem lookup_other_slot (before after : State)
    (slot other : Fin m) (different : other ≠ slot) (newTable : Table domains)
    (work row : Nat) (accepted : before.tryReplace slot newTable = some (after, work)) :
    lookup? (fun i : Fin m => after.factors[i]) (entry other.val row) =
      lookup? (fun i : Fin m => before.factors[i]) (entry other.val row) := by
  simp only [lookup_entry]
  rw [before.tryReplace_factors after slot newTable work accepted]
  have retained : (before.factors.set slot.val newTable slot.isLt)[other] = before.factors[other] :=
    Vector.getElem_set_ne slot.isLt other.isLt (fun same => different (Fin.ext same.symm))
  rw [retained]

/-- Distinct-slot edits agree on the factor bank and on the new retained
table, in either order of successful execution. -/
theorem distinct_edits_commute (start afterLeft afterRight leftThenRight rightThenLeft : State)
    {left right : Fin m} (different : left ≠ right) (leftTable rightTable : Table domains)
    {firstLeft secondRight firstRight secondLeft : Nat}
    (leftStep : start.tryReplace left leftTable = some (afterLeft, firstLeft))
    (leftRight : afterLeft.tryReplace right rightTable = some (leftThenRight, secondRight))
    (rightStep : start.tryReplace right rightTable = some (afterRight, firstRight))
    (rightLeft : afterRight.tryReplace left leftTable = some (rightThenLeft, secondLeft)) :
    leftThenRight.factors = rightThenLeft.factors ∧ leftThenRight.table = rightThenLeft.table := by
  have banks : leftThenRight.factors = rightThenLeft.factors := by
    rw [afterLeft.tryReplace_factors leftThenRight right rightTable secondRight leftRight,
      afterRight.tryReplace_factors rightThenLeft left leftTable secondLeft rightLeft,
      start.tryReplace_factors afterLeft left leftTable firstLeft leftStep,
      start.tryReplace_factors afterRight right rightTable firstRight rightStep]
    exact Vector.set_comm leftTable rightTable (fun equal => different (Fin.ext equal))
  exact ⟨banks, by rw [leftThenRight.table_exact, rightThenLeft.table_exact, banks]⟩

end Edits
end Mettapedia.ProbabilityTheory.BayesianNetworks.ScopedFactorReadout
