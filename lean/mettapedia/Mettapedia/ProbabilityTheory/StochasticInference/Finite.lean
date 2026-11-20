import Mettapedia.ProbabilityTheory.StochasticInference.Ledger
import Mettapedia.ProbabilityTheory.BayesianNetworks.ExecutableFactorTable
import Mettapedia.ProbabilityTheory.BayesianNetworks.FactorMasses

/-!
# Exact finite stochastic inference

The state denotes a product of nonnegative factors. Each active observation
contributes one likelihood factor on its declared variables. Report identity
does not imply probabilistic independence. Hard evidence uses an indicator
factor. Expectations and event probabilities share the elimination engine.
-/

set_option autoImplicit false

namespace Mettapedia.ProbabilityTheory.StochasticInference

open Mettapedia.ProbabilityTheory.BayesianNetworks
open ExecutableFactorTable ScopedFactorReadout

variable {n : Nat} {domains : Fin n → Nat}

abbrev LocalConfig (domains : Fin n → Nat) (scope : List (Fin n)) :=
  ∀ v ∈ scope, Fin (domains v)

def tableOnScope (positive : ∀ v, 0 < domains v) (scope : List (Fin n))
    (distinct : scope.Nodup) (values : LocalConfig domains scope → ℚ) : Table domains :=
  tabulate domains positive scope distinct (fun x => values (fun v _ => x v))

theorem tableOnScope_value (positive : ∀ v, 0 < domains v) (scope : List (Fin n))
    (distinct : scope.Nodup) (values : LocalConfig domains scope → ℚ) (x : Config domains) :
    (tableOnScope positive scope distinct values).value domains positive x =
      values (fun v _ => x v) := by
  apply tabulate_value
  intro left right agree
  congr 1
  funext v inside
  exact agree v inside

structure Potential (domains : Fin n → Nat) where
  table : Table domains
  nonneg : ∀ i : Fin table.coefficients.size, 0 ≤ table.coefficients[i.val]
  deriving DecidableEq

namespace Potential

def checked (table : Table domains) : Option (Potential domains) :=
  if h : ∀ i : Fin table.coefficients.size, 0 ≤ table.coefficients[i.val] then some ⟨table, h⟩ else none

theorem value_nonneg (potential : Potential domains) (positive : ∀ v, 0 < domains v)
    (x : Config domains) : 0 ≤ potential.table.value domains positive x :=
  potential.nonneg ⟨_, by
    rw [potential.table.size_eq]
    exact encode_bound domains positive potential.table.scope x⟩

def onScope (positive : ∀ v, 0 < domains v) (scope : List (Fin n)) (distinct : scope.Nodup)
    (values : LocalConfig domains scope → ℚ) (nonnegative : ∀ x, 0 ≤ values x) :
    Potential domains :=
  ⟨tableOnScope positive scope distinct values, by
    intro row
    simp only [tableOnScope, tabulate, Array.getElem_ofFn]
    exact nonnegative _⟩

def neutral (positive : ∀ v, 0 < domains v) (scope : List (Fin n)) (distinct : scope.Nodup) :
    Potential domains := onScope positive scope distinct (fun _ => 1) (fun _ => zero_le_one)

@[simp] theorem neutral_value (positive : ∀ v, 0 < domains v) (scope : List (Fin n))
    (distinct : scope.Nodup) (x : Config domains) :
    (neutral positive scope distinct).table.value domains positive x = 1 :=
  tableOnScope_value positive scope distinct _ x

end Potential

structure Event (domains : Fin n → Nat) where
  table : Table domains
  binary : ∀ i : Fin table.coefficients.size, table.coefficients[i.val] = 0 ∨ table.coefficients[i.val] = 1
  deriving DecidableEq

namespace Event

def checked (table : Table domains) : Option (Event domains) :=
  if h : ∀ i : Fin table.coefficients.size,
      table.coefficients[i.val] = 0 ∨ table.coefficients[i.val] = 1 then some ⟨table, h⟩ else none

def onScope (positive : ∀ v, 0 < domains v) (scope : List (Fin n)) (distinct : scope.Nodup)
    (test : LocalConfig domains scope → Bool) : Event domains :=
  ⟨tableOnScope positive scope distinct (fun x => if test x then 1 else 0), by
    intro row
    simp only [tableOnScope, tabulate, Array.getElem_ofFn]
    split <;> simp⟩

def value (event : Event domains) (positive : ∀ v, 0 < domains v) (x : Config domains) : ℚ :=
  event.table.value domains positive x

theorem value_binary (event : Event domains) (positive : ∀ v, 0 < domains v)
    (x : Config domains) : event.value positive x = 0 ∨ event.value positive x = 1 :=
  event.binary ⟨_, by
    rw [event.table.size_eq]
    exact encode_bound domains positive event.table.scope x⟩

def holds (event : Event domains) (positive : ∀ v, 0 < domains v) (x : Config domains) : Bool :=
  decide (event.value positive x = 1)

theorem value_eq_indicator (event : Event domains) (positive : ∀ v, 0 < domains v)
    (x : Config domains) : event.value positive x = if event.holds positive x then 1 else 0 := by
  rcases event.value_binary positive x with zero | one
  · simp [holds, zero]
  · simp [holds, one]

def asPotential (event : Event domains) : Potential domains :=
  ⟨event.table, by
    intro i
    rcases event.binary i with h | h <;> simp [h]⟩

def equalTo (positive : ∀ v, 0 < domains v) (v : Fin n) (value : Fin (domains v)) : Event domains :=
  onScope positive [v] (by simp) (fun x => decide (x v (by simp) = value))

def fromWorldTest (positive : ∀ v, 0 < domains v) (scope : List (Fin n))
    (distinct : scope.Nodup) (test : Config domains → Bool)
    (_respects : ∀ x y, (∀ v ∈ scope, x v = y v) → test x = test y) : Event domains :=
  ⟨tabulate domains positive scope distinct (fun x => if test x then 1 else 0), by
    intro row
    simp only [tabulate, Array.getElem_ofFn]
    split <;> simp⟩

theorem holds_agree (event : Event domains) (positive : ∀ v, 0 < domains v)
    (x y : Config domains) (agree : ∀ v ∈ event.table.scope, x v = y v) :
    event.holds positive x = event.holds positive y := by
  have equal := event.table.respects domains positive x y
    (fun v member => agree v (List.mem_toFinset.mp member))
  change event.value positive x = event.value positive y at equal
  simp [holds, equal]

/-- Use an event as a feature or a report likelihood with two explicit
potentials. Both values may exceed one when they represent relative scores. -/
def weighted (positive : ∀ v, 0 < domains v) (event : Event domains)
    (whenTrue whenFalse : ℚ) (hTrue : 0 ≤ whenTrue) (hFalse : 0 ≤ whenFalse) :
    Potential domains :=
  ⟨tabulate domains positive event.table.scope event.table.distinct
    (fun x => if event.holds positive x then whenTrue else whenFalse), by
    intro row
    simp only [tabulate, Array.getElem_ofFn]
    split <;> assumption⟩

theorem weighted_value (positive : ∀ v, 0 < domains v) (event : Event domains)
    (whenTrue whenFalse : ℚ) (hTrue : 0 ≤ whenTrue) (hFalse : 0 ≤ whenFalse)
    (x : Config domains) :
    (event.weighted positive whenTrue whenFalse hTrue hFalse).table.value domains positive x =
      if event.holds positive x then whenTrue else whenFalse := by
  apply tabulate_value
  intro a b agree
  rw [holds_agree event positive a b agree]

theorem fromWorldTest_holds (positive : ∀ v, 0 < domains v) (scope : List (Fin n))
    (distinct : scope.Nodup) (test : Config domains → Bool)
    (respects : ∀ x y, (∀ v ∈ scope, x v = y v) → test x = test y) (x : Config domains) :
    (fromWorldTest positive scope distinct test respects).holds positive x = test x := by
  have eval : (fromWorldTest positive scope distinct test respects).value positive x =
      if test x then 1 else 0 := by
    apply tabulate_value
    intro a b agree
    rw [respects a b agree]
  unfold holds
  rw [eval]
  cases test x <;> decide

def neg (positive : ∀ v, 0 < domains v) (event : Event domains) : Event domains :=
  fromWorldTest positive event.table.scope event.table.distinct (fun x => !event.holds positive x)
    (fun a b agree => congrArg Bool.not (holds_agree event positive a b agree))

def combine (positive : ∀ v, 0 < domains v) (op : Bool → Bool → Bool)
    (left right : Event domains) : Event domains :=
  fromWorldTest positive (left.table.scope ++ right.table.scope).dedup (List.nodup_dedup _)
    (fun x => op (left.holds positive x) (right.holds positive x)) (by
      intro a b agree
      rw [holds_agree left positive a b (fun v inLeft =>
          agree v (List.mem_dedup.mpr (List.mem_append_left _ inLeft))),
        holds_agree right positive a b (fun v inRight =>
          agree v (List.mem_dedup.mpr (List.mem_append_right _ inRight)))])

abbrev conj (positive : ∀ v, 0 < domains v) := combine (domains := domains) positive (· && ·)
abbrev disj (positive : ∀ v, 0 < domains v) := combine (domains := domains) positive (· || ·)

theorem neg_holds (positive : ∀ v, 0 < domains v) (event : Event domains) (x : Config domains) :
    (event.neg positive).holds positive x = !event.holds positive x :=
  fromWorldTest_holds _ _ _ _ _ _

theorem combine_holds (positive : ∀ v, 0 < domains v) (op : Bool → Bool → Bool)
    (left right : Event domains) (x : Config domains) :
    (combine positive op left right).holds positive x =
      op (left.holds positive x) (right.holds positive x) :=
  fromWorldTest_holds _ _ _ _ _ _

end Event

structure Schedule (n : Nat) where
  order : List (Fin n)
  covers : ∀ v, v ∈ order

namespace Schedule

def checked (order : List (Fin n)) : Option (Schedule n) :=
  if complete : ∀ v : Fin n, v ∈ order then
    some ⟨order, complete⟩
  else none

def natural (n : Nat) : Schedule n := ⟨List.finRange n, fun _ => by simp⟩

end Schedule

def worldWeight (positive : ∀ v, 0 < domains v) (tables : List (Table domains))
    (x : Config domains) : ℚ :=
  (tables.map (fun table => table.value domains positive x)).prod

theorem worldWeight_append (positive : ∀ v, 0 < domains v) (left right : List (Table domains))
    (x : Config domains) :
    worldWeight positive (left ++ right) x = worldWeight positive left x * worldWeight positive right x := by
  simp [worldWeight, List.prod_append]

def mass (positive : ∀ v, 0 < domains v) (schedule : Schedule n) (tables : List (Table domains)) : ℚ :=
  ExecutableFactorTable.weight domains positive (tables ++ covering domains positive) schedule.order

theorem mass_exact (positive : ∀ v, 0 < domains v) (schedule : Schedule n)
    (tables : List (Table domains)) :
    mass positive schedule tables = ∑ x : Config domains, worldWeight positive tables x := by
  rw [mass, weight_eq_full_sum domains positive _ schedule.order schedule.covers
    (covering_scope domains positive tables)]
  apply Finset.sum_congr rfl
  intro x _
  have unit : worldWeight positive (covering domains positive) x = 1 := by
    rw [worldWeight, ← combineAll_value, covering_value]
  rw [combineAll_value, ← worldWeight, worldWeight_append, unit, mul_one]

structure State (Id : Type*) (domains : Fin n → Nat) where
  base : List (Potential domains)
  ledger : EvidenceLedger Id (Potential domains)
  deriving DecidableEq

namespace State

variable {Id : Type*}

def initial (base : List (Potential domains)) : State Id domains := ⟨base, EvidenceLedger.empty⟩

def factors (state : State Id domains) : List (Potential domains) :=
  state.base ++ state.ledger.active.map EvidenceEntry.payload

def tables (state : State Id domains) : List (Table domains) := state.factors.map Potential.table

def observe [DecidableEq Id] (state : State Id domains) (id : Id) (likelihood : Potential domains) :
    Except Id (EvidenceLedger.Arrival × State Id domains) := do
  let (disposition, ledger) ← state.ledger.observe id likelihood
  pure (disposition, { state with ledger := ledger })

def retract [DecidableEq Id] (state : State Id domains) (id : Id) : State Id domains :=
  { state with ledger := state.ledger.retract id }

def restore [DecidableEq Id] (state : State Id domains) (id : Id) : State Id domains :=
  { state with ledger := state.ledger.restore id }

def unnormalized (state : State Id domains) (positive : ∀ v, 0 < domains v) (x : Config domains) : ℚ :=
  worldWeight positive state.tables x

theorem unnormalized_nonneg (state : State Id domains) (positive : ∀ v, 0 < domains v)
    (x : Config domains) : 0 ≤ state.unnormalized positive x := by
  apply List.prod_nonneg
  intro value member
  obtain ⟨table, tableMember, rfl⟩ := List.mem_map.mp member
  obtain ⟨factor, _, rfl⟩ := List.mem_map.mp tableMember
  exact factor.value_nonneg positive x

theorem replay [DecidableEq Id] (state : State Id domains) (id : Id)
    (prior : EvidenceEntry Id (Potential domains)) (seen : state.ledger.lookup id = some prior) :
    state.observe id prior.payload = .ok (.replay, state) := by
  simp [observe, EvidenceLedger.observe_replay _ _ _ seen]

/-- Read a signed payoff under the conditional joint, retaining both masses. -/
def expectationMasses (state : State Id domains) (positive : ∀ v, 0 < domains v)
    (schedule : Schedule n) (payoff : Table domains) : Masses :=
  ⟨mass positive schedule (state.tables ++ [payoff]), mass positive schedule state.tables⟩

def probabilityMasses (state : State Id domains) (positive : ∀ v, 0 < domains v)
    (schedule : Schedule n) (event : Event domains) : Masses :=
  state.expectationMasses positive schedule event.table

def probability? (state : State Id domains) (positive : ∀ v, 0 < domains v)
    (schedule : Schedule n) (event : Event domains) : Option ℚ :=
  (state.probabilityMasses positive schedule event).posterior?

def expectedValue? (state : State Id domains) (positive : ∀ v, 0 < domains v)
    (schedule : Schedule n) (payoff : Table domains) : Option ℚ :=
  (state.expectationMasses positive schedule payoff).posterior?

theorem expectationMasses_exact (state : State Id domains) (positive : ∀ v, 0 < domains v)
    (schedule : Schedule n) (payoff : Table domains) :
    state.expectationMasses positive schedule payoff =
      ⟨∑ x, state.unnormalized positive x * payoff.value domains positive x,
        ∑ x, state.unnormalized positive x⟩ := by
  simp [expectationMasses, mass_exact, unnormalized, worldWeight]

theorem probabilityMasses_exact (state : State Id domains) (positive : ∀ v, 0 < domains v)
    (schedule : Schedule n) (event : Event domains) :
    state.probabilityMasses positive schedule event =
      ⟨∑ x, if event.holds positive x then state.unnormalized positive x else 0,
        ∑ x, state.unnormalized positive x⟩ := by
  rw [probabilityMasses, expectationMasses_exact]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  change state.unnormalized positive x * event.value positive x = _
  rw [Event.value_eq_indicator]
  split <;> simp

theorem probability_bounds (state : State Id domains) (positive : ∀ v, 0 < domains v)
    (schedule : Schedule n) (event : Event domains) {q : ℚ}
    (readout : state.probability? positive schedule event = some q) : 0 ≤ q ∧ q ≤ 1 := by
  apply Masses.posterior_bounds _ _ _ readout
  · rw [probabilityMasses_exact]
    exact Finset.sum_nonneg (fun x _ => by split <;> simp [state.unnormalized_nonneg])
  · rw [probabilityMasses_exact]
    exact Finset.sum_le_sum (fun x _ => by split <;> simp [state.unnormalized_nonneg])

/-- A new likelihood multiplies the world weight before normalization. -/
theorem fresh_observation [DecidableEq Id] (state : State Id domains)
    (id : Id) (likelihood : Potential domains) (fresh : state.ledger.lookup id = none)
    (observed : State Id domains) (step : state.observe id likelihood = .ok (.recorded, observed))
    (positive : ∀ v, 0 < domains v) (x : Config domains) :
    observed.unnormalized positive x =
      state.unnormalized positive x * likelihood.table.value domains positive x := by
  rw [observe, EvidenceLedger.observe_fresh _ _ _ fresh] at step
  have updated := congrArg Prod.snd (Except.ok.inj step)
  change _ = observed at updated
  subst observed
  simp [unnormalized, tables, factors, EvidenceLedger.active, worldWeight,
    List.prod_append, mul_comm, mul_left_comm]

end State

end Mettapedia.ProbabilityTheory.StochasticInference
