import Mettapedia.Machines.RecursiveInsertObservations

/-!
# Observation-qualified local plan selection

The input to this file is already an admitted finite ground Horn region,
not an arbitrary source-language program. Recursive execution retains its
ordered attempt log. Delta execution is eligible only for final-fact and
fresh-count observations. An ineligible request is declined, not interpreted
as false or as an empty answer.

Selection minimizes the supplied costs among these two eligible plans. This
is a finite cost-model theorem, not a global optimality or native timing
claim. In particular it supplies no source extraction theorem, probability
semantics, subsumption/deletion loop, or permission to reorder outer effects.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.RecursiveInsert.Region

open Mettapedia.Logic
open scoped BigOperators

variable {Fact : Type} [DecidableEq Fact] [Fintype Fact]

def agenda (rules : List (LP.PropRule Fact)) (seeds : List Fact) (policy : QueuePolicy Fact) :
    RecursiveInsert.State Fact :=
  match run rules policy (potential rules (initial rules seeds) + 1) (initial rules seeds) with
  | .done state => state
  | .paused state => state

theorem agenda_completed (rules : List (LP.PropRule Fact)) (seeds : List Fact) (policy : QueuePolicy Fact) :
    run rules policy (potential rules (initial rules seeds) + 1) (initial rules seeds) =
      .done (agenda rules seeds policy) := by
  rcases finite_saturation rules seeds policy with ⟨finish, h, _⟩
  simp only [agenda, h]

theorem agenda_known (rules : List (LP.PropRule Fact)) (seeds : List Fact) (policy : QueuePolicy Fact) :
    (agenda rules seeds policy).known = reference rules seeds :=
  completed_eq_reference rules seeds policy _ _ (agenda_completed rules seeds policy)

theorem agenda_freshMass (rules : List (LP.PropRule Fact)) (seeds : List Fact)
    (policy : QueuePolicy Fact) (weight : Fact → Nat) :
    freshMass weight (agenda rules seeds policy).log = ∑ fact ∈ reference rules seeds, weight fact := by
  have h := run_balanced rules policy _ _ _ weight (initial_balanced rules seeds weight)
    (agenda_completed rules seeds policy)
  change freshMass weight _ = _ at h
  simpa [agenda_known] using h

inductive Demand (Fact : Type) where
  | finalFacts
  | freshCount (weight : Fact → Nat)
  | attemptCount
  | orderedTrace
  | both (first second : Demand Fact)

inductive Observation (Fact : Type) where
  | facts (known : Finset Fact)
  | count (value : Nat)
  | trace (events : List (Event Fact))
  | pair (first second : Observation Fact)
  deriving DecidableEq

inductive Plan where
  | recursive
  | delta
  deriving DecidableEq

/-- The observer determines semantic eligibility before any cost comparison. -/
def deltaEligible : Demand Fact → Bool
  | .finalFacts => true
  | .freshCount _ => true
  | .attemptCount => false
  | .orderedTrace => false
  | .both first second => deltaEligible first && deltaEligible second

def eligible (demand : Demand Fact) (plan : Plan) : Bool :=
  match plan with
  | .recursive => true
  | .delta => deltaEligible demand

def observeAgenda (demand : Demand Fact) (state : RecursiveInsert.State Fact) : Observation Fact :=
  match demand with
  | .finalFacts => .facts state.known
  | .freshCount weight => .count (freshMass weight state.log)
  | .attemptCount => .count state.log.length
  | .orderedTrace => .trace state.log.reverse
  | .both first second => .pair (observeAgenda first state) (observeAgenda second state)

def observeDelta (demand : Demand Fact) (known : Finset Fact) : Option (Observation Fact) :=
  match demand with
  | .finalFacts => some (.facts known)
  | .freshCount weight => some (.count (∑ fact ∈ known, weight fact))
  | .attemptCount => none
  | .orderedTrace => none
  | .both first second => do
      let a ← observeDelta first known
      let b ← observeDelta second known
      return .pair a b

def execute (rules : List (LP.PropRule Fact)) (seeds : List Fact)
    (demand : Demand Fact) : Plan → Option (Observation Fact)
  | .recursive => some (observeAgenda demand (agenda rules seeds depthFirst))
  | .delta => observeDelta demand
      (SemiNaive.rounds rules.toFinset seeds.toFinset (LP.maxSteps (α := Fact))).known

theorem observeDelta_refines (rules : List (LP.PropRule Fact)) (seeds : List Fact)
    (demand : Demand Fact) (admitted : deltaEligible demand = true) :
    observeDelta demand
      (SemiNaive.rounds rules.toFinset seeds.toFinset (LP.maxSteps (α := Fact))).known =
      some (observeAgenda demand (agenda rules seeds depthFirst)) := by
  induction demand with
  | finalFacts => simp [observeDelta, observeAgenda, SemiNaive.rounds_saturate, agenda_known]
  | freshCount weight =>
      simp [observeDelta, observeAgenda, SemiNaive.rounds_saturate, agenda_freshMass]
  | attemptCount => simp [deltaEligible] at admitted
  | orderedTrace => simp [deltaEligible] at admitted
  | both first second ihFirst ihSecond =>
      have h := Bool.and_eq_true_iff.mp admitted
      simp [observeDelta, observeAgenda, ihFirst h.1, ihSecond h.2]

theorem eligible_refines (rules : List (LP.PropRule Fact)) (seeds : List Fact)
    (demand : Demand Fact) (plan : Plan) (admitted : eligible demand plan = true) :
    execute rules seeds demand plan = execute rules seeds demand .recursive := by
  cases plan with
  | recursive => rfl
  | delta => exact observeDelta_refines rules seeds demand admitted

structure Costs where
  recursive : Nat
  delta : Nat

def cost (costs : Costs) : Plan → Nat
  | .recursive => costs.recursive
  | .delta => costs.delta

def choose (demand : Demand Fact) (costs : Costs) : Plan :=
  if deltaEligible demand && decide (costs.delta < costs.recursive) then .delta else .recursive

omit [DecidableEq Fact] [Fintype Fact] in
theorem choose_eligible (demand : Demand Fact) (costs : Costs) :
    eligible demand (choose demand costs) = true := by
  unfold choose
  split
  · rename_i h
    exact (Bool.and_eq_true_iff.mp h).1
  · rfl

omit [DecidableEq Fact] [Fintype Fact] in
/-- Optimality is relative to the two declared plans and supplied cost model. -/
theorem choose_minimal (demand : Demand Fact) (costs : Costs) (other : Plan)
    (admitted : eligible demand other = true) :
    cost costs (choose demand costs) ≤ cost costs other := by
  unfold choose
  split
  · rename_i h
    have cheaper : costs.delta < costs.recursive := of_decide_eq_true (Bool.and_eq_true_iff.mp h).2
    cases other with
    | recursive => exact Nat.le_of_lt cheaper
    | delta => exact Nat.le_refl _
  · rename_i h
    cases other with
    | recursive => exact Nat.le_refl _
    | delta =>
        have allowed : deltaEligible demand = true := admitted
        have notCheaper : ¬ costs.delta < costs.recursive := by
          intro cheaper
          exact h (by simp [allowed, cheaper])
        exact Nat.le_of_not_gt notCheaper

theorem choose_refines (rules : List (LP.PropRule Fact)) (seeds : List Fact)
    (demand : Demand Fact) (costs : Costs) :
    execute rules seeds demand (choose demand costs) = execute rules seeds demand .recursive :=
  eligible_refines rules seeds demand _ (choose_eligible demand costs)

theorem choose_returns_observation (rules : List (LP.PropRule Fact)) (seeds : List Fact)
    (demand : Demand Fact) (costs : Costs) :
    ∃ observation, execute rules seeds demand (choose demand costs) = some observation := by
  rw [choose_refines]
  exact ⟨_, rfl⟩

namespace Controls

theorem cheaper_delta_not_allowed_to_drop_trace :
    choose (Demand.orderedTrace : Demand (Fin 3)) ⟨100, 0⟩ = .recursive := rfl

theorem cheaper_delta_selected_for_final_facts :
    choose (Demand.finalFacts : Demand (Fin 3)) ⟨100, 1⟩ = .delta := rfl

theorem cheaper_recursive_retained :
    choose (Demand.finalFacts : Demand (Fin 3)) ⟨1, 100⟩ = .recursive := rfl

theorem ordered_delta_declines :
    observeDelta (Demand.orderedTrace : Demand (Fin 3)) {0, 1, 2} = none := rfl

theorem extra_observer_restricts_the_region :
    choose (Demand.both .finalFacts .orderedTrace : Demand (Fin 3)) ⟨100, 0⟩ = .recursive := rfl

end Controls

end Mettapedia.Machines.RecursiveInsert.Region
