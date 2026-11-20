import Mettapedia.PLN.Bridges.GSLT.BayesianInferenceController

/-!
# Bayesian guidance of a concrete checked proof search

Three candidate-producing search actions attempt two premise lookups and a
modus-ponens construction. The authority checks the constructed proof against
a fixed context and goal before emitting a certificate. A failed lookup changes
the Bayesian action model and reverses the order of the two surviving actions.
The learned two-step run finds a proof; the frozen-policy run does not. Actual
attempt costs are charged separately from the model's predictions.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.PLN.Bridges.GSLT.BayesianProofSearchControls

open Mettapedia.InformationTheory
open Mettapedia.ProbabilityTheory.BayesianInference
open Mettapedia.GSLT.Core.BranchingTemporal
open Mettapedia.GSLT.Core.InferenceControl
open Mettapedia.PLN.Bridges.GSLT.BayesianInferenceController

inductive Formula where
  | atom (name : ℕ)
  | imp (antecedent consequent : Formula)
  deriving DecidableEq, Repr

def Formula.holds (valuation : ℕ → Prop) : Formula → Prop
  | .atom name => valuation name
  | .imp antecedent consequent => antecedent.holds valuation → consequent.holds valuation

inductive Proof where
  | premise (index : ℕ)
  | modusPonens (implication antecedent : Proof)
  deriving DecidableEq, Repr

def infer (context : List Formula) : Proof → Option Formula
  | .premise index => context[index]?
  | .modusPonens implication antecedent =>
      match infer context implication, infer context antecedent with
      | some (.imp first second), some supplied => if first = supplied then some second else none
      | _, _ => none

/-- Semantic soundness is earned by induction over the actual proof checker. -/
theorem infer_sound (context : List Formula) (proof : Proof) (conclusion : Formula)
    (checked : infer context proof = some conclusion) (valuation : ℕ → Prop)
    (premises : ∀ formula ∈ context, formula.holds valuation) : conclusion.holds valuation := by
  induction proof generalizing conclusion with
  | premise index =>
      exact premises conclusion (List.mem_of_getElem? checked)
  | modusPonens implication antecedent ihImp ihAnte =>
      cases hi : infer context implication with
      | none => simp [infer, hi] at checked
      | some formula =>
          cases formula with
          | atom name => simp [infer, hi] at checked
          | imp first second =>
              cases ha : infer context antecedent with
              | none => simp [infer, hi, ha] at checked
              | some supplied =>
                  by_cases same : first = supplied
                  · have result : second = conclusion := by simpa [infer, hi, ha, same] using checked
                    subst supplied
                    subst conclusion
                    exact ihImp _ hi (ihAnte _ ha)
                  · simp [infer, hi, ha, same] at checked

def context : List Formula := [.atom 0, .imp (.atom 0) (.atom 1)]
def goal : Formula := .atom 1

/-- Proof data and successful checker equality are both retained. -/
abbrev Certificate := {proof : Proof // infer context proof = some goal}

def check (proof : Proof) : Option Certificate :=
  if valid : infer context proof = some goal then some ⟨proof, valid⟩ else none

theorem certificate_sound (certificate : Certificate) (valuation : ℕ → Prop)
    (premises : ∀ formula ∈ context, formula.holds valuation) : goal.holds valuation :=
  infer_sound context certificate.1 goal certificate.2 valuation premises

inductive Action where
  | firstPremise
  | secondPremise
  | compose
  deriving DecidableEq, Repr

/-- Every search action computes a proof candidate, including failing ones. -/
def candidate : Action → Proof
  | .firstPremise => .premise 0
  | .secondPremise => .premise 1
  | .compose => .modusPonens (.premise 1) (.premise 0)

def authority : BranchingSystem Action Certificate where
  emit action := check (candidate action)
  successors _ := []

def cost : Action → ℝ
  | .firstPremise => 1 / 20
  | .secondPremise => 1 / 10
  | .compose => 1 / 5

def outcome (action : Action) : Bool := (authority.emit action).isSome

def model : Model Bool Action Bool where
  likelihood action state := match action with
    | .compose => Prob.dirac state
    | .firstPremise => Prob.dirac (!state)
    | .secondPremise => Prob.dirac (!state)
  reward result := if result then 1 else 0
  reward_nonneg result := by cases result <;> norm_num
  cost action _ := cost action
  cost_nonneg action _ := by cases action <;> norm_num [cost]

def prior : Prob Bool :=
  ⟨fun state => if state then 1 / 4 else 3 / 4,
    (by intro state; cases state <;> norm_num), by norm_num [Fintype.sum_bool]⟩

def initialMemory : Memory Bool Action Bool := ⟨prior, [], []⟩
def afterFailure : Memory Bool Action Bool := learn model initialMemory .firstPremise false

theorem first_fails : authority.emit .firstPremise = none := by decide +kernel
theorem second_fails : authority.emit .secondPremise = none := by decide +kernel
theorem composition_checks : infer context (candidate .compose) = some goal := by decide +kernel

/-- The successful branch contains a real two-premise derivation. -/
def proofCertificate : Certificate := ⟨candidate .compose, composition_checks⟩

theorem composition_emits : authority.emit .compose = some proofCertificate := by
  simp [authority, check, proofCertificate, composition_checks]

/-- The model's true latent state matches independently checked outcomes of
all three concrete proof procedures. -/
theorem actual_outcomes_match (action : Action) :
    model.likelihood action true = Prob.dirac (outcome action) := by
  cases action <;> simp [model, outcome, first_fails, second_fails, composition_emits]

/-- The alternative latent world has the goal available as a direct premise;
the actual world instead requires composing an implication and antecedent. -/
def contextAt (state : Bool) : List Formula := if state then context else [goal, goal]

/-- Every likelihood row is the outcome of executing the candidate checker
in its supplied latent proof context. The model is tied to actual procedure
behavior, rather than an arbitrary success table. -/
theorem model_outcomes_correct (state : Bool) (action : Action) :
    model.likelihood action state =
      Prob.dirac (decide (infer (contextAt state) (candidate action) = some goal)) := by
  cases state <;> cases action <;>
    simp [model, contextAt, candidate, infer, context, goal]

theorem initial_values : model.value prior .firstPremise = 7 / 10 ∧
    model.value prior .secondPremise = 13 / 20 ∧ model.value prior .compose = 1 / 20 := by
  norm_num [Model.value, Model.expectedReward, Model.expectedCost, model, prior,
    cost, Prob.dirac, Fintype.sum_bool]

theorem failure_possible :
    evidence prior (fun state => (model.likelihood .firstPremise state).1 false) = 1 / 4 := by
  norm_num [evidence, model, prior, Prob.dirac, Fintype.sum_bool]

theorem afterFailure_belief (state : Bool) : afterFailure.belief.1 state = if state then 1 else 0 := by
  have possible : 0 < evidence prior (fun state => (model.likelihood .firstPremise state).1 false) := by
    rw [failure_possible]; norm_num
  simp only [afterFailure, learn, initialMemory, Model.update?_apply model prior .firstPremise false possible]
  cases state <;> norm_num [posterior_apply, evidence, model, prior, Prob.dirac, Fintype.sum_bool]

theorem learned_values : model.value afterFailure.belief .firstPremise = -(1 / 20) ∧
    model.value afterFailure.belief .secondPremise = -(1 / 10) ∧
      model.value afterFailure.belief .compose = 4 / 5 := by
  norm_num [Model.value, Model.expectedReward, Model.expectedCost, model,
    cost, afterFailure_belief, Prob.dirac, Fintype.sum_bool]

def observe (_ : Action) (answer : Option Certificate) (_ : List Action) : Bool := answer.isSome
def adaptive := controller model initialMemory id observe

def frozen : Controller Action Certificate (Memory Bool Action Bool) where
  initialMemory := initialMemory
  scheduler memory := (model.guidance id).scheduler memory.belief
  advance memory _ _ _ := memory

def roots : List Action := [.firstPremise, .secondPremise, .compose]

@[simp] theorem adaptive_initial : adaptive.initialMemory = initialMemory := rfl

/-- The initial policy prefers two cheap premise checks to constructing MP. -/
theorem initial_order :
    (adaptive.scheduler initialMemory).reorder roots = roots := by
  change List.insertionSort
    (fun first second => (model.guidance id).priorityAt prior second ≤
      (model.guidance id).priorityAt prior first) roots = roots
  simp only [Model.guidance_priority, id_eq]
  norm_num [roots, List.insertionSort, List.orderedInsert,
    initial_values.1, initial_values.2.1, initial_values.2.2]

/-- Learning reorders two surviving candidates, rather than selecting the
only remaining candidate after an update. -/
theorem surviving_order_reversed :
    (adaptive.scheduler afterFailure).reorder [.secondPremise, .compose] = [.compose, .secondPremise] := by
  change List.insertionSort
    (fun first second => (model.guidance id).priorityAt afterFailure.belief second ≤
      (model.guidance id).priorityAt afterFailure.belief first) [.secondPremise, .compose] =
      [.compose, .secondPremise]
  simp only [Model.guidance_priority, id_eq]
  norm_num [List.insertionSort, List.orderedInsert,
    learned_values.2.1, learned_values.2.2]

def start : Snapshot Action Certificate (Memory Bool Action Bool) := Snapshot.initial adaptive roots

def firstCheckpoint : Snapshot Action Certificate (Memory Bool Action Bool) :=
  ⟨⟨[], [.secondPremise, .compose]⟩, afterFailure⟩

theorem first_tick : Snapshot.tick authority adaptive start = firstCheckpoint := by
  simp only [Snapshot.tick, start, Snapshot.initial, Mettapedia.GSLT.Core.BranchingTemporal.initial, adaptive_initial]
  rw [initial_order]
  simp only [Mettapedia.GSLT.Core.BranchingTemporal.tick]
  rw [initial_order]
  simp only [roots, first_fails]
  rfl

theorem learned_second_frontier :
    (Snapshot.tick authority adaptive firstCheckpoint).search.frontier = [.secondPremise] := by
  simp only [Snapshot.tick, firstCheckpoint, Mettapedia.GSLT.Core.BranchingTemporal.tick]
  rw [surviving_order_reversed]
  rfl

theorem learned_second_emits :
    (Snapshot.tick authority adaptive firstCheckpoint).search.events = [⟨.compose, proofCertificate⟩] := by
  simp only [Snapshot.tick, firstCheckpoint, Mettapedia.GSLT.Core.BranchingTemporal.tick]
  rw [surviving_order_reversed]
  dsimp only
  rw [composition_emits]
  rfl

theorem adaptive_two_steps :
    (Snapshot.run authority adaptive 2 start).search.frontier = [.secondPremise] ∧
      (Snapshot.run authority adaptive 2 start).search.events = [⟨.compose, proofCertificate⟩] := by
  change (Snapshot.tick authority adaptive (Snapshot.tick authority adaptive start)).search.frontier = _ ∧
    (Snapshot.tick authority adaptive (Snapshot.tick authority adaptive start)).search.events = _
  rw [first_tick]
  exact ⟨learned_second_frontier, learned_second_emits⟩

def frozenStart : Snapshot Action Certificate (Memory Bool Action Bool) := Snapshot.initial frozen roots
def frozenFirst : Snapshot Action Certificate (Memory Bool Action Bool) :=
  ⟨⟨[], [.secondPremise, .compose]⟩, initialMemory⟩

theorem frozen_initial_order : (frozen.scheduler initialMemory).reorder roots = roots := initial_order

theorem frozen_surviving_order :
    (frozen.scheduler initialMemory).reorder [.secondPremise, .compose] = [.secondPremise, .compose] := by
  change List.insertionSort
    (fun first second => (model.guidance id).priorityAt prior second ≤
      (model.guidance id).priorityAt prior first) [.secondPremise, .compose] = [.secondPremise, .compose]
  simp only [Model.guidance_priority, id_eq]
  norm_num [List.insertionSort, List.orderedInsert, initial_values.2.1, initial_values.2.2]

theorem frozen_first_tick : Snapshot.tick authority frozen frozenStart = frozenFirst := by
  have initialized : frozen.initialMemory = initialMemory := rfl
  simp only [Snapshot.tick, frozenStart, Snapshot.initial,
    Mettapedia.GSLT.Core.BranchingTemporal.initial, initialized]
  rw [frozen_initial_order]
  simp only [Mettapedia.GSLT.Core.BranchingTemporal.tick]
  rw [frozen_initial_order]
  simp only [roots, first_fails]
  rfl

theorem frozen_two_steps :
    (Snapshot.run authority frozen 2 frozenStart).search.frontier = [.compose] ∧
      (Snapshot.run authority frozen 2 frozenStart).search.events = [] := by
  change (Snapshot.tick authority frozen (Snapshot.tick authority frozen frozenStart)).search.frontier = _ ∧
    (Snapshot.tick authority frozen (Snapshot.tick authority frozen frozenStart)).search.events = _
  rw [frozen_first_tick]
  simp only [Snapshot.tick, frozenFirst, Mettapedia.GSLT.Core.BranchingTemporal.tick]
  rw [frozen_surviving_order]
  dsimp only
  rw [second_fails]
  exact ⟨rfl, rfl⟩

/-- For this terminal search, every consumed candidate disappears exactly
once and no new candidates are generated. The residual work sum therefore
provides an exact cost account, independent of the Bayesian forecast. -/
def spent (snapshot : Snapshot Action Certificate (Memory Bool Action Bool)) : ℝ :=
  (roots.map cost).sum - (snapshot.search.frontier.map cost).sum

theorem spent_tick (control : Controller Action Certificate (Memory Bool Action Bool))
    (snapshot : Snapshot Action Certificate (Memory Bool Action Bool))
    (action : Action) (pending : List Action)
    (selected : (control.scheduler snapshot.memory).reorder snapshot.search.frontier = action :: pending) :
    spent (Snapshot.tick authority control snapshot) = spent snapshot + cost action := by
  have balance := ((control.scheduler snapshot.memory).reorder_complete snapshot.search.frontier).map cost
  have sums := balance.sum_eq
  rw [selected, List.map_cons, List.sum_cons] at sums
  unfold spent
  simp only [Snapshot.tick, Mettapedia.GSLT.Core.BranchingTemporal.tick, selected]
  change (roots.map cost).sum -
      (((control.scheduler snapshot.memory).integrate pending []).map cost).sum = _
  have residual := ((control.scheduler snapshot.memory).integrate_complete pending []).map cost
  have residualSums := residual.sum_eq
  simp only [List.append_nil] at residualSums
  rw [residualSums, ← sums]
  ring

/-- Exact two-step utility charges the actual consumed candidate costs and
rewards a checked proof only after its certificate has been emitted. -/
def utility (snapshot : Snapshot Action Certificate (Memory Bool Action Bool)) : ℝ :=
  (if snapshot.search.events.isEmpty then 0 else 1) - spent snapshot

theorem adaptive_actual_utility : utility (Snapshot.run authority adaptive 2 start) = 3 / 4 := by
  rw [utility, adaptive_two_steps.2]
  simp only [List.isEmpty_cons, Bool.false_eq_true, if_false]
  rw [spent, adaptive_two_steps.1]
  norm_num [roots, cost]

theorem frozen_actual_utility : utility (Snapshot.run authority frozen 2 frozenStart) = -(3 / 20) := by
  rw [utility, frozen_two_steps.2]
  simp only [List.isEmpty_nil, if_true]
  rw [spent, frozen_two_steps.1]
  norm_num [roots, cost]

/-- A checked proof is found within two attempts after learning; with frozen
preferences the same budget is spent on two unsuccessful premise lookups. -/
theorem learning_improves_checked_search :
    utility (Snapshot.run authority frozen 2 frozenStart) < utility (Snapshot.run authority adaptive 2 start) := by
  rw [adaptive_actual_utility, frozen_actual_utility]
  norm_num

/-- Every emitted certificate establishes the goal in all models of the
actual supplied premises, after any Bayesian control updates. -/
theorem emitted_semantically_sound (work : Nat) (event : Emission Action Certificate)
    (_emitted : event ∈ (Snapshot.run authority adaptive work start).search.events)
    (valuation : ℕ → Prop) (premises : ∀ formula ∈ context, formula.holds valuation) :
    goal.holds valuation := certificate_sound event.value valuation premises

#print axioms infer_sound
#print axioms actual_outcomes_match
#print axioms model_outcomes_correct
#print axioms surviving_order_reversed
#print axioms adaptive_two_steps
#print axioms spent_tick
#print axioms learning_improves_checked_search

end Mettapedia.PLN.Bridges.GSLT.BayesianProofSearchControls
