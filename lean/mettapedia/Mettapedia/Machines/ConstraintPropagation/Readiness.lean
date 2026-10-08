import Mettapedia.Machines.ConstraintPropagation

/-!
# Readiness, selective watches and rechecking

This is the finite dependency view consumed by the existing delayed-goal table.
An atomic condition records the logical deps whose readiness it requires;
all/any retain their different meanings. The executable probe prunes watches
below a satisfied disjunction and inventories only currently unready deps.

Native extraction of this view must resolve aliases and reconstruct it after a
wakeup. A bound variable may introduce new dependencies through its value; this
file does not identify unification with setting a Boolean readiness flag. It
also does not introduce a second evaluator or delay service.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ConstraintPropagation.Readiness

variable {Var : Type*} [DecidableEq Var]

inductive Condition (Var : Type*) where
  | literal (ready : Bool)
  | requires (deps : Finset Var)
  | all (left right : Condition Var)
  | any (left right : Condition Var)
  deriving DecidableEq

inductive Plan (Var : Type*) where
  | ready
  | waiting (deps : Finset Var)
  deriving DecidableEq

def Plan.isReady : Plan Var → Bool
  | .ready => true
  | .waiting _ => false

def Plan.watches : Plan Var → Finset Var
  | .ready => ∅
  | .waiting deps => deps

def allPlans : Plan Var → Plan Var → Plan Var
  | .ready, right => right
  | left, .ready => left
  | .waiting left, .waiting right => .waiting (left ∪ right)

def anyPlans : Plan Var → Plan Var → Plan Var
  | .ready, _ | _, .ready => .ready
  | .waiting left, .waiting right => .waiting (left ∪ right)

/-- Independent readiness denotation. Watching is absent from this definition. -/
def denote (available : Var → Bool) : Condition Var → Bool
  | .literal ready => ready
  | .requires deps => decide (∀ v ∈ deps, available v = true)
  | .all left right => denote available left && denote available right
  | .any left right => denote available left || denote available right

/-- Compile readiness and its current watch inventory together. -/
def probe (available : Var → Bool) : Condition Var → Plan Var
  | .literal true => .ready
  | .literal false => .waiting ∅
  | .requires deps =>
      let pending := deps.filter (fun v => !available v)
      if pending = ∅ then .ready else .waiting pending
  | .all left right => allPlans (probe available left) (probe available right)
  | .any left right => anyPlans (probe available left) (probe available right)

theorem allPlans_ready (left right : Plan Var) :
    (allPlans left right).isReady = (left.isReady && right.isReady) := by
  cases left <;> cases right <;> rfl

theorem anyPlans_ready (left right : Plan Var) :
    (anyPlans left right).isReady = (left.isReady || right.isReady) := by
  cases left <;> cases right <;> rfl

omit [DecidableEq Var] in
theorem pending_empty_iff (available : Var → Bool) (deps : Finset Var) :
    deps.filter (fun v => !available v) = ∅ ↔
      ∀ v ∈ deps, available v = true := by
  simp

/-- The watch-producing algorithm accepts exactly the independent denotation. -/
theorem probe_correct (available : Var → Bool) (condition : Condition Var) :
    (probe available condition).isReady = denote available condition := by
  induction condition with
  | literal ready => cases ready <;> rfl
  | requires deps =>
      simp only [probe, denote]
      split_ifs with h
      · have ready := (pending_empty_iff available deps).mp h
        change true = decide (∀ v ∈ deps, available v = true)
        exact (decide_eq_true ready).symm
      · simp [Plan.isReady, (pending_empty_iff available deps).not.mp h]
  | all left right ihLeft ihRight =>
      simp [probe, denote, allPlans_ready, ihLeft, ihRight]
  | any left right ihLeft ihRight =>
      simp [probe, denote, anyPlans_ready, ihLeft, ihRight]

def support : Condition Var → Finset Var
  | .literal _ => ∅
  | .requires deps => deps
  | .all left right | .any left right => support left ∪ support right

theorem allPlans_watches_subset (left right : Plan Var) :
    (allPlans left right).watches ⊆ left.watches ∪ right.watches := by
  cases left <;> cases right <;> simp [allPlans, Plan.watches]

theorem anyPlans_watches_subset (left right : Plan Var) :
    (anyPlans left right).watches ⊆ left.watches ∪ right.watches := by
  cases left <;> cases right <;> simp [anyPlans, Plan.watches]

/-- The probe never invents a dependency from a different goal. -/
theorem watches_subset_support (available : Var → Bool) (condition : Condition Var) :
    (probe available condition).watches ⊆ support condition := by
  induction condition with
  | literal ready => cases ready <;> simp [probe, Plan.watches, support]
  | requires deps =>
      simp only [probe]
      split_ifs <;> simp [Plan.watches, support, Finset.filter_subset]
  | all left right ihLeft ihRight =>
      exact (allPlans_watches_subset _ _).trans (Finset.union_subset_union ihLeft ihRight)
  | any left right ihLeft ihRight =>
      exact (anyPlans_watches_subset _ _).trans (Finset.union_subset_union ihLeft ihRight)

/-- Readiness is independent of cells the condition cannot inspect. -/
theorem denote_eq_on_support (one two : Var → Bool) (condition : Condition Var)
    (same : ∀ v ∈ support condition, one v = two v) :
    denote one condition = denote two condition := by
  induction condition with
  | literal ready => rfl
  | requires deps =>
      unfold denote
      congr 1
      apply propext
      constructor <;> intro h v hv
      · rw [← same v hv]
        exact h v hv
      · rw [same v hv]
        exact h v hv
  | all left right ihLeft ihRight =>
      rw [denote, denote, ihLeft, ihRight]
      · exact fun v hv => same v (Finset.mem_union_right _ hv)
      · exact fun v hv => same v (Finset.mem_union_left _ hv)
  | any left right ihLeft ihRight =>
      rw [denote, denote, ihLeft, ihRight]
      · exact fun v hv => same v (Finset.mem_union_right _ hv)
      · exact fun v hv => same v (Finset.mem_union_left _ hv)

/-- Every emitted watch points to an input that is currently unavailable.
Already ready inputs are never registered as dormant dependencies. -/
theorem watches_unavailable (available : Var → Bool) (condition : Condition Var)
    {v : Var} (watched : v ∈ (probe available condition).watches) :
    available v = false := by
  induction condition with
  | literal ready => cases ready <;> simp [probe, Plan.watches] at watched
  | requires deps =>
      simp only [probe] at watched
      split_ifs at watched with empty
      · simp [Plan.watches] at watched
      · simpa [Plan.watches] using (Finset.mem_filter.mp watched).2
  | all left right ihLeft ihRight =>
      rcases Finset.mem_union.mp (allPlans_watches_subset _ _ watched) with hl | hr
      · exact ihLeft hl
      · exact ihRight hr
  | any left right ihLeft ihRight =>
      rcases Finset.mem_union.mp (anyPlans_watches_subset _ _ watched) with hl | hr
      · exact ihLeft hl
      · exact ihRight hr

omit [DecidableEq Var] in
theorem ready_has_no_watches {plan : Plan Var} (ready : plan.isReady = true) :
    plan.watches = ∅ := by
  cases plan with
  | ready => rfl
  | waiting deps => simp [Plan.isReady] at ready

/-- A ready alternative removes every watch beneath the disjunction. -/
theorem ready_alternative_prunes (left right : Plan Var)
    (ready : left.isReady = true ∨ right.isReady = true) :
    (anyPlans left right).watches = ∅ := by
  apply ready_has_no_watches
  rw [anyPlans_ready]
  simpa using ready

/-- Register a pending plan in the existing table. Each goal is stored once,
even if it waits on several deps. -/
noncomputable def register {Val Goal : Type*} (table : TableState Var Val Goal)
    (goal : Goal) (plan : Plan Var) : TableState Var Val Goal :=
  match plan with
  | .ready => table
  | .waiting deps => table.suspend goal deps.toList

/-- Effects are handed to the existing evaluator only after rechecking. -/
inductive Dispatch (Var Goal : Type*) where
  | execute (goal : Goal)
  | suspend (deps : Finset Var) (goal : Goal)
  deriving DecidableEq

def dispatch {Goal : Type*} (available : Var → Bool)
    (condition : Condition Var) (goal : Goal) : Dispatch Var Goal :=
  match probe available condition with
  | .ready => .execute goal
  | .waiting deps => .suspend deps goal

theorem executes_iff_ready {Goal : Type*} (available : Var → Bool)
    (condition : Condition Var) (goal : Goal) :
    dispatch available condition goal = .execute goal ↔ denote available condition = true := by
  rw [← probe_correct]
  cases h : probe available condition <;> simp [dispatch, h, Plan.isReady]

theorem not_ready_preserves_goal {Goal : Type*} (available : Var → Bool)
    (condition : Condition Var) (goal : Goal) (pending : denote available condition = false) :
    ∃ deps, dispatch available condition goal = .suspend deps goal := by
  rw [← probe_correct] at pending
  cases h : probe available condition with
  | ready => simp [h, Plan.isReady] at pending
  | waiting deps => exact ⟨deps, by simp [dispatch, h]⟩

/-- An ordinary rollback restores the input observation and therefore restores
the probe and its dispatch, using the service's already-proved shared log. -/
theorem rollback_restores_dispatch {Val Goal : Type*}
    (service : Service Var Val Goal) (operations : List (Op Var Val Goal))
    (observe : ServiceState Var Val Goal → Var → Bool)
    (condition : Condition Var) (goal : Goal) :
    dispatch (observe (rollback ((service.exec operations).log.drop service.log.length)
        (service.exec operations).state))
      condition goal = dispatch (observe service.state) condition goal := by
  rw [rollback_exec]

def both : Condition Bool := .all (.requires {false}) (.requires {true})

/-- A wake on the first variable is insufficient: the other dependency remains. -/
theorem wake_does_not_prove_check :
    probe (fun v => !v) both = .waiting {true} ∧
      dispatch (fun v => !v) both "numeric-check" = .suspend {true} "numeric-check" := by
  decide

/-- A satisfied disjunction can occur below a still-pending conjunction. -/
theorem nested_ready_alternative_prunes :
    probe (fun _ => false)
      (.all (.any (.requires {false}) (.literal true)) (.requires {true})) = .waiting {true} := by
  decide

/-- Source identity and occurrence identity remain distinct in the goal table. -/
theorem identical_checks_remain_two :
    let table : TableState Bool Nat String := ⟨fun _ => none, [], [], []⟩
    let registered := register (register table "check" (.waiting {false})) "check" (.waiting {false})
    (registered.bind false 1).woken = [0, 1] := by
  simp [register, TableState.suspend, TableState.bind, TableState.waitsOn,
    TableState.watching, Finset.toList_singleton]

end Mettapedia.Machines.ConstraintPropagation.Readiness
