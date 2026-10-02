import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

/-!
# Constraint propagation and dependency-directed worklists

An information order is oriented from less to more information. Propagators
are monotone and inflationary. Any finite run ending at a common fixed point
computes the least common fixed point above its input. This says nothing about
arbitrary finite prefixes, effects, answer multiplicity, or physical timing.

Finite Horn rules provide an executable instance. A worklist wakes only rules
whose premises intersect the newly added facts. Its invariant says every rule
outside the worklist is stable. Finite stores and a decreasing potential justify
termination, rather than treating fuel exhaustion as quiescence.

This is a machine component specification, not a proof of the C implementation,
foreign attributed-variable transport, or higher-order elaboration.
-/

namespace Mettapedia.Machines.ConstraintPropagation

structure Propagator (S : Type*) [PartialOrder S] where
  apply : S → S
  monotone_apply : Monotone apply
  le_apply : ∀ s, s ≤ apply s

section General

variable {S I : Type*} [PartialOrder S]

def run (ps : I → Propagator S) : List I → S → S
  | [], s => s
  | i :: rest, s => run ps rest ((ps i).apply s)

def Quiescent (ps : I → Propagator S) (s : S) : Prop :=
  ∀ i, (ps i).apply s = s

theorem le_run (ps : I → Propagator S) (schedule : List I) (s : S) :
    s ≤ run ps schedule s := by
  induction schedule generalizing s with
  | nil => exact le_rfl
  | cons i rest ih => exact (ps i).le_apply s |>.trans (ih _)

theorem run_le_fixed (ps : I → Propagator S) (schedule : List I)
    {s upper : S} (bound : s ≤ upper) (fixed : Quiescent ps upper) :
    run ps schedule s ≤ upper := by
  induction schedule generalizing s with
  | nil => exact bound
  | cons i rest ih =>
    apply ih
    simpa only [fixed i] using (ps i).monotone_apply bound

/-- Completed schedules agree; finite prefixes need not agree. -/
theorem quiescent_runs_equal (ps : I → Propagator S)
    (left right : List I) (s : S)
    (hl : Quiescent ps (run ps left s))
    (hr : Quiescent ps (run ps right s)) :
    run ps left s = run ps right s := by
  apply le_antisymm
  · exact run_le_fixed ps left (le_run ps right s) hr
  · exact run_le_fixed ps right (le_run ps left s) hl

end General

structure HornRule (Fact : Type*) where
  premises : Finset Fact
  conclusions : Finset Fact
  deriving DecidableEq

namespace HornRule

variable {Fact : Type*} [DecidableEq Fact]

def apply (r : HornRule Fact) (s : Finset Fact) : Finset Fact :=
  if r.premises ⊆ s then s ∪ r.conclusions else s

theorem subset_apply (r : HornRule Fact) (s : Finset Fact) : s ⊆ r.apply s := by
  simp only [apply]
  split_ifs <;> simp

theorem monotone_apply (r : HornRule Fact) : Monotone r.apply := by
  intro s t h
  by_cases enabled : r.premises ⊆ s
  · simp only [apply, if_pos enabled, if_pos (enabled.trans h)]
    exact Finset.union_subset_union h Finset.Subset.rfl
  · simp only [apply, if_neg enabled]
    exact h.trans (r.subset_apply t)

def propagator (r : HornRule Fact) : Propagator (Finset Fact) :=
  ⟨r.apply, r.monotone_apply, r.subset_apply⟩

theorem idempotent (r : HornRule Fact) (s : Finset Fact) :
    r.apply (r.apply s) = r.apply s := by
  by_cases enabled : r.premises ⊆ s
  · have enabled' : r.premises ⊆ s ∪ r.conclusions :=
      enabled.trans Finset.subset_union_left
    simp [apply, enabled, enabled', Finset.union_assoc]
  · simp [apply, enabled]

/-- A stable rule stays stable if none of its premises has just become true.
Watching conclusion cells is unnecessary for this monotone fact-store client. -/
theorem stable_of_disjoint_delta (r : HornRule Fact) {s t : Finset Fact}
    (extension : s ⊆ t) (stable : r.apply s = s)
    (unaffected : Disjoint r.premises (t \ s)) : r.apply t = t := by
  by_cases enabled : r.premises ⊆ t
  · have oldEnabled : r.premises ⊆ s := by
      intro x hx
      by_contra absent
      exact Finset.disjoint_left.mp unaffected hx
        (Finset.mem_sdiff.mpr ⟨enabled hx, absent⟩)
    have conclusions : r.conclusions ⊆ s := by
      have h := Finset.subset_union_right (s₁ := s) (s₂ := r.conclusions)
      rw [← stable]
      simpa only [apply, if_pos oldEnabled] using h
    simp [apply, enabled, Finset.union_eq_left.mpr (conclusions.trans extension)]
  · simp [apply, enabled]

end HornRule

section Worklist

variable {Fact I : Type*} [DecidableEq Fact] [DecidableEq I] [Fintype I]

structure WorkState (Fact I : Type*) where
  store : Finset Fact
  pending : Finset I
  deriving DecidableEq

def wake (rules : I → HornRule Fact) (old new : Finset Fact) : Finset I :=
  Finset.univ.filter fun i => ¬ Disjoint (rules i).premises (new \ old)

omit [DecidableEq I] in
theorem not_mem_wake_iff (rules : I → HornRule Fact)
    (old new : Finset Fact) (i : I) :
    i ∉ wake rules old new ↔ Disjoint (rules i).premises (new \ old) := by
  simp [wake]

def step (rules : I → HornRule Fact) (i : I) (w : WorkState Fact I) :
    WorkState Fact I :=
  let new := (rules i).apply w.store
  ⟨new, w.pending.erase i ∪ wake rules w.store new⟩

def Valid (rules : I → HornRule Fact) (w : WorkState Fact I) : Prop :=
  ∀ i, i ∉ w.pending → (rules i).apply w.store = w.store

def initial (s : Finset Fact) : WorkState Fact I := ⟨s, Finset.univ⟩

omit [DecidableEq I] in
theorem initial_valid (rules : I → HornRule Fact) (s : Finset Fact) :
    Valid rules (initial s) := by
  simp [Valid, initial]

theorem step_valid (rules : I → HornRule Fact) (i : I)
    {w : WorkState Fact I} (valid : Valid rules w) :
    Valid rules (step rules i w) := by
  intro j absent
  have hn : j ∉ w.pending.erase i ∧
      j ∉ wake rules w.store ((rules i).apply w.store) := by
    simpa only [step, Finset.mem_union, not_or] using absent
  by_cases same : j = i
  · subst j
    exact (rules i).idempotent w.store
  · have oldAbsent : j ∉ w.pending := by simpa [same] using hn.1
    exact (rules j).stable_of_disjoint_delta ((rules i).subset_apply w.store)
      (valid j oldAbsent) ((not_mem_wake_iff rules _ _ j).mp hn.2)

omit [DecidableEq I] [Fintype I] in
theorem quiescent_of_empty (rules : I → HornRule Fact)
    {w : WorkState Fact I} (valid : Valid rules w) (empty : w.pending = ∅) :
    Quiescent (fun i => (rules i).propagator) w.store := by
  intro i
  exact valid i (by simp [empty])

theorem step_le_fixed (rules : I → HornRule Fact) (i : I)
    {w : WorkState Fact I} {upper : Finset Fact} (bound : w.store ⊆ upper)
    (fixed : Quiescent (fun i => (rules i).propagator) upper) :
    (step rules i w).store ⊆ upper := by
  change (rules i).apply w.store ⊆ upper
  have h := (rules i).monotone_apply bound
  exact h.trans_eq (fixed i)

/-- The ordinary model condition for a finite collection of Horn implications. -/
def Models (rules : I → HornRule Fact) (facts : Finset Fact) : Prop :=
  ∀ i, (rules i).premises ⊆ facts → (rules i).conclusions ⊆ facts

omit [DecidableEq I] [Fintype I] in
theorem quiescent_iff_models (rules : I → HornRule Fact) (facts : Finset Fact) :
    Quiescent (fun i => (rules i).propagator) facts ↔ Models rules facts := by
  constructor
  · intro fixed i enabled
    have h := fixed i
    change (rules i).apply facts = facts at h
    rw [HornRule.apply, if_pos enabled] at h
    exact Finset.union_eq_left.mp h
  · intro models i
    change (rules i).apply facts = facts
    by_cases enabled : (rules i).premises ⊆ facts
    · simp [HornRule.apply, enabled, Finset.union_eq_left.mpr (models i enabled)]
    · simp [HornRule.apply, enabled]

/-- The static inverse dependency index. -/
def readers (rules : I → HornRule Fact) (fact : Fact) : Finset I :=
  Finset.univ.filter fun i => fact ∈ (rules i).premises

/-- A runtime can enumerate readers of changed facts instead of every rule. -/
def wakeIndexed (rules : I → HornRule Fact) (old new : Finset Fact) : Finset I :=
  (new \ old).biUnion (readers rules)

theorem wakeIndexed_eq_wake (rules : I → HornRule Fact) (old new : Finset Fact) :
    wakeIndexed rules old new = wake rules old new := by
  ext i
  simp only [wakeIndexed, Finset.mem_biUnion, readers, Finset.mem_filter,
    Finset.mem_univ, true_and, wake, Finset.not_disjoint_iff]
  exact ⟨fun ⟨x, hx, hi⟩ => ⟨x, hi, hx⟩, fun ⟨x, hi, hx⟩ => ⟨x, hx, hi⟩⟩

/-- The inverse index can be represented separately and cached by an
implementation. This mathematical function does not model its storage cost. -/
def indexedStep (rules : I → HornRule Fact) (i : I) (w : WorkState Fact I) :
    WorkState Fact I :=
  let new := (rules i).apply w.store
  ⟨new, w.pending.erase i ∪ wakeIndexed rules w.store new⟩

theorem indexedStep_eq_step (rules : I → HornRule Fact) (i : I)
    (w : WorkState Fact I) : indexedStep rules i w = step rules i w := by
  simp only [indexedStep, step, wakeIndexed_eq_wake]

variable [Fintype Fact]

/-- An actual step either adds a fact, or removes one pending rule. -/
def potential (w : WorkState Fact I) : Nat :=
  (Fintype.card Fact - w.store.card) * (Fintype.card I + 1) + w.pending.card

theorem potential_step_lt (rules : I → HornRule Fact) (i : I)
    (w : WorkState Fact I) (scheduled : i ∈ w.pending) :
    potential (step rules i w) < potential w := by
  have boundOld := Finset.card_le_univ w.store
  have boundNew := Finset.card_le_univ ((rules i).apply w.store)
  have boundQueue := Finset.card_le_univ (step rules i w).pending
  by_cases same : (rules i).apply w.store = w.store
  · have hw : wake rules w.store w.store = ∅ := by simp [wake]
    have erased := Finset.card_erase_lt_of_mem scheduled
    simpa only [potential, step, same, hw, Finset.union_empty] using
      Nat.add_lt_add_left erased
        ((Fintype.card Fact - w.store.card) * (Fintype.card I + 1))
  · have strict : w.store ⊂ (rules i).apply w.store :=
      Finset.ssubset_iff_subset_ne.mpr
        ⟨(rules i).subset_apply w.store, Ne.symm same⟩
    have grows := Finset.card_lt_card strict
    have drops : Fintype.card Fact - ((rules i).apply w.store).card + 1 ≤
        Fintype.card Fact - w.store.card := by omega
    have weighted := Nat.mul_le_mul_right (Fintype.card I + 1) drops
    change (Fintype.card Fact - ((rules i).apply w.store).card) *
        (Fintype.card I + 1) + (step rules i w).pending.card <
      (Fintype.card Fact - w.store.card) * (Fintype.card I + 1) + w.pending.card
    nlinarith

/-- A controller may select any pending rule. It cannot choose a nonpending
rule and pretend to make progress. -/
abbrev Selector (I : Type*) :=
  (pending : Finset I) → pending.Nonempty → { i // i ∈ pending }

def drain (rules : I → HornRule Fact) (select : Selector I) :
    Nat → WorkState Fact I → WorkState Fact I
  | 0, w => w
  | n + 1, w =>
      if h : w.pending.Nonempty then
        drain rules select n (step rules (select w.pending h).val w)
      else w

omit [Fintype Fact] in
theorem drain_valid (rules : I → HornRule Fact) (select : Selector I)
    (fuel : Nat) {w : WorkState Fact I} (valid : Valid rules w) :
    Valid rules (drain rules select fuel w) := by
  induction fuel generalizing w with
  | zero => exact valid
  | succ n ih =>
    simp only [drain]
    split_ifs
    · exact ih (step_valid rules _ valid)
    · exact valid

omit [Fintype Fact] in
theorem subset_drain (rules : I → HornRule Fact) (select : Selector I)
    (fuel : Nat) (w : WorkState Fact I) :
    w.store ⊆ (drain rules select fuel w).store := by
  induction fuel generalizing w with
  | zero => exact Finset.Subset.rfl
  | succ n ih =>
    simp only [drain]
    split_ifs with h
    · exact (rules (select w.pending h).val).subset_apply w.store |>.trans
        (ih (step rules (select w.pending h).val w))
    · exact Finset.Subset.rfl

omit [Fintype Fact] in
theorem drain_le_fixed (rules : I → HornRule Fact) (select : Selector I)
    (fuel : Nat) {w : WorkState Fact I} {upper : Finset Fact}
    (bound : w.store ⊆ upper)
    (fixed : Quiescent (fun i => (rules i).propagator) upper) :
    (drain rules select fuel w).store ⊆ upper := by
  induction fuel generalizing w with
  | zero => exact bound
  | succ n ih =>
    simp only [drain]
    split_ifs
    · exact ih (step_le_fixed rules _ bound fixed)
    · exact bound

/-- The explicit finite bound suffices for every pending-rule selection policy. -/
theorem drain_pending_empty (rules : I → HornRule Fact) (select : Selector I)
    (fuel : Nat) (w : WorkState Fact I) (enough : potential w ≤ fuel) :
    (drain rules select fuel w).pending = ∅ := by
  induction fuel generalizing w with
  | zero =>
    have : w.pending.card = 0 := by unfold potential at enough; omega
    exact Finset.card_eq_zero.mp this
  | succ n ih =>
    simp only [drain]
    split_ifs with nonempty
    · apply ih
      have h := potential_step_lt rules (select w.pending nonempty).val w
        (select w.pending nonempty).property
      omega
    · exact Finset.not_nonempty_iff_eq_empty.mp nonempty

def solve (rules : I → HornRule Fact) (select : Selector I) (s : Finset Fact) :
    Finset Fact :=
  (drain rules select (potential (initial s : WorkState Fact I)) (initial s)).store

/-- The executable worklist specification computes the least common fixed
point. Its scanning notification step admits the proved indexed replacement.
No constraint solver or answer relation is assumed in the premise. -/
theorem solve_least (rules : I → HornRule Fact) (select : Selector I) (s : Finset Fact) :
    s ⊆ solve rules select s ∧
    Quiescent (fun i => (rules i).propagator) (solve rules select s) ∧
    ∀ upper, s ⊆ upper → Quiescent (fun i => (rules i).propagator) upper →
      solve rules select s ⊆ upper := by
  unfold solve
  refine ⟨subset_drain rules select _ (initial s), ?_, ?_⟩
  · exact quiescent_of_empty rules
      (drain_valid rules select _ (initial_valid rules s))
      (drain_pending_empty rules select _ _ le_rfl)
  · intro upper bound fixed
    exact drain_le_fixed rules select _ bound fixed

theorem solve_policy_independent (rules : I → HornRule Fact)
    (left right : Selector I) (s : Finset Fact) :
    solve rules left s = solve rules right s := by
  have hl := solve_least rules left s
  have hr := solve_least rules right s
  exact Finset.Subset.antisymm (hl.2.2 _ hr.1 hr.2.1) (hr.2.2 _ hl.1 hl.2.1)

/-- The worklist computes logical closure, not merely a queue-dependent stable
state: it is a model contained in every model extending the input facts. -/
theorem solve_least_model (rules : I → HornRule Fact) (select : Selector I)
    (s : Finset Fact) :
    s ⊆ solve rules select s ∧ Models rules (solve rules select s) ∧
    ∀ model, s ⊆ model → Models rules model → solve rules select s ⊆ model := by
  obtain ⟨extension, fixed, least⟩ := solve_least rules select s
  refine ⟨extension, (quiescent_iff_models rules _).mp fixed, ?_⟩
  intro model bound satisfies
  exact least model bound ((quiescent_iff_models rules _).mpr satisfies)

end Worklist

/-! ## A dependency-and-suspension service

A machine branch owns a binding store, an index of the goals suspended on each
unbound variable, and a queue of woken goals. One chronological undo log
records every change to all three, so rolling back to a mark restores them
together (`rollback_exec`). Binding a variable wakes exactly the goals
suspended on it (`bind_wakes`); binding a variable nothing waits on leaves the
index and the queue as they were (`bind_unwatched`); a goal suspended on a
variable already bound is woken at once, so none is lost between inspecting a
variable and suspending on it (`suspend_bound`, `suspend_then_bind`); merging
one variable into another keeps every suspended goal, once
(`merge_then_bind`). Goals are the clients' own: a propagator, a foreign
constraint component, or a postponed judgment with its context. -/

section Service

variable {Var Val Goal : Type*} [DecidableEq Var]

structure ServiceState (Var Val Goal : Type*) where
  value : Var → Option Val
  suspended : Var → List Goal
  woken : List Goal

/-- The old contents of the one cell a write changed. -/
inductive Undo (Var Val Goal : Type*) where
  | value (v : Var) (old : Option Val)
  | suspended (v : Var) (old : List Goal)
  | woken (old : List Goal)

def Undo.apply : Undo Var Val Goal → ServiceState Var Val Goal → ServiceState Var Val Goal
  | .value v old, s => { s with value := Function.update s.value v old }
  | .suspended v old, s => { s with suspended := Function.update s.suspended v old }
  | .woken old, s => { s with woken := old }

structure Service (Var Val Goal : Type*) where
  state : ServiceState Var Val Goal
  log : List (Undo Var Val Goal)

/-- Undo a chronological log, newest entry first. -/
def rollback (log : List (Undo Var Val Goal)) (s : ServiceState Var Val Goal) :
    ServiceState Var Val Goal :=
  log.foldr Undo.apply s

theorem rollback_append (older newer : List (Undo Var Val Goal))
    (s : ServiceState Var Val Goal) :
    rollback (older ++ newer) s = rollback older (rollback newer s) := by
  simp [rollback, List.foldr_append]

def Service.setValue (x : Service Var Val Goal) (v : Var) (o : Option Val) :
    Service Var Val Goal :=
  ⟨{ x.state with value := Function.update x.state.value v o },
    x.log ++ [.value v (x.state.value v)]⟩

def Service.setSuspended (x : Service Var Val Goal) (v : Var) (goals : List Goal) :
    Service Var Val Goal :=
  ⟨{ x.state with suspended := Function.update x.state.suspended v goals },
    x.log ++ [.suspended v (x.state.suspended v)]⟩

def Service.setWoken (x : Service Var Val Goal) (goals : List Goal) :
    Service Var Val Goal :=
  ⟨{ x.state with woken := goals }, x.log ++ [.woken x.state.woken]⟩

/-- Bind a variable: the goals suspended on it are woken, each once. -/
def Service.bind (x : Service Var Val Goal) (v : Var) (a : Val) : Service Var Val Goal :=
  let x₁ := x.setValue v (some a)
  let x₂ := x₁.setWoken (x₁.state.woken ++ x₁.state.suspended v)
  x₂.setSuspended v []

/-- Suspend a goal on a variable, or wake it at once when the variable is
already bound. -/
def Service.suspend (x : Service Var Val Goal) (v : Var) (g : Goal) :
    Service Var Val Goal :=
  match x.state.value v with
  | some _ => x.setWoken (x.state.woken ++ [g])
  | none => x.setSuspended v (x.state.suspended v ++ [g])

/-- Merge `u` into `v`: `u` is bound to the value `link` that refers to `v`,
and `v` then holds every goal suspended on either. -/
def Service.merge (x : Service Var Val Goal) (u v : Var) (link : Val) :
    Service Var Val Goal :=
  let x₁ := x.setValue u (some link)
  let x₂ := x₁.setSuspended v (x₁.state.suspended v ++ x₁.state.suspended u)
  x₂.setSuspended u []

inductive Op (Var Val Goal : Type*) where
  | bind (v : Var) (a : Val)
  | suspend (v : Var) (g : Goal)
  | merge (u v : Var) (link : Val)

def Service.step (x : Service Var Val Goal) : Op Var Val Goal → Service Var Val Goal
  | .bind v a => x.bind v a
  | .suspend v g => x.suspend v g
  | .merge u v link => x.merge u v link

def Service.exec (x : Service Var Val Goal) : List (Op Var Val Goal) → Service Var Val Goal
  | [] => x
  | op :: ops => (x.step op).exec ops

section Laws

variable (x : Service Var Val Goal)

theorem bind_wakes (v : Var) (a : Val) :
    (x.bind v a).state.woken = x.state.woken ++ x.state.suspended v ∧
      (x.bind v a).state.suspended v = [] ∧
      (x.bind v a).state.value v = some a := by
  simp [Service.bind, Service.setValue, Service.setWoken, Service.setSuspended]

/-- Only the bound variable's goals move: a goal suspended elsewhere stays. -/
theorem bind_keeps_others (v w : Var) (a : Val) (other : w ≠ v) :
    (x.bind v a).state.suspended w = x.state.suspended w ∧
      (x.bind v a).state.value w = x.state.value w := by
  simp [Service.bind, Service.setValue, Service.setWoken, Service.setSuspended,
    Function.update_of_ne other]

/-- Binding a variable nothing waits on leaves the index and the queue as they
were: an unwatched binding does no service work. -/
theorem bind_unwatched (v : Var) (a : Val) (unwatched : x.state.suspended v = []) :
    (x.bind v a).state.woken = x.state.woken ∧
      (x.bind v a).state.suspended = x.state.suspended := by
  refine ⟨by simp [Service.bind, Service.setValue, Service.setWoken,
    Service.setSuspended, unwatched], ?_⟩
  funext w
  by_cases same : w = v
  · subst same
    simp [Service.bind, Service.setValue, Service.setWoken, Service.setSuspended,
      unwatched]
  · simp [Service.bind, Service.setValue, Service.setWoken, Service.setSuspended,
      Function.update_of_ne same]

theorem suspend_bound (v : Var) (g : Goal) (a : Val) (bound : x.state.value v = some a) :
    (x.suspend v g).state.woken = x.state.woken ++ [g] := by
  simp [Service.suspend, bound, Service.setWoken]

/-- A goal suspended on an unbound variable is woken when the variable is
bound. -/
theorem suspend_then_bind (v : Var) (g : Goal) (a : Val)
    (unbound : x.state.value v = none) :
    g ∈ ((x.suspend v g).bind v a).state.woken := by
  simp [Service.suspend, unbound, Service.bind, Service.setValue, Service.setWoken,
    Service.setSuspended]

/-- After a merge, binding the representative wakes the goals of both
variables, each once. -/
theorem merge_then_bind (u v : Var) (link a : Val) (distinct : u ≠ v) :
    ((x.merge u v link).bind v a).state.woken =
      x.state.woken ++ (x.state.suspended v ++ x.state.suspended u) ∧
      ((x.merge u v link).bind v a).state.suspended u = [] := by
  simp [Service.merge, Service.bind, Service.setValue, Service.setWoken,
    Service.setSuspended, Function.update_of_ne distinct,
    Function.update_of_ne distinct.symm]

/-- Every write logs the old contents of its cell, and undoing that entry
restores the state before the write. -/
theorem setValue_undo (v : Var) (o : Option Val) :
    (x.setValue v o).log = x.log ++ [.value v (x.state.value v)] ∧
      Undo.apply (.value v (x.state.value v)) (x.setValue v o).state = x.state := by
  refine ⟨rfl, ?_⟩
  simp [Service.setValue, Undo.apply]

theorem setSuspended_undo (v : Var) (goals : List Goal) :
    (x.setSuspended v goals).log = x.log ++ [.suspended v (x.state.suspended v)] ∧
      Undo.apply (.suspended v (x.state.suspended v)) (x.setSuspended v goals).state =
        x.state := by
  refine ⟨rfl, ?_⟩
  simp [Service.setSuspended, Undo.apply]

theorem setWoken_undo (goals : List Goal) :
    (x.setWoken goals).log = x.log ++ [.woken x.state.woken] ∧
      Undo.apply (.woken x.state.woken) (x.setWoken goals).state = x.state := by
  refine ⟨rfl, ?_⟩
  simp [Service.setWoken, Undo.apply]

end Laws

/-- A service change undoable to `x`: it appends entries to `x`'s log whose
rollback restores `x`'s state. -/
def Undoable (x y : Service Var Val Goal) : Prop :=
  ∃ entries, y.log = x.log ++ entries ∧ rollback entries y.state = x.state

theorem Undoable.refl (x : Service Var Val Goal) : Undoable x x :=
  ⟨[], by simp, rfl⟩

theorem Undoable.trans {x y z : Service Var Val Goal} (hxy : Undoable x y)
    (hyz : Undoable y z) : Undoable x z := by
  obtain ⟨e₁, hl₁, hr₁⟩ := hxy
  obtain ⟨e₂, hl₂, hr₂⟩ := hyz
  refine ⟨e₁ ++ e₂, by rw [hl₂, hl₁, List.append_assoc], ?_⟩
  rw [rollback_append, hr₂, hr₁]

theorem undoable_setValue (x : Service Var Val Goal) (v : Var) (o : Option Val) :
    Undoable x (x.setValue v o) := by
  obtain ⟨hl, hr⟩ := setValue_undo x v o
  exact ⟨_, hl, by simpa [rollback] using hr⟩

theorem undoable_setSuspended (x : Service Var Val Goal) (v : Var) (goals : List Goal) :
    Undoable x (x.setSuspended v goals) := by
  obtain ⟨hl, hr⟩ := setSuspended_undo x v goals
  exact ⟨_, hl, by simpa [rollback] using hr⟩

theorem undoable_setWoken (x : Service Var Val Goal) (goals : List Goal) :
    Undoable x (x.setWoken goals) := by
  obtain ⟨hl, hr⟩ := setWoken_undo x goals
  exact ⟨_, hl, by simpa [rollback] using hr⟩

theorem undoable_step (x : Service Var Val Goal) (op : Op Var Val Goal) :
    Undoable x (x.step op) := by
  cases op with
  | bind v a =>
      exact ((undoable_setValue _ _ _).trans (undoable_setWoken _ _)).trans
        (undoable_setSuspended _ _ _)
  | suspend v g =>
      simp only [Service.step, Service.suspend]
      split
      · exact undoable_setWoken _ _
      · exact undoable_setSuspended _ _ _
  | merge u v link =>
      exact ((undoable_setValue _ _ _).trans (undoable_setSuspended _ _ _)).trans
        (undoable_setSuspended _ _ _)

/-- Rolling back to a mark restores the binding store, the suspended goals and
the woken queue together, whatever operations ran after the mark. -/
theorem rollback_exec (x : Service Var Val Goal) (ops : List (Op Var Val Goal)) :
    rollback ((x.exec ops).log.drop x.log.length) (x.exec ops).state = x.state := by
  have h : Undoable x (x.exec ops) := by
    induction ops generalizing x with
    | nil => exact Undoable.refl x
    | cons op rest ih => exact (undoable_step x op).trans (ih (x.step op))
  obtain ⟨entries, hl, hr⟩ := h
  rw [hl, List.drop_left]
  exact hr

/-- The entries that restore the binding store. -/
def Undo.isValue : Undo Var Val Goal → Bool
  | .value _ _ => true
  | _ => false

/-- An entry that restores a binding and one that restores the index or the
queue write different parts of the state, so they commute. -/
theorem Undo.apply_comm {a b : Undo Var Val Goal} (ha : a.isValue = true)
    (hb : b.isValue = false) (s : ServiceState Var Val Goal) :
    a.apply (b.apply s) = b.apply (a.apply s) := by
  cases a <;> cases b <;> simp_all [Undo.apply, Undo.isValue]

theorem rollback_values_comm (values : List (Undo Var Val Goal))
    (allValue : ∀ a ∈ values, a.isValue = true) (u : Undo Var Val Goal)
    (notValue : u.isValue = false) (s : ServiceState Var Val Goal) :
    rollback values (u.apply s) = u.apply (rollback values s) := by
  induction values generalizing s with
  | nil => rfl
  | cons a rest ih =>
      simp only [rollback, List.foldr_cons] at ih ⊢
      rw [ih (fun b hb => allValue b (List.mem_cons_of_mem a hb)) s]
      exact Undo.apply_comm (allValue a (List.mem_cons_self)) notValue _

/-- A machine may keep the binding store's history and the service's history
in two logs: rolling back the one chronological log is rolling back the
service's part and then the binding store's, both cut at the same point.
Cutting only one of them is `split_logs_keep_stale_wakeups`. -/
theorem rollback_split (log : List (Undo Var Val Goal)) (s : ServiceState Var Val Goal) :
    rollback log s =
      rollback (log.filter (·.isValue))
        (rollback (log.filter (fun u => !u.isValue)) s) := by
  induction log generalizing s with
  | nil => rfl
  | cons u rest ih =>
      cases hu : u.isValue
      · have values : ∀ a ∈ rest.filter (·.isValue), a.isValue = true := by
          intro a ha
          exact (List.mem_filter.mp ha).2
        simp only [rollback, List.foldr_cons, List.filter_cons, hu] at ih ⊢
        simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_false]
        rw [ih s]
        exact (rollback_values_comm _ values u hu _).symm
      · simp only [rollback, List.foldr_cons, List.filter_cons, hu] at ih ⊢
        simp only [↓reduceIte, Bool.not_true, Bool.false_eq_true]
        rw [ih s]
        rfl

end Service

/-! ## A log keyed by trail marks

A machine records each change with the binding trail's mark at the time and
rolls back to a mark by undoing every change recorded at or after it. A
collection may compact the trail to the checkpoints still reachable, the
checkpoint `c` becoming position `keptPosition kept c`; the history is then
renumbered: a change recorded at mark `t` moves to the position of the last
kept checkpoint at or before `t`, and a change older than every kept
checkpoint leaves the log, since no rollback to a kept checkpoint undoes it.
Rolling the renumbered log back to a checkpoint's new position is rolling the
old log back to the checkpoint (`rollback_rebase`). The kept checkpoints need
not be sorted or distinct. -/

section Marked

variable {Var Val Goal : Type*} [DecidableEq Var]

/-- Undo every entry recorded at or after mark `m`. -/
def rollbackTo (m : ℕ) (log : List (ℕ × Undo Var Val Goal))
    (s : ServiceState Var Val Goal) : ServiceState Var Val Goal :=
  rollback ((log.filter (fun e => m ≤ e.1)).map Prod.snd) s

/-- How many kept checkpoints are at or before mark `t`. -/
def keptUpTo (kept : List ℕ) (t : ℕ) : ℕ := (kept.filter (· ≤ t)).length

/-- A kept checkpoint's position after compaction: how many kept checkpoints
come before it. -/
def keptPosition (kept : List ℕ) (c : ℕ) : ℕ := (kept.filter (· < c)).length

/-- The renumbered log. -/
def rebase (kept : List ℕ) (log : List (ℕ × Undo Var Val Goal)) :
    List (ℕ × Undo Var Val Goal) :=
  log.filterMap fun e =>
    if keptUpTo kept e.1 = 0 then none else some (keptUpTo kept e.1 - 1, e.2)

theorem length_filter_le_of_imp {p q : ℕ → Bool} (h : ∀ x, p x = true → q x = true)
    (l : List ℕ) : (l.filter p).length ≤ (l.filter q).length := by
  induction l with
  | nil => exact Nat.le_refl 0
  | cons a rest ih =>
      cases hp : p a with
      | true =>
          rw [List.filter_cons_of_pos hp, List.filter_cons_of_pos (h a hp)]
          exact Nat.succ_le_succ ih
      | false =>
          rw [List.filter_cons_of_neg (by simp [hp])]
          cases hq : q a with
          | true => rw [List.filter_cons_of_pos hq]; exact Nat.le_succ_of_le ih
          | false => rw [List.filter_cons_of_neg (by simp [hq])]; exact ih

theorem keptUpTo_le_keptPosition (kept : List ℕ) {c t : ℕ} (ht : t < c) :
    keptUpTo kept t ≤ keptPosition kept c :=
  length_filter_le_of_imp (fun x hx => by
    simp only [decide_eq_true_eq] at hx ⊢; omega) kept

theorem keptPosition_lt_keptUpTo {kept : List ℕ} {c t : ℕ} (hc : c ∈ kept) (ht : c ≤ t) :
    keptPosition kept c < keptUpTo kept t := by
  induction kept with
  | nil => exact absurd hc List.not_mem_nil
  | cons a rest ih =>
      unfold keptPosition keptUpTo at ih ⊢
      rcases List.mem_cons.mp hc with hca | hrest
      · subst hca
        have hle := length_filter_le_of_imp (p := fun x => decide (x < c))
          (q := fun x => decide (x ≤ t))
          (fun x hx => by simp only [decide_eq_true_eq] at hx ⊢; omega) rest
        rw [List.filter_cons_of_neg (by simp), List.filter_cons_of_pos (by simpa using ht),
          List.length_cons]
        omega
      · have hlt := ih hrest
        cases Nat.decLt a c with
        | isTrue h1 =>
            rw [List.filter_cons_of_pos (by simpa using h1),
              List.filter_cons_of_pos (by simpa using Nat.le_of_lt (Nat.lt_of_lt_of_le h1 ht)),
              List.length_cons, List.length_cons]
            omega
        | isFalse h1 =>
            rw [List.filter_cons_of_neg (by simpa using h1)]
            cases Nat.decLe a t with
            | isTrue h2 =>
                rw [List.filter_cons_of_pos (by simpa using h2), List.length_cons]
                omega
            | isFalse h2 =>
                rw [List.filter_cons_of_neg (by simpa using h2)]
                exact hlt

/-- A renumbered change is undone by a rollback to a kept checkpoint's new
position exactly when the old change was undone by a rollback to the
checkpoint. -/
theorem rebase_undoes_iff {kept : List ℕ} {c t : ℕ} (hc : c ∈ kept) :
    (keptUpTo kept t ≠ 0 ∧ keptPosition kept c ≤ keptUpTo kept t - 1) ↔ c ≤ t := by
  constructor
  · rintro ⟨h0, hle⟩
    rcases Nat.lt_or_ge t c with hlt | hge
    · have := keptUpTo_le_keptPosition kept hlt
      omega
    · exact hge
  · intro ht
    have := keptPosition_lt_keptUpTo hc ht
    exact ⟨by omega, by omega⟩

theorem rollback_rebase (kept : List ℕ) (c : ℕ) (hc : c ∈ kept)
    (log : List (ℕ × Undo Var Val Goal)) (s : ServiceState Var Val Goal) :
    rollbackTo (keptPosition kept c) (rebase kept log) s = rollbackTo c log s := by
  unfold rollbackTo
  congr 1
  induction log with
  | nil => rfl
  | cons e rest ih =>
      have key := rebase_undoes_iff (kept := kept) (t := e.1) hc
      cases Nat.decEq (keptUpTo kept e.1) 0 with
      | isTrue h0 =>
          have hlt : ¬ c ≤ e.1 := fun h => (key.mpr h).1 h0
          have hr : rebase kept (e :: rest) = rebase kept rest := by
            unfold rebase; rw [List.filterMap_cons, if_pos h0]
          rw [hr, ih, List.filter_cons_of_neg (by simpa using hlt)]
      | isFalse h0 =>
          have hr : rebase kept (e :: rest) =
              (keptUpTo kept e.1 - 1, e.2) :: rebase kept rest := by
            unfold rebase; rw [List.filterMap_cons, if_neg h0]
          rw [hr]
          cases Nat.decLe (keptPosition kept c) (keptUpTo kept e.1 - 1) with
          | isTrue hle =>
              have hce : c ≤ e.1 := key.mp ⟨h0, hle⟩
              rw [List.filter_cons_of_pos (by simpa using hle),
                List.filter_cons_of_pos (by simpa using hce), List.map_cons, List.map_cons, ih]
          | isFalse hle =>
              have hce : ¬ c ≤ e.1 := fun h => hle (key.mpr h).2
              rw [List.filter_cons_of_neg (by simpa using hle),
                List.filter_cons_of_neg (by simpa using hce), ih]

end Marked

/-! ## Goals that wait on several variables

A client's goal can wait on several variables and must run once: the first
binding among them wakes it, and it then leaves the index of every variable
it waited on (a component of residual constraints, re-posted with its
variables' values). Suspending the same goal once per variable, as `Service`
does, would wake it once per variable. The table below keeps each goal once,
with the variables it waits on, by its place in the table. -/

section Table

variable {Var Val Goal : Type*} [DecidableEq Var]

structure TableState (Var Val Goal : Type*) where
  value : Var → Option Val
  goals : List (Goal × List Var)
  /-- The suspended goals, in the order they were suspended. -/
  suspended : List ℕ
  woken : List ℕ

/-- Whether goal `id` waits on `v`. -/
def TableState.waitsOn (s : TableState Var Val Goal) (v : Var) (id : ℕ) : Bool :=
  match s.goals[id]? with
  | some (_, vars) => decide (v ∈ vars)
  | none => false

/-- The suspended goals waiting on `v`, in the order they were suspended. -/
def TableState.watching (s : TableState Var Val Goal) (v : Var) : List ℕ :=
  s.suspended.filter (s.waitsOn v)

/-- Bind `v`: every suspended goal waiting on it is woken, in the order they
were suspended, and leaves the index. -/
def TableState.bind (s : TableState Var Val Goal) (v : Var) (a : Val) :
    TableState Var Val Goal :=
  { s with value := Function.update s.value v (some a),
           suspended := s.suspended.filter (fun id => !s.waitsOn v id),
           woken := s.woken ++ s.watching v }

/-- Suspend a goal on its variables, or wake it at once when one of them is
already bound. -/
def TableState.suspend (s : TableState Var Val Goal) (g : Goal) (vars : List Var) :
    TableState Var Val Goal :=
  if vars.any (fun v => (s.value v).isSome) then
    { s with goals := s.goals ++ [(g, vars)], woken := s.woken ++ [s.goals.length] }
  else
    { s with goals := s.goals ++ [(g, vars)], suspended := s.suspended ++ [s.goals.length] }

/-- Every goal is suspended or woken at most once, and only goals of the
table are. -/
def TableState.Wf (s : TableState Var Val Goal) : Prop :=
  (s.suspended ++ s.woken).Nodup ∧ ∀ id ∈ s.suspended ++ s.woken, id < s.goals.length

section TableLaws

variable (s : TableState Var Val Goal)

theorem table_bind_wakes (v : Var) (a : Val) (id : ℕ) (w : id ∈ s.watching v) :
    id ∈ (s.bind v a).woken ∧ id ∉ (s.bind v a).suspended := by
  have hw : s.waitsOn v id = true := (List.mem_filter.mp w).2
  refine ⟨List.mem_append_right _ w, ?_⟩
  intro h
  have := (List.mem_filter.mp h).2
  simp [hw] at this

theorem table_bind_keeps_others (v : Var) (a : Val) (id : ℕ) (hs : id ∈ s.suspended)
    (other : s.waitsOn v id = false) : id ∈ (s.bind v a).suspended :=
  List.mem_filter.mpr ⟨hs, by simp [other]⟩

/-- Binding a variable no suspended goal waits on changes neither the index
nor the queue. -/
theorem table_bind_unwatched (v : Var) (a : Val) (unwatched : s.watching v = []) :
    (s.bind v a).suspended = s.suspended ∧ (s.bind v a).woken = s.woken := by
  refine ⟨?_, by simp [TableState.bind, unwatched]⟩
  have none : ∀ id ∈ s.suspended, s.waitsOn v id = false := by
    intro id hid
    by_contra h
    have : id ∈ s.watching v := List.mem_filter.mpr ⟨hid, by simpa using h⟩
    simp [unwatched] at this
  exact List.filter_eq_self.mpr (fun id hid => by simp [none id hid])

omit [DecidableEq Var] in
theorem table_suspend_bound (g : Goal) (vars : List Var) (v : Var) (hv : v ∈ vars)
    (a : Val) (bound : s.value v = some a) :
    s.goals.length ∈ (s.suspend g vars).woken := by
  have : vars.any (fun v => (s.value v).isSome) = true :=
    List.any_eq_true.mpr ⟨v, hv, by simp [bound]⟩
  simp [TableState.suspend, this]

/-- A woken goal is never woken again: binding keeps the table well formed,
so a goal appears in the queue at most once. -/
theorem table_bind_wf (v : Var) (a : Val) (wf : s.Wf) : (s.bind v a).Wf := by
  obtain ⟨nodup, bounded⟩ := wf
  have hsub : List.Perm ((s.bind v a).suspended ++ (s.bind v a).woken)
      (s.suspended ++ s.woken) := by
    simp only [TableState.bind, TableState.watching]
    have split := List.filter_append_perm (s.waitsOn v) s.suspended
    calc List.Perm (s.suspended.filter (fun id => !s.waitsOn v id) ++
          (s.woken ++ s.suspended.filter (s.waitsOn v)))
          (s.suspended.filter (fun id => !s.waitsOn v id) ++
            (s.suspended.filter (s.waitsOn v) ++ s.woken)) :=
          List.Perm.append_left _ List.perm_append_comm
      _ = (s.suspended.filter (fun id => !s.waitsOn v id) ++
            s.suspended.filter (s.waitsOn v)) ++ s.woken := by
          rw [List.append_assoc]
      List.Perm _ ((s.suspended.filter (s.waitsOn v) ++
            s.suspended.filter (fun id => !s.waitsOn v id)) ++ s.woken) :=
          List.Perm.append_right _ List.perm_append_comm
      List.Perm _ (s.suspended ++ s.woken) := List.Perm.append_right _ split
  exact ⟨hsub.nodup_iff.mpr nodup,
    fun id hid => by simpa [TableState.bind] using bounded id (hsub.subset hid)⟩

omit [DecidableEq Var] in
theorem table_suspend_wf (g : Goal) (vars : List Var) (wf : s.Wf) :
    (s.suspend g vars).Wf := by
  obtain ⟨nodup, bounded⟩ := wf
  have fresh : s.goals.length ∉ s.suspended ++ s.woken :=
    fun h => (Nat.lt_irrefl _) (bounded _ h)
  unfold TableState.suspend
  split
  · refine ⟨?_, ?_⟩
    · have : s.suspended ++ (s.woken ++ [s.goals.length]) =
          (s.suspended ++ s.woken) ++ [s.goals.length] := by simp
      simp only [this]
      exact List.nodup_append.mpr ⟨nodup, List.nodup_singleton _,
        fun x hx y hy => by
          simp only [List.mem_singleton] at hy
          subst hy
          exact fun h => fresh (h ▸ hx)⟩
    · intro id hid
      simp only [List.length_append, List.length_singleton]
      rcases List.mem_append.mp hid with h | h
      · exact Nat.lt_succ_of_lt (bounded id (List.mem_append_left _ h))
      · rcases List.mem_append.mp h with h | h
        · exact Nat.lt_succ_of_lt (bounded id (List.mem_append_right _ h))
        · simp only [List.mem_singleton] at h
          omega
  · refine ⟨?_, ?_⟩
    · have perm : List.Perm ((s.suspended ++ [s.goals.length]) ++ s.woken)
          ((s.suspended ++ s.woken) ++ [s.goals.length]) := by
        rw [List.append_assoc, List.append_assoc]
        exact List.Perm.append_left _ List.perm_append_comm
      refine perm.nodup_iff.mpr ?_
      exact List.nodup_append.mpr ⟨nodup, List.nodup_singleton _,
        fun x hx y hy => by
          simp only [List.mem_singleton] at hy
          subst hy
          exact fun h => fresh (h ▸ hx)⟩
    · intro id hid
      simp only [List.length_append, List.length_singleton]
      rcases List.mem_append.mp hid with h | h
      · rcases List.mem_append.mp h with h | h
        · exact Nat.lt_succ_of_lt (bounded id (List.mem_append_left _ h))
        · simp only [List.mem_singleton] at h
          omega
      · exact Nat.lt_succ_of_lt (bounded id (List.mem_append_right _ h))

end TableLaws

end Table

/-! ## Executable positive and negative controls -/

def chainRules : Bool → HornRule (Fin 3)
  | false => ⟨{0}, {1}⟩
  | true => ⟨{1}, {2}⟩

def leastPending : Selector Bool := fun pending nonempty =>
  ⟨pending.min' nonempty, pending.min'_mem nonempty⟩

theorem chain_saturates : solve chainRules leastPending {0} = {0, 1, 2} := by decide

def startupRules : Bool → HornRule (Fin 2)
  | false => ⟨∅, {0}⟩
  | true => ⟨{0}, {1}⟩

theorem empty_premise_fires_initially :
    solve startupRules leastPending ∅ = {0, 1} := by decide

def cycleRules : Bool → HornRule (Fin 2)
  | false => ⟨{0}, {1}⟩
  | true => ⟨{1}, {0}⟩

theorem recursive_rules_need_seed :
    solve cycleRules leastPending ∅ = ∅ ∧
    solve cycleRules leastPending {0} = {0, 1} := by decide

def jointPremises : Bool → HornRule (Fin 3)
  | false => ⟨{0, 1}, {2}⟩
  | true => ⟨{2}, ∅⟩

theorem duplicate_notifications_coalesce :
    wakeIndexed jointPremises ∅ {0, 1} = {false} := by decide

theorem insufficient_fuel_is_not_completion :
    (drain chainRules leastPending 1 (initial {0})).pending ≠ ∅ ∧
    ¬ Quiescent (fun i => (chainRules i).propagator)
      (drain chainRules leastPending 1 (initial {0})).store := by
  unfold Quiescent
  decide

/-- Stores deduplicate facts, so store equality does not justify deduplicating
the bag of successful derivations. -/
theorem two_derivations_one_fact :
    let rules : Bool → HornRule (Fin 1) := fun _ => ⟨∅, {0}⟩
    ([false, true] : List Bool).length = 2 ∧
      (run (fun i => (rules i).propagator) [false, true] ∅).card = 1 := by decide

def absentThenTell (s : Finset Bool) : Finset Bool :=
  if true ∈ s then s else insert false s

/-- A test of absence is not monotone, even though its update only adds facts. -/
theorem absence_guard_not_monotone : ¬ Monotone absentThenTell := by
  intro h
  have bound := h (Finset.empty_subset ({true} : Finset Bool))
  have member : false ∈ absentThenTell ∅ := by decide
  have : false ∈ absentThenTell {true} := bound member
  simp [absentThenTell] at this

/-- An absence guard and an unconditional tell can reach two different common
fixed points. Inflationarity alone is not the scheduling-independence law. -/
theorem absence_guard_changes_settled_result :
    absentThenTell (insert true ∅) ≠ insert true (absentThenTell ∅) ∧
    absentThenTell {true} = {true} ∧
    absentThenTell {false, true} = {false, true} := by decide

theorem one_pass_order_matters :
    run (fun i => (chainRules i).propagator) [false, true] {0} ≠
    run (fun i => (chainRules i).propagator) [true, false] {0} := by decide

/-- Waking the previously stable rule is essential: removing a processed rule
without notifications could report this incomplete store as finished. -/
theorem newly_enabled_rule_must_wake :
    let w : WorkState (Fin 3) Bool := ⟨{0}, {false}⟩
    Valid chainRules w ∧ true ∈ (step chainRules false w).pending ∧
      ¬ Quiescent (fun i => (chainRules i).propagator) {0, 1} := by
  unfold Valid Quiescent
  decide

theorem irrelevant_rule_not_woken :
    false ∉ wakeIndexed chainRules {0} {0, 1} := by decide

theorem starving_schedule_not_quiescent (n : Nat) :
    ¬ Quiescent (fun i => (chainRules i).propagator)
      (run (fun i => (chainRules i).propagator) (List.replicate (n + 1) false) {0}) := by
  have fixed : ∀ k, run (fun i => (chainRules i).propagator)
      (List.replicate k false) {0, 1} = {0, 1} := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => simpa [List.replicate_succ, run, chainRules, HornRule.propagator,
        HornRule.apply] using ih
  have head : (chainRules false).apply {0} = {0, 1} := by decide
  have first : run (fun i => (chainRules i).propagator)
      (List.replicate (n + 1) false) {0} = {0, 1} := by
    rw [List.replicate_succ, run]
    change run (fun i => (chainRules i).propagator)
      (List.replicate n false) ((chainRules false).apply {0}) = _
    rw [head]
    exact fixed n
  rw [first]
  unfold Quiescent
  decide

/-- A goal suspended on one variable is not woken by binding another. -/
theorem other_binding_not_woken :
    let x : Service Bool Nat String := ⟨⟨fun _ => none, fun v => if v then ["g"] else [], []⟩, []⟩
    (x.bind false 1).state.woken = [] ∧ (x.bind false 1).state.suspended true = ["g"] := by
  decide

/-- Suspending without first reading the variable loses the wakeup of a goal
whose variable is already bound: nothing will bind it again. -/
theorem suspend_without_check_loses_wakeup :
    let x : Service Bool Nat String := ⟨⟨fun _ => some 1, fun _ => [], []⟩, []⟩
    (x.setSuspended true ["g"]).state.woken = [] ∧ (x.suspend true "g").state.woken = ["g"] := by
  decide

/-- A service with one goal suspended on `true`. -/
def oneSuspended : Service Bool Nat String :=
  ⟨⟨fun _ => none, fun v => if v then ["g"] else [], []⟩, []⟩

/-- Undoing only the binding keeps the goal it woke; the one log undoes both:
bindings, suspended goals and woken goals must share one log. -/
theorem split_logs_keep_stale_wakeups :
    (Undo.apply (.value true none) (oneSuspended.bind true 1).state).woken = ["g"] ∧
      (rollback (oneSuspended.bind true 1).log (oneSuspended.bind true 1).state).woken =
        [] := by
  decide

/-- Renumbering a change to the next kept checkpoint, instead of the last one
at or before it, makes a rollback to that later checkpoint undo a change made
before it: with checkpoints 10 and 20 kept, a change at 12 survives a rollback
to 20, and survives it after `rebase`, but not after that renumbering. -/
theorem rebase_to_next_checkpoint_undoes_too_much :
    let log : List (ℕ × Undo Bool Nat String) := [(12, .woken [])]
    let s : ServiceState Bool Nat String := ⟨fun _ => none, fun _ => [], ["g"]⟩
    (rollbackTo 20 log s).woken = ["g"] ∧
      (rollbackTo (keptPosition [10, 20] 20) (rebase [10, 20] log) s).woken = ["g"] ∧
      (rollbackTo (keptPosition [10, 20] 20)
        (log.map fun e => (keptPosition [10, 20] e.1, e.2)) s).woken = [] := by
  decide

#print axioms quiescent_runs_equal
#print axioms wakeIndexed_eq_wake
#print axioms potential_step_lt
#print axioms solve_least
#print axioms solve_policy_independent
#print axioms solve_least_model
#print axioms chain_saturates
#print axioms newly_enabled_rule_must_wake
#print axioms rollback_exec
#print axioms rollback_split
#print axioms merge_then_bind
#print axioms suspend_then_bind
#print axioms table_bind_wakes
#print axioms table_bind_unwatched
#print axioms table_suspend_bound
#print axioms table_bind_wf
#print axioms table_suspend_wf
#print axioms rollback_rebase
#print axioms rebase_to_next_checkpoint_undoes_too_much

end Mettapedia.Machines.ConstraintPropagation
