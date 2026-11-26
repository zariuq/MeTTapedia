import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CommFootprint
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Context
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu
import Mathlib.Logic.Relation

/-!
# Running the rho COMM step on parallel workers

A parallel run keeps the live processes of a rho program as *tasks*: queued, running, or waiting on
a channel.  A scheduler repeatedly chooses the next event of the run's reduction history

* a COMM between a task holding an output and a task holding an input on the same channel,
* a COMM between a task holding an output and a task holding a persistent input on its channel,
  which consumes the send and keeps the receive (Rholang's `for (y <= x)`),
* the spawn of a task holding a parallel composition into one task per component,
* the end of a task holding `0`, or
* a name drawn by a task from its supply,

together with the party of a COMM that finds the match (the one of the two that runs second and meets
the other waiting) and the worker that runs the event.

Two disciplines sit beside the processes and are parameters of a `Runtime`.

* **Placement** (`Naming`).  Every task holds a *supply*: its position in the spawn tree and the
  counters from which it draws names.  A naming discipline says which name a supply gives next, where
  the components of a spawned parallel composition are placed, and where a COMM's continuation is
  placed — possibly depending on which party found the match.
* **Memory** (`Memory`).  The working memory of a COMM — its scratch and the continuation it builds —
  lives either in the worker's arena, where it outlives the task, or in the task's own region, which
  is released when the task ends while the tasks it creates receive what they need.

Each event is the existing COMM step on the bag of live processes, or a structural congruence of
that bag (`comm_reduces`, `spawn_congruent`, `finish_congruent`, `draw_processes`).  So every valid run
without persistent receives is a rho reduction sequence with one reduction per COMM
(`run_realizes`): the disciplines decide placement and memory only, never what the program does.  A
persistent receive is the replication of a receive (`persistentIn`); a COMM with it is the unfolding
of one copy followed by the COMM step, in the derived calculus with replication
(`persistentComm_realizes`), and every valid run is a sequence of such steps and structural
congruences (`run_realizes_derived`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.ParallelExecution

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CommFootprint

/-- The null process. -/
abbrev nil : Pattern := .apply "PZero" []

/-- A persistent input `for (y <= channel) body`: the replication of the input on `channel`, which
stays after each COMM. -/
def persistentIn (channel body : Pattern) : Pattern := .apply "PReplicate" [commIn channel body]

/-- The party of a COMM that finds the match: the one that runs second and meets the other
waiting on the channel. -/
inductive Finder where
  | sender
  | receiver
  deriving DecidableEq, Repr

/-- A live process of a parallel run, with the supply it draws names from and the memory it holds
in its own region. -/
structure Task (S : Type) where
  process : Pattern
  supply : S
  region : ℕ
  deriving DecidableEq

/-- A naming discipline. -/
structure Naming (S N : Type) where
  /-- The next name a supply gives, and the supply after giving it. -/
  draw : S → N × S
  /-- `component s k i` is the supply of component `i` of a parallel composition of `k` components
  spawned by a task with supply `s`. -/
  component : S → ℕ → ℕ → S
  /-- The supply of a COMM's continuation, from the sender's supply, the receiver's supply, the
  channel, and the party that found the match. -/
  continuation : S → S → Pattern → Finder → S
  /-- The supply of the continuation of a COMM with a persistent receive, which keeps its own
  supply: from the sender's supply, the receive's supply, the channel, and the finder. -/
  persistentContinuation : S → S → Pattern → Finder → S

/-- Where the working memory of a running task lives. -/
inductive Memory where
  /-- In the worker's arena: allocations outlive the task. -/
  | workerArena
  /-- In the task's own region: released when the task ends; a task it creates receives what that
  task needs. -/
  | taskRegion
  deriving DecidableEq, Repr

/-- `need p` is the memory the data of a live process `p` occupies; `scratch n q p` is the transient
memory of a COMM on channel `n` with message `q` and continuation body `p`, besides the continuation
it builds. -/
structure Costs where
  need : Pattern → ℕ
  scratch : Pattern → Pattern → Pattern → ℕ

/-- A runtime: a naming discipline, a memory discipline and the costs of its data. -/
structure Runtime (S N : Type) where
  naming : Naming S N
  memory : Memory
  costs : Costs

namespace Runtime

variable {S N : Type} (rt : Runtime S N)

/-- The working memory of a COMM: its scratch and the continuation it builds. -/
def work (channel message body : Pattern) : ℕ :=
  rt.costs.scratch channel message body + rt.costs.need (commRes body message)

/-- What a task created holding `process` receives in its own region: what it needs, under task
regions; nothing under worker arenas, where its data stays in an arena. -/
def handover (process : Pattern) : ℕ :=
  match rt.memory with
  | .workerArena => 0
  | .taskRegion => rt.costs.need process

/-- What a COMM leaves in its worker's arena: all of its working memory under worker arenas,
nothing under task regions. -/
def retained (channel message body : Pattern) : ℕ :=
  match rt.memory with
  | .workerArena => rt.work channel message body
  | .taskRegion => 0

end Runtime

/-- An event of a run's reduction history. -/
inductive Event (S : Type) where
  /-- The output of `message` on `channel` held by `sender` meets the input on `channel` with
  continuation `body` held by `receiver`. -/
  | comm (channel message body : Pattern) (sender receiver : Task S)
  /-- The output of `message` on `channel` held by `sender` meets the persistent input on `channel`
  with continuation `body` held by `receiver`: the send is consumed and the receive stays. -/
  | persistentComm (channel message body : Pattern) (sender receiver : Task S)
  /-- A task holding the parallel composition of `components` spawns a task for each. -/
  | spawn (parent : Task S) (components : List Pattern)
  /-- A task holding `0` ends. -/
  | finish (task : Task S)
  /-- A task draws a name from its supply. -/
  | draw (task : Task S)

/-- A scheduler choice: the next event, the party that finds the match when the event is a COMM,
and the worker that runs it. -/
structure Choice (S W : Type) where
  event : Event S
  finder : Finder
  worker : W

/-- The state of a parallel run: the live tasks, the memory in each worker's arena, and the names
drawn so far, oldest first. -/
structure State (S N W : Type) where
  tasks : Multiset (Task S)
  arena : W → ℕ
  drawn : List N

variable {S N W : Type}

/-- An event can happen when its tasks are live and have the right processes. -/
def Event.Enabled (tasks : Multiset (Task S)) : Event S → Prop
  | .comm channel message body sender receiver =>
      sender.process = commOut channel message ∧ receiver.process = commIn channel body ∧
        {sender, receiver} ≤ tasks
  | .persistentComm channel message body sender receiver =>
      sender.process = commOut channel message ∧ receiver.process = persistentIn channel body ∧
        {sender, receiver} ≤ tasks
  | .spawn parent components => parent.process = bag components ∧ parent ∈ tasks
  | .finish task => task.process = nil ∧ task ∈ tasks
  | .draw task => task ∈ tasks

/-- The continuation of a COMM, placed by the naming discipline and holding what the memory
discipline hands over. -/
def continuationTask (rt : Runtime S N) (channel message body : Pattern) (sender receiver : Task S)
    (finder : Finder) : Task S where
  process := commRes body message
  supply := rt.naming.continuation sender.supply receiver.supply channel finder
  region := rt.handover (commRes body message)

/-- The continuation of a COMM with a persistent receive. -/
def persistentContinuationTask (rt : Runtime S N) (channel message body : Pattern)
    (sender receiver : Task S) (finder : Finder) : Task S where
  process := commRes body message
  supply := rt.naming.persistentContinuation sender.supply receiver.supply channel finder
  region := rt.handover (commRes body message)

/-- The tasks a spawn creates, one per component. -/
def spawned (rt : Runtime S N) (parent : Task S) (components : List Pattern) : List (Task S) :=
  components.mapIdx fun i process =>
    ⟨process, rt.naming.component parent.supply components.length i, rt.handover process⟩

/-- A task after drawing a name. -/
def drawnTask (rt : Runtime S N) (task : Task S) : Task S :=
  { task with supply := (rt.naming.draw task.supply).2 }

variable [DecidableEq S] [DecidableEq W]

/-- One event of a run, as chosen by the scheduler.  A COMM removes its two parties and adds the
continuation; its working memory is left in the worker's arena or released with the finder's region,
according to the memory discipline. -/
def step (rt : Runtime S N) (st : State S N W) : Choice S W → State S N W
  | ⟨.comm channel message body sender receiver, finder, worker⟩ =>
      { tasks := continuationTask rt channel message body sender receiver finder ::ₘ
          (st.tasks - {sender, receiver})
        arena := st.arena + Pi.single worker (rt.retained channel message body)
        drawn := st.drawn }
  | ⟨.persistentComm channel message body sender receiver, finder, worker⟩ =>
      { tasks := persistentContinuationTask rt channel message body sender receiver finder ::ₘ
          st.tasks.erase sender
        arena := st.arena + Pi.single worker (rt.retained channel message body)
        drawn := st.drawn }
  | ⟨.spawn parent components, _, _⟩ =>
      { st with tasks := (spawned rt parent components : Multiset (Task S)) + st.tasks.erase parent }
  | ⟨.finish task, _, _⟩ => { st with tasks := st.tasks.erase task }
  | ⟨.draw task, _, _⟩ =>
      { st with
        tasks := drawnTask rt task ::ₘ st.tasks.erase task
        drawn := st.drawn ++ [(rt.naming.draw task.supply).1] }

/-- A run: the scheduler's choices, applied in order. -/
def run (rt : Runtime S N) (st : State S N W) (choices : List (Choice S W)) : State S N W :=
  choices.foldl (step rt) st

/-- A run is valid when each of its events can happen when it is chosen. -/
def Valid (rt : Runtime S N) : State S N W → List (Choice S W) → Prop
  | _, [] => True
  | st, choice :: rest => choice.event.Enabled st.tasks ∧ Valid rt (step rt st choice) rest

@[simp] theorem run_nil (rt : Runtime S N) (st : State S N W) : run rt st [] = st := rfl

@[simp] theorem run_cons (rt : Runtime S N) (st : State S N W) (choice : Choice S W)
    (rest : List (Choice S W)) : run rt st (choice :: rest) = run rt (step rt st choice) rest := rfl

theorem run_append (rt : Runtime S N) (st : State S N W) (first second : List (Choice S W)) :
    run rt st (first ++ second) = run rt (run rt st first) second := by
  simp [run, List.foldl_append]

@[simp] theorem valid_nil (rt : Runtime S N) (st : State S N W) : Valid rt st [] := trivial

@[simp] theorem valid_cons (rt : Runtime S N) (st : State S N W) (choice : Choice S W)
    (rest : List (Choice S W)) :
    Valid rt st (choice :: rest) ↔ choice.event.Enabled st.tasks ∧ Valid rt (step rt st choice) rest :=
  Iff.rfl

theorem valid_append (rt : Runtime S N) (st : State S N W) (first second : List (Choice S W)) :
    Valid rt st (first ++ second) ↔ Valid rt st first ∧ Valid rt (run rt st first) second := by
  induction first generalizing st with
  | nil => simp
  | cons choice rest ih => simp [ih, and_assoc]

/-! ## Events on a known part of the bag -/

theorem step_comm (rt : Runtime S N) (st : State S N W) {channel message body : Pattern}
    {sender receiver : Task S} {frame : Multiset (Task S)} (finder : Finder) (worker : W)
    (split : st.tasks = {sender, receiver} + frame) :
    step rt st ⟨.comm channel message body sender receiver, finder, worker⟩ =
      { tasks := continuationTask rt channel message body sender receiver finder ::ₘ frame
        arena := st.arena + Pi.single worker (rt.retained channel message body)
        drawn := st.drawn } := by
  simp [step, split]

theorem step_persistentComm (rt : Runtime S N) (st : State S N W) {channel message body : Pattern}
    {sender receiver : Task S} {frame : Multiset (Task S)} (finder : Finder) (worker : W)
    (split : st.tasks = sender ::ₘ frame) :
    step rt st ⟨.persistentComm channel message body sender receiver, finder, worker⟩ =
      { tasks := persistentContinuationTask rt channel message body sender receiver finder ::ₘ frame
        arena := st.arena + Pi.single worker (rt.retained channel message body)
        drawn := st.drawn } := by
  simp [step, split]

theorem step_spawn (rt : Runtime S N) (st : State S N W) {parent : Task S}
    {components : List Pattern} {frame : Multiset (Task S)} (finder : Finder) (worker : W)
    (split : st.tasks = parent ::ₘ frame) :
    step rt st ⟨.spawn parent components, finder, worker⟩ =
      { st with tasks := (spawned rt parent components : Multiset (Task S)) + frame } := by
  simp [step, split]

theorem step_finish (rt : Runtime S N) (st : State S N W) {task : Task S}
    {frame : Multiset (Task S)} (finder : Finder) (worker : W)
    (split : st.tasks = task ::ₘ frame) :
    step rt st ⟨.finish task, finder, worker⟩ = { st with tasks := frame } := by
  simp [step, split]

theorem step_draw (rt : Runtime S N) (st : State S N W) {task : Task S}
    {frame : Multiset (Task S)} (finder : Finder) (worker : W)
    (split : st.tasks = task ::ₘ frame) :
    step rt st ⟨.draw task, finder, worker⟩ =
      { st with
        tasks := drawnTask rt task ::ₘ frame
        drawn := st.drawn ++ [(rt.naming.draw task.supply).1] } := by
  simp [step, split]

/-! ## Every event is the COMM step or a structural congruence -/

/-- The bag of live processes. -/
noncomputable def processes (st : State S N W) : Pattern := bag (st.tasks.map Task.process).toList

omit [DecidableEq S] in
theorem spawned_processes (rt : Runtime S N) (parent : Task S) (components : List Pattern) :
    (spawned rt parent components).map Task.process = components := by
  apply List.ext_getElem
  · simp [spawned]
  · intro i _ _
    simp [spawned]

private theorem bag_congruent_of_eq {first second : Multiset Pattern} {list : List Pattern}
    (same : first = second) (listed : (list : Multiset Pattern) = second) :
    bag first.toList ≡ bag list := by
  subst same
  apply bag_perm
  exact Multiset.coe_eq_coe.mp (by rw [Multiset.coe_toList, listed])

/-- **A COMM event is the rho COMM step** on the bag of live processes. -/
theorem comm_reduces (rt : Runtime S N) (st : State S N W) {channel message body : Pattern}
    {sender receiver : Task S} (finder : Finder) (worker : W)
    (enabled : (Event.comm channel message body sender receiver).Enabled st.tasks) :
    Nonempty (Reduces (processes st)
      (processes (step rt st ⟨.comm channel message body sender receiver, finder, worker⟩))) := by
  obtain ⟨sent, received, present⟩ := enabled
  apply reduces_of_commRule (n := channel) (q := message) (p := body)
  refine ⟨(st.tasks - {sender, receiver}).map Task.process, ?_, ?_⟩
  · rw [Multiset.coe_toList]
    conv_lhs => rw [← tsub_add_cancel_of_le present]
    simp [Multiset.map_add, sent, received, commConsumed, add_comm]
  · rw [Multiset.coe_toList]
    simp [step, continuationTask, commProduced]

/-- **A spawn is a structural congruence**: the parallel composition is flattened into the bag. -/
theorem spawn_congruent (rt : Runtime S N) (st : State S N W) {parent : Task S}
    {components : List Pattern} (finder : Finder) (worker : W)
    (enabled : (Event.spawn parent components).Enabled st.tasks) :
    processes st ≡ processes (step rt st ⟨.spawn parent components, finder, worker⟩) := by
  obtain ⟨running, present⟩ := enabled
  let rest := ((st.tasks.erase parent).map Task.process).toList
  have before : processes st ≡ bag (bag components :: rest) :=
    bag_congruent_of_eq rfl (by
      rw [← Multiset.cons_coe, Multiset.coe_toList, ← running, ← Multiset.map_cons,
        Multiset.cons_erase present])
  have after : processes (step rt st ⟨.spawn parent components, finder, worker⟩) ≡
      bag (components ++ rest) :=
    bag_congruent_of_eq rfl (by
      rw [← Multiset.coe_add, Multiset.coe_toList]
      simp [step, Multiset.map_add, Multiset.map_coe, spawned_processes])
  exact StructuralCongruence.trans _ _ _ before
    (StructuralCongruence.trans _ _ _ (Context.par_flatten_head components rest)
      (StructuralCongruence.symm _ _ after))

private theorem nil_head_congruent (rest : List Pattern) : bag (nil :: rest) ≡ bag rest := by
  have empty : bag (nil :: rest) ≡ bag (bag [] :: rest) := by
    refine StructuralCongruence.par_cong _ _ (by simp) ?_
    intro i first second
    cases i with
    | zero => exact StructuralCongruence.symm _ _ StructuralCongruence.par_empty
    | succ i => exact StructuralCongruence.refl _
  exact StructuralCongruence.trans _ _ _ empty (by
    simpa using Context.par_flatten_head [] rest)

/-- **A task ending at `0` is a structural congruence**: `0 | rest ≡ rest`. -/
theorem finish_congruent (rt : Runtime S N) (st : State S N W) {task : Task S} (finder : Finder)
    (worker : W) (enabled : (Event.finish task).Enabled st.tasks) :
    processes st ≡ processes (step rt st ⟨.finish task, finder, worker⟩) := by
  obtain ⟨ended, present⟩ := enabled
  let rest := ((st.tasks.erase task).map Task.process).toList
  have before : processes st ≡ bag (nil :: rest) :=
    bag_congruent_of_eq rfl (by
      rw [← Multiset.cons_coe, Multiset.coe_toList, ← ended, ← Multiset.map_cons,
        Multiset.cons_erase present])
  have after : processes (step rt st ⟨.finish task, finder, worker⟩) ≡ bag rest :=
    bag_congruent_of_eq rfl (by simp [rest, step])
  exact StructuralCongruence.trans _ _ _ before
    (StructuralCongruence.trans _ _ _ (nil_head_congruent rest)
      (StructuralCongruence.symm _ _ after))

/-- **Drawing a name leaves the processes unchanged.** -/
theorem draw_processes (rt : Runtime S N) (st : State S N W) {task : Task S} (finder : Finder)
    (worker : W) (enabled : (Event.draw task).Enabled st.tasks) :
    processes (step rt st ⟨.draw task, finder, worker⟩) = processes st := by
  have same : (drawnTask rt task ::ₘ st.tasks.erase task).map Task.process =
      st.tasks.map Task.process := by
    rw [Multiset.map_cons]
    conv_rhs => rw [← Multiset.cons_erase (show task ∈ st.tasks from enabled), Multiset.map_cons]
    rfl
  simp only [processes, step]
  rw [same]

/-- **A COMM with a persistent receive is two derived reductions**: the replicated input unfolds
one copy, which meets the output by the COMM step; the replication stays. -/
theorem persistentComm_realizes (rt : Runtime S N) (st : State S N W)
    {channel message body : Pattern} {sender receiver : Task S} (finder : Finder) (worker : W)
    (enabled : (Event.persistentComm channel message body sender receiver).Enabled st.tasks) :
    Nonempty (DerivedRepNu.ReducesDerivedStar (processes st)
      (processes (step rt st ⟨.persistentComm channel message body sender receiver, finder, worker⟩))) := by
  obtain ⟨sent, received, present⟩ := enabled
  obtain ⟨frame, whole⟩ : ∃ frame, st.tasks = sender ::ₘ receiver ::ₘ frame := by
    refine ⟨st.tasks - {sender, receiver}, ?_⟩
    conv_lhs => rw [← tsub_add_cancel_of_le present, add_comm]
    rw [Multiset.insert_eq_cons, Multiset.cons_add, Multiset.singleton_add]
  let restList := (frame.map Task.process).toList
  have listed : (((st.tasks.map Task.process).toList : List Pattern) : Multiset Pattern) =
      commOut channel message ::ₘ persistentIn channel body ::ₘ (restList : Multiset Pattern) := by
    rw [Multiset.coe_toList, Multiset.coe_toList, whole]
    simp [sent, received]
  have member : persistentIn channel body ∈ (st.tasks.map Task.process).toList := by
    rw [← Multiset.mem_coe, listed]
    simp
  obtain ⟨before, after, split⟩ := List.append_of_mem member
  have unfold : DerivedRepNu.ReducesDerived (processes st)
      (bag (before ++ [bag [commIn channel body, persistentIn channel body]] ++ after)) := by
    have shape : processes st =
        bag (before ++ [.apply "PReplicate" [commIn channel body]] ++ after) := by
      simp only [processes, split, persistentIn, List.append_assoc, List.singleton_append]
    rw [shape]
    exact DerivedRepNu.ReducesDerived.par_any DerivedRepNu.ReducesDerived.rep_unfold
  have others : (before ++ after).Perm (commOut channel message :: restList) := by
    have moved : ((before ++ persistentIn channel body :: after : List Pattern) : Multiset Pattern) =
        persistentIn channel body ::ₘ ((before ++ after : List Pattern) : Multiset Pattern) := by
      rw [Multiset.cons_coe]
      exact Multiset.coe_eq_coe.mpr List.perm_middle
    have full : persistentIn channel body ::ₘ ((before ++ after : List Pattern) : Multiset Pattern) =
        persistentIn channel body ::ₘ commOut channel message ::ₘ (restList : Multiset Pattern) := by
      rw [← moved, ← split, listed, Multiset.cons_swap]
    rw [← Multiset.coe_eq_coe, ← Multiset.cons_coe]
    exact (Multiset.cons_inj_right _).mp full
  have toEnd : (before ++ [bag [commIn channel body, persistentIn channel body]] ++ after).Perm
      ((before ++ after) ++ [bag [commIn channel body, persistentIn channel body]]) := by
    rw [List.append_assoc, List.singleton_append]
    exact List.perm_middle.trans (List.perm_append_comm
      (l₁ := [bag [commIn channel body, persistentIn channel body]]) (l₂ := before ++ after))
  have front : bag (before ++ [bag [commIn channel body, persistentIn channel body]] ++ after) ≡
      bag (commOut channel message :: commIn channel body :: persistentIn channel body :: restList) :=
    StructuralCongruence.trans _ _ _ (bag_perm toEnd)
      (StructuralCongruence.trans _ _ _ (StructuralCongruence.par_flatten _ _)
        (bag_perm ((others.append_right _).trans (List.Perm.cons _ List.perm_append_comm))))
  have erased : st.tasks.erase sender = receiver ::ₘ frame := by
    rw [whole, Multiset.erase_cons_head]
  have back : bag (commRes body message :: persistentIn channel body :: restList) ≡
      processes (step rt st ⟨.persistentComm channel message body sender receiver, finder, worker⟩) := by
    apply bag_perm
    rw [← Multiset.coe_eq_coe, Multiset.coe_toList, ← Multiset.cons_coe, ← Multiset.cons_coe,
      Multiset.coe_toList]
    simp only [step, persistentContinuationTask, Multiset.map_cons, erased, received]
  exact ⟨.step unfold (.step (.core (Reduces.equiv front
    (comm_at_head channel message body (persistentIn channel body :: restList)) back)) (.refl _))⟩

/-- An event of the core calculus: anything but a COMM with a persistent receive. -/
def Event.IsCore : Event S → Prop
  | .persistentComm .. => False
  | _ => True

/-- A step of the calculus with derived replication, or a structural congruence. -/
def DerivedOrCongruent (source target : Pattern) : Prop :=
  Nonempty (DerivedRepNu.ReducesDerived source target) ∨ source ≡ target

private theorem derivedStar_chain {source target : Pattern}
    (reduction : DerivedRepNu.ReducesDerivedStar source target) :
    Relation.ReflTransGen DerivedOrCongruent source target := by
  induction reduction with
  | refl => exact .refl
  | step first _ later => exact .head (Or.inl ⟨first⟩) later

/-- **Every valid run is a sequence of derived reductions and structural congruences**, persistent
receives included. -/
theorem run_realizes_derived (rt : Runtime S N) (st : State S N W) (choices : List (Choice S W))
    (valid : Valid rt st choices) :
    Relation.ReflTransGen DerivedOrCongruent (processes st) (processes (run rt st choices)) := by
  induction choices generalizing st with
  | nil => exact .refl
  | cons choice rest ih =>
      obtain ⟨enabled, later⟩ := valid
      refine Relation.ReflTransGen.trans ?_ (ih (step rt st choice) later)
      obtain ⟨event, finder, worker⟩ := choice
      cases event with
      | comm channel message body sender receiver =>
          obtain ⟨first⟩ := comm_reduces rt st finder worker enabled
          exact .single (Or.inl ⟨.core first⟩)
      | persistentComm channel message body sender receiver =>
          obtain ⟨reduction⟩ := persistentComm_realizes rt st finder worker enabled
          exact derivedStar_chain reduction
      | spawn parent components =>
          exact .single (Or.inr (spawn_congruent rt st finder worker enabled))
      | finish task =>
          exact .single (Or.inr (finish_congruent rt st finder worker enabled))
      | draw task =>
          rw [draw_processes rt st finder worker enabled]

/-- The number of COMMs a run performs. -/
def commCount : List (Choice S W) → ℕ
  | [] => 0
  | ⟨.comm .., _, _⟩ :: rest => commCount rest + 1
  | _ :: rest => commCount rest

omit [DecidableEq S] [DecidableEq W] in
@[simp] theorem commCount_append (first second : List (Choice S W)) :
    commCount (first ++ second) = commCount first + commCount second := by
  induction first with
  | nil => simp [commCount]
  | cons choice rest ih =>
      obtain ⟨event, finder, worker⟩ := choice
      cases event <;> simp [commCount, ih, Nat.add_right_comm]

/-- **Every valid run of the core calculus is a rho reduction sequence**, with exactly one
reduction per COMM, up to the structural congruence of the final bag. -/
theorem run_realizes (rt : Runtime S N) (st : State S N W) (choices : List (Choice S W))
    (valid : Valid rt st choices) (core : ∀ choice ∈ choices, choice.event.IsCore) :
    ∃ target, Nonempty (ReducesN (commCount choices) (processes st) target) ∧
      target ≡ processes (run rt st choices) := by
  induction choices generalizing st with
  | nil => exact ⟨processes st, ⟨ReducesN.zero _⟩, StructuralCongruence.refl _⟩
  | cons choice rest ih =>
      obtain ⟨enabled, later⟩ := valid
      obtain ⟨target, ⟨reduction⟩, congruent⟩ :=
        ih (step rt st choice) later fun other member => core other (List.mem_cons_of_mem _ member)
      obtain ⟨event, finder, worker⟩ := choice
      -- absorb a structural congruence in front of a reduction sequence
      have absorb : ∀ {k : ℕ} {source : Pattern},
          (source ≡ processes (step rt st ⟨event, finder, worker⟩)) →
          ReducesN k (processes (step rt st ⟨event, finder, worker⟩)) target →
          ∃ target', Nonempty (ReducesN k source target') ∧
            target' ≡ processes (run rt st (⟨event, finder, worker⟩ :: rest)) := by
        intro k source front reduction
        cases reduction with
        | zero => exact ⟨source, ⟨ReducesN.zero _⟩, StructuralCongruence.trans _ _ _ front congruent⟩
        | succ first later =>
            exact ⟨target, ⟨ReducesN.succ (Reduces.equiv front first (StructuralCongruence.refl _)) later⟩,
              congruent⟩
      cases event with
      | comm channel message body sender receiver =>
          obtain ⟨first⟩ := comm_reduces rt st finder worker enabled
          exact ⟨target, ⟨ReducesN.succ first reduction⟩, congruent⟩
      | persistentComm channel message body sender receiver =>
          exact absurd (core _ (List.mem_cons_self ..)) id
      | spawn parent components =>
          exact absorb (spawn_congruent rt st finder worker enabled) reduction
      | finish task =>
          exact absorb (finish_congruent rt st finder worker enabled) reduction
      | draw task =>
          have same := draw_processes rt st finder worker enabled
          exact absorb (same ▸ StructuralCongruence.refl _) reduction

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.ParallelExecution
