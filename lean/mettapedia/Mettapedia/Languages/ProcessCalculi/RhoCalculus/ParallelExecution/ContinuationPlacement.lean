import Mettapedia.Languages.ProcessCalculi.RhoCalculus.ParallelExecution.DuplicatorPrograms
import Mettapedia.Machines.NameSupplies.Pedigree
import Mathlib.Logic.Relation

/-!
# Placing a COMM's continuation: by the finder, or by the COMM

Every task holds a position in the spawn tree, its *pedigree* (`NameSupplies.Pedigree`): the root,
and below a position its children `0, 1, …` in the order it splits them off.  Names are drawn from
positions: a supply at position `π` gives the names `(π, 0), (π, 1), …`.

**The issue.**  When a task pushes a COMM's continuation, the continuation is the pusher's next
child.  The pusher is the party that found the match (`pushedByFinder`), and which party that is
depends on scheduling.  On the duplicator loop, the same reduction history puts the continuation at
two different positions according to the finder, and the names it draws differ
(`finder_moves_continuation`, `finder_changes_names`).

**The fix.**  A placement is *canonical* when the continuation's supply is a function of the COMM
itself, its two parties' supplies and the channel, never of the finder (`Naming.Canonical`).

* Canonical placement is exactly the placement for which the outcome of a run — the multiset of
  live tasks with their positions, and the names drawn — is a function of the run's reduction history
  (`canonical_history_outcome`, `history_outcome_canonical`).
* Events on disjoint live tasks commute (`independent_steps_commute`), for every placement.
* Together: under canonical placement, every rescheduling — changing which party finds each match and
  which worker runs each event, and reordering events on disjoint tasks — preserves both validity
  and the outcome (`rescheduled_outcome`).  Positions are a function of the program's reduction
  history up to the order of independent events, not of who found each match.

## Controls

* Every local discipline of name supplies (`NameSupplies.Discipline`) gives a canonical placement
  (`Naming.ofDiscipline`, `ofDiscipline_canonical`): spawns fork, and a COMM's continuation receives
  the join of its parties' supplies.  The finder is not a function of the supplies, so placement by
  the finder is not of this kind.
* `pushedByFinder` is not canonical (`pushedByFinder_not_canonical`); `pushedForReceiver`, which
  always makes the continuation the receiver's next child, is the spawn-tree discipline
  (`pushedForReceiver_eq`), and under it the loop's run is the same for every schedule of finders
  (`receiver_placement_loop`).
* Under either placement, rescheduling a run of two loops side by side — swapping their COMMs and
  their finders — keeps the outcome when placement is canonical and changes it when it is by the
  finder (`two_loops_rescheduled`, `two_loops_rescheduled_by_finder`).
* Either placement deepens positions by two levels per COMM on the loop, without bound
  (`pedigree_loop_depth`): canonical placement alone does not bound positions.  Bounded positions
  are the subject of `SharedPositions`.

## Persistent receives

A COMM with a persistent receive consumes the send and only reads the receive (`Event.parties`,
`Event.reads`).  Canonical placement covers its continuation too (`Naming.Canonical`), and two events
are independent when they consume disjoint tasks and each reads tasks the other does not consume
(`Independent`): two COMMs with one persistent receive are independent.  So
`canonical_history_outcome` and `rescheduled_outcome` hold with persistent receives.

* Under the rule that the continuation takes the send's supply (`takesSendSupply`), two sends to one
  persistent receive end in the same outcome in either order, with either finders
  (`persistent_rescheduled`); under placement by the finder they do not
  (`persistent_rescheduled_by_finder`).
* Placing the continuation as the receive's next child is canonical but not exact: the receive keeps
  its supply, so its continuations share a position and draw the same name
  (`persistent_receiver_placement_repeats`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.ParallelExecution

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.ReflectiveReplication

/-! ## Positions in the spawn tree -/

open Mettapedia.Machines.NameSupplies (Pedigree Discipline pedigreeDiscipline mem_erase_of_twice)

/-- Naming by the spawn tree: the components of a parallel composition are its spawner's next
children, and `place` decides where a COMM's continuation goes. -/
def pedigreeNaming (place : Pedigree → Pedigree → Pattern → Finder → Pedigree)
    (persistentPlace : Pedigree → Pedigree → Pattern → Finder → Pedigree := place) :
    Naming Pedigree (List ℕ × ℕ) where
  draw := Pedigree.draw
  component supply _ i := supply.child i
  continuation := place
  persistentContinuation := persistentPlace

/-- **Placement by the finder**: the party that found the match pushes the continuation as its next
child. -/
def pushedByFinder (sender receiver : Pedigree) (_ : Pattern) : Finder → Pedigree
  | .sender => sender.child 0
  | .receiver => receiver.child 0

/-- Placement by the receiver: the continuation is always the receiver's next child. -/
def pushedForReceiver (_ receiver : Pedigree) (_ : Pattern) (_ : Finder) : Pedigree :=
  receiver.child 0

/-- A persistent COMM's continuation takes the send's supply: the send ends at the COMM, the
persistent receive keeps its own. -/
def takesSendSupply (sender _ : Pedigree) (_ : Pattern) (_ : Finder) : Pedigree := sender

/-! ## Events, parties and outcomes -/

variable {S N W : Type}

/-- The live tasks an event takes part in. -/
def Event.parties : Event S → Multiset (Task S)
  | .comm _ _ _ sender receiver => {sender, receiver}
  | .persistentComm _ _ _ sender _ => {sender}
  | .spawn parent _ => {parent}
  | .finish task => {task}
  | .draw task => {task}

/-- The live tasks an event reads without consuming them: a persistent receive. -/
def Event.reads : Event S → Multiset (Task S)
  | .persistentComm _ _ _ _ receiver => {receiver}
  | _ => 0

/-- The shape an event's tasks must have, besides being live. -/
def Event.Shaped : Event S → Prop
  | .comm channel message body sender receiver =>
      sender.process = commOut channel message ∧ receiver.process = commIn channel body
  | .persistentComm channel message body sender receiver =>
      sender.process = commOut channel message ∧ receiver.process = persistentIn channel body
  | .spawn parent components => parent.process = bag components
  | .finish task => task.process = nil
  | .draw _ => True

theorem Event.enabled_iff (tasks : Multiset (Task S)) (event : Event S) :
    event.Enabled tasks ↔ event.Shaped ∧ event.parties + event.reads ≤ tasks := by
  cases event <;>
    simp [Event.Enabled, Event.Shaped, Event.parties, Event.reads, and_assoc,
      Multiset.singleton_add, Multiset.insert_eq_cons]

/-- The tasks an event creates. -/
def created (rt : Runtime S N) (finder : Finder) : Event S → Multiset (Task S)
  | .comm channel message body sender receiver =>
      {continuationTask rt channel message body sender receiver finder}
  | .persistentComm channel message body sender receiver =>
      {persistentContinuationTask rt channel message body sender receiver finder}
  | .spawn parent components => spawned rt parent components
  | .finish _ => 0
  | .draw task => {drawnTask rt task}

/-- The names an event draws. -/
def namesOf (rt : Runtime S N) : Event S → List N
  | .draw task => [(rt.naming.draw task.supply).1]
  | _ => []

variable [DecidableEq S] [DecidableEq W]

/-- An event replaces its parties by the tasks it creates. -/
theorem step_tasks (rt : Runtime S N) (st : State S N W) (choice : Choice S W) :
    (step rt st choice).tasks = created rt choice.finder choice.event + (st.tasks - choice.event.parties) := by
  obtain ⟨event, finder, worker⟩ := choice
  cases event <;>
    simp [step, created, Event.parties, Multiset.sub_singleton, Multiset.singleton_add]

theorem step_drawn (rt : Runtime S N) (st : State S N W) (choice : Choice S W) :
    (step rt st choice).drawn = st.drawn ++ namesOf rt choice.event := by
  obtain ⟨event, finder, worker⟩ := choice
  cases event <;> simp [step, namesOf]

/-- **The outcome of a run**: the multiset of live tasks with their positions, and the names drawn. -/
def outcome (st : State S N W) : Multiset (Task S) × Multiset N := (st.tasks, (st.drawn : Multiset N))

/-- The outcome of a step depends on the state only through its outcome. -/
theorem outcome_step (rt : Runtime S N) {st st' : State S N W} (same : outcome st = outcome st')
    (choice : Choice S W) : outcome (step rt st choice) = outcome (step rt st' choice) := by
  simp only [outcome, Prod.mk.injEq] at same ⊢
  refine ⟨by rw [step_tasks, step_tasks, same.1], ?_⟩
  rw [step_drawn, step_drawn, ← Multiset.coe_add, ← Multiset.coe_add, same.2]

/-! ## The issue: placement by the finder -/

section Issue

variable (memory : Memory) (costs : Costs) (workers : ℕ → W)

/-- The pedigree runtime that places continuations by their finder. -/
abbrev finderRuntime : Runtime Pedigree (List ℕ × ℕ) := ⟨pedigreeNaming pushedByFinder, memory, costs⟩

/-- The loop's start under placement by the finder. -/
abbrev finderStart : State Pedigree (List ℕ × ℕ) W := loopStart (finderRuntime memory costs) Pedigree.root

/-- The loop's run up to its first COMM, found by the party `finder`. -/
def firstComm (finder : Finder) : List (Choice Pedigree W) :=
  loopRun (finderRuntime memory costs) Pedigree.root (fun _ => finder) workers 0 ++
    [loopComm (finderRuntime memory costs) Pedigree.root (fun _ => finder) workers 0]

/-- **The placement issue.**  On the duplicator loop, the two finders of the first COMM give runs
with the same reduction history that leave its continuation at two different positions: below the
sender, or below the receiver. -/
theorem finder_moves_continuation :
    (firstComm memory costs workers .sender).map Choice.event =
        (firstComm memory costs workers .receiver).map Choice.event ∧
      (run (finderRuntime memory costs) (finderStart memory costs)
          (firstComm memory costs workers .sender)).tasks =
        {task (finderRuntime memory costs) loopProgram ⟨[0, 0], 0, 0⟩} ∧
      (run (finderRuntime memory costs) (finderStart memory costs)
          (firstComm memory costs workers .receiver)).tasks =
        {task (finderRuntime memory costs) loopProgram ⟨[0, 1], 0, 0⟩} := by
  refine ⟨rfl, ?_, ?_⟩ <;>
  · rw [firstComm, run_append, loop_run]
    simp only [run_cons, run_nil]
    rw [loop_comm_step]
    rfl

/-- **The names the continuation draws depend on the finder.** -/
theorem finder_changes_names :
    (run (finderRuntime memory costs) (finderStart memory costs)
        (firstComm memory costs workers .sender ++
          [⟨.draw (task (finderRuntime memory costs) loopProgram ⟨[0, 0], 0, 0⟩), .sender,
            workers 1⟩])).drawn = [([0, 0], 0)] ∧
    (run (finderRuntime memory costs) (finderStart memory costs)
        (firstComm memory costs workers .receiver ++
          [⟨.draw (task (finderRuntime memory costs) loopProgram ⟨[0, 1], 0, 0⟩), .sender,
            workers 1⟩])).drawn = [([0, 1], 0)] := by
  refine ⟨?_, ?_⟩ <;>
  · rw [run_append, firstComm, run_append, loop_run]
    simp only [run_cons, run_nil]
    rw [loop_comm_step, step_drawn]
    rfl

end Issue

/-! ## The fix: canonical placement -/

/-- **Canonical placement**: the continuation's supply is a function of the COMM itself, the
parties' supplies and the channel, never of the party that found the match. -/
def Naming.Canonical (naming : Naming S N) : Prop :=
  (∀ sender receiver channel finder finder',
    naming.continuation sender receiver channel finder =
      naming.continuation sender receiver channel finder') ∧
  ∀ sender receiver channel finder finder',
    naming.persistentContinuation sender receiver channel finder =
      naming.persistentContinuation sender receiver channel finder'

/-- **The placement of a local discipline of name supplies**: spawns fork, a COMM's continuation
receives the join of its two parties' supplies, and the continuation of a COMM with a persistent
receive takes the send's supply, the receive keeping its own. -/
def Naming.ofDiscipline (D : Discipline S N) : Naming S N where
  draw := D.draw
  component := D.piece
  continuation sender receiver _ _ := D.join sender receiver
  persistentContinuation sender _ _ _ := sender

omit [DecidableEq S] [DecidableEq W] in
/-- **Every local discipline places continuations canonically.** -/
theorem ofDiscipline_canonical (D : Discipline S N) : (Naming.ofDiscipline D).Canonical :=
  ⟨fun _ _ _ _ _ => rfl, fun _ _ _ _ _ => rfl⟩

/-- The reduction history of a run: its events, without finders and workers. -/
def history (choices : List (Choice S W)) : List (Event S) := choices.map Choice.event

omit [DecidableEq S] [DecidableEq W] in
theorem created_canonical (rt : Runtime S N) (canonical : rt.naming.Canonical)
    (finder finder' : Finder) (event : Event S) :
    created rt finder event = created rt finder' event := by
  cases event <;>
    simp [created, continuationTask, persistentContinuationTask, canonical.1 _ _ _ finder finder',
      canonical.2 _ _ _ finder finder']

/-- Under canonical placement, the outcome of a step does not depend on the finder or the worker. -/
theorem canonical_step (rt : Runtime S N) (canonical : rt.naming.Canonical)
    {st st' : State S N W} (same : outcome st = outcome st') {choice choice' : Choice S W}
    (sameEvent : choice.event = choice'.event) :
    outcome (step rt st choice) = outcome (step rt st' choice') := by
  simp only [outcome, Prod.mk.injEq] at same ⊢
  refine ⟨?_, ?_⟩
  · rw [step_tasks, step_tasks, same.1, sameEvent, created_canonical rt canonical choice.finder
      choice'.finder]
  · rw [step_drawn, step_drawn, ← Multiset.coe_add, ← Multiset.coe_add, same.2, sameEvent]

/-- **Canonical placement makes the outcome a function of the reduction history**: two runs with
the same events, whatever their finders and workers, are both valid or both not, and end in the
same live tasks at the same positions with the same names drawn. -/
theorem canonical_history_outcome (rt : Runtime S N) (canonical : rt.naming.Canonical) :
    ∀ (choices choices' : List (Choice S W)) (st st' : State S N W),
      history choices = history choices' → outcome st = outcome st' →
        (Valid rt st choices ↔ Valid rt st' choices') ∧
          outcome (run rt st choices) = outcome (run rt st' choices')
  | [], [], _, _, _, same => ⟨by simp, same⟩
  | [], _ :: _, _, _, sameHistory, _ => by simp [history] at sameHistory
  | _ :: _, [], _, _, sameHistory, _ => by simp [history] at sameHistory
  | choice :: rest, choice' :: rest', st, st', sameHistory, same => by
      simp only [history, List.map_cons, List.cons.injEq] at sameHistory
      have next := canonical_step rt canonical same sameHistory.1
      obtain ⟨validRest, outcomeRest⟩ :=
        canonical_history_outcome rt canonical rest rest' _ _ sameHistory.2 next
      refine ⟨?_, outcomeRest⟩
      have sameTasks : st.tasks = st'.tasks := congrArg Prod.fst same
      rw [valid_cons, valid_cons, validRest, sameHistory.1, sameTasks]

/-- **Conversely, a placement under which the history determines the live tasks is canonical.** -/
theorem history_outcome_canonical (rt : Runtime S N) (worker : W)
    (determines : ∀ (st : State S N W) (choices choices' : List (Choice S W)),
      history choices = history choices' → (run rt st choices).tasks = (run rt st choices').tasks) :
    rt.naming.Canonical := by
  refine ⟨fun sender receiver channel finder finder' => ?_,
    fun sender receiver channel finder finder' => ?_⟩
  · let sendingTask : Task S := ⟨commOut channel nil, sender, 0⟩
    let receivingTask : Task S := ⟨commIn channel nil, receiver, 0⟩
    let st : State S N W := ⟨{sendingTask, receivingTask}, 0, []⟩
    have same := determines st [⟨.comm channel nil nil sendingTask receivingTask, finder, worker⟩]
      [⟨.comm channel nil nil sendingTask receivingTask, finder', worker⟩] rfl
    simp only [run_cons, run_nil, step_tasks, created, Event.parties, st, tsub_self, add_zero,
      Multiset.singleton_inj] at same
    exact congrArg Task.supply same
  · let sendingTask : Task S := ⟨commOut channel nil, sender, 0⟩
    let receivingTask : Task S := ⟨persistentIn channel nil, receiver, 0⟩
    let st : State S N W := ⟨{sendingTask, receivingTask}, 0, []⟩
    have same := determines st
      [⟨.persistentComm channel nil nil sendingTask receivingTask, finder, worker⟩]
      [⟨.persistentComm channel nil nil sendingTask receivingTask, finder', worker⟩] rfl
    simp only [run_cons, run_nil, step_tasks, created, Event.parties, st] at same
    have cancelled := (add_left_inj _).mp same
    rw [Multiset.singleton_inj] at cancelled
    exact congrArg Task.supply cancelled

/-! ## Independent events commute -/

/-- Two independent events: they consume disjoint live tasks, and what each reads is live and
consumed by neither. -/
def Independent (tasks : Multiset (Task S)) (first second : Event S) : Prop :=
  first.parties + second.parties ≤ tasks ∧
    first.reads ≤ tasks - (first.parties + second.parties) ∧
    second.reads ≤ tasks - (first.parties + second.parties)

theorem Independent.symm {tasks : Multiset (Task S)} {first second : Event S}
    (independent : Independent tasks first second) : Independent tasks second first := by
  obtain ⟨consumed, firstReads, secondReads⟩ := independent
  rw [add_comm] at consumed firstReads secondReads
  exact ⟨consumed, secondReads, firstReads⟩

/-- **Events on disjoint live tasks commute**, for every placement: the two orders end in the same
live tasks and the same names drawn. -/
theorem independent_steps_commute (rt : Runtime S N) (st : State S N W) {first second : Choice S W}
    (independent : Independent st.tasks first.event second.event) :
    outcome (step rt (step rt st first) second) = outcome (step rt (step rt st second) first) := by
  have secondAfter : second.event.parties ≤ st.tasks - first.event.parties :=
    le_tsub_of_add_le_left independent.1
  have firstAfter : first.event.parties ≤ st.tasks - second.event.parties :=
    le_tsub_of_add_le_right independent.1
  simp only [outcome, Prod.mk.injEq]
  refine ⟨?_, ?_⟩
  · rw [step_tasks, step_tasks, step_tasks, step_tasks,
      add_tsub_assoc_of_le secondAfter, add_tsub_assoc_of_le firstAfter, tsub_tsub, tsub_tsub,
      add_comm second.event.parties, add_left_comm]
  · rw [step_drawn, step_drawn, step_drawn, step_drawn, ← Multiset.coe_add, ← Multiset.coe_add,
      ← Multiset.coe_add, ← Multiset.coe_add, add_right_comm]

/-- Reordering two independent events keeps a run valid. -/
theorem independent_valid (rt : Runtime S N) (st : State S N W) {first second : Choice S W}
    (independent : Independent st.tasks first.event second.event)
    (valid : Valid rt st [first, second]) : Valid rt st [second, first] := by
  obtain ⟨firstEnabled, secondEnabled, -⟩ := valid
  rw [Event.enabled_iff] at firstEnabled secondEnabled
  obtain ⟨consumed, firstReads, secondReads⟩ := independent
  have firstFree : first.event.parties ≤ st.tasks - second.event.parties :=
    le_tsub_of_add_le_right consumed
  have secondBelow : second.event.parties ≤ st.tasks := le_trans le_add_self consumed
  have secondNow : second.event.parties + second.event.reads ≤ st.tasks := by
    have reads : second.event.reads ≤ st.tasks - second.event.parties :=
      le_trans secondReads (tsub_le_tsub_left le_add_self _)
    exact (le_tsub_iff_left secondBelow).mp reads
  have firstAfter : first.event.parties + first.event.reads ≤ (step rt st second).tasks := by
    rw [step_tasks]
    refine le_trans ?_ le_add_self
    have reads : first.event.reads ≤ st.tasks - second.event.parties - first.event.parties := by
      rw [tsub_tsub, add_comm]
      exact firstReads
    exact (le_tsub_iff_left firstFree).mp reads
  exact ⟨(Event.enabled_iff _ _).mpr ⟨secondEnabled.1, secondNow⟩,
    (Event.enabled_iff _ _).mpr ⟨firstEnabled.1, firstAfter⟩, trivial⟩

/-- One rescheduling move: give every event another finder and worker, or swap two adjacent
independent events. -/
inductive Reschedules (rt : Runtime S N) (st : State S N W) :
    List (Choice S W) → List (Choice S W) → Prop
  | refind {choices choices' : List (Choice S W)} :
      history choices = history choices' → Reschedules rt st choices choices'
  | swap {before after : List (Choice S W)} {first second : Choice S W} :
      Independent (run rt st before).tasks first.event second.event →
      Reschedules rt st (before ++ first :: second :: after) (before ++ second :: first :: after)

/-- Validity depends on the state only through its live tasks. -/
theorem valid_of_outcome (rt : Runtime S N) (choices : List (Choice S W)) :
    ∀ {st st' : State S N W}, outcome st = outcome st' → Valid rt st choices → Valid rt st' choices := by
  induction choices with
  | nil => intro _ _ _ _; trivial
  | cons choice rest ih =>
      intro st st' same valid
      have tasksSame : st.tasks = st'.tasks := congrArg Prod.fst same
      exact ⟨tasksSame ▸ valid.1, ih (outcome_step rt same choice) valid.2⟩

private theorem swap_valid (rt : Runtime S N) (st : State S N W)
    {first second : Choice S W} (after : List (Choice S W))
    (independent : Independent st.tasks first.event second.event)
    (valid : Valid rt st (first :: second :: after)) : Valid rt st (second :: first :: after) := by
  obtain ⟨secondEnabled, firstEnabled, -⟩ :=
    independent_valid rt st independent ⟨valid.1, valid.2.1, trivial⟩
  exact ⟨secondEnabled, firstEnabled,
    valid_of_outcome rt after (independent_steps_commute rt st independent) valid.2.2⟩

theorem outcome_run (rt : Runtime S N) (choices : List (Choice S W)) :
    ∀ {st st' : State S N W}, outcome st = outcome st' →
      outcome (run rt st choices) = outcome (run rt st' choices) := by
  induction choices with
  | nil => intro _ _ same; exact same
  | cons choice rest ih => intro st st' same; exact ih (outcome_step rt same choice)

/-- **Rescheduling under canonical placement.**  Changing which party finds each match and which
worker runs each event, and reordering independent events, keeps runs valid and keeps their
outcome: the multiset of live tasks with their positions, and the names drawn. -/
theorem rescheduled_outcome (rt : Runtime S N) (canonical : rt.naming.Canonical)
    (st : State S N W) {choices choices' : List (Choice S W)}
    (rescheduled : Relation.EqvGen (Reschedules rt st) choices choices') :
    (Valid rt st choices ↔ Valid rt st choices') ∧
      outcome (run rt st choices) = outcome (run rt st choices') := by
  induction rescheduled with
  | rel choices choices' move =>
      cases move with
      | refind sameHistory => exact canonical_history_outcome rt canonical _ _ st st sameHistory rfl
      | @swap before after first second independent =>
          have sameOutcome : outcome (run rt st (before ++ first :: second :: after)) =
              outcome (run rt st (before ++ second :: first :: after)) := by
            rw [run_append, run_append, run_cons, run_cons, run_cons, run_cons]
            exact outcome_run rt after (independent_steps_commute rt _ independent)
          refine ⟨?_, sameOutcome⟩
          rw [valid_append, valid_append]
          refine ⟨fun ⟨front, back⟩ => ⟨front, swap_valid rt _ after independent back⟩,
            fun ⟨front, back⟩ => ⟨front, swap_valid rt _ after ?_ back⟩⟩
          exact independent.symm
  | refl => exact ⟨Iff.rfl, rfl⟩
  | symm _ _ _ ih => exact ⟨ih.1.symm, ih.2.symm⟩
  | trans _ _ _ _ _ first second => exact ⟨first.1.trans second.1, first.2.trans second.2⟩

/-! ## Controls -/

/-- **Placement by the finder is not canonical.** -/
theorem pushedByFinder_not_canonical : ¬ (pedigreeNaming pushedByFinder).Canonical := by
  intro canonical
  have := canonical.1 ⟨[0], 0, 0⟩ ⟨[1], 0, 0⟩ nil .sender .receiver
  simp [pedigreeNaming, pushedByFinder, Pedigree.child] at this

/-- **Placement by the receiver, with persistent continuations taking the send's supply, is the
spawn-tree discipline.** -/
theorem pushedForReceiver_eq :
    pedigreeNaming pushedForReceiver takesSendSupply = Naming.ofDiscipline pedigreeDiscipline := rfl

/-- **Placement by the receiver is canonical**, persistent continuations included. -/
theorem pushedForReceiver_canonical : (pedigreeNaming pushedForReceiver).Canonical :=
  ⟨fun _ _ _ _ _ => rfl, fun _ _ _ _ _ => rfl⟩

omit [DecidableEq S] in
theorem loopSupplies_canonical (rt : Runtime S N) (canonical : rt.naming.Canonical) (root : S)
    (finders finders' : ℕ → Finder) (k : ℕ) :
    loopSupplies rt root finders k = loopSupplies rt root finders' k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [loopSupplies_succ, loopContinuation, ih, canonical.1 _ _ _ (finders k) (finders' k)]

/-- **Control: under placement by the receiver the loop's run is the same for every schedule of
finders and workers.** -/
theorem receiver_placement_loop (memory : Memory) (costs : Costs) (finders finders' : ℕ → Finder)
    (workers workers' : ℕ → W) (k : ℕ) :
    let rt : Runtime Pedigree (List ℕ × ℕ) := ⟨pedigreeNaming pushedForReceiver, memory, costs⟩
    outcome (run rt (loopStart rt Pedigree.root) (loopRun rt Pedigree.root finders workers k)) =
      outcome (run rt (loopStart rt Pedigree.root) (loopRun rt Pedigree.root finders' workers' k)) := by
  intro rt
  rw [loop_run, loop_run, loopSupplies_canonical rt pushedForReceiver_canonical Pedigree.root
    finders finders' k]
  rfl

/-- A placement that puts the continuation one level below a party of equal depth. -/
def OneLevelDown (place : Pedigree → Pedigree → Pattern → Finder → Pedigree) : Prop :=
  ∀ sender receiver channel finder, sender.position.length = receiver.position.length →
    (place sender receiver channel finder).position.length = sender.position.length + 1

theorem pushedByFinder_oneLevelDown : OneLevelDown pushedByFinder := by
  intro sender receiver channel finder same
  cases finder <;> simp [pushedByFinder, Pedigree.child, same]

theorem pushedForReceiver_oneLevelDown : OneLevelDown pushedForReceiver := by
  intro sender receiver channel finder same
  simp [pushedForReceiver, Pedigree.child, same]

/-- **Control: spawn-tree positions deepen by two levels per COMM on the loop**, under either
placement — canonical or not — so they are unbounded. -/
theorem pedigree_loop_depth (place : Pedigree → Pedigree → Pattern → Finder → Pedigree)
    (down : OneLevelDown place) (rt : Runtime Pedigree (List ℕ × ℕ))
    (naming : rt.naming = pedigreeNaming place) (finders : ℕ → Finder) (k : ℕ) :
    (loopSupplies rt Pedigree.root finders k).1.position.length = 2 * k + 1 ∧
      (loopSupplies rt Pedigree.root finders k).2.position.length = 2 * k + 1 := by
  induction k with
  | zero => simp [loopSupplies, naming, pedigreeNaming, Pedigree.child, Pedigree.root]
  | succ k ih =>
      have below := down _ _ atZero (finders k) (ih.1.trans ih.2.symm)
      rw [loopSupplies_succ, loopContinuation]
      simp only [naming, pedigreeNaming, Pedigree.child, List.length_cons]
      rw [below, ih.1]
      omega

/-! ### Two loops side by side -/

section TwoLoops

variable (place : Pedigree → Pedigree → Pattern → Finder → Pedigree) (memory : Memory)
  (costs : Costs)

/-- Two duplicator loops in parallel. -/
abbrev twoLoops : Pattern := bag [loopProgram, loopProgram]

/-- The spawn-tree runtime with a given placement of continuations. -/
abbrev pedigreeRuntime : Runtime Pedigree (List ℕ × ℕ) := ⟨pedigreeNaming place, memory, costs⟩

/-- A task of the spawn-tree runtime at a position. -/
abbrev placed (process : Pattern) (position : List ℕ) : Task Pedigree :=
  task (pedigreeRuntime place memory costs) process ⟨position, 0, 0⟩

/-- The two loops start as one task at the root. -/
def twoLoopsStart : State Pedigree (List ℕ × ℕ) Unit :=
  ⟨{placed place memory costs twoLoops []}, 0, []⟩

/-- Spawn the two loops, then each loop's two processes. -/
def twoLoopsOpening : List (Choice Pedigree Unit) :=
  [⟨.spawn (placed place memory costs twoLoops []) [loopProgram, loopProgram], .sender, ()⟩,
    ⟨.spawn (placed place memory costs loopProgram [0]) [loopSender, dup], .sender, ()⟩,
    ⟨.spawn (placed place memory costs loopProgram [1]) [loopSender, dup], .sender, ()⟩]

/-- The left loop's COMM, found by `finder`. -/
def leftComm (finder : Finder) : Choice Pedigree Unit :=
  ⟨.comm atZero dup relay (placed place memory costs loopSender [0, 0])
    (placed place memory costs dup [1, 0]), finder, ()⟩

/-- The right loop's COMM, found by `finder`. -/
def rightComm (finder : Finder) : Choice Pedigree Unit :=
  ⟨.comm atZero dup relay (placed place memory costs loopSender [0, 1])
    (placed place memory costs dup [1, 1]), finder, ()⟩

/-- The left loop's continuation. -/
abbrev leftContinuation (finder : Finder) : Task Pedigree :=
  task (pedigreeRuntime place memory costs) loopProgram (place ⟨[0, 0], 0, 0⟩ ⟨[1, 0], 0, 0⟩ atZero finder)

/-- The right loop's continuation. -/
abbrev rightContinuation (finder : Finder) : Task Pedigree :=
  task (pedigreeRuntime place memory costs) loopProgram (place ⟨[0, 1], 0, 0⟩ ⟨[1, 1], 0, 0⟩ atZero finder)

/-- The opened state: both loops' processes are live. -/
abbrev twoLoopsOpened : State Pedigree (List ℕ × ℕ) Unit :=
  ⟨({placed place memory costs loopSender [0, 1], placed place memory costs dup [1, 1]} :
      Multiset (Task Pedigree)) +
    {placed place memory costs loopSender [0, 0], placed place memory costs dup [1, 0]}, 0, []⟩

theorem twoLoops_spawn_root :
    step (pedigreeRuntime place memory costs) (twoLoopsStart place memory costs)
        ⟨.spawn (placed place memory costs twoLoops []) [loopProgram, loopProgram], .sender, ()⟩ =
      ⟨{placed place memory costs loopProgram [0], placed place memory costs loopProgram [1]}, 0, []⟩ := by
  rw [step_spawn (frame := 0) _ _ _ _ rfl, spawned_pair]
  rfl

theorem twoLoops_spawn_left :
    step (pedigreeRuntime place memory costs)
        ⟨{placed place memory costs loopProgram [0], placed place memory costs loopProgram [1]}, 0, []⟩
        ⟨.spawn (placed place memory costs loopProgram [0]) [loopSender, dup], .sender, ()⟩ =
      ⟨({placed place memory costs loopSender [0, 0], placed place memory costs dup [1, 0]} :
          Multiset (Task Pedigree)) + {placed place memory costs loopProgram [1]}, 0, []⟩ := by
  rw [step_spawn (frame := {placed place memory costs loopProgram [1]}) _ _ _ _ rfl, spawned_pair]
  rfl

theorem twoLoops_spawn_right :
    step (pedigreeRuntime place memory costs)
        ⟨({placed place memory costs loopSender [0, 0], placed place memory costs dup [1, 0]} :
          Multiset (Task Pedigree)) + {placed place memory costs loopProgram [1]}, 0, []⟩
        ⟨.spawn (placed place memory costs loopProgram [1]) [loopSender, dup], .sender, ()⟩ =
      twoLoopsOpened place memory costs := by
  rw [step_spawn (frame := ({placed place memory costs loopSender [0, 0],
      placed place memory costs dup [1, 0]} : Multiset (Task Pedigree))) _ _ _ _
      (by rw [add_comm]; rfl), spawned_pair]
  rfl

theorem twoLoops_opened :
    run (pedigreeRuntime place memory costs) (twoLoopsStart place memory costs)
        (twoLoopsOpening place memory costs) = twoLoopsOpened place memory costs := by
  simp only [twoLoopsOpening, run_cons, run_nil]
  rw [twoLoops_spawn_root, twoLoops_spawn_left, twoLoops_spawn_right]

theorem twoLoops_opening_valid :
    Valid (pedigreeRuntime place memory costs) (twoLoopsStart place memory costs)
      (twoLoopsOpening place memory costs) := by
  simp only [twoLoopsOpening]
  refine ⟨⟨rfl, Multiset.mem_singleton_self _⟩, ?_⟩
  rw [twoLoops_spawn_root]
  refine ⟨⟨rfl, by simp⟩, ?_⟩
  rw [twoLoops_spawn_left]
  exact ⟨⟨rfl, by simp⟩, trivial⟩

theorem twoLoops_left_first (finder : Finder) :
    step (pedigreeRuntime place memory costs) (twoLoopsOpened place memory costs)
        (leftComm place memory costs finder) =
      ⟨leftContinuation place memory costs finder ::ₘ
          {placed place memory costs loopSender [0, 1], placed place memory costs dup [1, 1]},
        0 + Pi.single () ((pedigreeRuntime place memory costs).retained atZero dup relay), []⟩ := by
  rw [leftComm, step_comm (frame := ({placed place memory costs loopSender [0, 1],
      placed place memory costs dup [1, 1]} : Multiset (Task Pedigree))) _ _ _ _ (add_comm _ _),
    continuation_of_loop]
  rfl

theorem twoLoops_right_first (finder : Finder) :
    step (pedigreeRuntime place memory costs) (twoLoopsOpened place memory costs)
        (rightComm place memory costs finder) =
      ⟨rightContinuation place memory costs finder ::ₘ
          {placed place memory costs loopSender [0, 0], placed place memory costs dup [1, 0]},
        0 + Pi.single () ((pedigreeRuntime place memory costs).retained atZero dup relay), []⟩ := by
  rw [rightComm, step_comm (frame := ({placed place memory costs loopSender [0, 0],
      placed place memory costs dup [1, 0]} : Multiset (Task Pedigree))) _ _ _ _ rfl,
    continuation_of_loop]
  rfl

private theorem cons_eq_add_singleton {α : Type} (a : α) (rest : Multiset α) :
    a ::ₘ rest = rest + {a} := by
  rw [add_comm, Multiset.singleton_add]

/-- **The two schedules end with the two continuations**, where the placement puts them. -/
theorem twoLoops_schedules (first second : Finder) :
    (run (pedigreeRuntime place memory costs) (twoLoopsStart place memory costs)
        (twoLoopsOpening place memory costs ++
          [leftComm place memory costs first, rightComm place memory costs second])).tasks =
      {rightContinuation place memory costs second, leftContinuation place memory costs first} ∧
    (run (pedigreeRuntime place memory costs) (twoLoopsStart place memory costs)
        (twoLoopsOpening place memory costs ++
          [rightComm place memory costs first, leftComm place memory costs second])).tasks =
      {leftContinuation place memory costs second, rightContinuation place memory costs first} := by
  constructor
  · rw [run_append, twoLoops_opened, run_cons, twoLoops_left_first, run_cons, run_nil, rightComm,
      cons_eq_add_singleton (leftContinuation place memory costs first),
      step_comm (frame := {leftContinuation place memory costs first}) _ _ _ _ rfl,
      continuation_of_loop]
    rfl
  · rw [run_append, twoLoops_opened, run_cons, twoLoops_right_first, run_cons, run_nil, leftComm,
      cons_eq_add_singleton (rightContinuation place memory costs first),
      step_comm (frame := {rightContinuation place memory costs first}) _ _ _ _ rfl,
      continuation_of_loop]
    rfl

theorem twoLoops_valid (first second : Finder) :
    Valid (pedigreeRuntime place memory costs) (twoLoopsStart place memory costs)
      (twoLoopsOpening place memory costs ++
        [leftComm place memory costs first, rightComm place memory costs second]) := by
  rw [valid_append, twoLoops_opened]
  refine ⟨twoLoops_opening_valid place memory costs, ⟨rfl, rfl, le_add_left (le_refl _)⟩, ?_⟩
  rw [twoLoops_left_first]
  exact ⟨⟨rfl, rfl, Multiset.le_cons_self _ _⟩, trivial⟩

/-- The two schedules are one rescheduling apart: swap the two independent COMMs, then exchange
their finders. -/
theorem twoLoops_reschedules :
    Relation.EqvGen (Reschedules (pedigreeRuntime place memory costs) (twoLoopsStart place memory costs))
      (twoLoopsOpening place memory costs ++
        [leftComm place memory costs .sender, rightComm place memory costs .receiver])
      (twoLoopsOpening place memory costs ++
        [rightComm place memory costs .sender, leftComm place memory costs .receiver]) := by
  refine Relation.EqvGen.trans _ (twoLoopsOpening place memory costs ++
      [rightComm place memory costs .receiver, leftComm place memory costs .sender]) _
    (Relation.EqvGen.rel _ _ (Reschedules.swap (after := []) ?_)) (Relation.EqvGen.rel _ _
      (Reschedules.refind rfl))
  rw [twoLoops_opened]
  exact ⟨le_of_eq (add_comm _ _), by simp [Event.reads, leftComm, rightComm],
    by simp [Event.reads, leftComm, rightComm]⟩

/-- **Rescheduling under canonical placement**: under placement by the receiver, the two schedules
are both valid and end in the same live tasks at the same positions. -/
theorem two_loops_rescheduled :
    Valid (pedigreeRuntime pushedForReceiver memory costs) (twoLoopsStart pushedForReceiver memory costs)
        (twoLoopsOpening pushedForReceiver memory costs ++
          [rightComm pushedForReceiver memory costs .sender,
            leftComm pushedForReceiver memory costs .receiver]) ∧
      outcome (run (pedigreeRuntime pushedForReceiver memory costs)
          (twoLoopsStart pushedForReceiver memory costs)
          (twoLoopsOpening pushedForReceiver memory costs ++
            [leftComm pushedForReceiver memory costs .sender,
              rightComm pushedForReceiver memory costs .receiver])) =
        outcome (run (pedigreeRuntime pushedForReceiver memory costs)
          (twoLoopsStart pushedForReceiver memory costs)
          (twoLoopsOpening pushedForReceiver memory costs ++
            [rightComm pushedForReceiver memory costs .sender,
              leftComm pushedForReceiver memory costs .receiver])) := by
  obtain ⟨validIff, sameOutcome⟩ := rescheduled_outcome _ pushedForReceiver_canonical _
    (twoLoops_reschedules pushedForReceiver memory costs)
  exact ⟨validIff.mp (twoLoops_valid pushedForReceiver memory costs .sender .receiver), sameOutcome⟩

/-- **Rescheduling under placement by the finder changes the outcome**: the same two schedules
leave the left loop's continuation below its sender in one and below its receiver in the other. -/
theorem two_loops_rescheduled_by_finder :
    outcome (run (pedigreeRuntime pushedByFinder memory costs)
        (twoLoopsStart pushedByFinder memory costs)
        (twoLoopsOpening pushedByFinder memory costs ++
          [leftComm pushedByFinder memory costs .sender,
            rightComm pushedByFinder memory costs .receiver])) ≠
      outcome (run (pedigreeRuntime pushedByFinder memory costs)
        (twoLoopsStart pushedByFinder memory costs)
        (twoLoopsOpening pushedByFinder memory costs ++
          [rightComm pushedByFinder memory costs .sender,
            leftComm pushedByFinder memory costs .receiver])) := by
  intro same
  have tasks := congrArg Prod.fst same
  simp only [outcome] at tasks
  rw [(twoLoops_schedules pushedByFinder memory costs .sender .receiver).1,
    (twoLoops_schedules pushedByFinder memory costs .sender .receiver).2] at tasks
  have member : leftContinuation pushedByFinder memory costs .sender ∈
      ({leftContinuation pushedByFinder memory costs .receiver,
        rightContinuation pushedByFinder memory costs .sender} : Multiset (Task Pedigree)) := by
    rw [← tasks]; simp
  simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at member
  rcases member with same | same <;>
    · have := congrArg (fun t : Task Pedigree => t.supply.position) same
      simp [pushedByFinder, Pedigree.child] at this

end TwoLoops

/-! ### Two sends to one persistent receive -/

section TwoPings

variable (place persistentPlace : Pedigree → Pedigree → Pattern → Finder → Pedigree)
  (memory : Memory) (costs : Costs)

/-- Two sends `x!(0)` beside the persistent receive `for (y <= x) x!(0)`. -/
abbrev twoPings : Pattern := bag [ping, ping, pingServer]

/-- The spawn-tree runtime with given placements of ordinary and persistent continuations. -/
abbrev pingRuntime : Runtime Pedigree (List ℕ × ℕ) :=
  ⟨pedigreeNaming place persistentPlace, memory, costs⟩

/-- A task of that runtime at a position. -/
abbrev pinged (process : Pattern) (position : List ℕ) : Task Pedigree :=
  task (pingRuntime place persistentPlace memory costs) process ⟨position, 0, 0⟩

def twoPingsStart : State Pedigree (List ℕ × ℕ) Unit :=
  ⟨{pinged place persistentPlace memory costs twoPings []}, 0, []⟩

/-- The program spawns its two sends and its persistent receive. -/
def twoPingsOpening : Choice Pedigree Unit :=
  ⟨.spawn (pinged place persistentPlace memory costs twoPings []) [ping, ping, pingServer], .sender, ()⟩

/-- The send at `position` meets the persistent receive, found by `finder`. -/
def pingComm (position : List ℕ) (finder : Finder) : Choice Pedigree Unit :=
  ⟨.persistentComm atZero nil ping (pinged place persistentPlace memory costs ping position)
    (pinged place persistentPlace memory costs pingServer [2]), finder, ()⟩

/-- The continuation of the send at `position`. -/
abbrev pingContinuation (position : List ℕ) (finder : Finder) : Task Pedigree :=
  task (pingRuntime place persistentPlace memory costs) ping
    (persistentPlace ⟨position, 0, 0⟩ ⟨[2], 0, 0⟩ atZero finder)

theorem twoPings_opened :
    step (pingRuntime place persistentPlace memory costs) (twoPingsStart place persistentPlace memory costs)
        (twoPingsOpening place persistentPlace memory costs) =
      ⟨{pinged place persistentPlace memory costs ping [0], pinged place persistentPlace memory costs ping [1],
        pinged place persistentPlace memory costs pingServer [2]}, 0, []⟩ := by
  rw [twoPingsOpening, step_spawn (frame := 0) _ _ _ _ rfl]
  rfl

theorem twoPings_after_opening :
    run (pingRuntime place persistentPlace memory costs) (twoPingsStart place persistentPlace memory costs)
        [twoPingsOpening place persistentPlace memory costs] =
      ⟨{pinged place persistentPlace memory costs ping [0], pinged place persistentPlace memory costs ping [1],
        pinged place persistentPlace memory costs pingServer [2]}, 0, []⟩ := by
  rw [run_cons, run_nil, twoPings_opened]

private theorem persistent_continuation (position : List ℕ) (finder : Finder) :
    persistentContinuationTask (pingRuntime place persistentPlace memory costs) atZero nil ping
        (pinged place persistentPlace memory costs ping position)
        (pinged place persistentPlace memory costs pingServer [2]) finder =
      pingContinuation place persistentPlace memory costs position finder := by
  simp only [persistentContinuationTask, task, persistent_residual]
  rfl

/-- **The two sends meet the persistent receive in either order**: each leaves its continuation, and
the receive stays. -/
theorem twoPings_schedule (first second : List ℕ) (firstFinder secondFinder : Finder)
    (arena : Unit → ℕ) :
    (run (pingRuntime place persistentPlace memory costs)
        ⟨{pinged place persistentPlace memory costs ping first,
          pinged place persistentPlace memory costs ping second,
          pinged place persistentPlace memory costs pingServer [2]}, arena, []⟩
        [pingComm place persistentPlace memory costs first firstFinder,
          pingComm place persistentPlace memory costs second secondFinder]).tasks =
      {pingContinuation place persistentPlace memory costs second secondFinder,
        pingContinuation place persistentPlace memory costs first firstFinder,
        pinged place persistentPlace memory costs pingServer [2]} := by
  rw [run_cons, pingComm, step_persistentComm (frame := {pinged place persistentPlace memory costs ping second,
      pinged place persistentPlace memory costs pingServer [2]}) _ _ _ _ rfl, persistent_continuation,
    run_cons, run_nil, pingComm, step_persistentComm (frame :=
      {pingContinuation place persistentPlace memory costs first firstFinder,
        pinged place persistentPlace memory costs pingServer [2]}) _ _ _ _
      (Multiset.cons_swap (pingContinuation place persistentPlace memory costs first firstFinder)
        (pinged place persistentPlace memory costs ping second)
        {pinged place persistentPlace memory costs pingServer [2]}), persistent_continuation]
  rfl

theorem twoPings_valid (first second : List ℕ) (firstFinder secondFinder : Finder)
    (arena : Unit → ℕ) :
    Valid (pingRuntime place persistentPlace memory costs)
      ⟨{pinged place persistentPlace memory costs ping first,
        pinged place persistentPlace memory costs ping second,
        pinged place persistentPlace memory costs pingServer [2]}, arena, []⟩
      [pingComm place persistentPlace memory costs first firstFinder,
        pingComm place persistentPlace memory costs second secondFinder] := by
  refine ⟨⟨rfl, rfl, ?_⟩, ?_⟩
  · simp [Multiset.insert_eq_cons, Multiset.cons_le_cons_iff]
  · rw [pingComm, step_persistentComm (frame := {pinged place persistentPlace memory costs ping second,
      pinged place persistentPlace memory costs pingServer [2]}) _ _ _ _ rfl, persistent_continuation]
    exact ⟨⟨rfl, rfl, by simp [Multiset.insert_eq_cons, Multiset.cons_swap,
      Multiset.cons_le_cons_iff]⟩, trivial⟩

/-- **Two COMMs that read one persistent receive are independent**, and the two schedules are one
rescheduling apart. -/
theorem twoPings_reschedules :
    Relation.EqvGen (Reschedules (pingRuntime place persistentPlace memory costs)
        (twoPingsStart place persistentPlace memory costs))
      ([twoPingsOpening place persistentPlace memory costs] ++
        [pingComm place persistentPlace memory costs [0] .sender,
          pingComm place persistentPlace memory costs [1] .receiver])
      ([twoPingsOpening place persistentPlace memory costs] ++
        [pingComm place persistentPlace memory costs [1] .sender,
          pingComm place persistentPlace memory costs [0] .receiver]) := by
  refine Relation.EqvGen.trans _ ([twoPingsOpening place persistentPlace memory costs] ++
      [pingComm place persistentPlace memory costs [1] .receiver,
        pingComm place persistentPlace memory costs [0] .sender]) _
    (Relation.EqvGen.rel _ _ (Reschedules.swap (after := []) ?_))
    (Relation.EqvGen.rel _ _ (Reschedules.refind rfl))
  rw [twoPings_after_opening]
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [Event.parties, Event.reads, pingComm, Multiset.insert_eq_cons, Multiset.cons_le_cons_iff,
      Multiset.sub_singleton]

/-- **Rescheduling persistent COMMs under the canonical rule**: when a persistent continuation takes
the send's supply, the two schedules are both valid and end in the same live tasks at the same
positions. -/
theorem persistent_rescheduled :
    Valid (pingRuntime pushedForReceiver takesSendSupply memory costs)
        (twoPingsStart pushedForReceiver takesSendSupply memory costs)
        ([twoPingsOpening pushedForReceiver takesSendSupply memory costs] ++
          [pingComm pushedForReceiver takesSendSupply memory costs [1] .sender,
            pingComm pushedForReceiver takesSendSupply memory costs [0] .receiver]) ∧
      outcome (run (pingRuntime pushedForReceiver takesSendSupply memory costs)
          (twoPingsStart pushedForReceiver takesSendSupply memory costs)
          ([twoPingsOpening pushedForReceiver takesSendSupply memory costs] ++
            [pingComm pushedForReceiver takesSendSupply memory costs [0] .sender,
              pingComm pushedForReceiver takesSendSupply memory costs [1] .receiver])) =
        outcome (run (pingRuntime pushedForReceiver takesSendSupply memory costs)
          (twoPingsStart pushedForReceiver takesSendSupply memory costs)
          ([twoPingsOpening pushedForReceiver takesSendSupply memory costs] ++
            [pingComm pushedForReceiver takesSendSupply memory costs [1] .sender,
              pingComm pushedForReceiver takesSendSupply memory costs [0] .receiver])) := by
  obtain ⟨validIff, sameOutcome⟩ := rescheduled_outcome _
    (show (pedigreeNaming pushedForReceiver takesSendSupply).Canonical from
      ⟨fun _ _ _ _ _ => rfl, fun _ _ _ _ _ => rfl⟩) _
    (twoPings_reschedules pushedForReceiver takesSendSupply memory costs)
  refine ⟨validIff.mp ?_, sameOutcome⟩
  rw [valid_append]
  refine ⟨⟨⟨rfl, Multiset.mem_singleton_self _⟩, trivial⟩, ?_⟩
  rw [twoPings_after_opening]
  exact twoPings_valid _ _ _ _ [0] [1] .sender .receiver 0

/-- **Persistent placement by the finder changes the outcome**: the same two schedules leave the
first send's continuation below that send in one and below the persistent receive in the other. -/
theorem persistent_rescheduled_by_finder :
    outcome (run (pingRuntime pushedByFinder pushedByFinder memory costs)
        (twoPingsStart pushedByFinder pushedByFinder memory costs)
        ([twoPingsOpening pushedByFinder pushedByFinder memory costs] ++
          [pingComm pushedByFinder pushedByFinder memory costs [0] .sender,
            pingComm pushedByFinder pushedByFinder memory costs [1] .receiver])) ≠
      outcome (run (pingRuntime pushedByFinder pushedByFinder memory costs)
        (twoPingsStart pushedByFinder pushedByFinder memory costs)
        ([twoPingsOpening pushedByFinder pushedByFinder memory costs] ++
          [pingComm pushedByFinder pushedByFinder memory costs [1] .sender,
            pingComm pushedByFinder pushedByFinder memory costs [0] .receiver])) := by
  intro same
  have tasks := congrArg Prod.fst same
  simp only [outcome] at tasks
  have swapped : ({pinged pushedByFinder pushedByFinder memory costs ping [0],
      pinged pushedByFinder pushedByFinder memory costs ping [1],
      pinged pushedByFinder pushedByFinder memory costs pingServer [2]} : Multiset (Task Pedigree)) =
    {pinged pushedByFinder pushedByFinder memory costs ping [1],
      pinged pushedByFinder pushedByFinder memory costs ping [0],
      pinged pushedByFinder pushedByFinder memory costs pingServer [2]} :=
    Multiset.cons_swap _ _ _
  rw [run_append, run_append, twoPings_after_opening, twoPings_schedule, swapped,
    twoPings_schedule] at tasks
  have member : pingContinuation pushedByFinder pushedByFinder memory costs [0] .sender ∈
      ({pingContinuation pushedByFinder pushedByFinder memory costs [0] .receiver,
        pingContinuation pushedByFinder pushedByFinder memory costs [1] .sender,
        pinged pushedByFinder pushedByFinder memory costs pingServer [2]} : Multiset (Task Pedigree)) := by
    rw [← tasks]; simp
  simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at member
  rcases member with same | same | same <;>
    · have := congrArg (fun t : Task Pedigree => (t.process, t.supply.position)) same
      simp [pushedByFinder, Pedigree.child] at this

/-- **Persistent placement as the receive's child is canonical but not exact**: both continuations of
one persistent receive land at its first child, so a valid run in which the two live sends there each
draw a name draws the same name twice. -/
theorem persistent_receiver_placement_repeats :
    let rt := pingRuntime pushedForReceiver pushedForReceiver memory costs
    let shared := pinged pushedForReceiver pushedForReceiver memory costs ping [0, 2]
    let choices := [twoPingsOpening pushedForReceiver pushedForReceiver memory costs] ++
      [pingComm pushedForReceiver pushedForReceiver memory costs [0] .sender,
        pingComm pushedForReceiver pushedForReceiver memory costs [1] .receiver] ++
      [⟨.draw shared, .sender, ()⟩, ⟨.draw shared, .sender, ()⟩]
    Valid rt (twoPingsStart pushedForReceiver pushedForReceiver memory costs) choices ∧
      ¬ (run rt (twoPingsStart pushedForReceiver pushedForReceiver memory costs) choices).drawn.Nodup := by
  intro rt shared choices
  have afterComms : run rt (twoPingsStart pushedForReceiver pushedForReceiver memory costs)
      ([twoPingsOpening pushedForReceiver pushedForReceiver memory costs] ++
        [pingComm pushedForReceiver pushedForReceiver memory costs [0] .sender,
          pingComm pushedForReceiver pushedForReceiver memory costs [1] .receiver]) =
      ⟨{shared, shared, pinged pushedForReceiver pushedForReceiver memory costs pingServer [2]},
        0 + Pi.single () (rt.retained atZero nil ping) + Pi.single () (rt.retained atZero nil ping),
        []⟩ := by
    rw [run_append, twoPings_after_opening, run_cons, pingComm,
      step_persistentComm (frame := {pinged pushedForReceiver pushedForReceiver memory costs ping [1],
        pinged pushedForReceiver pushedForReceiver memory costs pingServer [2]}) _ _ _ _ rfl,
      persistent_continuation, run_cons, run_nil, pingComm,
      step_persistentComm (frame :=
        {pingContinuation pushedForReceiver pushedForReceiver memory costs [0] .sender,
          pinged pushedForReceiver pushedForReceiver memory costs pingServer [2]}) _ _ _ _
        (Multiset.cons_swap (pingContinuation pushedForReceiver pushedForReceiver memory costs [0] .sender)
          (pinged pushedForReceiver pushedForReceiver memory costs ping [1])
          {pinged pushedForReceiver pushedForReceiver memory costs pingServer [2]}),
      persistent_continuation]
    rfl
  have twice : ({shared, shared} : Multiset (Task Pedigree)) ≤
      {shared, shared, pinged pushedForReceiver pushedForReceiver memory costs pingServer [2]} := by
    simp [Multiset.insert_eq_cons]
  constructor
  · rw [valid_append, afterComms]
    refine ⟨?_, ?_, ?_, trivial⟩
    · rw [valid_append, twoPings_after_opening]
      exact ⟨⟨⟨rfl, Multiset.mem_singleton_self _⟩, trivial⟩,
        twoPings_valid _ _ _ _ [0] [1] .sender .receiver 0⟩
    · exact Multiset.mem_of_le twice (by simp)
    · exact Multiset.mem_cons_of_mem (mem_erase_of_twice (twice.trans (le_refl _)))
  · rw [run_append, afterComms]
    simp [run, step, rt, shared, pedigreeNaming, Pedigree.draw]

end TwoPings

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.ParallelExecution
