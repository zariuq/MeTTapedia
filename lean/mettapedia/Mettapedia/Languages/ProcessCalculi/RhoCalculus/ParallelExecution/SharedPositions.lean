import Mettapedia.Languages.ProcessCalculi.RhoCalculus.ParallelExecution.ContinuationPlacement
import Mettapedia.Machines.NameSupplies.SharedSupplies
import Mettapedia.Machines.NameSupplies.BalancedPieces

/-!
# Shared positions for the rho COMM

A local discipline of name supplies (`NameSupplies.Discipline`) places rho tasks canonically
(`Naming.ofDiscipline`): a spawn forks its supply among the components, and a COMM's continuation
receives the join of its two parties' supplies, both parties ending at the COMM; a COMM with a
persistent receive hands the send's supply to its continuation and leaves the receive's alone.  The
supplies of a rho run then follow a pool run of the discipline: a COMM is a join, a spawn a fork into
the discipline's pieces (`spawned_supplies`), the end of a `0` a release, a draw a draw, and a COMM
with a persistent receive no operation at all (`supplies_step`, `supplies_run`).  So the theorems of
the abstract theory hold of rho runs, for every splitter (`split_names_distinct`), balanced forks
included (`balanced_names_distinct`).

With the share discipline (`NameSupplies.shareDiscipline`, in the style of interval tree clocks):

* **Exact names** (`shared_names_distinct`, `shared_next_names_distinct`, `shared_next_name_fresh`):
  instances of `NameSupplies.shares_exact`, `next_names_distinct` and `next_name_fresh`.
* **The duplicator loop keeps its shares** (`shared_loop_supplies`, `shared_loop_bounded`): its COMM
  joins exactly the two halves its spawn forked, an instance of `NameSupplies.join_pieces`; its
  shares never exceed three nodes and its names stay exact (`shared_loop_exact`).  Spawn-tree
  positions on the same loop deepen without bound (`pedigree_loop_depth`).
* **The persistent loop keeps its shares** (`shared_persistent_supplies`, `shared_persistent_bounded`,
  `shared_persistent_exact`): every continuation takes the send's supply, so the send keeps its share
  and the persistent receive its own, after any number of COMMs.

## Exactness against bounded positions, for the COMM

`exact_positions_unbounded` is the rho form of `NameSupplies.exact_forking_unbounded`, and it holds
for **every** rho naming, placed by the finder or not: if no valid run of replicated nil draws a name
twice, then its eager run never holds more than three live tasks, yet the positions of its live tasks
exceed every bound for every measure with finitely many positions of each size.  In the lazy run
every copy of `0` is live at once and may draw (`exact_zeros_injective`), and the eager run spawns
the same copies at the same positions.  Shares are exact, so on replicated nil they grow without
bound (`shared_generator_unbounded`; the first two in `shared_generator_first_zeros`).

Naming disciplines see supplies (and the channel and finder of a COMM), not processes: any live task
may draw names.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.ParallelExecution

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.ReflectiveReplication
open Mettapedia.Machines.NameSupplies

/-! ## Rho runs move supplies by pool operations -/

variable {S N W : Type}

/-- The supplies of a state's live tasks, with the names drawn. -/
def supplies (st : State S N W) : Pool S N := ⟨st.tasks.map Task.supply, st.drawn⟩

/-- What an event does to the supplies: a COMM joins its parties' supplies, a spawn forks, the end
of a `0` releases, a draw draws.  A COMM with a persistent receive hands the send's supply to its
continuation and leaves the receive's alone, so it changes no supply. -/
def Event.operations : Event S → List (Operation S)
  | .comm _ _ _ sender receiver => [.join sender.supply receiver.supply]
  | .persistentComm .. => []
  | .spawn parent components => [.fork parent.supply components.length]
  | .finish task => [.release task.supply]
  | .draw task => [.draw task.supply]

private theorem map_sub_of_le {α β : Type} [DecidableEq α] [DecidableEq β] (f : α → β)
    {whole part : Multiset α} (below : part ≤ whole) :
    (whole - part).map f = whole.map f - part.map f := by
  have split : (whole - part).map f + part.map f = whole.map f := by
    rw [← Multiset.map_add, tsub_add_cancel_of_le below]
  exact eq_tsub_of_add_eq split

variable [DecidableEq S] [DecidableEq W]

/-- An event that moves supplies by one pool operation. -/
private theorem supplies_single (D : Discipline S N) (rt : Runtime S N) (st : State S N W)
    (choice : Choice S W) (operation : Operation S)
    (parties : choice.event.parties ≤ st.tasks)
    (consumed : choice.event.parties.map Task.supply = operation.consumed)
    (produced : (created rt choice.finder choice.event).map Task.supply = operation.produced D)
    (named : namesOf rt choice.event = operation.names D) :
    Pool.Valid D (supplies st) [operation] ∧
      supplies (step rt st choice) = (supplies st).run D [operation] := by
  refine ⟨⟨by rw [Operation.Enabled, ← consumed]; exact Multiset.map_le_map parties, trivial⟩, ?_⟩
  simp only [Pool.run_cons, Pool.run_nil, supplies, Pool.step, Pool.mk.injEq]
  refine ⟨?_, by rw [step_drawn, named]⟩
  rw [step_tasks, Multiset.map_add, produced, map_sub_of_le _ parties, consumed]

/-- **A rho event moves supplies by the pool operations** of the discipline that places the
tasks. -/
theorem supplies_step (D : Discipline S N) (rt : Runtime S N)
    (naming : rt.naming = Naming.ofDiscipline D) (st : State S N W) (choice : Choice S W)
    (enabled : choice.event.Enabled st.tasks) :
    Pool.Valid D (supplies st) choice.event.operations ∧
      supplies (step rt st choice) = (supplies st).run D choice.event.operations := by
  have present : choice.event.parties + choice.event.reads ≤ st.tasks :=
    ((Event.enabled_iff _ _).mp enabled).2
  have parties : choice.event.parties ≤ st.tasks := le_trans le_self_add present
  obtain ⟨event, finder, worker⟩ := choice
  cases event with
  | comm channel message body sender receiver =>
      exact supplies_single D rt st _ _ parties
        (by simp [Event.parties, Operation.consumed])
        (by simp [created, Operation.produced, continuationTask, naming, Naming.ofDiscipline])
        (by simp [namesOf, Operation.names])
  | persistentComm channel message body sender receiver =>
      have sent : sender ∈ st.tasks := Multiset.mem_of_le parties (by simp [Event.parties])
      refine ⟨trivial, ?_⟩
      simp only [Event.operations, Pool.run_nil, supplies, Pool.mk.injEq]
      refine ⟨?_, by simp [step]⟩
      simp only [step, persistentContinuationTask, Multiset.map_cons, naming, Naming.ofDiscipline]
      rw [← Multiset.map_cons, Multiset.cons_erase sent]
  | spawn parent components =>
      refine supplies_single D rt st _ _ parties (by simp [Event.parties, Operation.consumed]) ?_
        (by simp [namesOf, Operation.names])
      simp only [created, Operation.produced, Multiset.map_coe]
      congr 1
      apply List.ext_getElem
      · simp [spawned, Discipline.pieces]
      · intro i _ _
        simp [spawned, Discipline.pieces, naming, Naming.ofDiscipline]
  | finish task =>
      exact supplies_single D rt st _ _ parties (by simp [Event.parties, Operation.consumed]) rfl
        (by simp [namesOf, Operation.names])
  | draw task =>
      exact supplies_single D rt st _ _ parties (by simp [Event.parties, Operation.consumed])
        (by simp [created, Operation.produced, drawnTask, naming, Naming.ofDiscipline])
        (by simp [namesOf, Operation.names, naming, Naming.ofDiscipline])

/-- **A valid rho run moves supplies by a valid pool run.** -/
theorem supplies_run (D : Discipline S N) (rt : Runtime S N)
    (naming : rt.naming = Naming.ofDiscipline D) (st : State S N W) (choices : List (Choice S W))
    (valid : Valid rt st choices) :
    Pool.Valid D (supplies st) (choices.flatMap fun choice => choice.event.operations) ∧
      supplies (run rt st choices) =
        (supplies st).run D (choices.flatMap fun choice => choice.event.operations) := by
  induction choices generalizing st with
  | nil => exact ⟨trivial, rfl⟩
  | cons choice rest ih =>
      obtain ⟨enabled, later⟩ := valid
      obtain ⟨operationsValid, moved⟩ := supplies_step D rt naming st choice enabled
      obtain ⟨restValid, restMoved⟩ := ih _ later
      rw [moved] at restValid restMoved
      rw [List.flatMap_cons, Pool.valid_append, Pool.run_append]
      exact ⟨⟨operationsValid, restValid⟩, restMoved⟩

omit [DecidableEq S] [DecidableEq W] in
/-- **Spawn placement depends only on the spawner's supply, the number of components and the
index**: the supplies of the spawned tasks are the discipline's pieces. -/
theorem spawned_supplies (D : Discipline S N) (rt : Runtime S N)
    (naming : rt.naming = Naming.ofDiscipline D) (parent : Task S) (components : List Pattern) :
    (spawned rt parent components).map Task.supply = D.pieces parent.supply components.length := by
  apply List.ext_getElem
  · simp [spawned, Discipline.pieces]
  · intro i _ _
    simp [spawned, Discipline.pieces, naming, Naming.ofDiscipline]

/-! ## Shared positions -/

/-- **Shared positions**: rho tasks placed by the share discipline. -/
abbrev sharedNaming : Naming ShareSupply ShareName := Naming.ofDiscipline shareDiscipline

/-- The runtime with shared positions, under either memory discipline. -/
abbrev sharedRuntime (memory : Memory) (costs : Costs) : Runtime ShareSupply ShareName :=
  ⟨sharedNaming, memory, costs⟩

theorem sharedNaming_canonical : sharedNaming.Canonical := ofDiscipline_canonical _

variable (memory : Memory) (costs : Costs)

/-- The runtime placing rho tasks by the share discipline with a splitter's pieces. -/
abbrev splitRuntime (splitter : Splitter) (memory : Memory) (costs : Costs) :
    Runtime ShareSupply ShareName :=
  ⟨Naming.ofDiscipline (splitDiscipline splitter), memory, costs⟩

/-- **Exact names on rho runs, with any splitter**: from a state whose supplies are well shared, no
valid run draws a name twice, and the supplies stay well shared. -/
theorem split_names_distinct (splitter : Splitter) (st : State ShareSupply ShareName W)
    (shared : WellShared (supplies st)) (choices : List (Choice ShareSupply W))
    (valid : Valid (splitRuntime splitter memory costs) st choices) :
    WellShared (supplies (run (splitRuntime splitter memory costs) st choices)) ∧
      (run (splitRuntime splitter memory costs) st choices).drawn.Nodup := by
  obtain ⟨poolValid, moved⟩ := supplies_run (splitDiscipline splitter)
    (splitRuntime splitter memory costs) rfl st choices valid
  have stays := wellShared_run_with splitter _ shared _ poolValid
  rw [← moved] at stays
  exact ⟨stays, stays.fresh⟩

/-- **Exact names on rho runs**: from a state whose supplies are well shared, no valid run draws a
name twice, and the supplies stay well shared. -/
theorem shared_names_distinct (st : State ShareSupply ShareName W)
    (shared : WellShared (supplies st)) (choices : List (Choice ShareSupply W))
    (valid : Valid (sharedRuntime memory costs) st choices) :
    WellShared (supplies (run (sharedRuntime memory costs) st choices)) ∧
      (run (sharedRuntime memory costs) st choices).drawn.Nodup :=
  split_names_distinct memory costs linearSplitter st shared choices valid

/-- **Balanced forks keep rho names exact.** -/
theorem balanced_names_distinct (st : State ShareSupply ShareName W)
    (shared : WellShared (supplies st)) (choices : List (Choice ShareSupply W))
    (valid : Valid (splitRuntime balancedSplitter memory costs) st choices) :
    (run (splitRuntime balancedSplitter memory costs) st choices).drawn.Nodup :=
  (split_names_distinct memory costs balancedSplitter st shared choices valid).2

omit [DecidableEq W] in
/-- **Live tasks at distinct positions draw distinct names.** -/
theorem shared_next_names_distinct {st : State ShareSupply ShareName W}
    (shared : WellShared (supplies st)) {t u : Task ShareSupply} (pair : {t, u} ≤ st.tasks) :
    (sharedNaming.draw t.supply).1 ≠ (sharedNaming.draw u.supply).1 :=
  next_names_distinct shared (by simpa [supplies] using Multiset.map_le_map (f := Task.supply) pair)

omit [DecidableEq W] in
/-- **A live task's next name was never drawn.** -/
theorem shared_next_name_fresh {st : State ShareSupply ShareName W}
    (shared : WellShared (supplies st)) {t : Task ShareSupply} (live : t ∈ st.tasks) :
    (sharedNaming.draw t.supply).1 ∉ st.drawn :=
  next_name_fresh shared (Multiset.mem_map_of_mem _ live)

/-! ## The duplicator loop keeps its shares -/

/-- **The loop's shares come back after every COMM**: its sender holds the left half and its
receiver the right half, whichever party finds each match. -/
theorem shared_loop_supplies (finders : ℕ → Finder) (k : ℕ) :
    loopSupplies (sharedRuntime memory costs) wholeSupply finders k =
      (⟨.node .all .none, 0⟩, ⟨.node .none .all, 0⟩) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [loopSupplies_succ, loopContinuation, ih]
      rfl

/-- **Shared positions stay bounded on the loop**: every live share has at most three nodes, after
any number of COMMs. -/
theorem shared_loop_bounded (finders : ℕ → Finder) (workers : ℕ → W) (k : ℕ) :
    ∀ t ∈ (run (sharedRuntime memory costs)
      (loopStart (sharedRuntime memory costs) wholeSupply : State ShareSupply ShareName W)
      (loopRun (sharedRuntime memory costs) wholeSupply finders workers k)).tasks,
        t.supply.share.size ≤ 3 := by
  intro t live
  rw [loop_run, shared_loop_supplies] at live
  simp only [loopTasks, Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at live
  rcases live with rfl | rfl <;> simp [Share.size]

/-- **Shared positions are exact on the loop**: no valid run continuing the loop's run draws a name
twice. -/
theorem shared_loop_exact (finders : ℕ → Finder) (workers : ℕ → W) (k : ℕ)
    (more : List (Choice ShareSupply W))
    (valid : Valid (sharedRuntime memory costs)
      (run (sharedRuntime memory costs)
        (loopStart (sharedRuntime memory costs) wholeSupply : State ShareSupply ShareName W)
        (loopRun (sharedRuntime memory costs) wholeSupply finders workers k)) more) :
    (run (sharedRuntime memory costs)
      (run (sharedRuntime memory costs)
        (loopStart (sharedRuntime memory costs) wholeSupply : State ShareSupply ShareName W)
        (loopRun (sharedRuntime memory costs) wholeSupply finders workers k)) more).drawn.Nodup := by
  have start : WellShared (supplies (loopStart (sharedRuntime memory costs) wholeSupply :
      State ShareSupply ShareName W)) := wellShared_whole
  have opened := (shared_names_distinct memory costs _ start _
    (loop_valid (sharedRuntime memory costs) wholeSupply finders workers k)).1
  exact (shared_names_distinct memory costs _ opened more valid).2

/-! ## The persistent loop keeps its shares -/

/-- **The persistent loop's send keeps its share**: each continuation takes the send's supply, whichever
party finds each match. -/
theorem shared_persistent_supplies (finders : ℕ → Finder) (k : ℕ) :
    pingSupply (sharedRuntime memory costs) wholeSupply finders k = ⟨.node .all .none, 0⟩ := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pingSupply, ih]; rfl

/-- **Shared positions stay bounded on the persistent loop**, after any number of COMMs. -/
theorem shared_persistent_bounded (finders : ℕ → Finder) (workers : ℕ → W) (k : ℕ) :
    ∀ t ∈ (run (sharedRuntime memory costs)
      (persistentStart (sharedRuntime memory costs) wholeSupply : State ShareSupply ShareName W)
      (persistentRun (sharedRuntime memory costs) wholeSupply finders workers k)).tasks,
        t.supply.share.size ≤ 3 := by
  intro t live
  rw [persistent_run, shared_persistent_supplies] at live
  simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at live
  rcases live with rfl | rfl
  · simp [Share.size]
  · exact (by decide : (Share.node .none .all).size ≤ 3)

/-- **Shared positions are exact on the persistent loop**: no valid run continuing it draws a name
twice. -/
theorem shared_persistent_exact (finders : ℕ → Finder) (workers : ℕ → W) (k : ℕ)
    (more : List (Choice ShareSupply W))
    (valid : Valid (sharedRuntime memory costs)
      (run (sharedRuntime memory costs)
        (persistentStart (sharedRuntime memory costs) wholeSupply : State ShareSupply ShareName W)
        (persistentRun (sharedRuntime memory costs) wholeSupply finders workers k)) more) :
    (run (sharedRuntime memory costs)
      (run (sharedRuntime memory costs)
        (persistentStart (sharedRuntime memory costs) wholeSupply : State ShareSupply ShareName W)
        (persistentRun (sharedRuntime memory costs) wholeSupply finders workers k)) more).drawn.Nodup := by
  have start : WellShared (supplies (persistentStart (sharedRuntime memory costs) wholeSupply :
      State ShareSupply ShareName W)) := wellShared_whole
  have opened := (shared_names_distinct memory costs _ start _
    (persistent_valid (sharedRuntime memory costs) wholeSupply finders workers k)).1
  exact (shared_names_distinct memory costs _ opened more valid).2

/-! ## Exactness against bounded positions on replicated nil -/

/-- A rho naming is exact from a state when no valid run from it draws a name twice. -/
def ExactFrom (rt : Runtime S N) (st : State S N W) : Prop :=
  ∀ choices, Valid rt st choices → (run rt st choices).drawn.Nodup

/-- **Exactness separates the copies of `0`**: every exact rho naming gives the copies of `0` that
replicated nil spawns pairwise distinct positions. -/
theorem exact_zeros_injective (rt : Runtime S N) (root : S) (finders : ℕ → Finder)
    (workers : ℕ → W) (exact : ExactFrom rt (generatorStart rt root : State S N W)) :
    Function.Injective (generatorZero rt root finders) := by
  intro i j same
  by_contra distinct
  let zeroTask := task rt nil (generatorZero rt root finders i)
  let k := max i j + 1
  let lazy := run rt (generatorStart rt root : State S N W) (lazyRun rt root finders workers k)
  have twice : {zeroTask, zeroTask} ≤ lazy.tasks := by
    have indices : ({i, j} : Multiset ℕ) ≤ Multiset.range k := by
      rw [Multiset.le_iff_subset (by simp [distinct])]
      intro index member
      simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at member
      simp only [Multiset.mem_range, k]
      omega
    have mapped := Multiset.map_le_map
      (f := fun index => task rt nil (generatorZero rt root finders index)) indices
    simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton, ← same] at mapped
    simp only [lazy, lazy_run]
    exact mapped.trans (Multiset.le_add_left _ _)
  let drawTwice : List (Choice S W) :=
    [⟨.draw zeroTask, .sender, workers 0⟩, ⟨.draw zeroTask, .sender, workers 0⟩]
  have valid : Valid rt (generatorStart rt root : State S N W)
      (lazyRun rt root finders workers k ++ drawTwice) := by
    rw [valid_append]
    refine ⟨lazy_valid rt root finders workers k, ?_, ?_, trivial⟩
    · exact Multiset.mem_of_le twice (by simp)
    · show zeroTask ∈ (step rt lazy _).tasks
      simp only [step]
      exact Multiset.mem_cons_of_mem (mem_erase_of_twice twice)
  have nodup := exact _ valid
  rw [run_append] at nodup
  simp only [drawTwice, run_cons, run_nil, step] at nodup
  have startDrawn : (run rt (generatorStart rt root : State S N W)
      (lazyRun rt root finders workers k)).drawn = [] := by rw [lazy_run]
  rw [startDrawn] at nodup
  simp at nodup

/-- **Exact names and bounded positions conflict on the COMM.**  For every rho naming under which no
valid run of replicated nil draws a name twice, and every measure of positions with finitely many
positions of each size: the eager run never holds more than three live tasks, yet the positions of
its live tasks exceed every bound. -/
theorem exact_positions_unbounded (rt : Runtime S N) (root : S) (finders : ℕ → Finder)
    (workers : ℕ → W) (exact : ExactFrom rt (generatorStart rt root : State S N W))
    (size : S → ℕ) (finite : ∀ bound, {s | size s ≤ bound}.Finite) :
    (∀ k (choices : List (Choice S W)), choices <+: eagerRun rt root finders workers k →
      (run rt (generatorStart rt root) choices).tasks.card ≤ 3) ∧
    ∀ bound, ∃ k, ∃ choices : List (Choice S W), choices <+: eagerRun rt root finders workers k ∧
      ∃ t ∈ (run rt (generatorStart rt root) choices).tasks, bound < size t.supply := by
  refine ⟨fun k choices isPrefix => eager_prefix_tasks rt root finders workers k choices isPrefix,
    fun bound => ?_⟩
  obtain ⟨k, large⟩ := unbounded_of_injective size finite
    (exact_zeros_injective rt root finders workers exact) bound
  refine ⟨k + 1, _, ?_, _, eager_zero_live rt root finders workers k, large⟩
  rw [eagerRun]
  exact ⟨[generatorFinish rt root finders workers k], by simp⟩

/-! ## Shared positions on replicated nil -/

theorem shared_generator_exact :
    ExactFrom (sharedRuntime memory costs)
      (generatorStart (sharedRuntime memory costs) wholeSupply : State ShareSupply ShareName W) :=
  fun choices valid =>
    (shared_names_distinct memory costs
      (generatorStart (sharedRuntime memory costs) wholeSupply) wellShared_whole choices valid).2

theorem shared_generator_clocks (finders : ℕ → Finder) (k : ℕ) :
    (generatorSupplies (sharedRuntime memory costs) wholeSupply finders k).1.clock = 0 ∧
      (generatorSupplies (sharedRuntime memory costs) wholeSupply finders k).2.clock = 0 := by
  induction k with
  | zero => exact ⟨rfl, rfl⟩
  | succ k ih =>
      simp only [generatorSupplies_succ, generatorCodeSupply, generatorContinuation]
      generalize generatorSupplies (sharedRuntime memory costs) wholeSupply finders k = supplies at ih ⊢
      simp [Naming.ofDiscipline, shareDiscipline, ih.1, ih.2]

theorem shared_zero_clock (finders : ℕ → Finder) (k : ℕ) :
    (generatorZero (sharedRuntime memory costs) wholeSupply finders k).clock = 0 := by
  have clocks := shared_generator_clocks memory costs finders k
  simp only [generatorZero, generatorCodeSupply, generatorContinuation]
  generalize generatorSupplies (sharedRuntime memory costs) wholeSupply finders k = supplies at clocks ⊢
  simp [Naming.ofDiscipline, shareDiscipline, clocks.1, clocks.2]

/-- **Shared positions grow without bound on replicated nil**: its eager run never holds more than
three live tasks, while the shares of its live tasks exceed every size. -/
theorem shared_generator_unbounded (finders : ℕ → Finder) (workers : ℕ → W) (bound : ℕ) :
    ∃ k, ∃ choices : List (Choice ShareSupply W),
      choices <+: eagerRun (sharedRuntime memory costs) wholeSupply finders workers k ∧
      ∃ t ∈ (run (sharedRuntime memory costs)
        (generatorStart (sharedRuntime memory costs) wholeSupply : State ShareSupply ShareName W)
        choices).tasks, bound < t.supply.share.size := by
  have injective := exact_zeros_injective (sharedRuntime memory costs) wholeSupply finders workers
    (shared_generator_exact memory costs)
  have shareInjective : Function.Injective fun k =>
      (generatorZero (sharedRuntime memory costs) wholeSupply finders k).share := by
    intro i j same
    apply injective
    cases hi : generatorZero (sharedRuntime memory costs) wholeSupply finders i
    cases hj : generatorZero (sharedRuntime memory costs) wholeSupply finders j
    have ci := shared_zero_clock memory costs finders i
    have cj := shared_zero_clock memory costs finders j
    simp only [hi, hj] at same ci cj
    simp [same, ci, cj]
  obtain ⟨k, large⟩ := unbounded_of_injective Share.size Share.finite_size_le shareInjective bound
  refine ⟨k + 1, _, ?_, _, eager_zero_live (sharedRuntime memory costs) wholeSupply finders workers k,
    large⟩
  rw [eagerRun]
  exact ⟨[generatorFinish (sharedRuntime memory costs) wholeSupply finders workers k], by simp⟩

/-- **The conflict theorem applies to shared positions**: they are exact on replicated nil, so its
eager run, which never holds more than three live tasks, holds supplies of every size. -/
theorem shared_positions_unbounded (finders : ℕ → Finder) (workers : ℕ → W) :
    (∀ k (choices : List (Choice ShareSupply W)),
      choices <+: eagerRun (sharedRuntime memory costs) wholeSupply finders workers k →
        (run (sharedRuntime memory costs)
          (generatorStart (sharedRuntime memory costs) wholeSupply) choices).tasks.card ≤ 3) ∧
    ∀ bound, ∃ k, ∃ choices : List (Choice ShareSupply W),
      choices <+: eagerRun (sharedRuntime memory costs) wholeSupply finders workers k ∧
      ∃ t ∈ (run (sharedRuntime memory costs)
        (generatorStart (sharedRuntime memory costs) wholeSupply) choices).tasks,
        bound < t.supply.size :=
  exact_positions_unbounded (sharedRuntime memory costs) wholeSupply finders workers
    (shared_generator_exact memory costs) ShareSupply.size finite_supply_size_le

/-- The shares of the first two copies of `0`: five nodes, then seven. -/
theorem shared_generator_first_zeros (finders : ℕ → Finder) :
    (generatorZero (sharedRuntime memory costs) wholeSupply finders 0).share =
        .node .none (.node .none .all) ∧
      (generatorZero (sharedRuntime memory costs) wholeSupply finders 1).share =
        .node .none (.node (.node .none .all) .none) :=
  ⟨rfl, rfl⟩

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.ParallelExecution
