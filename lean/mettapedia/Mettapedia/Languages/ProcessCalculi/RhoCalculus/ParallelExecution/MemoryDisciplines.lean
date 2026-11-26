import Mettapedia.Languages.ProcessCalculi.RhoCalculus.ParallelExecution.DuplicatorPrograms
import Mettapedia.OSLF.MeTTaIL.CoreLanguageDef

/-!
# Worker arenas grow with the COMMs; task regions hold what the live tasks need

The memory a parallel run holds is what the tasks hold in their own regions plus what the workers'
arenas hold (`live`).  Each COMM allocates its working memory, its scratch and the continuation it
builds (`Runtime.work`), while the task that found the match runs.

* **Worker arenas** (`Memory.workerArena`).  The working memory stays in the worker's arena after the
  task ends.  Along every valid run the memory grows by exactly the working memory of the COMMs run
  (`arena_run`).  On the duplicator loop, whose run keeps two live tasks, it is `k` times the working
  memory of one COMM after `k` COMMs (`arena_loop`), unbounded (`arena_loop_unbounded`), and positive
  for every program-size measure of need (`loop_arena_leak`).  This is the observed growth per COMM
  at a constant number of live processes.
* **Task regions** (`Memory.taskRegion`).  The task that found the match releases its region when it
  ends, and the continuation receives only what it needs.  Along every valid run each live task
  holds exactly what it needs and the arenas stay empty (`region_run`), so the memory held is what
  the live tasks need (`region_live_eq_need`), a function of the live tasks alone, whatever the
  number of COMMs.  The duplicator loop's memory is the same after every COMM (`region_loop`) and
  never exceeds one bound along the whole run (`region_loop_bounded`).

## Controls

* Runs without COMMs do not grow worker arenas (`arena_without_comms`): the growth is the COMMs'.
* The persistent loop `x!(0) | for (y <= x) x!(0)` behaves the same way: `k` times the working memory
  under worker arenas (`arena_persistent_loop`), the same memory after every COMM under task regions
  (`region_persistent_loop`).
* Under task regions the memory follows the live data: the lazy run of replicated nil, which keeps
  every spawned `0` queued, holds one more `0` per COMM (`region_lazy_generator`), while its eager
  run is bounded (`region_eager_generator`).

The working memory of a COMM in progress lives in the finder's region until the COMM ends; it is
`Runtime.work` of that COMM, a function of the COMM's two parties.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.ParallelExecution

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.ReflectiveReplication

variable {S N W : Type} [DecidableEq S] [DecidableEq W] [Fintype W]

/-- **The memory a run holds**: the tasks' own regions and the workers' arenas. -/
def live (st : State S N W) : ℕ := (st.tasks.map Task.region).sum + ∑ w, st.arena w

/-- What the live tasks need. -/
def liveNeed (rt : Runtime S N) (st : State S N W) : ℕ :=
  (st.tasks.map fun t => rt.costs.need t.process).sum

/-- The working memory of a run's COMMs. -/
def commWork (rt : Runtime S N) : List (Choice S W) → ℕ
  | [] => 0
  | ⟨.comm channel message body _ _, _, _⟩ :: rest => rt.work channel message body + commWork rt rest
  | ⟨.persistentComm channel message body _ _, _, _⟩ :: rest =>
      rt.work channel message body + commWork rt rest
  | _ :: rest => commWork rt rest

omit [DecidableEq S] [DecidableEq W] [Fintype W] in
@[simp] theorem commWork_append (rt : Runtime S N) (first second : List (Choice S W)) :
    commWork rt (first ++ second) = commWork rt first + commWork rt second := by
  induction first with
  | nil => simp [commWork]
  | cons choice rest ih =>
      obtain ⟨event, finder, worker⟩ := choice
      cases event <;> simp [commWork, ih, Nat.add_assoc]

private theorem sum_add_single (arena : W → ℕ) (worker : W) (amount : ℕ) :
    ∑ w, (arena + Pi.single worker amount : W → ℕ) w = ∑ w, arena w + amount := by
  simp [Finset.sum_add_distrib, Finset.sum_pi_single']

omit [DecidableEq S] in
private theorem region_sum_zero {tasks : Multiset (Task S)} (zero : ∀ t ∈ tasks, t.region = 0) :
    (tasks.map Task.region).sum = 0 :=
  Multiset.sum_eq_zero fun x member => by
    obtain ⟨t, present, rfl⟩ := Multiset.mem_map.mp member
    exact zero t present

private theorem mem_of_mem_sub {tasks removed : Multiset (Task S)} {t : Task S}
    (member : t ∈ tasks - removed) : t ∈ tasks :=
  Multiset.mem_of_le (Multiset.sub_le_self _ _) member

/-! ## Worker arenas -/

/-- Every task's data is in an arena: no task holds a region of its own. -/
def ArenaOnly (st : State S N W) : Prop := ∀ t ∈ st.tasks, t.region = 0

omit [Fintype W] in
private theorem arena_only_step (rt : Runtime S N) (arena : rt.memory = .workerArena)
    (st : State S N W) (only : ArenaOnly st) (choice : Choice S W)
    (enabled : choice.event.Enabled st.tasks) : ArenaOnly (step rt st choice) := by
  have handover : ∀ process, rt.handover process = 0 := fun _ => by simp [Runtime.handover, arena]
  obtain ⟨event, finder, worker⟩ := choice
  cases event with
  | comm channel message body sender receiver =>
      intro t member
      rcases Multiset.mem_cons.mp member with rfl | rest
      · exact handover _
      · exact only t (mem_of_mem_sub rest)
  | persistentComm channel message body sender receiver =>
      intro t member
      rcases Multiset.mem_cons.mp member with rfl | rest
      · exact handover _
      · exact only t (Multiset.mem_of_mem_erase rest)
  | spawn parent components =>
      intro t member
      rcases Multiset.mem_add.mp member with child | rest
      · obtain ⟨i, _, rfl⟩ := List.mem_mapIdx.mp (Multiset.mem_coe.mp child)
        exact handover _
      · exact only t (Multiset.mem_of_mem_erase rest)
  | finish task => exact fun t member => only t (Multiset.mem_of_mem_erase member)
  | draw task =>
      intro t member
      rcases Multiset.mem_cons.mp member with rfl | rest
      · exact only task enabled
      · exact only t (Multiset.mem_of_mem_erase rest)

/-- **Worker arenas keep the working memory of every COMM.**  Along every valid run from a state
whose data is in arenas, the memory held grows by exactly the working memory of the run's COMMs. -/
theorem arena_run (rt : Runtime S N) (arena : rt.memory = .workerArena) (st : State S N W)
    (only : ArenaOnly st) (choices : List (Choice S W)) (valid : Valid rt st choices) :
    ArenaOnly (run rt st choices) ∧ live (run rt st choices) = live st + commWork rt choices := by
  induction choices generalizing st with
  | nil => exact ⟨only, by simp [commWork]⟩
  | cons choice rest ih =>
      obtain ⟨enabled, later⟩ := valid
      have nextOnly := arena_only_step rt arena st only choice enabled
      obtain ⟨finalOnly, finalLive⟩ := ih (step rt st choice) nextOnly later
      refine ⟨finalOnly, ?_⟩
      rw [run_cons, finalLive]
      have : live (step rt st choice) = live st + commWork rt [choice] := by
        simp only [live, region_sum_zero nextOnly, region_sum_zero only, zero_add]
        obtain ⟨event, finder, worker⟩ := choice
        cases event <;>
          simp [step, commWork, Runtime.retained, arena, Finset.sum_add_distrib,
            Finset.sum_pi_single']
      rw [this, show choice :: rest = [choice] ++ rest from rfl, commWork_append]
      omega

/-- **Control: runs without COMMs do not grow worker arenas.** -/
theorem arena_without_comms (rt : Runtime S N) (arena : rt.memory = .workerArena)
    (st : State S N W) (only : ArenaOnly st) (choices : List (Choice S W))
    (valid : Valid rt st choices) (noComm : commWork rt choices = 0) :
    live (run rt st choices) = live st := by
  rw [(arena_run rt arena st only choices valid).2, noComm, add_zero]

variable (rt : Runtime S N) (root : S) (finders : ℕ → Finder) (workers : ℕ → W)

omit [DecidableEq S] [DecidableEq W] [Fintype W] in
theorem commWork_loopRun (k : ℕ) :
    commWork rt (loopRun rt root finders workers k) = k * rt.work atZero dup relay := by
  induction k with
  | zero => simp [loopRun, loopOpening, commWork]
  | succ k ih =>
      simp only [loopRun, commWork_append, ih, loopComm, loopRespawn, commWork]
      ring

/-- **Worker arenas on the duplicator loop**: after `k` COMMs, with two live tasks, the arenas hold
`k` times the working memory of one COMM. -/
theorem arena_loop (arena : rt.memory = .workerArena) (k : ℕ) :
    live (run rt (loopStart rt root) (loopRun rt root finders workers k)) =
        k * rt.work atZero dup relay ∧
      (run rt (loopStart rt root) (loopRun rt root finders workers k)).tasks.card = 2 := by
  have start : ArenaOnly (loopStart rt root : State S N W) := by
    intro t member
    rw [loopStart, Multiset.mem_singleton] at member
    subst member
    simp [Runtime.handover, arena]
  refine ⟨?_, by rw [loop_run]; simp [loopTasks]⟩
  rw [(arena_run rt arena _ start _ (loop_valid rt root finders workers k)).2, commWork_loopRun]
  simp [live, loopStart, Runtime.handover, arena]

/-- **Worker arenas grow without bound on the duplicator loop** when a COMM allocates anything. -/
theorem arena_loop_unbounded (arena : rt.memory = .workerArena)
    (allocates : 0 < rt.work atZero dup relay) (bound : ℕ) :
    ∃ k, bound < live (run rt (loopStart rt root) (loopRun rt root finders workers k)) := by
  refine ⟨bound + 1, ?_⟩
  rw [(arena_loop rt root finders workers arena (bound + 1)).1]
  nlinarith

/-! ## Task regions -/

/-- Every task holds in its region exactly what it needs, and the arenas are empty. -/
structure RegionExact (rt : Runtime S N) (st : State S N W) : Prop where
  regions : ∀ t ∈ st.tasks, t.region = rt.costs.need t.process
  arenas : ∀ w, st.arena w = 0

omit [Fintype W] in
private theorem region_exact_step (region : rt.memory = .taskRegion) (st : State S N W)
    (exact : RegionExact rt st) (choice : Choice S W) (enabled : choice.event.Enabled st.tasks) :
    RegionExact rt (step rt st choice) := by
  have handover : ∀ process, rt.handover process = rt.costs.need process :=
    fun _ => by simp [Runtime.handover, region]
  have retained : ∀ channel message body, rt.retained channel message body = 0 :=
    fun _ _ _ => by simp [Runtime.retained, region]
  obtain ⟨event, finder, worker⟩ := choice
  cases event with
  | comm channel message body sender receiver =>
      refine ⟨fun t member => ?_, fun w => by simp [step, retained, exact.arenas w]⟩
      rcases Multiset.mem_cons.mp member with rfl | rest
      · exact handover _
      · exact exact.regions t (mem_of_mem_sub rest)
  | persistentComm channel message body sender receiver =>
      refine ⟨fun t member => ?_, fun w => by simp [step, retained, exact.arenas w]⟩
      rcases Multiset.mem_cons.mp member with rfl | rest
      · exact handover _
      · exact exact.regions t (Multiset.mem_of_mem_erase rest)
  | spawn parent components =>
      refine ⟨fun t member => ?_, exact.arenas⟩
      rcases Multiset.mem_add.mp member with child | rest
      · obtain ⟨i, _, rfl⟩ := List.mem_mapIdx.mp (Multiset.mem_coe.mp child)
        exact handover _
      · exact exact.regions t (Multiset.mem_of_mem_erase rest)
  | finish task =>
      exact ⟨fun t member => exact.regions t (Multiset.mem_of_mem_erase member), exact.arenas⟩
  | draw task =>
      refine ⟨fun t member => ?_, exact.arenas⟩
      rcases Multiset.mem_cons.mp member with rfl | rest
      · exact exact.regions task enabled
      · exact exact.regions t (Multiset.mem_of_mem_erase rest)

omit [Fintype W] in
/-- **Task regions hold what the live tasks need.**  Along every valid run from a state where
every task holds exactly what it needs, every task still does, and no arena holds anything. -/
theorem region_run (region : rt.memory = .taskRegion) (st : State S N W)
    (exact : RegionExact rt st) (choices : List (Choice S W)) (valid : Valid rt st choices) :
    RegionExact rt (run rt st choices) := by
  induction choices generalizing st with
  | nil => exact exact
  | cons choice rest ih =>
      exact ih _ (region_exact_step rt region st exact choice valid.1) valid.2

omit [DecidableEq S] [DecidableEq W] in
theorem live_eq_need_of_exact (st : State S N W) (exact : RegionExact rt st) :
    live st = liveNeed rt st := by
  have regions : st.tasks.map Task.region = st.tasks.map fun t => rt.costs.need t.process :=
    Multiset.map_congr rfl exact.regions
  simp [live, liveNeed, regions, exact.arenas]

/-- **Under task regions the memory held is what the live tasks need**, at every point of every
valid run: a function of the live tasks alone, whatever the number of COMMs run. -/
theorem region_live_eq_need (region : rt.memory = .taskRegion) (st : State S N W)
    (exact : RegionExact rt st) (choices : List (Choice S W)) (valid : Valid rt st choices) :
    live (run rt st choices) = liveNeed rt (run rt st choices) :=
  live_eq_need_of_exact rt _ (region_run rt region st exact choices valid)

omit [DecidableEq S] [DecidableEq W] [Fintype W] in
theorem loopStart_exact (region : rt.memory = .taskRegion) :
    RegionExact rt (loopStart rt root : State S N W) :=
  ⟨fun t member => by
    rw [loopStart, Multiset.mem_singleton] at member
    subst member
    simp [Runtime.handover, region], fun _ => rfl⟩

/-- **Task regions on the duplicator loop**: after every COMM and the spawn of its continuation,
the memory held is what the loop's two processes need. -/
theorem region_loop (region : rt.memory = .taskRegion) (k : ℕ) :
    live (run rt (loopStart rt root) (loopRun rt root finders workers k)) =
      rt.costs.need loopSender + rt.costs.need dup := by
  rw [region_live_eq_need rt region _ (loopStart_exact rt root region) _
    (loop_valid rt root finders workers k), loop_run]
  simp [liveNeed, loopTasks]

/-- **Task regions keep the duplicator loop bounded**: at every point of its run, however many
COMMs it has run, the memory held is at most what the program and its two processes need. -/
theorem region_loop_bounded (region : rt.memory = .taskRegion) (k : ℕ)
    (choices : List (Choice S W)) (isPrefix : choices <+: loopRun rt root finders workers k) :
    live (run rt (loopStart rt root) choices) ≤
      rt.costs.need loopProgram + rt.costs.need loopSender + rt.costs.need dup := by
  have valid : Valid rt (loopStart rt root : State S N W) choices := by
    obtain ⟨rest, whole⟩ := isPrefix
    have := loop_valid rt root finders workers k
    rw [← whole, valid_append] at this
    exact this.1
  rw [region_live_eq_need rt region _ (loopStart_exact rt root region) _ valid]
  induction k generalizing choices with
  | zero =>
      rcases List.prefix_cons_iff.mp isPrefix with empty | ⟨rest, rfl, restPrefix⟩
      · subst empty; simp [liveNeed, loopStart]; omega
      · rcases List.prefix_nil.mp restPrefix with rfl
        have := loop_run rt root finders workers 0
        simp only [loopRun] at this
        rw [this]; simp [liveNeed, loopTasks]
  | succ k ih =>
      rw [loopRun] at isPrefix
      rcases List.prefix_concat_iff.mp isPrefix with whole | earlier
      · rw [whole, ← loopRun, loop_run]; simp [liveNeed, loopTasks]
      rcases List.prefix_concat_iff.mp earlier with whole | earlier
      · rw [whole, run_append, loop_run, run_cons, run_nil, loop_comm_step]
        simp [liveNeed, loopMidState]; omega
      · have earlierValid : Valid rt (loopStart rt root : State S N W) choices := by
          obtain ⟨rest, whole⟩ := earlier
          have := loop_valid rt root finders workers k
          rw [← whole, valid_append] at this
          exact this.1
        exact ih choices earlier earlierValid

/-! ## The persistent loop -/

omit [DecidableEq S] [DecidableEq W] [Fintype W] in
theorem commWork_persistentRun (k : ℕ) :
    commWork rt (persistentRun rt root finders workers k) = k * rt.work atZero nil ping := by
  induction k with
  | zero => simp [persistentRun, persistentOpening, commWork]
  | succ k ih =>
      simp only [persistentRun, commWork_append, ih, persistentLoopComm, commWork]
      ring

/-- **Worker arenas on the persistent loop**: after `k` COMMs with the persistent receive, the
arenas hold `k` times the working memory of one COMM. -/
theorem arena_persistent_loop (arena : rt.memory = .workerArena) (k : ℕ) :
    live (run rt (persistentStart rt root) (persistentRun rt root finders workers k)) =
      k * rt.work atZero nil ping := by
  have start : ArenaOnly (persistentStart rt root : State S N W) := by
    intro t member
    rw [persistentStart, Multiset.mem_singleton] at member
    subst member
    simp [Runtime.handover, arena]
  rw [(arena_run rt arena _ start _ (persistent_valid rt root finders workers k)).2,
    commWork_persistentRun]
  simp [live, persistentStart, Runtime.handover, arena]

omit [DecidableEq S] [DecidableEq W] [Fintype W] in
theorem persistentStart_exact (region : rt.memory = .taskRegion) :
    RegionExact rt (persistentStart rt root : State S N W) :=
  ⟨fun t member => by
    rw [persistentStart, Multiset.mem_singleton] at member
    subst member
    simp [Runtime.handover, region], fun _ => rfl⟩

/-- **Task regions on the persistent loop**: after every COMM the memory held is what the send and
the persistent receive need. -/
theorem region_persistent_loop (region : rt.memory = .taskRegion) (k : ℕ) :
    live (run rt (persistentStart rt root) (persistentRun rt root finders workers k)) =
      rt.costs.need ping + rt.costs.need pingServer := by
  rw [region_live_eq_need rt region _ (persistentStart_exact rt root region) _
    (persistent_valid rt root finders workers k), persistent_run]
  simp [liveNeed]

/-! ## Controls on replicated nil -/

omit [DecidableEq S] [DecidableEq W] [Fintype W] in
theorem generatorStart_exact (region : rt.memory = .taskRegion) :
    RegionExact rt (generatorStart rt root : State S N W) :=
  ⟨fun t member => by
    rw [generatorStart, Multiset.mem_singleton] at member
    subst member
    simp [Runtime.handover, region], fun _ => rfl⟩

/-- **Control: task regions follow the live data.**  The lazy run of replicated nil keeps every
spawned `0` queued, and holds one more `0` per COMM. -/
theorem region_lazy_generator (region : rt.memory = .taskRegion) (k : ℕ) :
    live (run rt (generatorStart rt root) (lazyRun rt root finders workers k)) =
      rt.costs.need generatorSender + rt.costs.need dup + k * rt.costs.need nil := by
  rw [region_live_eq_need rt region _ (generatorStart_exact rt root region) _
    (lazy_valid rt root finders workers k), lazy_run]
  simp [liveNeed, generatorTasks, generatorZeros, Multiset.map_map, Function.comp_def]
  ring

/-- **Control: the eager run of replicated nil is bounded under task regions.** -/
theorem region_eager_generator (region : rt.memory = .taskRegion) (k : ℕ) :
    live (run rt (generatorStart rt root) (eagerRun rt root finders workers k)) =
      rt.costs.need generatorSender + rt.costs.need dup := by
  rw [region_live_eq_need rt region _ (generatorStart_exact rt root region) _
    (eager_valid rt root finders workers k), eager_run]
  simp [liveNeed, generatorTasks]

/-! ## A concrete measure: memory as the number of syntax nodes -/

open Mettapedia.OSLF.MeTTaIL.CoreReduction in
/-- Need measured as the number of syntax nodes of a process, with any scratch per COMM. -/
def nodeCosts (scratch : Pattern → Pattern → Pattern → ℕ) : Costs :=
  ⟨nodeCount, scratch⟩

open Mettapedia.OSLF.MeTTaIL.CoreReduction in
theorem nodeCount_pos (process : Pattern) : 0 < nodeCount process := by
  cases process <;> simp [nodeCount]

open Mettapedia.OSLF.MeTTaIL.CoreReduction in
/-- **The memory issue, concretely.**  With need measured in syntax nodes, under worker arenas
the duplicator loop keeps two live tasks while its memory grows by the same positive amount, the
continuation's node count plus the COMM's scratch, with every COMM. -/
theorem loop_arena_leak (naming : Naming S N) (scratch : Pattern → Pattern → Pattern → ℕ) :
    let rt : Runtime S N := ⟨naming, .workerArena, nodeCosts scratch⟩
    ∃ perComm, 0 < perComm ∧ ∀ k,
      live (run rt (loopStart rt root) (loopRun rt root finders workers k)) = k * perComm ∧
        (run rt (loopStart rt root) (loopRun rt root finders workers k)).tasks.card = 2 := by
  intro rt
  refine ⟨rt.work atZero dup relay, ?_, arena_loop rt root finders workers rfl⟩
  simp only [Runtime.work, rt, nodeCosts]
  have := nodeCount_pos (commRes relay dup)
  omega

/-- The two disciplines on one schedule of the loop, with need in syntax nodes and one worker:
under worker arenas the memory after `k` COMMs exceeds every bound, under task regions it is the
same after every COMM. -/
theorem loop_disciplines_compared (naming : Naming S N)
    (scratch : Pattern → Pattern → Pattern → ℕ) (bound : ℕ) :
    let arenas : Runtime S N := ⟨naming, .workerArena, nodeCosts scratch⟩
    let regions : Runtime S N := ⟨naming, .taskRegion, nodeCosts scratch⟩
    (∃ k, bound < live (run arenas (loopStart arenas root : State S N Unit)
      (loopRun arenas root finders (fun _ => ()) k))) ∧
    ∀ k, live (run regions (loopStart regions root : State S N Unit)
      (loopRun regions root finders (fun _ => ()) k)) =
        (nodeCosts scratch).need loopSender + (nodeCosts scratch).need dup := by
  intro arenas regions
  obtain ⟨perComm, positive, grows⟩ := loop_arena_leak (W := Unit) root finders (fun _ => ())
    naming scratch
  refine ⟨⟨bound + 1, ?_⟩, fun k => region_loop regions root finders (fun _ => ()) rfl k⟩
  rw [(grows (bound + 1)).1]
  nlinarith

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.ParallelExecution
