import Mettapedia.Languages.ProcessCalculi.RhoCalculus.ParallelExecution.Tasks
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.ReflectiveReplication

/-!
# Two rho programs that run forever with few live processes

Both are built from the duplicator `D(x) = for (y ← x) (x!(*y) | *y)` of `ReflectiveReplication`,
on the closed channel `x = @0`.

* **The duplicator loop** `x!(D(x)) | D(x)`.  The duplicator receives its own code, resends it and
  runs it, so the continuation of each COMM is the program again (`loop_residual`).  Its parallel
  run is a chain of COMMs of every length (`loop_run`, `loop_valid`) that never holds more than two
  live tasks (`loop_prefix_tasks`).
* **The persistent loop** `x!(0) | for (y <= x) x!(0)`.  Each COMM with the persistent receive
  recreates the send and keeps the receive (`persistent_residual`), so its run keeps the same two
  tasks forever (`persistent_run`, `persistent_valid`).
* **Replicated nil** `!0 = x!(D(x) | 0) | D(x)` (`ReflectiveReplication.replicate` at `0`).  The
  continuation of each COMM is the replication together with a copy of `0` (`generator_residual`).
  Ending each copy at once keeps at most three tasks live (`eager_prefix_tasks`); leaving the
  copies queued keeps every one of them live (`lazy_run`).

The runs are generic in the runtime (naming and memory disciplines, costs), in the finder of each
COMM and in the worker that runs it.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.ParallelExecution

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.ReflectiveReplication

/-! ## The programs -/

/-- The continuation of the duplicator: `x!(*y) | *y` on `x = @0`. -/
abbrev relay : Pattern := duplicatorBody atZero

/-- The duplicator `D(x)` on `x = @0`. -/
abbrev dup : Pattern := duplicator atZero

/-- `x!(D(x))`. -/
abbrev loopSender : Pattern := commOut atZero dup

/-- **The duplicator loop** `x!(D(x)) | D(x)`. -/
abbrev loopProgram : Pattern := bag [loopSender, dup]

/-- The code replicated nil sends: `D(x) | 0`. -/
abbrev generatorCode : Pattern := bag [dup, nil]

/-- `x!(D(x) | 0)`. -/
abbrev generatorSender : Pattern := commOut atZero generatorCode

/-- **Replicated nil** `!0 = x!(D(x) | 0) | D(x)`. -/
abbrev generatorProgram : Pattern := bag [generatorSender, dup]

theorem dup_eq : dup = commIn atZero relay := rfl

theorem generatorProgram_eq : generatorProgram = replicate atZero nil := rfl

private theorem normalize_dup : semanticNormalizeProc dup = dup := by
  simp [duplicator, duplicatorBody, atZero, semanticNormalizeName, semanticNormalizeProc,
    semanticNormalizeProcList]

theorem substitute_channel (replacement : Pattern) :
    semanticSubstName 0 replacement atZero = atZero := by
  rw [substName_eq, if_neg atZero_channelInert]
  simp [atZero, semanticNormalizeName, semanticNormalizeProc]

/-- **The loop's COMM recreates the loop.** -/
theorem loop_residual : commRes relay dup = loopProgram := by
  rw [commRes, commSubst_duplicatorBody, normalize_dup, substitute_channel]
  rfl

/-- **Replicated nil's COMM recreates the replication beside a copy of `0`.** -/
theorem generator_residual : commRes relay generatorCode = bag [generatorSender, generatorCode] := by
  have normalized : semanticNormalizeProc generatorCode = generatorCode := by
    simp [semanticNormalizeProc, semanticNormalizeProcList, normalize_dup]
  rw [commRes, commSubst_duplicatorBody, normalized, substitute_channel]
  rfl

/-- In the calculus, the loop reduces to itself. -/
theorem loop_reduces : Nonempty (Reduces loopProgram (bag [loopProgram])) := by
  have step := comm_at_head atZero dup relay []
  rw [loop_residual] at step
  exact ⟨step⟩

/-! ## Tasks of a run -/

variable {S N W : Type} [DecidableEq S] [DecidableEq W]

/-- A task holding `process` at `supply`, with the region its memory discipline hands it. -/
def task (rt : Runtime S N) (process : Pattern) (supply : S) : Task S :=
  ⟨process, supply, rt.handover process⟩

omit [DecidableEq S] in
@[simp] theorem task_process (rt : Runtime S N) (process : Pattern) (supply : S) :
    (task rt process supply).process = process := rfl

omit [DecidableEq S] in
@[simp] theorem task_supply (rt : Runtime S N) (process : Pattern) (supply : S) :
    (task rt process supply).supply = supply := rfl

omit [DecidableEq S] in
@[simp] theorem task_region (rt : Runtime S N) (process : Pattern) (supply : S) :
    (task rt process supply).region = rt.handover process := rfl

theorem coe_pair {α : Type} (first second : α) :
    (([first, second] : List α) : Multiset α) = {first, second} := rfl

omit [DecidableEq S] in
theorem spawned_pair (rt : Runtime S N) (parent : Task S) (first second : Pattern) :
    (spawned rt parent [first, second] : Multiset (Task S)) =
      {task rt first (rt.naming.component parent.supply 2 0),
        task rt second (rt.naming.component parent.supply 2 1)} := rfl

omit [DecidableEq S] in
theorem continuation_of_loop (rt : Runtime S N) (sender receiver : Task S) (finder : Finder) :
    continuationTask rt atZero dup relay sender receiver finder =
      task rt loopProgram (rt.naming.continuation sender.supply receiver.supply atZero finder) := by
  simp only [continuationTask, task, loop_residual]

omit [DecidableEq S] in
theorem continuation_of_generator (rt : Runtime S N) (sender receiver : Task S)
    (finder : Finder) :
    continuationTask rt atZero generatorCode relay sender receiver finder =
      task rt (bag [generatorSender, generatorCode])
        (rt.naming.continuation sender.supply receiver.supply atZero finder) := by
  simp only [continuationTask, task, generator_residual]

/-! ## The loop's run -/

/-- The supplies of the loop's sender and receiver after `k` COMMs. -/
def loopSupplies (rt : Runtime S N) (root : S) (finders : ℕ → Finder) : ℕ → S × S
  | 0 => (rt.naming.component root 2 0, rt.naming.component root 2 1)
  | k + 1 =>
      let continuation := rt.naming.continuation (loopSupplies rt root finders k).1
        (loopSupplies rt root finders k).2 atZero (finders k)
      (rt.naming.component continuation 2 0, rt.naming.component continuation 2 1)

/-- The supply of the continuation of the loop's COMM number `k`. -/
def loopContinuation (rt : Runtime S N) (root : S) (finders : ℕ → Finder) (k : ℕ) : S :=
  rt.naming.continuation (loopSupplies rt root finders k).1 (loopSupplies rt root finders k).2
    atZero (finders k)

omit [DecidableEq S] in
theorem loopSupplies_succ (rt : Runtime S N) (root : S) (finders : ℕ → Finder) (k : ℕ) :
    loopSupplies rt root finders (k + 1) =
      (rt.naming.component (loopContinuation rt root finders k) 2 0,
        rt.naming.component (loopContinuation rt root finders k) 2 1) := rfl

/-- The loop's two live tasks between COMMs. -/
def loopTasks (rt : Runtime S N) (supplies : S × S) : Multiset (Task S) :=
  {task rt loopSender supplies.1, task rt dup supplies.2}

/-- The run starts with the program as one task at `root`. -/
def loopStart (rt : Runtime S N) (root : S) : State S N W :=
  ⟨{task rt loopProgram root}, 0, []⟩

/-- The program spawns its two components. -/
def loopOpening (rt : Runtime S N) (root : S) (worker : W) : Choice S W :=
  ⟨.spawn (task rt loopProgram root) [loopSender, dup], .sender, worker⟩

/-- COMM number `k`. -/
def loopComm (rt : Runtime S N) (root : S) (finders : ℕ → Finder) (workers : ℕ → W) (k : ℕ) :
    Choice S W :=
  ⟨.comm atZero dup relay (task rt loopSender (loopSupplies rt root finders k).1)
      (task rt dup (loopSupplies rt root finders k).2), finders k, workers k⟩

/-- The spawn of the continuation of COMM number `k`. -/
def loopRespawn (rt : Runtime S N) (root : S) (finders : ℕ → Finder) (workers : ℕ → W) (k : ℕ) :
    Choice S W :=
  ⟨.spawn (task rt loopProgram (loopContinuation rt root finders k)) [loopSender, dup],
    finders k, workers k⟩

/-- The loop's run through `k` COMMs. -/
def loopRun (rt : Runtime S N) (root : S) (finders : ℕ → Finder) (workers : ℕ → W) :
    ℕ → List (Choice S W)
  | 0 => [loopOpening rt root (workers 0)]
  | k + 1 => loopRun rt root finders workers k ++ [loopComm rt root finders workers k] ++
      [loopRespawn rt root finders workers k]

/-- What the loop's COMMs leave in the workers' arenas. -/
def loopArena (rt : Runtime S N) (workers : ℕ → W) (k : ℕ) : W → ℕ :=
  ∑ i ∈ Finset.range k, Pi.single (workers i) (rt.retained atZero dup relay)

variable (rt : Runtime S N) (root : S) (finders : ℕ → Finder) (workers : ℕ → W)

/-- The state after the loop's COMM number `k`: the continuation alone. -/
def loopMidState (k : ℕ) : State S N W :=
  ⟨{task rt loopProgram (loopContinuation rt root finders k)}, loopArena rt workers (k + 1), []⟩

theorem loop_comm_step (k : ℕ) :
    step rt (⟨loopTasks rt (loopSupplies rt root finders k), loopArena rt workers k, []⟩ :
        State S N W) (loopComm rt root finders workers k) =
      loopMidState rt root finders workers k := by
  rw [loopComm, step_comm (frame := 0) _ _ _ _ (by simp [loopTasks]), continuation_of_loop]
  simp [loopMidState, loopArena, Finset.sum_range_succ, loopContinuation]

theorem loop_respawn_step (k : ℕ) :
    step rt (loopMidState rt root finders workers k) (loopRespawn rt root finders workers k) =
      ⟨loopTasks rt (loopSupplies rt root finders (k + 1)), loopArena rt workers (k + 1), []⟩ := by
  rw [loopRespawn, loopMidState, step_spawn (frame := 0) _ _ _ _ (by simp), spawned_pair,
    loopSupplies_succ]
  simp [loopTasks]

/-- **The loop's run**: after `k` COMMs the two live tasks are back, at the supplies the naming
discipline gives them, and the arenas hold what the COMMs left. -/
theorem loop_run (k : ℕ) :
    run rt (loopStart rt root) (loopRun rt root finders workers k) =
      ⟨loopTasks rt (loopSupplies rt root finders k), loopArena rt workers k, []⟩ := by
  induction k with
  | zero =>
      simp only [loopRun, run_cons, run_nil, loopOpening, loopStart]
      rw [step_spawn (frame := 0) _ _ _ _ (by simp), spawned_pair]
      simp [loopTasks, loopSupplies, loopArena]
  | succ k ih =>
      rw [loopRun, run_append, run_append, ih]
      simp only [run_cons, run_nil]
      rw [loop_comm_step, loop_respawn_step]

omit [DecidableEq S] [DecidableEq W] in
theorem loop_comm_enabled (k : ℕ) :
    (loopComm rt root finders workers k).event.Enabled
      (loopTasks rt (loopSupplies rt root finders k)) :=
  ⟨rfl, rfl, le_refl _⟩

/-- **The loop's run is valid**: every event can happen when the scheduler chooses it. -/
theorem loop_valid (k : ℕ) :
    Valid rt (loopStart rt root : State S N W) (loopRun rt root finders workers k) := by
  induction k with
  | zero => exact ⟨⟨rfl, Multiset.mem_singleton_self _⟩, trivial⟩
  | succ k ih =>
      rw [loopRun, valid_append, valid_append, run_append, loop_run]
      refine ⟨⟨ih, loop_comm_enabled rt root finders workers k, trivial⟩, ?_⟩
      rw [run_cons, run_nil, loop_comm_step]
      exact ⟨⟨rfl, Multiset.mem_singleton_self _⟩, trivial⟩

omit [DecidableEq S] [DecidableEq W] in
theorem commCount_loopRun (k : ℕ) : commCount (loopRun rt root finders workers k) = k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [loopRun, ih, loopComm, loopRespawn, commCount]

include finders workers in
/-- **The loop's parallel run is a rho reduction sequence of one reduction per COMM**: for every
schedule of finders and workers, after `k` COMMs the program has reduced in `k` steps to the bag of
the loop's two processes. -/
theorem loop_realizes (k : ℕ) :
    ∃ target, Nonempty (ReducesN k (processes (loopStart rt root : State S N W)) target) ∧
      target ≡ bag [loopSender, dup] := by
  have core : ∀ choice ∈ loopRun rt root finders workers k, choice.event.IsCore := by
    induction k with
    | zero => simp [loopRun, loopOpening, Event.IsCore]
    | succ k ih =>
        simp only [loopRun, List.mem_append, List.mem_singleton]
        rintro choice ((earlier | rfl) | rfl)
        · exact ih choice earlier
        · exact trivial
        · exact trivial
  obtain ⟨target, reduction, congruent⟩ := run_realizes rt (loopStart rt root : State S N W)
    (loopRun rt root finders workers k) (loop_valid rt root finders workers k) core
  rw [commCount_loopRun] at reduction
  refine ⟨target, reduction, StructuralCongruence.trans _ _ _ congruent ?_⟩
  rw [loop_run]
  apply bag_perm
  exact Multiset.coe_eq_coe.mp (by rw [Multiset.coe_toList]; simp [loopTasks]; rfl)

/-- **Every state of the loop's run holds at most two live tasks**: two between COMMs, one, the
continuation, right after a COMM. -/
theorem loop_prefix_tasks (k : ℕ) (choices : List (Choice S W))
    (isPrefix : choices <+: loopRun rt root finders workers k) :
    (run rt (loopStart rt root) choices).tasks.card ≤ 2 := by
  induction k generalizing choices with
  | zero =>
      rcases List.prefix_cons_iff.mp isPrefix with empty | ⟨rest, rfl, restPrefix⟩
      · subst empty; simp [loopStart]
      · rcases List.prefix_nil.mp restPrefix with rfl
        have := loop_run rt root finders workers 0
        simp only [loopRun] at this
        rw [this]; simp [loopTasks]
  | succ k ih =>
      rw [loopRun] at isPrefix
      rcases List.prefix_concat_iff.mp isPrefix with whole | earlier
      · rw [whole, ← loopRun, loop_run]; simp [loopTasks]
      · rcases List.prefix_concat_iff.mp earlier with whole | earlier
        · rw [whole, run_append, loop_run, run_cons, run_nil, loop_comm_step]
          simp [loopMidState]
        · exact ih choices earlier

/-! ## The persistent loop -/

/-- `x!(0)`. -/
abbrev ping : Pattern := commOut atZero nil

/-- The persistent receive `for (y <= x) x!(0)`. -/
abbrev pingServer : Pattern := persistentIn atZero ping

/-- **The persistent loop** `x!(0) | for (y <= x) x!(0)`. -/
abbrev persistentLoop : Pattern := bag [ping, pingServer]

/-- **The persistent loop's COMM recreates the send.** -/
theorem persistent_residual : commRes ping nil = ping := by
  show semanticCommSubst (.apply "POutput" [atZero, nil]) nil = .apply "POutput" [atZero, nil]
  simp only [semanticCommSubst, semanticSubstProc, substitute_channel]
  rfl

/-- The send's supply after `k` COMMs. -/
def pingSupply (rt : Runtime S N) (root : S) (finders : ℕ → Finder) : ℕ → S
  | 0 => rt.naming.component root 2 0
  | k + 1 => rt.naming.persistentContinuation (pingSupply rt root finders k)
      (rt.naming.component root 2 1) atZero (finders k)

/-- The run starts with the program as one task at `root`. -/
def persistentStart (rt : Runtime S N) (root : S) : State S N W :=
  ⟨{task rt persistentLoop root}, 0, []⟩

/-- The program spawns the send and the persistent receive. -/
def persistentOpening (rt : Runtime S N) (root : S) (worker : W) : Choice S W :=
  ⟨.spawn (task rt persistentLoop root) [ping, pingServer], .sender, worker⟩

/-- COMM number `k`, with the persistent receive. -/
def persistentLoopComm (rt : Runtime S N) (root : S) (finders : ℕ → Finder) (workers : ℕ → W)
    (k : ℕ) : Choice S W :=
  ⟨.persistentComm atZero nil ping (task rt ping (pingSupply rt root finders k))
      (task rt pingServer (rt.naming.component root 2 1)), finders k, workers k⟩

/-- The persistent loop's run through `k` COMMs. -/
def persistentRun (rt : Runtime S N) (root : S) (finders : ℕ → Finder) (workers : ℕ → W) :
    ℕ → List (Choice S W)
  | 0 => [persistentOpening rt root (workers 0)]
  | k + 1 => persistentRun rt root finders workers k ++ [persistentLoopComm rt root finders workers k]

/-- What the persistent loop's COMMs leave in the workers' arenas. -/
def persistentArena (rt : Runtime S N) (workers : ℕ → W) (k : ℕ) : W → ℕ :=
  ∑ i ∈ Finset.range k, Pi.single (workers i) (rt.retained atZero nil ping)

/-- **The persistent loop's run**: after `k` COMMs the send, at the supply placement gives it, and
the persistent receive, unchanged, are live. -/
theorem persistent_run (rt : Runtime S N) (root : S) (finders : ℕ → Finder) (workers : ℕ → W)
    (k : ℕ) :
    run rt (persistentStart rt root) (persistentRun rt root finders workers k) =
      ⟨{task rt ping (pingSupply rt root finders k), task rt pingServer (rt.naming.component root 2 1)},
        persistentArena rt workers k, []⟩ := by
  induction k with
  | zero =>
      simp only [persistentRun, run_cons, run_nil, persistentOpening, persistentStart]
      rw [step_spawn (frame := 0) _ _ _ _ (by simp), spawned_pair]
      simp [pingSupply, persistentArena]
  | succ k ih =>
      rw [persistentRun, run_append, ih, run_cons, run_nil, persistentLoopComm,
        step_persistentComm (frame := {task rt pingServer (rt.naming.component root 2 1)}) _ _ _ _ rfl]
      simp [persistentContinuationTask, task, persistent_residual, pingSupply, persistentArena,
        Finset.sum_range_succ]

theorem persistent_valid (rt : Runtime S N) (root : S) (finders : ℕ → Finder) (workers : ℕ → W)
    (k : ℕ) :
    Valid rt (persistentStart rt root : State S N W) (persistentRun rt root finders workers k) := by
  induction k with
  | zero => exact ⟨⟨rfl, Multiset.mem_singleton_self _⟩, trivial⟩
  | succ k ih =>
      rw [persistentRun, valid_append, persistent_run]
      exact ⟨ih, ⟨rfl, rfl, le_refl _⟩, trivial⟩

/-! ## Replicated nil's runs -/

/-- The supplies of replicated nil's sender and receiver after `k` COMMs. -/
def generatorSupplies (rt : Runtime S N) (root : S) (finders : ℕ → Finder) : ℕ → S × S
  | 0 => (rt.naming.component root 2 0, rt.naming.component root 2 1)
  | k + 1 =>
      let continuation := rt.naming.continuation (generatorSupplies rt root finders k).1
        (generatorSupplies rt root finders k).2 atZero (finders k)
      (rt.naming.component continuation 2 0,
        rt.naming.component (rt.naming.component continuation 2 1) 2 0)

/-- The supply of the continuation of COMM number `k`. -/
def generatorContinuation (k : ℕ) : S :=
  rt.naming.continuation (generatorSupplies rt root finders k).1
    (generatorSupplies rt root finders k).2 atZero (finders k)

/-- The supply of the copy of the code `D(x) | 0` spawned after COMM number `k`. -/
def generatorCodeSupply (k : ℕ) : S :=
  rt.naming.component (generatorContinuation rt root finders k) 2 1

/-- **The supply of the copy of `0` spawned after COMM number `k`.** -/
def generatorZero (k : ℕ) : S :=
  rt.naming.component (generatorCodeSupply rt root finders k) 2 1

omit [DecidableEq S] in
theorem generatorSupplies_succ (k : ℕ) :
    generatorSupplies rt root finders (k + 1) =
      (rt.naming.component (generatorContinuation rt root finders k) 2 0,
        rt.naming.component (generatorCodeSupply rt root finders k) 2 0) := rfl

/-- Replicated nil's two persistent tasks. -/
def generatorTasks (supplies : S × S) : Multiset (Task S) :=
  {task rt generatorSender supplies.1, task rt dup supplies.2}

/-- The copies of `0` spawned by the first `k` COMMs. -/
def generatorZeros (k : ℕ) : Multiset (Task S) :=
  (Multiset.range k).map fun i => task rt nil (generatorZero rt root finders i)

/-- The run starts with the program as one task at `root`. -/
def generatorStart : State S N W := ⟨{task rt generatorProgram root}, 0, []⟩

/-- The program spawns its two components. -/
def generatorOpening (worker : W) : Choice S W :=
  ⟨.spawn (task rt generatorProgram root) [generatorSender, dup], .sender, worker⟩

/-- COMM number `k`. -/
def generatorComm (k : ℕ) : Choice S W :=
  ⟨.comm atZero generatorCode relay (task rt generatorSender (generatorSupplies rt root finders k).1)
      (task rt dup (generatorSupplies rt root finders k).2), finders k, workers k⟩

/-- The continuation spawns the replication's sender and the code. -/
def generatorRespawn (k : ℕ) : Choice S W :=
  ⟨.spawn (task rt (bag [generatorSender, generatorCode]) (generatorContinuation rt root finders k))
      [generatorSender, generatorCode], finders k, workers k⟩

/-- The code spawns the duplicator and a copy of `0`. -/
def generatorUnpack (k : ℕ) : Choice S W :=
  ⟨.spawn (task rt generatorCode (generatorCodeSupply rt root finders k)) [dup, nil],
    finders k, workers k⟩

/-- The copy of `0` ends. -/
def generatorFinish (k : ℕ) : Choice S W :=
  ⟨.finish (task rt nil (generatorZero rt root finders k)), finders k, workers k⟩

/-- The run through `k` COMMs that leaves every copy of `0` queued. -/
def lazyRun : ℕ → List (Choice S W)
  | 0 => [generatorOpening rt root (workers 0)]
  | k + 1 => lazyRun k ++ [generatorComm rt root finders workers k] ++
      [generatorRespawn rt root finders workers k] ++ [generatorUnpack rt root finders workers k]

/-- The run through `k` COMMs that ends each copy of `0` as soon as it is spawned. -/
def eagerRun : ℕ → List (Choice S W)
  | 0 => [generatorOpening rt root (workers 0)]
  | k + 1 => eagerRun k ++ [generatorComm rt root finders workers k] ++
      [generatorRespawn rt root finders workers k] ++ [generatorUnpack rt root finders workers k] ++
      [generatorFinish rt root finders workers k]

/-- What replicated nil's COMMs leave in the workers' arenas. -/
def generatorArena (k : ℕ) : W → ℕ :=
  ∑ i ∈ Finset.range k, Pi.single (workers i) (rt.retained atZero generatorCode relay)

/-- The three phases of iteration `k`, above a frame of further tasks. -/
def generatorAfterComm (frame : Multiset (Task S)) (k : ℕ) : State S N W :=
  ⟨task rt (bag [generatorSender, generatorCode]) (generatorContinuation rt root finders k) ::ₘ frame,
    generatorArena rt workers (k + 1), []⟩

def generatorAfterRespawn (frame : Multiset (Task S)) (k : ℕ) : State S N W :=
  ⟨task rt generatorSender (rt.naming.component (generatorContinuation rt root finders k) 2 0) ::ₘ
      task rt generatorCode (generatorCodeSupply rt root finders k) ::ₘ frame,
    generatorArena rt workers (k + 1), []⟩

def generatorAfterUnpack (frame : Multiset (Task S)) (k : ℕ) : State S N W :=
  ⟨task rt nil (generatorZero rt root finders k) ::ₘ
      generatorTasks rt (generatorSupplies rt root finders (k + 1)) + frame,
    generatorArena rt workers (k + 1), []⟩

theorem generator_comm_step (frame : Multiset (Task S)) (k : ℕ) :
    step rt (⟨generatorTasks rt (generatorSupplies rt root finders k) + frame,
        generatorArena rt workers k, []⟩ : State S N W) (generatorComm rt root finders workers k) =
      generatorAfterComm rt root finders workers frame k := by
  rw [generatorComm, step_comm (frame := frame) _ _ _ _ (by simp [generatorTasks]),
    continuation_of_generator]
  simp [generatorAfterComm, generatorArena, Finset.sum_range_succ, generatorContinuation]

theorem generator_respawn_step (frame : Multiset (Task S)) (k : ℕ) :
    step rt (generatorAfterComm rt root finders workers frame k)
        (generatorRespawn rt root finders workers k) =
      generatorAfterRespawn rt root finders workers frame k := by
  rw [generatorRespawn, generatorAfterComm, step_spawn (frame := frame) _ _ _ _ rfl, spawned_pair]
  simp [generatorAfterRespawn, generatorCodeSupply, Multiset.insert_eq_cons]

theorem generator_unpack_step (frame : Multiset (Task S)) (k : ℕ) :
    step rt (generatorAfterRespawn rt root finders workers frame k)
        (generatorUnpack rt root finders workers k) =
      generatorAfterUnpack rt root finders workers frame k := by
  rw [generatorUnpack, generatorAfterRespawn,
    step_spawn (frame := task rt generatorSender
      (rt.naming.component (generatorContinuation rt root finders k) 2 0) ::ₘ frame) _ _ _ _
      (Multiset.cons_swap _ _ _), spawned_pair]
  simp only [generatorAfterUnpack, generatorTasks, generatorSupplies_succ, generatorZero,
    task_supply, Multiset.insert_eq_cons, Multiset.cons_add, Multiset.singleton_add]
  congr 1
  rw [Multiset.cons_swap (task rt dup _), Multiset.cons_swap (task rt dup _)]

theorem generator_finish_step (frame : Multiset (Task S)) (k : ℕ) :
    step rt (generatorAfterUnpack rt root finders workers frame k)
        (generatorFinish rt root finders workers k) =
      ⟨generatorTasks rt (generatorSupplies rt root finders (k + 1)) + frame,
        generatorArena rt workers (k + 1), []⟩ := by
  rw [generatorFinish, generatorAfterUnpack, step_finish _ _ _ _ (Multiset.cons_add _ _ _)]

omit [DecidableEq S] in
theorem generatorZeros_succ (k : ℕ) :
    generatorZeros rt root finders (k + 1) =
      task rt nil (generatorZero rt root finders k) ::ₘ generatorZeros rt root finders k := by
  simp [generatorZeros, Multiset.range_succ]

/-- **The lazy run**: after `k` COMMs the two persistent tasks are live beside the `k` copies of
`0` spawned so far. -/
theorem lazy_run (k : ℕ) :
    run rt (generatorStart rt root) (lazyRun rt root finders workers k) =
      ⟨generatorTasks rt (generatorSupplies rt root finders k) + generatorZeros rt root finders k,
        generatorArena rt workers k, []⟩ := by
  induction k with
  | zero =>
      simp only [lazyRun, run_cons, run_nil, generatorOpening, generatorStart]
      rw [step_spawn (frame := 0) _ _ _ _ (by simp), spawned_pair]
      simp [generatorTasks, generatorSupplies, generatorArena, generatorZeros]
  | succ k ih =>
      rw [lazyRun, run_append, run_append, run_append, ih]
      simp only [run_cons, run_nil]
      rw [generator_comm_step, generator_respawn_step, generator_unpack_step,
        generatorAfterUnpack, generatorZeros_succ]
      congr 1
      rw [Multiset.cons_add, ← Multiset.add_cons]

/-- **The eager run**: after `k` COMMs only the two persistent tasks are live. -/
theorem eager_run (k : ℕ) :
    run rt (generatorStart rt root) (eagerRun rt root finders workers k) =
      ⟨generatorTasks rt (generatorSupplies rt root finders k), generatorArena rt workers k, []⟩ := by
  induction k with
  | zero =>
      simp only [eagerRun, run_cons, run_nil, generatorOpening, generatorStart]
      rw [step_spawn (frame := 0) _ _ _ _ (by simp), spawned_pair]
      simp [generatorTasks, generatorSupplies, generatorArena]
  | succ k ih =>
      have zeroFrame := generator_comm_step rt root finders workers 0 k
      rw [add_zero] at zeroFrame
      rw [eagerRun, run_append, run_append, run_append, run_append, ih]
      simp only [run_cons, run_nil]
      rw [zeroFrame, generator_respawn_step, generator_unpack_step, generator_finish_step, add_zero]

private theorem generator_iteration_valid (frame : Multiset (Task S)) (k : ℕ) :
    Valid rt (⟨generatorTasks rt (generatorSupplies rt root finders k) + frame,
        generatorArena rt workers k, []⟩ : State S N W)
      [generatorComm rt root finders workers k, generatorRespawn rt root finders workers k,
        generatorUnpack rt root finders workers k] := by
  refine ⟨⟨rfl, rfl, by simp [generatorTasks]⟩, ?_⟩
  rw [generator_comm_step]
  refine ⟨⟨rfl, Multiset.mem_cons_self _ _⟩, ?_⟩
  rw [generator_respawn_step]
  exact ⟨⟨rfl, Multiset.mem_cons_of_mem (Multiset.mem_cons_self _ _)⟩, trivial⟩

/-- **The lazy run is valid.** -/
theorem lazy_valid (k : ℕ) :
    Valid rt (generatorStart rt root : State S N W) (lazyRun rt root finders workers k) := by
  induction k with
  | zero => exact ⟨⟨rfl, Multiset.mem_singleton_self _⟩, trivial⟩
  | succ k ih =>
      have iteration := generator_iteration_valid rt root finders workers
        (generatorZeros rt root finders k) k
      rw [lazyRun, List.append_assoc, List.append_assoc, valid_append, lazy_run]
      exact ⟨ih, by simpa using iteration⟩

/-- **The eager run is valid.** -/
theorem eager_valid (k : ℕ) :
    Valid rt (generatorStart rt root : State S N W) (eagerRun rt root finders workers k) := by
  induction k with
  | zero => exact ⟨⟨rfl, Multiset.mem_singleton_self _⟩, trivial⟩
  | succ k ih =>
      have iteration := generator_iteration_valid rt root finders workers 0 k
      rw [add_zero] at iteration
      rw [eagerRun, List.append_assoc, List.append_assoc, List.append_assoc, valid_append,
        eager_run]
      refine ⟨ih, ?_⟩
      simp only [List.cons_append, List.nil_append]
      rw [show [generatorComm rt root finders workers k, generatorRespawn rt root finders workers k,
          generatorUnpack rt root finders workers k, generatorFinish rt root finders workers k] =
          [generatorComm rt root finders workers k, generatorRespawn rt root finders workers k,
          generatorUnpack rt root finders workers k] ++ [generatorFinish rt root finders workers k]
          from rfl, valid_append]
      refine ⟨iteration, ?_⟩
      have zeroFrame := generator_comm_step rt root finders workers 0 k
      rw [add_zero] at zeroFrame
      simp only [run_cons, run_nil, zeroFrame, generator_respawn_step, generator_unpack_step]
      exact ⟨⟨rfl, by simp [generatorAfterUnpack]⟩, trivial⟩

/-- **The copy of `0` spawned after COMM number `k` is live in the eager run**, right after the
code spawns it. -/
theorem eager_zero_live (k : ℕ) :
    task rt nil (generatorZero rt root finders k) ∈
      (run rt (generatorStart rt root)
        (eagerRun rt root finders workers k ++ [generatorComm rt root finders workers k,
          generatorRespawn rt root finders workers k, generatorUnpack rt root finders workers k])).tasks := by
  have zeroFrame := generator_comm_step rt root finders workers 0 k
  rw [add_zero] at zeroFrame
  rw [run_append, eager_run]
  simp only [run_cons, run_nil, zeroFrame, generator_respawn_step, generator_unpack_step,
    generatorAfterUnpack]
  simp

/-- **Every state of the eager run holds at most three live tasks.** -/
theorem eager_prefix_tasks (k : ℕ) (choices : List (Choice S W))
    (isPrefix : choices <+: eagerRun rt root finders workers k) :
    (run rt (generatorStart rt root) choices).tasks.card ≤ 3 := by
  induction k generalizing choices with
  | zero =>
      rcases List.prefix_cons_iff.mp isPrefix with empty | ⟨rest, rfl, restPrefix⟩
      · subst empty; simp [generatorStart]
      · rcases List.prefix_nil.mp restPrefix with rfl
        have := eager_run rt root finders workers 0
        simp only [eagerRun] at this
        rw [this]; simp [generatorTasks]
  | succ k ih =>
      have zeroFrame := generator_comm_step rt root finders workers 0 k
      rw [add_zero] at zeroFrame
      rw [eagerRun] at isPrefix
      rcases List.prefix_concat_iff.mp isPrefix with whole | earlier
      · rw [whole, ← eagerRun, eager_run]; simp [generatorTasks]
      rcases List.prefix_concat_iff.mp earlier with whole | earlier
      · rw [whole, run_append, run_append, run_append, eager_run]
        simp only [run_cons, run_nil]
        rw [zeroFrame, generator_respawn_step, generator_unpack_step]
        simp [generatorAfterUnpack, generatorTasks]
      rcases List.prefix_concat_iff.mp earlier with whole | earlier
      · rw [whole, run_append, run_append, eager_run]
        simp only [run_cons, run_nil]
        rw [zeroFrame, generator_respawn_step]
        simp [generatorAfterRespawn]
      rcases List.prefix_concat_iff.mp earlier with whole | earlier
      · rw [whole, run_append, eager_run, run_cons, run_nil, zeroFrame]
        simp [generatorAfterComm]
      exact ih choices earlier

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.ParallelExecution
