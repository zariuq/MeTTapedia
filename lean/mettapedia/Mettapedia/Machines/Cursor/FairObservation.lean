import Mettapedia.Machines.Cursor.Scheduling
import Mettapedia.GSLT.LanguageDef.NativeControlBoundedCursor
import Mettapedia.GSLT.Core.SearchStreamProductivity

/-!
# Fair scheduling of finite observations of ongoing cursors

The provider and client are the existing indexed cursor protocol. A fair
schedule gives each retained work item unbounded inspection allocation. If
one observation can finish after finitely many inspections, that observation
eventually finishes under the fair schedule, with exactly the same receipt,
result, and provider residual. The provider itself need not terminate.

This is allocation fairness for independent retained packets. Each provider
transition must itself return; a blocking native call cannot acquire a wall
clock fairness guarantee from these laws. Reordering shared effects requires
a separate commuting-effects argument.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor.FairObservation

open Mettapedia.TypeTheory
open Scheduling

universe u v
variable {Base : Type u} {Index : Base → Type u}
variable {P : IndexedPolynomial.{u,u,u,u} Base Index}
variable {Return : (base : Base) → Index base → Type u}
variable (M : Provider P) (C : Client (P := P) (Return := Return))
variable (charge : Charge M)
variable {Id : Type v} [DecidableEq Id] {base : Base}

/-- The chronological finite prefix of an indefinitely authored schedule. -/
def schedulePrefix (schedule : Nat → Command Id) : Nat → List (Command Id)
  | 0 => []
  | length + 1 => schedulePrefix schedule length ++ [schedule length]

theorem allocation_append (id : Id) (first second : List (Command Id)) :
    allocation id (first ++ second) = allocation id first + allocation id second := by
  induction first with
  | nil => simp [allocation]
  | cons command rest ih => simp only [List.cons_append, allocation, ih, Nat.add_assoc]

theorem allocation_prefix_mono (schedule : Nat → Command Id) (id : Id)
    {earlier later : Nat} (ordered : earlier ≤ later) :
    allocation id (schedulePrefix schedule earlier) ≤
      allocation id (schedulePrefix schedule later) := by
  induction later, ordered using Nat.le_induction with
  | base => exact Nat.le_refl _
  | succ later _ ih =>
      rw [schedulePrefix, allocation_append]
      exact ih.trans (Nat.le_add_right _ _)

/-- Every retained identity receives any requested finite inspection budget.
No queue representation, answer order, or finite global work set is assumed. -/
def FairAllocation (schedule : Nat → Command Id) : Prop :=
  ∀ id demand, ∃ horizon,
    demand ≤ allocation id (schedulePrefix schedule horizon)

/-- Once a client finishes, a larger allocation neither polls its provider
again nor changes its receipt or terminal residual. -/
theorem resume_done_of_le (cell : Cell M C base) (needed available spent : Nat)
    (result : Finished M (Return := Return) base)
    (finished : resume M C charge needed cell = (spent, .done result))
    (enough : needed ≤ available) :
    resume M C charge available cell = (spent, .done result) := by
  have decomposition : available = needed + (available - needed) := by omega
  rw [decomposition, resume_add, finished, resume_done]

/-- Local progress plus allocation fairness gives eventual, permanent
completion of this observation. An infinite producer may satisfy the local
progress premise for each bounded demand separately. -/
theorem fair_eventually_done (schedule : Nat → Command Id)
    (fair : FairAllocation schedule) (pool : Pool M C Id base) (id : Id)
    (needed spent : Nat) (result : Finished M (Return := Return) base)
    (finished : resume M C charge needed (pool id) = (spent, .done result)) :
    ∃ horizon, ∀ extra,
      execute M C charge (schedulePrefix schedule (horizon + extra)) pool id =
        (spent, .done result) := by
  obtain ⟨horizon, enough⟩ := fair id needed
  refine ⟨horizon, fun extra => ?_⟩
  rw [execute_at]
  exact resume_done_of_le M C charge (pool id) needed _ spent result finished
    (enough.trans (allocation_prefix_mono schedule id (Nat.le_add_right _ _)))

/-- Fair scheduling is exact about what it can accomplish: completion is
equivalent to some finite local allocation, not to fairness alone. -/
theorem eventually_done_iff (schedule : Nat → Command Id)
    (fair : FairAllocation schedule) (pool : Pool M C Id base) (id : Id)
    (spent : Nat) (result : Finished M (Return := Return) base) :
    (∃ horizon,
      execute M C charge (schedulePrefix schedule horizon) pool id =
        (spent, .done result)) ↔
    (∃ needed, resume M C charge needed (pool id) = (spent, .done result)) := by
  constructor
  · rintro ⟨horizon, completed⟩
    exact ⟨allocation id (schedulePrefix schedule horizon),
      (execute_at M C charge _ pool id).symm.trans completed⟩
  · rintro ⟨needed, completed⟩
    obtain ⟨horizon, stable⟩ :=
      fair_eventually_done M C charge schedule fair pool id needed spent result completed
    exact ⟨horizon, by simpa using stable 0⟩

/-! ## A fair policy and an unfair policy -/

def roundRobin (step : Nat) : Command Bool := (decide (step % 2 = 1), 1)

theorem roundRobin_allocation (id : Bool) (rounds : Nat) :
    allocation id (schedulePrefix roundRobin (2 * rounds)) = rounds := by
  induction rounds with
  | zero => simp [schedulePrefix, allocation]
  | succ rounds ih =>
      have twice : 2 * (rounds + 1) = (2 * rounds + 1) + 1 := by omega
      rw [twice, schedulePrefix, allocation_append, schedulePrefix, allocation_append, ih]
      cases id <;> simp [allocation, roundRobin, Nat.add_mod]

theorem roundRobin_fair : FairAllocation roundRobin := by
  intro id demand
  exact ⟨2 * demand, by rw [roundRobin_allocation]⟩

/-- A depth-first policy that never switches away from the first ongoing
item is not allocation-fair to the other item. -/
def neverSwitch (_ : Nat) : Command Bool := (false, 1)

theorem neverSwitch_starves (horizon : Nat) :
    allocation true (schedulePrefix neverSwitch horizon) = 0 := by
  induction horizon with
  | zero => rfl
  | succ horizon ih => simp [schedulePrefix, allocation_append, ih, allocation, neverSwitch]

theorem neverSwitch_not_fair : ¬ FairAllocation neverSwitch := by
  intro fair
  obtain ⟨horizon, enough⟩ := fair true 1
  rw [neverSwitch_starves] at enough
  omega

section OngoingProducer

open Mettapedia.GSLT.LanguageDef
open HostCalls (Pull)
open NativeControlEffectCursor (provider)
open NativeControlBoundedCursor (client packet collectBounded)
open Mettapedia.GSLT.Core.SearchStreamProductivity (streamPrefix)

variable {Answer World : Type}

/-- A genuine ongoing producer: every poll emits another authored occurrence.
The answer type may contain closures, witnesses, or repeated values. -/
def streamPull (expected : Nat → Answer) (index : Nat) (world : World) :
    World × Pull Nat Answer := (world, .yield (expected index) (index + 1))

theorem streamPrefix_succ (expected : Nat → Answer) (demand : Nat) :
    streamPrefix expected (demand + 1) =
      expected 0 :: streamPrefix (fun index => expected (index + 1)) demand := by
  simp only [streamPrefix, List.ofFn_succ]
  rfl

/-- Every requested finite prefix is obtained after exactly that many polls,
without inspecting the next occurrence or asserting global exhaustion. -/
theorem stream_collect_exact (expected : Nat → Answer) (demand index : Nat)
    (world : World) :
    collectBounded (streamPull expected) demand demand index world =
      (demand, ⟨index + demand, world,
        streamPrefix (fun offset => expected (index + offset)) demand, 0, .limit⟩) := by
  induction demand generalizing index with
  | zero => simp [collectBounded, streamPrefix]
  | succ demand ih =>
      simp only [collectBounded, streamPull, ih,
        NativeControlBoundedCursor.Snapshot.prefix, List.singleton_append]
      rw [streamPrefix_succ]
      simp [Nat.add_comm, Nat.add_left_comm]

/-- The independent collector's finite-prefix law transfers to the actual
protocol client. The extra inspection publishes, without another pull. -/
theorem stream_client_exact (expected : Nat → Answer) (demand index : Nat)
    (world : World) :
    advance (provider (streamPull expected)) (client Answer) (fun _ _ => 1)
      (demand + 1) (packet (streamPull expected) demand index world []) =
      (demand, .done ⟨(), ⟨0, .limit,
        streamPrefix (fun offset => expected (index + offset)) demand⟩,
        (index + demand, world)⟩) := by
  simpa using NativeControlBoundedCursor.completed_exact (streamPull expected)
    demand demand index world [] demand 0 (index + demand) world
    (streamPrefix (fun offset => expected (index + offset)) demand) .limit
    (stream_collect_exact expected demand index world)

/-- `once` observes one occurrence of an ongoing producer and leaves its
second occurrence unpolled. This does not require producer termination. -/
theorem stream_once (expected : Nat → Answer) (index : Nat) (world : World) :
    collectBounded (streamPull expected) 1 1 index world =
      (1, ⟨index + 1, world, [expected index], 0, .limit⟩) := rfl

/-- A whole pool may contain ongoing sources. Every requested finite prefix
is nevertheless delivered under fair scheduling of the retained clients. -/
theorem fair_stream_observation (expected : Nat → Answer)
    (demands starts : Id → Nat) (worlds : Id → World)
    (schedule : Nat → Command Id) (fair : FairAllocation schedule) (id : Id) :
    let pool : Pool (provider (streamPull expected)) (client Answer) Id () :=
      fun item => (0, .paused (packet (streamPull expected)
        (demands item) (starts item) (worlds item) []))
    ∃ horizon, ∀ extra,
      execute (provider (streamPull expected)) (client Answer) (fun _ _ => 1)
        (schedulePrefix schedule (horizon + extra)) pool id =
      (demands id, .done ⟨(), ⟨0, .limit,
        streamPrefix (fun offset => expected (starts id + offset)) (demands id)⟩,
        (starts id + demands id, worlds id)⟩) := by
  dsimp only
  apply fair_eventually_done _ _ _ schedule fair _ id (demands id + 1)
  simpa only [resume, Nat.zero_add] using
    stream_client_exact expected (demands id) (starts id) (worlds id)

end OngoingProducer

#print axioms fair_eventually_done
#print axioms eventually_done_iff
#print axioms stream_collect_exact
#print axioms stream_client_exact
#print axioms roundRobin_fair
#print axioms fair_stream_observation

end Mettapedia.Machines.Cursor.FairObservation
