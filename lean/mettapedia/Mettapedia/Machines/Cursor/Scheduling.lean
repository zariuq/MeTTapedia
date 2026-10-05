import Mettapedia.Machines.Cursor.Protocol
import Mettapedia.Machines.SnapshotBatch

/-!
# Scheduling retained work without choosing an inference algorithm

Work identifiers index independently owned client/provider packets. A scheduling
command advances one existing packet by a quantum. No queue discipline, valuation,
inference rule, or processed-clause representation is built into this interface.

The allocation theorem identifies the exact residual and charge of every work item
under any finite schedule. Equal per-item allocations give equal states; permutation
is one sufficient condition. This is an independence theorem: each item owns its
provider state. It does not reorder accesses to a shared mutable provider.

Private quanta reuse the snapshot/private-write kernel: workers compute owned
cells and installation consumes those completed writes without another provider
request. The comparison keeps the entire indexed store and its cumulative
charges. Physical ownership transfer, ambient thread state and source
revalidation remain implementation obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor.Scheduling

open Mettapedia.TypeTheory
open CategoryTheory

universe u v
variable {Base : Type u} {Index : Base → Type u}
variable {P : IndexedPolynomial.{u,u,u,u} Base Index}
variable {Return : (base : Base) → Index base → Type u}
variable (M : Provider P) (C : Client (P := P) (Return := Return))
variable (charge : Charge M)
variable {Id : Type v} [DecidableEq Id] {base : Base}

/-- A work item retains its charge and exact cursor outcome, including suspension. -/
abbrev Cell (base : Base) := Nat × Outcome M C base

/-- A mathematical ownership boundary, not a physical array or queue. -/
abbrev Pool (Id : Type v) (base : Base) := Id → Cell M C base

/-- A quantum counts protocol inspections. It is not asserted to be CPU time. -/
abbrev Command (Id : Type v) := Id × Nat

def dispatch (command : Command Id) (pool : Pool M C Id base) :
    Pool M C Id base :=
  Function.update pool command.1
    (resume M C charge command.2 (pool command.1))

def execute : List (Command Id) → Pool M C Id base → Pool M C Id base
  | [], pool => pool
  | command :: rest, pool =>
      execute rest (dispatch M C charge command pool)

/-- Inspections allocated to this identity, regardless of scheduling order. -/
def allocation (id : Id) : List (Command Id) → Nat
  | [] => 0
  | command :: rest =>
      (if command.1 = id then command.2 else 0) + allocation id rest

@[simp] theorem dispatch_selected (command : Command Id)
    (pool : Pool M C Id base) :
    dispatch M C charge command pool command.1 =
      resume M C charge command.2 (pool command.1) := by
  simp [dispatch]

@[simp] theorem dispatch_other (command : Command Id)
    (pool : Pool M C Id base) (id : Id) (different : id ≠ command.1) :
    dispatch M C charge command pool id = pool id := by
  simp [dispatch, different]

/-- Scheduling never restarts a packet, even when it has already completed. -/
theorem execute_at (schedule : List (Command Id))
    (pool : Pool M C Id base) (id : Id) :
    execute M C charge schedule pool id =
      resume M C charge (allocation id schedule) (pool id) := by
  induction schedule generalizing pool with
  | nil => simp [execute, allocation]
  | cons command rest ih =>
      rw [execute, ih]
      by_cases same : command.1 = id
      · subst id
        simp only [allocation, dispatch_selected]
        exact (resume_add M C charge command.2 (allocation command.1 rest)
          (pool command.1)).symm
      · have different : id ≠ command.1 := Ne.symm same
        simp [allocation, same, dispatch_other, different]

theorem execute_append (first second : List (Command Id))
    (pool : Pool M C Id base) :
    execute M C charge (first ++ second) pool =
      execute M C charge second (execute M C charge first pool) := by
  induction first generalizing pool with
  | nil => rfl
  | cons command rest ih =>
      simp only [List.cons_append, execute, ih]

theorem allocation_perm {first second : List (Command Id)}
    (permutation : first.Perm second) (id : Id) :
    allocation id first = allocation id second := by
  induction permutation with
  | nil => rfl
  | cons command permutation ih => simp only [allocation, ih]
  | swap first second rest =>
      simp only [allocation]
      omega
  | trans first second ihFirst ihSecond => exact ihFirst.trans ihSecond

/-- The actual criterion is allocation equality, allowing splitting and fusion
of quanta as well as permutation of commands. -/
theorem execute_eq_of_allocation_eq (first second : List (Command Id))
    (allocations : ∀ id, allocation id first = allocation id second)
    (pool : Pool M C Id base) :
    execute M C charge first pool = execute M C charge second pool := by
  funext id
  rw [execute_at, execute_at, allocations id]

theorem execute_perm {first second : List (Command Id)}
    (permutation : first.Perm second) (pool : Pool M C Id base) :
    execute M C charge first pool = execute M C charge second pool :=
  execute_eq_of_allocation_eq M C charge first second
    (fun id => allocation_perm permutation id) pool

/-- Inline consecutive quanta for one identity without changing any residual
or operation receipt. Queue-management overhead is not included in this law. -/
theorem fuse_quanta (id : Id) (first second : Nat)
    (pool : Pool M C Id base) :
    execute M C charge [(id, first), (id, second)] pool =
      execute M C charge [(id, first + second)] pool := by
  apply execute_eq_of_allocation_eq
  intro other
  by_cases same : id = other <;> simp [allocation, same]

theorem resume_charge_monotone (quantum : Nat) (cell : Cell M C base) :
    cell.1 ≤ (resume M C charge quantum cell).1 := by
  rcases cell with ⟨spent, outcome⟩
  cases outcome <;> simp [resume]

/-- Reprioritizing cannot refund a work item's already incurred charges. -/
theorem execute_charge_monotone (schedule : List (Command Id))
    (pool : Pool M C Id base) (id : Id) :
    (pool id).1 ≤ (execute M C charge schedule pool id).1 := by
  rw [execute_at]
  exact resume_charge_monotone M C charge _ _

theorem unallocated_unchanged (schedule : List (Command Id))
    (pool : Pool M C Id base) (id : Id) (unallocated : allocation id schedule = 0) :
    execute M C charge schedule pool id = pool id := by
  rw [execute_at, unallocated, resume_zero]

/-! ## Private quantum preparation and installation -/

/-- The fixed charge profile and logical quantum feed the existing private-write
 * kernel. Each destination stores its cumulative charge and full cursor outcome. -/
def quantumKernel : SnapshotBatch.Kernel
    (Charge M) (Command Id) Nat Id (Cell M C base) where
  destination := Prod.fst
  compute valuation _command quantum cell := resume M C valuation quantum cell

/-- Compute paid quanta from independently owned initial packets. This does not
 * install their residuals or advance the parent scheduler. -/
def prepareQuanta (schedule : List (Command Id)) (pool : Pool M C Id base) :
    List (Id × Cell M C base) :=
  (quantumKernel M C).prepare charge Prod.snd pool schedule

/-- Install already computed cells. No provider step or charge callback runs here;
 * the charge argument is deliberately absent. -/
def installQuanta (writes : List (Id × Cell M C base))
    (pool : Pool M C Id base) : Pool M C Id base :=
  SnapshotBatch.Kernel.publish pool writes

/-- The sequential private kernel is the independently defined scheduler. -/
theorem quantum_kernel_reference (schedule : List (Command Id))
    (pool : Pool M C Id base) :
    (quantumKernel M C).run charge Prod.snd pool schedule =
      execute M C charge schedule pool := by
  induction schedule generalizing pool with
  | nil => rfl
  | cons command rest ih =>
      rw [SnapshotBatch.Kernel.run_cons, execute]
      exact ih _

/-- Distinct writable owners make preparation and installation agree with
 * sequential execution at the complete pool, including charges and residuals. -/
theorem prepared_quanta_agree (schedule : List (Command Id))
    (pool : Pool M C Id base) (distinct : (schedule.map Prod.fst).Nodup) :
    installQuanta M C (prepareQuanta M C charge schedule pool) pool =
      execute M C charge schedule pool := by
  have unique : (quantumKernel M C (Id := Id) (base := base)).Disjoint schedule := distinct
  exact ((quantumKernel M C).batch_eq_run charge Prod.snd pool schedule unique).trans
    (quantum_kernel_reference M C charge schedule pool)

/-- The installed cell contains exactly its allocated prefix. Installing it
 * does not spend another evaluator quantum. -/
theorem prepared_quanta_at (schedule : List (Command Id))
    (pool : Pool M C Id base) (distinct : (schedule.map Prod.fst).Nodup) (id : Id) :
    installQuanta M C (prepareQuanta M C charge schedule pool) pool id =
      resume M C charge (allocation id schedule) (pool id) := by
  rw [prepared_quanta_agree M C charge schedule pool distinct,
    execute_at]

/-- Worker partition and completion order preserve the logical scheduler
 * under a common immutable profile and distinct writable destinations. -/
theorem prepared_quanta_partitioned (parts : List (List (Command Id)))
    (schedule : List (Command Id)) (pool : Pool M C Id base)
    (coverage : parts.flatten.Perm schedule) (distinct : (schedule.map Prod.fst).Nodup) :
    installQuanta M C ((parts.map (fun part => prepareQuanta M C charge part pool)).flatten)
      pool = execute M C charge schedule pool := by
  have unique : (quantumKernel M C (Id := Id) (base := base)).Disjoint schedule := distinct
  exact ((quantumKernel M C).partitioned_eq_run charge Prod.snd pool parts schedule
    coverage unique).trans (quantum_kernel_reference M C charge schedule pool)

/-! ## Differently indexed packets on one private frontier -/

/-- The protocol tag selects the actual provider, control and result families.
 * Packing retains that dependency instead of casting every operation to one mode. -/
abbrev PackedCell := Σ base : Base, Cell M C base

/-- Resume the retained packet through its own tag, preserving its full charge. -/
def resumePacked (quantum : Nat) (cell : PackedCell M C) : PackedCell M C :=
  ⟨cell.1, resume M C charge quantum cell.2⟩

@[simp] theorem resumePacked_zero (cell : PackedCell M C) :
    resumePacked M C charge 0 cell = cell := by
  rcases cell with ⟨base, cell⟩
  simp [resumePacked]

theorem resumePacked_add (first second : Nat) (cell : PackedCell M C) :
    resumePacked M C charge (first + second) cell =
      resumePacked M C charge second (resumePacked M C charge first cell) := by
  rcases cell with ⟨base, cell⟩
  simp only [resumePacked, resume_add]

/-- The same private-write construction accepts differently indexed packets.
 * Each item can mutate only its own retained cell under the immutable charge profile. -/
def packedQuantumKernel : SnapshotBatch.Kernel
    (Charge M) (Command Id) Nat Id (PackedCell M C) where
  destination := Prod.fst
  compute valuation _command quantum cell := resumePacked M C valuation quantum cell

/-- Prepare without publication. The tag stays attached to the paid result. -/
def preparePackedQuanta (schedule : List (Command Id)) (pool : Id → PackedCell M C) :=
  (packedQuantumKernel M C).prepare charge Prod.snd pool schedule

/-- Installation performs no provider request, including across protocol kinds. -/
def installPackedQuanta (writes : List (Id × PackedCell M C))
    (pool : Id → PackedCell M C) : Id → PackedCell M C :=
  SnapshotBatch.Kernel.publish pool writes

/-- Compare the private kernel with independently allocated cursor resumptions. -/
theorem packed_kernel_reference_at (schedule : List (Command Id))
    (pool : Id → PackedCell M C) (id : Id) :
    (packedQuantumKernel M C).run charge Prod.snd pool schedule id =
      resumePacked M C charge (allocation id schedule) (pool id) := by
  induction schedule generalizing pool with
  | nil => simp [allocation]
  | cons command rest ih =>
      rw [SnapshotBatch.Kernel.run_cons, ih]
      by_cases same : command.1 = id
      · subst id
        simp only [allocation, SnapshotBatch.Kernel.step,
          packedQuantumKernel, Function.update_self, if_true]
        exact (resumePacked_add M C charge command.2 (allocation command.1 rest)
          (pool command.1)).symm
      · have different : id ≠ command.1 := Ne.symm same
        simp [allocation, same, SnapshotBatch.Kernel.step, packedQuantumKernel,
          Function.update_of_ne different]

/-- Every installed cell is exactly its paid prefix, with no extra grant. -/
theorem prepared_packed_quanta_at (schedule : List (Command Id))
    (pool : Id → PackedCell M C) (distinct : (schedule.map Prod.fst).Nodup) (id : Id) :
    installPackedQuanta M C (preparePackedQuanta M C charge schedule pool) pool id =
      resumePacked M C charge (allocation id schedule) (pool id) := by
  have unique : (packedQuantumKernel M C).Disjoint schedule := distinct
  have full := (packedQuantumKernel M C).batch_eq_run charge Prod.snd pool schedule unique
  exact (congrArg (fun result => result id) full).trans
    (packed_kernel_reference_at M C charge schedule pool id)

/-- Worker partition and completion order preserve the complete tagged pool.
 * Writable ownership remains a hypothesis; protocol tags alone do not imply it. -/
theorem prepared_packed_quanta_partitioned (parts : List (List (Command Id)))
    (schedule : List (Command Id)) (pool : Id → PackedCell M C)
    (coverage : parts.flatten.Perm schedule) (distinct : (schedule.map Prod.fst).Nodup) :
    installPackedQuanta M C
      ((parts.map (fun part => preparePackedQuanta M C charge part pool)).flatten) pool =
      fun id => resumePacked M C charge (allocation id schedule) (pool id) := by
  have unique : (packedQuantumKernel M C).Disjoint schedule := distinct
  have full := (packedQuantumKernel M C).partitioned_eq_run charge Prod.snd pool parts schedule
    coverage unique
  funext id
  exact (congrArg (fun result => result id) full).trans
    (packed_kernel_reference_at M C charge schedule pool id)

/-- A completed worker cannot reinterpret its result as another protocol. -/
theorem prepared_packed_quanta_keep_protocol (schedule : List (Command Id))
    (pool : Id → PackedCell M C) (distinct : (schedule.map Prod.fst).Nodup) (id : Id) :
    (installPackedQuanta M C (preparePackedQuanta M C charge schedule pool) pool id).1 =
      (pool id).1 := by
  rw [prepared_packed_quanta_at M C charge schedule pool distinct id]
  rfl

/-- The same owner can run in later waves from its installed residual.
 * Distinctness is required within each simultaneous preparation, not across time. -/
theorem prepared_packed_waves_at (first second : List (Command Id))
    (pool : Id → PackedCell M C) (firstDistinct : (first.map Prod.fst).Nodup)
    (secondDistinct : (second.map Prod.fst).Nodup) (id : Id) :
    let earlierPool := installPackedQuanta M C
      (preparePackedQuanta M C charge first pool) pool
    installPackedQuanta M C (preparePackedQuanta M C charge second earlierPool)
      earlierPool id =
      resumePacked M C charge (allocation id first + allocation id second) (pool id) := by
  dsimp only
  rw [prepared_packed_quanta_at M C charge second _ secondDistinct id,
    prepared_packed_quanta_at M C charge first _ firstDistinct id]
  exact (resumePacked_add M C charge _ _ _).symm

/-- The existing fixed-protocol pool is the constant-family case of packing. -/
theorem prepared_packed_constant_family {base : Base} (schedule : List (Command Id))
    (pool : Pool M C Id base) (distinct : (schedule.map Prod.fst).Nodup) (id : Id) :
    installPackedQuanta M C
      (preparePackedQuanta M C charge schedule (fun id => ⟨base, pool id⟩))
      (fun id => ⟨base, pool id⟩) id =
      ⟨base, installQuanta M C (prepareQuanta M C charge schedule pool) pool id⟩ := by
  rw [prepared_packed_quanta_at M C charge schedule _ distinct id,
    prepared_quanta_at M C charge schedule pool distinct id]
  rfl

namespace PackedControls
open CategoryTheory

def protocol : IndexedPolynomial Bool (fun _ => Unit) where
  Shape base _ := match base with | false => Unit | true => Nat
  Position {base} _ _ := match base with | false => Option Nat | true => Unit
  next _ _ := ()

def provider : Provider protocol where
  State base _ := match base with | false => List Nat | true => Nat
  step {base} {_} state request := by
    cases base with
    | false => exact match state with
        | [] => ⟨none, []⟩
        | value :: rest => ⟨some value, rest⟩
    | true =>
        change Nat at state request
        exact ⟨(), state + request⟩

def client : Client (P := protocol)
    (Return := fun base _ => match base with | false => List Nat | true => Nat) where
  V base _ := match base with
    | false => List Nat × Bool
    | true => List Nat × Nat
  str := fun base _ => ↾(fun state => by
    cases base with
    | false => exact if state.2 then
        ⟨.inl state.1, fun impossible => nomatch impossible⟩
      else ⟨.inr (), fun reply => match reply with
        | none => (state.1, true)
        | some value => (state.1 ++ [value], false)⟩
    | true => exact match state.1 with
        | [] => ⟨.inl state.2, fun impossible => nomatch impossible⟩
        | increment :: rest => ⟨.inr increment, fun _ => (rest, state.2 + increment)⟩)

def receipt : Charge provider := fun {base} {_} _ request => by
  cases base with
  | false => exact 1
  | true =>
      change Nat at request
      exact request + 1

def pool : Bool → PackedCell provider client
  | false => ⟨false, 0, .paused ⟨(), ([], false), [3, 3, 5]⟩⟩
  | true => ⟨true, 0, .paused ⟨(), ([1, 2], 0), (0 : Nat)⟩⟩

def observed (cell : PackedCell provider client) : Nat × Option (Nat ⊕ List Nat) :=
  match cell with
  | ⟨false, spent, .paused _⟩ => (spent, none)
  | ⟨false, spent, .done result⟩ => (spent, some (.inr result.2.1))
  | ⟨true, spent, .paused _⟩ => (spent, none)
  | ⟨true, spent, .done result⟩ => (spent, some (.inl result.2.1))

theorem mixed_types_finish_without_protocol_cast :
    let result := installPackedQuanta provider client
      (preparePackedQuanta provider client receipt [(false, 5), (true, 3)] pool) pool
    observed (result false) = (4, some (.inr [3, 3, 5])) ∧
      observed (result true) = (5, some (.inl 3)) := by
  constructor <;> rfl

theorem mixed_types_keep_complete_residual :
    let result := installPackedQuanta provider client
      (preparePackedQuanta provider client receipt [(false, 2), (true, 2)] pool) pool
    result false = ⟨false, 2, .paused ⟨(), ([3, 3], false), [5]⟩⟩ ∧
      result true = ⟨true, 5, .paused ⟨(), ([], 3), (3 : Nat)⟩⟩ := by
  constructor <;> rfl

theorem resuming_one_type_keeps_the_other :
    let earlierPool := installPackedQuanta provider client
      (preparePackedQuanta provider client receipt [(false, 2), (true, 2)] pool) pool
    let final := installPackedQuanta provider client
      (preparePackedQuanta provider client receipt [(false, 3)] earlierPool) earlierPool
    observed (final false) = (4, some (.inr [3, 3, 5])) ∧
      final true = earlierPool true := by
  constructor <;> rfl

theorem choosing_wrong_protocol_is_observable :
    (pool false).1 ≠ (pool true).1 := by decide

theorem repeated_private_owner_loses_exhaustion :
    observed (installPackedQuanta provider client
      (preparePackedQuanta provider client receipt [(false, 3), (false, 3)] pool)
      pool false) = (3, none) ∧
    observed (resumePacked provider client receipt 6 (pool false)) =
      (4, some (.inr [3, 3, 5])) := by
  constructor <;> rfl

end PackedControls


/-! ## Concrete independent work and a shared-state counterexample -/

namespace Controls

def protocol : IndexedPolynomial Unit (fun _ => Unit) where
  Shape _ _ := Nat
  Position _ := Unit
  next _ _ := ()

def provider : Provider protocol where
  State _ _ := Nat
  step state increment := by
    change Nat at increment
    exact ⟨(), state + increment⟩

def client : Client (P := protocol) (Return := fun _ _ => Nat) where
  V _ _ := List Nat × Nat
  str := fun _ _ => ↾(fun state => match state.1 with
    | [] => ⟨Sum.inl state.2, fun impossible => nomatch impossible⟩
    | increment :: rest =>
        ⟨Sum.inr increment, fun _ => (rest, state.2 + increment)⟩)

def receipt : Charge provider := fun _ increment => by
  change Nat at increment
  exact increment + 1

def initial : Pool provider client Bool () :=
  fun id => (0, .paused ⟨(), ((if id then [5] else [1, 2]), 0), (0 : Nat)⟩)

def summary (cell : Cell provider client ()) : Nat × Option (Nat × Nat) :=
  (cell.1, match cell.2 with
    | .paused _ => none
    | .done result => some (result.2.1, result.2.2))

theorem interleaved_finishes_exactly :
    let result := execute provider client receipt
      [(false, 1), (true, 1), (false, 2), (true, 1)] initial
    summary (result false) = (5, some (3, 3)) ∧
      summary (result true) = (6, some (5, 5)) := by
  constructor <;> rfl

theorem insufficient_quantum_retains_work :
    summary (execute provider client receipt [(false, 1)] initial false) =
      (2, none) ∧
    execute provider client receipt [(false, 1)] initial true = initial true := by
  constructor <;> rfl

/-- A shared mutable cell is deliberately outside Pool's independence boundary. -/
inductive SharedCommand where
  | write (value : Nat)
  | read

def sharedStep : SharedCommand → Nat × List Nat → Nat × List Nat
  | .write value, (_, answers) => (value, answers)
  | .read, (value, answers) => (value, answers ++ [value])

theorem shared_access_reordering_changes_answers :
    (sharedStep .read (sharedStep (.write 1) (0, []))).2 ≠
      (sharedStep (.write 1) (sharedStep .read (0, []))).2 := by
  decide

theorem prepared_interleaving_agrees :
    installQuanta provider client
      (prepareQuanta provider client receipt [(false, 3), (true, 2)] initial) initial =
      execute provider client receipt
        [(false, 1), (true, 1), (false, 2), (true, 1)] initial := by
  rw [prepared_quanta_agree provider client receipt _ initial (by decide)]
  apply execute_eq_of_allocation_eq
  intro id
  cases id <;> rfl

/-- Two preparations from the same initial owner overwrite rather than compose. -/
theorem repeated_owner_loses_paid_progress :
    summary (installQuanta provider client
      (prepareQuanta provider client receipt [(false, 1), (false, 1)] initial) initial false) =
      (2, none) ∧
    summary (execute provider client receipt [(false, 1), (false, 1)] initial false) =
      (5, none) := by
  constructor <;> rfl

/-- Re-entering dispatch during installation spends an unauthorized second quantum. -/
theorem joining_with_extra_quantum_is_wrong :
    summary (installQuanta provider client
      (prepareQuanta provider client receipt [(false, 1)] initial) initial false) =
      (2, none) ∧
    summary (dispatch provider client receipt (false, 1)
      (installQuanta provider client
        (prepareQuanta provider client receipt [(false, 1)] initial) initial) false) =
      (5, none) := by
  constructor <;> rfl


end Controls

#print axioms prepared_packed_quanta_partitioned
#print axioms prepared_packed_waves_at
#print axioms prepared_packed_constant_family
#print axioms prepared_quanta_agree
#print axioms prepared_quanta_partitioned
#print axioms execute_at
#print axioms execute_perm
#print axioms fuse_quanta
#print axioms execute_charge_monotone
#print axioms Controls.shared_access_reordering_changes_answers

end Mettapedia.Machines.Cursor.Scheduling
