import Mettapedia.Machines.Cursor.Protocol

/-!
# Scheduling retained work without choosing an inference algorithm

Work identifiers index independently owned client/provider packets. A scheduling
command advances one existing packet by a quantum. No queue discipline, valuation,
inference rule, or processed-clause representation is built into this interface.

The allocation theorem identifies the exact residual and charge of every work item
under any finite schedule. Equal per-item allocations give equal states; permutation
is one sufficient condition. This is an independence theorem: each item owns its
provider state. It does not reorder accesses to a shared mutable provider.
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

end Controls

#print axioms execute_at
#print axioms execute_perm
#print axioms fuse_quanta
#print axioms execute_charge_monotone
#print axioms Controls.shared_access_reordering_changes_answers

end Mettapedia.Machines.Cursor.Scheduling
