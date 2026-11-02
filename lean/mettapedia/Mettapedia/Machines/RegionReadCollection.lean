import Mettapedia.Machines.ResourceOwnership

/-!
# Collection between operations of a nested read region

The operation language contains nested sequencing and complete finite-path
reads. Its stack, fallback handles and returned handles determine the roots;
there is no caller-supplied claim that a proposed root list is complete.
The worker may trace and collect before every operation. It preserves the
entire ordered answer prefix and pending stack of the uncollected machine.

Paths contain candidate edge addresses, not additional root capabilities.
Following an edge requires membership in the actual cell's references. Shared
and cyclic graphs are allowed. Answers retain their endpoint handles, so a
later client may continue reading from them. Missing roots remain missing.

This is a read-region operation model. A source adapter must account for its
own hidden fields, writes and allocation. It does not discover native C roots
or license simultaneous mutation of the protected graph.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.RegionReadCollection

open ResourceOwnership

variable {Address Value : Type} [DecidableEq Address]

inductive Task (Address : Type) where
  | read (start : Address) (path : List Address)
  | sequence (first second : Task Address)
  deriving DecidableEq

def Task.roots : Task Address → List Address
  | .read start _ => [start]
  | .sequence first second => first.roots ++ second.roots

abbrev Answer (Address Value : Type) := Option (Address × Cell Address Value)

structure State (Address Value : Type) where
  pending : List (Task Address)
  fallback : List Address
  answers : List (Answer Address Value)

def State.roots (state : State Address Value) : List Address :=
  state.fallback ++ state.answers.filterMap (Option.map Prod.fst) ++
    state.pending.flatMap Task.roots

def State.registry (state : State Address Value) : Roots Unit Address :=
  state.roots.toFinset.image (fun address => ((), address))

theorem registry_mem (state : State Address Value) (address : Address) :
    ((), address) ∈ state.registry ↔ address ∈ state.roots := by simp [State.registry]

def step (heap : Heap Address Value) (state : State Address Value) : State Address Value :=
  match state.pending with
  | [] => state
  | .sequence first second :: rest => {state with pending := first :: second :: rest}
  | .read start path :: rest =>
      {state with pending := rest, answers := state.answers ++ [walk heap start path]}

def run (heap : Heap Address Value) : Nat → State Address Value → State Address Value
  | 0, state => state
  | budget + 1, state => run heap budget (step heap state)

theorem run_add (heap : Heap Address Value) (first second : Nat) (state : State Address Value) :
    run heap (first + second) state = run heap second (run heap first state) := by
  induction first generalizing state with
  | zero => simp [run]
  | succ first ih => simpa only [Nat.succ_add, run] using ih (step heap state)

/-- Each needed handle is absent or belongs to the retained source graph. -/
def Covered (heap : Heap Address Value) (roots : Roots Unit Address) (state : State Address Value) : Prop :=
  ∀ address ∈ state.roots, address ∉ heap.allocated ∨ Live heap roots address

theorem self_covered (heap : Heap Address Value) (state : State Address Value) :
    Covered heap state.registry state := by
  intro address member
  by_cases allocated : address ∈ heap.allocated
  · exact Or.inr (live_of_root heap state.registry ((registry_mem state address).mpr member) allocated)
  · exact Or.inl allocated

omit [DecidableEq Address] in
theorem lookup_absent (heap : Heap Address Value) (address : Address)
    (absent : address ∉ heap.allocated) : heap.lookup address = none := by
  cases found : heap.lookup address with
  | none => rfl
  | some cell => exact False.elim (absent ((heap.allocated_iff address).mpr ⟨cell, found⟩))

theorem walk_absent (heap : Heap Address Value) (address : Address) (path : List Address)
    (absent : address ∉ heap.allocated) : walk heap address path = none := by
  cases path <;> simp [walk, lookup_absent heap address absent]

theorem walk_success_live (heap : Heap Address Value) (roots : Roots Unit Address)
    (start endpoint : Address) (path : List Address) (cell : Cell Address Value)
    (live : Live heap roots start) (success : walk heap start path = some (endpoint, cell)) :
    Live heap roots endpoint := by
  induction path generalizing start with
  | nil =>
      obtain ⟨found, _, equal⟩ := Option.map_eq_some_iff.mp success
      have same : start = endpoint := congrArg Prod.fst equal
      exact same ▸ live
  | cons next rest ih =>
      cases found : heap.lookup start with
      | none => simp [walk, found] at success
      | some here =>
          simp only [walk, found, Option.bind_some] at success
          split at success
          next reference => exact ih next (live_step heap roots live found reference) success
          next => cases success

theorem walk_preserved (heap : Heap Address Value) (roots : Roots Unit Address)
    (start : Address) (path : List Address)
    (covered : start ∉ heap.allocated ∨ Live heap roots start) :
    walk (collect heap roots) start path = walk heap start path := by
  rcases covered with absent | live
  · have removed : start ∉ (collect heap roots).allocated := by
      intro present
      exact absent (live_allocated heap roots ((mem_footprint heap roots start).mp present))
    rw [walk_absent _ _ _ removed, walk_absent _ _ _ absent]
  · exact walk_collect heap roots live path

theorem step_preserved (heap : Heap Address Value) (roots : Roots Unit Address)
    (state : State Address Value) (covered : Covered heap roots state) :
    step (collect heap roots) state = step heap state := by
  cases pending : state.pending with
  | nil => simp [step, pending]
  | cons task rest =>
      cases task with
      | sequence => simp [step, pending]
      | read start path =>
          have needed : start ∈ state.roots := by simp [State.roots, pending, Task.roots]
          simp only [step, pending, walk_preserved heap roots start path (covered start needed)]

theorem step_covered (heap : Heap Address Value) (roots : Roots Unit Address)
    (state : State Address Value) (covered : Covered heap roots state) :
    Covered heap roots (step heap state) := by
  intro address member
  cases pending : state.pending with
  | nil => exact covered address (by simpa [step, pending] using member)
  | cons task rest =>
      cases task with
      | sequence first second =>
          apply covered address
          simpa [step, pending, State.roots, Task.roots, List.mem_append, or_assoc] using member
      | read start path =>
          have head : start ∈ state.roots := by simp [State.roots, pending, Task.roots]
          cases observed : walk heap start path with
          | none =>
              apply covered address
              simp only [step, pending, State.roots, List.filterMap_append, observed,
                List.filterMap_cons, List.filterMap_nil, Option.map_none, List.append_nil,
                List.mem_append] at member
              simp only [State.roots, pending, Task.roots, List.flatMap_cons, List.mem_append,
                List.mem_cons, List.not_mem_nil, or_false]
              tauto
          | some result =>
              rcases result with ⟨endpoint, cell⟩
              have reached : Live heap roots endpoint := by
                rcases covered start head with absent | live
                · rw [walk_absent heap start path absent] at observed
                  cases observed
                · exact walk_success_live heap roots start endpoint path cell live observed
              simp only [step, pending, State.roots, List.filterMap_append, observed,
                List.filterMap_cons, List.filterMap_nil, Option.map_some, List.mem_append,
                List.mem_cons, List.not_mem_nil, or_false] at member
              rcases member with (old | old | equal) | old
              · exact covered address (by simp [State.roots, old])
              · exact covered address (by simp [State.roots, old])
              · subst address; exact Or.inr reached
              · exact covered address (by simp [State.roots, pending, Task.roots, old])

theorem run_preserved (heap : Heap Address Value) (roots : Roots Unit Address)
    (budget : Nat) (state : State Address Value) (covered : Covered heap roots state) :
    run (collect heap roots) budget state = run heap budget state := by
  induction budget generalizing state with
  | zero => rfl
  | succ budget ih =>
      rw [run, step_preserved heap roots state covered, ih _ (step_covered heap roots state covered)]
      rfl

theorem operation_boundary_exact (heap : Heap Address Value) (budget : Nat) (state : State Address Value) :
    run (collect heap state.registry) budget state = run heap budget state :=
  run_preserved heap state.registry budget state (self_covered heap state)

/-- The policy may collect at every operation, at none, or at any selected
operation. Neither nested sequencing nor an unfinished region blocks it. -/
noncomputable def runCollecting (policy : Nat → Bool) (heap : Heap Address Value) :
    Nat → State Address Value → State Address Value
  | 0, state => state
  | budget + 1, state =>
      let current := if policy budget then collect heap state.registry else heap
      runCollecting policy current budget (step current state)

theorem arbitrary_collection_schedule_exact (policy : Nat → Bool) (heap : Heap Address Value)
    (budget : Nat) (state : State Address Value) :
    runCollecting policy heap budget state = run heap budget state := by
  induction budget generalizing heap state with
  | zero => rfl
  | succ budget ih =>
      simp only [runCollecting]
      rw [ih]
      cases choice : policy budget with
      | false => rfl
      | true =>
          change run (collect heap state.registry) (budget + 1) state = _
          exact operation_boundary_exact heap _ state

theorem collected_pages_compose (policy : Nat → Bool) (heap : Heap Address Value)
    (first second : Nat) (state : State Address Value) :
    runCollecting policy heap (first + second) state =
      run heap second (runCollecting policy heap first state) := by
  rw [arbitrary_collection_schedule_exact, arbitrary_collection_schedule_exact, run_add]

/-- Complete future path observations from every handle in the continuation,
fallback inputs or returned values. This also observes identity and aliases. -/
def AgreesAt (before after : Heap Address Value) (state : State Address Value) : Prop :=
  ∀ address ∈ state.roots, ∀ path, walk after address path = walk before address path

theorem collect_agrees (heap : Heap Address Value) (state : State Address Value) :
    AgreesAt heap (collect heap state.registry) state := by
  intro address member path
  exact walk_preserved heap state.registry address path (self_covered heap state address member)

theorem step_agrees (before after : Heap Address Value) (state : State Address Value)
    (agree : AgreesAt before after state) : step after state = step before state := by
  cases pending : state.pending with
  | nil => simp [step, pending]
  | cons task rest =>
      cases task with
      | sequence => simp [step, pending]
      | read start path =>
          have needed : start ∈ state.roots := by simp [State.roots, pending, Task.roots]
          simp only [step, pending, agree start needed path]

theorem agrees_after_step (before after : Heap Address Value) (state : State Address Value)
    (agree : AgreesAt before after state) : AgreesAt before after (step before state) := by
  intro address member suffix
  cases pending : state.pending with
  | nil => exact agree address (by simpa [step, pending] using member) suffix
  | cons task rest =>
      cases task with
      | sequence first second =>
          apply agree address _ suffix
          simpa [step, pending, State.roots, Task.roots, List.mem_append, or_assoc] using member
      | read start path =>
          have head : start ∈ state.roots := by simp [State.roots, pending, Task.roots]
          cases observed : walk before start path with
          | none =>
              apply agree address _ suffix
              simp only [step, pending, State.roots, List.filterMap_append, observed,
                List.filterMap_cons, List.filterMap_nil, Option.map_none, List.append_nil,
                List.mem_append] at member
              simp only [State.roots, pending, Task.roots, List.flatMap_cons, List.mem_append,
                List.mem_cons, List.not_mem_nil, or_false]
              tauto
          | some result =>
              rcases result with ⟨endpoint, cell⟩
              simp only [step, pending, State.roots, List.filterMap_append, observed,
                List.filterMap_cons, List.filterMap_nil, Option.map_some, List.mem_append,
                List.mem_cons, List.not_mem_nil, or_false] at member
              rcases member with (old | old | equal) | old
              · exact agree address (by simp [State.roots, old]) suffix
              · exact agree address (by simp [State.roots, old]) suffix
              · subst address
                rw [← walk_append_of_success after path suffix ((agree start head path).trans observed),
                  agree start head (path ++ suffix), walk_append_of_success before path suffix observed]
              · exact agree address (by simp [State.roots, pending, Task.roots, old]) suffix

theorem run_agrees (before after : Heap Address Value) (budget : Nat) (state : State Address Value)
    (agree : AgreesAt before after state) :
    run after budget state = run before budget state ∧ AgreesAt before after (run before budget state) := by
  induction budget generalizing state with
  | zero => exact ⟨rfl, agree⟩
  | succ budget ih =>
      have rest := ih (step before state) (agrees_after_step before after state agree)
      exact ⟨by rw [run, step_agrees before after state agree]; exact rest.1, rest.2⟩

/-- Unlike the answer-only worker, this returns the actual post-collection
heap, which is used by the next page without resurrecting discarded cells. -/
noncomputable def runHeap (policy : Nat → Bool) (heap : Heap Address Value) :
    Nat → State Address Value → Heap Address Value × State Address Value
  | 0, state => (heap, state)
  | budget + 1, state =>
      let current := if policy budget then collect heap state.registry else heap
      runHeap policy current budget (step current state)

theorem heap_run_preserves_future (policy : Nat → Bool) (heap : Heap Address Value)
    (budget : Nat) (state : State Address Value) :
    (runHeap policy heap budget state).2 = run heap budget state ∧
      AgreesAt heap (runHeap policy heap budget state).1 (runHeap policy heap budget state).2 := by
  induction budget generalizing heap state with
  | zero => exact ⟨rfl, fun _ _ _ => rfl⟩
  | succ budget ih =>
      let current := if policy budget then collect heap state.registry else heap
      have agree : AgreesAt heap current state := by
        cases choice : policy budget
        · exact fun _ _ _ => by simp [current, choice]
        · simpa [current, choice] using collect_agrees heap state
      have stepSame := step_agrees heap current state agree
      have future := run_agrees heap current budget (step heap state)
        (agrees_after_step heap current state agree)
      have rest := ih current (step current state)
      change (runHeap policy current budget (step current state)).2 = _ ∧ _
      constructor
      · rw [rest.1, stepSame, future.1]
        rfl
      · intro address member path
        have sameState : (runHeap policy current budget (step current state)).2 =
            run heap budget (step heap state) := by rw [rest.1, stepSame, future.1]
        exact (rest.2 address member path).trans (future.2 address (sameState ▸ member) path)

theorem resumed_collected_heap_exact (firstPolicy secondPolicy : Nat → Bool)
    (heap : Heap Address Value) (first second : Nat) (state : State Address Value) :
    let page := runHeap firstPolicy heap first state
    (runHeap secondPolicy page.1 second page.2).2 = run heap (first + second) state := by
  have page := heap_run_preserves_future firstPolicy heap first state
  have later := heap_run_preserves_future secondPolicy (runHeap firstPolicy heap first state).1
    second (runHeap firstPolicy heap first state).2
  have stable := run_agrees heap (runHeap firstPolicy heap first state).1 second
    (runHeap firstPolicy heap first state).2 page.2
  dsimp only
  rw [later.1, stable.1, page.1, run_add]

end Mettapedia.Machines.RegionReadCollection
