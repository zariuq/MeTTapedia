import Mettapedia.Machines.Kernel.EpochLedger
import Mathlib.Tactic

/-!
# Keyed memory transitions in the bounded epoch ledger

A permitted install publishes one exact live binding, reclaim retires one
binding, and cleanup retires a same-subject, same-key list atomically. Other
frames retain both live and retired state. Checked commits combine these
permission boundaries with the bounded, sealed epoch ledger.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Kernel.EpochMemory

open EpochLedger

structure Binding where
  frame : Nat
  subject : Nat
  token : Nat
  address : Nat
  rights : Nat
  key : Nat
  deriving DecidableEq, Repr

inductive Operation where
  | install (binding : Binding)
  | reclaim (binding : Binding)
  | cleanup (bindings : List Binding)
  deriving DecidableEq, Repr

structure Memory where
  live : Nat → Option Binding
  retired : Nat → Option Binding

def Permitted (state : Memory) (binding : Binding) : Prop :=
  state.live binding.frame = some binding ∧ state.retired binding.frame = none

def InstallPermitted (state : Memory) (binding : Binding) : Prop :=
  binding.key ≠ 0 ∧ state.live binding.frame = none

def CleanupPermitted (state : Memory) : List Binding → Prop
  | [] => True
  | first :: rest =>
      (first :: rest).Pairwise (fun left right => left.frame ≠ right.frame) ∧
      (first :: rest).Forall (fun binding =>
        state.live binding.frame = some binding ∧
        binding.subject = first.subject ∧ binding.key = first.key ∧ binding.key ≠ 0)

instance permittedDecidable (state : Memory) (binding : Binding) :
    Decidable (Permitted state binding) := by
  unfold Permitted
  infer_instance

instance installPermittedDecidable (state : Memory) (binding : Binding) :
    Decidable (InstallPermitted state binding) := by
  unfold InstallPermitted
  infer_instance

instance cleanupPermittedDecidable (state : Memory) (bindings : List Binding) :
    Decidable (CleanupPermitted state bindings) := by
  cases bindings with
  | nil => exact isTrue trivial
  | cons first rest =>
      unfold CleanupPermitted
      infer_instance

def reclaim (state : Memory) (binding : Binding) : Memory :=
  { live := Function.update state.live binding.frame none
    retired := Function.update state.retired binding.frame (some binding) }

def install (state : Memory) (binding : Binding) : Memory :=
  { state with live := Function.update state.live binding.frame (some binding) }

def cleanup : Memory → List Binding → Memory
  | state, [] => state
  | state, binding :: rest => cleanup (reclaim state binding) rest

def step (state : Memory) : Operation → Memory
  | .install binding => install state binding
  | .reclaim binding => reclaim state binding
  | .cleanup bindings => cleanup state bindings

def checkedCommit (maximum capacity : Nat)
    (ledger : Ledger Memory Operation) (binding : Binding) : Option (Ledger Memory Operation) :=
  if Permitted ledger.current binding then
    commit maximum capacity step ledger (.reclaim binding)
  else none

def checkedInstall (maximum capacity : Nat)
    (ledger : Ledger Memory Operation) (binding : Binding) : Option (Ledger Memory Operation) :=
  if InstallPermitted ledger.current binding then
    commit maximum capacity step ledger (.install binding)
  else none

def checkedCleanup (maximum capacity : Nat)
    (ledger : Ledger Memory Operation) (bindings : List Binding) : Option (Ledger Memory Operation) :=
  if CleanupPermitted ledger.current bindings then
    commit maximum capacity step ledger (.cleanup bindings)
  else none

theorem reclaim_consumes (state : Memory) (binding : Binding) :
    (reclaim state binding).live binding.frame = none := by
  simp [reclaim]

theorem reclaim_retires (state : Memory) (binding : Binding) :
    (reclaim state binding).retired binding.frame = some binding := by
  simp [reclaim]

theorem reclaim_preserves_other (state : Memory) (binding : Binding) {other : Nat}
    (different : other ≠ binding.frame) :
    (reclaim state binding).live other = state.live other ∧
      (reclaim state binding).retired other = state.retired other := by
  simp [reclaim, different]

theorem reclaim_preserves_other_holder (state : Memory) (binding held : Binding)
    (different : held.frame ≠ binding.frame)
    (present : state.live held.frame = some held) :
    (reclaim state binding).live held.frame = some held := by
  rw [(reclaim_preserves_other state binding different).1, present]

theorem install_places (state : Memory) (binding : Binding) :
    (install state binding).live binding.frame = some binding := by
  simp [install]

theorem install_retains_history (state : Memory) (binding : Binding) :
    (install state binding).retired binding.frame = state.retired binding.frame := by
  rfl

theorem install_preserves_other (state : Memory) (binding : Binding) {other : Nat}
    (different : other ≠ binding.frame) :
    (install state binding).live other = state.live other ∧
      (install state binding).retired other = state.retired other := by
  simp [install, different]

theorem cleanup_preserves_other (state : Memory) (bindings : List Binding) {other : Nat}
    (different : ∀ binding ∈ bindings, other ≠ binding.frame) :
    (cleanup state bindings).live other = state.live other ∧
      (cleanup state bindings).retired other = state.retired other := by
  induction bindings generalizing state with
  | nil => simp [cleanup]
  | cons binding rest ih =>
      have headDifferent : other ≠ binding.frame := different binding (by simp)
      have tailDifferent : ∀ item ∈ rest, other ≠ item.frame := by
        intro item member
        exact different item (by simp [member])
      rw [show cleanup state (binding :: rest) = cleanup (reclaim state binding) rest by rfl]
      rw [(ih (reclaim state binding) tailDifferent).1,
        (ih (reclaim state binding) tailDifferent).2]
      exact reclaim_preserves_other state binding headDifferent

theorem checkedCommit_permitted {maximum capacity : Nat}
    {ledger next : Ledger Memory Operation} {binding : Binding}
    (accepted : checkedCommit maximum capacity ledger binding = some next) :
    Permitted ledger.current binding := by
  unfold checkedCommit at accepted
  split at accepted
  · assumption
  · cases accepted

theorem checkedCommit_preserves_valid {maximum capacity : Nat}
    {ledger next : Ledger Memory Operation} {binding : Binding}
    (valid : Valid step ledger)
    (accepted : checkedCommit maximum capacity ledger binding = some next) :
    Valid step next := by
  unfold checkedCommit at accepted
  split at accepted
  · exact commit_preserves_valid step valid accepted
  · cases accepted

theorem checkedCommit_current {maximum capacity : Nat}
    {ledger next : Ledger Memory Operation} {binding : Binding}
    (accepted : checkedCommit maximum capacity ledger binding = some next) :
    next.current = reclaim ledger.current binding := by
  unfold checkedCommit at accepted
  split at accepted
  · unfold commit at accepted
    split at accepted
    · simp only [Option.some.injEq] at accepted
      subst next
      rfl
    · cases accepted
  · cases accepted

theorem checkedCommit_retires {maximum capacity : Nat}
    {ledger next : Ledger Memory Operation} {binding : Binding}
    (accepted : checkedCommit maximum capacity ledger binding = some next) :
    next.current.live binding.frame = none ∧
      next.current.retired binding.frame = some binding := by
  rw [checkedCommit_current accepted]
  exact ⟨reclaim_consumes _ _, reclaim_retires _ _⟩

theorem checkedCommit_preserves_other_frame {maximum capacity : Nat}
    {ledger next : Ledger Memory Operation} {binding : Binding} {other : Nat}
    (different : other ≠ binding.frame)
    (accepted : checkedCommit maximum capacity ledger binding = some next) :
    next.current.live other = ledger.current.live other ∧
      next.current.retired other = ledger.current.retired other := by
  rw [checkedCommit_current accepted]
  exact reclaim_preserves_other _ _ different

theorem checkedInstall_permitted {maximum capacity : Nat}
    {ledger next : Ledger Memory Operation} {binding : Binding}
    (accepted : checkedInstall maximum capacity ledger binding = some next) :
    InstallPermitted ledger.current binding := by
  unfold checkedInstall at accepted
  split at accepted
  · assumption
  · cases accepted

theorem checkedInstall_preserves_valid {maximum capacity : Nat}
    {ledger next : Ledger Memory Operation} {binding : Binding}
    (valid : Valid step ledger)
    (accepted : checkedInstall maximum capacity ledger binding = some next) :
    Valid step next := by
  unfold checkedInstall at accepted
  split at accepted
  · exact commit_preserves_valid step valid accepted
  · cases accepted

theorem checkedInstall_current {maximum capacity : Nat}
    {ledger next : Ledger Memory Operation} {binding : Binding}
    (accepted : checkedInstall maximum capacity ledger binding = some next) :
    next.current = install ledger.current binding := by
  unfold checkedInstall at accepted
  split at accepted
  · unfold commit at accepted
    split at accepted
    · simp only [Option.some.injEq] at accepted
      subst next
      rfl
    · cases accepted
  · cases accepted

theorem checkedInstall_places_exact_binding {maximum capacity : Nat}
    {ledger next : Ledger Memory Operation} {binding : Binding}
    (accepted : checkedInstall maximum capacity ledger binding = some next) :
    next.current.live binding.frame = some binding ∧
      next.current.retired binding.frame = ledger.current.retired binding.frame := by
  rw [checkedInstall_current accepted]
  exact ⟨install_places _ _, install_retains_history _ _⟩

theorem checkedInstall_preserves_other_frame {maximum capacity : Nat}
    {ledger next : Ledger Memory Operation} {binding : Binding} {other : Nat}
    (different : other ≠ binding.frame)
    (accepted : checkedInstall maximum capacity ledger binding = some next) :
    next.current.live other = ledger.current.live other ∧
      next.current.retired other = ledger.current.retired other := by
  rw [checkedInstall_current accepted]
  exact install_preserves_other _ _ different

theorem checkedCleanup_permitted {maximum capacity : Nat}
    {ledger next : Ledger Memory Operation} {bindings : List Binding}
    (accepted : checkedCleanup maximum capacity ledger bindings = some next) :
    CleanupPermitted ledger.current bindings := by
  unfold checkedCleanup at accepted
  split at accepted
  · assumption
  · cases accepted

theorem checkedCleanup_preserves_valid {maximum capacity : Nat}
    {ledger next : Ledger Memory Operation} {bindings : List Binding}
    (valid : Valid step ledger)
    (accepted : checkedCleanup maximum capacity ledger bindings = some next) :
    Valid step next := by
  unfold checkedCleanup at accepted
  split at accepted
  · exact commit_preserves_valid step valid accepted
  · cases accepted

theorem checkedCleanup_current {maximum capacity : Nat}
    {ledger next : Ledger Memory Operation} {bindings : List Binding}
    (accepted : checkedCleanup maximum capacity ledger bindings = some next) :
    next.current = cleanup ledger.current bindings := by
  unfold checkedCleanup at accepted
  split at accepted
  · unfold commit at accepted
    split at accepted
    · simp only [Option.some.injEq] at accepted
      subst next
      rfl
    · cases accepted
  · cases accepted

theorem checkedCleanup_preserves_other_frame {maximum capacity : Nat}
    {ledger next : Ledger Memory Operation} {bindings : List Binding} {other : Nat}
    (different : ∀ binding ∈ bindings, other ≠ binding.frame)
    (accepted : checkedCleanup maximum capacity ledger bindings = some next) :
    next.current.live other = ledger.current.live other ∧
      next.current.retired other = ledger.current.retired other := by
  rw [checkedCleanup_current accepted]
  exact cleanup_preserves_other _ _ different

namespace Controls

def retiring : Binding := ⟨2, 15, 33, 0x70002000, 6, 15⟩
def replacement : Binding := ⟨2, 10, 34, 0x70002000, 6, 10⟩
def unrelated : Binding := ⟨5, 10, 44, 0x70005000, 4, 10⟩
def observer : Binding := ⟨7, 3, 55, 0x70007000, 4, 3⟩

def initial : Memory :=
  { live := fun frame =>
      if frame = retiring.frame then some retiring
      else if frame = unrelated.frame then some unrelated
      else if frame = observer.frame then some observer
      else none
    retired := fun _ => none }

def start : Ledger Memory Operation :=
  ⟨initial, initial, 0, [], [], true⟩

def first : Ledger Memory Operation :=
  ⟨initial, reclaim initial retiring, 1, [.reclaim retiring],
    [⟨1, .reclaim retiring, initial, reclaim initial retiring⟩], true⟩

def second : Ledger Memory Operation :=
  ⟨initial, install (reclaim initial retiring) replacement, 2,
    [.reclaim retiring, .install replacement],
    [⟨1, .reclaim retiring, initial, reclaim initial retiring⟩,
     ⟨2, .install replacement, reclaim initial retiring,
       install (reclaim initial retiring) replacement⟩], true⟩

def closed : Ledger Memory Operation :=
  ⟨initial, cleanup (install (reclaim initial retiring) replacement) [replacement, unrelated], 3,
    [.reclaim retiring, .install replacement, .cleanup [replacement, unrelated]],
    [⟨1, .reclaim retiring, initial, reclaim initial retiring⟩,
     ⟨2, .install replacement, reclaim initial retiring,
       install (reclaim initial retiring) replacement⟩,
     ⟨3, .cleanup [replacement, unrelated], install (reclaim initial retiring) replacement,
       cleanup (install (reclaim initial retiring) replacement) [replacement, unrelated]⟩], true⟩

theorem start_valid : Valid step start := by
  simp [Valid, start, replay, traceFrom]

theorem retiring_is_permitted : Permitted initial retiring := by
  decide

theorem first_is_checked_commit : checkedCommit 10 8 start retiring = some first := by
  unfold checkedCommit
  change (if Permitted initial retiring then commit 10 8 step start (.reclaim retiring) else none) = some first
  rw [if_pos retiring_is_permitted]
  unfold commit
  rw [dif_pos (by decide)]
  rfl

theorem first_valid : Valid step first :=
  checkedCommit_preserves_valid start_valid first_is_checked_commit

theorem exact_binding_retired :
    first.current.live retiring.frame = none ∧
      first.current.retired retiring.frame = some retiring := by
  exact checkedCommit_retires first_is_checked_commit

theorem unrelated_binding_survives :
    first.current.live unrelated.frame = some unrelated ∧
      first.current.retired unrelated.frame = none := by
  have preserved := checkedCommit_preserves_other_frame
    (ledger := start) (next := first) (binding := retiring)
    (other := unrelated.frame) (by decide) first_is_checked_commit
  simpa [start, initial, unrelated, retiring] using preserved

theorem duplicate_reclaim_refused : checkedCommit 10 8 first retiring = none := by
  simp [checkedCommit, Permitted, first, reclaim, retiring]

theorem replacement_is_permitted : InstallPermitted first.current replacement := by
  decide

theorem second_is_checked_install : checkedInstall 10 8 first replacement = some second := by
  unfold checkedInstall
  rw [if_pos replacement_is_permitted]
  unfold commit
  rw [dif_pos (by decide)]
  rfl

theorem second_valid : Valid step second :=
  checkedInstall_preserves_valid first_valid second_is_checked_install

theorem replacement_is_exclusive_and_history_remains :
    second.current.live replacement.frame = some replacement ∧
      second.current.retired replacement.frame = some retiring := by
  have placed := checkedInstall_places_exact_binding second_is_checked_install
  simpa [first, reclaim, retiring, replacement] using placed

theorem unrelated_survives_reclaim_and_install :
    second.current.live unrelated.frame = some unrelated ∧
      second.current.retired unrelated.frame = none := by
  have preserved := checkedInstall_preserves_other_frame
    (ledger := first) (next := second) (binding := replacement)
    (other := unrelated.frame) (by decide) second_is_checked_install
  simpa [first, initial, reclaim, unrelated, retiring] using preserved

theorem keys_are_explicitly_distinct :
    retiring.key = 15 ∧ replacement.key = 10 ∧ retiring.key ≠ replacement.key := by
  decide

theorem duplicate_install_refused : checkedInstall 10 8 second replacement = none := by
  simp [checkedInstall, InstallPermitted, second, install, replacement]

theorem cleanup_is_permitted :
    CleanupPermitted second.current [replacement, unrelated] := by
  decide

theorem closed_is_checked_cleanup :
    checkedCleanup 10 8 second [replacement, unrelated] = some closed := by
  unfold checkedCleanup
  rw [if_pos cleanup_is_permitted]
  unfold commit
  rw [dif_pos (by decide)]
  rfl

theorem closed_valid : Valid step closed :=
  checkedCleanup_preserves_valid second_valid closed_is_checked_cleanup

theorem cleanup_removes_both_bindings :
    closed.current.live replacement.frame = none ∧
      closed.current.retired replacement.frame = some replacement ∧
      closed.current.live unrelated.frame = none ∧
      closed.current.retired unrelated.frame = some unrelated := by
  decide

theorem observer_survives_cleanup :
    closed.current.live observer.frame = some observer ∧
      closed.current.retired observer.frame = none := by
  have preserved := checkedCleanup_preserves_other_frame
    (ledger := second) (next := closed) (bindings := [replacement, unrelated])
    (other := observer.frame) (by decide) closed_is_checked_cleanup
  have liveBefore : second.current.live observer.frame = some observer := by rfl
  have retiredBefore : second.current.retired observer.frame = none := by rfl
  exact ⟨preserved.1.trans liveBefore, preserved.2.trans retiredBefore⟩

theorem mixed_authority_cleanup_refused :
    checkedCleanup 10 8 second [replacement, observer] = none := by
  decide

end Controls

#print axioms reclaim_preserves_other_holder
#print axioms checkedCommit_preserves_valid
#print axioms checkedCommit_retires
#print axioms checkedCommit_preserves_other_frame
#print axioms install_preserves_other
#print axioms checkedInstall_preserves_valid
#print axioms checkedInstall_places_exact_binding
#print axioms checkedInstall_preserves_other_frame
#print axioms cleanup_preserves_other
#print axioms checkedCleanup_preserves_valid
#print axioms checkedCleanup_preserves_other_frame
#print axioms Controls.start_valid
#print axioms Controls.retiring_is_permitted
#print axioms Controls.first_is_checked_commit
#print axioms Controls.first_valid
#print axioms Controls.exact_binding_retired
#print axioms Controls.unrelated_binding_survives
#print axioms Controls.duplicate_reclaim_refused
#print axioms Controls.second_is_checked_install
#print axioms Controls.second_valid
#print axioms Controls.replacement_is_exclusive_and_history_remains
#print axioms Controls.unrelated_survives_reclaim_and_install
#print axioms Controls.keys_are_explicitly_distinct
#print axioms Controls.duplicate_install_refused
#print axioms Controls.closed_is_checked_cleanup
#print axioms Controls.closed_valid
#print axioms Controls.cleanup_removes_both_bindings
#print axioms Controls.observer_survives_cleanup
#print axioms Controls.mixed_authority_cleanup_refused

end Mettapedia.Machines.Kernel.EpochMemory
