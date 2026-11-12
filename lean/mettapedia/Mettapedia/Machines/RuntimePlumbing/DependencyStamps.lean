import Mettapedia.Machines.ReadOnlyQuery
import Mathlib.Tactic

/-!
# Dependency-local stamps for pure adaptive observers

Stamps license reuse only when unchanged stamps imply unchanged complete cell
observations. Successful writes advance the edited stamp even when the payload
is restored. Reads of absence are dependencies too. Logical owner and query
identity are checked separately; address reuse is not owner identity.

The write model proves the stamp obligation constructively for arbitrary finite
write schedules. A native adapter must establish the same obligation for its
chosen declaration, subtype, frame and import regions. No stamp storage layout,
per-operation allocation or runtime wrapper is prescribed.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.RuntimePlumbing.DependencyStamps

open ReadOnlyQuery

variable {Key Value Answer : Type}

structure Memory (Key Value : Type) where
  value : Key → Value
  stamp : Key → Nat

/-- Monotone versions, with no equal-version change hidden by a rollback. -/
def Advances (before after : Memory Key Value) : Prop :=
  ∀ key, before.stamp key ≤ after.stamp key ∧
    (before.stamp key = after.stamp key → before.value key = after.value key)

theorem advances_refl (memory : Memory Key Value) : Advances memory memory := by
  intro key
  exact ⟨le_rfl, fun _ => rfl⟩

theorem advances_trans {first middle last : Memory Key Value}
    (left : Advances first middle) (right : Advances middle last) : Advances first last := by
  intro key
  refine ⟨(left key).1.trans (right key).1, fun same => ?_⟩
  have firstMiddle : first.stamp key = middle.stamp key := by
    have := (left key).1
    have := (right key).1
    omega
  have middleLast : middle.stamp key = last.stamp key := firstMiddle.symm.trans same
  exact ((left key).2 firstMiddle).trans ((right key).2 middleLast)

def write [DecidableEq Key] (memory : Memory Key Value) (key : Key) (value : Value) :
    Memory Key Value :=
  ⟨Function.update memory.value key value,
    Function.update memory.stamp key (memory.stamp key + 1)⟩

theorem write_advances [DecidableEq Key] (memory : Memory Key Value) (key : Key) (value : Value) :
    Advances memory (write memory key value) := by
  intro other
  by_cases same : other = key
  · subst other
    simp [write]
  · simp [write, Function.update_of_ne same]

def writes [DecidableEq Key] (memory : Memory Key Value) (schedule : List (Key × Value)) :
    Memory Key Value := schedule.foldl (fun state edit => write state edit.1 edit.2) memory

theorem writes_advance [DecidableEq Key] (memory : Memory Key Value)
    (schedule : List (Key × Value)) : Advances memory (writes memory schedule) := by
  induction schedule generalizing memory with
  | nil => exact advances_refl memory
  | cons edit rest ih =>
    exact advances_trans (write_advances memory edit.1 edit.2) (ih _)

/-- Captured versions follow the actual adaptive read path, including `none`. -/
def valid (before after : Memory Key Value) (reads : Reads Key Value) : Prop :=
  ∀ observed ∈ reads, before.stamp observed.1 = after.stamp observed.1

def check (before after : Memory Key Value) (reads : Reads Key Value) : Bool :=
  reads.all fun observed => decide (before.stamp observed.1 = after.stamp observed.1)

theorem check_iff (before after : Memory Key Value) (reads : Reads Key Value) :
    check before after reads = true ↔ valid before after reads := by
  simp [check, valid]

theorem valid_agrees (before after : Memory Key Value) (program : Program Key Value Answer)
    (sound : Advances before after) (current : valid before after (run before.value program).reads) :
    Agrees after.value (run before.value program).reads := by
  intro observed member
  exact ((sound observed.1).2 (current observed member)).symm.trans
    (run_agrees before.value program observed member)

/-- Validation needs only dependency stamps; it need not rerun the observer. -/
theorem checked_observation (before after : Memory Key Value) (program : Program Key Value Answer)
    (sound : Advances before after)
    (current : check before after (run before.value program).reads = true) :
    run after.value program = run before.value program :=
  run_eq_of_agrees _ _ program (valid_agrees before after program sound
    ((check_iff _ _ _).mp current))

theorem untouched_write_valid [DecidableEq Key] (memory : Memory Key Value)
    (reads : Reads Key Value) (key : Key) (value : Value)
    (untouched : ∀ observed ∈ reads, observed.1 ≠ key) :
    valid memory (write memory key value) reads := by
  intro observed member
  simp [write, Function.update_of_ne (untouched observed member)]

theorem unrelated_write_reuses [DecidableEq Key] (memory : Memory Key Value)
    (program : Program Key Value Answer) (key : Key) (value : Value)
    (untouched : ∀ observed ∈ (run memory.value program).reads, observed.1 ≠ key) :
    run (write memory key value).value program = run memory.value program :=
  run_eq_of_agrees _ _ program (valid_agrees _ _ program (write_advances _ _ _)
    (untouched_write_valid _ _ _ _ untouched))

namespace Controls

def empty : Memory Nat (Option Nat) := ⟨fun _ => none, fun _ => 0⟩

def lookup : Program Nat (Option Nat) (Option Nat) := .read 3 .pure

theorem unrelated_declaration_does_not_expire_absence :
    check empty (write empty 8 (some 17)) (run empty.value lookup).reads = true ∧
      (run (write empty 8 (some 17)).value lookup).answer = none := by decide

theorem adding_the_missing_declaration_expires_absence :
    check empty (write empty 3 (some 17)) (run empty.value lookup).reads = false ∧
      (run (write empty 3 (some 17)).value lookup).answer = some 17 := by decide

def bound : Memory Nat (Option Nat) := write empty 3 (some 10)
def rebound : Memory Nat (Option Nat) := write (write bound 3 none) 3 (some 20)

theorem rollback_and_rebind_reject_the_old_result :
    check bound rebound (run bound.value lookup).reads = false ∧
      (run bound.value lookup).answer = some 10 ∧
      (run rebound.value lookup).answer = some 20 := by decide

theorem restoring_payload_still_advances_the_stamp :
    (write (write bound 3 none) 3 (some 10)).value 3 = bound.value 3 ∧
      check bound (write (write bound 3 none) 3 (some 10))
        (run bound.value lookup).reads = false := by decide

/-- A version policy that resets on rollback violates the required law. -/
def broken : Memory Nat (Option Nat) := ⟨rebound.value, bound.stamp⟩

theorem equal_reset_versions_can_certify_a_wrong_answer :
    check bound broken (run bound.value lookup).reads = true ∧
      (run bound.value lookup).answer ≠ (run broken.value lookup).answer ∧
      ¬ Advances bound broken := by
  refine ⟨by decide, by decide, fun sound => ?_⟩
  have impossible := (sound 3).2 rfl
  change some 10 = some 20 at impossible
  contradiction

end Controls

end Mettapedia.Machines.RuntimePlumbing.DependencyStamps
