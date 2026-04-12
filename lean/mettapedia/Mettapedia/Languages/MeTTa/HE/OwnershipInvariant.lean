-- LLM primer: Models the running-stack contract from CeTTa's 2026-04-06
-- contract cleanup. Three-way target safety: ownedResumeSafe (can defer),
-- borrowedUnsafe (heap but borrows stack data), stackLocal (directly stack).
-- Only ownedResumeSafe targets may be deferred onto a running stack.
-- This catches the eval_visit_append_outcome bug (heap ptr to stack OutcomeSet).

import Mettapedia.Languages.MeTTa.HE.ArgFrameMachine

/-!
# Target-Sensitive Ownership Invariant

Formalizes CeTTa's running-stack contract after the 2026-04-06 cleanup:
> If the stack is running, only truly owned-resume-safe continuations
> may be deferred. Targets that borrow stack-local state are refused
> even if they are themselves heap-allocated.

This catches three bug classes:
1. Stack-local struct deferred directly (Bugs A-G from prior analysis)
2. Heap object that borrows stack-local callback state (eval_visit_append_outcome bug)
3. Any target not classified as owned-resume-safe

## C Seam Mapping

| Lean | C (eval.c) |
|------|-----------|
| `TargetSafety.ownedResumeSafe` | targets passing `native_resume_stack_can_defer_target` |
| `TargetSafety.borrowedUnsafe` | `eval_visit_append_outcome` (heap ptr to stack OutcomeSet) |
| `TargetSafety.stackLocal` | `QueryEvalVisitorCtx` on C stack |
| `canDefer` | `native_resume_stack_can_defer_target(stack, target)` |
| `stackForTarget` | `native_resume_stack_for_target(stack, target)` |
| `DeferSafe` | the running-stack contract invariant |
-/

namespace Mettapedia.Languages.MeTTa.HE

/-! ## Target Safety Classification -/

/-- Three-way classification of continuation target safety.

    This models CeTTa's `native_resume_stack_can_defer_target`:
    - `ownedResumeSafe`: target owns all its state, safe to outlive creator
    - `borrowedUnsafe`: target is heap-allocated but borrows stack-local data
    - `stackLocal`: target itself is on the C stack -/
inductive TargetSafety where
  | ownedResumeSafe
  | borrowedUnsafe
  | stackLocal
  deriving DecidableEq, Repr

/-- Can this target be deferred onto a running stack? -/
def TargetSafety.canDefer : TargetSafety → Bool
  | .ownedResumeSafe => true
  | .borrowedUnsafe => false
  | .stackLocal => false

/-! ## Machine State -/

/-- A worklist entry: a continuation with its target safety classification. -/
structure WorkEntry where
  safety : TargetSafety
  deriving DecidableEq, Repr

/-- Abstract machine with call stack and worklist (NativeResumeStack). -/
structure DeferMachine where
  stack    : List WorkEntry
  worklist : List WorkEntry
  deriving Repr

namespace DeferMachine

def empty : DeferMachine := ⟨[], []⟩

def pushImmediate (m : DeferMachine) (s : TargetSafety) : DeferMachine :=
  { m with stack := ⟨s⟩ :: m.stack }

def popStack (m : DeferMachine) : DeferMachine :=
  { m with stack := m.stack.tail }

/-- Defer a target onto the worklist. The contract check is EXTERNAL —
    callers must verify `canDefer` before calling this. -/
def deferToWorklist (m : DeferMachine) (s : TargetSafety) : DeferMachine :=
  { m with worklist := ⟨s⟩ :: m.worklist }

def popWorklist (m : DeferMachine) : DeferMachine :=
  { m with worklist := m.worklist.tail }

/-- The target-filtered stack: returns `some m` only if the target is safe to defer.
    Models `native_resume_stack_for_target(stack, target)`. -/
def stackForTarget (m : DeferMachine) (s : TargetSafety) : Option DeferMachine :=
  if s.canDefer then some m else none

end DeferMachine

/-! ## The Strengthened Invariant -/

/-- The running-stack deferral invariant: every entry in the worklist
    has `ownedResumeSafe` target safety.

    This is STRONGER than the old "not stackLocal" check:
    it also rejects `borrowedUnsafe` targets (heap objects that
    borrow stack-local data). -/
def DeferSafe (m : DeferMachine) : Prop :=
  ∀ e, e ∈ m.worklist → e.safety = .ownedResumeSafe

/-! ## Preservation Theorems -/

theorem deferSafe_initial : DeferSafe DeferMachine.empty := by
  intro e h; simp [DeferMachine.empty] at h

theorem deferSafe_pushImmediate (m : DeferMachine) (s : TargetSafety)
    (h : DeferSafe m) : DeferSafe (m.pushImmediate s) := by
  intro e he; simp [DeferMachine.pushImmediate] at he; exact h e he

theorem deferSafe_popStack (m : DeferMachine)
    (h : DeferSafe m) : DeferSafe (m.popStack) := h

theorem deferSafe_deferOwned (m : DeferMachine)
    (h : DeferSafe m) : DeferSafe (m.deferToWorklist .ownedResumeSafe) := by
  intro e he
  simp [DeferMachine.deferToWorklist] at he
  cases he with
  | inl heq => rw [heq]
  | inr hmem => exact h e hmem

theorem deferSafe_popWorklist (m : DeferMachine)
    (h : DeferSafe m) : DeferSafe (m.popWorklist) := by
  intro e he
  simp [DeferMachine.popWorklist] at he
  exact h e (List.tail_subset _ he)

/-! ## Violation Witnesses -/

/-- Violation 1: deferring a stack-local target breaks the invariant. -/
theorem deferStackLocal_unsafe (m : DeferMachine) :
    ¬DeferSafe (m.deferToWorklist .stackLocal) := by
  intro hsafe
  have := hsafe ⟨.stackLocal⟩ (by simp [DeferMachine.deferToWorklist])
  simp at this

/-- Violation 2: deferring a borrowedUnsafe target ALSO breaks the invariant.

    This is the NEW bug class Codex found: `eval_visit_append_outcome` is
    heap-allocated but borrows a stack-local `OutcomeSet`. The old 2-way
    model (stackLocal vs heapOwned) would NOT catch this. The 3-way model does. -/
theorem deferBorrowedUnsafe_unsafe (m : DeferMachine) :
    ¬DeferSafe (m.deferToWorklist .borrowedUnsafe) := by
  intro hsafe
  have := hsafe ⟨.borrowedUnsafe⟩ (by simp [DeferMachine.deferToWorklist])
  simp at this

/-- The stackForTarget gate: if it returns `some`, deferral is safe.
    If the target is unsafe, it returns `none`, forcing the caller
    to fall back to a non-deferred path. -/
theorem stackForTarget_safe (m : DeferMachine) (s : TargetSafety)
    (h : DeferSafe m)
    (h_some : m.stackForTarget s = some m) :
    DeferSafe (m.deferToWorklist s) := by
  simp [DeferMachine.stackForTarget, TargetSafety.canDefer] at h_some
  split at h_some <;> simp at h_some
  -- s = .ownedResumeSafe
  exact deferSafe_deferOwned m h

theorem stackForTarget_none_borrowedUnsafe (m : DeferMachine) :
    m.stackForTarget .borrowedUnsafe = none := by
  simp [DeferMachine.stackForTarget, TargetSafety.canDefer]

theorem stackForTarget_none_stackLocal (m : DeferMachine) :
    m.stackForTarget .stackLocal = none := by
  simp [DeferMachine.stackForTarget, TargetSafety.canDefer]

/-! ## Safe Operations -/

inductive SafeOp where
  | pushImmediate (s : TargetSafety)
  | popStack
  | deferOwned  -- only ownedResumeSafe may be deferred
  | popWorklist

def SafeOp.apply (m : DeferMachine) : SafeOp → DeferMachine
  | .pushImmediate s => m.pushImmediate s
  | .popStack => m.popStack
  | .deferOwned => m.deferToWorklist .ownedResumeSafe
  | .popWorklist => m.popWorklist

theorem safeOp_preserves (m : DeferMachine) (op : SafeOp)
    (h : DeferSafe m) : DeferSafe (op.apply m) := by
  cases op with
  | pushImmediate s => exact deferSafe_pushImmediate m s h
  | popStack => exact deferSafe_popStack m h
  | deferOwned => exact deferSafe_deferOwned m h
  | popWorklist => exact deferSafe_popWorklist m h

theorem safeOps_preserves (m : DeferMachine) (ops : List SafeOp)
    (h : DeferSafe m) :
    DeferSafe (ops.foldl SafeOp.apply m) := by
  induction ops generalizing m with
  | nil => exact h
  | cons op rest ih => exact ih _ (safeOp_preserves m op h)

/-! ## Examples -/

/-- Safe sequence: push borrowed (immediate only), defer owned, pop. -/
example : DeferSafe
    ([.pushImmediate .borrowedUnsafe, .deferOwned, .popWorklist].foldl
      SafeOp.apply DeferMachine.empty) :=
  safeOps_preserves _ _ deferSafe_initial

/-- The gate refuses borrowedUnsafe. -/
example : DeferMachine.empty.stackForTarget .borrowedUnsafe = none :=
  stackForTarget_none_borrowedUnsafe _

/-- The gate refuses stackLocal. -/
example : DeferMachine.empty.stackForTarget .stackLocal = none :=
  stackForTarget_none_stackLocal _

/-- The gate accepts ownedResumeSafe. -/
example : DeferMachine.empty.stackForTarget .ownedResumeSafe = some DeferMachine.empty := rfl

end Mettapedia.Languages.MeTTa.HE
