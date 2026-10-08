import Mettapedia.GSLT.Logic.DisjointConcurrency

/-!
# One lock with a resource invariant

Concurrent separation logic with one lock (O'Hearn, "Resources, concurrency,
and local reasoning", TCS 375, 2007; Brookes, "A semantics for concurrent
separation logic", TCS 375, 2007).  The lock owns a resource described by an
invariant `I`.  Acquiring the lock moves that resource into the acquiring
thread; releasing it moves a resource satisfying `I` back.  Between acquire and
release the thread may break `I`, because no other thread can see the
resource.

**Programs.**  The primitives of a base signature, plus `acquire` and
`release` (`LockOp`).  `withLock c` is a critical section around a base
program `c`.

**Semantics.**  Two threads interleave on one state and one lock
(`LockStep`).  `acquire` waits while the lock is held.  Releasing a lock one
does not hold, and acquiring a lock one already holds, are faults: both are
undefined for a default POSIX mutex.

**Thread-local safety** (`LSafe`, after Vafeiadis, "Concurrent Separation
Logic and Operational Semantics", MFPS 2011): a program is safe from a local
state when its base primitives are defined there and stay safe after every
outcome, `acquire` stays safe after adding any separate resource satisfying
`I`, and `release` can split off a resource satisfying `I`.

**Soundness** (`lock_par`): two threads that are each safe from their own
part run in parallel, beside a free lock holding `I`, without fault, and every
complete interleaving ends in `Q₁ ∗ Q₂ ∗ I`.  In every reachable configuration
the state splits into the parts of the two threads and, when the lock is free,
the lock's part (`lockGood_of_reaches`): every primitive a thread runs is
defined on its own part.  That is data-race freedom, which C11 and POSIX turn
into sequential consistency for the real program.

**The critical-region rule** (`lsafe_withLock`): a base program that turns
`P ∗ I` into `Q ∗ I` sequentially is safe as a critical section from `P`.

## Examples

`CMemory.Concurrency` instantiates this with C memory: a counter shared
through the lock (positive) and the lost update of unsynchronized increments
(negative).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Logic.AbstractSeparationLogic

open Mettapedia.GSLT.SeparationAlgebra
open scoped Mettapedia.GSLT.SeparationAlgebra

universe u v s

/-- The primitives of a base signature, plus the lock. -/
inductive LockOp (Op : Type u) where
  | base (o : Op)
  | acquire
  | release

/-- Result types: the base primitive's, or nothing. -/
def LockOp.Ret {Op : Type u} (Ret : Op → Type v) : LockOp Op → Type v
  | .base o => Ret o
  | .acquire => PUnit
  | .release => PUnit

/-- Programs that may use the lock. -/
abbrev LProg (Op : Type u) (Ret : Op → Type v) (α : Type v) :=
  Prog (LockOp Op) (LockOp.Ret Ret) α

namespace LProg

variable {Op : Type u} {Ret : Op → Type v} {α : Type v}

/-- A base program, run without touching the lock. -/
def lift : Prog Op Ret α → LProg Op Ret α
  | .ret a => .ret a
  | .call o k => .call (.base o) fun r => lift (k r)

/-- **A critical section**: acquire, run the base program, release. -/
def withLock (c : Prog Op Ret α) : LProg Op Ret α :=
  .call .acquire fun _ => (lift c).bind fun a => .call .release fun _ => .ret a

end LProg

/-- The lock: free, or held by the first or the second thread. -/
inductive LockState where
  | free
  | first
  | second
  deriving DecidableEq

variable {S : Type s} {Op : Type u} {Ret : Op → Type v} {α β : Type v}
variable (act : (o : Op) → Action S (Ret o))

/-- **One interleaved step with the lock.** -/
inductive LockStep :
    LProg Op Ret α → LProg Op Ret β → LockState → S →
      LProg Op Ret α → LProg Op Ret β → LockState → S → Prop
  | leftBase {o : Op} {k : Ret o → LProg Op Ret α} {c₂ : LProg Op Ret β} {l : LockState}
      {σ σ' : S} {r : Ret o} :
      (act o).Step σ r σ' → LockStep (.call (.base o) k) c₂ l σ (k r) c₂ l σ'
  | rightBase {c₁ : LProg Op Ret α} {o : Op} {k : Ret o → LProg Op Ret β} {l : LockState}
      {σ σ' : S} {r : Ret o} :
      (act o).Step σ r σ' → LockStep c₁ (.call (.base o) k) l σ c₁ (k r) l σ'
  | leftAcquire {k : PUnit → LProg Op Ret α} {c₂ : LProg Op Ret β} {σ : S} :
      LockStep (.call .acquire k) c₂ .free σ (k ⟨⟩) c₂ .first σ
  | rightAcquire {c₁ : LProg Op Ret α} {k : PUnit → LProg Op Ret β} {σ : S} :
      LockStep c₁ (.call .acquire k) .free σ c₁ (k ⟨⟩) .second σ
  | leftRelease {k : PUnit → LProg Op Ret α} {c₂ : LProg Op Ret β} {σ : S} :
      LockStep (.call .release k) c₂ .first σ (k ⟨⟩) c₂ .free σ
  | rightRelease {c₁ : LProg Op Ret α} {k : PUnit → LProg Op Ret β} {σ : S} :
      LockStep c₁ (.call .release k) .second σ c₁ (k ⟨⟩) .free σ

/-- Some interleaving faults: an undefined base primitive, a release of a lock
the thread does not hold, or an acquire of a lock it already holds. -/
inductive LockFaults : LProg Op Ret α → LProg Op Ret β → LockState → S → Prop
  | leftBase {o : Op} {k : Ret o → LProg Op Ret α} {c₂ : LProg Op Ret β} {l : LockState}
      {σ : S} : ¬ (act o).Safe σ → LockFaults (.call (.base o) k) c₂ l σ
  | rightBase {c₁ : LProg Op Ret α} {o : Op} {k : Ret o → LProg Op Ret β} {l : LockState}
      {σ : S} : ¬ (act o).Safe σ → LockFaults c₁ (.call (.base o) k) l σ
  | leftRelease {k : PUnit → LProg Op Ret α} {c₂ : LProg Op Ret β} {l : LockState} {σ : S} :
      l ≠ .first → LockFaults (.call .release k) c₂ l σ
  | rightRelease {c₁ : LProg Op Ret α} {k : PUnit → LProg Op Ret β} {l : LockState} {σ : S} :
      l ≠ .second → LockFaults c₁ (.call .release k) l σ
  | leftReacquire {k : PUnit → LProg Op Ret α} {c₂ : LProg Op Ret β} {σ : S} :
      LockFaults (.call .acquire k) c₂ .first σ
  | rightReacquire {c₁ : LProg Op Ret α} {k : PUnit → LProg Op Ret β} {σ : S} :
      LockFaults c₁ (.call .acquire k) .second σ
  | step {c₁ c₁' : LProg Op Ret α} {c₂ c₂' : LProg Op Ret β} {l l' : LockState} {σ σ' : S} :
      LockStep act c₁ c₂ l σ c₁' c₂' l' σ' → LockFaults c₁' c₂' l' σ' → LockFaults c₁ c₂ l σ

/-- A complete interleaving: both threads return. -/
inductive LockRuns : LProg Op Ret α → LProg Op Ret β → LockState → S → α → β → S → Prop
  | done {a : α} {b : β} {l : LockState} {σ : S} : LockRuns (.ret a) (.ret b) l σ a b σ
  | step {c₁ c₁' : LProg Op Ret α} {c₂ c₂' : LProg Op Ret β} {l l' : LockState}
      {σ σ' σ'' : S} {a : α} {b : β} :
      LockStep act c₁ c₂ l σ c₁' c₂' l' σ' → LockRuns c₁' c₂' l' σ' a b σ'' →
        LockRuns c₁ c₂ l σ a b σ''

/-- The configurations some interleaving reaches. -/
inductive LockReaches : LProg Op Ret α → LProg Op Ret β → LockState → S →
    LProg Op Ret α → LProg Op Ret β → LockState → S → Prop
  | refl {c₁ : LProg Op Ret α} {c₂ : LProg Op Ret β} {l : LockState} {σ : S} :
      LockReaches c₁ c₂ l σ c₁ c₂ l σ
  | step {c₁ c₁' c₁'' : LProg Op Ret α} {c₂ c₂' c₂'' : LProg Op Ret β}
      {l l' l'' : LockState} {σ σ' σ'' : S} :
      LockStep act c₁ c₂ l σ c₁' c₂' l' σ' → LockReaches c₁' c₂' l' σ' c₁'' c₂'' l'' σ'' →
        LockReaches c₁ c₂ l σ c₁'' c₂'' l'' σ''

variable [Zero S] [Add S] [SepAlgebra S]

/-- **Thread-local safety** with lock invariant `I`, for a thread that holds
the lock (`held`) or not.  A thread returns only after releasing the lock. -/
def LSafe (I : S → Prop) (Q : α → S → Prop) : LProg Op Ret α → Bool → S → Prop
  | .ret a, held, σ => held = false ∧ Q a σ
  | .call (.base o) k, held, σ =>
      (act o).Safe σ ∧ ∀ r σ', (act o).Step σ r σ' → LSafe I Q (k r) held σ'
  | .call .acquire k, held, σ =>
      held = false ∧ ∀ τ, I τ → σ ## τ → LSafe I Q (k ⟨⟩) true (σ + τ)
  | .call .release k, held, σ =>
      held = true ∧ ∃ σ₁ τ, σ₁ ## τ ∧ σ = σ₁ + τ ∧ I τ ∧ LSafe I Q (k ⟨⟩) false σ₁

/-- **The invariant of a configuration**: when the lock is free, the state
splits into the two threads' parts and the lock's part satisfying `I`; when a
thread holds the lock, the lock's part belongs to that thread. -/
def LockGood (I : S → Prop) (Q₁ : α → S → Prop) (Q₂ : β → S → Prop)
    (c₁ : LProg Op Ret α) (c₂ : LProg Op Ret β) : LockState → S → Prop
  | .free => LSafe act I Q₁ c₁ false ∗ (LSafe act I Q₂ c₂ false ∗ I)
  | .first => LSafe act I Q₁ c₁ true ∗ LSafe act I Q₂ c₂ false
  | .second => LSafe act I Q₁ c₁ false ∗ LSafe act I Q₂ c₂ true

section Soundness

variable {act}
variable (isLocal : ∀ o, (act o).Local)
include isLocal

variable {I : S → Prop}

/-- A base step of the thread on the left of a separating conjunction stays in
the thread's part. -/
theorem lsafe_base_step {γ : Type v} {Q : γ → S → Prop} {o : Op} {k : Ret o → LProg Op Ret γ}
    {held : Bool} {R : S → Prop} {σ σ' : S} {r : Ret o}
    (holds : (LSafe act I Q (.call (.base o) k) held ∗ R) σ) (step : (act o).Step σ r σ') :
    (LSafe act I Q (k r) held ∗ R) σ' := by
  obtain ⟨σ₁, ρ, separate, rfl, ⟨safe, next⟩, framed⟩ := holds
  obtain ⟨σ₁', separate', rfl, step'⟩ := (isLocal o).step_frame safe separate step
  exact ⟨σ₁', ρ, separate', rfl, next r σ₁' step', framed⟩

/-- A base primitive the thread on the left runs is defined on the whole
state. -/
theorem lsafe_base_safe {γ : Type v} {Q : γ → S → Prop} {o : Op} {k : Ret o → LProg Op Ret γ}
    {held : Bool} {R : S → Prop} {σ : S}
    (holds : (LSafe act I Q (.call (.base o) k) held ∗ R) σ) : (act o).Safe σ := by
  obtain ⟨σ₁, ρ, separate, rfl, ⟨safe, -⟩, -⟩ := holds
  exact (isLocal o).safe_frame safe separate

omit isLocal in
theorem lsafe_acquire {γ : Type v} {Q : γ → S → Prop} {k : PUnit → LProg Op Ret γ} :
    (LSafe act I Q (.call .acquire k) false ∗ I) ≤ LSafe act I Q (k ⟨⟩) true := by
  rintro _ ⟨σ₁, τ, separate, rfl, ⟨-, after⟩, invariant⟩
  exact after τ invariant separate

omit isLocal in
theorem lsafe_release {γ : Type v} {Q : γ → S → Prop} {k : PUnit → LProg Op Ret γ} :
    LSafe act I Q (.call .release k) true ≤ (LSafe act I Q (k ⟨⟩) false ∗ I) := by
  rintro σ ⟨-, σ₁, τ, separate, rfl, invariant, rest⟩
  exact ⟨σ₁, τ, separate, rfl, rest, invariant⟩

/-- **Every interleaved step keeps the configuration invariant.** -/
theorem lockGood_step {Q₁ : α → S → Prop} {Q₂ : β → S → Prop} {c₁ c₁' : LProg Op Ret α}
    {c₂ c₂' : LProg Op Ret β} {l l' : LockState} {σ σ' : S}
    (good : LockGood act I Q₁ Q₂ c₁ c₂ l σ) (step : LockStep act c₁ c₂ l σ c₁' c₂' l' σ') :
    LockGood act I Q₁ Q₂ c₁' c₂' l' σ' := by
  cases step with
  | leftBase step =>
    cases l with
    | free => exact lsafe_base_step isLocal good step
    | first => exact lsafe_base_step isLocal good step
    | second => exact lsafe_base_step isLocal good step
  | rightBase step =>
    cases l with
    | free =>
      change (_ ∗ (_ ∗ I)) σ at good
      change (_ ∗ (_ ∗ I)) σ'
      rw [sepConj_left_comm] at good ⊢
      exact lsafe_base_step isLocal good step
    | first =>
      change (_ ∗ _) σ at good
      change (_ ∗ _) σ'
      rw [sepConj_comm] at good ⊢
      exact lsafe_base_step isLocal good step
    | second =>
      change (_ ∗ _) σ at good
      change (_ ∗ _) σ'
      rw [sepConj_comm] at good ⊢
      exact lsafe_base_step isLocal good step
  | leftAcquire =>
    change (_ ∗ (_ ∗ I)) σ at good
    change (_ ∗ _) σ
    rw [sepConj_comm _ I, ← sepConj_assoc] at good
    exact sepConj_mono lsafe_acquire le_rfl σ good
  | rightAcquire =>
    change (_ ∗ (_ ∗ I)) σ at good
    change (_ ∗ _) σ
    exact sepConj_mono le_rfl lsafe_acquire σ good
  | leftRelease =>
    change (_ ∗ _) σ at good
    change (_ ∗ (_ ∗ I)) σ
    have moved := sepConj_mono lsafe_release le_rfl σ good
    rw [sepConj_assoc, sepConj_comm I] at moved
    exact moved
  | rightRelease =>
    change (_ ∗ _) σ at good
    change (_ ∗ (_ ∗ I)) σ
    exact sepConj_mono le_rfl lsafe_release σ good

/-- **Every reachable configuration keeps the invariant**: the state always
splits into the threads' parts and, when the lock is free, the lock's part. -/
theorem lockGood_of_reaches {Q₁ : α → S → Prop} {Q₂ : β → S → Prop}
    {c₁ c₁' : LProg Op Ret α} {c₂ c₂' : LProg Op Ret β} {l l' : LockState} {σ σ' : S}
    (good : LockGood act I Q₁ Q₂ c₁ c₂ l σ)
    (reaches : LockReaches act c₁ c₂ l σ c₁' c₂' l' σ') :
    LockGood act I Q₁ Q₂ c₁' c₂' l' σ' := by
  induction reaches with
  | refl => exact good
  | step step _ ih => exact ih (lockGood_step isLocal good step)

/-- A configuration satisfying the invariant does not fault. -/
theorem lockGood_not_faults {Q₁ : α → S → Prop} {Q₂ : β → S → Prop}
    {c₁ : LProg Op Ret α} {c₂ : LProg Op Ret β} {l : LockState} {σ : S}
    (good : LockGood act I Q₁ Q₂ c₁ c₂ l σ) : ¬ LockFaults act c₁ c₂ l σ := by
  intro faults
  induction faults with
  | @leftBase o k c₂ l σ undefined =>
    cases l with
    | free => exact undefined (lsafe_base_safe isLocal good)
    | first => exact undefined (lsafe_base_safe isLocal good)
    | second => exact undefined (lsafe_base_safe isLocal good)
  | @rightBase c₁ o k l σ undefined =>
    cases l with
    | free =>
      change (_ ∗ (_ ∗ I)) _ at good
      rw [sepConj_left_comm] at good
      exact undefined (lsafe_base_safe isLocal good)
    | first =>
      change (_ ∗ _) _ at good
      rw [sepConj_comm] at good
      exact undefined (lsafe_base_safe isLocal good)
    | second =>
      change (_ ∗ _) _ at good
      rw [sepConj_comm] at good
      exact undefined (lsafe_base_safe isLocal good)
  | @leftRelease k c₂ l σ notHeld =>
    cases l with
    | free =>
      have held := fact_of_sepConj_left good fun _ safe => safe.1
      cases held
    | first => exact notHeld rfl
    | second =>
      have held := fact_of_sepConj_left good fun _ safe => safe.1
      cases held
  | @rightRelease c₁ k l σ notHeld =>
    cases l with
    | free =>
      have held := fact_of_sepConj_right good fun _ rest =>
        fact_of_sepConj_left rest fun _ safe => safe.1
      cases held
    | first =>
      have held := fact_of_sepConj_right good fun _ safe => safe.1
      cases held
    | second => exact notHeld rfl
  | leftReacquire =>
    have held := fact_of_sepConj_left good fun _ safe => safe.1
    cases held
  | rightReacquire =>
    have held := fact_of_sepConj_right good fun _ safe => safe.1
    cases held
  | step step _ ih => exact ih (lockGood_step isLocal good step)

/-- A complete interleaving from the invariant ends in the two postconditions
beside the lock invariant. -/
theorem lockGood_runs {Q₁ : α → S → Prop} {Q₂ : β → S → Prop}
    {c₁ : LProg Op Ret α} {c₂ : LProg Op Ret β} {l : LockState} {σ σ' : S} {a : α} {b : β}
    (good : LockGood act I Q₁ Q₂ c₁ c₂ l σ) (runs : LockRuns act c₁ c₂ l σ a b σ') :
    (Q₁ a ∗ (Q₂ b ∗ I)) σ' := by
  induction runs with
  | @done a b l σ =>
    cases l with
    | free =>
      exact sepConj_mono (fun _ safe => safe.2) (sepConj_mono (fun _ safe => safe.2) le_rfl) _
        good
    | first =>
      have held := fact_of_sepConj_left good fun _ safe => safe.1
      cases held
    | second =>
      have held := fact_of_sepConj_right good fun _ safe => safe.1
      cases held
  | step step _ ih => exact ih (lockGood_step isLocal good step)

/-- **Soundness of the lock rule for two threads.**  Each thread is safe from
its own part; beside a free lock that holds `I`, no interleaving faults and
every complete interleaving ends in `Q₁ ∗ Q₂ ∗ I`. -/
theorem lock_par {P₁ P₂ : S → Prop} {c₁ : LProg Op Ret α} {c₂ : LProg Op Ret β}
    {Q₁ : α → S → Prop} {Q₂ : β → S → Prop}
    (safe₁ : P₁ ≤ LSafe act I Q₁ c₁ false) (safe₂ : P₂ ≤ LSafe act I Q₂ c₂ false) :
    ∀ σ, (P₁ ∗ (P₂ ∗ I)) σ → ¬ LockFaults act c₁ c₂ .free σ ∧
      ∀ a b σ', LockRuns act c₁ c₂ .free σ a b σ' → (Q₁ a ∗ (Q₂ b ∗ I)) σ' := by
  intro σ holds
  have good : LockGood act I Q₁ Q₂ c₁ c₂ .free σ :=
    sepConj_mono safe₁ (sepConj_mono safe₂ le_rfl) σ holds
  exact ⟨lockGood_not_faults isLocal good, fun a b σ' runs => lockGood_runs isLocal good runs⟩

end Soundness

/-! ## Rules for thread-local safety -/

section Rules

variable {act}
variable {I : S → Prop}

/-- A base program, run without the lock, followed by a continuation. -/
theorem lsafe_lift_bind {γ δ : Type v} {Q : δ → S → Prop} (c : Prog Op Ret γ)
    (f : γ → LProg Op Ret δ) {held : Bool} {σ : S} {R : γ → S → Prop}
    (meets : Meets act c σ R) (after : ∀ a σ', R a σ' → LSafe act I Q (f a) held σ') :
    LSafe act I Q ((LProg.lift c).bind f) held σ := by
  induction c generalizing σ with
  | ret a => exact after a σ (meets.2 a σ ⟨rfl, rfl⟩)
  | call o k ih =>
    obtain ⟨⟨safe, next⟩, post⟩ := meets
    exact ⟨safe, fun r σ' step =>
      ih r ⟨next r σ' step, fun a τ runs => post a τ ⟨r, σ', step, runs⟩⟩⟩

/-- **Lock-free code**: a base program meeting a specification is safe without
the lock. -/
theorem lsafe_lift {P : S → Prop} {c : Prog Op Ret α} {Q : α → S → Prop}
    (spec : Triple act P c Q) : P ≤ LSafe act I Q (LProg.lift c) false := by
  intro σ holds
  have safe := lsafe_lift_bind (I := I) (Q := Q) c Prog.ret (held := false) (spec σ holds)
    fun a σ' post => ⟨rfl, post⟩
  rwa [Prog.bind_ret] at safe

/-- **The critical-region rule**: a base program that turns `P ∗ I` into
`Q ∗ I` is safe from `P` as a critical section. -/
theorem lsafe_withLock {P : S → Prop} {c : Prog Op Ret α} {Q : α → S → Prop}
    (spec : Triple act (P ∗ I) c (fun a => Q a ∗ I)) :
    P ≤ LSafe act I Q (LProg.withLock c) false := by
  intro σ holds
  refine ⟨rfl, fun τ invariant separate => ?_⟩
  refine lsafe_lift_bind c _ (spec (σ + τ) ⟨σ, τ, separate, rfl, holds, invariant⟩) ?_
  rintro a σ' ⟨σ₁, τ', separate', rfl, post, invariant'⟩
  exact ⟨rfl, σ₁, τ', separate', rfl, invariant', rfl, post⟩

/-- **Sequencing**: a program safe up to `R`, followed by continuations safe
from `R`. -/
theorem lsafe_bind {γ δ : Type v} {R : γ → S → Prop} {Q : δ → S → Prop}
    (c : LProg Op Ret γ) (f : γ → LProg Op Ret δ) {held : Bool} {σ : S}
    (first : LSafe act I R c held σ) (after : ∀ a σ', R a σ' → LSafe act I Q (f a) false σ') :
    LSafe act I Q (c.bind f) held σ := by
  induction c generalizing held σ with
  | ret a =>
    obtain ⟨rfl, post⟩ := first
    exact after a σ post
  | call op k ih =>
    cases op with
    | base o =>
      obtain ⟨safe, next⟩ := first
      exact ⟨safe, fun r σ' step => ih r (next r σ' step)⟩
    | acquire =>
      obtain ⟨unheld, next⟩ := first
      exact ⟨unheld, fun τ invariant separate => ih ⟨⟩ (next τ invariant separate)⟩
    | release =>
      obtain ⟨isHeld, σ₁, τ, separate, rfl, invariant, rest⟩ := first
      exact ⟨isHeld, σ₁, τ, separate, rfl, invariant, ih ⟨⟩ rest⟩

end Rules

end Mettapedia.GSLT.Logic.AbstractSeparationLogic
