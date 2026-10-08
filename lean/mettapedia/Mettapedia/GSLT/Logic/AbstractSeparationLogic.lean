import Mettapedia.GSLT.Logic.SeparationAlgebra
import Mettapedia.GSLT.Dynamics.ResumptionAlgebra

/-!
# Abstract separation logic: local actions and the frame rule

A program is a tree of primitive calls: each node calls one primitive, and its
continuation receives the primitive's result.  Sequencing is substitution at
the leaves, so programs form a monad, and Lean's `do` notation, conditionals,
pattern matching and recursion build them.  Every program is a finite tree, so
every execution terminates.  Loops are bounded iterations (`foldList`).

The primitive tree is isomorphic to the existing free polynomial resumption
construction. The comparison retains dependent response continuations and
sequencing. Its direct stateful handler preserves both fault avoidance and
all permitted final states; equality of answers alone is insufficient.

The states form a separation algebra.  Each primitive has a meaning on states:
where it is defined (`Safe`), and which results and next states it may produce
(`Step`).  A primitive is a **local action** in the sense of Calcagno, O'Hearn
and Yang ("Local Action and Abstract Separation Logic", LICS 2007): when it is
defined on a state, it stays defined after a separate frame is added, and every
outcome on the larger state is an outcome on the smaller one with the frame
left untouched.

The main theorem, `denote_local`, says that every program built from local
primitives is itself a local action.  The frame rule (`triple_frame`) follows
once, for every program over every signature of local primitives:

  `{P} c {Q}`  implies  `{P ∗ F} c {Q ∗ F}`.

The Hoare triples are fault-avoiding: `{P} c {Q}` says that from any state
satisfying `P`, no execution of `c` reaches an undefined primitive, and every
execution ends in a state satisfying `Q`.  When every primitive also has an
outcome wherever it is defined (`Action.Progress`), a safe program has a
terminating execution (`exists_runs`), so the triples are not satisfied
vacuously.

Beside the program rules (return, sequencing, consequence, existentials,
disjunction, pure facts, a primitive's own specification, bounded iteration),
the module collects the rearrangement, quantifier and pure-fact laws of the
separating conjunction that program proofs need, and the iterated separating
conjunction `bigSep`, which does not depend on the order of its list
(`bigSep_perm`).  Two-thread concurrency builds on this module in
`DisjointConcurrency` and `LockInvariant`.

## Examples

* **Positive.**  Adding an atom to a bag is a local action; its triple framed
  by an unrelated atom keeps that atom (`Controls.add_framed`).
* **Negative.**  A probe that reports whether the whole state is empty is not
  local, and the frame rule fails for it: framed by a nonempty bag, its
  specification claims a result that no execution produces
  (`Controls.probe_frame_fails`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Logic.AbstractSeparationLogic

open Mettapedia.GSLT.SeparationAlgebra
open scoped Mettapedia.GSLT.SeparationAlgebra

universe u v s

/-- **Programs** over a signature of primitives `Op`, where `Ret o` is the type
of the result of primitive `o`: either a final result, or a call of one
primitive followed by a continuation that receives its result. -/
inductive Prog (Op : Type u) (Ret : Op → Type v) (α : Type v) : Type (max u v) where
  | ret (value : α)
  | call (op : Op) (next : Ret op → Prog Op Ret α)

namespace Prog

variable {Op : Type u} {Ret : Op → Type v} {α β γ : Type v}

/-- Sequencing: run `c`, then continue with its result. -/
def bind : Prog Op Ret α → (α → Prog Op Ret β) → Prog Op Ret β
  | ret a, f => f a
  | call o k, f => call o fun r => (k r).bind f

instance : Monad (Prog Op Ret) where
  pure := ret
  bind := bind

@[simp] theorem pure_eq (a : α) : (pure a : Prog Op Ret α) = ret a := rfl

@[simp] theorem bind_eq (c : Prog Op Ret α) (f : α → Prog Op Ret β) :
    c >>= f = c.bind f := rfl

@[simp] theorem ret_bind (a : α) (f : α → Prog Op Ret β) : (ret a).bind f = f a := rfl

@[simp] theorem call_bind (o : Op) (k : Ret o → Prog Op Ret α) (f : α → Prog Op Ret β) :
    (call o k).bind f = call o fun r => (k r).bind f := rfl

@[simp] theorem bind_ret (c : Prog Op Ret α) : c.bind ret = c := by
  induction c with
  | ret a => rfl
  | call o k ih => simp only [call_bind, ih]

theorem bind_assoc (c : Prog Op Ret α) (f : α → Prog Op Ret β) (g : β → Prog Op Ret γ) :
    (c.bind f).bind g = c.bind fun a => (f a).bind g := by
  induction c with
  | ret a => rfl
  | call o k ih => simp only [call_bind, ih]

instance : LawfulMonad (Prog Op Ret) := LawfulMonad.mk'
  (id_map := fun c => bind_ret c)
  (pure_bind := fun _ _ => rfl)
  (bind_assoc := bind_assoc)

/-- One call of a primitive, returning its result. -/
def prim (o : Op) : Prog Op Ret (Ret o) := call o ret

/-- Bounded iteration: `f` runs once for each element of the list, in order,
threading an accumulator.  A C loop over an index range is `foldList` over
`List.range`; an early exit is an accumulated flag that the remaining
iterations test. -/
def foldList (f : β → γ → Prog Op Ret β) : List γ → β → Prog Op Ret β
  | [], b => ret b
  | x :: xs, b => (f b x).bind (foldList f xs)

end Prog

/-- The meaning of one primitive on states `S`: where it is defined, and the
results and next states it may produce. -/
structure Action (S : Type s) (β : Type v) where
  /-- The primitive is defined in this state. -/
  Safe : S → Prop
  /-- One permitted outcome: a result and the next state. -/
  Step : S → β → S → Prop

/-- Wherever the primitive is defined, it has an outcome. -/
def Action.Progress {S : Type s} {β : Type v} (a : Action S β) : Prop :=
  ∀ σ, a.Safe σ → ∃ r σ', a.Step σ r σ'

namespace Prog

variable {Op : Type u} {Ret : Op → Type v} {α β γ : Type v} {S : Type s}
variable (act : (o : Op) → Action S (Ret o))

/-- No execution of the program reaches an undefined primitive. -/
def Safe : Prog Op Ret α → S → Prop
  | ret _, _ => True
  | call o k, σ => (act o).Safe σ ∧ ∀ r σ', (act o).Step σ r σ' → (k r).Safe σ'

/-- Some execution of the program ends with this result in this state. -/
def Runs : Prog Op Ret α → S → α → S → Prop
  | ret a, σ, b, σ' => a = b ∧ σ = σ'
  | call o k, σ, b, σ' => ∃ r σ₁, (act o).Step σ r σ₁ ∧ (k r).Runs σ₁ b σ'

/-- The meaning of a whole program, as an action. -/
def denote (c : Prog Op Ret α) : Action S α := ⟨c.Safe act, c.Runs act⟩

theorem safe_ret (a : α) (σ : S) : (ret a : Prog Op Ret α).Safe act σ := trivial

theorem safe_call (o : Op) (k : Ret o → Prog Op Ret α) (σ : S) :
    (call o k).Safe act σ ↔
      (act o).Safe σ ∧ ∀ r σ', (act o).Step σ r σ' → (k r).Safe act σ' := Iff.rfl

theorem runs_ret (a b : α) (σ σ' : S) :
    (ret a : Prog Op Ret α).Runs act σ b σ' ↔ a = b ∧ σ = σ' := Iff.rfl

theorem runs_call (o : Op) (k : Ret o → Prog Op Ret α) (σ : S) (b : α) (σ' : S) :
    (call o k).Runs act σ b σ' ↔ ∃ r σ₁, (act o).Step σ r σ₁ ∧ (k r).Runs act σ₁ b σ' :=
  Iff.rfl

theorem safe_bind (c : Prog Op Ret α) (f : α → Prog Op Ret β) (σ : S) :
    (c.bind f).Safe act σ ↔
      c.Safe act σ ∧ ∀ a σ', c.Runs act σ a σ' → (f a).Safe act σ' := by
  induction c generalizing σ with
  | ret a =>
    constructor
    · intro safe
      exact ⟨trivial, by rintro b σ' ⟨rfl, rfl⟩; exact safe⟩
    · rintro ⟨-, after⟩
      exact after a σ ⟨rfl, rfl⟩
  | call o k ih =>
    simp only [call_bind, safe_call, runs_call, ih]
    constructor
    · rintro ⟨safe, next⟩
      exact ⟨⟨safe, fun r σ₁ step => (next r σ₁ step).1⟩,
        fun a σ' ⟨r, σ₁, step, runs⟩ => (next r σ₁ step).2 a σ' runs⟩
    · rintro ⟨⟨safe, next⟩, after⟩
      exact ⟨safe, fun r σ₁ step =>
        ⟨next r σ₁ step, fun a σ' runs => after a σ' ⟨r, σ₁, step, runs⟩⟩⟩

theorem runs_bind (c : Prog Op Ret α) (f : α → Prog Op Ret β) (σ : S) (b : β) (σ'' : S) :
    (c.bind f).Runs act σ b σ'' ↔ ∃ a σ', c.Runs act σ a σ' ∧ (f a).Runs act σ' b σ'' := by
  induction c generalizing σ with
  | ret a =>
    constructor
    · intro runs
      exact ⟨a, σ, ⟨rfl, rfl⟩, runs⟩
    · rintro ⟨a', σ', ⟨rfl, rfl⟩, runs⟩
      exact runs
  | call o k ih =>
    simp only [call_bind, runs_call, ih]
    constructor
    · rintro ⟨r, σ₁, step, a, σ', runs, after⟩
      exact ⟨a, σ', ⟨r, σ₁, step, runs⟩, after⟩
    · rintro ⟨a, σ', ⟨r, σ₁, step, runs⟩, after⟩
      exact ⟨r, σ₁, step, a, σ', runs, after⟩

/-- When every primitive has an outcome wherever it is defined, every safe
program has a terminating execution. -/
theorem exists_runs (progress : ∀ o, (act o).Progress) (c : Prog Op Ret α) (σ : S)
    (safe : c.Safe act σ) : ∃ a σ', c.Runs act σ a σ' := by
  induction c generalizing σ with
  | ret a => exact ⟨a, σ, rfl, rfl⟩
  | call o k ih =>
    obtain ⟨r, σ₁, step⟩ := progress o σ safe.1
    obtain ⟨a, σ', runs⟩ := ih r σ₁ (safe.2 r σ₁ step)
    exact ⟨a, σ', r, σ₁, step, runs⟩

end Prog

/-! ## Separating conjunction: rearrangement, quantifiers and pure facts -/

section Connectives

variable {S : Type s} [Zero S] [Add S] [SepAlgebra S]

theorem sepConj_left_comm (P Q R : S → Prop) : (P ∗ (Q ∗ R)) = (Q ∗ (P ∗ R)) := by
  rw [← sepConj_assoc, sepConj_comm P Q, sepConj_assoc]

theorem sepConj_exists_left {ι : Sort*} (P : ι → S → Prop) (Q : S → Prop) :
    ((fun σ => ∃ i, P i σ) ∗ Q) = fun σ => ∃ i, (P i ∗ Q) σ := by
  funext σ
  apply propext
  constructor
  · rintro ⟨x, y, separate, rfl, ⟨i, holds⟩, framed⟩
    exact ⟨i, x, y, separate, rfl, holds, framed⟩
  · rintro ⟨i, x, y, separate, rfl, holds, framed⟩
    exact ⟨x, y, separate, rfl, ⟨i, holds⟩, framed⟩

theorem sepConj_exists_right {ι : Sort*} (P : S → Prop) (Q : ι → S → Prop) :
    (P ∗ fun σ => ∃ i, Q i σ) = fun σ => ∃ i, (P ∗ Q i) σ := by
  rw [sepConj_comm, sepConj_exists_left]
  simp only [sepConj_comm]

theorem sepConj_pure_left (φ : Prop) (P Q : S → Prop) :
    ((fun σ => φ ∧ P σ) ∗ Q) = fun σ => φ ∧ (P ∗ Q) σ := by
  funext σ
  apply propext
  constructor
  · rintro ⟨x, y, separate, rfl, ⟨fact, holds⟩, framed⟩
    exact ⟨fact, x, y, separate, rfl, holds, framed⟩
  · rintro ⟨fact, x, y, separate, rfl, holds, framed⟩
    exact ⟨x, y, separate, rfl, ⟨fact, holds⟩, framed⟩

theorem sepConj_pure_right (φ : Prop) (P Q : S → Prop) :
    (P ∗ fun σ => φ ∧ Q σ) = fun σ => φ ∧ (P ∗ Q) σ := by
  rw [sepConj_comm, sepConj_pure_left]
  simp only [sepConj_comm]

theorem sepConj_or_right (P Q R : S → Prop) :
    (P ∗ fun σ => Q σ ∨ R σ) = fun σ => (P ∗ Q) σ ∨ (P ∗ R) σ := by
  funext σ
  apply propext
  constructor
  · rintro ⟨x, y, separate, rfl, holds, framed | framed⟩
    · exact Or.inl ⟨x, y, separate, rfl, holds, framed⟩
    · exact Or.inr ⟨x, y, separate, rfl, holds, framed⟩
  · rintro (⟨x, y, separate, rfl, holds, framed⟩ | ⟨x, y, separate, rfl, holds, framed⟩)
    · exact ⟨x, y, separate, rfl, holds, Or.inl framed⟩
    · exact ⟨x, y, separate, rfl, holds, Or.inr framed⟩

/-- A fact entailed by the left part of a separating conjunction. -/
theorem fact_of_sepConj_left {P Q : S → Prop} {φ : Prop} {σ : S} (holds : (P ∗ Q) σ)
    (fact : ∀ τ, P τ → φ) : φ := by
  obtain ⟨x, -, -, -, holdsP, -⟩ := holds
  exact fact x holdsP

/-- A fact entailed by the right part of a separating conjunction. -/
theorem fact_of_sepConj_right {P Q : S → Prop} {φ : Prop} {σ : S} (holds : (P ∗ Q) σ)
    (fact : ∀ τ, Q τ → φ) : φ := by
  obtain ⟨-, y, -, -, -, holdsQ⟩ := holds
  exact fact y holdsQ

/-- **Iterated separating conjunction** over a list of assertions. -/
def bigSep : List (S → Prop) → S → Prop
  | [] => emp
  | P :: Ps => P ∗ bigSep Ps

@[simp] theorem bigSep_nil : bigSep ([] : List (S → Prop)) = emp := rfl

@[simp] theorem bigSep_cons (P : S → Prop) (Ps : List (S → Prop)) :
    bigSep (P :: Ps) = (P ∗ bigSep Ps) := rfl

theorem bigSep_append (Ps Qs : List (S → Prop)) :
    bigSep (Ps ++ Qs) = (bigSep Ps ∗ bigSep Qs) := by
  induction Ps with
  | nil => rw [List.nil_append, bigSep_nil, emp_sepConj]
  | cons P Ps ih => rw [List.cons_append, bigSep_cons, bigSep_cons, ih, sepConj_assoc]

/-- The order of an iterated separating conjunction does not matter. -/
theorem bigSep_perm {Ps Qs : List (S → Prop)} (perm : Ps.Perm Qs) : bigSep Ps = bigSep Qs := by
  induction perm with
  | nil => rfl
  | cons P _ ih => rw [bigSep_cons, bigSep_cons, ih]
  | swap P Q Ps => rw [bigSep_cons, bigSep_cons, bigSep_cons, bigSep_cons, sepConj_left_comm]
  | trans _ _ ih₁ ih₂ => rw [ih₁, ih₂]

end Connectives

/-! ## Hoare triples -/

section Hoare

variable {S : Type s} {Op : Type u} {Ret : Op → Type v} {α β γ : Type v}
variable (act : (o : Op) → Action S (Ret o))

/-- **Hoare triple**: from every state satisfying `P`, no execution of `c`
reaches an undefined primitive, and every execution ends in a state satisfying
the postcondition for its result. -/
def Triple (P : S → Prop) (c : Prog Op Ret α) (Q : α → S → Prop) : Prop :=
  ∀ σ, P σ → c.Safe act σ ∧ ∀ a σ', c.Runs act σ a σ' → Q a σ'

theorem triple_ret (a : α) (Q : α → S → Prop) : Triple act (Q a) (Prog.ret a) Q :=
  fun _ holds => ⟨trivial, by rintro b σ' ⟨rfl, rfl⟩; exact holds⟩

theorem triple_bind {P : S → Prop} {c : Prog Op Ret α} {Q : α → S → Prop}
    {f : α → Prog Op Ret β} {R : β → S → Prop}
    (first : Triple act P c Q) (second : ∀ a, Triple act (Q a) (f a) R) :
    Triple act P (c.bind f) R := by
  intro σ holds
  obtain ⟨safe, post⟩ := first σ holds
  refine ⟨(Prog.safe_bind act c f σ).mpr ⟨safe, fun a σ' runs =>
    (second a σ' (post a σ' runs)).1⟩, ?_⟩
  intro b σ'' runs
  obtain ⟨a, σ', runs₁, runs₂⟩ := (Prog.runs_bind act c f σ b σ'').mp runs
  exact (second a σ' (post a σ' runs₁)).2 b σ'' runs₂

theorem triple_consequence {P P' : S → Prop} {c : Prog Op Ret α} {Q Q' : α → S → Prop}
    (strengthen : P' ≤ P) (spec : Triple act P c Q) (weaken : ∀ a, Q a ≤ Q' a) :
    Triple act P' c Q' := by
  intro σ holds
  obtain ⟨safe, post⟩ := spec σ (strengthen σ holds)
  exact ⟨safe, fun a σ' runs => weaken a σ' (post a σ' runs)⟩

theorem triple_pre {P P' : S → Prop} {c : Prog Op Ret α} {Q : α → S → Prop}
    (strengthen : P' ≤ P) (spec : Triple act P c Q) : Triple act P' c Q :=
  triple_consequence act strengthen spec fun _ => le_rfl

theorem triple_post {P : S → Prop} {c : Prog Op Ret α} {Q Q' : α → S → Prop}
    (spec : Triple act P c Q) (weaken : ∀ a, Q a ≤ Q' a) : Triple act P c Q' :=
  triple_consequence act le_rfl spec weaken

theorem triple_exists {ι : Sort*} {P : ι → S → Prop} {c : Prog Op Ret α}
    {Q : α → S → Prop} (spec : ∀ i, Triple act (P i) c Q) :
    Triple act (fun σ => ∃ i, P i σ) c Q := by
  rintro σ ⟨i, holds⟩
  exact spec i σ holds

theorem triple_or {P P' : S → Prop} {c : Prog Op Ret α} {Q : α → S → Prop}
    (left : Triple act P c Q) (right : Triple act P' c Q) :
    Triple act (fun σ => P σ ∨ P' σ) c Q := by
  rintro σ (holds | holds)
  · exact left σ holds
  · exact right σ holds

/-- An unsatisfiable precondition meets every specification. -/
theorem triple_false (c : Prog Op Ret α) (Q : α → S → Prop) :
    Triple act (fun _ => False) c Q :=
  fun _ impossible => impossible.elim

/-- A pure fact in the precondition may be assumed. -/
theorem triple_pure {φ : Prop} {P : S → Prop} {c : Prog Op Ret α} {Q : α → S → Prop}
    (spec : φ → Triple act P c Q) : Triple act (fun σ => φ ∧ P σ) c Q := by
  rintro σ ⟨fact, holds⟩
  exact spec fact σ holds

/-- One primitive call meets any specification its action meets. -/
theorem triple_prim (o : Op) {P : S → Prop} {Q : Ret o → S → Prop}
    (spec : ∀ σ, P σ → (act o).Safe σ ∧ ∀ r σ', (act o).Step σ r σ' → Q r σ') :
    Triple act P (Prog.prim o) Q := by
  intro σ holds
  obtain ⟨safe, post⟩ := spec σ holds
  refine ⟨⟨safe, fun _ _ _ => trivial⟩, ?_⟩
  rintro r σ' ⟨r', σ₁, step, rfl, rfl⟩
  exact post r' σ₁ step

/-- **Bounded iteration**: an invariant indexed by the elements still to be
processed. -/
theorem triple_foldList (f : β → γ → Prog Op Ret β) (I : List γ → β → S → Prop)
    (step : ∀ x xs b, Triple act (I (x :: xs) b) (f b x) (I xs)) :
    ∀ xs b, Triple act (I xs b) (Prog.foldList f xs b) (I []) := by
  intro xs
  induction xs with
  | nil => intro b; exact triple_ret act b (I [])
  | cons x xs ih => intro b; exact triple_bind act (step x xs b) ih

end Hoare

/-! ## Local actions -/

section Locality

variable {S : Type s} [Zero S] [Add S] [SepAlgebra S]

/-- **A local action** (Calcagno, O'Hearn and Yang): when it is defined on a
state, it stays defined after adding a separate frame (safety monotonicity),
and every outcome on the larger state is an outcome on the smaller state with
the frame untouched beside it (the frame property). -/
structure Action.Local {β : Type v} (a : Action S β) : Prop where
  safe_frame : ∀ {σ τ : S}, a.Safe σ → σ ## τ → a.Safe (σ + τ)
  step_frame : ∀ {σ τ σ' : S} {r : β}, a.Safe σ → σ ## τ → a.Step (σ + τ) r σ' →
    ∃ σ₁, σ₁ ## τ ∧ σ' = σ₁ + τ ∧ a.Step σ r σ₁

variable {Op : Type u} {Ret : Op → Type v} {α β γ : Type v}
variable (act : (o : Op) → Action S (Ret o))

/-- **Programs built from local actions are local actions.**  This is the
only place where the frame property is proved for whole programs. -/
theorem Prog.denote_local (isLocal : ∀ o, (act o).Local) (c : Prog Op Ret α) :
    (c.denote act).Local where
  safe_frame := by
    induction c with
    | ret a => intros; trivial
    | call o k ih =>
      rintro σ τ ⟨safe, next⟩ separate
      refine ⟨(isLocal o).safe_frame safe separate, fun r σ' step => ?_⟩
      obtain ⟨σ₁, separate₁, rfl, step₁⟩ := (isLocal o).step_frame safe separate step
      exact ih r (next r σ₁ step₁) separate₁
  step_frame := by
    induction c with
    | ret a =>
      rintro σ τ σ' b - separate ⟨rfl, rfl⟩
      exact ⟨σ, separate, rfl, rfl, rfl⟩
    | call o k ih =>
      rintro σ τ σ' b ⟨safe, next⟩ separate ⟨r, σ₁, step, runs⟩
      obtain ⟨σ₂, separate₂, rfl, step₂⟩ := (isLocal o).step_frame safe separate step
      obtain ⟨σ₃, separate₃, rfl, runs₃⟩ := ih r (next r σ₂ step₂) separate₂ runs
      exact ⟨σ₃, separate₃, rfl, r, σ₂, step₂, runs₃⟩

/-- **The frame rule**, for every program over local primitives. -/
theorem triple_frame (isLocal : ∀ o, (act o).Local) {P : S → Prop} {c : Prog Op Ret α}
    {Q : α → S → Prop} (spec : Triple act P c Q) (F : S → Prop) :
    Triple act (P ∗ F) c (fun a => Q a ∗ F) := by
  rintro _ ⟨σ, τ, separate, rfl, holds, framed⟩
  obtain ⟨safe, post⟩ := spec σ holds
  refine ⟨(Prog.denote_local act isLocal c).safe_frame safe separate, ?_⟩
  intro a σ' runs
  obtain ⟨σ₁, separate₁, rfl, runs₁⟩ :=
    (Prog.denote_local act isLocal c).step_frame safe separate runs
  exact ⟨σ₁, τ, separate₁, rfl, post a σ₁ runs₁, framed⟩

/-- The frame rule with the frame on the left. -/
theorem triple_frame_left (isLocal : ∀ o, (act o).Local) {P : S → Prop}
    {c : Prog Op Ret α} {Q : α → S → Prop} (spec : Triple act P c Q) (F : S → Prop) :
    Triple act (F ∗ P) c (fun a => F ∗ Q a) := by
  have framed := triple_frame act isLocal spec F
  rw [sepConj_comm F P]
  simpa only [sepConj_comm F] using framed

end Locality

/-! ## Controls -/

namespace Controls

open Prog

/-- Add an atom to a bag. -/
def addAct (atom : ℕ) : Action (Multiset ℕ) Unit :=
  ⟨fun _ => True, fun bag _ bag' => bag' = atom ::ₘ bag⟩

/-- Probe whether the whole bag is empty. -/
def probeAct (_ : Unit) : Action (Multiset ℕ) Bool :=
  ⟨fun _ => True, fun bag r bag' => r = decide (bag = 0) ∧ bag' = bag⟩

/-- Adding an atom is a local action. -/
theorem add_local (atom : ℕ) : (addAct atom).Local where
  safe_frame _ _ := trivial
  step_frame := by
    rintro σ τ σ' r - - rfl
    exact ⟨atom ::ₘ σ, trivial, (Multiset.cons_add atom σ τ).symm, rfl⟩

/-- **Positive control**: the specification of adding to the empty bag, framed
by an unrelated atom, keeps that atom. -/
theorem add_framed (atom other : ℕ) :
    Triple (Ret := fun _ : ℕ => Unit) addAct (sepConj emp (fun bag => bag = {other}))
      (prim atom)
      (fun _ => sepConj (fun bag => bag = {atom}) (fun bag => bag = {other})) := by
  have small : Triple (Ret := fun _ : ℕ => Unit) addAct emp (prim atom)
      (fun _ bag => bag = {atom}) := by
    apply triple_prim
    rintro σ rfl
    exact ⟨trivial, fun _ σ' step => step⟩
  exact triple_frame (Ret := fun _ : ℕ => Unit) addAct add_local small
    (fun bag => bag = {other})

/-- The probe meets "on the empty bag it answers `true`". -/
theorem probe_small : Triple (Ret := fun _ : Unit => Bool) probeAct emp (prim ())
    (fun r bag => r = true ∧ bag = 0) := by
  apply triple_prim
  rintro σ rfl
  exact ⟨trivial, by rintro r σ' ⟨rfl, rfl⟩; exact ⟨rfl, rfl⟩⟩

/-- **Negative control**: framing the probe's triple is unsound.  Beside the
atom `1` the probe never answers `true`. -/
theorem probe_frame_fails :
    ¬ Triple (Ret := fun _ : Unit => Bool) probeAct
      (sepConj emp (fun bag => bag = {1})) (prim ())
      (fun r => sepConj (fun bag => r = true ∧ bag = 0) (fun bag => bag = {1})) := by
  intro framed
  have pre : sepConj emp (fun bag : Multiset ℕ => bag = {1}) {1} :=
    ⟨0, {1}, trivial, (zero_add _).symm, rfl, rfl⟩
  obtain ⟨-, post⟩ := framed {1} pre
  obtain ⟨x, y, -, -, ⟨answer, -⟩, -⟩ :=
    post false {1} ⟨false, {1}, ⟨by decide, rfl⟩, rfl, rfl⟩
  cases answer

/-- The reason: the probe is not a local action. -/
theorem probe_not_local : ¬ (probeAct ()).Local := by
  intro isLocal
  obtain ⟨σ₁, -, -, answer, -⟩ := isLocal.step_frame (σ := 0) (τ := {1})
    (σ' := {1}) (r := false) trivial trivial ⟨by decide, (zero_add _).symm⟩
  simp at answer

end Controls

namespace Prog

open Mettapedia.GSLT.Dynamics


variable {Op : Type u} {Ret : Op → Type v} {α β : Type v}

/-- Preserve every primitive and its dependent response continuation. -/
def toResumption : Prog Op Ret α → ResumptionAlgebra.Computation Op Ret α
  | .ret value => ResumptionAlgebra.pure value
  | .call operation next => ResumptionAlgebra.perform operation fun reply => toResumption (next reply)

/-- Interpret the independent polynomial tree as the existing primitive program. -/
def fromResumption : ResumptionAlgebra.Computation Op Ret α → Prog Op Ret α :=
  ResumptionAlgebra.fold .ret .call

@[simp] theorem fromResumption_toResumption (program : Prog Op Ret α) :
    fromResumption (toResumption program) = program := by
  induction program with
  | ret value => rfl
  | call operation next ih =>
      change Prog.call operation (fun reply => fromResumption (toResumption (next reply))) =
        Prog.call operation next
      exact congrArg (Prog.call operation) (funext ih)

@[simp] theorem toResumption_fromResumption (tree : ResumptionAlgebra.Computation Op Ret α) :
    toResumption (fromResumption tree) = tree := by
  induction tree with
  | mk shape next ih =>
      cases shape with
      | inl value =>
          have empty : next = PEmpty.elim := by funext reply; exact reply.elim
          subst next
          rfl
      | inr operation =>
          change ResumptionAlgebra.perform operation
            (fun reply => toResumption (fromResumption (next reply))) =
              ResumptionAlgebra.perform operation next
          exact congrArg (ResumptionAlgebra.perform operation) (funext ih)

theorem toResumption_injective : Function.Injective (@toResumption Op Ret α) := by
  intro left right same
  exact (fromResumption_toResumption left).symm.trans
    ((congrArg fromResumption same).trans (fromResumption_toResumption right))

/-- This isomorphism does not quotient operation nodes, replies or returned state. -/
def resumptionEquiv : Prog Op Ret α ≃ ResumptionAlgebra.Computation Op Ret α where
  toFun := toResumption
  invFun := fromResumption
  left_inv := fromResumption_toResumption
  right_inv := toResumption_fromResumption

@[simp] theorem toResumption_bind (program : Prog Op Ret α)
    (next : α → Prog Op Ret β) :
    toResumption (program.bind next) =
      ResumptionAlgebra.bind (toResumption program) (fun answer => toResumption (next answer)) := by
  induction program with
  | ret value => rfl
  | call operation continuation ih =>
      change ResumptionAlgebra.perform operation (fun reply => toResumption ((continuation reply).bind next)) =
        ResumptionAlgebra.perform operation (fun reply =>
          ResumptionAlgebra.bind (toResumption (continuation reply)) (fun answer => toResumption (next answer)))
      exact congrArg (ResumptionAlgebra.perform operation) (funext ih)

@[simp] theorem fromResumption_bind (tree : ResumptionAlgebra.Computation Op Ret α)
    (next : α → ResumptionAlgebra.Computation Op Ret β) :
    fromResumption (ResumptionAlgebra.bind tree next) =
      (fromResumption tree).bind (fun answer => fromResumption (next answer)) := by
  apply toResumption_injective
  simp only [toResumption_bind, toResumption_fromResumption]

@[simp] theorem toResumption_prim (operation : Op) :
    toResumption (Prog.prim (Ret := Ret) operation) = ResumptionAlgebra.perform operation ResumptionAlgebra.pure := rfl

/-- The existing resumption budget law transfers without losing open states. -/
theorem fromResumption_unfold_add {State : Type v}
    (observe : State → ResumptionAlgebra.View Op Ret α State)
    (first second : Nat) (state : State) :
    fromResumption (ResumptionAlgebra.unfold observe (first + second) state) =
      (fromResumption (ResumptionAlgebra.unfold observe first state)).bind
        (fun leaf => fromResumption (ResumptionAlgebra.resume observe second leaf)) := by
  rw [ResumptionAlgebra.unfold_add, fromResumption_bind]

end Prog

namespace Resumption

open Mettapedia.GSLT.Dynamics


variable {Op : Type u} {Ret : Op → Type v} {α : Type v} {S : Type s}

/-- The return handler retains the complete final state. -/
def returnAction (value : α) : Action S α where
  Safe := fun _ => True
  Step := fun before answer after => value = answer ∧ before = after

/-- A stateful operation handler retains all permitted replies and successor states. -/
def operationAction {Reply : Type v} (operation : Action S Reply)
    (next : Reply → Action S α) : Action S α where
  Safe := fun before => operation.Safe before ∧
    ∀ reply middle, operation.Step before reply middle → (next reply).Safe middle
  Step := fun before answer after => ∃ reply middle,
    operation.Step before reply middle ∧ (next reply).Step middle answer after

/-- Interpret the polynomial tree directly, without going through `Prog` or an image. -/
def denote (act : (operation : Op) → Action S (Ret operation))
    (tree : ResumptionAlgebra.Computation Op Ret α) : Action S α :=
  ResumptionAlgebra.fold returnAction (fun operation => operationAction (act operation)) tree

@[simp] theorem denote_pure (act : (operation : Op) → Action S (Ret operation))
    (value : α) : denote act (ResumptionAlgebra.pure value) = returnAction value := rfl

@[simp] theorem denote_perform (act : (operation : Op) → Action S (Ret operation))
    (operation : Op) (next : Ret operation → ResumptionAlgebra.Computation Op Ret α) :
    denote act (ResumptionAlgebra.perform operation next) =
      operationAction (act operation) (fun reply => denote act (next reply)) := rfl

/-- Preserve both fault avoidance and the full nondeterministic state relation. -/
theorem denote_toResumption (act : (operation : Op) → Action S (Ret operation))
    (program : Prog Op Ret α) : denote act program.toResumption = program.denote act := by
  induction program with
  | ret value => rfl
  | call operation next ih =>
      calc
        denote act (Prog.toResumption (.call operation next)) =
            operationAction (act operation) (fun reply => denote act (next reply).toResumption) := rfl
        _ = operationAction (act operation) (fun reply => (next reply).denote act) :=
          congrArg (operationAction (act operation)) (funext ih)
        _ = (Prog.call operation next).denote act := rfl

theorem safe_toResumption (act : (operation : Op) → Action S (Ret operation))
    (program : Prog Op Ret α) (before : S) :
    (denote act program.toResumption).Safe before ↔ program.Safe act before := by
  rw [denote_toResumption]
  rfl

theorem runs_toResumption (act : (operation : Op) → Action S (Ret operation))
    (program : Prog Op Ret α) (before after : S) (answer : α) :
    (denote act program.toResumption).Step before answer after ↔
      program.Runs act before answer after := by
  rw [denote_toResumption]
  rfl

namespace Controls

inductive Operation where
  | sample
  | record (bit : Bool)

def Response : Operation → Type
  | .sample => Bool
  | .record _ => Unit

def primitive : (operation : Operation) → Action (List Bool) (Response operation)
  | .sample => ⟨fun _ => True, fun before _ after => before = after⟩
  | .record bit => ⟨fun _ => True, fun before _ after => after = before ++ [bit]⟩

def recordSample : Prog Operation Response Nat := do
  let bit ← Prog.prim (Ret := Response) Operation.sample
  Prog.prim (Ret := Response) (Operation.record bit)
  pure 7

/-- Equal printed answers still have two different permitted successor histories. -/
theorem true_history_is_kept :
    (denote primitive recordSample.toResumption).Step [] 7 [true] := by
  rw [runs_toResumption]
  exact ⟨true, [], rfl, (), [true], rfl, rfl, rfl⟩

theorem false_history_is_kept :
    (denote primitive recordSample.toResumption).Step [] 7 [false] := by
  rw [runs_toResumption]
  exact ⟨false, [], rfl, (), [false], rfl, rfl, rfl⟩

/-- Returning the same number does not license dropping its operation nodes. -/
theorem answer_only_erasure_loses_history :
    ¬ (denote primitive (ResumptionAlgebra.pure (7 : Nat))).Step [] 7 [true] := by
  change ¬ (7 = 7 ∧ ([] : List Bool) = [true])
  decide

theorem operation_tree_is_not_its_answer :
    recordSample.toResumption ≠ ResumptionAlgebra.pure (7 : Nat) := by
  intro same
  have kept := true_history_is_kept
  rw [same] at kept
  exact answer_only_erasure_loses_history kept

/-- One unsafe possible reply is enough to refute universal fault avoidance. -/
def guardedPrimitive : (operation : Operation) → Action (List Bool) (Response operation)
  | .sample => primitive .sample
  | .record bit => ⟨fun _ => bit = true, fun before _ after => after = before ++ [bit]⟩

theorem unsafe_alternative_is_not_erased :
    ¬ (denote guardedPrimitive recordSample.toResumption).Safe [] := by
  rw [safe_toResumption]
  intro safe
  have next := safe.2 false [] rfl
  have bad : false = true := next.1
  cases bad

end Controls

end Resumption

end Mettapedia.GSLT.Logic.AbstractSeparationLogic
