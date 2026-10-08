import Mettapedia.GSLT.Logic.AbstractSeparationLogic

/-!
# Weakest preconditions for programs over local actions

`Prog.wp act c Q σ` says that no execution of `c` from `σ` reaches an undefined
primitive, and that every execution ends in a state satisfying `Q` of its
result.  It is the body of the Hoare triple, so a triple is exactly an
entailment into the weakest precondition (`triple_iff_wp`), with no second
semantics to relate.

The calculus computes the weakest precondition of a program from its shape:

* `wp_ret`, `wp_pure`: a returned value meets the postcondition at once;
* `wp_bind`: sequencing composes weakest preconditions;
* `wp_ite`, `wp_dite` (and their pointwise forms): a conditional chooses one;
* `wp_call`, `wp_prim`: one primitive is its action's safety and outcomes;
* `wp_foldList`: bounded iteration with an invariant.

The frame rule of `AbstractSeparationLogic` becomes `wp_frame`, and its usual
use, calling a specified program inside a larger resource, is
`wp_call_framed`: from `{P} c {R}` and a state holding `P ∗ F`, every
execution ends in `R a ∗ F`.  Locality is a class, `LocalSignature`, so the
rules and the tactics built on them find it by instance resolution.

A `StepInvariant` is a property of whole states that every primitive step
preserves, such as the well-formedness of C memory.  It holds after every
execution (`runs_stepInvariant`), so a proof may carry it across calls
(`wp_call_framed_invariant`) beside the separating conjunction.

Every rule is a theorem about `Triple`; nothing here is assumed.  In
particular `wp_call_framed` is `triple_frame` read backwards.

## Examples

* **Positive.**  Adding an atom twice to a bag that holds an unrelated atom
  keeps it (`Controls.twice_framed`), by two framed calls.
* **Negative.**  The weakest precondition of the non-local probe of
  `AbstractSeparationLogic` is not framed: framing it would give a result no
  execution produces (`Controls.probe_wp_frame_fails`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Logic.AbstractSeparationLogic

open Mettapedia.GSLT.SeparationAlgebra
open scoped Mettapedia.GSLT.SeparationAlgebra

universe u v s

/-! ## The weakest precondition -/

section WeakestPrecondition

variable {S : Type s} {Op : Type u} {Ret : Op → Type v} {α β γ : Type v}
variable (act : (o : Op) → Action S (Ret o))

/-- **The weakest precondition** of `c` for `Q`: from `σ`, no execution of `c`
reaches an undefined primitive, and every execution ends in a state satisfying
`Q` of its result. -/
def Prog.wp (c : Prog Op Ret α) (Q : α → S → Prop) (σ : S) : Prop :=
  c.Safe act σ ∧ ∀ a σ', c.Runs act σ a σ' → Q a σ'

/-- **A triple is an entailment into the weakest precondition.**  This is the
soundness and the completeness of the calculus at once: the weakest
precondition is the body of the triple. -/
theorem triple_iff_wp {P : S → Prop} {c : Prog Op Ret α} {Q : α → S → Prop} :
    Triple act P c Q ↔ ∀ σ, P σ → c.wp act Q σ :=
  Iff.rfl

theorem triple_of_wp {P : S → Prop} {c : Prog Op Ret α} {Q : α → S → Prop}
    (entails : ∀ σ, P σ → c.wp act Q σ) : Triple act P c Q :=
  entails

/-- The weakest precondition is a precondition. -/
theorem wp_triple (c : Prog Op Ret α) (Q : α → S → Prop) : Triple act (c.wp act Q) c Q :=
  fun _ holds => holds

theorem wp_of_triple {P : S → Prop} {c : Prog Op Ret α} {Q : α → S → Prop}
    (spec : Triple act P c Q) {σ : S} (holds : P σ) : c.wp act Q σ :=
  spec σ holds

theorem wp_ret (a : α) (Q : α → S → Prop) : (Prog.ret a : Prog Op Ret α).wp act Q = Q a := by
  funext σ
  apply propext
  constructor
  · rintro ⟨-, post⟩
    exact post a σ ⟨rfl, rfl⟩
  · intro holds
    exact ⟨trivial, by rintro b σ' ⟨rfl, rfl⟩; exact holds⟩

theorem wp_pure (a : α) (Q : α → S → Prop) : (pure a : Prog Op Ret α).wp act Q = Q a :=
  wp_ret act a Q

/-- **Sequencing** composes weakest preconditions. -/
theorem wp_bind (c : Prog Op Ret α) (f : α → Prog Op Ret β) (Q : β → S → Prop) :
    (c.bind f).wp act Q = c.wp act (fun a => (f a).wp act Q) := by
  funext σ
  apply propext
  unfold Prog.wp
  rw [Prog.safe_bind]
  constructor
  · rintro ⟨⟨safe, after⟩, post⟩
    exact ⟨safe, fun a σ' runs => ⟨after a σ' runs, fun b σ'' runs' =>
      post b σ'' ((Prog.runs_bind act c f σ b σ'').mpr ⟨a, σ', runs, runs'⟩)⟩⟩
  · rintro ⟨safe, post⟩
    refine ⟨⟨safe, fun a σ' runs => (post a σ' runs).1⟩, fun b σ'' runs => ?_⟩
    obtain ⟨a, σ', first, second⟩ := (Prog.runs_bind act c f σ b σ'').mp runs
    exact (post a σ' first).2 b σ'' second

/-- Sequencing, in `do` notation. -/
theorem wp_bind' (c : Prog Op Ret α) (f : α → Prog Op Ret β) (Q : β → S → Prop) :
    (c >>= f).wp act Q = c.wp act (fun a => (f a).wp act Q) :=
  wp_bind act c f Q

theorem wp_ite (b : Prop) [Decidable b] (c d : Prog Op Ret α) (Q : α → S → Prop) :
    (if b then c else d).wp act Q = if b then c.wp act Q else d.wp act Q := by
  split <;> rfl

theorem wp_dite (b : Prop) [Decidable b] (c : b → Prog Op Ret α) (d : ¬ b → Prog Op Ret α)
    (Q : α → S → Prop) :
    (if h : b then c h else d h).wp act Q = if h : b then (c h).wp act Q else (d h).wp act Q := by
  split <;> rfl

/-- A conditional chooses one weakest precondition, at a given state. -/
theorem wp_ite_apply (b : Prop) [Decidable b] (c d : Prog Op Ret α) (Q : α → S → Prop) (σ : S) :
    (if b then c else d).wp act Q σ = if b then c.wp act Q σ else d.wp act Q σ := by
  split <;> rfl

theorem wp_dite_apply (b : Prop) [Decidable b] (c : b → Prog Op Ret α) (d : ¬ b → Prog Op Ret α)
    (Q : α → S → Prop) (σ : S) :
    (if h : b then c h else d h).wp act Q σ =
      if h : b then (c h).wp act Q σ else (d h).wp act Q σ := by
  split <;> rfl

/-- One primitive call followed by a continuation. -/
theorem wp_call (o : Op) (k : Ret o → Prog Op Ret α) (Q : α → S → Prop) (σ : S) :
    (Prog.call o k).wp act Q σ ↔
      (act o).Safe σ ∧ ∀ r σ', (act o).Step σ r σ' → (k r).wp act Q σ' := by
  constructor
  · rintro ⟨⟨safe, next⟩, post⟩
    exact ⟨safe, fun r σ' step => ⟨next r σ' step, fun a σ'' runs =>
      post a σ'' ⟨r, σ', step, runs⟩⟩⟩
  · rintro ⟨safe, next⟩
    exact ⟨⟨safe, fun r σ' step => (next r σ' step).1⟩, fun a σ'' ⟨r, σ', step, runs⟩ =>
      (next r σ' step).2 a σ'' runs⟩

/-- One primitive call: its action is defined, and every outcome meets the
postcondition. -/
theorem wp_prim (o : Op) (Q : Ret o → S → Prop) (σ : S) :
    (Prog.prim o : Prog Op Ret (Ret o)).wp act Q σ ↔
      (act o).Safe σ ∧ ∀ r σ', (act o).Step σ r σ' → Q r σ' := by
  rw [Prog.prim, wp_call]
  simp only [wp_ret]

theorem wp_mono {c : Prog Op Ret α} {Q Q' : α → S → Prop} (weaken : ∀ a σ, Q a σ → Q' a σ)
    {σ : S} (holds : c.wp act Q σ) : c.wp act Q' σ :=
  ⟨holds.1, fun a σ' runs => weaken a σ' (holds.2 a σ' runs)⟩

/-- **Consequence**: a specified program meets every postcondition its own
postcondition entails. -/
theorem wp_consequence {P : S → Prop} {c : Prog Op Ret α} {R Q : α → S → Prop}
    (spec : Triple act P c R) {σ : S} (holds : P σ) (post : ∀ a σ', R a σ' → Q a σ') :
    c.wp act Q σ :=
  wp_mono act post (spec σ holds)

/-- **Bounded iteration** with an invariant indexed by the elements still to
be processed. -/
theorem wp_foldList (f : β → γ → Prog Op Ret β) (I : List γ → β → S → Prop)
    (step : ∀ x xs b, Triple act (I (x :: xs) b) (f b x) (I xs)) (xs : List γ) (b : β)
    {Q : β → S → Prop} {σ : S} (holds : I xs b σ) (post : ∀ b' σ', I [] b' σ' → Q b' σ') :
    (Prog.foldList f xs b).wp act Q σ :=
  wp_consequence act (triple_foldList act f I step xs b) holds post

/-- **A step invariant** of a signature: a property of states that every
defined step of every primitive preserves, such as the well-formedness of
the whole of memory. -/
class StepInvariant (G : S → Prop) : Prop where
  preserved : ∀ o σ r σ', G σ → (act o).Safe σ → (act o).Step σ r σ' → G σ'

/-- A step invariant holds at the end of every execution of a safe program. -/
theorem runs_stepInvariant (G : S → Prop) [StepInvariant act G] (c : Prog Op Ret α)
    {σ σ' : S} {a : α} (holds : G σ) (safe : c.Safe act σ) (runs : c.Runs act σ a σ') :
    G σ' := by
  induction c generalizing σ with
  | ret b =>
    obtain ⟨-, rfl⟩ := runs
    exact holds
  | call o k ih =>
    obtain ⟨r, σ₁, step, rest⟩ := runs
    exact ih r (StepInvariant.preserved o σ r σ₁ holds safe.1 step) (safe.2 r σ₁ step) rest

/-- **A step invariant may be assumed of the final state.** -/
theorem wp_stepInvariant (G : S → Prop) [StepInvariant act G] {c : Prog Op Ret α}
    {Q : α → S → Prop} {σ : S} (holds : G σ) (body : c.wp act (fun a σ' => G σ' → Q a σ') σ) :
    c.wp act Q σ :=
  ⟨body.1, fun a σ' runs => body.2 a σ' runs (runs_stepInvariant act G c holds body.1 runs)⟩

end WeakestPrecondition

/-! ## The frame rule, read backwards -/

section Frame

variable {S : Type s} [Zero S] [Add S] [SepAlgebra S]
variable {Op : Type u} {Ret : Op → Type v} {α : Type v}

/-- **A signature of local actions.**  The frame rule holds for every program
over it (`triple_frame`); as a class, the rules below find it by instance
resolution. -/
class LocalSignature (act : (o : Op) → Action S (Ret o)) : Prop where
  isLocal : ∀ o, (act o).Local

variable (act : (o : Op) → Action S (Ret o)) [LocalSignature act]

/-- **The frame rule for weakest preconditions.** -/
theorem wp_frame {c : Prog Op Ret α} {Q : α → S → Prop} {F : S → Prop} {σ : S}
    (holds : (c.wp act Q ∗ F) σ) : c.wp act (fun a => Q a ∗ F) σ :=
  triple_frame act LocalSignature.isLocal (wp_triple act c Q) F σ holds

/-- **A framed call**: from `{P} c {R}` and a state that holds `P` beside a
frame `F`, every execution of `c` ends in `R a` beside the untouched frame. -/
theorem wp_call_framed {P : S → Prop} {c : Prog Op Ret α} {R Q : α → S → Prop}
    {F : S → Prop} (spec : Triple act P c R) {σ : S} (holds : (P ∗ F) σ)
    (post : ∀ a σ', (R a ∗ F) σ' → Q a σ') : c.wp act Q σ :=
  wp_mono act post (triple_frame act LocalSignature.isLocal spec F σ holds)

/-- A framed call that keeps a step invariant of the whole state. -/
theorem wp_call_framed_invariant (G : S → Prop) [StepInvariant act G] {P : S → Prop}
    {c : Prog Op Ret α} {R Q : α → S → Prop} {F : S → Prop} (spec : Triple act P c R)
    {σ : S} (holds : (P ∗ F) σ) (invariant : G σ)
    (post : ∀ a σ', (R a ∗ F) σ' → G σ' → Q a σ') : c.wp act Q σ :=
  wp_stepInvariant act G invariant (wp_mono act post
    (triple_frame act LocalSignature.isLocal spec F σ holds))

end Frame

/-! ## Controls -/

namespace Controls

open Prog

instance : LocalSignature (S := Multiset ℕ) (Ret := fun _ : ℕ => Unit) addAct :=
  ⟨add_local⟩

/-- Add one atom to the empty bag. -/
theorem add_small (atom : ℕ) :
    Triple (Ret := fun _ : ℕ => Unit) addAct emp (prim atom) (fun _ bag => bag = {atom}) := by
  apply triple_prim
  rintro σ rfl
  exact ⟨trivial, fun _ σ' step => step⟩

/-- **Positive control**: two framed calls add two atoms beside an unrelated
one, which is kept. -/
theorem twice_framed (first second other : ℕ) :
    Triple (Ret := fun _ : ℕ => Unit) addAct (fun bag => bag = {other})
      (prim first >>= fun _ => prim second)
      (fun _ => (fun bag => bag = {second}) ∗ ((fun bag => bag = {first}) ∗
        (fun bag => bag = {other}))) := by
  apply triple_of_wp
  intro σ holds
  rw [wp_bind']
  refine wp_call_framed (Ret := fun _ : ℕ => Unit) addAct (add_small first)
    (F := fun bag => bag = {other}) (by rwa [emp_sepConj]) fun _ σ' after => ?_
  exact wp_call_framed (Ret := fun _ : ℕ => Unit) addAct (add_small second)
    (by rwa [emp_sepConj]) fun _ _ done => done

/-- **Negative control**: the probe's weakest precondition is not framed.
Framed by the atom `1`, it would promise the answer `true`, which no
execution gives. -/
theorem probe_wp_frame_fails :
    ¬ ∀ σ : Multiset ℕ, ((prim () : Prog Unit (fun _ : Unit => Bool) Bool).wp probeAct
        (fun r bag => r = true ∧ bag = 0) ∗ (fun bag => bag = {1})) σ →
      (prim () : Prog Unit (fun _ : Unit => Bool) Bool).wp probeAct
        (fun r => (fun bag => r = true ∧ bag = 0) ∗ (fun bag => bag = {1})) σ := by
  intro framed
  have small : (prim () : Prog Unit (fun _ : Unit => Bool) Bool).wp probeAct
      (fun r bag => r = true ∧ bag = 0) 0 := probe_small 0 rfl
  have pre : ((prim () : Prog Unit (fun _ : Unit => Bool) Bool).wp probeAct
      (fun r bag => r = true ∧ bag = 0) ∗ (fun bag => bag = {1})) {1} :=
    ⟨0, {1}, trivial, (zero_add _).symm, small, rfl⟩
  obtain ⟨-, post⟩ := framed {1} pre
  obtain ⟨x, y, -, -, ⟨answer, -⟩, -⟩ :=
    post false {1} ⟨false, {1}, ⟨by decide, rfl⟩, rfl, rfl⟩
  cases answer

end Controls

end Mettapedia.GSLT.Logic.AbstractSeparationLogic
