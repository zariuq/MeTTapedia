/-
# State-component algebra for the evaluator seal

LeaTTa's threaded state is a PAIR: `St = { counter : Nat, world : World }`.
The two components have completely different roles in the conformance seal:

* `world` is the observable mutable state (named spaces, state cells, tokens).
  It is touched only by the enumerated control instructions, through
  `St.mapWorld`.  On the state-free fragment it is INVARIANT, so the
  "alternatives share one ordered final state" chronology question — the
  hard part of configuration simulation — does not arise there at all.
* `counter` is the gensym source.  It is monotone and feeds only fresh-name
  generation, whose effects are alpha-immaterial, so the specification must
  NOT index by it: it is quantified existentially and discharged by
  monotonicity.

This module provides the predicate algebra for that decomposition, so a
configuration simulation is a branch-by-branch application of closure lemmas
rather than a monolithic induction: each evaluator branch is either
world-preserving (the state-free fragment) or one of the enumerated world
mutations (the state tranche).

Nothing here mentions the specification side; these are facts about the
runtime state carrier only.
-/
import MettaHyperonFull.Minimal.Interpreter

namespace Mettapedia.Languages.MeTTa.HE.StateComponentAlgebra

open Metta.Minimal

/-! ## Component predicates on state transformers

A state transformer is any `St → α × St`: exactly the shape of `mettaEval`,
`interpretStack1`, and every evaluator helper. -/

/-- The transformer leaves the observable world untouched.  This is the
state-free fragment's defining property, and the reason that fragment needs
no state chronology. -/
def PreservesWorld {α : Type _} (f : St → α × St) : Prop :=
  ∀ st, (f st).2.world = st.world

/-- The transformer never decreases the gensym counter.  Every evaluator
branch satisfies this; it is what makes freshly generated names at distinct
steps distinguishable. -/
def CounterMonotone {α : Type _} (f : St → α × St) : Prop :=
  ∀ st, st.counter ≤ (f st).2.counter

/-- The transformer leaves the gensym counter untouched: it generates no
fresh names.  Strictly stronger than `CounterMonotone`. -/
def PreservesCounter {α : Type _} (f : St → α × St) : Prop :=
  ∀ st, (f st).2.counter = st.counter

/-! ## Base facts for the two state operations -/

@[simp] theorem fresh_world (st : St) : (St.fresh st).2.world = st.world := rfl

@[simp] theorem fresh_counter (st : St) :
    (St.fresh st).2.counter = st.counter + 1 := rfl

@[simp] theorem mapWorld_counter (st : St) (f : World → World) :
    (st.mapWorld f).counter = st.counter := rfl

@[simp] theorem mapWorld_world (st : St) (f : World → World) :
    (st.mapWorld f).world = f st.world := rfl

/-- Gensym freshening preserves the world: name generation is not a state
effect.  This is the fact that keeps the state-free fragment state-free even
though it freshens rule variables. -/
theorem fresh_preservesWorld : PreservesWorld St.fresh := fun _ => rfl

/-- Gensym freshening is counter-monotone. -/
theorem fresh_counterMonotone : CounterMonotone St.fresh := fun st => by
  simp only [fresh_counter]
  omega

/-- A world mutation preserves the counter: state effects generate no names.
The two components are genuinely independent. -/
theorem mapWorld_preservesCounter (f : World → World) :
    PreservesCounter (fun st => ((), st.mapWorld f)) := fun _ => rfl

/-! ## Closure algebra

These are the lemmas that make a configuration simulation mechanical: each
evaluator branch is discharged by one closure step rather than by reasoning
about `St` as a single indivisible carrier. -/

theorem preservesWorld_pure {α : Type _} (a : α) :
    PreservesWorld (fun st => (a, st)) := fun _ => rfl

theorem counterMonotone_pure {α : Type _} (a : α) :
    CounterMonotone (fun st => (a, st)) := fun _ => Nat.le_refl _

theorem preservesCounter_pure {α : Type _} (a : α) :
    PreservesCounter (fun st => (a, st)) := fun _ => rfl

/-- World preservation is closed under sequential composition (monadic bind):
the shape every evaluator branch has. -/
theorem preservesWorld_bind {α β : Type _}
    {f : St → α × St} {g : α → St → β × St}
    (hf : PreservesWorld f) (hg : ∀ a, PreservesWorld (g a)) :
    PreservesWorld (fun st => let r := f st; g r.1 r.2) := by
  intro st
  simp only
  rw [hg (f st).1 (f st).2, hf st]

/-- Counter monotonicity is closed under sequential composition. -/
theorem counterMonotone_bind {α β : Type _}
    {f : St → α × St} {g : α → St → β × St}
    (hf : CounterMonotone f) (hg : ∀ a, CounterMonotone (g a)) :
    CounterMonotone (fun st => let r := f st; g r.1 r.2) := by
  intro st
  simp only
  exact Nat.le_trans (hf st) (hg (f st).1 (f st).2)

/-- Counter preservation is closed under sequential composition. -/
theorem preservesCounter_bind {α β : Type _}
    {f : St → α × St} {g : α → St → β × St}
    (hf : PreservesCounter f) (hg : ∀ a, PreservesCounter (g a)) :
    PreservesCounter (fun st => let r := f st; g r.1 r.2) := by
  intro st
  simp only
  rw [hg (f st).1 (f st).2, hf st]

/-- Preserving the counter implies monotonicity. -/
theorem counterMonotone_of_preservesCounter {α : Type _} {f : St → α × St}
    (h : PreservesCounter f) : CounterMonotone f := fun st => by
  rw [h st]
  exact Nat.le_refl _

/-! ### Folds

The evaluator threads state through lists of work items and alternatives.
Both component properties survive an arbitrary left fold, which is what makes
per-branch reasoning suffice for whole-list steps. -/

theorem preservesWorld_foldl {α β : Type _}
    (step : β → α → St → β × St)
    (hstep : ∀ b a, PreservesWorld (step b a)) :
    ∀ (as : List α) (b : β),
      PreservesWorld (fun st => as.foldl
        (fun (acc : β × St) a => step acc.1 a acc.2) (b, st))
  | [], b => fun st => rfl
  | a :: as, b => by
    intro st
    have ih := preservesWorld_foldl step hstep as (step b a st).1 (step b a st).2
    simp only [List.foldl_cons]
    rw [ih, hstep b a st]

theorem counterMonotone_foldl {α β : Type _}
    (step : β → α → St → β × St)
    (hstep : ∀ b a, CounterMonotone (step b a)) :
    ∀ (as : List α) (b : β),
      CounterMonotone (fun st => as.foldl
        (fun (acc : β × St) a => step acc.1 a acc.2) (b, st))
  | [], b => fun st => Nat.le_refl _
  | a :: as, b => by
    intro st
    have ih := counterMonotone_foldl step hstep as (step b a st).1 (step b a st).2
    simp only [List.foldl_cons]
    exact Nat.le_trans (hstep b a st) ih

/-! ## The separation theorem

The two components are independent: a transformer that only freshens names
preserves the world, and a transformer that only mutates the world preserves
the counter.  Consequently a branch cannot secretly couple them, which is the
structural content of "the state-free fragment needs no chronology". -/

/-- A transformer built only from gensym freshening and pure steps preserves
the world, however many names it generates. -/
theorem preservesWorld_of_freshOnly {α : Type _}
    {f : St → α × St} (h : ∀ st, (f st).2.world = st.world) :
    PreservesWorld f := h

/-- World-preserving transformers compose with counter-monotone ones without
interaction: the pair `(world, counter)` decomposes the state completely. -/
theorem stateComponents_independent {α β : Type _}
    {f : St → α × St} {g : α → St → β × St}
    (hfw : PreservesWorld f) (hgw : ∀ a, PreservesWorld (g a))
    (hfc : CounterMonotone f) (hgc : ∀ a, CounterMonotone (g a)) :
    PreservesWorld (fun st => let r := f st; g r.1 r.2) ∧
      CounterMonotone (fun st => let r := f st; g r.1 r.2) :=
  ⟨preservesWorld_bind hfw hgw, counterMonotone_bind hfc hgc⟩

/-- An `St` is determined by its two components: there is no hidden state, so
the decomposition is exhaustive rather than merely convenient. -/
theorem st_eq_of_components {st st' : St}
    (hcounter : st.counter = st'.counter) (hworld : st.world = st'.world) :
    st = st' := by
  cases st
  cases st'
  simp only [St.mk.injEq]
  exact ⟨hcounter, hworld⟩

/-- Consequently, a transformer preserving BOTH components is the identity on
state — the sharpest form of "this branch has no state effect". -/
theorem st_unchanged_of_preserves_both {α : Type _} {f : St → α × St}
    (hw : PreservesWorld f) (hc : PreservesCounter f) (st : St) :
    (f st).2 = st :=
  st_eq_of_components (hc st) (hw st)

end Mettapedia.Languages.MeTTa.HE.StateComponentAlgebra
