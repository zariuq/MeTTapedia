import Mettapedia.SetTheory.ValuesAndLocations.Reuse
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Commits

/-!
# A step that takes the atom holding a value may reuse its cell; a step that keeps it may not

In the store of `OccurrenceCommits` an occurrence carries its label once and for all
(`label : O → V`): an occurrence's value never changes. Updating a set held in a space is a step
that **takes** the occurrence holding the old value and **makes** an occurrence holding the new one
(`Commit`, `fire`). This is the value reading at the level of occurrences.

A runtime holds the values in cells. Its roots are the occurrences of the store and the names `K`
that the rest of the program holds: the continuation of the step, or an enclosing `let` that read
the old value. A heap over the roots `O ⊕ K` **implements** a store and an environment of names
(`Implements`) when every occurrence denotes its label and every name its value.

* `take_reuse_sound`: a step that takes `o` and makes only `o'`, labelled `f` of the label of `o`,
  may give `o'` the cell of `o`, written over with the new value (`takeReuse`), when no occurrence
  that survives the step and no name references that cell. A take is a use after which the taken
  occurrence is gone (`taken_gone`), so its cell's other references are the only possible
  observers.
* `keep_reuse_unsound`: a step that keeps `o` may not: `o` survives the step (`kept_survives`), so it
  observes the cell, and with an update that changes the value it now denotes the wrong value.
* `name_observer_unsound`: a take whose old value is still held by a name, as `$old` in
  `(let $old (match …) (transform …))`, may not reuse the cell either.
* `copy_sound`: making the successor in a fresh cell is right whether the step takes or keeps.

The controls (`Controls`) replay these on the store `{0}` whose occurrence holds `{1 2}`.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.ValuesAndLocations.StepReuse

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open Mettapedia.SetTheory.ValuesAndLocations.Reuse

universe u v w x

variable {O : Type u} {K : Type v} {Ptr : Type w} {V : Type x}
variable [DecidableEq O] [DecidableEq K] [DecidableEq Ptr]

/-- A heap over the occurrences and the names **implements** a store and an environment: every
occurrence of the store denotes its label, and every name denotes its value. -/
def Implements (h : Heap (O ⊕ K) Ptr V) (label : O → V) (env : K → Option V)
    (store : Finset O) : Prop :=
  (∀ o ∈ store, h.denote (.inl o) = some (label o)) ∧ ∀ k, h.denote (.inr k) = env k

/-- **Reuse on take**: the made `o'` gets the cell of the taken `o`, written over with `f` of its
value; `o` lets go of its reference. -/
def takeReuse (h : Heap (O ⊕ K) Ptr V) (o o' : O) (f : V → V) : Heap (O ⊕ K) Ptr V :=
  match h.ref (.inl o) with
  | some p =>
      ⟨Function.update (Function.update h.ref (.inl o) none) (.inl o') (some p),
        Function.update h.cell p ((h.cell p).map f)⟩
  | none => h

/-- **Reuse on keep**: write over the cell of the kept `o` and point `o'` at it; `o` keeps its
reference. -/
def keepReuse (h : Heap (O ⊕ K) Ptr V) (o o' : O) (f : V → V) : Heap (O ⊕ K) Ptr V :=
  match h.ref (.inl o) with
  | some p => ⟨Function.update h.ref (.inl o') (some p), Function.update h.cell p ((h.cell p).map f)⟩
  | none => h

/-- **Copy**: the made `o'` gets the fresh cell `q`, holding `f` of the value of `o`. -/
def copyStep (h : Heap (O ⊕ K) Ptr V) (o o' : O) (f : V → V) (q : Ptr) : Heap (O ⊕ K) Ptr V :=
  ⟨Function.update h.ref (.inl o') (some q), Function.update h.cell q ((h.denote (.inl o)).map f)⟩

section Laws

variable {label : O → V} {store : Finset O} {c : Commit O V}

/-- **A take is a use after which the occurrence is gone.** -/
theorem taken_gone (enabled : Enabled label store c) {o : O} (taken : o ∈ c.taken) :
    o ∉ fire store c :=
  fun inFire => Finset.disjoint_left.mp (disjoint_taken_fire enabled) taken inFire

/-- **A keep is not**: the kept occurrence survives the step. -/
theorem kept_survives (enabled : Enabled label store c) {o : O} (kept : o ∈ c.kept) :
    o ∈ fire store c :=
  kept_subset_fire enabled kept

omit [DecidableEq O] [DecidableEq K] [DecidableEq Ptr] in
/-- The cell of an occurrence that a heap implements. -/
theorem cell_of_implements {h : Heap (O ⊕ K) Ptr V} {env : K → Option V}
    (impl : Implements h label env store) {o : O} (member : o ∈ store) :
    ∃ p, h.ref (.inl o) = some p ∧ h.cell p = some (label o) := by
  have := impl.1 o member
  rw [Heap.denote_apply] at this
  cases hr : h.ref (.inl o) with
  | none => rw [hr] at this; cases this
  | some p =>
      rw [hr, Option.bind_some] at this
      exact ⟨p, rfl, this⟩

/-- **A step that takes an atom holding a value may reuse its cell for the successor**, when no
occurrence that survives the step and no name references that cell. -/
theorem take_reuse_sound {h : Heap (O ⊕ K) Ptr V} {env : K → Option V} {o o' : O} {f : V → V}
    (enabled : Enabled label store c) (taken : o ∈ c.taken) (made : c.made = {o'})
    (succ : label o' = f (label o)) (impl : Implements h label env store)
    (aloneInStore : ∀ y ∈ store, y ∉ c.taken → h.ref (.inl y) ≠ h.ref (.inl o))
    (aloneInNames : ∀ k, h.ref (.inr k) ≠ h.ref (.inl o)) :
    Implements (takeReuse h o o' f) label env (fire store c) := by
  obtain ⟨p, hp, hv⟩ := cell_of_implements impl (enabled.taken_subset taken)
  have o'Fresh : o' ∉ store := fun inStore =>
    Finset.disjoint_left.mp enabled.fresh (by rw [made]; exact Finset.mem_singleton_self o') inStore
  simp only [takeReuse, hp]
  refine ⟨fun y inFire => ?_, fun k => ?_⟩
  · rcases mem_fire.mp inFire with ⟨inStore, notTaken⟩ | inMade
    · have yo : y ≠ o := fun e => notTaken (e ▸ taken)
      have yo' : y ≠ o' := fun e => o'Fresh (e ▸ inStore)
      have apart : h.ref (.inl y) ≠ some p := fun e => aloneInStore y inStore notTaken (e.trans hp.symm)
      rw [Heap.denote_apply]
      simp only
      rw [Function.update_of_ne (fun e => yo' (Sum.inl_injective e)),
        Function.update_of_ne (fun e => yo (Sum.inl_injective e)), Heap.bind_update_of_ne apart]
      exact impl.1 y inStore
    · rw [made, Finset.mem_singleton] at inMade
      subst inMade
      simp [Heap.denote, hv, succ]
  · have apart : h.ref (.inr k) ≠ some p := fun e => aloneInNames k (e.trans hp.symm)
    rw [Heap.denote_apply]
    simp only
    rw [Function.update_of_ne Sum.inr_ne_inl, Function.update_of_ne Sum.inr_ne_inl,
      Heap.bind_update_of_ne apart]
    exact impl.2 k

/-- **A step that keeps the atom may not reuse its cell**: the kept occurrence survives and then
denotes the new value. -/
theorem keep_reuse_unsound {h : Heap (O ⊕ K) Ptr V} {env : K → Option V} {o o' : O} {f : V → V}
    (enabled : Enabled label store c) (kept : o ∈ c.kept) (made : o' ∈ c.made)
    (impl : Implements h label env store) (moves : f (label o) ≠ label o) :
    ¬ Implements (keepReuse h o o' f) label env (fire store c) := by
  rintro ⟨occurrences, -⟩
  obtain ⟨p, hp, hv⟩ := cell_of_implements impl (enabled.kept_subset kept)
  have oo' : o ≠ o' := fun e =>
    Finset.disjoint_left.mp enabled.fresh (e ▸ made) (enabled.kept_subset kept)
  have := occurrences o (kept_survives enabled kept)
  simp only [keepReuse, hp, Heap.denote_apply] at this
  rw [Function.update_of_ne (fun e => oo' (Sum.inl_injective e)), hp, Option.bind_some,
    Function.update_self, hv, Option.map_some, Option.some.injEq] at this
  exact moves this

/-- **A name that still holds the old value observes the cell**: reusing it on take is wrong. -/
theorem name_observer_unsound {h : Heap (O ⊕ K) Ptr V} {env : K → Option V} {o o' : O}
    {f : V → V} (enabled : Enabled label store c) (taken : o ∈ c.taken)
    (impl : Implements h label env store) {k : K} (observer : h.ref (.inr k) = h.ref (.inl o))
    (moves : f (label o) ≠ label o) :
    ¬ Implements (takeReuse h o o' f) label env (fire store c) := by
  rintro ⟨-, names⟩
  obtain ⟨p, hp, hv⟩ := cell_of_implements impl (enabled.taken_subset taken)
  have before := impl.2 k
  have after := names k
  rw [Heap.denote_apply, observer, hp, Option.bind_some, hv] at before
  simp only [takeReuse, hp, Heap.denote_apply] at after
  rw [Function.update_of_ne Sum.inr_ne_inl, Function.update_of_ne Sum.inr_ne_inl, observer, hp,
    Option.bind_some, Function.update_self, hv, Option.map_some, ← before,
    Option.some.injEq] at after
  exact moves after

/-- **A copy into a fresh cell is right**, whether the step takes or keeps the occurrence. -/
theorem copy_sound {h : Heap (O ⊕ K) Ptr V} {env : K → Option V} {o o' : O} {f : V → V}
    {q : Ptr} (enabled : Enabled label store c) (used : o ∈ store) (made : c.made = {o'})
    (succ : label o' = f (label o)) (impl : Implements h label env store)
    (fresh : ∀ r, h.ref r ≠ some q) :
    Implements (copyStep h o o' f q) label env (fire store c) := by
  have o'Fresh : o' ∉ store := fun inStore =>
    Finset.disjoint_left.mp enabled.fresh (by rw [made]; exact Finset.mem_singleton_self o') inStore
  refine ⟨fun y inFire => ?_, fun k => ?_⟩
  · rcases mem_fire.mp inFire with ⟨inStore, -⟩ | inMade
    · have yo' : y ≠ o' := fun e => o'Fresh (e ▸ inStore)
      simp only [copyStep, Heap.denote_apply]
      rw [Function.update_of_ne (fun e => yo' (Sum.inl_injective e)),
        Heap.bind_update_of_ne (fresh _)]
      exact impl.1 y inStore
    · rw [made, Finset.mem_singleton] at inMade
      subst inMade
      have := impl.1 o used
      simp only [copyStep, Heap.denote_apply, Function.update_self, Option.bind_some]
      rw [← Heap.denote_apply, this, Option.map_some, succ]
  · simp only [copyStep, Heap.denote_apply]
    rw [Function.update_of_ne Sum.inr_ne_inl, Heap.bind_update_of_ne (fresh _)]
    exact impl.2 k

end Laws

/-! ## Controls -/

namespace Controls

/-- Occurrence `0` holds `{1 2}`; every other occurrence holds `{3 1 2}`. -/
def label : ℕ → Multiset ℕ := fun n => if n = 0 then {1, 2} else {3, 1, 2}

/-- Take occurrence `0` and make occurrence `1`. -/
def takeStep : Commit ℕ (Multiset ℕ) := ⟨{0}, ∅, {1}, []⟩

/-- Keep occurrence `0` and make occurrence `1`. -/
def keepStep : Commit ℕ (Multiset ℕ) := ⟨∅, {0}, {1}, []⟩

theorem takeStep_enabled : Enabled label {0} takeStep :=
  ⟨by decide, by decide, by decide, by decide, by simp [takeStep]⟩

theorem keepStep_enabled : Enabled label {0} keepStep :=
  ⟨by decide, by decide, by decide, by decide, by simp [keepStep]⟩

/-- The heap: occurrence `0` references cell `0`, which holds `{1 2}`. The name (`Unit`) references
cell `0` too when `held` is true: an enclosing `let $old` that read the value. -/
def heap (held : Bool) : Heap (ℕ ⊕ Unit) ℕ (Multiset ℕ) :=
  ⟨fun r => match r with
    | .inl 0 => some 0
    | .inl _ => none
    | .inr _ => if held then some 0 else none,
   fun p => if p = 0 then some {1, 2} else none⟩

/-- The name's value: `{1 2}` when it holds the old value. -/
def env (held : Bool) : Unit → Option (Multiset ℕ) := fun _ => if held then some {1, 2} else none

theorem heap_implements (held : Bool) : Implements (heap held) label (env held) {0} := by
  refine ⟨fun o member => ?_, fun k => ?_⟩
  · rw [Finset.mem_singleton] at member
    subst member
    rfl
  · cases held <;> rfl

/-- **Positive**: taking `0` and reusing its cell for `1` implements the store after the step. -/
theorem take_reuse_right :
    Implements (takeReuse (heap false) 0 1 (3 ::ₘ ·)) label (env false) (fire {0} takeStep) :=
  take_reuse_sound takeStep_enabled (by decide) rfl rfl (heap_implements false)
    (fun y member notTaken => by
      rw [Finset.mem_singleton] at member
      subst member
      exact absurd (by decide) notTaken)
    (fun k => by cases k; decide)

/-- **Negative**: keeping `0` and writing over its cell makes `0` denote `{3 1 2}`. -/
theorem keep_reuse_wrong :
    ¬ Implements (keepReuse (heap false) 0 1 (3 ::ₘ ·)) label (env false) (fire {0} keepStep) :=
  keep_reuse_unsound keepStep_enabled (by decide) (by decide) (heap_implements false)
    (bag_cons_ne_self 3 _)

/-- **Negative**: a name that read the old value (`$old`) sees it change under reuse on take. -/
theorem old_name_wrong :
    ¬ Implements (takeReuse (heap true) 0 1 (3 ::ₘ ·)) label (env true) (fire {0} takeStep) :=
  name_observer_unsound takeStep_enabled (by decide) (heap_implements true) (k := ())
    rfl (bag_cons_ne_self 3 _)

/-- **Positive**: with the name, copying into the fresh cell `1` is right. -/
theorem old_name_copy_right :
    Implements (copyStep (heap true) 0 1 (3 ::ₘ ·) 1) label (env true) (fire {0} takeStep) :=
  copy_sound takeStep_enabled (by decide) rfl rfl (heap_implements true) (fun r => by
    rcases r with (_ | _ | n) | u
    · decide
    · decide
    · simp [heap]
    · cases u; decide)

end Controls

end Mettapedia.SetTheory.ValuesAndLocations.StepReuse
