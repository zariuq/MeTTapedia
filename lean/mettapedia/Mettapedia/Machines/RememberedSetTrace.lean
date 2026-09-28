import Mathlib.Data.List.Basic

/-!
# Tracing a young generation from a remembered set

A generational collector copies only the young objects that are still reached.
Tracing every root through the whole heap finds them, at a cost that grows with
the old generation.  A minor collection instead starts from the young roots and
from the old objects written since the last collection, and follows edges only
into young objects.

This module states the condition under which that trace misses nothing, and the
write discipline that keeps the condition.

* `young_reached_of_reached`: every young object reached from any root is
  reached, through young objects only, from a young root or from a remembered
  object, provided every edge from an old object to a young one starts at a
  remembered object (`Barrier`).
* `Barrier` holds after a collection (no young objects) and is kept by each
  mutator step: allocating a young object with any edges (`barrier_alloc`),
  writing an edge from a young object (`barrier_write_young`), writing an edge
  from an old object that is remembered at the write (`barrier_write_remember`),
  and deleting an edge (`barrier_delete`).
* An old object written without being remembered breaks it
  (`barrier_unremembered_write_fails`), and the young-only trace then misses a
  reached young object (`unremembered_write_misses`).

In the open-equation machine's minor collection, the old objects are the old
generation's atoms, continuations and slot vectors, the cells below the old
boundary, and the frames below the frame stack's low-water mark.  The young
roots are the frames above that mark, the call's destination and query cells.
The remembered objects are the old cells bound, and the old slot vectors stored
into, since the last collection.
-/

namespace Mettapedia.Machines.RememberedSetTrace

variable {N : Type*}

/-- A heap as its edges: `edge a b` when object `a` refers to object `b`. -/
abbrev Edges (N : Type*) := N → N → Prop

/-- `b` is reached from `a` along edges. -/
inductive Reach (edge : Edges N) : N → N → Prop
  | refl (a : N) : Reach edge a a
  | step {a b c : N} : edge a b → Reach edge b c → Reach edge a c

/-- `b` is reached from `a` along edges whose every target is young: the path
may leave `a` whatever `a` is, and then stays among young objects. -/
inductive YoungReach (edge : Edges N) (old : N → Prop) : N → N → Prop
  | refl (a : N) : YoungReach edge old a a
  | step {a b c : N} : edge a b → ¬ old b → YoungReach edge old b c →
      YoungReach edge old a c

/-- Every edge from an old object to a young one starts at a remembered
object. -/
def Barrier (edge : Edges N) (old remembered : N → Prop) : Prop :=
  ∀ a b, edge a b → old a → ¬ old b → remembered a

/-- A young object reached from a root is reached, through young objects only,
from that root when the root is young, or from a remembered object. -/
theorem young_reached_of_reached {edge : Edges N} {old remembered : N → Prop}
    [DecidablePred old]
    (barrier : Barrier edge old remembered) {r y : N} (reach : Reach edge r y)
    (young : ¬ old y) :
    (¬ old r ∧ YoungReach edge old r y) ∨
      ∃ m, remembered m ∧ YoungReach edge old m y := by
  induction reach with
  | refl a => exact Or.inl ⟨young, YoungReach.refl a⟩
  | @step a b c hab _ ih =>
    rcases ih young with ⟨hb, hbc⟩ | ⟨m, hm, hmc⟩
    · by_cases ha : old a
      · exact Or.inr ⟨a, barrier a b hab ha hb, YoungReach.step hab hb hbc⟩
      · exact Or.inl ⟨ha, YoungReach.step hab hb hbc⟩
    · exact Or.inr ⟨m, hm, hmc⟩

/-- The trace a minor collection runs reaches exactly the young objects the
full trace reaches: from young roots and remembered objects, through young
objects only. -/
theorem minor_trace_complete {edge : Edges N} {old remembered : N → Prop}
    [DecidablePred old]
    (roots : N → Prop) (barrier : Barrier edge old remembered) {y : N}
    (young : ¬ old y) (reached : ∃ r, roots r ∧ Reach edge r y) :
    ∃ s, ((roots s ∧ ¬ old s) ∨ remembered s) ∧ YoungReach edge old s y := by
  obtain ⟨r, hr, hry⟩ := reached
  rcases young_reached_of_reached barrier hry young with
    ⟨hro, hy⟩ | ⟨m, hm, hmy⟩
  · exact ⟨r, Or.inl ⟨hr, hro⟩, hy⟩
  · exact ⟨m, Or.inr hm, hmy⟩

/-- Young-only paths are paths. -/
theorem reach_of_youngReach {edge : Edges N} {old : N → Prop} {a b : N}
    (h : YoungReach edge old a b) : Reach edge a b := by
  induction h with
  | refl a => exact Reach.refl a
  | step hab _ _ ih => exact Reach.step hab ih

/-- Right after a collection nothing is young, and the barrier holds with no
object remembered. -/
theorem barrier_all_old (edge : Edges N) (old : N → Prop)
    (all_old : ∀ a, old a) : Barrier edge old (fun _ => False) :=
  fun _ b _ _ hb => absurd (all_old b) hb

/-- Allocating a young object `n` with any edges out of it keeps the
barrier. -/
theorem barrier_alloc {edge : Edges N} {old remembered : N → Prop}
    (barrier : Barrier edge old remembered) (n : N) (fresh : ¬ old n)
    (out : N → Prop) :
    Barrier (fun a b => edge a b ∨ (a = n ∧ out b)) old remembered := by
  intro a b hab ha hb
  rcases hab with hab | ⟨rfl, _⟩
  · exact barrier a b hab ha hb
  · exact absurd ha fresh

/-- Writing an edge from a young object keeps the barrier. -/
theorem barrier_write_young {edge : Edges N} {old remembered : N → Prop}
    (barrier : Barrier edge old remembered) (w t : N) (young : ¬ old w) :
    Barrier (fun a b => edge a b ∨ (a = w ∧ b = t)) old remembered := by
  intro a b hab ha hb
  rcases hab with hab | ⟨rfl, _⟩
  · exact barrier a b hab ha hb
  · exact absurd ha young

/-- Writing an edge from an old object keeps the barrier once the object is
remembered at the write. -/
theorem barrier_write_remember {edge : Edges N}
    {old remembered : N → Prop} (barrier : Barrier edge old remembered)
    (w t : N) :
    Barrier (fun a b => edge a b ∨ (a = w ∧ b = t)) old
      (fun a => remembered a ∨ a = w) := by
  intro a b hab ha hb
  rcases hab with hab | ⟨rfl, _⟩
  · exact Or.inl (barrier a b hab ha hb)
  · exact Or.inr rfl

/-- Deleting edges, as unbinding a cell or emptying a slot does, keeps the
barrier. -/
theorem barrier_delete {edge edge' : Edges N} {old remembered : N → Prop}
    (barrier : Barrier edge old remembered)
    (sub : ∀ a b, edge' a b → edge a b) :
    Barrier edge' old remembered :=
  fun a b hab ha hb => barrier a b (sub a b hab) ha hb

/-- Writing an edge from an old object to a young one without remembering the
object breaks the barrier. -/
theorem barrier_unremembered_write_fails :
    ¬ Barrier (N := Bool) (fun a b => a = true ∧ b = false)
      (fun a => a = true) (fun _ => False) := by
  intro barrier
  exact barrier true false ⟨rfl, rfl⟩ rfl (by decide)

/-- Without the barrier the minor trace misses a reached young object: the
root `true` is old and reaches the young `false` through an unremembered
write, and no young root or remembered object reaches it. -/
theorem unremembered_write_misses :
    Reach (N := Bool) (fun a b => a = true ∧ b = false) true false ∧
      ¬ ∃ s, (((s = true) ∧ ¬ (s = true)) ∨ False) ∧
          YoungReach (fun a b => a = true ∧ b = false) (fun a => a = true)
            s false := by
  refine ⟨Reach.step ⟨rfl, rfl⟩ (Reach.refl false), ?_⟩
  rintro ⟨s, hs, _⟩
  rcases hs with ⟨h1, h2⟩ | h
  · exact h2 h1
  · exact h

end Mettapedia.Machines.RememberedSetTrace
