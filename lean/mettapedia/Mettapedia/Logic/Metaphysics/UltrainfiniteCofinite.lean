import Mathlib.Order.Filter.Cofinite
import Mettapedia.Logic.Metaphysics.UltrainfinitismCore

/-!
# The effable core of the free One: the cofinite filter

An ultrafilter is **free** (`IsFree`) when it is the principal ultrafilter of no point; for
ultrafilters this is the same as refining the cofinite filter (`isFree_iff_le_cofinite`), and the
same as containing no finite set (`isFree_iff_finite_notMem`).

* **The cofinite filter is the meet of the free ultrafilters**: a set is cofinite exactly when every
  free ultrafilter contains it (`mem_cofinite_iff_forall_free`). In the order of `Filter`, where a
  finer filter is smaller, the meet of set systems is the supremum (`iSup_free_eq_cofinite`).
* **What every free perspective affirms is what holds at all but finitely many coordinates**
  (`forall_free_ultraTrue_iff`); **some free perspective affirms what holds at infinitely many**
  (`exists_free_ultraTrue_iff`).
* **The free dial** (`freeOpen_iff`): the free perspectives disagree about a family exactly when
  it holds at infinitely many coordinates and fails at infinitely many. Whatever is not decided
  cofinitely depends on the choice of a free ultrafilter.

No hypothesis on the index is needed. On a finite index there is no free ultrafilter
(`not_exists_free_of_finite`) and every set is cofinite, so both sides are trivially true; on an
infinite index free ultrafilters exist (`isFree_hyperfilter`) and the statements have content.

**Controls on `ℕ`.** "nonzero" is affirmed by every free perspective (`forall_free_ne_zero`); "is
zero" by none (`not_exists_free_eq_zero`); "is even" is open among them (`freeOpen_even`).

The free ultrafilters themselves are given by choice (`Filter.hyperfilter` is `Ultrafilter.of`);
the cofinite filter is defined without it. The meet is the effable part of the indexed One.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.Metaphysics.Ultrainfinite

open Filter

universe u

variable {I : Type u}

/-- **A free ultrafilter**: the principal ultrafilter of no point. -/
def IsFree (U : Ultrafilter I) : Prop := ∀ i, U ≠ pure i

theorem isFree_iff_le_cofinite {U : Ultrafilter I} : IsFree U ↔ (U : Filter I) ≤ cofinite := by
  constructor
  · intro free
    rcases U.le_cofinite_or_eq_pure with le | ⟨i, rfl⟩
    · exact le
    · exact absurd rfl (free i)
  · intro le i same
    have away : ({i}ᶜ : Set I) ∈ U := le_cofinite_iff_compl_singleton_mem.mp le i
    rw [same, Ultrafilter.mem_pure] at away
    exact away rfl

theorem isFree_iff_finite_notMem {U : Ultrafilter I} : IsFree U ↔ ∀ s : Set I, s.Finite → s ∉ U := by
  rw [isFree_iff_le_cofinite]
  constructor
  · intro le s finite member
    exact Ultrafilter.compl_notMem_iff.mpr member (le finite.compl_mem_cofinite)
  · intro none s cofiniteSet
    rw [mem_cofinite] at cofiniteSet
    have := none _ cofiniteSet
    rwa [Ultrafilter.compl_notMem_iff] at this

theorem isFree_hyperfilter [Infinite I] : IsFree (hyperfilter I) :=
  isFree_iff_le_cofinite.mpr hyperfilter_le_cofinite

theorem not_isFree_pure (i : I) : ¬ IsFree (pure i : Ultrafilter I) :=
  fun free => free i rfl

/-- On a finite index every ultrafilter is principal. -/
theorem not_exists_free_of_finite [Finite I] : ¬ ∃ U : Ultrafilter I, IsFree U := by
  rintro ⟨U, free⟩
  obtain ⟨i, rfl⟩ := U.eq_pure_of_finite
  exact not_isFree_pure i free

theorem exists_free_iff_infinite : (∃ U : Ultrafilter I, IsFree U) ↔ Infinite I := by
  constructor
  · rintro ⟨U, free⟩
    by_contra notInfinite
    have : Finite I := not_infinite_iff_finite.mp notInfinite
    exact not_exists_free_of_finite ⟨U, free⟩
  · intro
    exact ⟨_, isFree_hyperfilter⟩

/-! ## The meet -/

/-- **The cofinite filter is the meet of the free ultrafilters**: a set is cofinite exactly when
every free ultrafilter contains it. -/
theorem mem_cofinite_iff_forall_free {s : Set I} :
    s ∈ cofinite ↔ ∀ U : Ultrafilter I, IsFree U → s ∈ U := by
  rw [mem_iff_ultrafilter]
  exact forall_congr' fun U => imp_congr_left isFree_iff_le_cofinite.symm

/-- The same statement in the order of `Filter`, where the meet of set systems is the supremum. -/
theorem iSup_free_eq_cofinite :
    ⨆ (U : Ultrafilter I) (_ : IsFree U), (U : Filter I) = cofinite := by
  rw [← iSup_ultrafilter_le_eq (cofinite : Filter I)]
  exact iSup_congr fun U => iSup_congr_Prop isFree_iff_le_cofinite fun _ => rfl

/-- **What every free perspective affirms is what holds at all but finitely many coordinates.** -/
theorem forall_free_ultraTrue_iff (P : I → Prop) :
    (∀ U : Ultrafilter I, IsFree U → UltraTrue U P) ↔ {i | ¬ P i}.Finite := by
  rw [← eventually_cofinite]
  exact mem_cofinite_iff_forall_free.symm

/-- **Some free perspective affirms what holds at infinitely many coordinates.** -/
theorem exists_free_ultraTrue_iff (P : I → Prop) :
    (∃ U : Ultrafilter I, IsFree U ∧ UltraTrue U P) ↔ {i | P i}.Infinite := by
  have dual := forall_free_ultraTrue_iff (fun i => ¬ P i)
  simp only [not_not] at dual
  rw [Set.Infinite, ← dual]
  constructor
  · rintro ⟨U, free, holds⟩ never
    exact (ultraTrue_not_iff U P).mpr (never U free) holds
  · intro notAll
    simp only [not_forall, exists_prop] at notAll
    obtain ⟨U, free, notNever⟩ := notAll
    refine ⟨U, free, ?_⟩
    have holds := (ultraTrue_not_iff U _).mp notNever
    simpa only [not_not] using holds

/-- **The free dial**: free perspectives disagree about a family exactly when it holds at
infinitely many coordinates and fails at infinitely many. -/
theorem freeOpen_iff (P : I → Prop) :
    (∃ U V : Ultrafilter I, IsFree U ∧ IsFree V ∧ UltraTrue U P ∧ ¬ UltraTrue V P) ↔
      {i | P i}.Infinite ∧ {i | ¬ P i}.Infinite := by
  rw [← exists_free_ultraTrue_iff, ← exists_free_ultraTrue_iff]
  constructor
  · rintro ⟨U, V, freeU, freeV, yes, no⟩
    exact ⟨⟨U, freeU, yes⟩, ⟨V, freeV, (ultraTrue_not_iff V P).mp no⟩⟩
  · rintro ⟨⟨U, freeU, yes⟩, ⟨V, freeV, no⟩⟩
    exact ⟨U, V, freeU, freeV, yes, (ultraTrue_not_iff V P).mpr no⟩

/-! ## Controls on `ℕ` -/

theorem forall_free_ne_zero :
    ∀ U : Ultrafilter ℕ, IsFree U → UltraTrue U (fun n => n ≠ 0) :=
  (forall_free_ultraTrue_iff _).mpr ((Set.finite_singleton 0).subset fun _ h => by simpa using h)

theorem not_exists_free_eq_zero :
    ¬ ∃ U : Ultrafilter ℕ, IsFree U ∧ UltraTrue U (fun n => n = 0) := fun h =>
  (exists_free_ultraTrue_iff _).mp h ((Set.finite_singleton 0).subset fun _ h => by simpa using h)

theorem infinite_setOf_even : {n : ℕ | Even n}.Infinite :=
  Set.infinite_of_forall_exists_gt fun n => ⟨2 * n + 2, ⟨n + 1, by ring⟩, by omega⟩

theorem infinite_setOf_not_even : {n : ℕ | ¬ Even n}.Infinite :=
  Set.infinite_of_forall_exists_gt fun n =>
    ⟨2 * n + 1, Nat.not_even_iff_odd.mpr ⟨n, rfl⟩, by omega⟩

/-- "Even" is open among the free perspectives: one affirms it and another denies it. -/
theorem freeOpen_even :
    ∃ U V : Ultrafilter ℕ, IsFree U ∧ IsFree V ∧ UltraTrue U (fun n => Even n) ∧
      ¬ UltraTrue V (fun n => Even n) :=
  (freeOpen_iff _).mpr ⟨infinite_setOf_even, infinite_setOf_not_even⟩

end Mettapedia.Logic.Metaphysics.Ultrainfinite

namespace Mettapedia.Logic.Metaphysics.Ultrainfinite

#print axioms isFree_iff_le_cofinite
#print axioms isFree_iff_finite_notMem
#print axioms isFree_hyperfilter
#print axioms not_exists_free_of_finite
#print axioms exists_free_iff_infinite
#print axioms mem_cofinite_iff_forall_free
#print axioms iSup_free_eq_cofinite
#print axioms forall_free_ultraTrue_iff
#print axioms exists_free_ultraTrue_iff
#print axioms freeOpen_iff
#print axioms forall_free_ne_zero
#print axioms not_exists_free_eq_zero
#print axioms freeOpen_even

end Mettapedia.Logic.Metaphysics.Ultrainfinite
