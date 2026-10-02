import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Finset.Image
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Fintype.EquivFin

/-!
# Label sequences and their doors

A simplex with `n + 1` vertices carries labels in `{0, …, n}`, one of which
is distinguished. A vertex is a *door* when the other `n` vertices carry
exactly the `n` labels that are not distinguished.

The count of doors detects whether all labels occur:

* if every label occurs, there is exactly one door (the vertex with the
  distinguished label);
* otherwise there are none or two.

This is the local step of Sperner's lemma and of Kuhn's lemma (Kuhn 1960,
"Some combinatorial lemmas in topology").
-/

set_option autoImplicit false

namespace Mettapedia.Combinatorics.Kuhn

open Finset

variable {n : ℕ}

/-- The vertices other than `k` carry exactly the labels other than `top`. -/
def IsDoor (labels : Fin (n + 1) → Fin (n + 1)) (top k : Fin (n + 1)) : Prop :=
  (univ.erase k).image labels = univ.erase top

instance (labels : Fin (n + 1) → Fin (n + 1)) (top : Fin (n + 1)) :
    DecidablePred (IsDoor labels top) := fun k => by
  unfold IsDoor
  infer_instance

/-- The doors of a label sequence. -/
def doors (labels : Fin (n + 1) → Fin (n + 1)) (top : Fin (n + 1)) : Finset (Fin (n + 1)) :=
  univ.filter (IsDoor labels top)

theorem mem_doors {labels : Fin (n + 1) → Fin (n + 1)} {top k : Fin (n + 1)} :
    k ∈ doors labels top ↔ IsDoor labels top k := by
  simp [doors]

/-- Being a door depends only on the labels of the other vertices. -/
theorem IsDoor.congr {labels labels' : Fin (n + 1) → Fin (n + 1)} {top k : Fin (n + 1)}
    (same : ∀ vertex, vertex ≠ k → labels' vertex = labels vertex) :
    IsDoor labels' top k ↔ IsDoor labels top k := by
  unfold IsDoor
  rw [image_congr fun vertex member => same vertex (ne_of_mem_erase (mem_coe.mp member))]

/-- At a door the labels of the other vertices are pairwise different. -/
theorem IsDoor.injOn {labels : Fin (n + 1) → Fin (n + 1)} {top k : Fin (n + 1)}
    (door : IsDoor labels top k) : Set.InjOn labels ↑(univ.erase k) := by
  apply card_image_iff.mp
  rw [door, card_erase_of_mem (mem_univ _), card_erase_of_mem (mem_univ _)]

/-- If every label occurs, the only door is the vertex with the distinguished
label. -/
theorem doors_of_surjective {labels : Fin (n + 1) → Fin (n + 1)} (top : Fin (n + 1))
    (surjective : Function.Surjective labels) : (doors labels top).card = 1 := by
  have injective : Function.Injective labels := Finite.injective_iff_surjective.mpr surjective
  obtain ⟨topVertex, isTop⟩ := surjective top
  have only : doors labels top = {topVertex} := by
    ext k
    rw [mem_doors, mem_singleton]
    constructor
    · intro door
      by_contra different
      have member : labels topVertex ∈ (univ.erase k).image labels :=
        mem_image_of_mem _ (mem_erase.mpr ⟨fun same => different same.symm, mem_univ _⟩)
      rw [door, isTop] at member
      exact (notMem_erase _ _) member
    · rintro rfl
      unfold IsDoor
      rw [image_erase injective, image_univ_of_surjective surjective, isTop]
  rw [only, card_singleton]

/-- If some label does not occur, the doors come in pairs. -/
theorem even_card_doors_of_not_surjective {labels : Fin (n + 1) → Fin (n + 1)}
    (top : Fin (n + 1)) (notSurjective : ¬Function.Surjective labels) :
    Even (doors labels top).card := by
  by_cases empty : doors labels top = ∅
  · rw [empty, card_empty]
    exact ⟨0, rfl⟩
  obtain ⟨k, member⟩ := nonempty_iff_ne_empty.mpr empty
  have door : IsDoor labels top k := mem_doors.mp member
  -- the label of `k` is not the distinguished one, so another vertex carries it
  have notTop : labels k ≠ top := by
    intro isTop
    apply notSurjective
    intro label
    by_cases distinguished : label = top
    · exact ⟨k, by rw [isTop, distinguished]⟩
    · have : label ∈ (univ.erase k).image labels := by
        rw [door]
        exact mem_erase.mpr ⟨distinguished, mem_univ _⟩
      obtain ⟨vertex, _, same⟩ := mem_image.mp this
      exact ⟨vertex, same⟩
  have repeated : labels k ∈ (univ.erase k).image labels := by
    rw [door]
    exact mem_erase.mpr ⟨notTop, mem_univ _⟩
  obtain ⟨j, jMember, sameLabel⟩ := mem_image.mp repeated
  have different : j ≠ k := (mem_erase.mp jMember).1
  -- the other vertex with that label is the second door
  have doorJ : IsDoor labels top j := by
    unfold IsDoor at door ⊢
    rw [← door]
    ext label
    simp only [mem_image, mem_erase, mem_univ, and_true]
    constructor
    · rintro ⟨vertex, notJ, rfl⟩
      by_cases isK : vertex = k
      · exact ⟨j, different, by rw [sameLabel, isK]⟩
      · exact ⟨vertex, isK, rfl⟩
    · rintro ⟨vertex, notK, rfl⟩
      by_cases isJ : vertex = j
      · exact ⟨k, fun same => different same.symm, by rw [isJ, sameLabel]⟩
      · exact ⟨vertex, isJ, rfl⟩
  -- and there is no third one
  have only : doors labels top = {k, j} := by
    ext vertex
    rw [mem_doors, mem_insert, mem_singleton]
    constructor
    · intro doorVertex
      by_contra neither
      rw [not_or] at neither
      have kIn : k ∈ (↑(univ.erase vertex) : Set (Fin (n + 1))) :=
        mem_coe.mpr (mem_erase.mpr ⟨fun same => neither.1 same.symm, mem_univ _⟩)
      have jIn : j ∈ (↑(univ.erase vertex) : Set (Fin (n + 1))) :=
        mem_coe.mpr (mem_erase.mpr ⟨fun same => neither.2 same.symm, mem_univ _⟩)
      exact different (doorVertex.injOn jIn kIn sameLabel)
    · rintro (rfl | rfl)
      · exact door
      · exact doorJ
  rw [only, card_pair (fun same => different same.symm)]
  exact even_two

/-- **The number of doors is odd exactly when every label occurs.** -/
theorem odd_card_doors_iff (labels : Fin (n + 1) → Fin (n + 1)) (top : Fin (n + 1)) :
    Odd (doors labels top).card ↔ Function.Surjective labels := by
  constructor
  · intro odd
    by_contra notSurjective
    exact (Nat.not_odd_iff_even.mpr (even_card_doors_of_not_surjective top notSurjective)) odd
  · intro surjective
    rw [doors_of_surjective top surjective]
    exact odd_one

end Mettapedia.Combinatorics.Kuhn
