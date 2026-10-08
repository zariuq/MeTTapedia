import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Card

/-!
# Surjective finite interpolation away from a retained support

Unused finite positions can cover a separately supplied finite target
without changing the values at retained positions. A second construction
factors an arbitrary reading of those positions through a finite carrier,
with a surjective first map. Neither construction assumes that retained
values are distinct.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory.FiniteSupportInterpolation

open Classical

universe u v w

/-- Reserve an independent position for every target value outside the support. -/
theorem surjective_extension {X : Type u} {Y : Type v} [Fintype X] [Fintype Y]
    [Nonempty Y] (retained : Finset X) (reading : X → Y)
    (room : retained.card + Fintype.card Y ≤ Fintype.card X) :
    ∃ result : X → Y, Function.Surjective result ∧
      ∀ value ∈ retained, result value = reading value := by
  have cardRoom : Fintype.card Y ≤ (retainedᶜ).card := by
    rw [Finset.card_compl]
    omega
  obtain ⟨reserve, inReserve⟩ :=
    Function.Embedding.exists_of_card_le_finset (α := Y) (s := retainedᶜ) cardRoom
  let result : X → Y := Function.extend reserve id reading
  refine ⟨result, ?_, ?_⟩
  · intro target
    exact ⟨reserve target, reserve.injective.extend_apply id reading target⟩
  · intro value member
    apply Function.extend_apply'
    rintro ⟨target, same⟩
    have outside := inReserve ⟨target, rfl⟩
    rw [same] at outside
    exact (Finset.mem_compl.mp outside) member

/-- A small intermediary names the retained positions independently; unused
positions still supply complete surjectivity onto that intermediary. -/
theorem factor_through {X : Type u} {Y : Type v} [Fintype X] [Nonempty Y]
    (retained : Finset X) (reading : X → Y) (capacity : Nat)
    (positive : 0 < capacity) (enoughNames : retained.card ≤ capacity)
    (room : retained.card + capacity ≤ Fintype.card X) :
    ∃ first : X → Fin capacity, ∃ second : Fin capacity → Y,
      Function.Surjective first ∧
        ∀ value ∈ retained, second (first value) = reading value := by
  have cardRoom : Fintype.card {value // value ∈ retained} ≤ Fintype.card (Fin capacity) := by
    simpa only [Fintype.card_coe, Fintype.card_fin] using enoughNames
  obtain ⟨names⟩ := Function.Embedding.nonempty_of_card_le cardRoom
  let seed : Fin capacity := ⟨0, positive⟩
  let _ : Nonempty (Fin capacity) := ⟨seed⟩
  let nameReading : X → Fin capacity :=
    Function.extend (fun value : {value // value ∈ retained} => value.val) names (fun _ => seed)
  let valueReading : Fin capacity → Y :=
    Function.extend names (fun value => reading value.val) (fun _ => Classical.choice inferInstance)
  obtain ⟨first, surjective, agrees⟩ :=
    surjective_extension retained nameReading (by simpa only [Fintype.card_fin] using room)
  refine ⟨first, valueReading, surjective, ?_⟩
  intro value member
  rw [agrees value member]
  have named : nameReading value = names ⟨value, member⟩ :=
    Subtype.val_injective.extend_apply names (fun _ => seed) ⟨value, member⟩
  rw [named]
  exact names.injective.extend_apply (fun value => reading value.val)
    (fun _ => Classical.choice inferInstance) ⟨value, member⟩

end Mettapedia.CategoryTheory.FiniteSupportInterpolation
