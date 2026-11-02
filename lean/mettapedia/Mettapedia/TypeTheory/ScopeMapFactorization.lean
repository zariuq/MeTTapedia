import Mathlib.Data.Finset.Sort
import Mathlib.Tactic

/-!
# Finite scope maps separate support from parameter order

Every injective map of finite scopes factors into a permutation of its input
slots followed by an order-preserving embedding. The selected ordered image
and the input-slot map are explicit finite constructions. Repeated arguments
do not have such a factorization: contraction is a further kind of map, not
an order-preserving inclusion with different punctuation.

These are laws of finite scope maps. Typed dependent contexts additionally
require preservation of their declarations and dependencies.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ScopeMapFactorization

variable {n m : ℕ}

def support (f : Fin n → Fin m) : Finset (Fin m) := Finset.univ.image f

theorem mem_support (f : Fin n → Fin m) (i : Fin n) : f i ∈ support f := by
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩

theorem card_support (f : Fin n → Fin m) (injective : Function.Injective f) :
    (support f).card = n := by
  rw [support, Finset.card_image_of_injective _ injective]
  simp

/-- The chosen variables in their ambient scope order. -/
def ordered (f : Fin n → Fin m) (injective : Function.Injective f) : Fin n ↪o Fin m :=
  (support f).orderEmbOfFin (card_support f injective)

/-- Which slot in the ordered support the original parameter occupies. -/
def permutationIndex (f : Fin n → Fin m) (injective : Function.Injective f) (i : Fin n) : Fin n :=
  ((support f).orderIsoOfFin (card_support f injective)).symm ⟨f i, mem_support f i⟩

theorem factor (f : Fin n → Fin m) (injective : Function.Injective f) (i : Fin n) :
    f i = ordered f injective (permutationIndex f injective i) := by
  simp [ordered, permutationIndex, Finset.orderEmbOfFin]

theorem permutationIndex_injective (f : Fin n → Fin m) (injective : Function.Injective f) :
    Function.Injective (permutationIndex f injective) := by
  intro i j same
  apply injective
  rw [factor f injective i, factor f injective j, same]

theorem permutationIndex_bijective (f : Fin n → Fin m) (injective : Function.Injective f) :
    Function.Bijective (permutationIndex f injective) :=
  ⟨permutationIndex_injective f injective,
    Finite.surjective_of_injective (permutationIndex_injective f injective)⟩

theorem factor_unique (f : Fin n → Fin m) (injective : Function.Injective f)
    (inclusion : Fin n ↪o Fin m) (permutation : Equiv.Perm (Fin n))
    (factored : ∀ i, f i = inclusion (permutation i)) :
    inclusion = ordered f injective ∧ ∀ i, permutation i = permutationIndex f injective i := by
  have contained : ∀ j, inclusion j ∈ support f := by
    intro j
    obtain ⟨i, rfl⟩ := permutation.surjective j
    rw [← factored i]
    exact mem_support f i
  have orderedSame : inclusion = ordered f injective :=
    Finset.orderEmbOfFin_unique' (card_support f injective) contained
  refine ⟨orderedSame, ?_⟩
  intro i
  apply (ordered f injective).injective
  calc
    ordered f injective (permutation i) = inclusion (permutation i) := by rw [orderedSame]
    _ = f i := (factored i).symm
    _ = ordered f injective (permutationIndex f injective i) := factor f injective i

/-- Permutation plus ordered inclusion covers exactly the injective scope
maps. The construction does not assert validity of dependent exchange. -/
theorem factors_iff_injective (f : Fin n → Fin m) :
    (∃ (inclusion : Fin n ↪o Fin m) (permutation : Equiv.Perm (Fin n)),
      ∀ i, f i = inclusion (permutation i)) ↔ Function.Injective f := by
  constructor
  · rintro ⟨inclusion, permutation, factored⟩ i j same
    apply permutation.injective
    apply inclusion.injective
    simpa only [← factored] using same
  · intro injective
    let permutation := Equiv.ofBijective (permutationIndex f injective)
      (permutationIndex_bijective f injective)
    exact ⟨ordered f injective, permutation, factor f injective⟩

namespace Controls

def swap (i : Fin 2) : Fin 2 := if i = 0 then 1 else 0

theorem swap_involutive : Function.Involutive swap := by
  intro i
  fin_cases i <;> decide

theorem swap_has_factorization :
    ∃ (inclusion : Fin 2 ↪o Fin 2) (permutation : Equiv.Perm (Fin 2)),
      ∀ i, swap i = inclusion (permutation i) :=
  (factors_iff_injective swap).mpr swap_involutive.injective

theorem swap_is_not_order_preserving : ¬StrictMono swap := by
  intro increasing
  have impossible := increasing (show (0 : Fin 2) < 1 by decide)
  norm_num [swap] at impossible

theorem repeated_arguments_are_not_injective :
    ¬Function.Injective (fun _ : Fin 2 => (0 : Fin 1)) := by
  intro injective
  have same := injective (a₁ := (0 : Fin 2)) (a₂ := 1) rfl
  norm_num at same

theorem repeated_arguments_need_more_than_exchange :
    ¬∃ (inclusion : Fin 2 ↪o Fin 1) (permutation : Equiv.Perm (Fin 2)),
      ∀ i, (0 : Fin 1) = inclusion (permutation i) := by
  rw [factors_iff_injective]
  exact repeated_arguments_are_not_injective

end Controls
end Mettapedia.TypeTheory.ScopeMapFactorization
