import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Domain.Projections

/-!
# Controls for the compact elements, their typing and the projections

Positive and negative instances of each construction of the domain:

* the order: a successor of the least element is below a successor of zero,
  and not conversely; the step-function order is pointwise, so a constant
  function is above a function defined only at zero, and not conversely;
* the lazy constructors: a function whose outputs are all the least element,
  and the pair of least elements, are the least element; the strict ones are
  not: `Π ⊥ ⊥`, `S ⊥` and reflexivity at the least element are above it and
  different from it;
* disjointness of constructors: the universe is not below `Π ⊥ ⊥`, and `Π ⊥ ⊥`
  is not below `Σ ⊥ ⊥`;
* typing: the universe is an element of itself, zero is not a type; the
  identity on zero is a function from the numbers to the numbers, and a
  function defined on the universe is not; reflexivity at zero is an element of
  the identity type from zero to zero, and not of the one from zero to a
  successor;
* the projection onto the numbers keeps zero, and the projection onto the
  universe does not.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Impredicative
namespace Domain
namespace Controls

open Elem

/-! ## The order -/

theorem succ_bot_le_succ_zero : succ [] ⊑ succ zero := by
  rw [succ_le_iff]
  exact ⟨List.mem_cons_self, Le.nil _⟩

theorem not_succ_zero_le_succ_bot : ¬ succ zero ⊑ succ [] := by
  rw [succ_le_iff, pred_succ]
  rintro ⟨-, h⟩
  have := h _ List.mem_cons_self
  simp [ent_tag, hasTag] at this

/-- A constant function is above the function defined only at zero. -/
theorem partial_le_constant : lam [(zero, zero)] ⊑ lam [([], zero)] := by
  rw [lam_le_iff]
  intro p hp
  rw [List.mem_singleton.1 hp]
  intro t ht
  rw [List.mem_singleton.1 ht]
  simp [app_lam, stepApp, ent_tag, hasTag, zero, List.filter_cons]

theorem not_constant_le_partial : ¬ lam [([], zero)] ⊑ lam [(zero, zero)] := by
  rw [lam_le_iff]
  intro h
  have := h _ List.mem_cons_self _ List.mem_cons_self
  simp [app_lam, stepApp, ent_tag, hasTag, zero] at this

/-! ## Lazy and strict constructors -/

theorem lam_of_bot_outputs : Equiv (lam [(univ, [])]) [] := by
  refine ⟨?_, Le.nil _⟩
  intro t ht
  rw [lam, List.map_singleton, List.mem_singleton] at ht
  rw [ht, ent_fn]
  rfl

theorem pair_bot_bot : pair [] [] = [] := rfl

theorem pi_bot_not_bot : ¬ former .pi [] [] ⊑ [] := by
  intro h
  have := h _ List.mem_cons_self
  simp [ent_tag, hasTag] at this

theorem succ_bot_not_bot : ¬ succ [] ⊑ [] := by
  intro h
  have := h _ List.mem_cons_self
  simp [ent_tag, hasTag] at this

theorem refl_bot_not_bot : ¬ refl [] ⊑ [] := by
  intro h
  have := h _ List.mem_cons_self
  simp [ent_tag, hasTag] at this

/-! ## Disjointness -/

theorem univ_not_le_pi : ¬ univ ⊑ former .pi [] [] := by
  intro h
  have := h _ List.mem_cons_self
  simp [ent_tag, hasTag, former] at this

theorem pi_not_le_sigma : ¬ former .pi [] [] ⊑ former .sigma [] [] := by
  intro h
  have := h _ List.mem_cons_self
  simp [ent_tag, hasTag, former] at this

/-! ## Typing -/

theorem univ_in_univ : Ty univ univ := ty_univ_univ

theorem zero_not_type : ¬ Ty zero univ := by
  intro h
  have := tyTok_tag_zero.1 (h _ List.mem_cons_self)
  simp [univ] at this

/-- The type of functions from the numbers to the numbers. -/
def natToNat : List Tok := former .pi nat [([], nat)]

theorem natToNat_pi : Tok.tag .pi ∈ natToNat := List.mem_cons_self

theorem nat_mem_dom : Tok.tag .nat ∈ args .pi 0 natToNat := by
  simp [natToNat, former, nat]

theorem nat_mem_fam (X : List Tok) : Tok.tag .nat ∈ fnApp .pi natToNat X := by
  simp [natToNat, former, fnApp, nat]

/-- The function sending zero to zero is a function from the numbers to the
numbers. -/
theorem zero_to_zero_typed : Ty (lam [(zero, zero)]) natToNat := by
  rw [ty_lam natToNat_pi]
  intro p hp
  rw [List.mem_singleton.1 hp]
  exact ⟨ty_zero nat_mem_dom, ty_zero (nat_mem_fam _)⟩

/-- A function defined on the universe is not a function from the numbers. -/
theorem univ_input_untyped : ¬ Ty (lam [(univ, univ)]) natToNat := by
  rw [ty_lam natToNat_pi]
  intro h
  have := (h _ List.mem_cons_self).1 _ List.mem_cons_self
  rw [tyTok_tag_former (k := .univ) trivial] at this
  rcases this with h | h <;> simp [natToNat, former, nat] at h

theorem refl_zero_typed : Ty (refl zero) (ident nat zero zero) := by
  rw [ty_refl (show Tok.tag .ident ∈ ident nat zero zero from List.mem_cons_self)]
  refine ⟨ty_zero (by simp [ident, nat]), ?_, ?_⟩ <;>
  · intro t ht
    rw [List.mem_singleton.1 ht]
    simp [ident, zero, nat, ent_tag, hasTag]

theorem refl_zero_not_to_succ : ¬ Ty (refl zero) (ident nat zero (succ [])) := by
  rw [ty_refl (show Tok.tag .ident ∈ ident nat zero (succ []) from List.mem_cons_self)]
  rintro ⟨-, -, h⟩
  have := h _ List.mem_cons_self
  simp [ident, zero, succ, nat, ent_tag, hasTag] at this

/-! ## Projections -/

theorem proj_nat_keeps_zero : (Ideal.proj nat (Ideal.principal zero)).Mem (.tag .zero) :=
  Ideal.subset_closure ⟨ent_of_mem List.mem_cons_self, tyTok_tag_zero.2 List.mem_cons_self⟩

theorem proj_univ_drops_zero : ¬ (Ideal.proj univ (Ideal.principal zero)).Mem (.tag .zero) := by
  rintro ⟨v, hv, ht⟩
  rw [ent_tag, hasTag_iff] at ht
  have := tyTok_tag_zero.1 (hv _ ht).2
  simp [univ] at this

end Controls
end Domain
end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
