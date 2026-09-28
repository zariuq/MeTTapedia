import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Consistency.Structure

/-!
# Universes and type formers in the consistency model

A universe denotes the partial equivalence of its level: types with one
interpretation at that level at every world reached by a morphism. A term of
a universe is therefore a valid type, and the type formers build terms of a
universe from terms of universes:

* dependent function and pair types, whose partial equivalences are read
  from the interpretations of their domains and codomains at one level;
* identity types, which relate all terms when their endpoints are related.

Equal terms of a universe are types with one denotation, which gives
conversion, and cumulativity of universes gives inclusion of their partial
equivalences.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Impredicative
namespace Consistency

open Normalization

open UniverseLevel (LevelOrder)

variable {Head L : Type} [LevelOrder L] {M : Model Head L}

/-! ## The partial equivalence of a universe -/

/-- The partial equivalence of the universe at level `k`: types with one
interpretation at level `k` at every world reached by a morphism. -/
abbrev universeAt (M : Model Head L) (k : L) {n : Nat} (ξ : World M.reading n) : Rel Head n :=
  universeRel (InterpAt M k) ξ

theorem universeRel_levelsBelow {l k : L} (h : k < l) {n : Nat} (ξ : World M.reading n) :
    universeRel (levelsBelow M l k) ξ = universeAt M k ξ := by
  funext A B
  simp only [universeRel, levelsBelow_iff M h]

/-- A universe denotes the partial equivalence of its level. -/
theorem Den.sort {u : Head} (isUniverse : M.rules.isUniverse u) {n : Nat} (ξ : World M.reading n) :
    Den M ξ (.head u) (universeAt M (M.levels.level u) ξ) := by
  have interp := Interp.sort (M := M) (l := LevelOrder.succ (M.levels.level u))
    (below := levelsBelow M (LevelOrder.succ (M.levels.level u))) (ξ := ξ) (A := .head u) isUniverse
    (LevelOrder.lt_succ _) .refl
  rw [universeRel_levelsBelow (LevelOrder.lt_succ _)] at interp
  exact ⟨_, interp⟩

theorem Den.sort_inv (laws : M.Laws) {u : Head} (isUniverse : M.rules.isUniverse u)
    {n : Nat} {ξ : World M.reading n} {R : Rel Head n} (den : Den M ξ (.head u) R) :
    R = universeAt M (M.levels.level u) ξ := by
  obtain ⟨l, interp⟩ := den
  rcases InterpAt.head_inv laws interp with ⟨_, lt, rfl⟩ | ⟨notUniverse, _⟩
  · exact universeRel_levelsBelow lt ξ
  · exact absurd isUniverse notUniverse

/-- A universe is a valid type. -/
theorem ValidTy.sort {n : Nat} {Γ : Ctx Head n} {u : Head}
    (isUniverse : M.rules.isUniverse u) : ValidTy M Γ (.head u) :=
  fun {_ ξ _ _} _ => ⟨_, Den.sort isUniverse ξ, Den.sort isUniverse ξ⟩

/-- Related types of a universe have one interpretation at its level. -/
theorem universeAt.den {k : L} {n : Nat} {ξ : World M.reading n} {A B : Tm Head n}
    (h : universeAt M k ξ A B) : ∃ R, InterpAt M k ξ A R ∧ InterpAt M k ξ B R := by
  obtain ⟨R, hA, hB⟩ := h (Morph.id ξ)
  rw [rename_id] at hA hB
  exact ⟨R, hA, hB⟩

/-- Universes are cumulative. -/
theorem universeAt.mono {k k' : L} {n : Nat} (le : k ≤ k') {ξ : World M.reading n} {A B : Tm Head n}
    (h : universeAt M k ξ A B) : universeAt M k' ξ A B := by
  intro _ _ _ w
  obtain ⟨R, hA, hB⟩ := h w
  exact ⟨R, hA.cumul le, hB.cumul le⟩

/-- Related types of a universe stay related at every world reached by a
morphism. -/
theorem universeAt.rename {k : L} {n m : Nat} {ξ : World M.reading n} {ξ' : World M.reading m} {ρ : Ren n m}
    (w : Morph ξ ξ' ρ) {A B : Tm Head n} (h : universeAt M k ξ A B) :
    universeAt M k ξ' (Presentation.rename ρ A) (Presentation.rename ρ B) := by
  intro _ _ _ w'
  obtain ⟨R, hA, hB⟩ := h (w.comp' w')
  rw [rename_comp, rename_comp]
  exact ⟨R, hA, hB⟩

/-- Instances of two types under related substitutions are related in a
universe when they have one interpretation at its level under all related
substitutions. -/
theorem universeAt.of_interp (laws : M.Laws) {k : L} {n : Nat} {Γ : Ctx Head n} {T T' : Tm Head n}
    (here : ∀ {m : Nat} {ξ : World M.reading m} {σ σ' : Sub Head n m}, EqSubst M Γ ξ σ σ' →
      ∃ R, InterpAt M k ξ (Presentation.subst σ T) R ∧ InterpAt M k ξ (Presentation.subst σ' T') R)
    {m : Nat} {ξ : World M.reading m} {σ σ' : Sub Head n m} (e : EqSubst M Γ ξ σ σ') :
    universeAt M k ξ (Presentation.subst σ T) (Presentation.subst σ' T') := by
  intro _ _ _ w
  rw [rename_subst, rename_subst]
  exact here (EqSubst.rename laws e w)

/-- A term of a universe is related to itself at its level under related
substitutions. -/
theorem ValidTm.universe {n : Nat} {Γ : Ctx Head n} {A : Tm Head n} {u : Head}
    (valid : ValidTm M Γ A (.head u)) (isUniverse : M.rules.isUniverse u) {m : Nat}
    {ξ : World M.reading m} {σ σ' : Sub Head n m} (e : EqSubst M Γ ξ σ σ') :
    universeAt M (M.levels.level u) ξ (Presentation.subst σ A) (Presentation.subst σ' A) :=
  valid.2 e (Den.sort isUniverse ξ)

/-- Equal terms of a universe are related at its level under related
substitutions. -/
theorem ValidEq.universe {n : Nat} {Γ : Ctx Head n} {A B : Tm Head n} {u : Head}
    (valid : ValidEq M Γ A B (.head u)) (isUniverse : M.rules.isUniverse u) {m : Nat}
    {ξ : World M.reading m} {σ σ' : Sub Head n m} (e : EqSubst M Γ ξ σ σ') :
    universeAt M (M.levels.level u) ξ (Presentation.subst σ A) (Presentation.subst σ' B) :=
  valid.2.2 e (Den.sort isUniverse ξ)

/-- A term of a universe is a valid type. -/
theorem ValidTm.validTy {n : Nat} {Γ : Ctx Head n} {A : Tm Head n} {u : Head}
    (valid : ValidTm M Γ A (.head u)) (isUniverse : M.rules.isUniverse u) : ValidTy M Γ A := by
  intro _ ξ _ _ e
  obtain ⟨R, hA, hA'⟩ := universeAt.den (valid.universe isUniverse e)
  exact ⟨R, ⟨_, hA⟩, ⟨_, hA'⟩⟩

/-- A universe's relation between the instances of two types gives them one
denotation. -/
theorem ValidEq.den {n : Nat} {Γ : Ctx Head n} {A B : Tm Head n} {u : Head}
    (valid : ValidEq M Γ A B (.head u)) (isUniverse : M.rules.isUniverse u) {m : Nat}
    {ξ : World M.reading m} {σ σ' : Sub Head n m} (e : EqSubst M Γ ξ σ σ') :
    ∃ R, Den M ξ (Presentation.subst σ A) R ∧ Den M ξ (Presentation.subst σ' B) R := by
  obtain ⟨R, hA, hB⟩ := universeAt.den (valid.universe isUniverse e)
  exact ⟨R, ⟨_, hA⟩, ⟨_, hB⟩⟩

/-! ## Heads -/

/-- A head typed by a universe is a term of it. -/
theorem ValidTm.headType (laws : M.Laws) {n : Nat} {Γ : Ctx Head n} {h u : Head}
    (typing : M.rules.headTyping h u) : ValidTm M Γ (.head h) (.head u) := by
  have isUniverse := M.levels.ground_typing typing
  refine ⟨ValidTy.sort isUniverse, fun {_ ξ _ _} _ {R} den => ?_⟩
  rw [Den.sort_inv laws isUniverse den]
  intro _ ξ' _ _
  rcases M.levels.universe_decided h with hu | hu
  · have level := (M.levels.universe_typing hu typing).2
    have interp := Interp.sort (M := M) (l := M.levels.level u)
      (below := levelsBelow M (M.levels.level u)) (ξ := ξ') (A := .head h) hu
      (by rw [level]; exact LevelOrder.lt_succ _) .refl
    exact ⟨_, interp, interp⟩
  · have interp := Interp.ground (M := M) (l := M.levels.level u)
      (below := levelsBelow M (M.levels.level u)) (ξ := ξ') (A := .head h) hu .refl
    exact ⟨_, interp, interp⟩

end Consistency
end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
