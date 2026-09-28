import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Conversion.Structure

/-!
# Universes in the conversion model

A universe denotes the pack of its level: types with one pack and one shape at
that level at every world reached by a morphism, realized by the types, the
terms that reach the weak-head form of a type and that the generic equality
relates at the universe (`ECand.types`). So a term of a universe is a valid
type: related valuations give its instances one pack, and its realizer
instances are related as types (`ValidTmN.validTy`). Equal terms of a universe
have one pack and one shape under related valuations
(`ValidEqN.universe_shape`).

A head typed by a universe is a term of it: on the value side a universe is of
one shape with itself by its level, and any other head is a leaf; on the
realizer side a head is a weak-head form of a type, and the generic equality
relates heads that are the same up to the package's head equality
(`types_head`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Impredicative
namespace Conversion

open Normalization (tailSub CtxFormed IsType)
open UniverseLevel (LevelOrder)
open Consistency (World Morph)
open ValueSide (universeAt)

variable {Head L : Type} [LevelOrder L]

/-! ## Heads on the realizer side -/

/-- Two heads that are the same up to the package's head equality, typed at a
universe, are related there by the types. -/
theorem types_head {T : RealizerSide Head L} {m : Nat} {Δ : Ctx Head m} {h h' v : Head}
    (same : h = h' ∨ T.R.headEq h h') (typing : Typed T.R Δ (.head h) (.head v))
    (typing' : Typed T.R Δ (.head h') (.head v)) (hv : T.R.isUniverse v) :
    (ECand.types T).rel Δ (.head v) (.head h) (.head h') :=
  ⟨⟨typing, typing', T.laws.convTm_head same typing typing' hv⟩,
    ⟨_, .refl typing, .inl ⟨h, rfl⟩⟩, ⟨_, .refl typing', .inl ⟨h', rfl⟩⟩⟩

/-- A universe of the realizer side is related to itself as a type. -/
theorem TypesRel.head {T : RealizerSide Head L} {m : Nat} {Δ : Ctx Head m} {u : Head}
    (hu : T.R.isUniverse u) : TypesRel T Δ (.head u) (.head u) := by
  obtain ⟨v, hv, typing, -⟩ := T.levels.successor hu
  exact ⟨v, hv, types_head (.inl rfl) (.headType typing) (.headType typing) hv⟩

variable {M : NModel Head L}

/-! ## The pack of a universe -/

/-- A universe is a valid type. -/
theorem ValidTyN.sort {n : Nat} {Γ : Ctx Head n} {u : Head} (hu : M.rules.isUniverse u)
    (hu' : M.side.R.isUniverse u) : ValidTyN M Γ (.head u) :=
  fun {_ _ ξ _ _ _ _ _} _ => ⟨_, ValueSide.DenS.sort (V := M.value) hu ξ,
    ValueSide.DenS.sort (V := M.value) hu ξ, TypesRel.head hu'⟩

/-! ## Terms of universes -/

/-- A term of a universe is related to itself at its level under related
valuations, and its realizer instances are related there by the types. -/
theorem ValidTmN.universe {n : Nat} {Γ : Ctx Head n} {A : Tm Head n} {u : Head}
    (valid : ValidTmN M Γ A (.head u)) (isUniverse : M.rules.isUniverse u) {m r : Nat}
    {ξ : World M.reading m} {σ σ' : Sub Head n m} {Δ : Ctx Head r} {ς ς' : Sub Head n r}
    (e : EqSubstN M Γ ξ σ σ' Δ ς ς') :
    (universeAt M.value (M.levels.level u) ξ).rel (Presentation.subst σ A)
        (Presentation.subst σ' A) ∧
      (ECand.types M.side).rel Δ (.head u) (Presentation.subst ς A) (Presentation.subst ς' A) :=
  valid.2 e (ValueSide.DenS.sort (V := M.value) isUniverse ξ)

/-- Equal terms of a universe are related at its level under related valuations,
and so are their realizer instances. -/
theorem ValidEqN.universe {n : Nat} {Γ : Ctx Head n} {A B : Tm Head n} {u : Head}
    (valid : ValidEqN M Γ A B (.head u)) (isUniverse : M.rules.isUniverse u) {m r : Nat}
    {ξ : World M.reading m} {σ σ' : Sub Head n m} {Δ : Ctx Head r} {ς ς' : Sub Head n r}
    (e : EqSubstN M Γ ξ σ σ' Δ ς ς') :
    (universeAt M.value (M.levels.level u) ξ).rel (Presentation.subst σ A)
        (Presentation.subst σ' B) ∧
      (ECand.types M.side).rel Δ (.head u) (Presentation.subst ς A) (Presentation.subst ς' B) :=
  valid.2.2 e (ValueSide.DenS.sort (V := M.value) isUniverse ξ)

/-- **Validly equal terms of a universe have one pack and one shape** at its
level under related valuations. -/
theorem ValidEqN.universe_shape {n : Nat} {Γ : Ctx Head n} {A B : Tm Head n} {u : Head}
    (valid : ValidEqN M Γ A B (.head u)) (isUniverse : M.rules.isUniverse u) {m r : Nat}
    {ξ : World M.reading m} {σ σ' : Sub Head n m} {Δ : Ctx Head r} {ς ς' : Sub Head n r}
    (e : EqSubstN M Γ ξ σ σ' Δ ς ς') :
    ∃ P, ValueSide.InterpAt M.value (M.levels.level u) ξ (Presentation.subst σ A) P ∧
      ValueSide.InterpAt M.value (M.levels.level u) ξ (Presentation.subst σ' B) P ∧
      ValueSide.Shape M.value (ValueSide.InterpAt M.value (M.levels.level u)) .pair ξ
        (Presentation.subst σ A) (Presentation.subst σ' B) :=
  ValueSide.universeAt.den (valid.universe isUniverse e).1

/-- A term of a universe is a valid type. -/
theorem ValidTmN.validTy {n : Nat} {Γ : Ctx Head n} {A : Tm Head n} {u : Head}
    (valid : ValidTmN M Γ A (.head u)) (isUniverse : M.rules.isUniverse u)
    (isUniverse' : M.side.R.isUniverse u) : ValidTyN M Γ A := fun e => by
  obtain ⟨rel, types⟩ := valid.universe isUniverse e
  obtain ⟨P, hA, hA', -⟩ := ValueSide.universeAt.den rel
  exact ⟨P, ⟨_, hA⟩, ⟨_, hA'⟩, u, isUniverse', types⟩

/-- Validly equal terms of a universe have one pack under related valuations. -/
theorem ValidEqN.den {n : Nat} {Γ : Ctx Head n} {A B : Tm Head n} {u : Head}
    (valid : ValidEqN M Γ A B (.head u)) (isUniverse : M.rules.isUniverse u) {m r : Nat}
    {ξ : World M.reading m} {σ σ' : Sub Head n m} {Δ : Ctx Head r} {ς ς' : Sub Head n r}
    (e : EqSubstN M Γ ξ σ σ' Δ ς ς') :
    ∃ P : NPack M m, DenN M ξ (Presentation.subst σ A) P ∧ DenN M ξ (Presentation.subst σ' B) P := by
  obtain ⟨P, hA, hB, -⟩ := valid.universe_shape isUniverse e
  exact ⟨P, ⟨_, hA⟩, ⟨_, hB⟩⟩

/-! ## Heads -/

/-- A head typed by a universe is a term of it. -/
theorem ValidTmN.headType (laws : M.Laws) {n : Nat} {Γ : Ctx Head n} {h u : Head}
    (typing : M.rules.headTyping h u) (typing' : M.side.R.headTyping h u) :
    ValidTmN M Γ (.head h) (.head u) := by
  have isUniverse := M.levels.ground_typing typing
  have isUniverse' := M.side.levels.ground_typing typing'
  refine ⟨ValidTyN.sort isUniverse isUniverse', fun {_ _ ξ _ _ Δ _ _} e {P} den => ?_⟩
  rw [ValueSide.DenS.sort_inv laws.value isUniverse den]
  refine ⟨fun {_ ξ' _} _ => ?_, types_head (.inl rfl) (.headType typing') (.headType typing')
    isUniverse'⟩
  obtain ⟨Q, hQ, s⟩ :=
    ValueSide.head_shape laws.value (fun hh => M.levels.level_lt_of_typing hh typing) ξ'
  exact ⟨Q, hQ, hQ, s⟩

end Conversion
end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
