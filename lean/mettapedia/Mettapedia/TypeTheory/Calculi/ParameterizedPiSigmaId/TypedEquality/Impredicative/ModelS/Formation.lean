import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.ModelS.Structure
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.ValueSide.DecoderShape
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.ValueSide.Families

/-!
# Universes in model S

A universe denotes the pack of its level: types with one pack and one shape at
that level at every world reached by a morphism, realized by the strongly
normalizing terms. So a term of a universe is a valid type: related valuations
give its instances one pack, and its realizer instance is strongly
normalizing. Equal terms of a universe have one pack and one shape under
related valuations (`ValidEqS.universe_shape`).

A head typed by a universe is a term of it: a universe is of one shape with
itself by its level, and any other head is a leaf, a hereditarily total type.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Impredicative
namespace ModelS

open Normalization (tailSub)
open UniverseLevel (LevelOrder)
open Consistency (World Morph)
open StrongNormalization
open ValueSide

variable {Head L : Type} [LevelOrder L] {M : SModel Head L}

/-! ## The pack of a universe -/

variable (M) in
/-- The pack of the universe at level `k`: the value side's. -/
abbrev universeAt (k : L) {n : Nat} (ξ : World M.reading n) : Pack M.value n :=
  ValueSide.universeAt M.value k ξ

/-- A universe denotes the pack of its level. -/
theorem DenS.sort_inv (laws : M.Laws) {u : Head} (isUniverse : M.rules.isUniverse u)
    {n : Nat} {ξ : World M.reading n} {P : Pack M.value n} (den : DenS M.value ξ (.head u) P) :
    P = universeAt M (M.levels.level u) ξ :=
  ValueSide.DenS.sort_inv laws.value isUniverse den

/-- A universe is a valid type. -/
theorem ValidTyS.sort {n : Nat} {Γ : Ctx Head n} {u : Head}
    (isUniverse : M.rules.isUniverse u) : ValidTyS M Γ (.head u) :=
  fun {_ _ ξ _ _ _} _ => ⟨_, ValueSide.DenS.sort (V := M.value) isUniverse ξ,
    ValueSide.DenS.sort (V := M.value) isUniverse ξ,
    SN.head (RootShape.spineHeaded M.realizers.shape) u⟩

/-- Types related in a universe have one pack and one shape at its level. -/
theorem universeAt.den {k : L} {n : Nat} {ξ : World M.reading n} {A B : Tm Head n}
    (h : (universeAt M k ξ).rel A B) :
    ∃ P, InterpAt M.value k ξ A P ∧ InterpAt M.value k ξ B P ∧
      Shape M.value (InterpAt M.value k) .pair ξ A B :=
  ValueSide.universeAt.den h

/-! ## Terms of universes -/

/-- A term of a universe is related to itself at its level under related
valuations, and its realizer instance is strongly normalizing. -/
theorem ValidTmS.universe {n : Nat} {Γ : Ctx Head n} {A : Tm Head n} {u : Head}
    (valid : ValidTmS M Γ A (.head u)) (isUniverse : M.rules.isUniverse u) {m r : Nat}
    {ξ : World M.reading m} {σ σ' : Sub Head n m} {ς : Sub Head n r}
    (e : EqSubstS M Γ ξ σ σ' ς) :
    (universeAt M (M.levels.level u) ξ).rel (Presentation.subst σ A)
      (Presentation.subst σ' A) ∧ SN M.realizers.rules (Presentation.subst ς A) :=
  valid.2 e (ValueSide.DenS.sort (V := M.value) isUniverse ξ)

/-- Equal terms of a universe are related at its level under related
valuations. -/
theorem ValidEqS.universe {n : Nat} {Γ : Ctx Head n} {A B : Tm Head n} {u : Head}
    (valid : ValidEqS M Γ A B (.head u)) (isUniverse : M.rules.isUniverse u) {m r : Nat}
    {ξ : World M.reading m} {σ σ' : Sub Head n m} {ς : Sub Head n r}
    (e : EqSubstS M Γ ξ σ σ' ς) :
    (universeAt M (M.levels.level u) ξ).rel (Presentation.subst σ A)
      (Presentation.subst σ' B) :=
  valid.2.2 e (ValueSide.DenS.sort (V := M.value) isUniverse ξ)

/-- **Validly equal terms of a universe have one pack and one shape** at its
level under related valuations. -/
theorem ValidEqS.universe_shape {n : Nat} {Γ : Ctx Head n} {A B : Tm Head n} {u : Head}
    (valid : ValidEqS M Γ A B (.head u)) (isUniverse : M.rules.isUniverse u) {m r : Nat}
    {ξ : World M.reading m} {σ σ' : Sub Head n m} {ς : Sub Head n r}
    (e : EqSubstS M Γ ξ σ σ' ς) :
    ∃ P, InterpAt M.value (M.levels.level u) ξ (Presentation.subst σ A) P ∧
      InterpAt M.value (M.levels.level u) ξ (Presentation.subst σ' B) P ∧
      Shape M.value (InterpAt M.value (M.levels.level u)) .pair ξ (Presentation.subst σ A)
        (Presentation.subst σ' B) :=
  universeAt.den (valid.universe isUniverse e)

/-- A term of a universe is a valid type. -/
theorem ValidTmS.validTy {n : Nat} {Γ : Ctx Head n} {A : Tm Head n} {u : Head}
    (valid : ValidTmS M Γ A (.head u)) (isUniverse : M.rules.isUniverse u) :
    ValidTyS M Γ A := fun e => by
  obtain ⟨rel, sn⟩ := valid.universe isUniverse e
  obtain ⟨P, hA, hA', -⟩ := universeAt.den rel
  exact ⟨P, ⟨_, hA⟩, ⟨_, hA'⟩, sn⟩

/-- Validly equal terms of a universe have one pack under related valuations. -/
theorem ValidEqS.den {n : Nat} {Γ : Ctx Head n} {A B : Tm Head n} {u : Head}
    (valid : ValidEqS M Γ A B (.head u)) (isUniverse : M.rules.isUniverse u) {m r : Nat}
    {ξ : World M.reading m} {σ σ' : Sub Head n m} {ς : Sub Head n r}
    (e : EqSubstS M Γ ξ σ σ' ς) :
    ∃ P, DenS M.value ξ (Presentation.subst σ A) P ∧
      DenS M.value ξ (Presentation.subst σ' B) P := by
  obtain ⟨P, hA, hB, -⟩ := valid.universe_shape isUniverse e
  exact ⟨P, ⟨_, hA⟩, ⟨_, hB⟩⟩

/-! ## Heads -/

/-- A head typed by a universe is a term of it. -/
theorem ValidTmS.headType (laws : M.Laws) {n : Nat} {Γ : Ctx Head n} {h u : Head}
    (typing : M.rules.headTyping h u) : ValidTmS M Γ (.head h) (.head u) := by
  have isUniverse := M.levels.ground_typing typing
  refine ⟨ValidTyS.sort isUniverse, fun {_ _ ξ _ _ _} _ {P} den => ?_⟩
  rw [DenS.sort_inv laws isUniverse den]
  refine ⟨fun {_ ξ' _} _ => ?_, SN.head (RootShape.spineHeaded M.realizers.shape) h⟩
  obtain ⟨Q, hQ, s⟩ :=
    head_shape laws.value (fun hh => M.levels.level_lt_of_typing hh typing) ξ'
  exact ⟨Q, hQ, hQ, s⟩

end ModelS
end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
