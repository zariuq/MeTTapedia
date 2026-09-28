import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.Reduction

/-!
# One pack per reducible type

Reducibility at a level persists at every higher level with the same pack,
because the relations below a level do not change when the level grows.

A type has one pack at every level at which it is reducible, and reducibly
equal types have the same pack; the pack of a reducible type is `packOf`
(both in the irrelevance module). The facts about reducible types collected
here are therefore stated without naming a level.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Normalization

open UniverseLevel (LevelOrder)

variable {Head L : Type} [LevelOrder L] {S : Setting Head L}

/-! ## Levels -/

/-- The relation at a level below `l` is the same in the table of every level
above `l`. -/
theorem levelsBelow_mono (S : Setting Head L) {k l : L} (below : k < l) {l' : L}
    (le : l ≤ l') {n : Nat} (Γ : Ctx Head n) (A : Tm Head n) (P : Pack Head n) :
    levelsBelow S l' k Γ A P ↔ levelsBelow S l k Γ A P := by
  rw [levelsBelow_iff S (lt_of_lt_of_le below le), levelsBelow_iff S below]

/-- A universe pack depends on the lower relations only at the universe's level. -/
theorem universePack_congr {rec rec' : L → RedRel Head} {n : Nat} (Γ : Ctx Head n)
    (u : Head)
    (same : ∀ {m : Nat} (Δ : Ctx Head m) (t : Tm Head m) (P : Pack Head m),
      rec (S.levels.level u) Δ t P ↔ rec' (S.levels.level u) Δ t P) :
    universePack S rec Γ u = universePack S rec' Γ u := by
  apply PackEquiv.eq
  refine ⟨Iff.rfl, ?_, ?_⟩
  · intro t
    simp only [universePack, same]
  · intro t t'
    simp only [universePack, same]

/-- Reducibility persists at higher levels, with the same pack. -/
theorem LR.lift {l : L} {n : Nat} {Γ : Ctx Head n} {A : Tm Head n} {P : Pack Head n}
    (reducible : LR S l (levelsBelow S l) Γ A P) :
    ∀ {l' : L}, l ≤ l' → LR S l' (levelsBelow S l') Γ A P := by
  intro l' le
  induction reducible with
  | @sort n Γ A u isUniverse below formed red =>
      rw [universePack_congr (S := S) Γ u fun Δ t P => (levelsBelow_mono S below le Δ t P).symm]
      exact .sort isUniverse (lt_of_lt_of_le below le) formed red
  | neutral red neutral isUniverse typing refl =>
      exact .neutral red neutral isUniverse typing refl
  | ground notUniverse red typing isUniverse =>
      exact .ground notUniverse red typing isUniverse
  | pi red domType codType refl P _ _ ihDom ihCod =>
      exact .pi red domType codType refl P (fun w => ihDom w) (fun {_} {_} {_} w {_} ha => ihCod w ha)
  | sigma red domType codType refl P _ _ ihDom ihCod =>
      exact .sigma red domType codType refl P (fun w => ihDom w) (fun {_} {_} {_} w {_} ha => ihCod w ha)
  | ident red refl tyPack _ lhsRed rhsRed lhsRefl rhsRefl tySymm tyTrans ihTy =>
      exact .ident red refl tyPack ihTy lhsRed rhsRed lhsRefl rhsRefl tySymm tyTrans
  | inductiveType red role typing isUniverse fieldPack _ ihFields =>
      exact .inductiveType red role typing isUniverse fieldPack
        fun mem closed => ihFields mem closed

theorem LogRel.lift {l l' : L} {n : Nat} {Γ : Ctx Head n} {A : Tm Head n}
    {P : Pack Head n} (reducible : LogRel S l Γ A P) (le : l ≤ l') : LogRel S l' Γ A P :=
  LR.lift reducible le

/-! ## Reducible types -/

section Reducible

variable (laws : S.E.Laws S.R S.roles)
include laws

omit laws in
theorem Reducible.reflexive {n : Nat} {Γ : Ctx Head n} {A : Tm Head n} {P : Pack Head n}
    (reducible : Reducible S Γ A P) : Reflexive A P := by
  obtain ⟨l, r⟩ := reducible
  exact LogRel.reflexive S l r

theorem Reducible.escape {n : Nat} {Γ : Ctx Head n} {A : Tm Head n} {P : Pack Head n}
    (reducible : Reducible S Γ A P) : Escapes S Γ A P := by
  obtain ⟨l, r⟩ := reducible
  exact LR.escape laws r

theorem Reducible.reflects {n : Nat} {Γ : Ctx Head n} {A : Tm Head n} {P : Pack Head n}
    (reducible : Reducible S Γ A P) : Reflects S Γ A P := by
  obtain ⟨l, r⟩ := reducible
  exact LR.reflects laws r

theorem Reducible.eqTm_symm {n : Nat} {Γ : Ctx Head n} {A : Tm Head n} {P : Pack Head n}
    (reducible : Reducible S Γ A P) {t u : Tm Head n} (equal : P.eqTm t u) : P.eqTm u t := by
  obtain ⟨l, r⟩ := reducible
  exact LR.eqTm_symm laws r equal

theorem Reducible.eqTm_trans {n : Nat} {Γ : Ctx Head n} {A : Tm Head n} {P : Pack Head n}
    (reducible : Reducible S Γ A P) {t u v : Tm Head n} (first : P.eqTm t u)
    (second : P.eqTm u v) : P.eqTm t v := by
  obtain ⟨l, r⟩ := reducible
  exact LR.eqTm_trans laws r first second

theorem Reducible.eqTm_redTm {n : Nat} {Γ : Ctx Head n} {A : Tm Head n} {P : Pack Head n}
    (reducible : Reducible S Γ A P) {t u : Tm Head n} (equal : P.eqTm t u) :
    P.redTm t ∧ P.redTm u := by
  obtain ⟨l, r⟩ := reducible
  exact LR.eqTm_redTm laws r equal

theorem Reducible.eqTy_symm {n : Nat} {Γ : Ctx Head n} {A B : Tm Head n}
    {P Q : Pack Head n} (reducible : Reducible S Γ A P) (reducible' : Reducible S Γ B Q)
    (equal : P.eqTy B) : Q.eqTy A := by
  obtain ⟨l, r⟩ := reducible
  obtain ⟨l', r'⟩ := reducible'
  exact LR.eqTy_symm laws r r' equal

theorem Reducible.eqTy_trans {n : Nat} {Γ : Ctx Head n} {A B C : Tm Head n}
    {P Q : Pack Head n} (reducible : Reducible S Γ A P) (reducible' : Reducible S Γ B Q)
    (first : P.eqTy B) (second : Q.eqTy C) : P.eqTy C := by
  obtain ⟨l, r⟩ := reducible
  obtain ⟨l', r'⟩ := reducible'
  exact LR.eqTy_trans laws r r' first second

/-- Weakening a reducible type along a world weakens its pack. -/
theorem Reducible.weaken {n m : Nat} {Γ : Ctx Head n} {A : Tm Head n} {P : Pack Head n}
    (reducible : Reducible S Γ A P) {Δ : Ctx Head m} {ρ : Ren n m} (w : World S Γ Δ ρ) :
    ∃ P', Reducible S Δ (Presentation.rename ρ A) P' ∧ Weakened P ρ P' := by
  obtain ⟨l, r⟩ := reducible
  obtain ⟨P', r', weakened⟩ := LogRel.weaken laws l (LevelOrder.lt_succ l) r w
  exact ⟨P', ⟨l, r'⟩, weakened⟩

omit laws in
/-- Expansion of a reducible type keeps its pack. -/
theorem Reducible.expand {n : Nat} {Γ : Ctx Head n} {A A' : Tm Head n} {P : Pack Head n}
    (reducible : Reducible S Γ A' P) (red : RedTy S.R S.roles Γ A A') :
    Reducible S Γ A P := by
  obtain ⟨l, r⟩ := reducible
  exact ⟨l, LR.expand r red⟩

omit laws in
theorem Reducible.redTm_expand {n : Nat} {Γ : Ctx Head n} {A t u : Tm Head n}
    {P : Pack Head n} (reducible : Reducible S Γ A P) (red : RedTm S.R S.roles Γ t u A)
    (reducibleU : P.redTm u) : P.redTm t ∧ P.eqTm t u := by
  obtain ⟨l, r⟩ := reducible
  exact LR.redTm_expand r red reducibleU

theorem Reducible.eqTm_expand {n : Nat} {Γ : Ctx Head n} {A t t' u u' : Tm Head n}
    {P : Pack Head n} (reducible : Reducible S Γ A P) (redT : RedTm S.R S.roles Γ t t' A)
    (redU : RedTm S.R S.roles Γ u u' A) (equal : P.eqTm t' u') : P.eqTm t u := by
  obtain ⟨l, r⟩ := reducible
  exact LR.eqTm_expand laws r redT redU equal

end Reducible

/-! ## Universes -/

/-- A universe is reducible one level above its own. -/
theorem universe_logRel {n : Nat} {Γ : Ctx Head n} {u : Head} (isUniverse : S.R.isUniverse u)
    (formed : CtxFormed S.R Γ) :
    LogRel S (LevelOrder.succ (S.levels.level u)) Γ (.head u)
      (universePack S (levelsBelow S (LevelOrder.succ (S.levels.level u))) Γ u) := by
  obtain ⟨v, hv, typing, _⟩ := S.levels.successor isUniverse
  exact .sort isUniverse (LevelOrder.lt_succ _) formed
    (RedTy.refl ⟨v, hv, .headType typing⟩)

/-- The terms of a universe are reducible types, at the universe's level. -/
theorem universePack_redTm_logRel {l : L} {n : Nat} {Γ : Ctx Head n} {u : Head}
    (below : S.levels.level u < l) {t : Tm Head n}
    (reducible : (universePack S (levelsBelow S l) Γ u).redTm t) :
    ∃ P, LogRel S (S.levels.level u) Γ t P := by
  obtain ⟨_, _, _, _, P, r⟩ := reducible
  exact ⟨P, (levelsBelow_iff S below Γ t P).mp r⟩

end Normalization
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
