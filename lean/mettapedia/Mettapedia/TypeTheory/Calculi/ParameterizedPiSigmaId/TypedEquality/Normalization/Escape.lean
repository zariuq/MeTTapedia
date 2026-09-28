import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.InductivePacks

/-!
# Escape and reflexivity

A reducible type is a type convertible to itself; its reducible terms are
typed and convertible to themselves; reducibly equal terms and types are
convertible. Every case of the relation keeps the conversion facts of its
weak-head normal form, so escape needs no induction.

Reducibility is reflexive: a reducible type is reducibly equal to itself and a
reducible term is reducibly equal to itself. The universe case refers to the
relations below the current level, so the statement is proved for any family
of lower relations that is itself reflexive.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Normalization

open UniverseLevel (LevelOrder)

variable {Head L : Type} [LevelOrder L] {S : Setting Head L}

/-! ## Conversion through reduction -/

section Expansion

variable (laws : S.E.Laws S.R S.roles)
include laws

theorem convTy_of_red {n : Nat} {Γ : Ctx Head n} {A A' B B' : Tm Head n}
    (redA : RedTy S.R S.roles Γ A A') (redB : RedTy S.R S.roles Γ B B')
    (equal : S.E.convTy Γ A' B') : S.E.convTy Γ A B :=
  laws.convTy_expand redA redB equal

theorem convTm_of_red {n : Nat} {Γ : Ctx Head n} {t t' u u' A B : Tm Head n}
    (redT : RedTm S.R S.roles Γ t t' B) (redU : RedTm S.R S.roles Γ u u' B)
    (equal : S.E.convTm Γ t' u' B) (typeEq : TypeEq S.R Γ B A) : S.E.convTm Γ t u A :=
  laws.convTm_conv (laws.convTm_expand redT redU equal) typeEq

/-- Two heads typed by universes are convertible when they are equal heads. -/
theorem convTy_heads {n : Nat} {Γ : Ctx Head n} {h h' : Head}
    (same : h = h' ∨ S.R.headEq h h') (formed : IsType S.R Γ (.head h))
    (formed' : IsType S.R Γ (.head h')) : S.E.convTy Γ (.head h) (.head h') := by
  obtain ⟨v, hv, typing⟩ := formed
  obtain ⟨v', hv', typing'⟩ := formed'
  obtain ⟨w, join⟩ := S.levels.join_exists hv hv'
  obtain ⟨vw, vw'⟩ := S.levels.join_upper join
  exact laws.convTy_head same (.cumul typing vw) (.cumul typing' vw')
    (S.levels.join_level join).1

end Expansion

/-! ## Escape -/

/-- What escape gives for a reducible type and its pack. -/
structure Escapes (S : Setting Head L) {n : Nat} (Γ : Ctx Head n) (A : Tm Head n)
    (P : Pack Head n) : Prop where
  type : IsType S.R Γ A
  refl : S.E.convTy Γ A A
  eqTy : ∀ {B}, P.eqTy B → S.E.convTy Γ A B
  redTm : ∀ {t}, P.redTm t → Typed S.R Γ t A ∧ S.E.convTm Γ t t A
  eqTm : ∀ {t u}, P.eqTm t u → S.E.convTm Γ t u A

theorem LR.escape (laws : S.E.Laws S.R S.roles) {l : L} {rec : L → RedRel Head}
    {n : Nat} {Γ : Ctx Head n} {A : Tm Head n} {P : Pack Head n}
    (reducible : LR S l rec Γ A P) : Escapes S Γ A P := by
  cases reducible with
  | @sort _ _ _ u isUniverse _ _ red =>
      have typeEq := red.typeEq
      refine ⟨red.sourceType, ?_, ?_, ?_, ?_⟩
      · exact convTy_of_red laws red red
          (convTy_heads laws (.inl rfl) red.targetType red.targetType)
      · rintro B ⟨u', redB, same⟩
        exact convTy_of_red laws red redB
          (convTy_heads laws same red.targetType redB.targetType)
      · rintro t ⟨nf, redT, _, refl, _⟩
        exact ⟨Typed.convType redT.source typeEq.symm,
          convTm_of_red laws redT redT refl typeEq.symm⟩
      · rintro t u ⟨nf, nf', redT, redU, _, _, equal, _⟩
        exact convTm_of_red laws redT redU equal typeEq.symm
  | @neutral _ _ _ ty u red neutral isUniverse typing refl =>
      have typeEq := red.typeEq
      have tyRefl : S.E.convTy Γ ty ty :=
        laws.convTy_of_convTm (laws.convTm_of_convNe (.inl neutral) (.inl neutral) refl) isUniverse
      refine ⟨red.sourceType, convTy_of_red laws red red tyRefl, ?_, ?_, ?_⟩
      · rintro B ⟨ty', redB, neutral', v, hv, equal⟩
        exact convTy_of_red laws red redB
          (laws.convTy_of_convTm (laws.convTm_of_convNe (.inl neutral) (.inl neutral') equal) hv)
      · rintro t ⟨nf, redT, nNf, reflT⟩
        exact ⟨Typed.convType redT.source typeEq.symm,
          convTm_of_red laws redT redT (laws.convTm_of_convNe (.inl nNf) (.inl nNf) reflT)
            typeEq.symm⟩
      · rintro t u ⟨nf, nf', redT, redU, n₁, n₂, equal⟩
        exact convTm_of_red laws redT redU (laws.convTm_of_convNe (.inl n₁) (.inl n₂) equal)
          typeEq.symm
  | @ground _ _ _ h u notUniverse red typing isUniverse =>
      have typeEq := red.typeEq
      refine ⟨red.sourceType, ?_, ?_, ?_, ?_⟩
      · exact convTy_of_red laws red red
          (convTy_heads laws (.inl rfl) red.targetType red.targetType)
      · rintro B ⟨h', redB, same⟩
        exact convTy_of_red laws red redB
          (convTy_heads laws same red.targetType redB.targetType)
      · rintro t ⟨nf, redT, nNf, reflT⟩
        exact ⟨Typed.convType redT.source typeEq.symm,
          convTm_of_red laws redT redT (laws.convTm_of_convNe (.inl nNf) (.inl nNf) reflT)
            typeEq.symm⟩
      · rintro t u ⟨nf, nf', redT, redU, n₁, n₂, equal⟩
        exact convTm_of_red laws redT redU (laws.convTm_of_convNe (.inl n₁) (.inl n₂) equal)
          typeEq.symm
  | @pi _ _ _ dom cod red domType codType refl P _ _ =>
      have typeEq := red.typeEq
      refine ⟨red.sourceType, convTy_of_red laws red red refl, ?_, ?_, ?_⟩
      · rintro B ⟨dom', cod', redB, equal, _, _⟩
        exact convTy_of_red laws red redB equal
      · rintro t ⟨nf, redT, _, reflT, _, _⟩
        exact ⟨Typed.convType redT.source typeEq.symm,
          convTm_of_red laws redT redT reflT typeEq.symm⟩
      · rintro t u ⟨_, _, nf, nf', redT, redU, _, _, equal, _⟩
        exact convTm_of_red laws redT redU equal typeEq.symm
  | @sigma _ _ _ dom cod red domType codType refl P _ _ =>
      have typeEq := red.typeEq
      refine ⟨red.sourceType, convTy_of_red laws red red refl, ?_, ?_, ?_⟩
      · rintro B ⟨dom', cod', redB, equal, _, _⟩
        exact convTy_of_red laws red redB equal
      · rintro t ⟨nf, redT, _, reflT, _⟩
        exact ⟨Typed.convType redT.source typeEq.symm,
          convTm_of_red laws redT redT reflT typeEq.symm⟩
      · rintro t u ⟨_, _, nf, nf', redT, redU, _, _, equal, _⟩
        exact convTm_of_red laws redT redU equal typeEq.symm
  | @ident _ _ _ ty lhs rhs red refl tyPack _ _ _ _ _ _ _ =>
      have typeEq := red.typeEq
      refine ⟨red.sourceType, convTy_of_red laws red red refl, ?_, ?_, ?_⟩
      · rintro B ⟨ty', lhs', rhs', redB, equal, _⟩
        exact convTy_of_red laws red redB equal
      · rintro t ⟨nf, redT, reflT, _⟩
        exact ⟨Typed.convType redT.source typeEq.symm,
          convTm_of_red laws redT redT reflT typeEq.symm⟩
      · rintro t u ⟨nf, nf', redT, redU, equal, _⟩
        exact convTm_of_red laws redT redU equal typeEq.symm
  | @inductiveType _ _ _ T ctors u red role typing isUniverse fieldPack _ =>
      have typeEq := red.typeEq
      have constRefl : S.E.convTy Γ (.const T) (.const T) :=
        laws.convTy_of_convTm (laws.convTm_of_convNe (.inr (.inr ⟨T, ctors, role, rfl⟩))
          (.inr (.inr ⟨T, ctors, role, rfl⟩)) (laws.convNe_const T typing)) isUniverse
      refine ⟨red.sourceType, convTy_of_red laws red red constRefl, ?_, ?_, ?_⟩
      · intro B redB
        exact convTy_of_red laws red redB constRefl
      · rintro t ⟨redT, reflT, _⟩
        exact ⟨Typed.convType redT.source typeEq.symm,
          convTm_of_red laws redT redT reflT typeEq.symm⟩
      · rintro t u ⟨redT, redU, equal, _⟩
        exact convTm_of_red laws redT redU equal typeEq.symm

/-! ## Reflexivity -/

/-- Reflexivity of one pack. -/
structure Reflexive {n : Nat} (A : Tm Head n) (P : Pack Head n) : Prop where
  eqTy : P.eqTy A
  eqTm : ∀ {t}, P.redTm t → P.eqTm t t

/-- Every lower relation below level `l` is reflexive. -/
def RecReflexive (l : L) (rec : L → RedRel Head) : Prop :=
  ∀ {k : L}, k < l → ∀ {n : Nat} {Γ : Ctx Head n} {A : Tm Head n} {P : Pack Head n},
    rec k Γ A P → Reflexive A P

theorem LR.reflexive {l : L} {rec : L → RedRel Head} (recRefl : RecReflexive l rec)
    {n : Nat} {Γ : Ctx Head n} {A : Tm Head n} {P : Pack Head n}
    (reducible : LR S l rec Γ A P) : Reflexive A P := by
  induction reducible with
  | @sort n Γ A u isUniverse below formed red =>
      refine ⟨⟨u, red, .inl rfl⟩, ?_⟩
      rintro t ⟨nf, redT, whnf, refl, P', reducibleT⟩
      exact ⟨nf, nf, redT, redT, whnf, whnf, refl, ⟨P', reducibleT⟩, P', reducibleT,
        (recRefl below reducibleT).eqTy⟩
  | @neutral n Γ A ty u red neutral isUniverse typing refl =>
      refine ⟨⟨ty, red, neutral, u, isUniverse, refl⟩, ?_⟩
      rintro t ⟨nf, redT, neutralT, reflT⟩
      exact ⟨nf, nf, redT, redT, neutralT, neutralT, reflT⟩
  | @ground n Γ A h u notUniverse red typing isUniverse =>
      refine ⟨⟨h, red, .inl rfl⟩, ?_⟩
      rintro t ⟨nf, redT, neutralT, reflT⟩
      exact ⟨nf, nf, redT, redT, neutralT, neutralT, reflT⟩
  | @pi n Γ A dom cod red domType codType refl P domAdequate codAdequate domIH codIH =>
      refine ⟨⟨dom, cod, red, refl, fun w => (domIH w).eqTy,
        fun w a ha => (codIH w ha).eqTy⟩, ?_⟩
      intro t reducibleT
      have copy := reducibleT
      obtain ⟨nf, redT, isFun, reflT, apps, appEqs⟩ := copy
      exact ⟨reducibleT, reducibleT, nf, nf, redT, redT, isFun, isFun, reflT,
        fun w a ha => (codIH w ha).eqTm (apps w ha)⟩
  | @sigma n Γ A dom cod red domType codType refl P domAdequate codAdequate domIH codIH =>
      refine ⟨⟨dom, cod, red, refl, fun w => (domIH w).eqTy,
        fun w a ha => (codIH w ha).eqTy⟩, ?_⟩
      intro t reducibleT
      have copy := reducibleT
      obtain ⟨nf, redT, isPair, reflT, first, second⟩ := copy
      exact ⟨reducibleT, reducibleT, nf, nf, redT, redT, isPair, isPair, reflT,
        fun w => (domIH w).eqTm (first w), fun w h => (codIH w h).eqTm (second w)⟩
  | @ident n Γ A ty lhs rhs red refl tyPack tyAdequate lhsRed rhsRed lhsRefl rhsRefl
      tySymm tyTrans tyIH =>
      refine ⟨⟨ty, lhs, rhs, red, refl, tyIH.eqTy, lhsRefl, rhsRefl⟩, ?_⟩
      rintro t ⟨nf, redT, reflT, prop⟩
      refine ⟨nf, nf, redT, redT, reflT, ?_⟩
      rcases prop with ⟨x, rfl, typing, left, right⟩ | ⟨neutral, reflN⟩
      · exact .inl ⟨x, x, rfl, rfl, typing, typing, left, left, right, right⟩
      · exact .inr ⟨neutral, neutral, reflN⟩
  | @inductiveType n Γ A T ctors u red role typing isUniverse fieldPack fieldAdequate fieldIH =>
      refine ⟨red, ?_⟩
      intro t reducibleT
      exact IndRedTm.refl (fun ⟨_, _, mem, closed⟩ _ ha => (fieldIH mem closed).eqTm ha)
        reducibleT

/-- Reducibility at every level is reflexive. -/
theorem LogRel.reflexive (S : Setting Head L) (l : L) {n : Nat} {Γ : Ctx Head n}
    {A : Tm Head n} {P : Pack Head n} (reducible : LogRel S l Γ A P) : Reflexive A P := by
  induction l using LevelOrder.induction generalizing n Γ A P with
  | step l ih =>
      refine LR.reflexive ?_ reducible
      intro k lt n Γ A P reducibleK
      exact ih k lt ((levelsBelow_iff S lt Γ A P).mp reducibleK)

end Normalization
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
