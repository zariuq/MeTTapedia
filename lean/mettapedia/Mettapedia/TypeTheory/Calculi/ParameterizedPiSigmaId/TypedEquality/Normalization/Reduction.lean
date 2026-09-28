import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.Neutral

/-!
# Closure under expansion

A type that reduces to a reducible type is reducible, with the same pack: every
pack depends only on the weak-head normal form. A term that reduces to a
reducible term is reducible and reducibly equal to its reduct, and reducible
equalities and type equalities are closed under expansion on either side.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Normalization

open UniverseLevel (LevelOrder)

variable {Head L : Type} [LevelOrder L] {S : Setting Head L}

/-- Expansion of a reducible type keeps its pack. -/
theorem LR.expand {l : L} {rec : L → RedRel Head} {n : Nat} {Γ : Ctx Head n}
    {A A' : Tm Head n} {P : Pack Head n} (reducible : LR S l rec Γ A' P)
    (red : RedTy S.R S.roles Γ A A') : LR S l rec Γ A P := by
  cases reducible with
  | sort isUniverse below formed red' =>
      exact .sort isUniverse below formed (red.trans S.levels red')
  | neutral red' neutral isUniverse typing refl =>
      exact .neutral (red.trans S.levels red') neutral isUniverse typing refl
  | ground notUniverse red' typing isUniverse =>
      exact .ground notUniverse (red.trans S.levels red') typing isUniverse
  | pi red' domType codType refl P domAdequate codAdequate =>
      exact .pi (red.trans S.levels red') domType codType refl P domAdequate codAdequate
  | sigma red' domType codType refl P domAdequate codAdequate =>
      exact .sigma (red.trans S.levels red') domType codType refl P domAdequate codAdequate
  | ident red' refl tyPack tyAdequate lhsRed rhsRed lhsRefl rhsRefl tySymm tyTrans =>
      exact .ident (red.trans S.levels red') refl tyPack tyAdequate lhsRed rhsRed lhsRefl
        rhsRefl tySymm tyTrans
  | inductiveType red' role typing isUniverse fieldPack fieldAdequate =>
      exact .inductiveType (red.trans S.levels red') role typing isUniverse fieldPack
        fieldAdequate

/-- Reducible type equality is closed under expansion of the other type. -/
theorem LR.eqTy_expand {l : L} {rec : L → RedRel Head} {n : Nat} {Γ : Ctx Head n}
    {A B B' : Tm Head n} {P : Pack Head n} (reducible : LR S l rec Γ A P)
    (red : RedTy S.R S.roles Γ B B') (equal : P.eqTy B') : P.eqTy B := by
  cases reducible with
  | sort =>
      obtain ⟨u', redB, same⟩ := equal
      exact ⟨u', red.trans S.levels redB, same⟩
  | neutral =>
      obtain ⟨ty', redB, neutral', v, hv, conv⟩ := equal
      exact ⟨ty', red.trans S.levels redB, neutral', v, hv, conv⟩
  | ground =>
      obtain ⟨h', redB, same⟩ := equal
      exact ⟨h', red.trans S.levels redB, same⟩
  | pi =>
      obtain ⟨d, c, redB, conv, domEq, codEq⟩ := equal
      exact ⟨d, c, red.trans S.levels redB, conv, domEq, codEq⟩
  | sigma =>
      obtain ⟨d, c, redB, conv, domEq, codEq⟩ := equal
      exact ⟨d, c, red.trans S.levels redB, conv, domEq, codEq⟩
  | ident =>
      obtain ⟨t, lh, rh, redB, conv, tyEq, lEq, rEq⟩ := equal
      exact ⟨t, lh, rh, red.trans S.levels redB, conv, tyEq, lEq, rEq⟩
  | inductiveType => exact red.trans S.levels equal

/-- Expansion of a reducible term: the source is reducible and reducibly equal to
the target. -/
theorem LR.redTm_expand {l : L} {n : Nat}
    {Γ : Ctx Head n} {A t u : Tm Head n} {P : Pack Head n}
    (reducible : LR S l (levelsBelow S l) Γ A P) (red : RedTm S.R S.roles Γ t u A)
    (reducibleU : P.redTm u) : P.redTm t ∧ P.eqTm t u := by
  have reflexive := LogRel.reflexive S l reducible
  cases reducible with
  | @sort _ _ _ w isUniverse below formed redA =>
      have typeEq := redA.typeEq
      obtain ⟨nf, redU, form, refl, Q, reducibleQ⟩ := reducibleU
      have redT := (red.conv typeEq).trans redU
      have lowerT : levelsBelow S l (S.levels.level w) Γ t Q :=
        (levelsBelow_iff S below Γ t Q).mpr
          (LR.expand ((levelsBelow_iff S below Γ u Q).mp reducibleQ)
            ((red.conv typeEq).toRedTy isUniverse))
      refine ⟨⟨nf, redT, form, refl, Q, lowerT⟩, ?_⟩
      exact ⟨nf, nf, redT, redU, form, form, refl, ⟨Q, reducibleQ⟩, Q, lowerT,
        (LogRel.reflexive S _ ((levelsBelow_iff S below Γ u Q).mp reducibleQ)).eqTy⟩
  | neutral redA neutral isUniverse typing refl =>
      have typeEq := redA.typeEq
      obtain ⟨nf, redU, neutralU, reflU⟩ := reducibleU
      have redT := (red.conv typeEq).trans redU
      exact ⟨⟨nf, redT, neutralU, reflU⟩, nf, nf, redT, redU, neutralU, neutralU, reflU⟩
  | ground notUniverse redA typing isUniverse =>
      have typeEq := redA.typeEq
      obtain ⟨nf, redU, neutralU, reflU⟩ := reducibleU
      have redT := (red.conv typeEq).trans redU
      exact ⟨⟨nf, redT, neutralU, reflU⟩, nf, nf, redT, redU, neutralU, neutralU, reflU⟩
  | pi redA domType codType refl P domAdequate codAdequate =>
      have typeEq := redA.typeEq
      obtain ⟨nf, redU, isFun, reflU, apps, appEqs⟩ := reducibleU
      have redT := (red.conv typeEq).trans redU
      have reducibleT : PiRedTm S P t := ⟨nf, redT, isFun, reflU, apps, appEqs⟩
      refine ⟨reducibleT, reducibleT, ⟨nf, redU, isFun, reflU, apps, appEqs⟩, nf, nf, redT,
        redU, isFun, isFun, reflU, ?_⟩
      intro m Δ ρ w a ha
      exact (LogRel.reflexive S l (codAdequate w ha)).eqTm (apps w ha)
  | sigma redA domType codType refl P domAdequate codAdequate =>
      have typeEq := redA.typeEq
      obtain ⟨nf, redU, isPair, reflU, first, second⟩ := reducibleU
      have redT := (red.conv typeEq).trans redU
      have reducibleT : SigmaRedTm S P t := ⟨nf, redT, isPair, reflU, first, second⟩
      refine ⟨reducibleT, reducibleT, ⟨nf, redU, isPair, reflU, first, second⟩, nf, nf, redT,
        redU, isPair, isPair, reflU, ?_, ?_⟩
      · intro m Δ ρ w
        exact (LogRel.reflexive S l (domAdequate w)).eqTm (first w)
      · intro m Δ ρ w h
        exact (LogRel.reflexive S l (codAdequate w h)).eqTm (second w)
  | ident redA refl tyPack tyAdequate lhsRed rhsRed lhsRefl rhsRefl tySymm tyTrans =>
      have typeEq := redA.typeEq
      obtain ⟨nf, redU, reflU, prop⟩ := reducibleU
      have redT := (red.conv typeEq).trans redU
      refine ⟨⟨nf, redT, reflU, prop⟩, nf, nf, redT, redU, reflU, ?_⟩
      rcases prop with ⟨x, rfl, typing, left, right⟩ | ⟨neutral, reflN⟩
      · exact .inl ⟨x, x, rfl, rfl, typing, typing, left, left, right, right⟩
      · exact .inr ⟨neutral, neutral, reflN⟩
  | inductiveType redA role typing isUniverse fieldPack fieldAdequate =>
      have redT := red.conv redA.typeEq
      exact ⟨IndRedTm.expand redT reducibleU,
        IndEqTm.expand redT (RedTm.refl redT.target) (reflexive.eqTm reducibleU)⟩

/-- Both sides of a reducible equality are reducible. -/
theorem LR.eqTm_redTm (laws : S.E.Laws S.R S.roles) {l : L} {rec : L → RedRel Head}
    {n : Nat} {Γ : Ctx Head n} {A : Tm Head n} {P : Pack Head n}
    (reducible : LR S l rec Γ A P) :
    ∀ {t u : Tm Head n}, P.eqTm t u → P.redTm t ∧ P.redTm u := by
  induction reducible with
  | sort =>
      intro t u equal
      obtain ⟨nf, nf', r, r', f, f', c, ⟨Q', q'⟩, Q, q, _⟩ := equal
      exact ⟨⟨nf, r, f, laws.convTm_trans c (laws.convTm_symm c), Q, q⟩,
        ⟨nf', r', f', laws.convTm_trans (laws.convTm_symm c) c, Q', q'⟩⟩
  | neutral =>
      intro t u equal
      obtain ⟨nf, nf', r, r', n₁, n₂, c⟩ := equal
      exact ⟨⟨nf, r, n₁, laws.convNe_trans c (laws.convNe_symm c)⟩,
        ⟨nf', r', n₂, laws.convNe_trans (laws.convNe_symm c) c⟩⟩
  | ground =>
      intro t u equal
      obtain ⟨nf, nf', r, r', n₁, n₂, c⟩ := equal
      exact ⟨⟨nf, r, n₁, laws.convNe_trans c (laws.convNe_symm c)⟩,
        ⟨nf', r', n₂, laws.convNe_trans (laws.convNe_symm c) c⟩⟩
  | pi => intro t u equal; exact ⟨equal.1, equal.2.1⟩
  | sigma => intro t u equal; exact ⟨equal.1, equal.2.1⟩
  | ident =>
      intro t u equal
      obtain ⟨nf, nf', r, r', c, prop⟩ := equal
      have refl₁ := laws.convTm_trans c (laws.convTm_symm c)
      have refl₂ := laws.convTm_trans (laws.convTm_symm c) c
      rcases prop with ⟨x, x', rfl, rfl, ty, ty', l₁, l₂, r₁, r₂⟩ | ⟨n₁, n₂, cN⟩
      · exact ⟨⟨_, r, refl₁, .inl ⟨x, rfl, ty, l₁, r₁⟩⟩, ⟨_, r', refl₂, .inl ⟨x', rfl, ty', l₂, r₂⟩⟩⟩
      · exact ⟨⟨nf, r, refl₁, .inr ⟨n₁, laws.convNe_trans cN (laws.convNe_symm cN)⟩⟩,
          ⟨nf', r', refl₂, .inr ⟨n₂, laws.convNe_trans (laws.convNe_symm cN) cN⟩⟩⟩
  | inductiveType red role typing isUniverse fieldPack fieldAdequate fieldIH =>
      intro t u equal
      exact IndEqTm.ends laws (fun ⟨_, _, mem, closed⟩ _ _ h => fieldIH mem closed h) equal

/-- Reducible term equality is closed under expansion on both sides. -/
theorem LR.eqTm_expand (laws : S.E.Laws S.R S.roles) {l : L} {n : Nat}
    {Γ : Ctx Head n} {A t t' u u' : Tm Head n} {P : Pack Head n}
    (reducible : LR S l (levelsBelow S l) Γ A P) (redT : RedTm S.R S.roles Γ t t' A)
    (redU : RedTm S.R S.roles Γ u u' A) (equal : P.eqTm t' u') : P.eqTm t u := by
  have per := reducible.eqTm_per laws
  obtain ⟨reducibleT', reducibleU'⟩ := reducible.eqTm_redTm laws equal
  have left := (reducible.redTm_expand redT reducibleT').2
  have right := (reducible.redTm_expand redU reducibleU').2
  exact per.2 left (per.2 equal (per.1 right))

end Normalization
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
