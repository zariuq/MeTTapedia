import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.Escape

/-!
# Irrelevance

Two reducibility derivations of reducibly equal types, possibly at different
levels, give equivalent packs. In particular a type's pack does not depend on
its derivation, and reducible type equality is symmetric.

The proof inducts on the first derivation. The type equality of its pack fixes
the weak-head normal form of the second type, and weak-head normal forms are
unique, so the second derivation is the same case. Each case then compares the
two packs, recursively for the parts of function, pair and identity types.
The comparison is an equivalence rather than an implication because function
types are contravariant in their domain.

Packs are extensional: packs with the same three relations are equal. By
irrelevance, a type therefore has one pack at every level at which it is
reducible, and reducibly equal types have the same pack. The pack of a
reducible type is `packOf`, defined without reference to any derivation, so
packs can be named for the parts of a type before its derivation exists, such
as the closed field types of an inductive type in a new context.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Normalization

open UniverseLevel (LevelOrder)

variable {Head L : Type} [LevelOrder L] {S : Setting Head L}

/-- Two packs that agree. -/
structure PackEquiv {n : Nat} (P P' : Pack Head n) : Prop where
  eqTy : ∀ {B}, P.eqTy B ↔ P'.eqTy B
  redTm : ∀ {t}, P.redTm t ↔ P'.redTm t
  eqTm : ∀ {t u}, P.eqTm t u ↔ P'.eqTm t u

theorem PackEquiv.refl {n : Nat} (P : Pack Head n) : PackEquiv P P :=
  ⟨Iff.rfl, Iff.rfl, Iff.rfl⟩

theorem PackEquiv.symm {n : Nat} {P P' : Pack Head n} (equiv : PackEquiv P P') :
    PackEquiv P' P :=
  ⟨equiv.eqTy.symm, equiv.redTm.symm, equiv.eqTm.symm⟩

/-- Packs with the same relations are equal. -/
theorem PackEquiv.eq {n : Nat} {P P' : Pack Head n} (equiv : PackEquiv P P') : P = P' := by
  cases P with
  | mk eqTy redTm eqTm =>
    cases P' with
    | mk eqTy' redTm' eqTm' =>
      have e₁ : eqTy = eqTy' := funext fun B => propext (equiv.eqTy (B := B))
      have e₂ : redTm = redTm' := funext fun t => propext (equiv.redTm (t := t))
      have e₃ : eqTm = eqTm' := funext fun t => funext fun u =>
        propext (equiv.eqTm (t := t) (u := u))
      subst e₁ e₂ e₃
      rfl

/-! ## Weak-head normal forms of reducible types -/

theorem RedTy.unique {n : Nat} {Γ : Ctx Head n} {A X Y : Tm Head n}
    (first : RedTy S.R S.roles Γ A X) (second : RedTy S.R S.roles Γ A Y)
    (normal : Whnf S.R S.roles X) (normal' : Whnf S.R S.roles Y) : X = Y :=
  WhRed.whnf_unique S.shape first.red second.red normal normal'

/-- Two heads that are the same are equal types, when both are types. -/
theorem headTypeEq {n : Nat} {Γ : Ctx Head n} {h h' : Head} (same : HeadSame S.R h h')
    (formed : IsType S.R Γ (.head h)) (formed' : IsType S.R Γ (.head h')) :
    TypeEq S.R Γ (.head h) (.head h') := by
  obtain ⟨v, hv, typing⟩ := formed
  obtain ⟨v', hv', typing'⟩ := formed'
  obtain ⟨w, join⟩ := S.levels.join_exists hv hv'
  obtain ⟨vw, vw'⟩ := S.levels.join_upper join
  exact ⟨w, (S.levels.join_level join).1,
    headEquality same (.cumul typing vw) (.cumul typing' vw')⟩

/-! ## The universe case -/

theorem universePack_forward {l l' : L} {n : Nat} {Γ : Ctx Head n} {u u₂ : Head}
    (laws : S.E.Laws S.R S.roles) (same : HeadSame S.R u u₂)
    (formed : IsType S.R Γ (.head u)) (formed₂ : IsType S.R Γ (.head u₂))
    (below₁ : S.levels.level u < l) (below₂ : S.levels.level u₂ < l') :
    (∀ {B}, (universePack S (levelsBelow S l) Γ u).eqTy B →
      (universePack S (levelsBelow S l') Γ u₂).eqTy B) ∧
    (∀ {t}, (universePack S (levelsBelow S l) Γ u).redTm t →
      (universePack S (levelsBelow S l') Γ u₂).redTm t) ∧
    (∀ {t t'}, (universePack S (levelsBelow S l) Γ u).eqTm t t' →
      (universePack S (levelsBelow S l') Γ u₂).eqTm t t') := by
  have typeEq := headTypeEq same formed formed₂
  have sameLevel := (HeadSame.level S.levels same).2
  have transfer : ∀ {m : Nat} {Δ : Ctx Head m} {X : Tm Head m} {Q : Pack Head m},
      levelsBelow S l (S.levels.level u) Δ X Q → levelsBelow S l' (S.levels.level u₂) Δ X Q := by
    intro m Δ X Q h
    rw [← sameLevel]
    rw [← sameLevel] at below₂
    exact (levelsBelow_iff S below₂ Δ X Q).mpr ((levelsBelow_iff S below₁ Δ X Q).mp h)
  refine ⟨?_, ?_, ?_⟩
  · rintro B ⟨v, redB, sameV⟩
    exact ⟨v, redB, HeadSame.trans S.levels (HeadSame.symm S.levels same) sameV⟩
  · rintro t ⟨nf, redT, whnf, refl, Q, reducible⟩
    exact ⟨nf, redT.conv typeEq, whnf, laws.convTm_conv refl typeEq, Q, transfer reducible⟩
  · rintro t t' ⟨nf, nf', redT, redT', whnf, whnf', equal, ⟨Q', reducible'⟩, Q, reducible,
      eqTy⟩
    exact ⟨nf, nf', redT.conv typeEq, redT'.conv typeEq, whnf, whnf',
      laws.convTm_conv equal typeEq, ⟨Q', transfer reducible'⟩, Q, transfer reducible, eqTy⟩

/-! ## Neutral and ground types -/

theorem neutralPack_forward {n : Nat} {Γ : Ctx Head n} {ty ty₂ : Tm Head n} {v : Head}
    (laws : S.E.Laws S.R S.roles) (isUniverse : S.R.isUniverse v)
    (neutral : Neutral S.roles ty) (neutral₂ : Neutral S.roles ty₂)
    (conv : S.E.convNe Γ ty ty₂ (.head v)) :
    (∀ {B}, (neutralPack S Γ ty).eqTy B → (neutralPack S Γ ty₂).eqTy B) ∧
    (∀ {t}, (neutralPack S Γ ty).redTm t → (neutralPack S Γ ty₂).redTm t) ∧
    (∀ {t t'}, (neutralPack S Γ ty).eqTm t t' → (neutralPack S Γ ty₂).eqTm t t') := by
  have typeEq : TypeEq S.R Γ ty ty₂ :=
    laws.convTy_sound (laws.convTy_of_convTm
      (laws.convTm_of_convNe (.inl neutral) (.inl neutral₂) conv) isUniverse)
  refine ⟨?_, ?_, ?_⟩
  · rintro B ⟨ty', redB, neutral, v', hv', conv'⟩
    obtain ⟨w, join⟩ := S.levels.join_exists isUniverse hv'
    obtain ⟨vw, vw'⟩ := S.levels.join_upper join
    exact ⟨ty', redB, neutral, w, (S.levels.join_level join).1,
      laws.convNe_trans (laws.convNe_symm (laws.convNe_cumul conv vw))
        (laws.convNe_cumul conv' vw')⟩
  · rintro t ⟨nf, redT, neutral, refl⟩
    exact ⟨nf, redT.conv typeEq, neutral, laws.convNe_conv refl typeEq⟩
  · rintro t t' ⟨nf, nf', redT, redT', neutral, neutral', equal⟩
    exact ⟨nf, nf', redT.conv typeEq, redT'.conv typeEq, neutral, neutral',
      laws.convNe_conv equal typeEq⟩

theorem groundPack_forward {n : Nat} {Γ : Ctx Head n} {h h₂ : Head}
    (laws : S.E.Laws S.R S.roles) (same : HeadSame S.R h h₂)
    (formed : IsType S.R Γ (.head h)) (formed₂ : IsType S.R Γ (.head h₂)) :
    (∀ {B}, (groundPack S Γ h).eqTy B → (groundPack S Γ h₂).eqTy B) ∧
    (∀ {t}, (groundPack S Γ h).redTm t → (groundPack S Γ h₂).redTm t) ∧
    (∀ {t t'}, (groundPack S Γ h).eqTm t t' → (groundPack S Γ h₂).eqTm t t') := by
  have typeEq := headTypeEq same formed formed₂
  refine ⟨?_, ?_, ?_⟩
  · rintro B ⟨h', redB, sameH⟩
    exact ⟨h', redB, HeadSame.trans S.levels (HeadSame.symm S.levels same) sameH⟩
  · rintro t ⟨nf, redT, neutral, refl⟩
    exact ⟨nf, redT.conv typeEq, neutral, laws.convNe_conv refl typeEq⟩
  · rintro t t' ⟨nf, nf', redT, redT', neutral, neutral', equal⟩
    exact ⟨nf, nf', redT.conv typeEq, redT'.conv typeEq, neutral, neutral',
      laws.convNe_conv equal typeEq⟩

/-! ## Function and pair types -/

section Parts

variable {n : Nat} {Γ : Ctx Head n} {dom dom₂ : Tm Head n} {cod cod₂ : Tm Head (n + 1)}
  {P : PolyPack S Γ dom cod} {P₂ : PolyPack S Γ dom₂ cod₂}

theorem piPack_forward (laws : S.E.Laws S.R S.roles)
    (conv : S.E.convTy Γ (.pi dom cod) (.pi dom₂ cod₂))
    (domain : ∀ {m : Nat} {Δ : Ctx Head m} {ρ : Ren n m} (w : World S Γ Δ ρ),
      PackEquiv (P.domPack w) (P₂.domPack w))
    (codomain : ∀ {m : Nat} {Δ : Ctx Head m} {ρ : Ren n m} (w : World S Γ Δ ρ)
      {a : Tm Head m} (ha : (P.domPack w).redTm a) (ha₂ : (P₂.domPack w).redTm a),
      PackEquiv (P.codPack w ha) (P₂.codPack w ha₂)) :
    (∀ {B}, (piPack S Γ dom cod P).eqTy B → (piPack S Γ dom₂ cod₂ P₂).eqTy B) ∧
    (∀ {t}, (piPack S Γ dom cod P).redTm t → (piPack S Γ dom₂ cod₂ P₂).redTm t) ∧
    (∀ {t t'}, (piPack S Γ dom cod P).eqTm t t' →
      (piPack S Γ dom₂ cod₂ P₂).eqTm t t') := by
  have typeEq := laws.convTy_sound conv
  have redForward : ∀ {t}, PiRedTm S P t → PiRedTm S P₂ t := by
    rintro t ⟨nf, redT, isFun, refl, apps, appEqs⟩
    refine ⟨nf, redT.conv typeEq, isFun, laws.convTm_conv refl typeEq, ?_, ?_⟩
    · intro m Δ ρ w a ha₂
      have ha := (domain w).redTm.mpr ha₂
      exact (codomain w ha ha₂).redTm.mp (apps w ha)
    · intro m Δ ρ w a b ha₂ hb₂ eq₂
      have ha := (domain w).redTm.mpr ha₂
      exact (codomain w ha ha₂).eqTm.mp
        (appEqs w ha ((domain w).redTm.mpr hb₂) ((domain w).eqTm.mpr eq₂))
  refine ⟨?_, redForward, ?_⟩
  · rintro B ⟨d, c, redB, equal, domEq, codEq⟩
    refine ⟨d, c, redB, laws.convTy_trans (laws.convTy_symm conv) equal,
      fun w => (domain w).eqTy.mp (domEq w), ?_⟩
    intro m Δ ρ w a ha₂
    have ha := (domain w).redTm.mpr ha₂
    exact (codomain w ha ha₂).eqTy.mp (codEq w ha)
  · rintro t t' ⟨redT, redT', nf, nf', r, r', isFun, isFun', equal, apps⟩
    refine ⟨redForward redT, redForward redT', nf, nf', r.conv typeEq, r'.conv typeEq,
      isFun, isFun', laws.convTm_conv equal typeEq, ?_⟩
    intro m Δ ρ w a ha₂
    have ha := (domain w).redTm.mpr ha₂
    exact (codomain w ha ha₂).eqTm.mp (apps w ha)

theorem sigmaPack_forward (laws : S.E.Laws S.R S.roles)
    (conv : S.E.convTy Γ (.sigma dom cod) (.sigma dom₂ cod₂))
    (domain : ∀ {m : Nat} {Δ : Ctx Head m} {ρ : Ren n m} (w : World S Γ Δ ρ),
      PackEquiv (P.domPack w) (P₂.domPack w))
    (codomain : ∀ {m : Nat} {Δ : Ctx Head m} {ρ : Ren n m} (w : World S Γ Δ ρ)
      {a : Tm Head m} (ha : (P.domPack w).redTm a) (ha₂ : (P₂.domPack w).redTm a),
      PackEquiv (P.codPack w ha) (P₂.codPack w ha₂)) :
    (∀ {B}, (sigmaPack S Γ dom cod P).eqTy B → (sigmaPack S Γ dom₂ cod₂ P₂).eqTy B) ∧
    (∀ {t}, (sigmaPack S Γ dom cod P).redTm t → (sigmaPack S Γ dom₂ cod₂ P₂).redTm t) ∧
    (∀ {t t'}, (sigmaPack S Γ dom cod P).eqTm t t' →
      (sigmaPack S Γ dom₂ cod₂ P₂).eqTm t t') := by
  have typeEq := laws.convTy_sound conv
  have redForward : ∀ {t}, SigmaRedTm S P t → SigmaRedTm S P₂ t := by
    rintro t ⟨nf, redT, isPair, refl, first, second⟩
    refine ⟨nf, redT.conv typeEq, isPair, laws.convTm_conv refl typeEq,
      fun w => (domain w).redTm.mp (first w), ?_⟩
    intro m Δ ρ w
    exact (codomain w (first w) _).redTm.mp (second w)
  refine ⟨?_, redForward, ?_⟩
  · rintro B ⟨d, c, redB, equal, domEq, codEq⟩
    refine ⟨d, c, redB, laws.convTy_trans (laws.convTy_symm conv) equal,
      fun w => (domain w).eqTy.mp (domEq w), ?_⟩
    intro m Δ ρ w a ha₂
    have ha := (domain w).redTm.mpr ha₂
    exact (codomain w ha ha₂).eqTy.mp (codEq w ha)
  · rintro t t' ⟨redT, redT', nf, nf', r, r', isPair, isPair', equal, firsts, seconds⟩
    refine ⟨redForward redT, redForward redT', nf, nf', r.conv typeEq, r'.conv typeEq,
      isPair, isPair', laws.convTm_conv equal typeEq, fun w => (domain w).eqTm.mp (firsts w), ?_⟩
    intro m Δ ρ w first₂
    have first := (domain w).redTm.mpr first₂
    exact (codomain w first first₂).eqTm.mp (seconds w first)

end Parts

/-! ## Identity types -/

theorem idPack_forward {n : Nat} {Γ : Ctx Head n} {ty ty₂ lhs lhs₂ rhs rhs₂ : Tm Head n}
    {tyPack tyPack₂ : Pack Head n} (laws : S.E.Laws S.R S.roles)
    (conv : S.E.convTy Γ (.id ty lhs rhs) (.id ty₂ lhs₂ rhs₂))
    (tyEquiv : PackEquiv tyPack tyPack₂) (tyTypeEq : TypeEq S.R Γ ty ty₂)
    (lhsEq : tyPack.eqTm lhs lhs₂) (rhsEq : tyPack.eqTm rhs rhs₂)
    (tySymm : ∀ {t t'}, tyPack.eqTm t t' → tyPack.eqTm t' t)
    (tyTrans : ∀ {t t' t''}, tyPack.eqTm t t' → tyPack.eqTm t' t'' → tyPack.eqTm t t'') :
    (∀ {B}, (idPack S Γ ty lhs rhs tyPack).eqTy B →
      (idPack S Γ ty₂ lhs₂ rhs₂ tyPack₂).eqTy B) ∧
    (∀ {t}, (idPack S Γ ty lhs rhs tyPack).redTm t →
      (idPack S Γ ty₂ lhs₂ rhs₂ tyPack₂).redTm t) ∧
    (∀ {t t'}, (idPack S Γ ty lhs rhs tyPack).eqTm t t' →
      (idPack S Γ ty₂ lhs₂ rhs₂ tyPack₂).eqTm t t') := by
  have typeEq := laws.convTy_sound conv
  have moveLhs : ∀ {x}, tyPack.eqTm lhs x → tyPack₂.eqTm lhs₂ x :=
    fun h => tyEquiv.eqTm.mp (tyTrans (tySymm lhsEq) h)
  have moveRhs : ∀ {x}, tyPack.eqTm rhs x → tyPack₂.eqTm rhs₂ x :=
    fun h => tyEquiv.eqTm.mp (tyTrans (tySymm rhsEq) h)
  refine ⟨?_, ?_, ?_⟩
  · rintro B ⟨t, l, r, redB, equal, tyEq, lEq, rEq⟩
    exact ⟨t, l, r, redB, laws.convTy_trans (laws.convTy_symm conv) equal,
      tyEquiv.eqTy.mp tyEq, moveLhs lEq, moveRhs rEq⟩
  · rintro t ⟨nf, redT, refl, prop⟩
    refine ⟨nf, redT.conv typeEq, laws.convTm_conv refl typeEq, ?_⟩
    rcases prop with ⟨x, rfl, typing, left, right⟩ | ⟨neutral, reflN⟩
    · exact .inl ⟨x, rfl, Typed.convType typing tyTypeEq, moveLhs left, moveRhs right⟩
    · exact .inr ⟨neutral, laws.convNe_conv reflN typeEq⟩
  · rintro t t' ⟨nf, nf', redT, redT', equal, prop⟩
    refine ⟨nf, nf', redT.conv typeEq, redT'.conv typeEq, laws.convTm_conv equal typeEq, ?_⟩
    rcases prop with ⟨x, x', rfl, rfl, typing, typing', l, l', r, r'⟩ |
      ⟨neutral, neutral', equalN⟩
    · exact .inl ⟨x, x', rfl, rfl, Typed.convType typing tyTypeEq, Typed.convType typing' tyTypeEq,
        moveLhs l, moveLhs l', moveRhs r, moveRhs r'⟩
    · exact .inr ⟨neutral, neutral', laws.convNe_conv equalN typeEq⟩

/-! ## Simple inductive types -/

theorem indPack_forward {n : Nat} {Γ : Ctx Head n} {T : DeclName}
    {ctors : List (DeclName × List (Field Head))} {fieldPack fieldPack₂ : Tm Head 0 → Pack Head n}
    (fields : ∀ {F}, IsClosedField ctors F → PackEquiv (fieldPack F) (fieldPack₂ F)) :
    (∀ {B}, (indPack S Γ T ctors fieldPack).eqTy B → (indPack S Γ T ctors fieldPack₂).eqTy B) ∧
    (∀ {t}, (indPack S Γ T ctors fieldPack).redTm t →
      (indPack S Γ T ctors fieldPack₂).redTm t) ∧
    (∀ {t t'}, (indPack S Γ T ctors fieldPack).eqTm t t' →
      (indPack S Γ T ctors fieldPack₂).eqTm t t') :=
  ⟨id, IndRedTm.transport fun closed _ h => (fields closed).redTm.mp h,
    IndEqTm.transport fun closed _ _ h => (fields closed).eqTm.mp h⟩

/-! ## Irrelevance -/

private theorem iffs {n : Nat} {P P' : Pack Head n}
    (forward : (∀ {B}, P.eqTy B → P'.eqTy B) ∧ (∀ {t}, P.redTm t → P'.redTm t) ∧
      (∀ {t u}, P.eqTm t u → P'.eqTm t u))
    (backward : (∀ {B}, P'.eqTy B → P.eqTy B) ∧ (∀ {t}, P'.redTm t → P.redTm t) ∧
      (∀ {t u}, P'.eqTm t u → P.eqTm t u)) : PackEquiv P P' :=
  ⟨⟨forward.1, backward.1⟩, ⟨forward.2.1, backward.2.1⟩, ⟨forward.2.2, backward.2.2⟩⟩

/-- Reducibility derivations of reducibly equal types give equivalent packs,
at any two levels. -/
theorem LR.irrelevant (laws : S.E.Laws S.R S.roles) {l : L} {n : Nat}
    {Γ : Ctx Head n} {A : Tm Head n} {P : Pack Head n}
    (first : LR S l (levelsBelow S l) Γ A P) :
    ∀ {l' : L} {A' : Tm Head n} {P' : Pack Head n},
      LR S l' (levelsBelow S l') Γ A' P' → P.eqTy A' → PackEquiv P P' := by
  induction first with
  | @sort n Γ A u isUniverse below₁ formed red =>
      intro l' A' P' second eqTy
      obtain ⟨u', redA', same⟩ := eqTy
      have universe' : S.R.isUniverse u' := ((HeadSame.level S.levels same).1).mp isUniverse
      cases second with
      | @sort _ _ _ u₂ isUniverse₂ below₂ formed₂ red₂ =>
          have h := Tm.head.inj (RedTy.unique redA' red₂ (head_whnf S.shape _)
            (head_whnf S.shape _))
          subst h
          exact iffs
            (universePack_forward laws same red.targetType red₂.targetType below₁ below₂)
            (universePack_forward laws (HeadSame.symm S.levels same) red₂.targetType red.targetType
              below₂ below₁)
      | @neutral _ _ _ ty₂ u₂ red₂ neutral₂ _ _ _ =>
          exact absurd (RedTy.unique redA' red₂ (head_whnf S.shape _)
            (neutral₂.whnf S.shape)).symm (neutral₂.not_former.1 _)
      | @ground _ _ _ h₂ u₂ notUniverse₂ red₂ _ _ =>
          have h := Tm.head.inj (RedTy.unique redA' red₂ (head_whnf S.shape _)
            (head_whnf S.shape _))
          subst h
          exact absurd universe' notUniverse₂
      | @pi _ _ _ dom₂ cod₂ red₂ _ _ _ _ _ _ =>
          exact absurd (RedTy.unique redA' red₂ (head_whnf S.shape _) (pi_whnf S.shape _ _))
            (by intro h; cases h)
      | @sigma _ _ _ dom₂ cod₂ red₂ _ _ _ _ _ _ =>
          exact absurd (RedTy.unique redA' red₂ (head_whnf S.shape _)
            (sigma_whnf S.shape _ _)) (by intro h; cases h)
      | @ident _ _ _ ty₂ lhs₂ rhs₂ red₂ _ _ _ _ _ _ _ _ _ =>
          exact absurd (RedTy.unique redA' red₂ (head_whnf S.shape _)
            (id_whnf S.shape _ _ _)) (by intro h; cases h)
      | @inductiveType _ _ _ T₂ _ _ red₂ role₂ _ _ _ _ =>
          exact absurd (RedTy.unique redA' red₂ (head_whnf S.shape _)
            (inductive_whnf S.shape role₂)) (by intro h; cases h)
  | @neutral n Γ A ty u red neutral isUniverse typing refl =>
      intro l' A' P' second eqTy
      obtain ⟨ty', redA', neutral', v, hv, conv⟩ := eqTy
      cases second with
      | @neutral _ _ _ ty₂ u₂ red₂ neutral₂ _ _ _ =>
          have h := RedTy.unique redA' red₂ (neutral'.whnf S.shape) (neutral₂.whnf S.shape)
          subst h
          exact iffs (neutralPack_forward laws hv neutral neutral' conv)
            (neutralPack_forward laws hv neutral' neutral (laws.convNe_symm conv))
      | @sort _ _ _ u₂ _ _ _ red₂ =>
          exact absurd (RedTy.unique redA' red₂ (neutral'.whnf S.shape)
            (head_whnf S.shape _)) (neutral'.not_former.1 _)
      | @ground _ _ _ h₂ u₂ _ red₂ _ _ =>
          exact absurd (RedTy.unique redA' red₂ (neutral'.whnf S.shape)
            (head_whnf S.shape _)) (neutral'.not_former.1 _)
      | @pi _ _ _ dom₂ cod₂ red₂ _ _ _ _ _ _ =>
          exact absurd (RedTy.unique redA' red₂ (neutral'.whnf S.shape)
            (pi_whnf S.shape _ _)) (neutral'.not_former.2.1 _ _)
      | @sigma _ _ _ dom₂ cod₂ red₂ _ _ _ _ _ _ =>
          exact absurd (RedTy.unique redA' red₂ (neutral'.whnf S.shape)
            (sigma_whnf S.shape _ _)) (neutral'.not_former.2.2.1 _ _)
      | @ident _ _ _ ty₂ lhs₂ rhs₂ red₂ _ _ _ _ _ _ _ _ _ =>
          exact absurd (RedTy.unique redA' red₂ (neutral'.whnf S.shape)
            (id_whnf S.shape _ _ _)) (neutral'.not_former.2.2.2 _ _ _)
      | @inductiveType _ _ _ T₂ _ _ red₂ role₂ _ _ _ _ =>
          exact absurd (RedTy.unique redA' red₂ (neutral'.whnf S.shape)
            (inductive_whnf S.shape role₂)) (neutral'.ne_inductive role₂)
  | @ground n Γ A h u notUniverse red typing isUniverse =>
      intro l' A' P' second eqTy
      obtain ⟨h', redA', same⟩ := eqTy
      cases second with
      | @ground _ _ _ h₂ u₂ _ red₂ _ _ =>
          have e := Tm.head.inj (RedTy.unique redA' red₂ (head_whnf S.shape _)
            (head_whnf S.shape _))
          subst e
          exact iffs (groundPack_forward laws same red.targetType red₂.targetType)
            (groundPack_forward laws (HeadSame.symm S.levels same) red₂.targetType red.targetType)
      | @sort _ _ _ u₂ isUniverse₂ _ _ red₂ =>
          have e := Tm.head.inj (RedTy.unique redA' red₂ (head_whnf S.shape _)
            (head_whnf S.shape _))
          subst e
          exact absurd (((HeadSame.level S.levels same).1).mpr isUniverse₂) notUniverse
      | @neutral _ _ _ ty₂ u₂ red₂ neutral₂ _ _ _ =>
          exact absurd (RedTy.unique redA' red₂ (head_whnf S.shape _)
            (neutral₂.whnf S.shape)).symm (neutral₂.not_former.1 _)
      | @pi _ _ _ dom₂ cod₂ red₂ _ _ _ _ _ _ =>
          exact absurd (RedTy.unique redA' red₂ (head_whnf S.shape _) (pi_whnf S.shape _ _))
            (by intro e; cases e)
      | @sigma _ _ _ dom₂ cod₂ red₂ _ _ _ _ _ _ =>
          exact absurd (RedTy.unique redA' red₂ (head_whnf S.shape _)
            (sigma_whnf S.shape _ _)) (by intro e; cases e)
      | @ident _ _ _ ty₂ lhs₂ rhs₂ red₂ _ _ _ _ _ _ _ _ _ =>
          exact absurd (RedTy.unique redA' red₂ (head_whnf S.shape _)
            (id_whnf S.shape _ _ _)) (by intro e; cases e)
      | @inductiveType _ _ _ T₂ _ _ red₂ role₂ _ _ _ _ =>
          exact absurd (RedTy.unique redA' red₂ (head_whnf S.shape _)
            (inductive_whnf S.shape role₂)) (by intro e; cases e)
  | @pi n Γ A dom cod red domType codType refl P domAdequate codAdequate domIH codIH =>
      intro l' A' P' second eqTy
      obtain ⟨d, c, redA', conv, domEq, codEq⟩ := eqTy
      cases second with
      | @pi _ _ _ dom₂ cod₂ red₂ _ _ _ P₂ domAdequate₂ codAdequate₂ =>
          obtain ⟨rfl, rfl⟩ := Tm.pi.inj (RedTy.unique redA' red₂ (pi_whnf S.shape _ _)
            (pi_whnf S.shape _ _))
          have domain : ∀ {m : Nat} {Δ : Ctx Head m} {ρ : Ren n m} (w : World S Γ Δ ρ),
              PackEquiv (P.domPack w) (P₂.domPack w) :=
            fun w => domIH w (domAdequate₂ w) (domEq w)
          have codomain : ∀ {m : Nat} {Δ : Ctx Head m} {ρ : Ren n m} (w : World S Γ Δ ρ)
              {a : Tm Head m} (ha : (P.domPack w).redTm a) (ha₂ : (P₂.domPack w).redTm a),
              PackEquiv (P.codPack w ha) (P₂.codPack w ha₂) :=
            by
              intro _ _ _ w _ ha ha₂
              exact codIH w ha (codAdequate₂ w ha₂) (codEq w ha)
          exact iffs (piPack_forward laws conv domain codomain)
            (piPack_forward laws (laws.convTy_symm conv) (fun w => (domain w).symm)
              (by intro _ _ _ w _ ha₂ ha; exact (codomain w ha ha₂).symm))
      | @sort _ _ _ u₂ _ _ _ red₂ =>
          exact absurd (RedTy.unique redA' red₂ (pi_whnf S.shape _ _) (head_whnf S.shape _))
            (by intro e; cases e)
      | @neutral _ _ _ ty₂ u₂ red₂ neutral₂ _ _ _ =>
          exact absurd (RedTy.unique redA' red₂ (pi_whnf S.shape _ _)
            (neutral₂.whnf S.shape)).symm (neutral₂.not_former.2.1 _ _)
      | @ground _ _ _ h₂ u₂ _ red₂ _ _ =>
          exact absurd (RedTy.unique redA' red₂ (pi_whnf S.shape _ _) (head_whnf S.shape _))
            (by intro e; cases e)
      | @sigma _ _ _ dom₂ cod₂ red₂ _ _ _ _ _ _ =>
          exact absurd (RedTy.unique redA' red₂ (pi_whnf S.shape _ _)
            (sigma_whnf S.shape _ _)) (by intro e; cases e)
      | @ident _ _ _ ty₂ lhs₂ rhs₂ red₂ _ _ _ _ _ _ _ _ _ =>
          exact absurd (RedTy.unique redA' red₂ (pi_whnf S.shape _ _)
            (id_whnf S.shape _ _ _)) (by intro e; cases e)
      | @inductiveType _ _ _ T₂ _ _ red₂ role₂ _ _ _ _ =>
          exact absurd (RedTy.unique redA' red₂ (pi_whnf S.shape _ _)
            (inductive_whnf S.shape role₂)) (by intro e; cases e)
  | @sigma n Γ A dom cod red domType codType refl P domAdequate codAdequate domIH codIH =>
      intro l' A' P' second eqTy
      obtain ⟨d, c, redA', conv, domEq, codEq⟩ := eqTy
      cases second with
      | @sigma _ _ _ dom₂ cod₂ red₂ _ _ _ P₂ domAdequate₂ codAdequate₂ =>
          obtain ⟨rfl, rfl⟩ := Tm.sigma.inj (RedTy.unique redA' red₂
            (sigma_whnf S.shape _ _) (sigma_whnf S.shape _ _))
          have domain : ∀ {m : Nat} {Δ : Ctx Head m} {ρ : Ren n m} (w : World S Γ Δ ρ),
              PackEquiv (P.domPack w) (P₂.domPack w) :=
            fun w => domIH w (domAdequate₂ w) (domEq w)
          have codomain : ∀ {m : Nat} {Δ : Ctx Head m} {ρ : Ren n m} (w : World S Γ Δ ρ)
              {a : Tm Head m} (ha : (P.domPack w).redTm a) (ha₂ : (P₂.domPack w).redTm a),
              PackEquiv (P.codPack w ha) (P₂.codPack w ha₂) :=
            by
              intro _ _ _ w _ ha ha₂
              exact codIH w ha (codAdequate₂ w ha₂) (codEq w ha)
          exact iffs (sigmaPack_forward laws conv domain codomain)
            (sigmaPack_forward laws (laws.convTy_symm conv) (fun w => (domain w).symm)
              (by intro _ _ _ w _ ha₂ ha; exact (codomain w ha ha₂).symm))
      | @sort _ _ _ u₂ _ _ _ red₂ =>
          exact absurd (RedTy.unique redA' red₂ (sigma_whnf S.shape _ _)
            (head_whnf S.shape _)) (by intro e; cases e)
      | @neutral _ _ _ ty₂ u₂ red₂ neutral₂ _ _ _ =>
          exact absurd (RedTy.unique redA' red₂ (sigma_whnf S.shape _ _)
            (neutral₂.whnf S.shape)).symm (neutral₂.not_former.2.2.1 _ _)
      | @ground _ _ _ h₂ u₂ _ red₂ _ _ =>
          exact absurd (RedTy.unique redA' red₂ (sigma_whnf S.shape _ _)
            (head_whnf S.shape _)) (by intro e; cases e)
      | @pi _ _ _ dom₂ cod₂ red₂ _ _ _ _ _ _ =>
          exact absurd (RedTy.unique redA' red₂ (sigma_whnf S.shape _ _)
            (pi_whnf S.shape _ _)) (by intro e; cases e)
      | @ident _ _ _ ty₂ lhs₂ rhs₂ red₂ _ _ _ _ _ _ _ _ _ =>
          exact absurd (RedTy.unique redA' red₂ (sigma_whnf S.shape _ _)
            (id_whnf S.shape _ _ _)) (by intro e; cases e)
      | @inductiveType _ _ _ T₂ _ _ red₂ role₂ _ _ _ _ =>
          exact absurd (RedTy.unique redA' red₂ (sigma_whnf S.shape _ _)
            (inductive_whnf S.shape role₂)) (by intro e; cases e)
  | @ident n Γ A ty lhs rhs red refl tyPack tyAdequate lhsRed rhsRed lhsRefl rhsRefl
      tySymm tyTrans tyIH =>
      intro l' A' P' second eqTy
      obtain ⟨t, lh, rh, redA', conv, tyEq, lEq, rEq⟩ := eqTy
      cases second with
      | @ident _ _ _ ty₂ lhs₂ rhs₂ red₂ _ tyPack₂ tyAdequate₂ _ _ _ _ tySymm₂ tyTrans₂ =>
          obtain ⟨rfl, rfl, rfl⟩ := Tm.id.inj (RedTy.unique redA' red₂
            (id_whnf S.shape _ _ _) (id_whnf S.shape _ _ _))
          have tyEquiv := tyIH tyAdequate₂ tyEq
          have tyTypeEq : TypeEq S.R Γ ty t :=
            laws.convTy_sound ((tyAdequate.escape laws).eqTy tyEq)
          exact iffs
            (idPack_forward laws conv tyEquiv tyTypeEq lEq rEq tySymm tyTrans)
            (idPack_forward laws (laws.convTy_symm conv) tyEquiv.symm tyTypeEq.symm
              (tyEquiv.eqTm.mp (tySymm lEq)) (tyEquiv.eqTm.mp (tySymm rEq)) tySymm₂ tyTrans₂)
      | @sort _ _ _ u₂ _ _ _ red₂ =>
          exact absurd (RedTy.unique redA' red₂ (id_whnf S.shape _ _ _)
            (head_whnf S.shape _)) (by intro e; cases e)
      | @neutral _ _ _ ty₂ u₂ red₂ neutral₂ _ _ _ =>
          exact absurd (RedTy.unique redA' red₂ (id_whnf S.shape _ _ _)
            (neutral₂.whnf S.shape)).symm (neutral₂.not_former.2.2.2 _ _ _)
      | @ground _ _ _ h₂ u₂ _ red₂ _ _ =>
          exact absurd (RedTy.unique redA' red₂ (id_whnf S.shape _ _ _)
            (head_whnf S.shape _)) (by intro e; cases e)
      | @pi _ _ _ dom₂ cod₂ red₂ _ _ _ _ _ _ =>
          exact absurd (RedTy.unique redA' red₂ (id_whnf S.shape _ _ _)
            (pi_whnf S.shape _ _)) (by intro e; cases e)
      | @sigma _ _ _ dom₂ cod₂ red₂ _ _ _ _ _ _ =>
          exact absurd (RedTy.unique redA' red₂ (id_whnf S.shape _ _ _)
            (sigma_whnf S.shape _ _)) (by intro e; cases e)
      | @inductiveType _ _ _ T₂ _ _ red₂ role₂ _ _ _ _ =>
          exact absurd (RedTy.unique redA' red₂ (id_whnf S.shape _ _ _)
            (inductive_whnf S.shape role₂)) (by intro e; cases e)
  | @inductiveType n Γ A T ctors u red role typing isUniverse fieldPack fieldAdequate fieldIH =>
      intro l' A' P' second redA'
      have constWhnf := inductive_whnf (n := n) S.shape role
      cases second with
      | @inductiveType _ _ _ T₂ ctors₂ _ red₂ role₂ _ _ fieldPack₂ fieldAdequate₂ =>
          have same := Tm.const.inj (RedTy.unique redA' red₂ constWhnf
            (inductive_whnf S.shape role₂))
          subst same
          have sameCtors := role.symm.trans role₂
          injection sameCtors with sameCtors
          subst sameCtors
          have fields : ∀ {F}, IsClosedField ctors F → PackEquiv (fieldPack F) (fieldPack₂ F) :=
            fun ⟨_, _, mem, closed⟩ => fieldIH mem closed (fieldAdequate₂ mem closed)
              (LogRel.reflexive S l (fieldAdequate mem closed)).eqTy
          exact iffs (indPack_forward fields) (indPack_forward fun closed => (fields closed).symm)
      | @sort _ _ _ u₂ _ _ _ red₂ =>
          exact absurd (RedTy.unique redA' red₂ constWhnf (head_whnf S.shape _))
            (by intro e; cases e)
      | @neutral _ _ _ ty₂ u₂ red₂ neutral₂ _ _ _ =>
          exact absurd (RedTy.unique redA' red₂ constWhnf (neutral₂.whnf S.shape)).symm
            (neutral₂.ne_inductive role)
      | @ground _ _ _ h₂ u₂ _ red₂ _ _ =>
          exact absurd (RedTy.unique redA' red₂ constWhnf (head_whnf S.shape _))
            (by intro e; cases e)
      | @pi _ _ _ dom₂ cod₂ red₂ _ _ _ _ _ _ =>
          exact absurd (RedTy.unique redA' red₂ constWhnf (pi_whnf S.shape _ _))
            (by intro e; cases e)
      | @sigma _ _ _ dom₂ cod₂ red₂ _ _ _ _ _ _ =>
          exact absurd (RedTy.unique redA' red₂ constWhnf (sigma_whnf S.shape _ _))
            (by intro e; cases e)
      | @ident _ _ _ ty₂ lhs₂ rhs₂ red₂ _ _ _ _ _ _ _ _ _ =>
          exact absurd (RedTy.unique redA' red₂ constWhnf (id_whnf S.shape _ _ _))
            (by intro e; cases e)

/-! ## One pack per type -/

/-- `A` is reducible in `Γ` with pack `P`, at some level. -/
def Reducible (S : Setting Head L) {n : Nat} (Γ : Ctx Head n) (A : Tm Head n)
    (P : Pack Head n) : Prop :=
  ∃ l, LogRel S l Γ A P

theorem LogRel.reducible {l : L} {n : Nat} {Γ : Ctx Head n} {A : Tm Head n}
    {P : Pack Head n} (reducible : LogRel S l Γ A P) : Reducible S Γ A P :=
  ⟨l, reducible⟩

section Reducible

variable (laws : S.E.Laws S.R S.roles)
include laws

/-- Reducibly equal types have the same pack. -/
theorem Reducible.conv {n : Nat} {Γ : Ctx Head n} {A B : Tm Head n} {P Q : Pack Head n}
    (reducible : Reducible S Γ A P) (reducible' : Reducible S Γ B Q) (equal : P.eqTy B) :
    P = Q := by
  obtain ⟨l, r⟩ := reducible
  obtain ⟨l', r'⟩ := reducible'
  exact (LR.irrelevant laws r r' equal).eq

/-- A reducible type has one pack. -/
theorem Reducible.unique {n : Nat} {Γ : Ctx Head n} {A : Tm Head n} {P Q : Pack Head n}
    (reducible : Reducible S Γ A P) (reducible' : Reducible S Γ A Q) : P = Q := by
  obtain ⟨l, r⟩ := reducible
  exact Reducible.conv laws ⟨l, r⟩ reducible' (LogRel.reflexive S l r).eqTy

end Reducible

/-! ## The pack of a type -/

/-- The pack of `A`: what every reducibility derivation of `A` provides. -/
def packOf (S : Setting Head L) {n : Nat} (Γ : Ctx Head n) (A : Tm Head n) : Pack Head n where
  eqTy B := ∃ P, Reducible S Γ A P ∧ P.eqTy B
  redTm t := ∃ P, Reducible S Γ A P ∧ P.redTm t
  eqTm t u := ∃ P, Reducible S Γ A P ∧ P.eqTm t u

/-- The pack of a reducible type is `packOf`. -/
theorem Reducible.eq_packOf (laws : S.E.Laws S.R S.roles) {n : Nat} {Γ : Ctx Head n}
    {A : Tm Head n} {P : Pack Head n} (reducible : Reducible S Γ A P) :
    P = packOf S Γ A := by
  apply PackEquiv.eq
  refine ⟨⟨fun h => ⟨P, reducible, h⟩, ?_⟩, ⟨fun h => ⟨P, reducible, h⟩, ?_⟩,
    ⟨fun h => ⟨P, reducible, h⟩, ?_⟩⟩
  · rintro ⟨Q, reducible', h⟩
    rwa [reducible.unique laws reducible']
  · rintro ⟨Q, reducible', h⟩
    rwa [reducible.unique laws reducible']
  · rintro ⟨Q, reducible', h⟩
    rwa [reducible.unique laws reducible']

/-- The pack of a reducible type is reducible. -/
theorem Reducible.packOf_self (laws : S.E.Laws S.R S.roles) {n : Nat} {Γ : Ctx Head n}
    {A : Tm Head n} {P : Pack Head n} (reducible : Reducible S Γ A P) :
    Reducible S Γ A (packOf S Γ A) := by
  rw [← reducible.eq_packOf laws]
  exact reducible

/-- A reducible type is reducible with the pack `packOf` at its level. -/
theorem LogRel.packOf (laws : S.E.Laws S.R S.roles) {l : L} {n : Nat} {Γ : Ctx Head n}
    {A : Tm Head n} {P : Pack Head n} (reducible : LogRel S l Γ A P) :
    LogRel S l Γ A (packOf S Γ A) := by
  rw [← (LogRel.reducible reducible).eq_packOf laws]
  exact reducible

end Normalization
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
