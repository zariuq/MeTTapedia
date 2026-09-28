import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.Weakening

/-!
# Neutral terms are reducible

A typed neutral term that is convertible to itself is reducible at every
reducible type, and two typed neutral terms that are convertible are reducibly
equal. At a dependent function type the neutral term applied to a reducible
argument is again neutral, and at a pair type so are its projections, so these
cases recurse on the codomain. At a universe a neutral term is a neutral type,
reducible at the lower level.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Normalization

open UniverseLevel (LevelOrder)

variable {Head L : Type} [LevelOrder L] {S : Setting Head L}

/-- What reflection gives at one reducible type. -/
structure Reflects (S : Setting Head L) {n : Nat} (Γ : Ctx Head n) (A : Tm Head n)
    (P : Pack Head n) : Prop where
  redTm : ∀ {t}, Neutral S.roles t → Typed S.R Γ t A → S.E.convNe Γ t t A → P.redTm t
  eqTm : ∀ {t u}, Neutral S.roles t → Neutral S.roles u → Typed S.R Γ t A →
    Typed S.R Γ u A → S.E.convNe Γ t u A → P.eqTm t u

theorem LR.reflects (laws : S.E.Laws S.R S.roles) {l : L} {n : Nat} {Γ : Ctx Head n}
    {A : Tm Head n} {P : Pack Head n} (reducible : LR S l (levelsBelow S l) Γ A P) :
    Reflects S Γ A P := by
  induction reducible with
  | @sort n Γ A u isUniverse below₁ formed red =>
      have typeEq := red.typeEq
      have lowerNeutral : ∀ {t : Tm Head n}, Neutral S.roles t → Typed S.R Γ t (.head u) →
          S.E.convNe Γ t t (.head u) →
          levelsBelow S l (S.levels.level u) Γ t (neutralPack S Γ t) := by
        intro t neutral typing refl
        exact (levelsBelow_iff S below₁ Γ t _).mpr
          (.neutral (RedTy.refl ⟨u, isUniverse, typing⟩) neutral isUniverse typing refl)
      refine ⟨?_, ?_⟩
      · intro t neutral typing refl
        have typing' := Typed.convType typing typeEq
        have refl' := laws.convNe_conv refl typeEq
        exact ⟨t, RedTm.refl typing', .inr (.inr (.inr (.inr (.inl neutral)))),
          laws.convTm_of_convNe (.inl neutral) (.inl neutral) refl', _,
          lowerNeutral neutral typing' refl'⟩
      · intro t t' neutral neutral' typing typing' equal
        have ty := Typed.convType typing typeEq
        have ty' := Typed.convType typing' typeEq
        have equal' := laws.convNe_conv equal typeEq
        have refl : S.E.convNe Γ t t (.head u) :=
          laws.convNe_trans equal' (laws.convNe_symm equal')
        have refl' : S.E.convNe Γ t' t' (.head u) :=
          laws.convNe_trans (laws.convNe_symm equal') equal'
        exact ⟨t, t', RedTm.refl ty, RedTm.refl ty',
          .inr (.inr (.inr (.inr (.inl neutral)))), .inr (.inr (.inr (.inr (.inl neutral')))),
          laws.convTm_of_convNe (.inl neutral) (.inl neutral') equal',
          ⟨_, lowerNeutral neutral' ty' refl'⟩, _,
          lowerNeutral neutral ty refl,
          ⟨t', RedTy.refl ⟨u, isUniverse, ty'⟩, neutral', u, isUniverse, equal'⟩⟩
  | @neutral n Γ A ty u red neutral isUniverse typing refl =>
      have typeEq := red.typeEq
      refine ⟨?_, ?_⟩
      · intro t neutralT typingT reflT
        exact ⟨t, RedTm.refl (Typed.convType typingT typeEq), neutralT,
          laws.convNe_conv reflT typeEq⟩
      · intro t t' n₁ n₂ ty₁ ty₂ equal
        exact ⟨t, t', RedTm.refl (Typed.convType ty₁ typeEq),
          RedTm.refl (Typed.convType ty₂ typeEq), n₁, n₂, laws.convNe_conv equal typeEq⟩
  | @ground n Γ A h u notUniverse red typing isUniverse =>
      have typeEq := red.typeEq
      refine ⟨?_, ?_⟩
      · intro t neutralT typingT reflT
        exact ⟨t, RedTm.refl (Typed.convType typingT typeEq), neutralT,
          laws.convNe_conv reflT typeEq⟩
      · intro t t' n₁ n₂ ty₁ ty₂ equal
        exact ⟨t, t', RedTm.refl (Typed.convType ty₁ typeEq),
          RedTm.refl (Typed.convType ty₂ typeEq), n₁, n₂, laws.convNe_conv equal typeEq⟩
  | @pi n Γ A dom cod red domType codType refl P domAdequate codAdequate domIH codIH =>
      have typeEq := red.typeEq
      /- Applications of a renamed neutral function. -/
      have applied : ∀ {t t' : Tm Head n} {m : Nat} {Δ : Ctx Head m} {ρ : Ren n m}
          (w : World S Γ Δ ρ) {a b : Tm Head m} (ha : (P.domPack w).redTm a),
          (P.domPack w).redTm b → (P.domPack w).eqTm a b →
          Typed S.R Γ t (.pi dom cod) → Typed S.R Γ t' (.pi dom cod) →
          S.E.convNe Γ t t' (.pi dom cod) →
          Typed S.R Δ (.app (Presentation.rename ρ t) a)
            (inst0 a (Presentation.rename (liftRen ρ) cod)) ∧
          Typed S.R Δ (.app (Presentation.rename ρ t') b)
            (inst0 a (Presentation.rename (liftRen ρ) cod)) ∧
          S.E.convNe Δ (.app (Presentation.rename ρ t) a)
            (.app (Presentation.rename ρ t') b)
            (inst0 a (Presentation.rename (liftRen ρ) cod)) := by
        intro t t' m Δ ρ w a b ha hb equal typing typing' conv
        have escA := (domAdequate w).escape laws
        have typeA := (escA.redTm ha).1
        have typeB := (escA.redTm hb).1
        have convAB := escA.eqTm equal
        have typingR := typing.rename w.1
        have typingR' := typing'.rename w.1
        have convR := laws.convNe_rename w.1 w.2 conv
        simp only [Presentation.rename] at typingR typingR' convR
        have codEq : TypeEq S.R Δ (inst0 b (Presentation.rename (liftRen ρ) cod))
            (inst0 a (Presentation.rename (liftRen ρ) cod)) :=
          laws.convTy_sound (((codAdequate w ha).escape laws).eqTy
            (P.codExt w ha hb equal)) |>.symm
        exact ⟨.appElim typingR typeA,
          Typed.convType (.appElim typingR' typeB) codEq,
          laws.convNe_app convR convAB⟩
      refine ⟨?_, ?_⟩
      · intro t neutralT typingT reflT
        have typing := Typed.convType typingT typeEq
        have refl' := laws.convNe_conv reflT typeEq
        refine ⟨t, RedTm.refl typing, .inr (.inl neutralT),
          laws.convTm_of_convNe (.inl neutralT) (.inl neutralT) refl', ?_, ?_⟩
        · intro m Δ ρ w a ha
          obtain ⟨tyA, _, conv⟩ := applied w ha ha (LogRel.reflexive S l (domAdequate w) |>.eqTm ha)
            typing typing refl'
          exact (codIH w ha).redTm (.app (neutralT.rename ρ)) tyA conv
        · intro m Δ ρ w a b ha hb equal
          obtain ⟨tyA, tyB, conv⟩ := applied w ha hb equal typing typing refl'
          exact (codIH w ha).eqTm (.app (neutralT.rename ρ)) (.app (neutralT.rename ρ))
            tyA tyB conv
      · intro t t' n₁ n₂ ty₁ ty₂ equal
        have typing₁ := Typed.convType ty₁ typeEq
        have typing₂ := Typed.convType ty₂ typeEq
        have equal' := laws.convNe_conv equal typeEq
        have refl₁ : S.E.convNe Γ t t (.pi dom cod) :=
          laws.convNe_trans equal' (laws.convNe_symm equal')
        have refl₂ : S.E.convNe Γ t' t' (.pi dom cod) :=
          laws.convNe_trans (laws.convNe_symm equal') equal'
        have reduces : ∀ {s : Tm Head n}, Neutral S.roles s → Typed S.R Γ s (.pi dom cod) →
            S.E.convNe Γ s s (.pi dom cod) → PiRedTm S P s := by
          intro s neutralS typingS reflS
          refine ⟨s, RedTm.refl typingS, .inr (.inl neutralS),
            laws.convTm_of_convNe (.inl neutralS) (.inl neutralS) reflS,
            ?_, ?_⟩
          · intro m Δ ρ w a ha
            obtain ⟨tyA, _, conv⟩ := applied w ha ha
              (LogRel.reflexive S l (domAdequate w) |>.eqTm ha) typingS typingS reflS
            exact (codIH w ha).redTm (.app (neutralS.rename ρ)) tyA conv
          · intro m Δ ρ w a b ha hb eq
            obtain ⟨tyA, tyB, conv⟩ := applied w ha hb eq typingS typingS reflS
            exact (codIH w ha).eqTm (.app (neutralS.rename ρ)) (.app (neutralS.rename ρ))
              tyA tyB conv
        refine ⟨reduces n₁ typing₁ refl₁, reduces n₂ typing₂ refl₂, t, t', RedTm.refl typing₁,
          RedTm.refl typing₂, .inr (.inl n₁), .inr (.inl n₂),
          laws.convTm_of_convNe (.inl n₁) (.inl n₂) equal', ?_⟩
        intro m Δ ρ w a ha
        obtain ⟨tyA, tyB, conv⟩ := applied w ha ha
          (LogRel.reflexive S l (domAdequate w) |>.eqTm ha) typing₁ typing₂ equal'
        exact (codIH w ha).eqTm (.app (n₁.rename ρ)) (.app (n₂.rename ρ)) tyA tyB conv
  | @sigma n Γ A dom cod red domType codType refl P domAdequate codAdequate domIH codIH =>
      have typeEq := red.typeEq
      /- The projections of a renamed neutral pair. -/
      have firsts : ∀ {t t' : Tm Head n} {m : Nat} {Δ : Ctx Head m} {ρ : Ren n m}
          (w : World S Γ Δ ρ), Neutral S.roles t → Neutral S.roles t' →
          Typed S.R Γ t (.sigma dom cod) → Typed S.R Γ t' (.sigma dom cod) →
          S.E.convNe Γ t t' (.sigma dom cod) →
          (P.domPack w).eqTm (.fst (Presentation.rename ρ t)) (.fst (Presentation.rename ρ t')) := by
        intro t t' m Δ ρ w n₁ n₂ ty₁ ty₂ conv
        have tyR₁ := ty₁.rename w.1
        have tyR₂ := ty₂.rename w.1
        have convR := laws.convNe_rename w.1 w.2 conv
        simp only [Presentation.rename] at tyR₁ tyR₂ convR
        exact (domIH w).eqTm (.fst (n₁.rename ρ)) (.fst (n₂.rename ρ)) (.fstElim tyR₁)
          (.fstElim tyR₂) (laws.convNe_fst convR)
      have firstRed : ∀ {t : Tm Head n} {m : Nat} {Δ : Ctx Head m} {ρ : Ren n m}
          (w : World S Γ Δ ρ), Neutral S.roles t → Typed S.R Γ t (.sigma dom cod) →
          S.E.convNe Γ t t (.sigma dom cod) →
          (P.domPack w).redTm (.fst (Presentation.rename ρ t)) := by
        intro t m Δ ρ w neutralT typingT reflT
        have tyR := typingT.rename w.1
        have convR := laws.convNe_rename w.1 w.2 reflT
        simp only [Presentation.rename] at tyR convR
        exact (domIH w).redTm (.fst (neutralT.rename ρ)) (.fstElim tyR) (laws.convNe_fst convR)
      have seconds : ∀ {t t' : Tm Head n} {m : Nat} {Δ : Ctx Head m} {ρ : Ren n m}
          (w : World S Γ Δ ρ) (first : (P.domPack w).redTm (.fst (Presentation.rename ρ t))),
          Neutral S.roles t → Neutral S.roles t' →
          Typed S.R Γ t (.sigma dom cod) → Typed S.R Γ t' (.sigma dom cod) →
          S.E.convNe Γ t t' (.sigma dom cod) →
          (P.codPack w first).eqTm (.snd (Presentation.rename ρ t))
            (.snd (Presentation.rename ρ t')) := by
        intro t t' m Δ ρ w first n₁ n₂ ty₁ ty₂ conv
        have tyR₁ := ty₁.rename w.1
        have tyR₂ := ty₂.rename w.1
        have convR := laws.convNe_rename w.1 w.2 conv
        simp only [Presentation.rename] at tyR₁ tyR₂ convR
        have eqFirst := firsts w n₁ n₂ ty₁ ty₂ conv
        have codEq : TypeEq S.R Δ
            (inst0 (.fst (Presentation.rename ρ t')) (Presentation.rename (liftRen ρ) cod))
            (inst0 (.fst (Presentation.rename ρ t)) (Presentation.rename (liftRen ρ) cod)) := by
          have second' : (P.domPack w).redTm (.fst (Presentation.rename ρ t')) :=
            firstRed w n₂ ty₂ (laws.convNe_trans (laws.convNe_symm conv) conv)
          exact (laws.convTy_sound (((codAdequate w first).escape laws).eqTy
            (P.codExt w first second' eqFirst))).symm
        exact (codIH w first).eqTm (.snd (n₁.rename ρ)) (.snd (n₂.rename ρ)) (.sndElim tyR₁)
          (Typed.convType (.sndElim tyR₂) codEq) (laws.convNe_snd convR)
      have reduces : ∀ {s : Tm Head n}, Neutral S.roles s → Typed S.R Γ s (.sigma dom cod) →
          S.E.convNe Γ s s (.sigma dom cod) → SigmaRedTm S P s := by
        intro s neutralS typingS reflS
        refine ⟨s, RedTm.refl typingS, .inr neutralS,
          laws.convTm_of_convNe (.inl neutralS) (.inl neutralS) reflS,
          fun w => firstRed w neutralS typingS reflS, ?_⟩
        intro m Δ ρ w
        have tyR := typingS.rename w.1
        have convR := laws.convNe_rename w.1 w.2 reflS
        simp only [Presentation.rename] at tyR convR
        exact (codIH w (firstRed w neutralS typingS reflS)).redTm (.snd (neutralS.rename ρ))
          (.sndElim tyR) (laws.convNe_snd convR)
      refine ⟨?_, ?_⟩
      · intro t neutralT typingT reflT
        exact reduces neutralT (Typed.convType typingT typeEq) (laws.convNe_conv reflT typeEq)
      · intro t t' n₁ n₂ ty₁ ty₂ equal
        have typing₁ := Typed.convType ty₁ typeEq
        have typing₂ := Typed.convType ty₂ typeEq
        have equal' := laws.convNe_conv equal typeEq
        have refl₁ : S.E.convNe Γ t t (.sigma dom cod) :=
          laws.convNe_trans equal' (laws.convNe_symm equal')
        have refl₂ : S.E.convNe Γ t' t' (.sigma dom cod) :=
          laws.convNe_trans (laws.convNe_symm equal') equal'
        exact ⟨reduces n₁ typing₁ refl₁, reduces n₂ typing₂ refl₂, t, t', RedTm.refl typing₁,
          RedTm.refl typing₂, .inr n₁, .inr n₂, laws.convTm_of_convNe (.inl n₁) (.inl n₂) equal',
          fun w => firsts w n₁ n₂ typing₁ typing₂ equal',
          fun w first => seconds w first n₁ n₂ typing₁ typing₂ equal'⟩
  | @ident n Γ A ty lhs rhs red refl tyPack tyAdequate lhsRed rhsRed lhsRefl rhsRefl
      tySymm tyTrans tyIH =>
      have typeEq := red.typeEq
      refine ⟨?_, ?_⟩
      · intro t neutralT typingT reflT
        have typing := Typed.convType typingT typeEq
        have refl' := laws.convNe_conv reflT typeEq
        exact ⟨t, RedTm.refl typing, laws.convTm_of_convNe (.inl neutralT) (.inl neutralT) refl',
          .inr ⟨neutralT, refl'⟩⟩
      · intro t t' n₁ n₂ ty₁ ty₂ equal
        have equal' := laws.convNe_conv equal typeEq
        exact ⟨t, t', RedTm.refl (Typed.convType ty₁ typeEq), RedTm.refl (Typed.convType ty₂ typeEq),
          laws.convTm_of_convNe (.inl n₁) (.inl n₂) equal', .inr ⟨n₁, n₂, equal'⟩⟩
  | @inductiveType n Γ A T ctors u red role typing isUniverse fieldPack fieldAdequate fieldIH =>
      have typeEq := red.typeEq
      refine ⟨?_, ?_⟩
      · intro t neutralT typingT reflT
        have refl' := laws.convNe_conv reflT typeEq
        exact .mk (RedTm.refl (Typed.convType typingT typeEq))
          (laws.convTm_of_convNe (.inl neutralT) (.inl neutralT) refl')
          (.neutral neutralT refl')
      · intro t t' n₁ n₂ ty₁ ty₂ equal
        have equal' := laws.convNe_conv equal typeEq
        exact .mk (RedTm.refl (Typed.convType ty₁ typeEq)) (RedTm.refl (Typed.convType ty₂ typeEq))
          (laws.convTm_of_convNe (.inl n₁) (.inl n₂) equal') (.neutral n₁ n₂ equal')

end Normalization
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
