import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.Irrelevance

/-!
# Symmetry and transitivity

Reducible equality of types and of terms is symmetric and transitive. Type
equality follows from irrelevance and reflexivity. Term equality inducts on
the reducibility derivation; weak-head normal forms are unique, so the normal
forms of a middle term agree, and in the pair case the codomain packs at
reducibly equal first projections agree by irrelevance.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Normalization

open UniverseLevel (LevelOrder)

variable {Head L : Type} [LevelOrder L] {S : Setting Head L}

/-! ## Normal forms -/

theorem IsFun.whnf {n : Nat} {t : Tm Head n} (function : IsFun S.roles t) :
    Whnf S.R S.roles t := by
  rcases function with ⟨body, rfl⟩ | neutral | ⟨c, args, arity, role, short, rfl⟩
  · exact lam_whnf S.shape body
  · exact neutral.whnf S.shape
  · rcases role with role | ⟨scrutinee, role⟩
    · exact constSpine_whnf S.shape (by intro a s h; rw [role] at h; cases h) args
    · exact partialSpine_whnf S.shape role short

theorem IsTypeForm.whnf {n : Nat} {t : Tm Head n} (form : IsTypeForm S.roles t) :
    Whnf S.R S.roles t := by
  rcases form with ⟨h, rfl⟩ | ⟨A, B, rfl⟩ | ⟨A, B, rfl⟩ | ⟨A, a, b, rfl⟩ | neutral |
    ⟨T, constructors, role, rfl⟩
  · exact head_whnf S.shape h
  · exact pi_whnf S.shape A B
  · exact sigma_whnf S.shape A B
  · exact id_whnf S.shape A a b
  · exact neutral.whnf S.shape
  · exact constSpine_whnf S.shape (args := []) (by intro a s h; rw [role] at h; cases h)

theorem IsPair.whnf {n : Nat} {t : Tm Head n} (pair : IsPair S.roles t) :
    Whnf S.R S.roles t := by
  rcases pair with ⟨a, b, rfl⟩ | neutral
  · exact pair_whnf S.shape a b
  · exact neutral.whnf S.shape

theorem RedTm.unique {n : Nat} {Γ : Ctx Head n} {t nf nf' A A' : Tm Head n}
    (first : RedTm S.R S.roles Γ t nf A) (second : RedTm S.R S.roles Γ t nf' A')
    (normal : Whnf S.R S.roles nf) (normal' : Whnf S.R S.roles nf') : nf = nf' :=
  WhRed.whnf_unique S.shape first.red second.red normal normal'

theorem IdProp.whnf {n : Nat} {Γ : Ctx Head n} {ty lhs rhs nf : Tm Head n}
    {tyPack : Pack Head n} (prop : IdProp S Γ ty lhs rhs tyPack nf) :
    Whnf S.R S.roles nf := by
  rcases prop with ⟨x, rfl, _⟩ | ⟨neutral, _⟩
  · exact refl_whnf S.shape x
  · exact neutral.whnf S.shape

theorem IdPropEq.whnf {n : Nat} {Γ : Ctx Head n} {ty lhs rhs nf nf' : Tm Head n}
    {tyPack : Pack Head n} (prop : IdPropEq S Γ ty lhs rhs tyPack nf nf') :
    Whnf S.R S.roles nf ∧ Whnf S.R S.roles nf' := by
  rcases prop with ⟨x, x', rfl, rfl, _⟩ | ⟨neutral, neutral', _⟩
  · exact ⟨refl_whnf S.shape x, refl_whnf S.shape x'⟩
  · exact ⟨neutral.whnf S.shape, neutral'.whnf S.shape⟩

/-! ## Type equality -/

theorem LR.eqTy_symm (laws : S.E.Laws S.R S.roles) {l l' : L} {n : Nat}
    {Γ : Ctx Head n} {A B : Tm Head n} {P P' : Pack Head n}
    (reducible : LR S l (levelsBelow S l) Γ A P)
    (reducible' : LR S l' (levelsBelow S l') Γ B P') (equal : P.eqTy B) : P'.eqTy A :=
  (reducible.irrelevant laws reducible' equal).eqTy.mp
    (LogRel.reflexive S l reducible).eqTy

theorem LR.eqTy_trans (laws : S.E.Laws S.R S.roles) {l l' : L} {n : Nat}
    {Γ : Ctx Head n} {A B C : Tm Head n} {P P' : Pack Head n}
    (reducible : LR S l (levelsBelow S l) Γ A P)
    (reducible' : LR S l' (levelsBelow S l') Γ B P') (first : P.eqTy B)
    (second : P'.eqTy C) : P.eqTy C :=
  (reducible.irrelevant laws reducible' first).eqTy.mpr second

/-- Symmetry and transitivity of type equality at a level, through the table of
lower levels. -/
theorem levelsBelow_eqTy_symm (laws : S.E.Laws S.R S.roles) {l k : L} (below : k < l)
    {n : Nat} {Γ : Ctx Head n} {A B : Tm Head n} {P P' : Pack Head n}
    (reducible : levelsBelow S l k Γ A P) (reducible' : levelsBelow S l k Γ B P')
    (equal : P.eqTy B) : P'.eqTy A :=
  LR.eqTy_symm laws ((levelsBelow_iff S below Γ A P).mp reducible)
    ((levelsBelow_iff S below Γ B P').mp reducible') equal

theorem levelsBelow_eqTy_trans (laws : S.E.Laws S.R S.roles) {l k : L} (below : k < l)
    {n : Nat} {Γ : Ctx Head n} {A B C : Tm Head n} {P P' : Pack Head n}
    (reducible : levelsBelow S l k Γ A P) (reducible' : levelsBelow S l k Γ B P')
    (first : P.eqTy B) (second : P'.eqTy C) : P.eqTy C :=
  LR.eqTy_trans laws ((levelsBelow_iff S below Γ A P).mp reducible)
    ((levelsBelow_iff S below Γ B P').mp reducible') first second

/-! ## Term equality -/

/-- Reducible term equality is symmetric and transitive. -/
theorem LR.eqTm_per (laws : S.E.Laws S.R S.roles) {l : L} {n : Nat}
    {Γ : Ctx Head n} {A : Tm Head n} {P : Pack Head n}
    (reducible : LR S l (levelsBelow S l) Γ A P) :
    (∀ {t u}, P.eqTm t u → P.eqTm u t) ∧
      (∀ {t u v}, P.eqTm t u → P.eqTm u v → P.eqTm t v) := by
  induction reducible with
  | @sort n Γ A u isUniverse below₁ formed red =>
      constructor
      · rintro t t' ⟨nf, nf', redT, redT', whnf, whnf', equal, ⟨Q', reducible'⟩, Q,
          reducibleQ, eqTy⟩
        exact ⟨nf', nf, redT', redT, whnf', whnf, laws.convTm_symm equal, ⟨Q, reducibleQ⟩,
          Q', reducible', levelsBelow_eqTy_symm laws below₁ reducibleQ reducible' eqTy⟩
      · rintro t t' t'' ⟨nf, nf', redT, redT', whnf, whnf', equal, _, Q, reducibleQ, eqTy⟩
          ⟨mf', mf'', redT₂', redT₂'', whnf₂', whnf₂'', equal₂, ⟨Q'', reducible''⟩, Q',
            reducibleQ', eqTy'⟩
        have same := RedTm.unique redT' redT₂' whnf'.whnf whnf₂'.whnf
        subst same
        exact ⟨nf, mf'', redT, redT₂'', whnf, whnf₂'', laws.convTm_trans equal equal₂,
          ⟨Q'', reducible''⟩, Q, reducibleQ,
          levelsBelow_eqTy_trans laws below₁ reducibleQ reducibleQ' eqTy eqTy'⟩
  | @neutral n Γ A ty u red neutral isUniverse typing refl =>
      constructor
      · rintro t t' ⟨nf, nf', redT, redT', n₁, n₂, equal⟩
        exact ⟨nf', nf, redT', redT, n₂, n₁, laws.convNe_symm equal⟩
      · rintro t t' t'' ⟨nf, nf', redT, redT', n₁, n₂, equal⟩
          ⟨mf', mf'', redT₂', redT₂'', m₁, m₂, equal₂⟩
        have same := RedTm.unique redT' redT₂' (n₂.whnf S.shape) (m₁.whnf S.shape)
        subst same
        exact ⟨nf, mf'', redT, redT₂'', n₁, m₂, laws.convNe_trans equal equal₂⟩
  | @ground n Γ A h u notUniverse red typing isUniverse =>
      constructor
      · rintro t t' ⟨nf, nf', redT, redT', n₁, n₂, equal⟩
        exact ⟨nf', nf, redT', redT, n₂, n₁, laws.convNe_symm equal⟩
      · rintro t t' t'' ⟨nf, nf', redT, redT', n₁, n₂, equal⟩
          ⟨mf', mf'', redT₂', redT₂'', m₁, m₂, equal₂⟩
        have same := RedTm.unique redT' redT₂' (n₂.whnf S.shape) (m₁.whnf S.shape)
        subst same
        exact ⟨nf, mf'', redT, redT₂'', n₁, m₂, laws.convNe_trans equal equal₂⟩
  | @pi n Γ A dom cod red domType codType refl P domAdequate codAdequate domIH codIH =>
      constructor
      · rintro t t' ⟨redT, redT', nf, nf', r, r', isFun, isFun', equal, apps⟩
        exact ⟨redT', redT, nf', nf, r', r, isFun', isFun, laws.convTm_symm equal,
          fun w a ha => (codIH w ha).1 (apps w ha)⟩
      · rintro t t' t'' ⟨redT, _, nf, nf', r, r', isFun, isFun', equal, apps⟩
          ⟨_, redT'', mf', mf'', q', q'', isFun₂', isFun₂'', equal₂, apps₂⟩
        have same := RedTm.unique r' q' isFun'.whnf isFun₂'.whnf
        subst same
        exact ⟨redT, redT'', nf, mf'', r, q'', isFun, isFun₂'',
          laws.convTm_trans equal equal₂,
          fun w a ha => (codIH w ha).2 (apps w ha) (apps₂ w ha)⟩
  | @sigma n Γ A dom cod red domType codType refl P domAdequate codAdequate domIH codIH =>
      /- The codomain packs at two reducibly equal first projections agree. -/
      have transfer : ∀ {m : Nat} {Δ : Ctx Head m} {ρ : Ren n m} (w : World S Γ Δ ρ)
          {a b : Tm Head m} (ha : (P.domPack w).redTm a) (hb : (P.domPack w).redTm b),
          (P.domPack w).eqTm a b → PackEquiv (P.codPack w ha) (P.codPack w hb) :=
        by
          intro _ _ _ w _ _ ha hb equal
          exact (codAdequate w ha).irrelevant laws (codAdequate w hb) (P.codExt w ha hb equal)
      constructor
      · rintro t t' ⟨redT, redT', nf, nf', r, r', isPair, isPair', equal, firsts, seconds⟩
        obtain ⟨nf₀, r₀, isPair₀, _, first₀, _⟩ := redT
        have same := RedTm.unique r r₀ isPair.whnf isPair₀.whnf
        subst same
        refine ⟨redT', ⟨nf, r₀, isPair₀, ‹_›, first₀, ‹_›⟩, nf', nf, r', r₀, isPair', isPair₀,
          laws.convTm_symm equal, fun w => (domIH w).1 (firsts w), ?_⟩
        intro m Δ ρ w first'
        exact (transfer w (first₀ w) first' (firsts w)).eqTm.mp
          ((codIH w (first₀ w)).1 (seconds w (first₀ w)))
      · rintro t t' t'' ⟨redT, redT', nf, nf', r, r', isPair, isPair', equal, firsts, seconds⟩
          ⟨_, redT'', mf', mf'', q', q'', isPair₂', isPair₂'', equal₂, firsts₂, seconds₂⟩
        have same := RedTm.unique r' q' isPair'.whnf isPair₂'.whnf
        subst same
        obtain ⟨nf₁, r₁, isPair₁, _, first₁, _⟩ := redT'
        have same₁ := RedTm.unique r' r₁ isPair'.whnf isPair₁.whnf
        subst same₁
        refine ⟨redT, redT'', nf, mf'', r, q'', isPair, isPair₂'',
          laws.convTm_trans equal equal₂, fun w => (domIH w).2 (firsts w) (firsts₂ w), ?_⟩
        intro m Δ ρ w first
        have middle := (transfer w (first₁ w) first (by
          exact (domIH w).1 (firsts w))).eqTm.mp (seconds₂ w (first₁ w))
        exact (codIH w first).2 (seconds w first) middle
  | @ident n Γ A ty lhs rhs red refl tyPack tyAdequate lhsRed rhsRed lhsRefl rhsRefl
      tySymm tyTrans tyIH =>
      constructor
      · rintro t t' ⟨nf, nf', redT, redT', equal, prop⟩
        refine ⟨nf', nf, redT', redT, laws.convTm_symm equal, ?_⟩
        rcases prop with ⟨x, x', rfl, rfl, typing, typing', l, l', r, r'⟩ |
          ⟨n₁, n₂, equalN⟩
        · exact .inl ⟨x', x, rfl, rfl, typing', typing, l', l, r', r⟩
        · exact .inr ⟨n₂, n₁, laws.convNe_symm equalN⟩
      · rintro t t' t'' ⟨nf, nf', redT, redT', equal, prop⟩
          ⟨mf', mf'', redT₂', redT₂'', equal₂, prop₂⟩
        have same := RedTm.unique redT' redT₂' prop.whnf.2 prop₂.whnf.1
        subst same
        refine ⟨nf, mf'', redT, redT₂'', laws.convTm_trans equal equal₂, ?_⟩
        rcases prop with ⟨x, x', rfl, rfl, typing, typing', l, l', r, r'⟩ |
          ⟨n₁, n₂, equalN⟩
        · rcases prop₂ with ⟨y, y', hy, rfl, typingY, typingY', ly, ly', ry, ry'⟩ |
            ⟨m₁, m₂, _⟩
          · exact .inl ⟨x, y', rfl, rfl, typing, typingY', l, ly', r, ry'⟩
          · exact absurd rfl (m₁.ne_refl (a := x'))
        · rcases prop₂ with ⟨y, y', hy, rfl, _⟩ | ⟨m₁, m₂, equalN₂⟩
          · exact absurd hy (n₂.ne_refl)
          · exact .inr ⟨n₁, m₂, laws.convNe_trans equalN equalN₂⟩
  | @inductiveType n Γ A T ctors u red role typing isUniverse fieldPack fieldAdequate fieldIH =>
      constructor
      · intro t t' equal
        exact IndEqTm.symm laws (fun ⟨_, _, mem, closed⟩ _ _ h => (fieldIH mem closed).1 h) equal
      · intro t t' t'' first second
        exact IndEqTm.trans laws role
          (fun ⟨_, _, mem, closed⟩ _ _ _ h h' => (fieldIH mem closed).2 h h') first second

theorem LR.eqTm_symm (laws : S.E.Laws S.R S.roles) {l : L} {n : Nat}
    {Γ : Ctx Head n} {A : Tm Head n} {P : Pack Head n}
    (reducible : LR S l (levelsBelow S l) Γ A P) {t u : Tm Head n} (equal : P.eqTm t u) :
    P.eqTm u t :=
  (reducible.eqTm_per laws).1 equal

theorem LR.eqTm_trans (laws : S.E.Laws S.R S.roles) {l : L} {n : Nat}
    {Γ : Ctx Head n} {A : Tm Head n} {P : Pack Head n}
    (reducible : LR S l (levelsBelow S l) Γ A P) {t u v : Tm Head n}
    (first : P.eqTm t u) (second : P.eqTm u v) : P.eqTm t v :=
  (reducible.eqTm_per laws).2 first second

end Normalization
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
