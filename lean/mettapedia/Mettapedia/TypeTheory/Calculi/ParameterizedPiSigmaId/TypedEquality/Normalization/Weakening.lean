import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.Transitivity

/-!
# Weakening

A reducible type stays reducible along a renaming into a formed context, and
its reducible equalities and terms transport. Dependent function and pair
types are already reducible in every world, so their weakening reuses their
packs through the composed world. The universe case weakens at the lower
level; the identity case weakens its carrier.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Normalization

open UniverseLevel (LevelOrder)

variable {Head L : Type} [LevelOrder L] {S : Setting Head L}

/-! ## Worlds and renamings -/

theorem World.comp {n m k : Nat} {Γ : Ctx Head n} {Δ : Ctx Head m} {Θ : Ctx Head k}
    {ρ : Ren n m} {ρ' : Ren m k} (first : World S Γ Δ ρ) (second : World S Δ Θ ρ') :
    World S Γ Θ (fun i => ρ' (ρ i)) :=
  ⟨CtxRen.comp first.1 second.1, second.2⟩

theorem liftRen_comp {n m k : Nat} (ρ : Ren n m) (ρ' : Ren m k) :
    (fun i => liftRen ρ' (liftRen ρ i)) = liftRen (fun i => ρ' (ρ i)) := by
  funext i
  refine Fin.cases ?_ ?_ i
  · rfl
  · intro j
    rfl

theorem rename_rename {n m k : Nat} (ρ : Ren n m) (ρ' : Ren m k) (t : Tm Head n) :
    Presentation.rename ρ' (Presentation.rename ρ t) =
      Presentation.rename (fun i => ρ' (ρ i)) t :=
  rename_comp ρ' ρ t

theorem rename_rename_lift {n m k : Nat} (ρ : Ren n m) (ρ' : Ren m k)
    (t : Tm Head (n + 1)) :
    Presentation.rename (liftRen ρ') (Presentation.rename (liftRen ρ) t) =
      Presentation.rename (liftRen (fun i => ρ' (ρ i))) t := by
  rw [rename_comp, liftRen_comp]

/-! ## Transport of packs -/

/-- `P'` is a pack for the renamed type that contains everything `P` has,
renamed. -/
structure Weakened {n m : Nat} (P : Pack Head n) (ρ : Ren n m) (P' : Pack Head m) : Prop where
  eqTy : ∀ {B}, P.eqTy B → P'.eqTy (Presentation.rename ρ B)
  redTm : ∀ {t}, P.redTm t → P'.redTm (Presentation.rename ρ t)
  eqTm : ∀ {t u}, P.eqTm t u → P'.eqTm (Presentation.rename ρ t) (Presentation.rename ρ u)

/-- Weakening of every reducibility derivation at levels below `l`. -/
def WeakensBelow (S : Setting Head L) (l : L) : Prop :=
  ∀ {k : L}, k < l → ∀ {n : Nat} {Γ : Ctx Head n} {A : Tm Head n} {P : Pack Head n},
    LogRel S k Γ A P → ∀ {m : Nat} {Δ : Ctx Head m} {ρ : Ren n m}, World S Γ Δ ρ →
      ∃ P', LogRel S k Δ (Presentation.rename ρ A) P' ∧ Weakened P ρ P'

/-- The weakened parts of a dependent function or pair type. -/
def PolyPack.weaken {n m : Nat} {Γ : Ctx Head n} {Δ : Ctx Head m} {ρ : Ren n m}
    {dom : Tm Head n} {cod : Tm Head (n + 1)} (P : PolyPack S Γ dom cod)
    (w : World S Γ Δ ρ) :
    PolyPack S Δ (Presentation.rename ρ dom) (Presentation.rename (liftRen ρ) cod) where
  domPack := fun w' => P.domPack (w.comp w')
  codPack := fun {_} {_} {_} w' {_} ha => P.codPack (w.comp w') ha
  codExt := by
    intro k Θ ρ' w' a b ha hb equal
    rw [rename_rename_lift]
    exact P.codExt (w.comp w') ha hb equal

/-- Codomain packs at equal arguments are equal. -/
theorem PolyPack.codPack_transport {n : Nat} {Γ : Ctx Head n} {dom : Tm Head n}
    {cod : Tm Head (n + 1)} (P : PolyPack S Γ dom cod) {m : Nat} {Δ : Ctx Head m}
    {ρ : Ren n m} (w : World S Γ Δ ρ) {X Y : Tm Head m} (e : X = Y)
    (hX : (P.domPack w).redTm X) (hY : (P.domPack w).redTm Y) :
    P.codPack w hX = P.codPack w hY := by
  subst e
  rfl

theorem PolyPack.snd_redTm_transport {n : Nat} {Γ : Ctx Head n} {dom : Tm Head n}
    {cod : Tm Head (n + 1)} (P : PolyPack S Γ dom cod) {m : Nat} {Δ : Ctx Head m}
    {ρ : Ren n m} (w : World S Γ Δ ρ) {X Y : Tm Head m} (e : X = Y)
    (hX : (P.domPack w).redTm (.fst X)) (hY : (P.domPack w).redTm (.fst Y)) :
    (P.codPack w hX).redTm (.snd X) ↔ (P.codPack w hY).redTm (.snd Y) := by
  subst e
  rfl

theorem PolyPack.snd_eqTm_transport {n : Nat} {Γ : Ctx Head n} {dom : Tm Head n}
    {cod : Tm Head (n + 1)} (P : PolyPack S Γ dom cod) {m : Nat} {Δ : Ctx Head m}
    {ρ : Ren n m} (w : World S Γ Δ ρ) {X X' Y Y' : Tm Head m} (e : X = Y) (e' : X' = Y')
    (hX : (P.domPack w).redTm (.fst X)) (hY : (P.domPack w).redTm (.fst Y)) :
    (P.codPack w hX).eqTm (.snd X) (.snd X') ↔ (P.codPack w hY).eqTm (.snd Y) (.snd Y') := by
  subst e e'
  rfl

theorem RedTy.rename' {n m : Nat} {Γ : Ctx Head n} {Δ : Ctx Head m} {ρ : Ren n m}
    {A B : Tm Head n} (red : RedTy S.R S.roles Γ A B) (w : World S Γ Δ ρ) :
    RedTy S.R S.roles Δ (Presentation.rename ρ A) (Presentation.rename ρ B) :=
  red.rename w.1

theorem LR.weaken (laws : S.E.Laws S.R S.roles) {l : L} (lower : WeakensBelow S l)
    {n : Nat} {Γ : Ctx Head n} {A : Tm Head n} {P : Pack Head n}
    (reducible : LR S l (levelsBelow S l) Γ A P) :
    ∀ {m : Nat} {Δ : Ctx Head m} {ρ : Ren n m}, World S Γ Δ ρ →
      ∃ P', LR S l (levelsBelow S l) Δ (Presentation.rename ρ A) P' ∧ Weakened P ρ P' := by
  induction reducible with
  | @sort n Γ A u isUniverse below₁ formed red =>
      intro m Δ ρ w
      refine ⟨universePack S (levelsBelow S l) Δ u,
        .sort isUniverse below₁ w.2 (by simpa [Presentation.rename] using red.rename' w), ?_⟩
      have lowerWeaken : ∀ {t : Tm Head n} {Q : Pack Head n},
          levelsBelow S l (S.levels.level u) Γ t Q →
          ∃ Q', levelsBelow S l (S.levels.level u) Δ (Presentation.rename ρ t) Q' ∧
            Weakened Q ρ Q' := by
        intro t Q reducibleQ
        obtain ⟨Q', r', weakened⟩ :=
          lower below₁ ((levelsBelow_iff S below₁ Γ t Q).mp reducibleQ) w
        exact ⟨Q', (levelsBelow_iff S below₁ Δ _ Q').mpr r', weakened⟩
      refine ⟨?_, ?_, ?_⟩
      · rintro B ⟨u', redB, same⟩
        exact ⟨u', by simpa [Presentation.rename] using redB.rename' w, same⟩
      · rintro t ⟨nf, redT, form, refl, Q, reducibleQ⟩
        obtain ⟨Q', r', _⟩ := lowerWeaken reducibleQ
        exact ⟨Presentation.rename ρ nf, by simpa [Presentation.rename] using redT.rename w.1,
          form.rename ρ, by simpa [Presentation.rename] using laws.convTm_rename w.1 w.2 refl,
          Q', r'⟩
      · rintro t t' ⟨nf, nf', redT, redT', form, form', equal, ⟨Q', reducible'⟩, Q,
          reducibleQ, eqTy⟩
        obtain ⟨Q₁', r₁', _⟩ := lowerWeaken reducible'
        obtain ⟨Q₁, r₁, weakened⟩ := lowerWeaken reducibleQ
        exact ⟨Presentation.rename ρ nf, Presentation.rename ρ nf',
          by simpa [Presentation.rename] using redT.rename w.1,
          by simpa [Presentation.rename] using redT'.rename w.1, form.rename ρ, form'.rename ρ,
          by simpa [Presentation.rename] using laws.convTm_rename w.1 w.2 equal,
          ⟨Q₁', r₁'⟩, Q₁, r₁, weakened.eqTy eqTy⟩
  | @neutral n Γ A ty u red neutral isUniverse typing refl =>
      intro m Δ ρ w
      refine ⟨neutralPack S Δ (Presentation.rename ρ ty),
        .neutral (red.rename' w) (neutral.rename ρ) isUniverse
          (by simpa [Presentation.rename] using typing.rename w.1)
          (by simpa [Presentation.rename] using laws.convNe_rename w.1 w.2 refl), ?_⟩
      refine ⟨?_, ?_, ?_⟩
      · rintro B ⟨ty', redB, neutral', v, hv, conv⟩
        exact ⟨Presentation.rename ρ ty', redB.rename' w, neutral'.rename ρ, v, hv,
          by simpa [Presentation.rename] using laws.convNe_rename w.1 w.2 conv⟩
      · rintro t ⟨nf, redT, neutralT, reflT⟩
        exact ⟨Presentation.rename ρ nf, redT.rename w.1, neutralT.rename ρ,
          laws.convNe_rename w.1 w.2 reflT⟩
      · rintro t t' ⟨nf, nf', redT, redT', n₁, n₂, equal⟩
        exact ⟨Presentation.rename ρ nf, Presentation.rename ρ nf', redT.rename w.1,
          redT'.rename w.1, n₁.rename ρ, n₂.rename ρ, laws.convNe_rename w.1 w.2 equal⟩
  | @ground n Γ A h u notUniverse red typing isUniverse =>
      intro m Δ ρ w
      refine ⟨groundPack S Δ h,
        .ground notUniverse (by simpa [Presentation.rename] using red.rename' w)
          (by simpa [Presentation.rename] using typing.rename w.1) isUniverse, ?_⟩
      refine ⟨?_, ?_, ?_⟩
      · rintro B ⟨h', redB, same⟩
        exact ⟨h', by simpa [Presentation.rename] using redB.rename' w, same⟩
      · rintro t ⟨nf, redT, neutralT, reflT⟩
        exact ⟨Presentation.rename ρ nf, by simpa [Presentation.rename] using redT.rename w.1,
          neutralT.rename ρ, by simpa [Presentation.rename] using laws.convNe_rename w.1 w.2 reflT⟩
      · rintro t t' ⟨nf, nf', redT, redT', n₁, n₂, equal⟩
        exact ⟨Presentation.rename ρ nf, Presentation.rename ρ nf',
          by simpa [Presentation.rename] using redT.rename w.1,
          by simpa [Presentation.rename] using redT'.rename w.1, n₁.rename ρ, n₂.rename ρ,
          by simpa [Presentation.rename] using laws.convNe_rename w.1 w.2 equal⟩
  | @pi n Γ A dom cod red domType codType refl P domAdequate codAdequate _ _ =>
      intro m Δ ρ w
      refine ⟨piPack S Δ (Presentation.rename ρ dom) (Presentation.rename (liftRen ρ) cod)
        (P.weaken w), ?_, ?_⟩
      · refine .pi (by simpa [Presentation.rename] using red.rename' w)
          (domType.rename w.1) (codType.rename (w.1.snoc dom))
          (by simpa [Presentation.rename] using laws.convTy_rename w.1 w.2 refl) (P.weaken w)
          ?_ ?_
        · intro k Θ ρ' w'
          change LR S l (levelsBelow S l) Θ _ (P.domPack (w.comp w'))
          rw [rename_rename]
          exact domAdequate (w.comp w')
        · intro k Θ ρ' w' a ha
          change LR S l (levelsBelow S l) Θ _ (P.codPack (w.comp w') ha)
          rw [rename_rename_lift]
          exact codAdequate (w.comp w') ha
      · refine ⟨?_, ?_, ?_⟩
        · rintro B ⟨d, c, redB, equal, domEq, codEq⟩
          refine ⟨Presentation.rename ρ d, Presentation.rename (liftRen ρ) c,
            by simpa [Presentation.rename] using redB.rename' w,
            by simpa [Presentation.rename] using laws.convTy_rename w.1 w.2 equal, ?_, ?_⟩
          · intro k Θ ρ' w'
            change (P.domPack (w.comp w')).eqTy _
            rw [rename_rename]
            exact domEq (w.comp w')
          · intro k Θ ρ' w' a ha
            change (P.codPack (w.comp w') ha).eqTy _
            rw [rename_rename_lift]
            exact codEq (w.comp w') ha
        · rintro t ⟨nf, redT, isFun, reflT, apps, appEqs⟩
          refine ⟨Presentation.rename ρ nf,
            by simpa [Presentation.rename] using redT.rename w.1, isFun.rename ρ,
            by simpa [Presentation.rename] using laws.convTm_rename w.1 w.2 reflT, ?_, ?_⟩
          · intro k Θ ρ' w' a ha
            change (P.codPack (w.comp w') ha).redTm _
            rw [rename_rename]
            exact apps (w.comp w') ha
          · intro k Θ ρ' w' a b ha hb equal
            change (P.codPack (w.comp w') ha).eqTm _ _
            rw [rename_rename]
            exact appEqs (w.comp w') ha hb equal
        · rintro t t' ⟨⟨nf₀, redT₀, isFun₀, reflT₀, apps₀, appEqs₀⟩,
            ⟨nf₁, redT₁, isFun₁, reflT₁, apps₁, appEqs₁⟩, nf, nf', r, r', isFun, isFun',
            equal, apps⟩
          refine ⟨⟨Presentation.rename ρ nf₀,
              by simpa [Presentation.rename] using redT₀.rename w.1, isFun₀.rename ρ,
              by simpa [Presentation.rename] using laws.convTm_rename w.1 w.2 reflT₀,
              ?_, ?_⟩,
            ⟨Presentation.rename ρ nf₁,
              by simpa [Presentation.rename] using redT₁.rename w.1, isFun₁.rename ρ,
              by simpa [Presentation.rename] using laws.convTm_rename w.1 w.2 reflT₁,
              ?_, ?_⟩,
            Presentation.rename ρ nf, Presentation.rename ρ nf',
            by simpa [Presentation.rename] using r.rename w.1,
            by simpa [Presentation.rename] using r'.rename w.1, isFun.rename ρ, isFun'.rename ρ,
            by simpa [Presentation.rename] using laws.convTm_rename w.1 w.2 equal, ?_⟩
          · intro k Θ ρ' w' a ha
            change (P.codPack (w.comp w') ha).redTm _
            rw [rename_rename]
            exact apps₀ (w.comp w') ha
          · intro k Θ ρ' w' a b ha hb e
            change (P.codPack (w.comp w') ha).eqTm _ _
            rw [rename_rename]
            exact appEqs₀ (w.comp w') ha hb e
          · intro k Θ ρ' w' a ha
            change (P.codPack (w.comp w') ha).redTm _
            rw [rename_rename]
            exact apps₁ (w.comp w') ha
          · intro k Θ ρ' w' a b ha hb e
            change (P.codPack (w.comp w') ha).eqTm _ _
            rw [rename_rename]
            exact appEqs₁ (w.comp w') ha hb e
          · intro k Θ ρ' w' a ha
            change (P.codPack (w.comp w') ha).eqTm _ _
            rw [rename_rename, rename_rename]
            exact apps (w.comp w') ha
  | @sigma n Γ A dom cod red domType codType refl P domAdequate codAdequate _ _ =>
      intro m Δ ρ w
      have weakRed : ∀ {t : Tm Head n}, SigmaRedTm S P t →
          SigmaRedTm S (P.weaken w) (Presentation.rename ρ t) := by
        rintro t ⟨nf, redT, isPair, reflT, first, second⟩
        refine ⟨Presentation.rename ρ nf,
          by simpa [Presentation.rename] using redT.rename w.1, isPair.rename ρ,
          by simpa [Presentation.rename] using laws.convTm_rename w.1 w.2 reflT, ?_, ?_⟩
        · intro k Θ ρ' w'
          change (P.domPack (w.comp w')).redTm _
          rw [rename_rename]
          exact first (w.comp w')
        · intro k Θ ρ' w'
          exact (P.snd_redTm_transport (w.comp w') (rename_rename ρ ρ' nf).symm
            (first (w.comp w')) _).mp (second (w.comp w'))
      refine ⟨sigmaPack S Δ (Presentation.rename ρ dom) (Presentation.rename (liftRen ρ) cod)
        (P.weaken w), ?_, ?_⟩
      · refine .sigma (by simpa [Presentation.rename] using red.rename' w)
          (domType.rename w.1) (codType.rename (w.1.snoc dom))
          (by simpa [Presentation.rename] using laws.convTy_rename w.1 w.2 refl) (P.weaken w)
          ?_ ?_
        · intro k Θ ρ' w'
          change LR S l (levelsBelow S l) Θ _ (P.domPack (w.comp w'))
          rw [rename_rename]
          exact domAdequate (w.comp w')
        · intro k Θ ρ' w' a ha
          change LR S l (levelsBelow S l) Θ _ (P.codPack (w.comp w') ha)
          rw [rename_rename_lift]
          exact codAdequate (w.comp w') ha
      · refine ⟨?_, weakRed, ?_⟩
        · rintro B ⟨d, c, redB, equal, domEq, codEq⟩
          refine ⟨Presentation.rename ρ d, Presentation.rename (liftRen ρ) c,
            by simpa [Presentation.rename] using redB.rename' w,
            by simpa [Presentation.rename] using laws.convTy_rename w.1 w.2 equal, ?_, ?_⟩
          · intro k Θ ρ' w'
            change (P.domPack (w.comp w')).eqTy _
            rw [rename_rename]
            exact domEq (w.comp w')
          · intro k Θ ρ' w' a ha
            change (P.codPack (w.comp w') ha).eqTy _
            rw [rename_rename_lift]
            exact codEq (w.comp w') ha
        · rintro t t' ⟨redT, redT', nf, nf', r, r', isPair, isPair', equal, firsts, seconds⟩
          refine ⟨weakRed redT, weakRed redT', Presentation.rename ρ nf,
            Presentation.rename ρ nf', by simpa [Presentation.rename] using r.rename w.1,
            by simpa [Presentation.rename] using r'.rename w.1, isPair.rename ρ,
            isPair'.rename ρ,
            by simpa [Presentation.rename] using laws.convTm_rename w.1 w.2 equal, ?_, ?_⟩
          · intro k Θ ρ' w'
            change (P.domPack (w.comp w')).eqTm _ _
            rw [rename_rename, rename_rename]
            exact firsts (w.comp w')
          · intro k Θ ρ' w' first
            have first' : (P.domPack (w.comp w')).redTm
                (.fst (Presentation.rename (fun i => ρ' (ρ i)) nf)) :=
              (congrArg (fun X => (P.domPack (w.comp w')).redTm (.fst X))
                (rename_rename ρ ρ' nf)).mp first
            exact (P.snd_eqTm_transport (w.comp w') (rename_rename ρ ρ' nf).symm
              (rename_rename ρ ρ' nf').symm first' first).mp (seconds (w.comp w') first')
  | @ident n Γ A ty lhs rhs red refl tyPack tyAdequate lhsRed rhsRed lhsRefl rhsRefl
      tySymm tyTrans tyIH =>
      intro m Δ ρ w
      obtain ⟨tyPack', tyAdequate', weakened⟩ := tyIH w
      refine ⟨idPack S Δ (Presentation.rename ρ ty) (Presentation.rename ρ lhs)
        (Presentation.rename ρ rhs) tyPack',
        .ident (by simpa [Presentation.rename] using red.rename' w)
          (by simpa [Presentation.rename] using laws.convTy_rename w.1 w.2 refl) tyPack'
          tyAdequate' (weakened.redTm lhsRed) (weakened.redTm rhsRed)
          (weakened.eqTm lhsRefl) (weakened.eqTm rhsRefl)
          (tyAdequate'.eqTm_symm laws) (tyAdequate'.eqTm_trans laws), ?_⟩
      refine ⟨?_, ?_, ?_⟩
      · rintro B ⟨t, lh, rh, redB, equal, tyEq, lEq, rEq⟩
        exact ⟨Presentation.rename ρ t, Presentation.rename ρ lh, Presentation.rename ρ rh,
          by simpa [Presentation.rename] using redB.rename' w,
          by simpa [Presentation.rename] using laws.convTy_rename w.1 w.2 equal,
          weakened.eqTy tyEq, weakened.eqTm lEq, weakened.eqTm rEq⟩
      · rintro t ⟨nf, redT, reflT, prop⟩
        refine ⟨Presentation.rename ρ nf, by simpa [Presentation.rename] using redT.rename w.1,
          by simpa [Presentation.rename] using laws.convTm_rename w.1 w.2 reflT, ?_⟩
        rcases prop with ⟨x, rfl, typing, left, right⟩ | ⟨neutral, reflN⟩
        · exact .inl ⟨Presentation.rename ρ x, rfl, typing.rename w.1, weakened.eqTm left,
            weakened.eqTm right⟩
        · exact .inr ⟨neutral.rename ρ,
            by simpa [Presentation.rename] using laws.convNe_rename w.1 w.2 reflN⟩
      · rintro t t' ⟨nf, nf', redT, redT', equal, prop⟩
        refine ⟨Presentation.rename ρ nf, Presentation.rename ρ nf',
          by simpa [Presentation.rename] using redT.rename w.1,
          by simpa [Presentation.rename] using redT'.rename w.1,
          by simpa [Presentation.rename] using laws.convTm_rename w.1 w.2 equal, ?_⟩
        rcases prop with ⟨x, x', rfl, rfl, typing, typing', l₁, l₂, r₁, r₂⟩ |
          ⟨n₁, n₂, equalN⟩
        · exact .inl ⟨Presentation.rename ρ x, Presentation.rename ρ x', rfl, rfl,
            typing.rename w.1, typing'.rename w.1, weakened.eqTm l₁, weakened.eqTm l₂,
            weakened.eqTm r₁, weakened.eqTm r₂⟩
        · exact .inr ⟨n₁.rename ρ, n₂.rename ρ,
            by simpa [Presentation.rename] using laws.convNe_rename w.1 w.2 equalN⟩
  | @inductiveType n Γ A T ctors u red role typing isUniverse fieldPack fieldAdequate fieldIH =>
      intro m Δ ρ w
      /- The closed field types keep their meaning in `Δ`; their packs there are
      the canonical ones. -/
      have fields : ∀ {k : DeclName} {fields : List (Field Head)} {F : Tm Head 0},
          (k, fields) ∈ ctors → Field.closed F ∈ fields →
          LR S l (levelsBelow S l) Δ (liftClosed F) (packOf S Δ (liftClosed F)) ∧
            Weakened (fieldPack F) ρ (packOf S Δ (liftClosed F)) := by
        intro k fields F mem closed
        obtain ⟨P', reducible', weakened⟩ := fieldIH mem closed w
        rw [Presentation.rename_liftClosed] at reducible'
        rw [← (LogRel.reducible (S := S) (l := l) reducible').eq_packOf laws]
        exact ⟨reducible', weakened⟩
      refine ⟨indPack S Δ T ctors fun F => packOf S Δ (liftClosed F),
        .inductiveType (by simpa [Presentation.rename] using red.rename' w) role
          (by simpa [Presentation.rename] using typing.rename w.1) isUniverse _
          fun mem closed => (fields mem closed).1, ?_⟩
      refine ⟨?_, ?_, ?_⟩
      · intro B redB
        change RedTy S.R S.roles Δ _ (.const T)
        simpa [Presentation.rename] using redB.rename' w
      · intro t reducibleT
        exact IndRedTm.rename laws w
          (fun ⟨_, _, mem, closed⟩ _ h => (fields mem closed).2.redTm h) reducibleT
      · intro t t' equal
        exact IndEqTm.rename laws w
          (fun ⟨_, _, mem, closed⟩ _ _ h => (fields mem closed).2.eqTm h) equal

/-- Weakening at every level. -/
theorem LogRel.weaken (laws : S.E.Laws S.R S.roles) (l : L) :
    WeakensBelow S (LevelOrder.succ l) := by
  have every : ∀ l : L, WeakensBelow S l := by
    intro l
    induction l using LevelOrder.induction with
    | step l ih =>
        intro k lt n Γ A P reducible m Δ ρ w
        exact LR.weaken laws (ih k lt) reducible w
  exact @every (LevelOrder.succ l)

end Normalization
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
