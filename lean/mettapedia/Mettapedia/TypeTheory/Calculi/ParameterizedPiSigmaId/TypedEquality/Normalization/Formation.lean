import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.Views

/-!
# Validity of type formation

Universes are valid types, and the terms of a universe are valid types.

Dependent function and pair types formed from valid terms of universes are
valid terms of the join, and are validly related when their domains and
codomains are. Relatedness takes both a change of terms and a change of
substitution, so formation, its substitution stability and the congruence
rule are instances of one statement.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Normalization

open UniverseLevel (LevelOrder)

variable {Head L : Type} [LevelOrder L] {S : Setting Head L}

/-- Terms related by validity: equal substitutions make them reducibly equal. -/
def ValidRel (S : Setting Head L) {n : Nat} (Γ : Ctx Head n) (t u A : Tm Head n) : Prop :=
  ∀ {m : Nat} {Δ : Ctx Head m} {σ σ' : Sub Head n m}, ValidSubst S Γ Δ σ →
    ValidSubst S Γ Δ σ' → EqSubst S Γ Δ σ σ' →
    ∀ {P}, Reducible S Δ (Presentation.subst σ A) P →
      P.eqTm (Presentation.subst σ t) (Presentation.subst σ' u)

theorem ValidTm.rel {n : Nat} {Γ : Ctx Head n} {t A : Tm Head n} (valid : ValidTm S Γ t A) :
    ValidRel S Γ t t A :=
  fun vσ vσ' equal _ reducible => valid.ext vσ vσ' equal reducible

theorem ValidEq.rel (laws : S.E.Laws S.R S.roles) {n : Nat} {Γ : Ctx Head n}
    {t u A : Tm Head n} (valid : ValidEq S Γ t u A) : ValidRel S Γ t u A :=
  fun vσ vσ' equal _ reducible =>
    reducible.eqTm_trans laws (valid.eq vσ reducible) (valid.right.ext vσ vσ' equal reducible)

/-! ## Universes -/

section Universes

variable (laws : S.E.Laws S.R S.roles)
include laws

omit laws in
/-- A universe is a valid type. -/
theorem ValidTy.universe {n : Nat} {Γ : Ctx Head n} {u : Head} (isUniverse : S.R.isUniverse u) :
    ValidTy S Γ (.head u) := by
  refine ⟨fun vσ => ⟨_, (universe_logRel isUniverse vσ.formed).reducible⟩,
    fun _ _ _ P reducible => ?_⟩
  exact reducible.reflexive.eqTy

/-- The members of a universe, typed and self-convertible. -/
theorem universe_member {n : Nat} {Δ : Ctx Head n} {u : Head} (isUniverse : S.R.isUniverse u)
    (formed : CtxFormed S.R Δ) {t : Tm Head n}
    (member : (universePack S (levelsBelow S (LevelOrder.succ (S.levels.level u))) Δ u).redTm t) :
    Typed S.R Δ t (.head u) ∧ S.E.convTm Δ t t (.head u) :=
  ((universe_logRel isUniverse formed).reducible.escape laws).redTm member

/-- Equal members of a universe are convertible, and the pack of the first is
reducibly equal to the second. -/
theorem universe_equal {n : Nat} {Δ : Ctx Head n} {u : Head} (isUniverse : S.R.isUniverse u)
    (formed : CtxFormed S.R Δ) {t t' : Tm Head n}
    (equal : (universePack S (levelsBelow S (LevelOrder.succ (S.levels.level u))) Δ u).eqTm t t') :
    S.E.convTm Δ t t' (.head u) ∧ (∃ P, LogRel S (S.levels.level u) Δ t P) ∧
      (packOf S Δ t).eqTy t' := by
  refine ⟨((universe_logRel isUniverse formed).reducible.escape laws).eqTm equal, ?_⟩
  obtain ⟨_, _, _, _, _, _, _, _, P, r, eqP⟩ := equal
  have lower := (levelsBelow_iff S (LevelOrder.lt_succ _) Δ t P).mp r
  refine ⟨⟨P, lower⟩, ?_⟩
  rwa [← lower.reducible.eq_packOf laws]

omit laws in
/-- A type in weak-head normal form, reducible at a universe's level and typed
and self-convertible in it, is a member of the universe. -/
theorem universe_member_intro {n : Nat} {Δ : Ctx Head n} {u : Head} {t : Tm Head n}
    {P : Pack Head n} (typing : Typed S.R Δ t (.head u)) (conv : S.E.convTm Δ t t (.head u))
    (form : IsTypeForm S.roles t) (reducible : LogRel S (S.levels.level u) Δ t P) :
    (universePack S (levelsBelow S (LevelOrder.succ (S.levels.level u))) Δ u).redTm t :=
  ⟨t, RedTm.refl typing, form, conv, P,
    (levelsBelow_iff S (LevelOrder.lt_succ _) Δ t P).mpr reducible⟩

omit laws in
/-- Two such types, convertible in the universe with the first's pack equal to
the second, are equal members of the universe. -/
theorem universe_equal_intro {n : Nat} {Δ : Ctx Head n} {u : Head} {t t' : Tm Head n}
    {P P' : Pack Head n} (typing : Typed S.R Δ t (.head u)) (typing' : Typed S.R Δ t' (.head u))
    (form : IsTypeForm S.roles t) (form' : IsTypeForm S.roles t')
    (conv : S.E.convTm Δ t t' (.head u)) (reducible : LogRel S (S.levels.level u) Δ t P)
    (reducible' : LogRel S (S.levels.level u) Δ t' P') (equal : P.eqTy t') :
    (universePack S (levelsBelow S (LevelOrder.succ (S.levels.level u))) Δ u).eqTm t t' :=
  ⟨t, t', RedTm.refl typing, RedTm.refl typing', form, form', conv,
    ⟨P', (levelsBelow_iff S (LevelOrder.lt_succ _) Δ t' P').mpr reducible'⟩, P,
    (levelsBelow_iff S (LevelOrder.lt_succ _) Δ t P).mpr reducible, equal⟩

/-- A valid term of a universe, at a valid substitution: typed, convertible,
and reducible at the universe's level with its pack `packOf`. -/
theorem ValidTm.universe_at {n m : Nat} {Γ : Ctx Head n} {A : Tm Head n} {u : Head}
    (valid : ValidTm S Γ A (.head u)) (isUniverse : S.R.isUniverse u) {Δ : Ctx Head m}
    {σ : Sub Head n m} (vσ : ValidSubst S Γ Δ σ) :
    Typed S.R Δ (Presentation.subst σ A) (.head u) ∧
      S.E.convTm Δ (Presentation.subst σ A) (Presentation.subst σ A) (.head u) ∧
      LogRel S (S.levels.level u) Δ (Presentation.subst σ A)
        (packOf S Δ (Presentation.subst σ A)) := by
  have member := valid.red vσ (universe_logRel (S := S) isUniverse vσ.formed).reducible
  obtain ⟨typing, conv⟩ := universe_member laws isUniverse vσ.formed member
  obtain ⟨P, r⟩ := valid.logRel_at_level isUniverse vσ
  exact ⟨typing, conv, r.packOf laws⟩

/-- Validly related terms of a universe, at equal valid substitutions. -/
theorem ValidRel.universe_at {n m : Nat} {Γ : Ctx Head n} {A A' : Tm Head n} {u : Head}
    (rel : ValidRel S Γ A A' (.head u)) (isUniverse : S.R.isUniverse u) {Δ : Ctx Head m}
    {σ σ' : Sub Head n m} (vσ : ValidSubst S Γ Δ σ) (vσ' : ValidSubst S Γ Δ σ')
    (equal : EqSubst S Γ Δ σ σ') :
    S.E.convTm Δ (Presentation.subst σ A) (Presentation.subst σ' A') (.head u) ∧
      (packOf S Δ (Presentation.subst σ A)).eqTy (Presentation.subst σ' A') := by
  have e := rel vσ vσ' equal (universe_logRel (S := S) isUniverse vσ.formed).reducible
  obtain ⟨conv, _, eqTy⟩ := universe_equal laws isUniverse vσ.formed e
  exact ⟨conv, eqTy⟩

/-- Types validly equal in a universe are validly equal types. -/
theorem ValidEq.tyEq {n : Nat} {Γ : Ctx Head n} {A B : Tm Head n} {u : Head}
    (valid : ValidEq S Γ A B (.head u)) (isUniverse : S.R.isUniverse u) : ValidTyEq S Γ A B := by
  refine ⟨valid.left.validTy laws isUniverse, valid.right.validTy laws isUniverse,
    fun {m Δ σ} vσ P reducible => ?_⟩
  have e := valid.eq vσ (universe_logRel (S := S) isUniverse vσ.formed).reducible
  obtain ⟨_, _, eqTy⟩ := universe_equal laws isUniverse vσ.formed e
  rwa [reducible.eq_packOf laws]

end Universes

/-! ## Parts of function and pair types -/

section Parts

variable (laws : S.E.Laws S.R S.roles)
include laws

/-- The parts of a dependent function or pair type formed from valid terms of
universes are reducible at every level above both universes. -/
theorem ValidTm.polyReducible {n m : Nat} {Γ : Ctx Head n} {A : Tm Head n}
    {B : Tm Head (n + 1)} {u v : Head} {l : L} (validA : ValidTm S Γ A (.head u))
    (hu : S.R.isUniverse u) (validB : ValidTm S (.snoc Γ A) B (.head v))
    (hv : S.R.isUniverse v) (le_u : S.levels.level u ≤ l) (le_v : S.levels.level v ≤ l)
    {Δ : Ctx Head m} {σ : Sub Head n m} (vσ : ValidSubst S Γ Δ σ) :
    PolyReducible S l Δ (Presentation.subst σ A) (Presentation.subst (liftSub σ) B) := by
  have validTyB := validB.validTy laws hv
  obtain ⟨_, _, rA⟩ := validA.universe_at laws hu vσ
  have lifted := vσ.lift laws rA.reducible
  obtain ⟨_, _, rB⟩ := validB.universe_at laws hv lifted
  refine ⟨(rA.reducible.escape laws).type, (rB.reducible.escape laws).type, ?_, ?_, ?_⟩
  · intro k Δ' ρ w
    rw [rename_subst]
    exact ((validA.universe_at laws hu (vσ.weaken laws w)).2.2).lift le_u
  · intro k Δ' ρ w a ha
    rw [inst0_rename_subst_liftSub]
    obtain ⟨P, reducible, hP⟩ := ha
    rw [rename_subst] at reducible
    exact ((validB.universe_at laws hv ((vσ.weaken laws w).cons reducible hP)).2.2).lift le_v
  · intro k Δ' ρ w a b ha hb hab
    rw [inst0_rename_subst_liftSub, inst0_rename_subst_liftSub]
    obtain ⟨P, reducible, hPa⟩ := ha
    obtain ⟨Q, reducibleQ, hQb⟩ := hb
    obtain ⟨R, reducibleR, hRab⟩ := hab
    rw [rename_subst] at reducible reducibleQ reducibleR
    have e₁ := reducible.unique laws reducibleQ
    have e₂ := reducible.unique laws reducibleR
    subst e₁ e₂
    have vτ := (vσ.weaken laws w).cons reducible hPa
    have vτ' := (vσ.weaken laws w).cons reducible hQb
    have eτ : EqSubst S (.snoc Γ A) Δ' _ _ :=
      EqSubst.cons ((vσ.weaken laws w).refl) reducible hRab
    obtain ⟨X, reducibleX⟩ := validTyB.red vτ
    rw [← reducibleX.eq_packOf laws]
    exact validTyB.ext vτ vτ' eτ reducibleX

/-- Dependent function types formed from valid terms of universes. -/
theorem ValidTm.pi_at {n m : Nat} {Γ : Ctx Head n} {A : Tm Head n} {B : Tm Head (n + 1)}
    {u v w : Head} (validA : ValidTm S Γ A (.head u)) (hu : S.R.isUniverse u)
    (validB : ValidTm S (.snoc Γ A) B (.head v)) (hv : S.R.isUniverse v)
    (join : S.R.join u v w) {Δ : Ctx Head m} {σ : Sub Head n m} (vσ : ValidSubst S Γ Δ σ) :
    ∃ parts : PolyReducible S (S.levels.level w) Δ (Presentation.subst σ A)
        (Presentation.subst (liftSub σ) B),
      Typed S.R Δ (.pi (Presentation.subst σ A) (Presentation.subst (liftSub σ) B)) (.head w) ∧
      S.E.convTm Δ (.pi (Presentation.subst σ A) (Presentation.subst (liftSub σ) B))
        (.pi (Presentation.subst σ A) (Presentation.subst (liftSub σ) B)) (.head w) ∧
      LogRel S (S.levels.level w) Δ
        (.pi (Presentation.subst σ A) (Presentation.subst (liftSub σ) B))
        (piPack S Δ (Presentation.subst σ A) (Presentation.subst (liftSub σ) B)
          parts.polyPack) := by
  obtain ⟨hw, level⟩ := S.levels.join_level join
  have parts := validA.polyReducible laws hu validB hv (l := S.levels.level w)
    (level ▸ le_max_left _ _) (level ▸ le_max_right _ _) vσ
  obtain ⟨tA, cA, rA⟩ := validA.universe_at laws hu vσ
  obtain ⟨tB, cB, _⟩ := validB.universe_at laws hv (vσ.lift laws rA.reducible)
  have typing : Typed S.R Δ (.pi (Presentation.subst σ A) (Presentation.subst (liftSub σ) B))
      (.head w) := .piForm tA hu tB hv join
  refine ⟨parts, typing, laws.convTm_pi tA hu cA cB hv join, parts.pi ⟨w, hw, typing⟩ ?_⟩
  exact laws.convTy_pi parts.domType (laws.convTy_of_convTm cA hu) (laws.convTy_of_convTm cB hv)

/-- Dependent pair types formed from valid terms of universes. -/
theorem ValidTm.sigma_at {n m : Nat} {Γ : Ctx Head n} {A : Tm Head n} {B : Tm Head (n + 1)}
    {u v w : Head} (validA : ValidTm S Γ A (.head u)) (hu : S.R.isUniverse u)
    (validB : ValidTm S (.snoc Γ A) B (.head v)) (hv : S.R.isUniverse v)
    (join : S.R.join u v w) {Δ : Ctx Head m} {σ : Sub Head n m} (vσ : ValidSubst S Γ Δ σ) :
    ∃ parts : PolyReducible S (S.levels.level w) Δ (Presentation.subst σ A)
        (Presentation.subst (liftSub σ) B),
      Typed S.R Δ (.sigma (Presentation.subst σ A) (Presentation.subst (liftSub σ) B))
        (.head w) ∧
      S.E.convTm Δ (.sigma (Presentation.subst σ A) (Presentation.subst (liftSub σ) B))
        (.sigma (Presentation.subst σ A) (Presentation.subst (liftSub σ) B)) (.head w) ∧
      LogRel S (S.levels.level w) Δ
        (.sigma (Presentation.subst σ A) (Presentation.subst (liftSub σ) B))
        (sigmaPack S Δ (Presentation.subst σ A) (Presentation.subst (liftSub σ) B)
          parts.polyPack) := by
  obtain ⟨hw, level⟩ := S.levels.join_level join
  have parts := validA.polyReducible laws hu validB hv (l := S.levels.level w)
    (level ▸ le_max_left _ _) (level ▸ le_max_right _ _) vσ
  obtain ⟨tA, cA, rA⟩ := validA.universe_at laws hu vσ
  obtain ⟨tB, cB, _⟩ := validB.universe_at laws hv (vσ.lift laws rA.reducible)
  have typing : Typed S.R Δ
      (.sigma (Presentation.subst σ A) (Presentation.subst (liftSub σ) B)) (.head w) :=
    .sigmaForm tA hu tB hv join
  refine ⟨parts, typing, laws.convTm_sigma tA hu cA cB hv join,
    parts.sigma ⟨w, hw, typing⟩ ?_⟩
  exact laws.convTy_sigma parts.domType (laws.convTy_of_convTm cA hu)
    (laws.convTy_of_convTm cB hv)

/-- Pointwise related parts: the domains are related in every world, and the
codomains at every reducible argument. -/
theorem ValidRel.poly_parts {n m : Nat} {Γ : Ctx Head n} {A A' : Tm Head n}
    {B B' : Tm Head (n + 1)} {u v : Head} (validA : ValidTm S Γ A (.head u))
    (relA : ValidRel S Γ A A' (.head u)) (hu : S.R.isUniverse u)
    (relB : ValidRel S (.snoc Γ A) B B' (.head v)) (hv : S.R.isUniverse v)
    {Δ : Ctx Head m} {σ σ' : Sub Head n m} (vσ : ValidSubst S Γ Δ σ)
    (vσ' : ValidSubst S Γ Δ σ') (equal : EqSubst S Γ Δ σ σ') :
    (∀ {k : Nat} {Δ' : Ctx Head k} {ρ : Ren m k}, World S Δ Δ' ρ →
      (packOf S Δ' (Presentation.rename ρ (Presentation.subst σ A))).eqTy
        (Presentation.rename ρ (Presentation.subst σ' A'))) ∧
    (∀ {k : Nat} {Δ' : Ctx Head k} {ρ : Ren m k}, World S Δ Δ' ρ → ∀ {a : Tm Head k},
      (packOf S Δ' (Presentation.rename ρ (Presentation.subst σ A))).redTm a →
      (packOf S Δ' (inst0 a (Presentation.rename (liftRen ρ)
        (Presentation.subst (liftSub σ) B)))).eqTy
        (inst0 a (Presentation.rename (liftRen ρ) (Presentation.subst (liftSub σ') B')))) := by
  have validTyA := validA.validTy laws hu
  refine ⟨fun w => ?_, fun {k} {Δ'} {ρ} w {a} ha => ?_⟩
  · rw [rename_subst, rename_subst]
    exact (relA.universe_at laws hu (vσ.weaken laws w) (vσ'.weaken laws w)
      (equal.weaken laws w)).2
  · rw [inst0_rename_subst_liftSub, inst0_rename_subst_liftSub]
    obtain ⟨P, reducible, hPa⟩ := ha
    rw [rename_subst] at reducible
    have vρσ := vσ.weaken laws w
    have vρσ' := vσ'.weaken laws w
    have eρ := equal.weaken laws w
    obtain ⟨Q, reducibleQ⟩ := validTyA.red vρσ'
    have same : P = Q := validTyA.pack_eq laws vρσ vρσ' eρ reducible reducibleQ
    subst same
    have vτ := vρσ.cons reducible hPa
    have vτ' := vρσ'.cons reducibleQ hPa
    have eτ : EqSubst S (.snoc Γ A) Δ' _ _ :=
      EqSubst.cons eρ reducible (reducible.reflexive.eqTm hPa)
    exact (relB.universe_at laws hv vτ vτ' eτ).2

/-- Dependent function types related in both parts are related in the join. -/
theorem ValidRel.pi {n : Nat} {Γ : Ctx Head n} {A A' : Tm Head n} {B B' : Tm Head (n + 1)}
    {u v w : Head} (validA : ValidTm S Γ A (.head u)) (validA' : ValidTm S Γ A' (.head u))
    (relA : ValidRel S Γ A A' (.head u)) (hu : S.R.isUniverse u)
    (validB : ValidTm S (.snoc Γ A) B (.head v)) (validB' : ValidTm S (.snoc Γ A') B' (.head v))
    (relB : ValidRel S (.snoc Γ A) B B' (.head v)) (hv : S.R.isUniverse v)
    (join : S.R.join u v w) : ValidRel S Γ (.pi A B) (.pi A' B') (.head w) := by
  intro m Δ σ σ' vσ vσ' equal P reducible
  have hw := (S.levels.join_level join).1
  rw [universe_pack laws hw vσ.formed reducible]
  obtain ⟨parts, typing, _, r⟩ := validA.pi_at laws hu validB hv join vσ
  obtain ⟨_, typing', _, r'⟩ := validA'.pi_at laws hu validB' hv join vσ'
  obtain ⟨tA, _, rA⟩ := validA.universe_at laws hu vσ
  obtain ⟨vlift', elift⟩ := EqSubst.lift laws (validA.validTy laws hu) vσ vσ' equal rA.reducible
  have cA := (relA.universe_at laws hu vσ vσ' equal).1
  have cB := (relB.universe_at laws hv (vσ.lift laws rA.reducible) vlift' elift).1
  have conv := laws.convTm_pi tA hu cA cB hv join
  obtain ⟨domEq, codEq⟩ := ValidRel.poly_parts laws validA relA hu relB hv vσ vσ' equal
  exact universe_equal_intro typing typing' (.inr (.inl ⟨_, _, rfl⟩))
    (.inr (.inl ⟨_, _, rfl⟩)) conv r r'
    ⟨_, _, RedTy.refl ⟨w, hw, typing'⟩, laws.convTy_of_convTm conv hw, domEq,
      fun w' _ ha => codEq w' ha⟩

/-- Dependent pair types related in both parts are related in the join. -/
theorem ValidRel.sigma {n : Nat} {Γ : Ctx Head n} {A A' : Tm Head n}
    {B B' : Tm Head (n + 1)} {u v w : Head} (validA : ValidTm S Γ A (.head u))
    (validA' : ValidTm S Γ A' (.head u)) (relA : ValidRel S Γ A A' (.head u))
    (hu : S.R.isUniverse u) (validB : ValidTm S (.snoc Γ A) B (.head v))
    (validB' : ValidTm S (.snoc Γ A') B' (.head v))
    (relB : ValidRel S (.snoc Γ A) B B' (.head v)) (hv : S.R.isUniverse v)
    (join : S.R.join u v w) : ValidRel S Γ (.sigma A B) (.sigma A' B') (.head w) := by
  intro m Δ σ σ' vσ vσ' equal P reducible
  have hw := (S.levels.join_level join).1
  rw [universe_pack laws hw vσ.formed reducible]
  obtain ⟨parts, typing, _, r⟩ := validA.sigma_at laws hu validB hv join vσ
  obtain ⟨_, typing', _, r'⟩ := validA'.sigma_at laws hu validB' hv join vσ'
  obtain ⟨tA, _, rA⟩ := validA.universe_at laws hu vσ
  obtain ⟨vlift', elift⟩ := EqSubst.lift laws (validA.validTy laws hu) vσ vσ' equal rA.reducible
  have cA := (relA.universe_at laws hu vσ vσ' equal).1
  have cB := (relB.universe_at laws hv (vσ.lift laws rA.reducible) vlift' elift).1
  have conv := laws.convTm_sigma tA hu cA cB hv join
  obtain ⟨domEq, codEq⟩ := ValidRel.poly_parts laws validA relA hu relB hv vσ vσ' equal
  exact universe_equal_intro typing typing' (.inr (.inr (.inl ⟨_, _, rfl⟩)))
    (.inr (.inr (.inl ⟨_, _, rfl⟩))) conv r r'
    ⟨_, _, RedTy.refl ⟨w, hw, typing'⟩, laws.convTy_of_convTm conv hw, domEq,
      fun w' _ ha => codEq w' ha⟩

/-- Formation of dependent function types. -/
theorem ValidTm.pi {n : Nat} {Γ : Ctx Head n} {A : Tm Head n} {B : Tm Head (n + 1)}
    {u v w : Head} (validA : ValidTm S Γ A (.head u)) (hu : S.R.isUniverse u)
    (validB : ValidTm S (.snoc Γ A) B (.head v)) (hv : S.R.isUniverse v)
    (join : S.R.join u v w) : ValidTm S Γ (.pi A B) (.head w) := by
  have hw := (S.levels.join_level join).1
  refine ⟨ValidTy.universe hw, fun {m Δ σ} vσ P reducible => ?_,
    ValidRel.pi laws validA validA validA.rel hu validB validB validB.rel hv join⟩
  rw [universe_pack laws hw vσ.formed reducible]
  obtain ⟨_, typing, conv, r⟩ := validA.pi_at laws hu validB hv join vσ
  exact universe_member_intro typing conv (.inr (.inl ⟨_, _, rfl⟩)) r

/-- Formation of dependent pair types. -/
theorem ValidTm.sigma {n : Nat} {Γ : Ctx Head n} {A : Tm Head n} {B : Tm Head (n + 1)}
    {u v w : Head} (validA : ValidTm S Γ A (.head u)) (hu : S.R.isUniverse u)
    (validB : ValidTm S (.snoc Γ A) B (.head v)) (hv : S.R.isUniverse v)
    (join : S.R.join u v w) : ValidTm S Γ (.sigma A B) (.head w) := by
  have hw := (S.levels.join_level join).1
  refine ⟨ValidTy.universe hw, fun {m Δ σ} vσ P reducible => ?_,
    ValidRel.sigma laws validA validA validA.rel hu validB validB validB.rel hv join⟩
  rw [universe_pack laws hw vσ.formed reducible]
  obtain ⟨_, typing, conv, r⟩ := validA.sigma_at laws hu validB hv join vσ
  exact universe_member_intro typing conv (.inr (.inr (.inl ⟨_, _, rfl⟩))) r

end Parts

/-! ## Context conversion -/

/-- Two contexts with the same valid and equal substitutions. -/
structure CtxEquiv (S : Setting Head L) {n : Nat} (Γ Γ' : Ctx Head n) : Prop where
  valid : ∀ {m : Nat} {Δ : Ctx Head m} {σ : Sub Head n m},
    ValidSubst S Γ Δ σ ↔ ValidSubst S Γ' Δ σ
  equal : ∀ {m : Nat} {Δ : Ctx Head m} {σ σ' : Sub Head n m}, ValidSubst S Γ Δ σ →
    (EqSubst S Γ Δ σ σ' ↔ EqSubst S Γ' Δ σ σ')

theorem CtxEquiv.symm {n : Nat} {Γ Γ' : Ctx Head n} (equiv : CtxEquiv S Γ Γ') :
    CtxEquiv S Γ' Γ :=
  ⟨equiv.valid.symm, fun vσ => (equiv.equal (equiv.valid.mpr vσ)).symm⟩

theorem ValidTy.transport {n : Nat} {Γ Γ' : Ctx Head n} {A : Tm Head n}
    (equiv : CtxEquiv S Γ Γ') (valid : ValidTy S Γ A) : ValidTy S Γ' A :=
  ⟨fun vσ => valid.red (equiv.valid.mpr vσ), fun vσ vσ' equal _ reducible =>
    valid.ext (equiv.valid.mpr vσ) (equiv.valid.mpr vσ')
      ((equiv.equal (equiv.valid.mpr vσ)).mpr equal) reducible⟩

theorem ValidTm.transport {n : Nat} {Γ Γ' : Ctx Head n} {t A : Tm Head n}
    (equiv : CtxEquiv S Γ Γ') (valid : ValidTm S Γ t A) : ValidTm S Γ' t A :=
  ⟨valid.type.transport equiv, fun vσ _ reducible => valid.red (equiv.valid.mpr vσ) reducible,
    fun vσ vσ' equal _ reducible => valid.ext (equiv.valid.mpr vσ) (equiv.valid.mpr vσ')
      ((equiv.equal (equiv.valid.mpr vσ)).mpr equal) reducible⟩

theorem ValidEq.transport {n : Nat} {Γ Γ' : Ctx Head n} {t u A : Tm Head n}
    (equiv : CtxEquiv S Γ Γ') (valid : ValidEq S Γ t u A) : ValidEq S Γ' t u A :=
  ⟨valid.left.transport equiv, valid.right.transport equiv,
    fun vσ _ reducible => valid.eq (equiv.valid.mpr vσ) reducible⟩

/-- Extending a context by validly equal types. -/
theorem CtxEquiv.snoc (laws : S.E.Laws S.R S.roles) {n : Nat} {Γ : Ctx Head n}
    {A A' : Tm Head n} {u : Head} (equal : ValidEq S Γ A A' (.head u))
    (isUniverse : S.R.isUniverse u) : CtxEquiv S (.snoc Γ A) (.snoc Γ A') := by
  have validA := equal.left.validTy laws isUniverse
  have validA' := equal.right.validTy laws isUniverse
  /- At every valid substitution, the two types have the same pack. -/
  have same : ∀ {m : Nat} {Δ : Ctx Head m} {τ : Sub Head n m}, ValidSubst S Γ Δ τ →
      ∀ {P Q}, Reducible S Δ (Presentation.subst τ A) P →
        Reducible S Δ (Presentation.subst τ A') Q → P = Q := by
    intro m Δ τ vτ P Q r r'
    have e := equal.eq vτ (universe_logRel (S := S) isUniverse vτ.formed).reducible
    obtain ⟨_, _, eqTy⟩ := universe_equal laws isUniverse vτ.formed e
    have := r.conv laws r' (by rwa [r.eq_packOf laws])
    exact this
  refine ⟨fun {m Δ σ} => ⟨?_, ?_⟩, fun {m Δ σ σ'} vσ => ⟨?_, ?_⟩⟩
  · rintro ⟨tail, P, r, h⟩
    obtain ⟨Q, r'⟩ := validA'.red tail
    exact ⟨tail, Q, r', by rwa [← same tail r r']⟩
  · rintro ⟨tail, Q, r', h⟩
    obtain ⟨P, r⟩ := validA.red tail
    exact ⟨tail, P, r, by rwa [same tail r r']⟩
  · rintro ⟨tail, P, r, h⟩
    obtain ⟨Q, r'⟩ := validA'.red vσ.1
    exact ⟨tail, Q, r', by rwa [← same vσ.1 r r']⟩
  · rintro ⟨tail, Q, r', h⟩
    obtain ⟨P, r⟩ := validA.red vσ.1
    exact ⟨tail, P, r, by rwa [same vσ.1 r r']⟩

/-- Congruence of dependent function types. -/
theorem ValidEq.pi (laws : S.E.Laws S.R S.roles) {n : Nat} {Γ : Ctx Head n}
    {A A' : Tm Head n} {B B' : Tm Head (n + 1)} {u v w : Head}
    (equalA : ValidEq S Γ A A' (.head u)) (hu : S.R.isUniverse u)
    (equalB : ValidEq S (.snoc Γ A) B B' (.head v)) (hv : S.R.isUniverse v)
    (join : S.R.join u v w) : ValidEq S Γ (.pi A B) (.pi A' B') (.head w) := by
  have validB' := equalB.right.transport (CtxEquiv.snoc laws equalA hu)
  refine ⟨ValidTm.pi laws equalA.left hu equalB.left hv join,
    ValidTm.pi laws equalA.right hu validB' hv join, fun vσ _ reducible => ?_⟩
  exact ValidRel.pi laws equalA.left equalA.right (equalA.rel laws) hu equalB.left validB'
    (equalB.rel laws) hv join vσ vσ vσ.refl reducible

/-- Congruence of dependent pair types. -/
theorem ValidEq.sigma (laws : S.E.Laws S.R S.roles) {n : Nat} {Γ : Ctx Head n}
    {A A' : Tm Head n} {B B' : Tm Head (n + 1)} {u v w : Head}
    (equalA : ValidEq S Γ A A' (.head u)) (hu : S.R.isUniverse u)
    (equalB : ValidEq S (.snoc Γ A) B B' (.head v)) (hv : S.R.isUniverse v)
    (join : S.R.join u v w) : ValidEq S Γ (.sigma A B) (.sigma A' B') (.head w) := by
  have validB' := equalB.right.transport (CtxEquiv.snoc laws equalA hu)
  refine ⟨ValidTm.sigma laws equalA.left hu equalB.left hv join,
    ValidTm.sigma laws equalA.right hu validB' hv join, fun vσ _ reducible => ?_⟩
  exact ValidRel.sigma laws equalA.left equalA.right (equalA.rel laws) hu equalB.left validB'
    (equalB.rel laws) hv join vσ vσ vσ.refl reducible

end Normalization
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
