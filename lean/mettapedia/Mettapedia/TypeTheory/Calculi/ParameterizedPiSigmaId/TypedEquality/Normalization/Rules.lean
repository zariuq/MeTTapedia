import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.Identity

/-!
# Validity of the structural rules

Variables, universe heads, cumulativity, conversion, the equivalence rules,
head equality, declared root computations and declared constants.

Declared constants are where the model depends on the rule package beyond its
shape. A constant is semantic when it is reducible at its declared type in
every formed context. Rigid constants are semantic by neutral reflection;
computing constants, constructors and the type constants of inductive types
need arguments of their own.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Normalization

open UniverseLevel (LevelOrder)

variable {Head L : Type} [LevelOrder L] {S : Setting Head L}

/-! ## Heads -/

/-- Typed reduction at a universe is typed reduction at every universe above it. -/
theorem RedTm.cumul {n : Nat} {Δ : Ctx Head n} {t nf : Tm Head n} {u v : Head}
    (red : RedTm S.R S.roles Δ t nf (.head u)) (c : S.R.cumulative u v) :
    RedTm S.R S.roles Δ t nf (.head v) :=
  ⟨red.red, .cumul red.source c, .cumul red.target c, .cumulEq red.equal c⟩

/-- A head typed by a universe is reducible at the universe's level. -/
theorem head_logRel {n : Nat} {Δ : Ctx Head n} {h u : Head} (typing : S.R.headTyping h u)
    (formed : CtxFormed S.R Δ) : ∃ P, LogRel S (S.levels.level u) Δ (.head h) P := by
  have hu := S.levels.ground_typing typing
  have t : Typed S.R Δ (.head h) (.head u) := .headType typing
  rcases S.levels.universe_decided h with hh | hh
  · obtain ⟨_, level⟩ := S.levels.universe_typing hh typing
    exact ⟨_, .sort hh (level ▸ LevelOrder.lt_succ _) formed (RedTy.refl ⟨u, hu, t⟩)⟩
  · exact ⟨_, .ground hh (RedTy.refl ⟨u, hu, t⟩) t hu⟩

/-- A reducible head is reducibly equal to every equal typed head. -/
theorem LR.head_eqTy {l : L} {rec : L → RedRel Head} {n : Nat} {Δ : Ctx Head n}
    {h h' : Head} {Q : Pack Head n} (reducible : LR S l rec Δ (.head h) Q)
    (same : HeadSame S.R h h') (formed' : IsType S.R Δ (.head h')) : Q.eqTy (.head h') := by
  have normal : Whnf S.R S.roles (.head h : Tm Head n) := head_whnf S.shape h
  cases reducible with
  | sort _ _ _ red =>
      obtain rfl := Tm.head.inj (WhRed.eq_of_whnf normal red.red)
      exact ⟨h', RedTy.refl formed', same⟩
  | neutral red neutral =>
      exact absurd (WhRed.eq_of_whnf normal red.red) (neutral.not_former.1 _)
  | ground _ red =>
      obtain rfl := Tm.head.inj (WhRed.eq_of_whnf normal red.red)
      exact ⟨h', RedTy.refl formed', same⟩
  | pi red => exact absurd (WhRed.eq_of_whnf normal red.red) (by intro e; cases e)
  | sigma red => exact absurd (WhRed.eq_of_whnf normal red.red) (by intro e; cases e)
  | ident red => exact absurd (WhRed.eq_of_whnf normal red.red) (by intro e; cases e)
  | inductiveType red => exact absurd (WhRed.eq_of_whnf normal red.red) (by intro e; cases e)

theorem appSpine_const_ne_head {n : Nat} {c : DeclName} {as : List (Tm Head n)} {h : Head} :
    appSpine (.const c) as ≠ .head h := by
  rcases appSpine_const_cases c as with e | ⟨f, a, e⟩ <;> rw [e] <;> intro h' <;> cases h'

/-- Two equal heads in a reducible type's pack are reducibly equal. -/
theorem LR.heads_eqTm (laws : S.E.Laws S.R S.roles) {l : L} {n : Nat} {Δ : Ctx Head n}
    {A : Tm Head n} {P : Pack Head n} (reducible : LR S l (levelsBelow S l) Δ A P)
    {h h' : Head} (same : S.R.headEq h h') (hh : P.redTm (.head h))
    (hh' : P.redTm (.head h')) : P.eqTm (.head h) (.head h') := by
  have normal : Whnf S.R S.roles (.head h : Tm Head n) := head_whnf S.shape h
  have normal' : Whnf S.R S.roles (.head h' : Tm Head n) := head_whnf S.shape h'
  cases reducible with
  | @sort _ _ _ u isUniverse below formed red =>
      obtain ⟨nf, redH, form, _, Q, rQ⟩ := hh
      obtain ⟨nf', redH', form', _, Q', rQ'⟩ := hh'
      obtain rfl := WhRed.eq_of_whnf normal redH.red
      obtain rfl := WhRed.eq_of_whnf normal' redH'.red
      have lower := (levelsBelow_iff S below Δ _ Q).mp rQ
      exact ⟨_, _, redH, redH', form, form',
        laws.convTm_head (.inr same) redH.source redH'.source isUniverse, ⟨Q', rQ'⟩, Q, rQ,
        lower.head_eqTy (.inr same) ⟨u, isUniverse, redH'.source⟩⟩
  | neutral =>
      obtain ⟨nf, redH, neutral, _⟩ := hh
      obtain rfl := WhRed.eq_of_whnf normal redH.red
      exact absurd rfl (neutral.not_former.1 h)
  | ground =>
      obtain ⟨nf, redH, neutral, _⟩ := hh
      obtain rfl := WhRed.eq_of_whnf normal redH.red
      exact absurd rfl (neutral.not_former.1 h)
  | pi =>
      obtain ⟨nf, redH, isFun, _⟩ := hh
      obtain rfl := WhRed.eq_of_whnf normal redH.red
      rcases isFun with ⟨_, e⟩ | neutral | ⟨_, _, _, _, _, e⟩
      · cases e
      · exact absurd rfl (neutral.not_former.1 h)
      · exact absurd e.symm appSpine_const_ne_head
  | sigma =>
      obtain ⟨nf, redH, isPair, _⟩ := hh
      obtain rfl := WhRed.eq_of_whnf normal redH.red
      rcases isPair with ⟨_, _, e⟩ | neutral
      · cases e
      · exact absurd rfl (neutral.not_former.1 h)
  | ident =>
      obtain ⟨nf, redH, _, prop⟩ := hh
      obtain rfl := WhRed.eq_of_whnf normal redH.red
      rcases prop with ⟨_, e, _⟩ | ⟨neutral, _⟩
      · cases e
      · exact absurd rfl (neutral.not_former.1 h)
  | inductiveType =>
      obtain ⟨redH, _, normalH⟩ := hh
      obtain rfl := WhRed.eq_of_whnf normal redH.red
      rcases normalH.shape with ⟨_, _, _, _, _, e⟩ | ⟨neutral, _⟩
      · exact absurd e.symm appSpine_const_ne_head
      · exact absurd rfl (neutral.not_former.1 h)

/-! ## Structural rules -/

section Structural

variable (laws : S.E.Laws S.R S.roles)
include laws

/-- Variables of a valid context. -/
theorem ValidTm.var {n : Nat} {Γ : Ctx Head n} (valid : ValidCtx S Γ) (i : Fin n) :
    ValidTm S Γ (.var i) (Ctx.lookup Γ i) := by
  refine ⟨valid.lookup i, fun vσ P r => ?_, fun vσ vσ' e P r => ?_⟩
  · obtain ⟨Q, rQ, h⟩ := vσ.lookup i
    rw [r.unique laws rQ]
    exact h
  · obtain ⟨Q, rQ, h⟩ := e.lookup i
    rw [r.unique laws rQ]
    exact h

/-- Heads typed by a universe. -/
theorem ValidTm.headType {n : Nat} {Γ : Ctx Head n} {h u : Head}
    (typing : S.R.headTyping h u) : ValidTm S Γ (.head h) (.head u) := by
  have hu := S.levels.ground_typing typing
  have member : ∀ {m : Nat} {Δ : Ctx Head m}, CtxFormed S.R Δ →
      (universePack S (levelsBelow S (LevelOrder.succ (S.levels.level u))) Δ u).redTm (.head h) := by
    intro m Δ formed
    obtain ⟨P, r⟩ := head_logRel typing formed
    have t : Typed S.R Δ (.head h) (.head u) := .headType typing
    exact universe_member_intro t (laws.convTm_head (.inl rfl) t t hu) (.inl ⟨h, rfl⟩) r
  refine ⟨ValidTy.universe hu, fun vσ P r => ?_, fun vσ vσ' e P r => ?_⟩
  · rw [universe_pack laws hu vσ.formed r]
    exact member vσ.formed
  · rw [universe_pack laws hu vσ.formed r]
    exact (universe_logRel hu vσ.formed).reducible.reflexive.eqTm (member vσ.formed)

theorem universePack_cumul_redTm {n : Nat} {Δ : Ctx Head n} {u v : Head}
    (c : S.R.cumulative u v) {t : Tm Head n}
    (member : (universePack S (levelsBelow S (LevelOrder.succ (S.levels.level u))) Δ u).redTm t) :
    (universePack S (levelsBelow S (LevelOrder.succ (S.levels.level v))) Δ v).redTm t := by
  obtain ⟨_, _, le⟩ := S.levels.cumulative_universe c
  obtain ⟨nf, red, form, conv, Q, rQ⟩ := member
  have lower := (levelsBelow_iff S (LevelOrder.lt_succ _) Δ _ Q).mp rQ
  exact ⟨nf, red.cumul c, form, laws.convTm_cumul conv c, Q,
    (levelsBelow_iff S (LevelOrder.lt_succ _) Δ _ Q).mpr (lower.lift le)⟩

theorem universePack_cumul_eqTm {n : Nat} {Δ : Ctx Head n} {u v : Head}
    (c : S.R.cumulative u v) {t t' : Tm Head n}
    (equal : (universePack S (levelsBelow S (LevelOrder.succ (S.levels.level u))) Δ u).eqTm t t') :
    (universePack S (levelsBelow S (LevelOrder.succ (S.levels.level v))) Δ v).eqTm t t' := by
  obtain ⟨_, _, le⟩ := S.levels.cumulative_universe c
  obtain ⟨nf, nf', red, red', form, form', conv, ⟨Q', rQ'⟩, Q, rQ, eqQ⟩ := equal
  have lower := (levelsBelow_iff S (LevelOrder.lt_succ _) Δ _ Q).mp rQ
  have lower' := (levelsBelow_iff S (LevelOrder.lt_succ _) Δ _ Q').mp rQ'
  exact ⟨nf, nf', red.cumul c, red'.cumul c, form, form', laws.convTm_cumul conv c,
    ⟨Q', (levelsBelow_iff S (LevelOrder.lt_succ _) Δ _ Q').mpr (lower'.lift le)⟩, Q,
    (levelsBelow_iff S (LevelOrder.lt_succ _) Δ _ Q).mpr (lower.lift le), eqQ⟩

/-- Cumulativity of typing. -/
theorem ValidTm.cumul {n : Nat} {Γ : Ctx Head n} {t : Tm Head n} {u v : Head}
    (valid : ValidTm S Γ t (.head u)) (c : S.R.cumulative u v) : ValidTm S Γ t (.head v) := by
  obtain ⟨hu, hv, _⟩ := S.levels.cumulative_universe c
  refine ⟨ValidTy.universe hv, fun vσ P r => ?_, fun vσ vσ' e P r => ?_⟩
  · rw [universe_pack laws hv vσ.formed r]
    exact universePack_cumul_redTm laws c (valid.red vσ (universe_logRel hu vσ.formed).reducible)
  · rw [universe_pack laws hv vσ.formed r]
    exact universePack_cumul_eqTm laws c
      (valid.ext vσ vσ' e (universe_logRel hu vσ.formed).reducible)

/-- Cumulativity of equality. -/
theorem ValidEq.cumul {n : Nat} {Γ : Ctx Head n} {A B : Tm Head n} {u v : Head}
    (valid : ValidEq S Γ A B (.head u)) (c : S.R.cumulative u v) :
    ValidEq S Γ A B (.head v) := by
  obtain ⟨hu, hv, _⟩ := S.levels.cumulative_universe c
  refine ⟨valid.left.cumul laws c, valid.right.cumul laws c, fun vσ P r => ?_⟩
  rw [universe_pack laws hv vσ.formed r]
  exact universePack_cumul_eqTm laws c (valid.eq vσ (universe_logRel hu vσ.formed).reducible)

omit laws in
/-- Reflexivity of equality. -/
theorem ValidTm.eq_self {n : Nat} {Γ : Ctx Head n} {a A : Tm Head n} (valid : ValidTm S Γ a A) :
    ValidEq S Γ a a A :=
  ⟨valid, valid, fun vσ _ r => r.reflexive.eqTm (valid.red vσ r)⟩

/-- Symmetry of equality. -/
theorem ValidEq.symm {n : Nat} {Γ : Ctx Head n} {a b A : Tm Head n} (valid : ValidEq S Γ a b A) :
    ValidEq S Γ b a A :=
  ⟨valid.right, valid.left, fun vσ _ r => r.eqTm_symm laws (valid.eq vσ r)⟩

/-- Transitivity of equality. -/
theorem ValidEq.trans {n : Nat} {Γ : Ctx Head n} {a b c A : Tm Head n}
    (first : ValidEq S Γ a b A) (second : ValidEq S Γ b c A) : ValidEq S Γ a c A :=
  ⟨first.left, second.right, fun vσ _ r => r.eqTm_trans laws (first.eq vσ r) (second.eq vσ r)⟩

/-- Equality of universe heads. -/
theorem ValidEq.headEq {n : Nat} {Γ : Ctx Head n} {h h' : Head} {A : Tm Head n}
    (same : S.R.headEq h h') (valid : ValidTm S Γ (.head h) A) (valid' : ValidTm S Γ (.head h') A) :
    ValidEq S Γ (.head h) (.head h') A := by
  refine ⟨valid, valid', fun vσ P r => ?_⟩
  obtain ⟨l, rl⟩ := r
  exact LR.heads_eqTm laws rl same (valid.red vσ ⟨l, rl⟩) (valid'.red vσ ⟨l, rl⟩)

/-- A declared root computation between valid terms of one type. -/
theorem ValidEq.root {n : Nat} {Γ : Ctx Head n} {l r A : Tm Head n}
    (step : S.R.computation.step l r) (validL : ValidTm S Γ l A) (validR : ValidTm S Γ r A) :
    ValidEq S Γ l r A := by
  refine ⟨validL, validR, fun {m Δ σ} vσ P rP => ?_⟩
  have e := rP.escape laws
  have tl := (e.redTm (validL.red vσ rP)).1
  have tr := (e.redTm (validR.red vσ rP)).1
  have red := RedTm.root (roles := S.roles) (S.R.computation.substitute σ step) tl tr
  exact (rP.redTm_expand red (validR.red vσ rP)).2

end Structural

/-! ## Declared constants -/

/-- A declared constant is semantic when it is reducible at its declared type in
every formed context. -/
def SemanticConstant (S : Setting Head L) (name : DeclName) (type : Tm Head 0) : Prop :=
  ∀ {m : Nat} {Δ : Ctx Head m}, CtxFormed S.R Δ → ∀ {P : Pack Head m},
    Reducible S Δ (liftClosed type) P → P.redTm (.const name)

/-- Every declared constant of a rule package whose declared type is typed in a
universe is semantic in the model. -/
def SemanticConstantsOf (S : Setting Head L) (R : Rules Head) : Prop :=
  ∀ {name : DeclName} {type : Tm Head 0} {u : Head}, R.constantType name = some type →
    Typed R .nil type (.head u) → R.isUniverse u → SemanticConstant S name type

/-- Every declared constant of the model's rule package is semantic. -/
abbrev SemanticConstants (S : Setting Head L) : Prop := SemanticConstantsOf S S.R

/-- A rigid constant is semantic. -/
theorem SemanticConstant.rigid (laws : S.E.Laws S.R S.roles) {name : DeclName}
    {type : Tm Head 0} {u : Head} (declared : S.R.constantType name = some type)
    (typing : Typed S.R .nil type (.head u)) (hu : S.R.isUniverse u)
    (role : S.roles name = .rigid) : SemanticConstant S name type := by
  intro m Δ _ P r
  have t : Typed S.R Δ (.const name) (liftClosed type) := .const declared typing hu
  exact (r.reflects laws).redTm (.rigid [] role) t (laws.convNe_const name t)

/-- A rule package whose declared constants are all rigid has semantic
constants. -/
theorem SemanticConstants.of_rigid (laws : S.E.Laws S.R S.roles)
    (rigid : ∀ {name : DeclName} {type : Tm Head 0}, S.R.constantType name = some type →
      S.roles name = .rigid) : SemanticConstants S :=
  fun declared typing hu => SemanticConstant.rigid laws declared typing hu (rigid declared)

theorem subst_closed {m : Nat} (σ : Sub Head 0 m) (t : Tm Head 0) :
    Presentation.subst σ t = liftClosed t := by
  unfold liftClosed
  rw [← subst_renSub]
  exact subst_ext (fun i => Fin.elim0 i) t

/-- A semantic declared constant is valid at its declared type. -/
theorem ValidTm.const (laws : S.E.Laws S.R S.roles) {n : Nat} {Γ : Ctx Head n}
    {name : DeclName} {type : Tm Head 0} {u : Head}
    (validType : ValidTm S .nil type (.head u)) (hu : S.R.isUniverse u)
    (semantic : SemanticConstant S name type) :
    ValidTm S Γ (.const name) (liftClosed type) := by
  have validTy := validType.validTy laws hu
  have closed : ∀ {m : Nat} {Δ : Ctx Head m}, CtxFormed S.R Δ →
      ∃ P, Reducible S Δ (liftClosed type) P := by
    intro m Δ formed
    obtain ⟨P, r⟩ := validTy.red (Δ := Δ) (σ := fun i => Fin.elim0 i) formed
    rw [subst_closed] at r
    exact ⟨P, r⟩
  refine ⟨⟨fun vσ => ?_, fun vσ _ _ P r => ?_⟩, fun vσ P r => ?_, fun vσ _ _ P r => ?_⟩
  · rw [subst_liftClosed]
    exact closed vσ.formed
  · rw [subst_liftClosed] at r ⊢
    exact r.reflexive.eqTy
  · rw [subst_liftClosed] at r
    exact semantic vσ.formed r
  · rw [subst_liftClosed] at r
    exact r.reflexive.eqTm (semantic vσ.formed r)

end Normalization
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
