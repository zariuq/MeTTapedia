import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.WeakHead
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Functionality
import Mettapedia.TypeTheory.UniverseLevel.Order

/-!
# Typed reduction, formed contexts and universe levels

Typed weak-head reduction is weak-head reduction whose endpoints are typed
and equal at the given type; its soundness is part of the definition. Types
are terms of a universe, and type equality is equality at some universe.
Joining two universes gives a common upper universe, so type equality is an
equivalence relation.

A level model assigns to every universe head a level in a level order (a
well-founded linear order with a least level and a least strict upper bound,
`UniverseLevel.LevelOrder`) so that the universe of a universe is one
successor up, cumulativity does not lower levels, equal heads have equal
levels, and a join is a maximum. The tower of universes with explicit level
expressions has such a model in the natural numbers for every valuation of its
level variables.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Normalization

open UniverseLevel (LevelOrder)

variable {Head L : Type} [LevelOrder L]

/-! ## Universes -/

/-- What the normalization model needs from the universe heads of a rule
package, with levels in a level order `L`. -/
structure LevelModel (R : Rules Head) (L : Type) [LevelOrder L] where
  level : Head → L
  /-- Every universe is typed by a universe one level up. -/
  successor : ∀ {u : Head}, R.isUniverse u →
    ∃ v, R.isUniverse v ∧ R.headTyping u v ∧ level v = LevelOrder.succ (level u)
  /-- A universe head is typed only by universes one level up. -/
  universe_typing : ∀ {u v : Head}, R.isUniverse u → R.headTyping u v →
    R.isUniverse v ∧ level v = LevelOrder.succ (level u)
  /-- A head that is not a universe is typed by a universe. -/
  ground_typing : ∀ {h v : Head}, R.headTyping h v → R.isUniverse v
  cumulative_universe : ∀ {u v : Head}, R.cumulative u v →
    R.isUniverse u ∧ R.isUniverse v ∧ level u ≤ level v
  headEq_level : ∀ {h h' : Head}, R.headEq h h' →
    (R.isUniverse h ↔ R.isUniverse h') ∧ level h = level h'
  join_level : ∀ {u v w : Head}, R.join u v w →
    R.isUniverse w ∧ level w = max (level u) (level v)
  /-- Any two universes have a join. -/
  join_exists : ∀ {u v : Head}, R.isUniverse u → R.isUniverse v → ∃ w, R.join u v w
  /-- Any universe is below the join of it with another. -/
  join_upper : ∀ {u v w : Head}, R.join u v w → R.cumulative u w ∧ R.cumulative v w
  /-- A universe is below itself. -/
  cumulative_refl : ∀ {u : Head}, R.isUniverse u → R.cumulative u u
  headEq_symm : ∀ {h h' : Head}, R.headEq h h' → R.headEq h' h
  headEq_trans : ∀ {h h' h'' : Head}, R.headEq h h' → R.headEq h' h'' → R.headEq h h''
  /-- Whether a head is a universe is decided. -/
  universe_decided : ∀ h : Head, R.isUniverse h ∨ ¬ R.isUniverse h

/-- Two heads that are the same up to the rule package's head equality. -/
def HeadSame (R : Rules Head) (h h' : Head) : Prop := h = h' ∨ R.headEq h h'

theorem HeadSame.refl {R : Rules Head} (h : Head) : HeadSame R h h := .inl rfl

theorem HeadSame.symm {R : Rules Head} (levels : LevelModel R L) {h h' : Head}
    (same : HeadSame R h h') : HeadSame R h' h := by
  rcases same with rfl | equal
  · exact .inl rfl
  · exact .inr (levels.headEq_symm equal)

theorem HeadSame.trans {R : Rules Head} (levels : LevelModel R L) {h h' h'' : Head}
    (first : HeadSame R h h') (second : HeadSame R h' h'') : HeadSame R h h'' := by
  rcases first with rfl | e₁
  · exact second
  · rcases second with rfl | e₂
    · exact .inr e₁
    · exact .inr (levels.headEq_trans e₁ e₂)

theorem HeadSame.level {R : Rules Head} (levels : LevelModel R L) {h h' : Head}
    (same : HeadSame R h h') :
    (R.isUniverse h ↔ R.isUniverse h') ∧ levels.level h = levels.level h' := by
  rcases same with rfl | equal
  · exact ⟨Iff.rfl, rfl⟩
  · exact levels.headEq_level equal

/-! ## Types and type equality -/

/-- `A` is a type in `Γ`: a term of some universe. -/
def IsType (R : Rules Head) {n : Nat} (Γ : Ctx Head n) (A : Tm Head n) : Prop :=
  ∃ u, R.isUniverse u ∧ Typed R Γ A (.head u)

/-- Equality of types: equality at some universe. -/
def TypeEq (R : Rules Head) {n : Nat} (Γ : Ctx Head n) (A B : Tm Head n) : Prop :=
  ∃ u, R.isUniverse u ∧ Equal R Γ A B (.head u)

theorem TypeEq.symm {R : Rules Head} {n : Nat} {Γ : Ctx Head n} {A B : Tm Head n}
    (equal : TypeEq R Γ A B) : TypeEq R Γ B A := by
  obtain ⟨u, hu, e⟩ := equal
  exact ⟨u, hu, .symm e⟩

theorem TypeEq.trans {R : Rules Head} (levels : LevelModel R L) {n : Nat}
    {Γ : Ctx Head n} {A B C : Tm Head n}
    (first : TypeEq R Γ A B) (second : TypeEq R Γ B C) : TypeEq R Γ A C := by
  obtain ⟨u, hu, e₁⟩ := first
  obtain ⟨v, hv, e₂⟩ := second
  obtain ⟨w, join⟩ := levels.join_exists hu hv
  obtain ⟨uw, vw⟩ := levels.join_upper join
  exact ⟨w, (levels.join_level join).1, .trans (.cumulEq e₁ uw) (.cumulEq e₂ vw)⟩

theorem IsType.refl {R : Rules Head} {n : Nat} {Γ : Ctx Head n} {A : Tm Head n}
    (formed : IsType R Γ A) : TypeEq R Γ A A := by
  obtain ⟨u, hu, t⟩ := formed
  exact ⟨u, hu, .refl t⟩

/-- Conversion of a typing along an equality of types. -/
theorem Typed.convType {R : Rules Head} {n : Nat} {Γ : Ctx Head n} {t A B : Tm Head n}
    (typing : Typed R Γ t A) (equal : TypeEq R Γ A B) : Typed R Γ t B := by
  obtain ⟨u, hu, e⟩ := equal
  exact .conv typing e hu

theorem Equal.convType {R : Rules Head} {n : Nat} {Γ : Ctx Head n} {a b A B : Tm Head n}
    (equality : Equal R Γ a b A) (equal : TypeEq R Γ A B) : Equal R Γ a b B := by
  obtain ⟨u, hu, e⟩ := equal
  exact .convEq equality e hu

theorem TypeEq.rename {R : Rules Head} {n m : Nat} {Γ : Ctx Head n} {Δ : Ctx Head m}
    {ρ : Ren n m} {A B : Tm Head n} (equal : TypeEq R Γ A B) (compatible : CtxRen Γ Δ ρ) :
    TypeEq R Δ (Presentation.rename ρ A) (Presentation.rename ρ B) := by
  obtain ⟨u, hu, e⟩ := equal
  exact ⟨u, hu, by simpa [Presentation.rename] using e.rename compatible⟩

theorem IsType.rename {R : Rules Head} {n m : Nat} {Γ : Ctx Head n} {Δ : Ctx Head m}
    {ρ : Ren n m} {A : Tm Head n} (formed : IsType R Γ A) (compatible : CtxRen Γ Δ ρ) :
    IsType R Δ (Presentation.rename ρ A) := by
  obtain ⟨u, hu, t⟩ := formed
  exact ⟨u, hu, by simpa [Presentation.rename] using t.rename compatible⟩

/-! ## Formed contexts and Kripke worlds -/

/-- Every telescope entry is a type. -/
inductive CtxFormed (R : Rules Head) : {n : Nat} → Ctx Head n → Prop where
  | nil : CtxFormed R .nil
  | snoc {n : Nat} {Γ : Ctx Head n} {A : Tm Head n} :
      CtxFormed R Γ → IsType R Γ A → CtxFormed R (.snoc Γ A)

theorem CtxFormed.lookup {R : Rules Head} {n : Nat} {Γ : Ctx Head n}
    (formed : CtxFormed R Γ) (i : Fin n) : IsType R Γ (Ctx.lookup Γ i) := by
  induction formed with
  | nil => exact Fin.elim0 i
  | @snoc n Γ A _ typeA ih =>
      refine Fin.cases ?_ ?_ i
      · obtain ⟨u, hu, t⟩ := typeA
        exact ⟨u, hu, by simpa [Presentation.rename] using
          (Typed.weaken (extension := A) t)⟩
      · intro j
        obtain ⟨u, hu, t⟩ := ih j
        exact ⟨u, hu, by simpa [Presentation.rename] using
          (Typed.weaken (extension := A) t)⟩

/-- Renamings compose. -/
theorem CtxRen.comp {n m k : Nat} {Γ : Ctx Head n} {Δ : Ctx Head m} {Θ : Ctx Head k}
    {ρ : Ren n m} {ρ' : Ren m k} (first : CtxRen Γ Δ ρ) (second : CtxRen Δ Θ ρ') :
    CtxRen Γ Θ (fun i => ρ' (ρ i)) := by
  intro i
  rw [second (ρ i), first i, rename_comp]

theorem CtxRen.id {n : Nat} (Γ : Ctx Head n) : CtxRen Γ Γ idRen := by
  intro i
  rw [rename_id]
  rfl

/-- Weakening past one entry. -/
theorem CtxRen.wk {n : Nat} (Γ : Ctx Head n) (A : Tm Head n) :
    CtxRen Γ (.snoc Γ A) wk := fun _ => rfl

/-! ## Typed reduction -/

/-- Typed weak-head reduction of a term at a type. -/
structure RedTm (R : Rules Head) (roles : Roles Head) {n : Nat} (Γ : Ctx Head n)
    (t u A : Tm Head n) : Prop where
  red : WhRed R roles t u
  source : Typed R Γ t A
  target : Typed R Γ u A
  equal : Equal R Γ t u A

/-- Typed weak-head reduction of a type, at some universe. -/
structure RedTy (R : Rules Head) (roles : Roles Head) {n : Nat} (Γ : Ctx Head n)
    (A B : Tm Head n) : Prop where
  red : WhRed R roles A B
  sort : ∃ u, R.isUniverse u ∧ Typed R Γ A (.head u) ∧ Typed R Γ B (.head u) ∧
    Equal R Γ A B (.head u)

variable {R : Rules Head} {roles : Roles Head}

theorem RedTy.sourceType {n : Nat} {Γ : Ctx Head n} {A B : Tm Head n}
    (red : RedTy R roles Γ A B) : IsType R Γ A := by
  obtain ⟨u, hu, t, _⟩ := red.sort
  exact ⟨u, hu, t⟩

theorem RedTy.targetType {n : Nat} {Γ : Ctx Head n} {A B : Tm Head n}
    (red : RedTy R roles Γ A B) : IsType R Γ B := by
  obtain ⟨u, hu, _, t, _⟩ := red.sort
  exact ⟨u, hu, t⟩

theorem RedTy.typeEq {n : Nat} {Γ : Ctx Head n} {A B : Tm Head n}
    (red : RedTy R roles Γ A B) : TypeEq R Γ A B := by
  obtain ⟨u, hu, _, _, e⟩ := red.sort
  exact ⟨u, hu, e⟩

theorem RedTm.refl {n : Nat} {Γ : Ctx Head n} {t A : Tm Head n}
    (typing : Typed R Γ t A) : RedTm R roles Γ t t A :=
  ⟨.refl, typing, typing, .refl typing⟩

theorem RedTy.refl {n : Nat} {Γ : Ctx Head n} {A : Tm Head n}
    (formed : IsType R Γ A) : RedTy R roles Γ A A := by
  obtain ⟨u, hu, t⟩ := formed
  exact { red := .refl, sort := ⟨u, hu, t, t, .refl t⟩ }

theorem RedTm.trans {n : Nat} {Γ : Ctx Head n} {t u v A : Tm Head n}
    (first : RedTm R roles Γ t u A) (second : RedTm R roles Γ u v A) :
    RedTm R roles Γ t v A :=
  ⟨first.red.trans second.red, first.source, second.target,
    .trans first.equal second.equal⟩

theorem RedTy.trans (levels : LevelModel R L) {n : Nat} {Γ : Ctx Head n} {A B C : Tm Head n}
    (first : RedTy R roles Γ A B) (second : RedTy R roles Γ B C) :
    RedTy R roles Γ A C := by
  obtain ⟨u, hu, tA, _, e₁⟩ := first.sort
  obtain ⟨v, hv, _, tC, e₂⟩ := second.sort
  obtain ⟨w, join⟩ := levels.join_exists hu hv
  obtain ⟨uw, vw⟩ := levels.join_upper join
  exact { red := first.red.trans second.red,
          sort := ⟨w, (levels.join_level join).1, .cumul tA uw, .cumul tC vw,
            .trans (.cumulEq e₁ uw) (.cumulEq e₂ vw)⟩ }

theorem RedTm.conv {n : Nat} {Γ : Ctx Head n} {t u A B : Tm Head n}
    (red : RedTm R roles Γ t u A) (equal : TypeEq R Γ A B) : RedTm R roles Γ t u B :=
  ⟨red.red, Typed.convType red.source equal, Typed.convType red.target equal,
    Equal.convType red.equal equal⟩

/-- A term of a universe reduces as a type. -/
theorem RedTm.toRedTy {n : Nat} {Γ : Ctx Head n} {A B : Tm Head n} {u : Head}
    (red : RedTm R roles Γ A B (.head u)) (isUniverse : R.isUniverse u) :
    RedTy R roles Γ A B :=
  { red := red.red, sort := ⟨u, isUniverse, red.source, red.target, red.equal⟩ }

theorem RedTm.rename {n m : Nat} {Γ : Ctx Head n} {Δ : Ctx Head m} {ρ : Ren n m}
    {t u A : Tm Head n} (red : RedTm R roles Γ t u A) (compatible : CtxRen Γ Δ ρ) :
    RedTm R roles Δ (Presentation.rename ρ t) (Presentation.rename ρ u)
      (Presentation.rename ρ A) :=
  ⟨red.red.rename ρ, red.source.rename compatible, red.target.rename compatible,
    red.equal.rename compatible⟩

theorem RedTy.rename {n m : Nat} {Γ : Ctx Head n} {Δ : Ctx Head m} {ρ : Ren n m}
    {A B : Tm Head n} (red : RedTy R roles Γ A B) (compatible : CtxRen Γ Δ ρ) :
    RedTy R roles Δ (Presentation.rename ρ A) (Presentation.rename ρ B) := by
  obtain ⟨u, hu, tA, tB, e⟩ := red.sort
  exact { red := red.red.rename ρ,
          sort := ⟨u, hu, by simpa [Presentation.rename] using tA.rename compatible,
            by simpa [Presentation.rename] using tB.rename compatible,
            by simpa [Presentation.rename] using e.rename compatible⟩ }

theorem RedTm.subst {n m : Nat} {Γ : Ctx Head n} {Δ : Ctx Head m} {σ : Sub Head n m}
    {t u A : Tm Head n} (red : RedTm R roles Γ t u A) (typed : SubstMor R Γ Δ σ) :
    RedTm R roles Δ (Presentation.subst σ t) (Presentation.subst σ u)
      (Presentation.subst σ A) :=
  ⟨red.red.subst σ, red.source.substitute typed, red.target.substitute typed,
    red.equal.substitute typed⟩

/-! ## The contractions, typed -/

theorem RedTm.beta {n : Nat} {Γ : Ctx Head n} {A a : Tm Head n}
    {body B : Tm Head (n + 1)} {u : Head}
    (pi : Typed R Γ (.pi A B) (.head u)) (isUniverse : R.isUniverse u)
    (bodyTyping : Typed R (.snoc Γ A) body B) (argument : Typed R Γ a A) :
    RedTm R roles Γ (.app (.lam body) a) (inst0 a body) (inst0 a B) :=
  ⟨.single (.beta body a), .appElim (.lamIntro pi isUniverse bodyTyping) argument,
    bodyTyping.instantiate argument, .betaPi pi isUniverse bodyTyping argument⟩

theorem RedTm.root {n : Nat} {Γ : Ctx Head n} {t u A : Tm Head n}
    (step : R.computation.step t u) (source : Typed R Γ t A) (target : Typed R Γ u A) :
    RedTm R roles Γ t u A :=
  ⟨.single (.root step), source, target, .root step source target⟩

theorem RedTm.fstPair {n : Nat} {Γ : Ctx Head n} {A a b : Tm Head n}
    {B : Tm Head (n + 1)} {u : Head}
    (sigma : Typed R Γ (.sigma A B) (.head u)) (isUniverse : R.isUniverse u)
    (first : Typed R Γ a A) (second : Typed R Γ b (inst0 a B)) :
    RedTm R roles Γ (.fst (.pair a b)) a A :=
  ⟨.single (.fstPair a b), .fstElim (.pairIntro sigma isUniverse first second), first,
    .betaFst sigma isUniverse first second⟩

/-! ## Congruences, typed -/

theorem RedTm.app {n : Nat} {Γ : Ctx Head n} {f f' a A : Tm Head n}
    {B : Tm Head (n + 1)} (red : RedTm R roles Γ f f' (.pi A B))
    (argument : Typed R Γ a A) :
    RedTm R roles Γ (.app f a) (.app f' a) (inst0 a B) :=
  ⟨red.red.app a, .appElim red.source argument, .appElim red.target argument,
    .appCong red.equal (.refl argument)⟩

theorem RedTm.fst {n : Nat} {Γ : Ctx Head n} {p p' A : Tm Head n}
    {B : Tm Head (n + 1)} (red : RedTm R roles Γ p p' (.sigma A B)) :
    RedTm R roles Γ (.fst p) (.fst p') A :=
  ⟨red.red.fst, .fstElim red.source, .fstElim red.target, .fstCong red.equal⟩

/-- The second projection of a pair, at the type the projection rule gives. -/
theorem RedTm.sndPair {n : Nat} {Γ : Ctx Head n} {A a b : Tm Head n}
    {B : Tm Head (n + 1)} {u v : Head}
    (sigma : Typed R Γ (.sigma A B) (.head u)) (isUniverse : R.isUniverse u)
    (family : Typed R (.snoc Γ A) B (.head v)) (familyUniverse : R.isUniverse v)
    (first : Typed R Γ a A) (second : Typed R Γ b (inst0 a B)) :
    RedTm R roles Γ (.snd (.pair a b)) b (inst0 (.fst (.pair a b)) B) := by
  have pairTyping := Derivable.pairIntro sigma isUniverse first second
  have change : Equal R Γ (inst0 a B) (inst0 (.fst (.pair a b)) B) (.head v) := by
    simpa [inst0, Presentation.subst] using
      family.instantiateEq first (.symm (.betaFst sigma isUniverse first second))
  exact ⟨.single (.sndPair a b), .sndElim pairTyping, .conv second change familyUniverse,
    .convEq (.betaSnd sigma isUniverse first second) change familyUniverse⟩

theorem RedTm.snd {n : Nat} {Γ : Ctx Head n} {p p' A : Tm Head n}
    {B : Tm Head (n + 1)} {v : Head}
    (family : Typed R (.snoc Γ A) B (.head v)) (familyUniverse : R.isUniverse v)
    (red : RedTm R roles Γ p p' (.sigma A B)) :
    RedTm R roles Γ (.snd p) (.snd p') (inst0 (.fst p) B) := by
  have change : Equal R Γ (inst0 (.fst p') B) (inst0 (.fst p) B) (.head v) := by
    simpa [inst0, Presentation.subst] using
      family.instantiateEq (.fstElim red.target) (.symm (.fstCong red.equal))
  exact ⟨red.red.snd, .sndElim red.source, .conv (.sndElim red.target) change familyUniverse,
    .sndCong red.equal⟩

end Normalization
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
