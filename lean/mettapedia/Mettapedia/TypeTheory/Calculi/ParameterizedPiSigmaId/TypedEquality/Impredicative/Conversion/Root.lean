import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Conversion.Equality
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.ValueSide.TypeLike

/-!
# Root computations and head equality in the conversion model

**Root steps.** A root step of an object package is read in the conversion model
as a step of the value side's own computation, or as a decoding of a code, and
as a step of the realizer side's computation (`ModelRootN`). On the value side
the two sides are related by weak-head expansion, or, for a decoding, because a
code and its decoding have one pack and one shape at every world reached by a
morphism, exactly as in every value model. On the realizer side the realizer
instance of the step is a typed reduction, since both sides are typed at the
realizer instance of the type, so the candidate of the value relates the two
by expansion. So such a step preserves meaning (`ModelRootN.semantic`).

**Heads.** Heads that the package identifies are related on the value side by
their one pack and one shape at every level. On the realizer side, two heads
typed at a realizer type are related by the generic equality there: the type
of a head is above a universe, so the realizer type is typed-equal to a
universe at which both heads are typed (`RealizerSide.head_type`), and the
generic equality relates identified heads at a universe. When the value type is
a universe, the candidate of its values is the types, which relate the two
heads (`ValidEqN.headEq`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Impredicative
namespace Conversion

open Normalization hiding World
open UniverseLevel (LevelOrder)
open Consistency (World Morph Truth TypeLike Stuck Decodes)
open ValueSide (universeAt)

variable {Head L : Type} [LevelOrder L]

/-! ## Heads on the realizer side -/

namespace RealizerSide

variable {T : RealizerSide Head L}

/-- **A type usable at another, and equal to a universe, makes the other equal to
a universe** above it. -/
theorem below_head {n : Nat} {Γ : Ctx Head n} {X Y : Tm Head n} (formed : CtxFormed T.R Γ)
    (le : Below T.R Γ X Y) {v : Head} (hv : T.R.isUniverse v)
    (eX : TypeEq T.R Γ X (.head v)) :
    ∃ v', T.R.isUniverse v' ∧ TypeEq T.R Γ Y (.head v') ∧ Below T.R Γ (.head v) (.head v') := by
  refine Below.induction (motive := fun n Γ X Y => CtxFormed T.R Γ →
      ∀ {v : Head}, T.R.isUniverse v → TypeEq T.R Γ X (.head v) →
        ∃ v', T.R.isUniverse v' ∧ TypeEq T.R Γ Y (.head v') ∧
          Below T.R Γ (.head v) (.head v'))
    ?equal ?univ ?pi ?sigma ?trans le formed hv eX
  case equal =>
    intro n Γ X Y u e hu formed v hv eX
    exact ⟨v, hv, TypeEq.trans T.levels (TypeEq.symm ⟨u, hu, e⟩) eX,
      (IsType.head_of_universe (S := T.toSetting) hv).below_refl⟩
  case univ =>
    intro n Γ u v' c formed v hv eX
    obtain ⟨-, hv', -⟩ := T.levels.cumulative_universe c
    exact ⟨v', hv', (IsType.head_of_universe (S := T.toSetting) hv').refl,
      .subTrans eX.symm.below (.subUniv c)⟩
  case pi =>
    intro n Γ A₀ A₁ B₀ B₁ u u₁ w _ _ _ _ _ _ _ _ formed v hv eX
    obtain ⟨_, _, e, -⟩ :=
      (T.facts.forms eX formed (.inr (.inl ⟨_, _, rfl⟩)) (.inl ⟨v, rfl⟩)).pi_left
    cases e
  case sigma =>
    intro n Γ A₀ A₁ B₀ B₁ u u₁ _ _ _ _ _ _ _ _ formed v hv eX
    obtain ⟨_, _, e, -⟩ :=
      (T.facts.forms eX formed (.inr (.inr (.inl ⟨_, _, rfl⟩))) (.inl ⟨v, rfl⟩)).sigma_left
    cases e
  case trans =>
    intro n Γ X Y Z _ _ ih₁ ih₂ formed v hv eX
    obtain ⟨v₁, hv₁, eY, le₁⟩ := ih₁ formed hv eX
    obtain ⟨v₂, hv₂, eZ, le₂⟩ := ih₂ formed hv₁ eY
    exact ⟨v₂, hv₂, eZ, .subTrans le₁ le₂⟩

/-- **The type of a head is equal to a universe at which the head is typed.** -/
theorem head_type {n : Nat} {Γ : Ctx Head n} {h : Head} {B : Tm Head n}
    (formed : CtxFormed T.R Γ) (typing : Typed T.R Γ (.head h) B) :
    ∃ v, T.R.isUniverse v ∧ Typed T.R Γ (.head h) (.head v) ∧ TypeEq T.R Γ B (.head v) := by
  obtain ⟨u, headTyping, le⟩ := Typed.generation typing
  have hu := T.levels.ground_typing headTyping
  -- Along the closure of conversion, cumulativity and subtyping, the type stays
  -- equal to a universe at which the head is typed.
  have key : ∀ {X C : Tm Head n}, TypeLe T.R Γ X C →
      (∃ v, T.R.isUniverse v ∧ Typed T.R Γ (.head h) (.head v) ∧ TypeEq T.R Γ X (.head v)) →
      ∃ v, T.R.isUniverse v ∧ Typed T.R Γ (.head h) (.head v) ∧ TypeEq T.R Γ C (.head v) := by
    intro X C le'
    induction le' with
    | refl => exact id
    | conv e hw _ ih =>
        rintro ⟨v, hv, t, eX⟩
        exact ih ⟨v, hv, t, TypeEq.trans T.levels (TypeEq.symm ⟨_, hw, e⟩) eX⟩
    | cumul c _ ih =>
        rintro ⟨v, hv, t, eX⟩
        obtain ⟨-, hv', -⟩ := T.levels.cumulative_universe c
        exact ih ⟨_, hv', .cumul (Typed.convType t eX.symm) c,
          (IsType.head_of_universe (S := T.toSetting) hv').refl⟩
    | sub le₀ _ ih =>
        rintro ⟨v, hv, t, eX⟩
        obtain ⟨v', hv', eY, leV⟩ := below_head formed le₀ hv eX
        exact ih ⟨v', hv', .sub t leV, eY⟩
  exact key le ⟨u, hu, .headType headTyping, (IsType.head_of_universe (S := T.toSetting) hu).refl⟩

/-- **Heads that are the same up to the package's head equality, typed at one
type, are related there by the generic equality.** -/
theorem convTm_heads {n : Nat} {Γ : Ctx Head n} {h h' : Head} {B : Tm Head n}
    (formed : CtxFormed T.R Γ) (same : h = h' ∨ T.R.headEq h h')
    (typing : Typed T.R Γ (.head h) B) (typing' : Typed T.R Γ (.head h') B) :
    T.E.convTm Γ (.head h) (.head h') B := by
  obtain ⟨v, hv, t, eB⟩ := head_type formed typing
  exact T.laws.convTm_conv (T.laws.convTm_head same t (Typed.convType typing' eB) hv) eB.symm

end RealizerSide

variable {M : NModel Head L}

/-! ## Heads -/

/-- **Heads that the package identifies are validly equal wherever each is a
valid term of one type that is a universe under related valuations.** -/
theorem ValidEqN.headEq (laws : M.Laws) {n : Nat} {Γ : Ctx Head n} {h h' : Head}
    {A : Tm Head n} (same : M.rules.headEq h h') (same' : M.side.R.headEq h h')
    (valid : ValidTmN M Γ (.head h) A) (valid' : ValidTmN M Γ (.head h') A)
    (universeType : ∀ {m r : Nat} {ξ : World M.reading m} {σ σ' : Sub Head n m}
      {Δ : Ctx Head r} {ς ς' : Sub Head n r}, EqSubstN M Γ ξ σ σ' Δ ς ς' →
        ∃ v, M.rules.isUniverse v ∧ WhRed M.rules M.roles (Presentation.subst σ A) (.head v)) :
    ValidEqN M Γ (.head h) (.head h') A := by
  refine ⟨valid, valid', fun {_ _ _ _ _ _ _ _} e {P} den => ?_⟩
  have rel : P.rel (.head h) (.head h') := by
    obtain ⟨l, interp⟩ := den
    exact ValueSide.InterpAt.typeLike_coherent laws.value interp (y := .head h') (.head h)
      (.head h) (.head h')
      (fun {_ _ _ _} _ {_ _} first second => ValueSide.head_coherent laws.value same first second)
      (valid.2 e ⟨l, interp⟩).1 (valid'.2 e ⟨l, interp⟩).1
  refine ⟨rel, ?_⟩
  obtain ⟨v, hv, red⟩ := universeType e
  have real := (valid.2 e den).2
  have real' := (valid'.2 e den).2
  rw [ValueSide.DenS.univ_inv laws.value den red hv] at real real' ⊢
  obtain ⟨⟨t, -, -⟩, reach, -⟩ := real
  obtain ⟨⟨t', -, -⟩, -, reach'⟩ := real'
  exact ⟨⟨t, t', RealizerSide.convTm_heads e.formed (.inr same') t t'⟩, reach, reach'⟩

/-! ## Root steps -/

/-- A root step of an object package, read in the conversion model: a step of
the value side's own computation or a decoding of its codes, and a step of the
realizer side's computation. -/
def ModelRootN (M : NModel Head L) (D : Decoders Head) {n : Nat} (l r : Tm Head n) : Prop :=
  (M.rules.computation.step l r ∨ DecoderStep D l r) ∧ M.side.R.computation.step l r

/-- A root step preserves meaning in the conversion model when its two sides are
validly equal wherever each is a valid term of one type. -/
def RootSemanticN (M : NModel Head L) {n : Nat} (l r : Tm Head n) : Prop :=
  ∀ {Γ : Ctx Head n} {A : Tm Head n}, ValidTmN M Γ l A → ValidTmN M Γ r A →
    ValidEqN M Γ l r A

/-- The realizer part of a root step of the realizer side: at the realizer
instance of a type at which both sides are valid, the instance of the step is a
typed reduction, so the candidate of the right side's value relates the left
side's instance to the right side's second instance. -/
theorem ValidEqN.root_real (laws : M.Laws) {n : Nat} {Γ : Ctx Head n} {l r A : Tm Head n}
    (step : M.side.R.computation.step l r) (validL : ValidTmN M Γ l A)
    (validR : ValidTmN M Γ r A) {m k : Nat} {ξ : World M.reading m} {σ σ' : Sub Head n m}
    {Δ : Ctx Head k} {ς ς' : Sub Head n k} (e : EqSubstN M Γ ξ σ σ' Δ ς ς') {P : NPack M m}
    (den : DenN M ξ (Presentation.subst σ A) P)
    (related : P.rel (Presentation.subst σ l) (Presentation.subst σ' r)) :
    (P.real (Presentation.subst σ l)).rel Δ (Presentation.subst ς A) (Presentation.subst ς l)
      (Presentation.subst ς' r) := by
  obtain ⟨hr, rr⟩ := validR.2 e den
  have tl := ((P.real _).typed (validL.2 e den).2).1
  have tr := ((P.real _).typed rr).1
  have red := RedTm.root (roles := M.side.roles) (M.side.R.computation.substitute ς step) tl tr
  rw [ValueSide.DenS.real_eq_of_rel laws.value den (ValueSide.DenS.trans laws.value den related
    (ValueSide.DenS.symm laws.value den hr))]
  exact (P.real _).expand_left red rr

/-- **The two sides of a root step of the object package, read in the model,
are validly equal wherever each is a valid term.** -/
theorem ValidEqN.root (laws : M.Laws) {D : Decoders Head} (decodes : Decodes M.toModel D)
    {n : Nat} {Γ : Ctx Head n} {l r A : Tm Head n} (root : ModelRootN M D l r)
    (validL : ValidTmN M Γ l A) (validR : ValidTmN M Γ r A) : ValidEqN M Γ l r A := by
  refine ⟨validL, validR, fun {_ _ _ σ σ' _ _ _} e {P} den => ?_⟩
  have hl := (validL.2 e den).1
  have hr := (validR.2 e den).1
  have related : P.rel (Presentation.subst σ l) (Presentation.subst σ' r) := by
    rcases root.1 with step | step
    · exact (ValueSide.DenS.expansive laws.value den).left
        (.single (WhStep.root (M.rules.computation.substitute σ step))) hr
    · obtain ⟨k, interp⟩ := den
      exact ValueSide.InterpAt.typeLike_coherent laws.value interp (y := Presentation.subst σ r)
        (Consistency.DecoderStep.typeLike_left decodes (step.substitute σ))
        (Consistency.DecoderStep.typeLike_left decodes (step.substitute σ'))
        (Consistency.DecoderStep.typeLike_right (step.substitute σ'))
        (fun {_ _ _ ρ} _ {_ _} first second =>
          ⟨ValueSide.decoder_coherent laws.value decodes ((step.substitute σ).rename ρ) first
            second,
            ValueSide.decoder_shape laws.value decodes ((step.substitute σ).rename ρ) first
              second⟩) hl hr
  exact ⟨related, ValidEqN.root_real laws root.2 validL validR e den related⟩

/-- A root step read in the model, as a step of the value side's own computation
or a decoding of its codes, and a step of the realizer side's computation,
preserves meaning. -/
theorem ModelRootN.semantic (laws : M.Laws) {D : Decoders Head} (decodes : Decodes M.toModel D)
    {n : Nat} {l r : Tm Head n} (root : ModelRootN M D l r) : RootSemanticN M l r :=
  fun validL validR => ValidEqN.root laws decodes root validL validR

end Conversion
end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
