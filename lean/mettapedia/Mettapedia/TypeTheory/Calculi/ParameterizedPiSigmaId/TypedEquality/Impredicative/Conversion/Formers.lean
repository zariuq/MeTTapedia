import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Conversion.Formation

/-!
# Type formers as terms of universes in the conversion model

The type formers build terms of a universe from terms of universes. On the
value side the universe relation relates types with one pack and one shape at
every world reached by a morphism; a type former gives both by the families of
its parts (`ValueSide.interp_family`, `ValueSide.shape_family`), exactly as
in every value model. Under related valuations, a codomain at related arguments
is the codomain under related valuations of the extended context, whose
realizer side is extended by a fresh variable of the domain's realizer
instance (`codomain_related`).

On the realizer side the realizers of a universe are the types: typed at the
universe, related by the generic equality there, and reaching weak-head forms
of types. A dependent function, pair or identity type is a weak-head form of a
type, is typed at the universe by its formation rule, and the generic equality
relates two of them when it relates their parts (`types_pi`, `types_sigma`,
`types_id`). The codomain of the second realizer instance is typed in the
context extended by the second domain, by conversion of the context along the
typed equality of the domains.

A context may also be converted along a type equality at a universe: related
valuations of the one extension are related valuations of the other, the
realizers being converted along the typed equality of the realizer instances
(`ValidMorN.convert`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Impredicative
namespace Conversion

open Normalization (inst0_rename_subst_liftSub CtxFormed IsType TypeEq)
open UniverseLevel (LevelOrder)
open Consistency (World Morph)
open ValueSide (universeAt)

variable {Head L : Type} [LevelOrder L]

/-- A substitution lifted under a binder is its extension by the fresh variable
after weakening. -/
theorem consSub_var_wk {n m : Nat} (σ : Sub Head n m) :
    consSub (.var 0) (fun i => Presentation.rename wk (σ i)) = liftSub σ :=
  rfl

/-! ## Type formers on the realizer side -/

section Realizers

variable {T : RealizerSide Head L} {m : Nat} {Δ : Ctx Head m}

/-- **Dependent function types are related as types** when their domains and
codomains are. -/
theorem types_pi {A A' : Tm Head m} {B B' : Tm Head (m + 1)} {u v w : Head}
    (hu : T.R.isUniverse u) (hv : T.R.isUniverse v) (join : T.R.join u v w)
    (dom : (ECand.types T).rel Δ (.head u) A A')
    (cod : (ECand.types T).rel (.snoc Δ A) (.head v) B B') :
    (ECand.types T).rel Δ (.head w) (.pi A B) (.pi A' B') := by
  obtain ⟨⟨tA, tA', cA⟩, -, -⟩ := dom
  obtain ⟨⟨tB, tB', cB⟩, -, -⟩ := cod
  have eA : TypeEq T.R Δ A A' := ⟨u, hu, T.laws.convTm_sound cA⟩
  have t : Typed T.R Δ (.pi A B) (.head w) := .piForm tA hu tB hv join
  have t' : Typed T.R Δ (.pi A' B') (.head w) :=
    .piForm tA' hu (Normalization.Typed.ctxConv tB' eA) hv join
  exact ⟨⟨t, t', T.laws.convTm_pi tA hu cA cB hv join⟩,
    ⟨_, .refl t, .inr (.inl ⟨_, _, rfl⟩)⟩, ⟨_, .refl t', .inr (.inl ⟨_, _, rfl⟩)⟩⟩

/-- **Dependent pair types are related as types** when their domains and
codomains are. -/
theorem types_sigma {A A' : Tm Head m} {B B' : Tm Head (m + 1)} {u v w : Head}
    (hu : T.R.isUniverse u) (hv : T.R.isUniverse v) (join : T.R.join u v w)
    (dom : (ECand.types T).rel Δ (.head u) A A')
    (cod : (ECand.types T).rel (.snoc Δ A) (.head v) B B') :
    (ECand.types T).rel Δ (.head w) (.sigma A B) (.sigma A' B') := by
  obtain ⟨⟨tA, tA', cA⟩, -, -⟩ := dom
  obtain ⟨⟨tB, tB', cB⟩, -, -⟩ := cod
  have eA : TypeEq T.R Δ A A' := ⟨u, hu, T.laws.convTm_sound cA⟩
  have t : Typed T.R Δ (.sigma A B) (.head w) := .sigmaForm tA hu tB hv join
  have t' : Typed T.R Δ (.sigma A' B') (.head w) :=
    .sigmaForm tA' hu (Normalization.Typed.ctxConv tB' eA) hv join
  exact ⟨⟨t, t', T.laws.convTm_sigma tA hu cA cB hv join⟩,
    ⟨_, .refl t, .inr (.inr (.inl ⟨_, _, rfl⟩))⟩, ⟨_, .refl t', .inr (.inr (.inl ⟨_, _, rfl⟩))⟩⟩

/-- **Identity types are related as types** when their carriers are related as
types and their endpoints are typed and related by the generic equality. -/
theorem types_id {A A' a a' b b' : Tm Head m} {u : Head} (hu : T.R.isUniverse u)
    (dom : (ECand.types T).rel Δ (.head u) A A') (ta : Typed T.R Δ a A)
    (ta' : Typed T.R Δ a' A) (ca : T.E.convTm Δ a a' A) (tb : Typed T.R Δ b A)
    (tb' : Typed T.R Δ b' A) (cb : T.E.convTm Δ b b' A) :
    (ECand.types T).rel Δ (.head u) (.id A a b) (.id A' a' b') := by
  obtain ⟨⟨tA, tA', cA⟩, -, -⟩ := dom
  have eA : TypeEq T.R Δ A A' := ⟨u, hu, T.laws.convTm_sound cA⟩
  have t : Typed T.R Δ (.id A a b) (.head u) := .idForm tA hu ta tb
  have t' : Typed T.R Δ (.id A' a' b') (.head u) :=
    .idForm tA' hu (Normalization.Typed.convType ta' eA) (Normalization.Typed.convType tb' eA)
  exact ⟨⟨t, t', T.laws.convTm_id cA hu ca cb⟩,
    ⟨_, .refl t, .inr (.inr (.inr (.inl ⟨_, _, _, rfl⟩)))⟩,
    ⟨_, .refl t', .inr (.inr (.inr (.inl ⟨_, _, _, rfl⟩)))⟩⟩

end Realizers

variable {M : NModel Head L}

section Rules

variable (laws : M.Laws)
include laws

/-! ## Valuations and universes -/

/-- Instances of two types under related valuations are related in a universe
when related valuations give them one interpretation and one shape at its
level. -/
theorem universeAt.of_interp {k : L} {n : Nat} {Γ : Ctx Head n} {T T' : Tm Head n}
    (here : ∀ {m r : Nat} {ξ : World M.reading m} {σ σ' : Sub Head n m} {Δ : Ctx Head r}
      {ς ς' : Sub Head n r}, EqSubstN M Γ ξ σ σ' Δ ς ς' →
        ∃ P, ValueSide.InterpAt M.value k ξ (Presentation.subst σ T) P ∧
          ValueSide.InterpAt M.value k ξ (Presentation.subst σ' T') P ∧
          ValueSide.Shape M.value (ValueSide.InterpAt M.value k) .pair ξ
            (Presentation.subst σ T) (Presentation.subst σ' T'))
    {m r : Nat} {ξ : World M.reading m} {σ σ' : Sub Head n m} {Δ : Ctx Head r}
    {ς ς' : Sub Head n r} (e : EqSubstN M Γ ξ σ σ' Δ ς ς') :
    (universeAt M.value k ξ).rel (Presentation.subst σ T) (Presentation.subst σ' T') := by
  intro _ _ _ w
  rw [rename_subst, rename_subst]
  exact here (EqSubstN.rename laws e w)

/-- A term of a universe is valid when related valuations give related instances
and realizer instances related by the types. -/
theorem ValidTmN.of_universe {n : Nat} {Γ : Ctx Head n} {T : Tm Head n} {u : Head}
    (isUniverse : M.rules.isUniverse u) (isUniverse' : M.side.R.isUniverse u)
    (rel : ∀ {m r : Nat} {ξ : World M.reading m} {σ σ' : Sub Head n m} {Δ : Ctx Head r}
      {ς ς' : Sub Head n r}, EqSubstN M Γ ξ σ σ' Δ ς ς' →
        (universeAt M.value (M.levels.level u) ξ).rel (Presentation.subst σ T)
            (Presentation.subst σ' T) ∧
          (ECand.types M.side).rel Δ (.head u) (Presentation.subst ς T)
            (Presentation.subst ς' T)) :
    ValidTmN M Γ T (.head u) := by
  refine ⟨ValidTyN.sort isUniverse isUniverse', fun {_ _ _ _ _ _ _ _} e {P} den => ?_⟩
  rw [ValueSide.DenS.sort_inv laws.value isUniverse den]
  exact rel e

/-- Two valid terms of a universe are validly equal when related valuations give
related instances of the one and the other, on both sides. -/
theorem ValidEqN.of_universe {n : Nat} {Γ : Ctx Head n} {T T' : Tm Head n} {u : Head}
    (isUniverse : M.rules.isUniverse u) (valid : ValidTmN M Γ T (.head u))
    (valid' : ValidTmN M Γ T' (.head u))
    (rel : ∀ {m r : Nat} {ξ : World M.reading m} {σ σ' : Sub Head n m} {Δ : Ctx Head r}
      {ς ς' : Sub Head n r}, EqSubstN M Γ ξ σ σ' Δ ς ς' →
        (universeAt M.value (M.levels.level u) ξ).rel (Presentation.subst σ T)
            (Presentation.subst σ' T') ∧
          (ECand.types M.side).rel Δ (.head u) (Presentation.subst ς T)
            (Presentation.subst ς' T')) :
    ValidEqN M Γ T T' (.head u) := by
  refine ⟨valid, valid', fun {_ _ _ _ _ _ _ _} e {P} den => ?_⟩
  rw [ValueSide.DenS.sort_inv laws.value isUniverse den]
  exact rel e

omit laws in
/-- The realizer instance of a term of a universe under related valuations is a
type of the realizer side. -/
theorem ValidTmN.realType {n : Nat} {Γ : Ctx Head n} {A : Tm Head n} {u : Head}
    (valid : ValidTmN M Γ A (.head u)) (hu : M.rules.isUniverse u)
    (hu' : M.side.R.isUniverse u) {m r : Nat} {ξ : World M.reading m} {σ σ' : Sub Head n m}
    {Δ : Ctx Head r} {ς ς' : Sub Head n r} (e : EqSubstN M Γ ξ σ σ' Δ ς ς') :
    IsType M.side.R Δ (Presentation.subst ς A) :=
  ⟨u, hu', ((ECand.types M.side).typed (valid.universe hu e).2).1⟩

/-- The codomains of two dependent types over one context are related at a
level at related arguments of the domain, under related valuations. -/
theorem codomain_related {n : Nat} {Γ : Ctx Head n} {A : Tm Head n} {B B' : Tm Head (n + 1)}
    {v : Head} {k : L} (le : M.levels.level v ≤ k)
    (related : ∀ {m r : Nat} {ξ : World M.reading m} {τ τ' : Sub Head (n + 1) m}
      {Δ : Ctx Head r} {ϑ ϑ' : Sub Head (n + 1) r}, EqSubstN M (.snoc Γ A) ξ τ τ' Δ ϑ ϑ' →
        (universeAt M.value (M.levels.level v) ξ).rel (Presentation.subst τ B)
          (Presentation.subst τ' B'))
    {m r : Nat} {ξ : World M.reading m} {σ σ' : Sub Head n m} {Δ : Ctx Head r}
    {ς ς' : Sub Head n r} (e : EqSubstN M Γ ξ σ σ' Δ ς ς')
    (typeA : IsType M.side.R Δ (Presentation.subst ς A)) :
    ∀ {m' : Nat} {ξ' : World M.reading m'} {ρ : Ren m m'}, Morph ξ ξ' ρ →
      ∀ {P : NPack M m'} {a b : Tm Head m'},
        ValueSide.InterpAt M.value k ξ' (Presentation.rename ρ (Presentation.subst σ A)) P →
          P.rel a b →
            (universeAt M.value k ξ').rel
              (inst0 a (Presentation.rename (liftRen ρ) (Presentation.subst (liftSub σ) B)))
              (inst0 b (Presentation.rename (liftRen ρ) (Presentation.subst (liftSub σ') B'))) := by
  intro _ _ _ w P a b hA hab
  rw [rename_subst] at hA
  rw [inst0_rename_subst_liftSub, inst0_rename_subst_liftSub]
  exact ValueSide.universeAt.mono laws.value le
    (related ((EqSubstN.rename laws e w).consVar typeA ⟨k, hA⟩ hab))

/-- **The formation rules at a universe, on the value side.** Under related
valuations, one family at a level interprets the instances of two dependent
types whose domains are related in a universe below it, and whose codomains are
related in a universe below it under related valuations; and the instances are
of one shape at that level, as dependent function types and as dependent pair
types. -/
theorem family_related {n : Nat} {Γ : Ctx Head n} {A A' : Tm Head n}
    {B B' : Tm Head (n + 1)} {u v : Head} {k : L} (leU : M.levels.level u ≤ k)
    (leV : M.levels.level v ≤ k)
    (domRel : ∀ {m r : Nat} {ξ : World M.reading m} {σ σ' : Sub Head n m} {Δ : Ctx Head r}
      {ς ς' : Sub Head n r}, EqSubstN M Γ ξ σ σ' Δ ς ς' →
        (universeAt M.value (M.levels.level u) ξ).rel (Presentation.subst σ A)
          (Presentation.subst σ' A'))
    (codRel : ∀ {m r : Nat} {ξ : World M.reading m} {τ τ' : Sub Head (n + 1) m}
      {Δ : Ctx Head r} {ϑ ϑ' : Sub Head (n + 1) r}, EqSubstN M (.snoc Γ A) ξ τ τ' Δ ϑ ϑ' →
        (universeAt M.value (M.levels.level v) ξ).rel (Presentation.subst τ B)
          (Presentation.subst τ' B'))
    {m r : Nat} {ξ : World M.reading m} {σ σ' : Sub Head n m} {Δ : Ctx Head r}
    {ς ς' : Sub Head n r} (e : EqSubstN M Γ ξ σ σ' Δ ς ς')
    (typeA : IsType M.side.R Δ (Presentation.subst ς A)) :
    ∃ Q : ValueSide.PiPack M.value ξ,
      Q.Interprets (ValueSide.InterpAt M.value k) (Presentation.subst σ A)
          (Presentation.subst (liftSub σ) B) ∧
        Q.Interprets (ValueSide.InterpAt M.value k) (Presentation.subst σ' A')
          (Presentation.subst (liftSub σ') B') ∧
        ValueSide.Shape M.value (ValueSide.InterpAt M.value k) .pair ξ
          (Presentation.subst σ (.pi A B)) (Presentation.subst σ' (.pi A' B')) ∧
        ValueSide.Shape M.value (ValueSide.InterpAt M.value k) .pair ξ
          (Presentation.subst σ (.sigma A B)) (Presentation.subst σ' (.sigma A' B')) := by
  have dom : (universeAt M.value k ξ).rel (Presentation.subst σ A) (Presentation.subst σ' A') :=
    ValueSide.universeAt.mono laws.value leU (domRel e)
  obtain ⟨Q, interprets, interprets'⟩ :=
    ValueSide.interp_family dom (codomain_related laws leV codRel e typeA) laws.value
  exact ⟨Q, interprets, interprets',
    ValueSide.shape_family dom (codomain_related laws leV codRel e typeA)⟩

/-! ## Dependent function and pair types -/

/-- The realizer instances of a codomain, at the valuation extended by the
daimon and a fresh variable of the domain's realizer instance. -/
theorem codomain_types {n : Nat} {Γ : Ctx Head n} {A : Tm Head n} {B B' : Tm Head (n + 1)}
    {u v : Head} (hu : M.rules.isUniverse u) (hu' : M.side.R.isUniverse u)
    (validA : ValidTmN M Γ A (.head u))
    (codRel : ∀ {m r : Nat} {ξ : World M.reading m} {τ τ' : Sub Head (n + 1) m}
      {Δ : Ctx Head r} {ϑ ϑ' : Sub Head (n + 1) r}, EqSubstN M (.snoc Γ A) ξ τ τ' Δ ϑ ϑ' →
        (ECand.types M.side).rel Δ (.head v) (Presentation.subst ϑ B) (Presentation.subst ϑ' B'))
    {m r : Nat} {ξ : World M.reading m} {σ σ' : Sub Head n m} {Δ : Ctx Head r}
    {ς ς' : Sub Head n r} (e : EqSubstN M Γ ξ σ σ' Δ ς ς') :
    (ECand.types M.side).rel (.snoc Δ (Presentation.subst ς A)) (.head v)
      (Presentation.subst (liftSub ς) B) (Presentation.subst (liftSub ς') B') := by
  obtain ⟨P, den, -, -⟩ := (validA.validTy hu hu') e
  exact codRel (e.consVar (validA.realType hu hu' e) den
    (ValueSide.DenS.star_val laws.value den))

/-- A dependent function type formed from terms of universes is a term of their
join. -/
theorem ValidTmN.piForm {n : Nat} {Γ : Ctx Head n} {A : Tm Head n} {B : Tm Head (n + 1)}
    {u v w : Head} (validA : ValidTmN M Γ A (.head u)) (hu : M.rules.isUniverse u)
    (hu' : M.side.R.isUniverse u) (validB : ValidTmN M (.snoc Γ A) B (.head v))
    (hv : M.rules.isUniverse v) (hv' : M.side.R.isUniverse v) (join : M.rules.join u v w)
    (join' : M.side.R.join u v w) : ValidTmN M Γ (.pi A B) (.head w) := by
  obtain ⟨leU, leV⟩ := ValueSide.level_join (V := M.value) join
  refine ValidTmN.of_universe laws (M.levels.join_level join).1
    (M.side.levels.join_level join').1 (fun e => ⟨?_, ?_⟩)
  · refine universeAt.of_interp laws (fun e' => ?_) e
    obtain ⟨Q, interprets, interprets', shape, -⟩ := family_related laws leU leV
      (fun e'' => (validA.universe hu e'').1) (fun e'' => (validB.universe hv e'').1) e'
      (validA.realType hu hu' e')
    exact ⟨_, ValueSide.PiPack.Interprets.pi interprets,
      ValueSide.PiPack.Interprets.pi interprets', shape⟩
  · exact types_pi hu' hv' join' (validA.universe hu e).2
      (codomain_types laws hu hu' validA (fun e'' => (validB.universe hv e'').2) e)

/-- A dependent pair type formed from terms of universes is a term of their
join. -/
theorem ValidTmN.sigmaForm {n : Nat} {Γ : Ctx Head n} {A : Tm Head n} {B : Tm Head (n + 1)}
    {u v w : Head} (validA : ValidTmN M Γ A (.head u)) (hu : M.rules.isUniverse u)
    (hu' : M.side.R.isUniverse u) (validB : ValidTmN M (.snoc Γ A) B (.head v))
    (hv : M.rules.isUniverse v) (hv' : M.side.R.isUniverse v) (join : M.rules.join u v w)
    (join' : M.side.R.join u v w) : ValidTmN M Γ (.sigma A B) (.head w) := by
  obtain ⟨leU, leV⟩ := ValueSide.level_join (V := M.value) join
  refine ValidTmN.of_universe laws (M.levels.join_level join).1
    (M.side.levels.join_level join').1 (fun e => ⟨?_, ?_⟩)
  · refine universeAt.of_interp laws (fun e' => ?_) e
    obtain ⟨Q, interprets, interprets', -, shape⟩ := family_related laws leU leV
      (fun e'' => (validA.universe hu e'').1) (fun e'' => (validB.universe hv e'').1) e'
      (validA.realType hu hu' e')
    exact ⟨_, ValueSide.PiPack.Interprets.sigma interprets,
      ValueSide.PiPack.Interprets.sigma interprets', shape⟩
  · exact types_sigma hu' hv' join' (validA.universe hu e).2
      (codomain_types laws hu hu' validA (fun e'' => (validB.universe hv e'').2) e)

/-- Dependent function types with equal domains and codomains are equal terms
of the join of their universes. -/
theorem ValidEqN.piCong {n : Nat} {Γ : Ctx Head n} {A A' : Tm Head n}
    {B B' : Tm Head (n + 1)} {u v w : Head} (eqA : ValidEqN M Γ A A' (.head u))
    (hu : M.rules.isUniverse u) (hu' : M.side.R.isUniverse u)
    (eqB : ValidEqN M (.snoc Γ A) B B' (.head v)) (hv : M.rules.isUniverse v)
    (hv' : M.side.R.isUniverse v) (join : M.rules.join u v w) (join' : M.side.R.join u v w)
    (validPi' : ValidTmN M Γ (.pi A' B') (.head w)) :
    ValidEqN M Γ (.pi A B) (.pi A' B') (.head w) := by
  obtain ⟨leU, leV⟩ := ValueSide.level_join (V := M.value) join
  refine ValidEqN.of_universe laws (M.levels.join_level join).1
    (ValidTmN.piForm laws eqA.1 hu hu' eqB.1 hv hv' join join') validPi' fun e => ⟨?_, ?_⟩
  · refine universeAt.of_interp laws (fun e' => ?_) e
    obtain ⟨Q, interprets, interprets', shape, -⟩ := family_related laws leU leV
      (fun e'' => (eqA.universe hu e'').1) (fun e'' => (eqB.universe hv e'').1) e'
      (eqA.1.realType hu hu' e')
    exact ⟨_, ValueSide.PiPack.Interprets.pi interprets,
      ValueSide.PiPack.Interprets.pi interprets', shape⟩
  · exact types_pi hu' hv' join' (eqA.universe hu e).2
      (codomain_types laws hu hu' eqA.1 (fun e'' => (eqB.universe hv e'').2) e)

/-- Dependent pair types with equal domains and codomains are equal terms of the
join of their universes. -/
theorem ValidEqN.sigmaCong {n : Nat} {Γ : Ctx Head n} {A A' : Tm Head n}
    {B B' : Tm Head (n + 1)} {u v w : Head} (eqA : ValidEqN M Γ A A' (.head u))
    (hu : M.rules.isUniverse u) (hu' : M.side.R.isUniverse u)
    (eqB : ValidEqN M (.snoc Γ A) B B' (.head v)) (hv : M.rules.isUniverse v)
    (hv' : M.side.R.isUniverse v) (join : M.rules.join u v w) (join' : M.side.R.join u v w)
    (validSigma' : ValidTmN M Γ (.sigma A' B') (.head w)) :
    ValidEqN M Γ (.sigma A B) (.sigma A' B') (.head w) := by
  obtain ⟨leU, leV⟩ := ValueSide.level_join (V := M.value) join
  refine ValidEqN.of_universe laws (M.levels.join_level join).1
    (ValidTmN.sigmaForm laws eqA.1 hu hu' eqB.1 hv hv' join join') validSigma' fun e => ⟨?_, ?_⟩
  · refine universeAt.of_interp laws (fun e' => ?_) e
    obtain ⟨Q, interprets, interprets', -, shape⟩ := family_related laws leU leV
      (fun e'' => (eqA.universe hu e'').1) (fun e'' => (eqB.universe hv e'').1) e'
      (eqA.1.realType hu hu' e')
    exact ⟨_, ValueSide.PiPack.Interprets.sigma interprets,
      ValueSide.PiPack.Interprets.sigma interprets', shape⟩
  · exact types_sigma hu' hv' join' (eqA.universe hu e).2
      (codomain_types laws hu hu' eqA.1 (fun e'' => (eqB.universe hv e'').2) e)

/-! ## Identity types -/

/-- An identity type formed from a term of a universe and two of its terms is
a term of the universe. -/
theorem ValidTmN.idForm {n : Nat} {Γ : Ctx Head n} {A a b : Tm Head n} {u : Head}
    (validA : ValidTmN M Γ A (.head u)) (hu : M.rules.isUniverse u)
    (hu' : M.side.R.isUniverse u) (valida : ValidTmN M Γ a A) (validb : ValidTmN M Γ b A) :
    ValidTmN M Γ (.id A a b) (.head u) := by
  refine ValidTmN.of_universe laws hu hu' (fun e => ⟨?_, ?_⟩)
  · exact universeAt.of_interp laws (fun e' => ValueSide.interp_ident laws.value
      (validA.universe hu e').1 (fun interp => (valida.2 e' ⟨_, interp⟩).1)
      (fun interp => (validb.2 e' ⟨_, interp⟩).1)) e
  · obtain ⟨P, den, -, -⟩ := valida.1 e
    obtain ⟨-, ra⟩ := valida.2 e den
    obtain ⟨-, rb⟩ := validb.2 e den
    obtain ⟨ta, ta'⟩ := (P.real _).typed ra
    obtain ⟨tb, tb'⟩ := (P.real _).typed rb
    exact types_id hu' (validA.universe hu e).2 ta ta' ((P.real _).escape ra) tb tb'
      ((P.real _).escape rb)

/-- Identity types with equal carriers and endpoints are equal terms of the
universe. -/
theorem ValidEqN.idCong {n : Nat} {Γ : Ctx Head n} {A A' a a' b b' : Tm Head n}
    {u : Head} (eqA : ValidEqN M Γ A A' (.head u)) (hu : M.rules.isUniverse u)
    (hu' : M.side.R.isUniverse u) (eqa : ValidEqN M Γ a a' A) (eqb : ValidEqN M Γ b b' A)
    (validId' : ValidTmN M Γ (.id A' a' b') (.head u)) :
    ValidEqN M Γ (.id A a b) (.id A' a' b') (.head u) := by
  refine ValidEqN.of_universe laws hu (ValidTmN.idForm laws eqA.1 hu hu' eqa.1 eqb.1) validId'
    fun e => ⟨?_, ?_⟩
  · exact universeAt.of_interp laws (fun e' => ValueSide.interp_ident laws.value
      (eqA.universe hu e').1 (fun interp => (eqa.2.2 e' ⟨_, interp⟩).1)
      (fun interp => (eqb.2.2 e' ⟨_, interp⟩).1)) e
  · obtain ⟨P, den, -, -⟩ := eqa.1.1 e
    obtain ⟨-, ra⟩ := eqa.2.2 e den
    obtain ⟨-, rb⟩ := eqb.2.2 e den
    obtain ⟨ta, ta'⟩ := (P.real _).typed ra
    obtain ⟨tb, tb'⟩ := (P.real _).typed rb
    exact types_id hu' (eqA.universe hu e).2 ta ta' ((P.real _).escape ra) tb tb'
      ((P.real _).escape rb)

/-! ## Conversion of a context extension -/

/-- Related valuations for an extension by a type are related valuations for an
extension by an equal type of a universe. -/
theorem ValidMorN.convert {n : Nat} {Γ : Ctx Head n} {A A' : Tm Head n} {u : Head}
    (ctx : ValidCtxN M Γ) (eqA : ValidEqN M Γ A A' (.head u)) (hu : M.rules.isUniverse u)
    (hu' : M.side.R.isUniverse u) : ValidMorN M (.snoc Γ A') ids (.snoc Γ A) := by
  intro _ _ ξ σ σ' Θ ς ς' e
  show EqSubstN M (.snoc Γ A) ξ σ σ' Θ ς ς'
  obtain ⟨tail, P, den, hab, hst⟩ := e
  have refl := EqSubstN.refl_left laws ctx tail
  obtain ⟨P', denA, denA'⟩ := eqA.den hu refl
  obtain rfl := ValueSide.DenS.deterministic laws.value den denA'
  have types := (eqA.universe hu refl).2
  refine ⟨tail, P, denA, hab, ?_⟩
  exact (P.real _).conv tail.formed
    (TypeEq.symm ⟨u, hu', (ECand.types M.side).equal types⟩) hst

end Rules

end Conversion
end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
