import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Conversion.Pairs

/-!
# Equality, conversion and inclusion in the conversion model

Validly equal terms of a type form a partial equivalence, on both sides: the
relation of a denotation is a partial equivalence, candidates are partial
equivalences at each realizer type, and related values have one realizer. A
valid term is equal to itself, and equality is symmetric and transitive.

Equal types of a universe have one pack under the first of two related
valuations, and typed-equal realizer instances: the types of the universe
relate them. Terms and equalities move along them, their realizers converted
along the typed equality of the realizer instances (`ECand.conv`).

Inclusion covers the realizer instances of the types, the value relation and
the realizers of valid values, each read at the realizer instance of its type.
It holds between equal types of a universe, and between cumulative universes,
whose types are types of every universe above (`types_cumul`). It composes, and
it is preserved

* by dependent function types with equal domains and included codomains: the
  realizer instances are included by the subtyping rule of dependent function
  types; realizers of a function reach weak-head normal functions at the
  larger type too, and their applications to realizers of valid arguments
  realize the results in the larger codomain, by the inclusion of the
  codomains under the extended valuation;
* by dependent pair types with included domains and codomains: realizers of a
  valid pair have projections that realize the projections in the larger
  domain and codomain.

Terms and equalities move along inclusions.

An identity type relates all terms. Its proofs are realized by the identity
candidate of the endpoints' relation: between equal terms, reflexivity proofs
related by the generic equality are related (`ident_refl`); so reflexivity
proofs of valid terms are valid, and reflexivity proofs of equal terms are
equal.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Impredicative
namespace Conversion

open Normalization hiding World
open UniverseLevel (LevelOrder)
open Consistency (World Morph)
open ValueSide (universeAt)

variable {Head L : Type} [LevelOrder L]

/-! ## Identity proofs on the realizer side -/

/-- **Reflexivity proofs of related points are related identity proofs** when
the proposition of the identity candidate holds. -/
theorem ident_refl {T : RealizerSide Head L} {P : Prop} (p : P) {m : Nat} {Δ : Ctx Head m}
    {A x x' : Tm Head m} (typeId : IsType T.R Δ (.id A x x)) (tx : Typed T.R Δ x A)
    (tx' : Typed T.R Δ x' A) (cv : T.E.convTm Δ x x' A) :
    (ECand.ident T P).rel Δ (.id A x x) (.refl x) (.refl x') := by
  obtain ⟨v, hv, tId⟩ := typeId
  obtain ⟨u, tA, hu, -, -, -⟩ := Typed.generation tId
  have e : Equal T.R Δ x' x A := (T.laws.convTm_sound cv).symm
  have change : TypeEq T.R Δ (.id A x' x') (.id A x x) :=
    ⟨u, hu, .idCong (.refl tA) hu e e⟩
  have tr : Typed T.R Δ (.refl x) (.id A x x) := .reflIntro tx
  have tr' : Typed T.R Δ (.refl x') (.id A x x) := Typed.convType (.reflIntro tx') change
  exact .inr ⟨⟨A, x, x, RedTy.refl ⟨v, hv, tId⟩⟩, ⟨x, .refl tr⟩, ⟨x', .refl tr'⟩,
    T.laws.convTm_refl cv, p⟩

variable {M : NModel Head L}

/-! ## Equality is a partial equivalence -/

/-- A valid term is validly equal to itself. -/
theorem ValidEqN.refl {n : Nat} {Γ : Ctx Head n} {a A : Tm Head n}
    (valid : ValidTmN M Γ a A) : ValidEqN M Γ a a A :=
  ⟨valid, valid, fun {_ _ _ _ _ _ _ _} e {_} den => valid.2 e den⟩

section Laws

variable (laws : M.Laws)
include laws

/-- Valid equality is symmetric. -/
theorem ValidEqN.symm {n : Nat} {Γ : Ctx Head n} {a b A : Tm Head n}
    (eq : ValidEqN M Γ a b A) : ValidEqN M Γ b a A := by
  obtain ⟨valid₁, valid₂, rel⟩ := eq
  refine ⟨valid₂, valid₁, fun {_ _ _ _ _ _ _ _} e {P} den => ?_⟩
  obtain ⟨ha, ra⟩ := valid₁.2 e den
  obtain ⟨hb, rb⟩ := valid₂.2 e den
  obtain ⟨hab, rab⟩ := rel e den
  have hba : P.rel _ _ := ValueSide.DenS.trans laws.value den hb
    (ValueSide.DenS.symm laws.value den hab)
  refine ⟨ValueSide.DenS.trans laws.value den hba ha, ?_⟩
  rw [ValueSide.DenS.real_eq_of_rel laws.value den hba] at rb ⊢
  exact (P.real _).trans rb ((P.real _).trans ((P.real _).symm rab) ra)

/-- Valid equality is transitive. -/
theorem ValidEqN.trans {n : Nat} {Γ : Ctx Head n} {a b c A : Tm Head n}
    (eq₁ : ValidEqN M Γ a b A) (eq₂ : ValidEqN M Γ b c A) : ValidEqN M Γ a c A := by
  obtain ⟨valid₁, valid₂, rel₁⟩ := eq₁
  obtain ⟨-, valid₃, rel₂⟩ := eq₂
  refine ⟨valid₁, valid₃, fun {_ _ _ _ _ _ _ _} e {P} den => ?_⟩
  obtain ⟨hb, rb⟩ := valid₂.2 e den
  obtain ⟨hab, rab⟩ := rel₁ e den
  obtain ⟨hbc, rbc⟩ := rel₂ e den
  have hab' : P.rel _ _ := ValueSide.DenS.trans laws.value den hab
    (ValueSide.DenS.symm laws.value den hb)
  refine ⟨ValueSide.DenS.trans laws.value den hab' hbc, ?_⟩
  rw [← ValueSide.DenS.real_eq_of_rel laws.value den hab'] at rb rbc
  exact (P.real _).trans rab ((P.real _).trans ((P.real _).symm rb) rbc)

/-! ## Conversion -/

/-- Equal types of a universe have one pack under the first of two related
valuations, and typed-equal realizer instances. -/
theorem ValidEqN.den_left {n : Nat} {Γ : Ctx Head n} {A B : Tm Head n} {u : Head}
    (eq : ValidEqN M Γ A B (.head u)) (hu : M.rules.isUniverse u)
    (hu' : M.side.R.isUniverse u) {m r : Nat} {ξ : World M.reading m} {σ σ' : Sub Head n m}
    {Δ : Ctx Head r} {ς ς' : Sub Head n r} (e : EqSubstN M Γ ξ σ σ' Δ ς ς') :
    (∃ P : NPack M m, DenN M ξ (Presentation.subst σ A) P ∧
      DenN M ξ (Presentation.subst σ B) P) ∧
      TypeEq M.side.R Δ (Presentation.subst ς A) (Presentation.subst ς B) := by
  obtain ⟨P, denA, denB'⟩ := ValidEqN.den eq hu e
  obtain ⟨P', denB, denB'', -⟩ := (ValidTmN.validTy eq.2.1 hu hu') e
  obtain rfl := ValueSide.DenS.deterministic laws.value denB' denB''
  refine ⟨⟨_, denA, denB⟩, u, hu', ?_⟩
  have h₁ := (eq.universe hu e).2
  have h₂ := (eq.2.1.universe hu e).2
  exact (ECand.types M.side).equal ((ECand.types M.side).trans h₁ ((ECand.types M.side).symm h₂))

/-- A term of a type is a term of every equal type of a universe. -/
theorem ValidTmN.conv {n : Nat} {Γ : Ctx Head n} {t A B : Tm Head n}
    {u : Head} (valid : ValidTmN M Γ t A) (eq : ValidEqN M Γ A B (.head u))
    (hu : M.rules.isUniverse u) (hu' : M.side.R.isUniverse u) : ValidTmN M Γ t B := by
  obtain ⟨-, rel⟩ := valid
  refine ⟨ValidTmN.validTy eq.2.1 hu hu', fun {_ _ _ _ _ _ _ _} e {P} den => ?_⟩
  obtain ⟨⟨_, denA, denB⟩, typeEq⟩ := ValidEqN.den_left laws eq hu hu' e
  rw [ValueSide.DenS.deterministic laws.value den denB]
  obtain ⟨h, real⟩ := rel e denA
  exact ⟨h, (ECand.conv _ e.formed typeEq real)⟩

/-- Equal terms of a type are equal terms of every equal type of a universe. -/
theorem ValidEqN.conv {n : Nat} {Γ : Ctx Head n} {a b A B : Tm Head n}
    {u : Head} (valid : ValidEqN M Γ a b A) (eq : ValidEqN M Γ A B (.head u))
    (hu : M.rules.isUniverse u) (hu' : M.side.R.isUniverse u) : ValidEqN M Γ a b B := by
  obtain ⟨valid₁, valid₂, rel⟩ := valid
  refine ⟨ValidTmN.conv laws valid₁ eq hu hu', ValidTmN.conv laws valid₂ eq hu hu',
    fun {_ _ _ _ _ _ _ _} e {P} den => ?_⟩
  obtain ⟨⟨_, denA, denB⟩, typeEq⟩ := ValidEqN.den_left laws eq hu hu' e
  rw [ValueSide.DenS.deterministic laws.value den denB]
  obtain ⟨h, real⟩ := rel e denA
  exact ⟨h, (ECand.conv _ e.formed typeEq real)⟩

/-! ## Inclusion -/

/-- Equal types of a universe are validly below one another. -/
theorem ValidLeN.ofEq {n : Nat} {Γ : Ctx Head n} {A B : Tm Head n}
    {u : Head} (eq : ValidEqN M Γ A B (.head u)) (hu : M.rules.isUniverse u)
    (hu' : M.side.R.isUniverse u) : ValidLeN M Γ A B := by
  refine ⟨ValidTmN.validTy eq.1 hu hu', ValidTmN.validTy eq.2.1 hu hu',
    fun {_ _ _ _ _ _ _ _} e => ?_⟩
  obtain ⟨⟨_, denA, denB⟩, typeEq⟩ := ValidEqN.den_left laws eq hu hu' e
  refine ⟨typeEq.below, fun {P P'} den den' => ?_⟩
  obtain rfl := ValueSide.DenS.deterministic laws.value den denA
  obtain rfl := ValueSide.DenS.deterministic laws.value den' denB
  exact ⟨fun h => h, fun {_} _ {_ _} h => (ECand.conv _ e.formed typeEq h)⟩

/-- A universe is validly below every universe it is cumulative into: the
universe relation grows with the level, and the types of a universe are types
of every universe above it. -/
theorem ValidLeN.univ {n : Nat} {Γ : Ctx Head n} {u v : Head}
    (cumulative : M.rules.cumulative u v) (cumulative' : M.side.R.cumulative u v) :
    ValidLeN M Γ (.head u) (.head v) := by
  obtain ⟨hu, hv, le⟩ := M.levels.cumulative_universe cumulative
  obtain ⟨hu', hv', -⟩ := M.side.levels.cumulative_universe cumulative'
  refine ⟨ValidTyN.sort hu hu', ValidTyN.sort hv hv', fun {_ _ _ _ _ _ _ _} _ =>
    ⟨.subUniv cumulative', fun {P P'} den den' => ?_⟩⟩
  rw [ValueSide.DenS.sort_inv laws.value hu den, ValueSide.DenS.sort_inv laws.value hv den']
  exact ⟨fun h => ValueSide.universeAt.mono laws.value le h,
    fun {_} _ {_ _} h => types_cumul cumulative' h⟩

/-- A term of a type is a term of every type validly above it. -/
theorem ValidTmN.below {n : Nat} {Γ : Ctx Head n} {t A B : Tm Head n}
    (valid : ValidTmN M Γ t A) (le : ValidLeN M Γ A B) : ValidTmN M Γ t B := by
  obtain ⟨-, rel⟩ := valid
  obtain ⟨validA, validB, incl⟩ := le
  refine ⟨validB, fun {_ _ _ _ _ _ _ _} e {P'} den' => ?_⟩
  obtain ⟨P, den, -, -⟩ := validA e
  obtain ⟨h, real⟩ := rel e den
  obtain ⟨inclRel, inclReal⟩ := (incl e).2 den den'
  exact ⟨inclRel h, inclReal (ValueSide.DenS.refl_left laws.value den h) real⟩

/-- Equal terms of a type are equal terms of every type validly above it. -/
theorem ValidEqN.below {n : Nat} {Γ : Ctx Head n} {a b A B : Tm Head n}
    (valid : ValidEqN M Γ a b A) (le : ValidLeN M Γ A B) : ValidEqN M Γ a b B := by
  obtain ⟨valid₁, valid₂, rel⟩ := valid
  refine ⟨ValidTmN.below laws valid₁ le, ValidTmN.below laws valid₂ le,
    fun {_ _ _ _ _ _ _ _} e {P'} den' => ?_⟩
  obtain ⟨validA, -, incl⟩ := le
  obtain ⟨P, den, -, -⟩ := validA e
  obtain ⟨h, real⟩ := rel e den
  obtain ⟨inclRel, inclReal⟩ := (incl e).2 den den'
  exact ⟨inclRel h, inclReal (ValueSide.DenS.refl_left laws.value den h) real⟩

omit laws in
/-- Valid inclusion is transitive. -/
theorem ValidLeN.trans {n : Nat} {Γ : Ctx Head n} {A B C : Tm Head n}
    (le₁ : ValidLeN M Γ A B) (le₂ : ValidLeN M Γ B C) : ValidLeN M Γ A C := by
  obtain ⟨validA, validB, incl₁⟩ := le₁
  obtain ⟨-, validC, incl₂⟩ := le₂
  refine ⟨validA, validC, fun {_ _ _ _ _ _ _ _} e => ⟨.subTrans (incl₁ e).1 (incl₂ e).1,
    fun {P P''} den den'' => ?_⟩⟩
  obtain ⟨P', den', -, -⟩ := validB e
  obtain ⟨rel₁, real₁⟩ := (incl₁ e).2 den den'
  obtain ⟨rel₂, real₂⟩ := (incl₂ e).2 den' den''
  exact ⟨fun h => rel₂ (rel₁ h), fun {_} ha {_ _} h => real₂ (rel₁ ha) (real₁ ha h)⟩

/-- A dependent function type is validly below another with an equal domain of a
universe and a codomain validly above its own. -/
theorem ValidLeN.pi {n : Nat} {Γ : Ctx Head n} {A A' : Tm Head n}
    {B B' : Tm Head (n + 1)} {w : Head} (validPi : ValidTyN M Γ (.pi A B))
    (validPi' : ValidTyN M Γ (.pi A' B')) (eqA : ValidEqN M Γ A A' (.head w))
    (hw : M.rules.isUniverse w) (hw' : M.side.R.isUniverse w)
    (leB : ValidLeN M (.snoc Γ A) B B') : ValidLeN M Γ (.pi A B) (.pi A' B') := by
  obtain ⟨-, -, inclB⟩ := leB
  refine ⟨validPi, validPi', fun {m _ ξ σ σ' Δ ς ς'} e => ?_⟩
  obtain ⟨PPi, denPi, -, typesPi⟩ := validPi e
  obtain ⟨-, -, -, typesPi'⟩ := validPi' e
  obtain ⟨u, hu, tPi, -⟩ := typesPi.typed
  obtain ⟨u', hu'', tPi', -⟩ := typesPi'.typed
  obtain ⟨typeA, -⟩ := IsType.pi_parts ⟨u, hu, tPi⟩
  obtain ⟨-, typeEqA⟩ := ValidEqN.den_left laws eqA hw hw' e
  -- The realizer instances are included by the subtyping rule of function types.
  have below : Below M.side.R Δ (Presentation.subst ς (.pi A B))
      (Presentation.subst ς (.pi A' B')) := by
    obtain ⟨PA, denA, -, -⟩ := (ValidTmN.validTy eqA.1 hw hw') e
    have leB' := (inclB (e.consVar typeA denA (ValueSide.DenS.star_val laws.value denA))).1
    rw [consSub_var_wk] at leB'
    obtain ⟨w₁, hw₁, eA⟩ := typeEqA
    exact .subPi tPi hu tPi' hu'' eA hw₁ leB'
  refine ⟨below, fun {P P'} den den' => ?_⟩
  obtain ⟨l, Q, rfl, QI⟩ := ValueSide.DenS.pi_inv laws.value den
  obtain ⟨l', Q', rfl, QI'⟩ := ValueSide.DenS.pi_inv laws.value den'
  -- The two families have one domain pack at every world reached by a morphism.
  have dom : ∀ {k : Nat} {ξ' : World M.reading k} {ρ : Ren m k} (mor : Morph ξ ξ' ρ),
      Q'.dom mor = Q.dom mor := by
    intro k ξ' ρ mor
    have denA := QI.dom mor
    have denA' := QI'.dom mor
    rw [rename_subst] at denA denA'
    obtain ⟨⟨D, denD, denD'⟩, -⟩ := ValidEqN.den_left laws eqA hw hw' (EqSubstN.rename laws e mor)
    exact (ValueSide.DenS.deterministic laws.value ⟨l', denA'⟩ denD').trans
      (ValueSide.DenS.deterministic laws.value ⟨l, denA⟩ denD).symm
  refine ⟨fun {f g} h => ?_, fun {f} hf {t t'} ht => ?_⟩
  · intro k ξ' ρ mor a b ha' hab'
    have ha : (Q.dom mor).Val a := by rw [← dom mor]; exact ha'
    have hab : (Q.dom mor).rel a b := by rw [← dom mor]; exact hab'
    have denA := QI.dom mor
    have codB := QI.cod mor ha
    have codB' := QI'.cod mor ha'
    rw [rename_subst] at denA
    rw [inst0_rename_subst_liftSub] at codB codB'
    exact ((inclB (EqSubstN.consVar (EqSubstN.rename laws e mor) typeA ⟨l, denA⟩ ha)).2
      ⟨l, codB⟩ ⟨l', codB'⟩).1 (h mor ha hab)
  · -- Realizers of a function reach normal functions at the larger type, and their
    -- applications realize the results in the larger codomain.
    have hX := RedTy.refl (roles := M.side.roles) typesPi.left
    have hX' := RedTy.refl (roles := M.side.roles) typesPi'.left
    obtain ⟨⟨w₀, r, fw⟩, ⟨w₀', r', fw'⟩, cv, app⟩ := (PiPack.real_rel_pi Q f hX).mp ht
    refine (PiPack.real_rel_pi Q' f hX').mpr ⟨⟨w₀, r.below below, fw⟩,
      ⟨w₀', r'.below below, fw'⟩, M.side.laws.convTm_below cv below, ?_⟩
    intro k ξ' ρ mor a ha' k' Θ ρr world s s' hs
    have ha : (Q.dom mor).Val a := by rw [← dom mor]; exact ha'
    have hs₁ : ((Q.dom mor).real a).rel Θ
        (Presentation.rename ρr (Presentation.subst ς A)) s s' := by
      rw [← dom mor]
      exact (ECand.conv _ world.2 (typeEqA.rename world.1).symm hs)
    have h := app mor ha world hs₁
    have denA := QI.dom mor
    have codB := QI.cod mor ha
    have codB' := QI'.cod mor ha'
    rw [rename_subst] at denA
    rw [inst0_rename_subst_liftSub] at codB codB'
    have hs₂ : ((Q.dom mor).real a).rel Θ
        (Presentation.subst (fun i => Presentation.rename ρr (ς i)) A) s s' := by
      rw [← rename_subst]
      exact hs₁
    have e' := ((EqSubstN.rename laws e mor).renameReal world.1 world.2).cons ⟨l, denA⟩ ⟨ha, hs₂⟩
    rw [inst0_rename_subst_liftSub] at h ⊢
    exact ((inclB e').2 ⟨l, codB⟩ ⟨l', codB'⟩).2 (hf mor ha ha) h

/-- A dependent pair type is validly below another whose domain and codomain are
validly above its own. -/
theorem ValidLeN.sigma {n : Nat} {Γ : Ctx Head n} {A A' : Tm Head n}
    {B B' : Tm Head (n + 1)} (validS : ValidTyN M Γ (.sigma A B))
    (validS' : ValidTyN M Γ (.sigma A' B')) (leA : ValidLeN M Γ A A')
    (leB : ValidLeN M (.snoc Γ A) B B') : ValidLeN M Γ (.sigma A B) (.sigma A' B') := by
  obtain ⟨validA, -, inclA⟩ := leA
  obtain ⟨-, -, inclB⟩ := leB
  refine ⟨validS, validS', fun {m _ ξ σ σ' Δ ς ς'} e => ?_⟩
  obtain ⟨-, -, -, typesS⟩ := validS e
  obtain ⟨-, -, -, typesS'⟩ := validS' e
  obtain ⟨u, hu, tS, -⟩ := typesS.typed
  obtain ⟨u', hu', tS', -⟩ := typesS'.typed
  obtain ⟨typeA, -⟩ := IsType.sigma_parts ⟨u, hu, tS⟩
  -- The realizer instances are included by the subtyping rule of pair types.
  have below : Below M.side.R Δ (Presentation.subst ς (.sigma A B))
      (Presentation.subst ς (.sigma A' B')) := by
    obtain ⟨PA, denA, -, -⟩ := validA e
    have leB' := (inclB (e.consVar typeA denA (ValueSide.DenS.star_val laws.value denA))).1
    rw [consSub_var_wk] at leB'
    exact .subSigma tS hu tS' hu' (inclA e).1 leB'
  refine ⟨below, fun {P P'} den den' => ?_⟩
  obtain ⟨l, Q, rfl, QI⟩ := ValueSide.DenS.sigma_inv laws.value den
  obtain ⟨l', Q', rfl, QI'⟩ := ValueSide.DenS.sigma_inv laws.value den'
  have denA := QI.dom_id
  have denA' := QI'.dom_id
  obtain ⟨domRel, domReal⟩ := (inclA e).2 ⟨l, denA⟩ ⟨l', denA'⟩
  -- At a valid first projection, the codomain pack of the first family is included in
  -- that of the second.
  have cod : ∀ {a : Tm Head _} (ha : (Q.dom (Morph.id ξ)).Val a)
      (ha' : (Q'.dom (Morph.id ξ)).Val a) {k : Nat} {Θ : Ctx Head k} {τ τ' : Sub Head _ k}
      {x x' : Tm Head k},
      EqSubstN M (.snoc Γ A) ξ (consSub a σ) (consSub a σ') Θ (consSub x τ) (consSub x' τ') →
        (∀ {b c : Tm Head _}, (Q.cod (Morph.id ξ) ha).rel b c →
          (Q'.cod (Morph.id ξ) ha').rel b c) ∧
        ∀ {b : Tm Head _}, (Q.cod (Morph.id ξ) ha).Val b → ∀ {t t' : Tm Head k},
          ((Q.cod (Morph.id ξ) ha).real b).rel Θ (Presentation.subst (consSub x τ) B) t t' →
            ((Q'.cod (Morph.id ξ) ha').real b).rel Θ (Presentation.subst (consSub x τ) B') t t' := by
    intro a ha ha' k Θ τ τ' x x' e'
    have codB := QI.cod_id ha
    have codB' := QI'.cod_id ha'
    rw [Normalization.inst0_subst_liftSub] at codB codB'
    exact (inclB e').2 ⟨l, codB⟩ ⟨l', codB'⟩
  refine ⟨?_, ?_⟩
  · rintro p q ⟨hp, hpq, hc⟩
    obtain ⟨PA, denA₀, -, -⟩ := validA e
    obtain rfl := ValueSide.DenS.deterministic laws.value denA₀ ⟨l, denA⟩
    have e' := e.consVar typeA ⟨l, denA⟩ hp
    exact ⟨domRel hp, domRel hpq, (cod hp (domRel hp) e').1 hc⟩
  · -- Realizers of a valid pair have projections realizing the projections in the
    -- larger domain and codomain.
    intro p hv t t' ht
    obtain ⟨hp, _, hc⟩ := hv
    have hp' := domRel hp
    have hX := RedTy.refl (roles := M.side.roles) typesS.left
    have hX' := RedTy.refl (roles := M.side.roles) typesS'.left
    obtain ⟨⟨w₀, r, pw⟩, ⟨w₀', r', pw'⟩, cv, proj⟩ :=
      (PiPack.pairReal_rel_sigma Q p hp hX).mp ht
    refine (PiPack.pairReal_rel_sigma Q' p hp' hX').mpr ⟨⟨w₀, r.below below, pw⟩,
      ⟨w₀', r'.below below, pw'⟩, M.side.laws.convTm_below cv below, ?_⟩
    intro k Θ ρr world
    obtain ⟨h₁, h₂⟩ := proj world
    have eR := e.renameReal world.1 world.2
    have h₁' : ((Q.dom (Morph.id ξ)).real (.fst p)).rel Θ
        (Presentation.subst (fun i => Presentation.rename ρr (ς i)) A)
        (.fst (Presentation.rename ρr t)) (.fst (Presentation.rename ρr t')) := by
      rw [← rename_subst]
      exact h₁
    have first := ((inclA eR).2 ⟨l, denA⟩ ⟨l', denA'⟩).2 hp h₁'
    rw [← rename_subst] at first
    refine ⟨first, ?_⟩
    have e' := eR.cons ⟨l, denA⟩ ⟨hp, h₁'⟩
    rw [inst0_rename_subst_liftSub] at h₂ ⊢
    exact (cod hp hp' e').2 hc h₂

/-! ## Identity types -/

/-- An identity type between valid terms of a type is a valid type. -/
theorem ValidTyN.ident {n : Nat} {Γ : Ctx Head n} {A a b : Tm Head n}
    (valid₁ : ValidTmN M Γ a A) (valid₂ : ValidTmN M Γ b A) :
    ValidTyN M Γ (.id A a b) := by
  intro _ _ _ σ σ' Δ ς ς' e
  obtain ⟨R, den, den', types⟩ := valid₁.1 e
  obtain ⟨ha, ra⟩ := valid₁.2 e den
  obtain ⟨hb, rb⟩ := valid₂.2 e den
  -- Related endpoints are related exactly when the other endpoints are.
  have same : R.rel (Presentation.subst σ a) (Presentation.subst σ b) ↔
      R.rel (Presentation.subst σ' a) (Presentation.subst σ' b) :=
    ⟨fun h => ValueSide.DenS.trans laws.value den (ValueSide.DenS.trans laws.value den
        (ValueSide.DenS.symm laws.value den ha) h) hb,
      fun h => ValueSide.DenS.trans laws.value den (ValueSide.DenS.trans laws.value den ha h)
        (ValueSide.DenS.symm laws.value den hb)⟩
  obtain ⟨u, hu, typesA⟩ := types
  obtain ⟨ta, ta'⟩ := (R.real _).typed ra
  obtain ⟨tb, tb'⟩ := (R.real _).typed rb
  refine ⟨_, ValueSide.DenS.ident den (ValueSide.DenS.refl_left laws.value den ha)
    (ValueSide.DenS.refl_left laws.value den hb), ?_,
    u, hu, types_id hu typesA ta ta' ((R.real _).escape ra) tb tb' ((R.real _).escape rb)⟩
  have e' : ValueSide.identPack R (Presentation.subst σ a) (Presentation.subst σ b) =
      ValueSide.identPack R (Presentation.subst σ' a) (Presentation.subst σ' b) := by
    unfold ValueSide.identPack
    rw [propext same]
  rw [e']
  exact ValueSide.DenS.ident den' (ValueSide.DenS.refl_right laws.value den ha)
    (ValueSide.DenS.refl_right laws.value den hb)

/-- Reflexivity proofs of equal terms are equal proofs of the identity of the
first with itself. -/
theorem ValidEqN.reflCong {n : Nat} {Γ : Ctx Head n} {a b A : Tm Head n}
    (eq : ValidEqN M Γ a b A) :
    ValidEqN M Γ (.refl a) (.refl b) (.id A a a) := by
  have validId : ValidTyN M Γ (.id A a a) := ValidTyN.ident laws eq.1 eq.1
  -- Reflexivity proofs of related realizers are related at the identity type.
  have proofs : ∀ {x y : Tm Head n}, ValidEqN M Γ a x A → ValidEqN M Γ a y A →
      ∀ {m r : Nat} {ξ : World M.reading m} {σ σ' : Sub Head n m} {Δ : Ctx Head r}
        {ς ς' : Sub Head n r}, EqSubstN M Γ ξ σ σ' Δ ς ς' → ∀ {P : NPack M m},
        DenN M ξ (Presentation.subst σ (.id A a a)) P →
          P.Related (Presentation.subst σ (.refl x)) (Presentation.subst σ' (.refl y)) Δ
            (Presentation.subst ς (.id A a a)) (Presentation.subst ς (.refl x))
            (Presentation.subst ς' (.refl y)) := by
    intro x y eqX eqY m r ξ σ σ' Δ ς ς' e P den
    obtain ⟨R, denA, -, -⟩ := eq.1.1 e
    obtain ⟨_, -, -, types⟩ := validId e
    refine ⟨ValueSide.DenS.id_rel laws.value den _ _, ?_⟩
    rw [DenN.id_diag laws den]
    obtain ⟨hax, rax⟩ := eqX.2.2 e denA
    obtain ⟨hay, ray⟩ := eqY.2.2 e denA
    obtain ⟨hx, rx⟩ := eqX.2.1.2 e denA
    rw [← ValueSide.DenS.real_eq_of_rel laws.value denA
      (ValueSide.DenS.trans laws.value denA hax (ValueSide.DenS.symm laws.value denA hx))] at rx
    have xy : (R.real (Presentation.subst σ a)).rel Δ (Presentation.subst ς A)
        (Presentation.subst ς x) (Presentation.subst ς' y) :=
      (R.real _).trans ((R.real _).trans rx ((R.real _).symm rax)) ray
    have ax := (R.real _).trans rax ((R.real _).symm rx)
    obtain ⟨tx, ty⟩ := (R.real _).typed xy
    -- The realizer instance of the identity type is the identity of the point.
    have typeId := types.left
    have eAX : Equal M.side.R Δ (Presentation.subst ς a) (Presentation.subst ς x)
        (Presentation.subst ς A) := (R.real _).equal ax
    obtain ⟨v, hv, tId⟩ := typeId
    obtain ⟨uA, tA, huA, -, -, -⟩ := Typed.generation tId
    have change : TypeEq M.side.R Δ (.id (Presentation.subst ς A) (Presentation.subst ς x)
        (Presentation.subst ς x)) (Presentation.subst ς (.id A a a)) :=
      ⟨uA, huA, .idCong (.refl tA) huA eAX.symm eAX.symm⟩
    have h := ident_refl (T := M.side) trivial ⟨uA, huA, .idForm tA huA tx tx⟩ tx ty
      ((R.real _).escape xy)
    exact (ECand.conv _ e.formed change h)
  refine ⟨⟨validId, fun {_ _ _ _ _ _ _ _} e {_} den => proofs (ValidEqN.refl eq.1)
      (ValidEqN.refl eq.1) e den⟩,
    ⟨validId, fun {_ _ _ _ _ _ _ _} e {_} den => proofs eq eq e den⟩,
    fun {_ _ _ _ _ _ _ _} e {_} den => proofs (ValidEqN.refl eq.1) eq e den⟩

/-- Reflexivity proves the identity of a valid term with itself. -/
theorem ValidTmN.refl {n : Nat} {Γ : Ctx Head n} {a A : Tm Head n}
    (valid : ValidTmN M Γ a A) : ValidTmN M Γ (.refl a) (.id A a a) :=
  (ValidEqN.reflCong laws (ValidEqN.refl valid)).1

end Laws

end Conversion
end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
