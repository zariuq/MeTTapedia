import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Conversion.Functions

/-!
# Dependent pairs in the conversion model

A dependent pair type denotes, at a world, the pairs whose first projections
are valid values of its domain related to each other and whose second
projections are related at its codomain instantiated at the first projection.
A pair with a valid first projection is realized, at a realizer type reducing
to `Σ D C`, by the terms reaching weak-head normal pairs, related by the generic
equality, whose projections, after every renaming into a formed context,
realize the projections of the pair (`PiPack.pairReal_rel_sigma`).

**The generic equality comes from the projections.** Two terms reaching
weak-head normal pairs are related at `Σ D C` when their projections are
(`convTm_sigma_of_proj`): the projections reduce, typed, to the projections of
the normal forms, which the generic equality relates since it respects typed
reduction; the normal forms are then related by extensionality, and the terms
by expansion.

**Pairs and projections.** A pair of realizers realizes a pair when its
components realize the components: its projections reduce, typed, to the
components, and the projections of the value are related to its components, so
they have the same realizers (`DenN.sigma_pair_real`). The projections of
related realizers of a pair realize the projections of the pair
(`DenN.sigma_fst_real`, `DenN.sigma_snd_real`).

From these: validity of pairing and of the projections, their congruences, β
for both projections and η.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Impredicative
namespace Conversion

open Normalization hiding World
open UniverseLevel (LevelOrder)
open Consistency (World Morph)

variable {Head L : Type} [LevelOrder L]

/-! ## Pairs on the realizer side -/

section Realizers

variable {T : RealizerSide Head L}

/-- **The generic equality at a dependent pair type from the projections**: two
terms reaching weak-head normal pairs are related when their projections are. -/
theorem convTm_sigma_of_proj {m : Nat} {Δ : Ctx Head m} {X t t' D : Tm Head m}
    {C : Tm Head (m + 1)} (hX : RedTy T.R T.roles Δ X (.sigma D C)) (pn : PairNf T Δ X t)
    (pn' : PairNf T Δ X t') (first : T.E.convTm Δ (.fst t) (.fst t') D)
    (second : T.E.convTm Δ (.snd t) (.snd t') (Presentation.inst0 (.fst t) C)) :
    T.E.convTm Δ t t' X := by
  obtain ⟨w, r, pw⟩ := pn
  obtain ⟨w', r', pw'⟩ := pn'
  have e := hX.typeEq
  have r₁ := r.conv e
  have r₁' := r'.conv e
  obtain ⟨typeD, v, hv, tC⟩ := IsType.sigma_parts hX.targetType
  have f := r₁.fst
  have f' := r₁'.fst
  have eFst : Equal T.R Δ (.fst t) (.fst t') D := T.laws.convTm_sound first
  have change : TypeEq T.R Δ (Presentation.inst0 (.fst t') C) (Presentation.inst0 (.fst t) C) :=
    TypeEq.of_instantiateEq tC hv f'.source eFst.symm
  have s₁ := RedTm.snd tC hv r₁
  have s₁' := (RedTm.snd tC hv r₁').conv change
  have toNormal : TypeEq T.R Δ (Presentation.inst0 (.fst t) C) (Presentation.inst0 (.fst w) C) :=
    TypeEq.of_instantiateEq tC hv f.source f.equal
  have eta := T.laws.convTm_etaSigma typeD ⟨v, hv, tC⟩ r₁.target pw r₁'.target pw'
    (T.reduce f f' first) (T.laws.convTm_conv (T.reduce s₁ s₁' second) toNormal)
  exact T.laws.convTm_conv (T.laws.convTm_expand r₁ r₁' eta) e.symm

/-- **Pairs of related components are related pairs**: at a dependent pair type
`Σ D C` of a formed context, `sigmaOver X Y` relates two pairs whose first
components are related by `X` at `D` and whose second components are related by
`Y` at `C` instantiated at the first component. -/
theorem ECand.sigmaOver_pair (X Y : ECand T) {m : Nat} {Δ : Ctx Head m} {D : Tm Head m}
    {C : Tm Head (m + 1)} (formed : CtxFormed T.R Δ) (typeSigma : IsType T.R Δ (.sigma D C))
    {u u' v v' : Tm Head m} (hu : X.rel Δ D u u')
    (hv : Y.rel Δ (Presentation.inst0 u C) v v') :
    (ECand.sigmaOver X Y).rel Δ (.sigma D C) (.pair u v) (.pair u' v') := by
  obtain ⟨w, hw, tS⟩ := typeSigma
  obtain ⟨-, vv, hvv, tC⟩ := IsType.sigma_parts ⟨w, hw, tS⟩
  obtain ⟨tu, tu'⟩ := X.typed hu
  obtain ⟨tv, tv'⟩ := Y.typed hv
  have eCu : TypeEq T.R Δ (Presentation.inst0 u C) (Presentation.inst0 u' C) :=
    TypeEq.of_instantiateEq tC hvv tu (X.equal hu)
  have tPair : Typed T.R Δ (.pair u v) (.sigma D C) := .pairIntro tS hw tu tv
  have tPair' : Typed T.R Δ (.pair u' v') (.sigma D C) :=
    .pairIntro tS hw tu' (Typed.convType tv' eCu)
  have hX : RedTy T.R T.roles Δ (.sigma D C) (.sigma D C) := RedTy.refl ⟨w, hw, tS⟩
  -- The projections, after every renaming into a formed context.
  have proj : ProjClause X Y Δ D C (.pair u v) (.pair u' v') := by
    intro k Θ ρ world
    have tSρ : Typed T.R Θ (.sigma (Presentation.rename ρ D) (Presentation.rename (liftRen ρ) C))
        (.head w) := Typed.rename tS world.1
    have tCρ := Typed.rename tC (CtxRen.snoc world.1 D)
    have tuρ := Typed.rename tu world.1
    have tuρ' := Typed.rename tu' world.1
    have tvρ : Typed T.R Θ (Presentation.rename ρ v)
        (Presentation.inst0 (Presentation.rename ρ u) (Presentation.rename (liftRen ρ) C)) := by
      rw [← rename_inst0]
      exact Typed.rename tv world.1
    have tvρ' : Typed T.R Θ (Presentation.rename ρ v')
        (Presentation.inst0 (Presentation.rename ρ u') (Presentation.rename (liftRen ρ) C)) := by
      rw [← rename_inst0]
      exact Typed.rename (Typed.convType tv' eCu) world.1
    have huρ := X.rename world.1 world.2 hu
    have hvρ := Y.rename world.1 world.2 hv
    rw [rename_inst0] at hvρ
    have fstL := RedTm.fstPair (roles := T.roles) tSρ hw tuρ tvρ
    have fstR := RedTm.fstPair (roles := T.roles) tSρ hw tuρ' tvρ'
    have sndL := RedTm.sndPair (roles := T.roles) tSρ hw tCρ hvv tuρ tvρ
    have sndR := RedTm.sndPair (roles := T.roles) tSρ hw tCρ hvv tuρ' tvρ'
    -- The codomains at the first projections of the two pairs are equal.
    have eFst : Equal T.R Θ (.fst (.pair (Presentation.rename ρ u) (Presentation.rename ρ v)))
        (.fst (.pair (Presentation.rename ρ u') (Presentation.rename ρ v')))
        (Presentation.rename ρ D) :=
      .trans fstL.equal (.trans (X.equal huρ) fstR.equal.symm)
    have change : TypeEq T.R Θ
        (Presentation.inst0 (.fst (.pair (Presentation.rename ρ u') (Presentation.rename ρ v')))
          (Presentation.rename (liftRen ρ) C))
        (Presentation.inst0 (.fst (.pair (Presentation.rename ρ u) (Presentation.rename ρ v)))
          (Presentation.rename (liftRen ρ) C)) :=
      TypeEq.of_instantiateEq tCρ hvv fstR.source eFst.symm
    have toFst : TypeEq T.R Θ
        (Presentation.inst0 (Presentation.rename ρ u) (Presentation.rename (liftRen ρ) C))
        (Presentation.inst0 (.fst (.pair (Presentation.rename ρ u) (Presentation.rename ρ v)))
          (Presentation.rename (liftRen ρ) C)) :=
      TypeEq.of_instantiateEq tCρ hvv tuρ fstL.equal.symm
    exact ⟨X.expand fstL fstR huρ,
      Y.expand sndL (sndR.conv change) (Y.conv world.2 toFst hvρ)⟩
  refine (ECand.sigmaOver_rel_sigma hX).mpr ⟨⟨_, .refl tPair, .inl ⟨_, _, rfl⟩⟩,
    ⟨_, .refl tPair', .inl ⟨_, _, rfl⟩⟩, ?_, proj⟩
  obtain ⟨p₁, p₂⟩ := proj ⟨CtxRen.id Δ, formed⟩
  simp only [rename_id, liftRen_id] at p₁ p₂
  exact convTm_sigma_of_proj hX ⟨_, .refl tPair, .inl ⟨_, _, rfl⟩⟩
    ⟨_, .refl tPair', .inl ⟨_, _, rfl⟩⟩ (X.escape p₁) (Y.escape p₂)

end Realizers

variable {M : NModel Head L}

/-! ## Pairs in a world -/

namespace PiPack

variable {n : Nat} {ξ : World M.reading n} (Q : ValueSide.PiPack M.value ξ)

/-- **The realizers of a pair from the clause of its projections**: at a
realizer type reducing to `Σ D C` of a formed context, two terms reaching
weak-head normal pairs are related by the realizers of a pair with a valid first
projection when their projections satisfy the clause. -/
theorem pairReal_of_clause {p : Tm Head n} (hp : (Q.dom (Morph.id ξ)).Val (.fst p)) {m : Nat}
    {Δ : Ctx Head m} {X t t' D : Tm Head m} {C : Tm Head (m + 1)}
    (hX : RedTy M.side.R M.side.roles Δ X (.sigma D C)) (formed : CtxFormed M.side.R Δ)
    (pn : PairNf M.side Δ X t) (pn' : PairNf M.side Δ X t')
    (proj : ProjClause ((Q.dom (Morph.id ξ)).real (.fst p)) ((Q.cod (Morph.id ξ) hp).real (.snd p))
      Δ D C t t') :
    (Q.pairReal p).rel Δ X t t' := by
  refine (PiPack.pairReal_rel_sigma Q p hp hX).mpr ⟨pn, pn', ?_, proj⟩
  obtain ⟨p₁, p₂⟩ := proj ⟨CtxRen.id Δ, formed⟩
  simp only [rename_id, liftRen_id] at p₁ p₂
  exact convTm_sigma_of_proj hX pn pn' (ECand.escape _ p₁) (ECand.escape _ p₂)

end PiPack

section Laws

variable (laws : M.Laws)
include laws

/-- A pair of realizers realizes a pair at a dependent pair type when its
components realize the components: a valid first component, and a second
component valid at the codomain instantiated at the first. -/
theorem DenN.sigma_pair_real {n : Nat} {ξ : World M.reading n} {A : Tm Head n}
    {B : Tm Head (n + 1)} {P : NPack M n} (den : DenN M ξ (.sigma A B) P) {a b : Tm Head n}
    {m : Nat} {Δ : Ctx Head m} (formed : CtxFormed M.side.R Δ) {D : Tm Head m}
    {C : Tm Head (m + 1)} (typeSigma : IsType M.side.R Δ (.sigma D C)) {u u' v v' : Tm Head m}
    (ha : ∀ {PA : NPack M n}, DenN M ξ A PA → PA.Val a ∧ (PA.real a).rel Δ D u u')
    (hb : ∀ {PB : NPack M n}, DenN M ξ (Presentation.inst0 a B) PB →
      PB.Val b ∧ (PB.real b).rel Δ (Presentation.inst0 u C) v v') :
    (P.real (.pair a b)).rel Δ (.sigma D C) (.pair u v) (.pair u' v') := by
  obtain ⟨l, Q, rfl, interprets⟩ := ValueSide.DenS.sigma_inv laws.value den
  have domI : DenN M ξ A (Q.dom (Morph.id ξ)) := ⟨l, interprets.dom_id⟩
  obtain ⟨va, hu⟩ := ha domI
  have codI : DenN M ξ (Presentation.inst0 a B) (Q.cod (Morph.id ξ) va) :=
    ⟨l, interprets.cod_id va⟩
  obtain ⟨vb, hv⟩ := hb codI
  have domE := ValueSide.DenS.expansive laws.value domI
  have fst : WhRed M.rules M.roles (.fst (.pair a b)) a := .single (.fstPair a b)
  have fv : (Q.dom (Morph.id ξ)).Val (.fst (.pair a b)) := domE.left fst (domE.right fst va)
  have frel : (Q.dom (Morph.id ξ)).rel (.fst (.pair a b)) a := domE.left fst va
  have srel : (Q.cod (Morph.id ξ) va).rel (.snd (.pair a b)) b :=
    (ValueSide.DenS.expansive laws.value codI).left (.single (.sndPair a b)) vb
  have related := ECand.sigmaOver_pair ((Q.dom (Morph.id ξ)).real a)
    ((Q.cod (Morph.id ξ) va).real b) formed typeSigma hu hv
  have hX : RedTy M.side.R M.side.roles Δ (.sigma D C) (.sigma D C) := RedTy.refl typeSigma
  obtain ⟨pn, pn', -, proj⟩ := (ECand.sigmaOver_rel_sigma hX).mp related
  refine PiPack.pairReal_of_clause Q fv hX formed pn pn' ?_
  rw [interprets.codRespect (Morph.id ξ) fv va frel,
    ValueSide.DenS.real_eq_of_rel laws.value domI frel,
    ValueSide.DenS.real_eq_of_rel laws.value codI srel]
  exact proj

/-- The projections of related realizers of a related pair realize the
projections of the pair: the first at the domain, the second at the codomain
instantiated at the first. -/
theorem DenN.sigma_proj_real {n : Nat} {ξ : World M.reading n} {A : Tm Head n}
    {B : Tm Head (n + 1)} {P : NPack M n} (den : DenN M ξ (.sigma A B) P) {p : Tm Head n}
    (hp : P.Val p) {m : Nat} {Δ : Ctx Head m} (formed : CtxFormed M.side.R Δ)
    {X t t' D : Tm Head m} {C : Tm Head (m + 1)}
    (hX : RedTy M.side.R M.side.roles Δ X (.sigma D C)) (real : (P.real p).rel Δ X t t') :
    (∀ {PA : NPack M n}, DenN M ξ A PA → (PA.real (.fst p)).rel Δ D (.fst t) (.fst t')) ∧
      ∀ {PB : NPack M n}, DenN M ξ (Presentation.inst0 (.fst p) B) PB →
        (PB.real (.snd p)).rel Δ (Presentation.inst0 (.fst t) C) (.snd t) (.snd t') := by
  obtain ⟨l, Q, rfl, interprets⟩ := ValueSide.DenS.sigma_inv laws.value den
  obtain ⟨vp, -, -⟩ := hp
  obtain ⟨-, -, -, proj⟩ := (PiPack.pairReal_rel_sigma Q p vp hX).mp real
  obtain ⟨p₁, p₂⟩ := proj ⟨CtxRen.id Δ, formed⟩
  simp only [rename_id, liftRen_id] at p₁ p₂
  refine ⟨fun {PA} denA => ?_, fun {PB} denB => ?_⟩
  · rw [ValueSide.DenS.deterministic laws.value denA ⟨l, interprets.dom_id⟩]
    exact p₁
  · rw [ValueSide.DenS.deterministic laws.value denB ⟨l, interprets.cod_id vp⟩]
    exact p₂

end Laws

/-! ## Pairing and projections -/

section Rules

variable (laws : M.Laws)
include laws

/-- Pairing. -/
theorem ValidTmN.pair {n : Nat} {Γ : Ctx Head n} {A a b : Tm Head n} {B : Tm Head (n + 1)}
    (validSigma : ValidTyN M Γ (.sigma A B)) (validA : ValidTmN M Γ a A)
    (validB : ValidTmN M Γ b (Presentation.inst0 a B)) :
    ValidTmN M Γ (.pair a b) (.sigma A B) := by
  refine ⟨validSigma, fun {_ _ ξ σ σ' Δ ς ς'} e {P} den => ⟨?_, ?_⟩⟩
  · refine ValueSide.DenS.sigma_pair laws.value den (fun denA => (validA.2 e denA).1)
      (fun {PB} denB => ?_)
    rw [← subst_inst0] at denB
    exact (validB.2 e denB).1
  · obtain ⟨_, _, _, types⟩ := validSigma e
    refine DenN.sigma_pair_real laws den e.formed types.left
      (fun denA => ⟨ValueSide.DenS.refl_left laws.value denA (validA.2 e denA).1,
        (validA.2 e denA).2⟩) (fun {PB} denB => ?_)
    rw [← subst_inst0] at denB
    obtain ⟨rel, real⟩ := validB.2 e denB
    rw [subst_inst0] at real
    exact ⟨ValueSide.DenS.refl_left laws.value denB rel, real⟩

/-- First projection. -/
theorem ValidTmN.fst {n : Nat} {Γ : Ctx Head n} {p A : Tm Head n} {B : Tm Head (n + 1)}
    (valid : ValidTmN M Γ p (.sigma A B)) (validA : ValidTyN M Γ A) :
    ValidTmN M Γ (.fst p) A := by
  obtain ⟨validSigma, rel⟩ := valid
  refine ⟨validA, fun {_ _ ξ σ σ' Δ ς ς'} e {PA} den => ?_⟩
  obtain ⟨_, denS, _, types⟩ := validSigma e
  obtain ⟨h, real⟩ := rel e denS
  exact ⟨ValueSide.DenS.sigma_fst laws.value denS h den,
    (DenN.sigma_proj_real laws denS (ValueSide.DenS.refl_left laws.value denS h) e.formed
      (RedTy.refl types.left) real).1 den⟩

/-- Second projection. -/
theorem ValidTmN.snd {n : Nat} {Γ : Ctx Head n} {p A : Tm Head n} {B : Tm Head (n + 1)}
    (valid : ValidTmN M Γ p (.sigma A B)) (validA : ValidTyN M Γ A)
    (validB : ValidTyN M (.snoc Γ A) B) :
    ValidTmN M Γ (.snd p) (Presentation.inst0 (.fst p) B) := by
  have validInst : ValidTyN M Γ (Presentation.inst0 (.fst p) B) :=
    ValidTyN.inst0 validB (ValidTmN.fst laws valid validA)
  obtain ⟨validSigma, rel⟩ := valid
  refine ⟨validInst, fun {_ _ ξ σ σ' Δ ς ς'} e {PB} den => ?_⟩
  obtain ⟨_, denS, _, types⟩ := validSigma e
  obtain ⟨h, real⟩ := rel e denS
  rw [subst_inst0] at den
  rw [subst_inst0]
  exact ⟨ValueSide.DenS.sigma_snd laws.value denS h den,
    (DenN.sigma_proj_real laws denS (ValueSide.DenS.refl_left laws.value denS h) e.formed
      (RedTy.refl types.left) real).2 den⟩

/-! ## Congruences -/

/-- The codomain of a dependent pair type, instantiated at arguments related
under related valuations, has one denotation, and its realizer instances are
typed-equal. -/
theorem sigma_codomain_move {n : Nat} {Γ : Ctx Head n} {A a a' : Tm Head n}
    {B : Tm Head (n + 1)} (validSigma : ValidTyN M Γ (.sigma A B)) (eqA : ValidEqN M Γ a a' A)
    {m r : Nat} {ξ : World M.reading m} {σ σ' : Sub Head n m} {Δ : Ctx Head r}
    {ς ς' : Sub Head n r} (e : EqSubstN M Γ ξ σ σ' Δ ς ς') :
    (∀ {P : NPack M m}, DenN M ξ (Presentation.subst σ (Presentation.inst0 a' B)) P ↔
      DenN M ξ (Presentation.subst σ (Presentation.inst0 a B)) P) ∧
      TypeEq M.side.R Δ (Presentation.subst ς (Presentation.inst0 a B))
        (Presentation.subst ς (Presentation.inst0 a' B)) := by
  obtain ⟨validLeft, validRight, relAA'⟩ := eqA
  obtain ⟨_, denS, _, types⟩ := validSigma e
  refine ⟨fun {P} => ⟨fun den => ?_, fun den => ?_⟩, ?_⟩
  · rw [subst_inst0] at den ⊢
    exact ValueSide.DenS.sigma_cod laws.value denS
      (fun denA => ValueSide.DenS.trans laws.value denA (validRight.2 e denA).1
        (ValueSide.DenS.symm laws.value denA (relAA' e denA).1)) den
  · rw [subst_inst0] at den ⊢
    exact ValueSide.DenS.sigma_cod laws.value denS
      (fun denA => ValueSide.DenS.trans laws.value denA (relAA' e denA).1
        (ValueSide.DenS.symm laws.value denA (validRight.2 e denA).1)) den
  · obtain ⟨PA, denA, -, -⟩ := validLeft.1 e
    have raa := (relAA' e denA).2
    have ra' := (validRight.2 e denA).2
    rw [← ValueSide.DenS.real_eq_of_rel laws.value denA
      (ValueSide.DenS.trans laws.value denA (relAA' e denA).1
        (ValueSide.DenS.symm laws.value denA (validRight.2 e denA).1))] at ra'
    have eaa := (PA.real _).equal ((PA.real _).trans raa ((PA.real _).symm ra'))
    obtain ⟨-, v, hv, tC⟩ := IsType.sigma_parts types.left
    rw [subst_inst0, subst_inst0]
    exact TypeEq.of_instantiateEq tC hv ((PA.real _).typed raa).1 eaa

/-- Congruence of pairing. -/
theorem ValidEqN.pair {n : Nat} {Γ : Ctx Head n} {A a a' b b' : Tm Head n} {B : Tm Head (n + 1)}
    (validSigma : ValidTyN M Γ (.sigma A B)) (validB : ValidTyN M (.snoc Γ A) B)
    (eqA : ValidEqN M Γ a a' A) (eqB : ValidEqN M Γ b b' (Presentation.inst0 a B)) :
    ValidEqN M Γ (.pair a b) (.pair a' b') (.sigma A B) := by
  obtain ⟨validB₁, validB₂', relBB'⟩ := eqB
  have validB₂ : ValidTmN M Γ b' (Presentation.inst0 a' B) := by
    refine ⟨ValidTyN.inst0 validB eqA.2.1, fun {_ _ _ _ _ _ _ _} e {_} den => ?_⟩
    obtain ⟨move, typeEq⟩ := sigma_codomain_move laws validSigma eqA e
    obtain ⟨rel, real⟩ := validB₂'.2 e (move.mp den)
    exact ⟨rel, (ECand.conv _ e.formed typeEq real)⟩
  refine ⟨ValidTmN.pair laws validSigma eqA.1 validB₁,
    ValidTmN.pair laws validSigma eqA.2.1 validB₂, fun {_ _ ξ σ σ' Δ ς ς'} e {P} den => ?_⟩
  obtain ⟨_, _, relAA'⟩ := eqA
  refine ⟨ValueSide.DenS.sigma_pair laws.value den (fun denA => (relAA' e denA).1)
    (fun {PB} denB => ?_), ?_⟩
  · rw [← subst_inst0] at denB
    exact (relBB' e denB).1
  · obtain ⟨_, _, _, types⟩ := validSigma e
    refine DenN.sigma_pair_real laws den e.formed types.left
      (fun denA => ⟨ValueSide.DenS.refl_left laws.value denA (relAA' e denA).1,
        (relAA' e denA).2⟩) (fun {PB} denB => ?_)
    rw [← subst_inst0] at denB
    obtain ⟨rel, real⟩ := relBB' e denB
    rw [subst_inst0] at real
    exact ⟨ValueSide.DenS.refl_left laws.value denB rel, real⟩

/-- Congruence of the first projection. -/
theorem ValidEqN.fst {n : Nat} {Γ : Ctx Head n} {p q A : Tm Head n} {B : Tm Head (n + 1)}
    (eq : ValidEqN M Γ p q (.sigma A B)) (validA : ValidTyN M Γ A) :
    ValidEqN M Γ (.fst p) (.fst q) A := by
  obtain ⟨validP, validQ, rel⟩ := eq
  refine ⟨ValidTmN.fst laws validP validA, ValidTmN.fst laws validQ validA,
    fun {_ _ ξ σ σ' Δ ς ς'} e {PA} den => ?_⟩
  obtain ⟨_, denS, _, types⟩ := validP.1 e
  obtain ⟨h, real⟩ := rel e denS
  exact ⟨ValueSide.DenS.sigma_fst laws.value denS h den,
    (DenN.sigma_proj_real laws denS (ValueSide.DenS.refl_left laws.value denS h) e.formed
      (RedTy.refl types.left) real).1 den⟩

/-- Congruence of the second projection. -/
theorem ValidEqN.snd {n : Nat} {Γ : Ctx Head n} {p q A : Tm Head n} {B : Tm Head (n + 1)}
    (eq : ValidEqN M Γ p q (.sigma A B)) (validA : ValidTyN M Γ A)
    (validB : ValidTyN M (.snoc Γ A) B) :
    ValidEqN M Γ (.snd p) (.snd q) (Presentation.inst0 (.fst p) B) := by
  have eqFst := ValidEqN.fst laws eq validA
  obtain ⟨validP, validQ, rel⟩ := eq
  have validSndP := ValidTmN.snd laws validP validA validB
  have validSndQ := ValidTmN.snd laws validQ validA validB
  have validSigma : ValidTyN M Γ (.sigma A B) := validP.1
  refine ⟨validSndP, ⟨validSndP.1, fun {_ _ _ _ _ _ _ _} e {_} den => ?_⟩,
    fun {_ _ ξ σ σ' Δ ς ς'} e {PB} den => ?_⟩
  · obtain ⟨move, typeEq⟩ := sigma_codomain_move laws validSigma eqFst e
    obtain ⟨rel', real⟩ := validSndQ.2 e (move.mpr den)
    exact ⟨rel', (ECand.conv _ e.formed typeEq.symm real)⟩
  · obtain ⟨_, denS, _, types⟩ := validP.1 e
    obtain ⟨h, real⟩ := rel e denS
    rw [subst_inst0] at den
    rw [subst_inst0]
    exact ⟨ValueSide.DenS.sigma_snd laws.value denS h den,
      (DenN.sigma_proj_real laws denS (ValueSide.DenS.refl_left laws.value denS h) e.formed
        (RedTy.refl types.left) real).2 den⟩

/-! ## β and η -/

omit laws in
/-- The reductions of the realizer instances of `fst (pair a b)` and
`snd (pair a b)`, at the first instance of the type, under related valuations. -/
theorem pair_steps {n : Nat} {Γ : Ctx Head n} {A a b : Tm Head n} {B : Tm Head (n + 1)}
    (validSigma : ValidTyN M Γ (.sigma A B)) (validA : ValidTmN M Γ a A)
    (validB : ValidTmN M Γ b (Presentation.inst0 a B)) {m r : Nat} {ξ : World M.reading m}
    {σ σ' : Sub Head n m} {Δ : Ctx Head r} {ς ς' : Sub Head n r}
    (e : EqSubstN M Γ ξ σ σ' Δ ς ς') :
    (RedTm M.side.R M.side.roles Δ (Presentation.subst ς (.fst (.pair a b)))
        (Presentation.subst ς a) (Presentation.subst ς A) ∧
      RedTm M.side.R M.side.roles Δ (Presentation.subst ς' (.fst (.pair a b)))
        (Presentation.subst ς' a) (Presentation.subst ς A)) ∧
    (RedTm M.side.R M.side.roles Δ (Presentation.subst ς (.snd (.pair a b)))
        (Presentation.subst ς b) (Presentation.subst ς (Presentation.inst0 a B)) ∧
      RedTm M.side.R M.side.roles Δ (Presentation.subst ς' (.snd (.pair a b)))
        (Presentation.subst ς' b) (Presentation.subst ς (Presentation.inst0 a B))) := by
  obtain ⟨_, _, _, types⟩ := validSigma e
  obtain ⟨w, hw, tS⟩ := types.left
  obtain ⟨-, v, hv, tC⟩ := IsType.sigma_parts ⟨w, hw, tS⟩
  obtain ⟨PA, denA, -, -⟩ := validA.1 e
  have ra := (validA.2 e denA).2
  obtain ⟨ta, ta'⟩ := (PA.real _).typed ra
  obtain ⟨PB, denB, -, -⟩ := validB.1 e
  have rb := (validB.2 e denB).2
  obtain ⟨tb, tb'⟩ := (PB.real _).typed rb
  rw [subst_inst0] at tb tb'
  have eC : TypeEq M.side.R Δ
      (Presentation.inst0 (Presentation.subst ς a) (Presentation.subst (liftSub ς) B))
      (Presentation.inst0 (Presentation.subst ς' a) (Presentation.subst (liftSub ς) B)) :=
    TypeEq.of_instantiateEq tC hv ta ((PA.real _).equal ra)
  have tb'' := Typed.convType tb' eC
  have fstL := RedTm.fstPair (roles := M.side.roles) tS hw ta tb
  have fstR := RedTm.fstPair (roles := M.side.roles) tS hw ta' tb''
  have sndL := RedTm.sndPair (roles := M.side.roles) tS hw tC hv ta tb
  have sndR := RedTm.sndPair (roles := M.side.roles) tS hw tC hv ta' tb''
  -- The codomain at the first projection of the pair is the codomain at the component.
  have toA : TypeEq M.side.R Δ
      (Presentation.inst0 (.fst (.pair (Presentation.subst ς a) (Presentation.subst ς b)))
        (Presentation.subst (liftSub ς) B))
      (Presentation.inst0 (Presentation.subst ς a) (Presentation.subst (liftSub ς) B)) :=
    TypeEq.of_instantiateEq tC hv fstL.source fstL.equal
  have toA' : TypeEq M.side.R Δ
      (Presentation.inst0 (.fst (.pair (Presentation.subst ς' a) (Presentation.subst ς' b)))
        (Presentation.subst (liftSub ς) B))
      (Presentation.inst0 (Presentation.subst ς a) (Presentation.subst (liftSub ς) B)) :=
    TypeEq.of_instantiateEq tC hv fstR.source (.trans fstR.equal ((PA.real _).equal ra).symm)
  rw [subst_inst0]
  exact ⟨⟨fstL, fstR⟩, ⟨sndL.conv toA, sndR.conv toA'⟩⟩

/-- β for the first projection. -/
theorem ValidEqN.betaFst {n : Nat} {Γ : Ctx Head n} {a b A : Tm Head n} {B : Tm Head (n + 1)}
    (validSigma : ValidTyN M Γ (.sigma A B)) (validA : ValidTmN M Γ a A)
    (validB : ValidTmN M Γ b (Presentation.inst0 a B)) :
    ValidEqN M Γ (.fst (.pair a b)) a A := by
  obtain ⟨validTyA, rel⟩ := validA
  refine ⟨⟨validTyA, fun {_ _ ξ σ σ' Δ ς ς'} e {P} den => ?_⟩, ⟨validTyA, rel⟩,
    fun {_ _ ξ σ σ' Δ ς ς'} e {P} den => ?_⟩
  · obtain ⟨h, real⟩ := rel e den
    have expansive := ValueSide.DenS.expansive laws.value den
    have related : P.rel (Presentation.subst σ (.fst (.pair a b))) (Presentation.subst σ a) :=
      expansive.left (.single (.fstPair _ _)) (ValueSide.DenS.refl_left laws.value den h)
    refine ⟨expansive.left (.single (.fstPair _ _)) (expansive.right (.single (.fstPair _ _)) h),
      ?_⟩
    rw [ValueSide.DenS.real_eq_of_rel laws.value den related]
    obtain ⟨⟨fstL, fstR⟩, -⟩ := pair_steps validSigma ⟨validTyA, rel⟩ validB e
    exact (P.real _).expand fstL fstR real
  · obtain ⟨h, real⟩ := rel e den
    have expansive := ValueSide.DenS.expansive laws.value den
    have related : P.rel (Presentation.subst σ (.fst (.pair a b))) (Presentation.subst σ a) :=
      expansive.left (.single (.fstPair _ _)) (ValueSide.DenS.refl_left laws.value den h)
    refine ⟨expansive.left (.single (.fstPair _ _)) h, ?_⟩
    rw [ValueSide.DenS.real_eq_of_rel laws.value den related]
    obtain ⟨⟨fstL, -⟩, -⟩ := pair_steps validSigma ⟨validTyA, rel⟩ validB e
    exact (P.real _).expand_left fstL real

/-- β for the second projection. -/
theorem ValidEqN.betaSnd {n : Nat} {Γ : Ctx Head n} {a b A : Tm Head n} {B : Tm Head (n + 1)}
    (validSigma : ValidTyN M Γ (.sigma A B)) (validA : ValidTmN M Γ a A)
    (validB : ValidTmN M Γ b (Presentation.inst0 a B)) :
    ValidEqN M Γ (.snd (.pair a b)) b (Presentation.inst0 a B) := by
  obtain ⟨validTyB, rel⟩ := validB
  refine ⟨⟨validTyB, fun {_ _ ξ σ σ' Δ ς ς'} e {P} den => ?_⟩, ⟨validTyB, rel⟩,
    fun {_ _ ξ σ σ' Δ ς ς'} e {P} den => ?_⟩
  · obtain ⟨h, real⟩ := rel e den
    have expansive := ValueSide.DenS.expansive laws.value den
    have related : P.rel (Presentation.subst σ (.snd (.pair a b))) (Presentation.subst σ b) :=
      expansive.left (.single (.sndPair _ _)) (ValueSide.DenS.refl_left laws.value den h)
    refine ⟨expansive.left (.single (.sndPair _ _)) (expansive.right (.single (.sndPair _ _)) h),
      ?_⟩
    rw [ValueSide.DenS.real_eq_of_rel laws.value den related]
    obtain ⟨-, ⟨sndL, sndR⟩⟩ := pair_steps validSigma validA ⟨validTyB, rel⟩ e
    exact (P.real _).expand sndL sndR real
  · obtain ⟨h, real⟩ := rel e den
    have expansive := ValueSide.DenS.expansive laws.value den
    have related : P.rel (Presentation.subst σ (.snd (.pair a b))) (Presentation.subst σ b) :=
      expansive.left (.single (.sndPair _ _)) (ValueSide.DenS.refl_left laws.value den h)
    refine ⟨expansive.left (.single (.sndPair _ _)) h, ?_⟩
    rw [ValueSide.DenS.real_eq_of_rel laws.value den related]
    obtain ⟨-, ⟨sndL, -⟩⟩ := pair_steps validSigma validA ⟨validTyB, rel⟩ e
    exact (P.real _).expand_left sndL real

/-- η for pairs: pairs are equal when their projections are. -/
theorem ValidEqN.etaSigma {n : Nat} {Γ : Ctx Head n} {p q A : Tm Head n} {B : Tm Head (n + 1)}
    (validP : ValidTmN M Γ p (.sigma A B)) (validQ : ValidTmN M Γ q (.sigma A B))
    (eqFst : ValidEqN M Γ (.fst p) (.fst q) A)
    (eqSnd : ValidEqN M Γ (.snd p) (.snd q) (Presentation.inst0 (.fst p) B)) :
    ValidEqN M Γ p q (.sigma A B) := by
  obtain ⟨_, _, relFst⟩ := eqFst
  obtain ⟨_, _, relSnd⟩ := eqSnd
  refine ⟨validP, validQ, fun {_ _ ξ σ σ' Δ ς ς'} e {P} den => ?_⟩
  obtain ⟨l, Q, rfl, interprets⟩ := ValueSide.DenS.sigma_inv laws.value den
  obtain ⟨vp, _, _⟩ := (validP.2 e den).1
  have domI : DenN M ξ (Presentation.subst σ A) (Q.dom (Morph.id ξ)) := ⟨l, interprets.dom_id⟩
  have denB : DenN M ξ (Presentation.subst σ (Presentation.inst0 (.fst p) B))
      (Q.cod (Morph.id ξ) vp) := by
    rw [subst_inst0]
    exact ⟨l, interprets.cod_id vp⟩
  refine ⟨⟨vp, (relFst e domI).1, (relSnd e denB).1⟩, ?_⟩
  obtain ⟨_, _, _, types⟩ := validP.1 e
  have hX := RedTy.refl (roles := M.side.roles) types.left
  obtain ⟨pnP, -, -, -⟩ := (PiPack.pairReal_rel_sigma Q _ vp hX).mp (validP.2 e den).2
  have relQ := (validQ.2 e den)
  obtain ⟨vq, _, _⟩ := relQ.1
  obtain ⟨-, pnQ, -, -⟩ := (PiPack.pairReal_rel_sigma Q _ vq hX).mp relQ.2
  refine PiPack.pairReal_of_clause Q vp hX e.formed pnP pnQ ?_
  intro k Θ ρ world
  have e' := e.renameReal world.1 world.2
  have denA' : DenN M ξ (Presentation.subst σ A) (Q.dom (Morph.id ξ)) := domI
  have hFst := (relFst e' denA').2
  have hSnd := (relSnd e' denB).2
  rw [subst_inst0, inst0_subst_liftSub] at hSnd
  rw [inst0_rename_subst_liftSub]
  simp only [rename_subst]
  exact ⟨hFst, hSnd⟩

end Rules

end Conversion
end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
