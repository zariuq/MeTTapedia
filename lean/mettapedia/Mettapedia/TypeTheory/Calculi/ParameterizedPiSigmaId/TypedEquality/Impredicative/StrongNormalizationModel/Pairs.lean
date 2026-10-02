import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.StrongNormalizationModel.Functions

/-!
# Dependent pairs in model SN

A dependent pair type denotes, at a world, the pairs whose first projections
are valid values of its domain related to each other and whose second
projections are related at its codomain instantiated at the first projection.
A pair is realized by the strongly normalizing terms whose projections realize
the two projections (`PiPack.mem_pairReal`).

A projection of a pair weak-head reduces to the component, and the relation is
closed under weak-head expansion, so pairs are related as soon as their
components are. On the realizer side, a projection of a pair of realizers
realizes the component when the discarded component is strongly normalizing,
and the projection and the component are related values, so they have the same
realizers. At related first components the codomain has one denotation.

From these: validity of pairing and of the projections, their congruences, β
for both projections and η. The β-rules hold by weak-head expansion; their
realizer parts need the discarded component to have strongly normalizing
realizers, which its validity provides.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Impredicative
namespace ModelSN

open Normalization (WhRed WhStep)
open UniverseLevel (LevelOrder)
open Consistency (World Morph)
open StrongNormalization
open ValueSide

variable {Head L : Type} [LevelOrder L] {M : SNModel Head L}

section Laws

variable (laws : M.Laws)
include laws

/-! ## Pairs in a world -/

/-- Related pairs have first projections related at the domain. -/
theorem DenS.sigma_fst {n : Nat} {ξ : World M.reading n} {A : Tm Head n}
    {B : Tm Head (n + 1)} {P : Pack M.value n} (den : DenS M.value ξ (.sigma A B) P)
    {p q : Tm Head n} (h : P.rel p q) {PA : Pack M.value n} (denA : DenS M.value ξ A PA) :
    PA.rel (.fst p) (.fst q) :=
  ValueSide.DenS.sigma_fst laws.value den h denA

/-- The first projection of a realizer of a related pair realizes the first
projection of the pair. -/
theorem DenS.sigma_fst_real {n : Nat} {ξ : World M.reading n} {A : Tm Head n}
    {B : Tm Head (n + 1)} {P : Pack M.value n} (den : DenS M.value ξ (.sigma A B) P)
    {p q : Tm Head n} (h : P.rel p q) {r : Nat} {t : Tm Head r} (real : (P.real p).mem t)
    {PA : Pack M.value n} (denA : DenS M.value ξ A PA) : (PA.real (.fst p)).mem (.fst t) := by
  obtain ⟨l, Q, rfl, interprets⟩ := ValueSide.DenS.sigma_inv laws.value den
  obtain rfl := DenS.deterministic laws.value denA ⟨l, interprets.dom_id⟩
  obtain ⟨hp, _⟩ := h
  exact (((PiPack.mem_pairReal Q).mp real).2 hp).1

/-- Related pairs have second projections related at the codomain instantiated
at the first projection. -/
theorem DenS.sigma_snd {n : Nat} {ξ : World M.reading n} {A : Tm Head n}
    {B : Tm Head (n + 1)} {P : Pack M.value n} (den : DenS M.value ξ (.sigma A B) P)
    {p q : Tm Head n} (h : P.rel p q) {PB : Pack M.value n}
    (denB : DenS M.value ξ (Presentation.inst0 (.fst p) B) PB) : PB.rel (.snd p) (.snd q) :=
  ValueSide.DenS.sigma_snd laws.value den h denB

/-- The second projection of a realizer of a related pair realizes the second
projection of the pair, at the codomain instantiated at the first projection. -/
theorem DenS.sigma_snd_real {n : Nat} {ξ : World M.reading n} {A : Tm Head n}
    {B : Tm Head (n + 1)} {P : Pack M.value n} (den : DenS M.value ξ (.sigma A B) P)
    {p q : Tm Head n} (h : P.rel p q) {r : Nat} {t : Tm Head r} (real : (P.real p).mem t)
    {PB : Pack M.value n} (denB : DenS M.value ξ (Presentation.inst0 (.fst p) B) PB) :
    (PB.real (.snd p)).mem (.snd t) := by
  obtain ⟨l, Q, rfl, interprets⟩ := ValueSide.DenS.sigma_inv laws.value den
  obtain ⟨hp, _⟩ := h
  rw [DenS.deterministic laws.value denB ⟨l, interprets.cod_id hp⟩]
  exact (((PiPack.mem_pairReal Q).mp real).2 hp).2

/-- Pairs are related at a dependent pair type when their first components are
related at the domain and their second components are related at the codomain
instantiated at the first component. -/
theorem DenS.sigma_pair {n : Nat} {ξ : World M.reading n} {A : Tm Head n}
    {B : Tm Head (n + 1)} {P : Pack M.value n} (den : DenS M.value ξ (.sigma A B) P)
    {a a' b b' : Tm Head n} (haa' : ∀ {PA : Pack M.value n}, DenS M.value ξ A PA → PA.rel a a')
    (hb : ∀ {PB : Pack M.value n}, DenS M.value ξ (Presentation.inst0 a B) PB → PB.rel b b') :
    P.rel (.pair a b) (.pair a' b') :=
  ValueSide.DenS.sigma_pair laws.value den haa' hb

/-- A pair of realizers realizes a pair at a dependent pair type when its
components realize the components: a valid first component, and a second
component valid at the codomain instantiated at the first. -/
theorem DenS.sigma_pair_real {n : Nat} {ξ : World M.reading n} {A : Tm Head n}
    {B : Tm Head (n + 1)} {P : Pack M.value n} (den : DenS M.value ξ (.sigma A B) P)
    {a b : Tm Head n} {r : Nat} {u v : Tm Head r}
    (ha : ∀ {PA : Pack M.value n}, DenS M.value ξ A PA → PA.Val a ∧ (PA.real a).mem u)
    (hb : ∀ {PB : Pack M.value n}, DenS M.value ξ (Presentation.inst0 a B) PB →
      PB.Val b ∧ (PB.real b).mem v) :
    (P.real (.pair a b)).mem (.pair u v) := by
  obtain ⟨l, Q, rfl, interprets⟩ := ValueSide.DenS.sigma_inv laws.value den
  have domI : DenS M.value ξ A (Q.dom (Morph.id ξ)) := ⟨l, interprets.dom_id⟩
  obtain ⟨va, hu⟩ := ha domI
  have codI : DenS M.value ξ (Presentation.inst0 a B) (Q.cod (Morph.id ξ) va) :=
    ⟨l, interprets.cod_id va⟩
  obtain ⟨vb, hv⟩ := hb codI
  have su := (KCand.sn _) hu
  have sv := (KCand.sn _) hv
  refine (PiPack.mem_pairReal Q).mpr
    ⟨SN.pair (RootShape.spineHeaded M.realizers.shape) su sv, fun fv => ?_⟩
  have frel : (Q.dom (Morph.id ξ)).rel (.fst (.pair a b)) a :=
    (domI.expansive laws.value).left (.single (.fstPair a b)) va
  have srel : (Q.cod (Morph.id ξ) va).rel (.snd (.pair a b)) b :=
    (codI.expansive laws.value).left (.single (.sndPair a b)) vb
  rw [interprets.codRespect (Morph.id ξ) fv va frel, domI.real_eq_of_rel laws.value frel,
    codI.real_eq_of_rel laws.value srel]
  exact ⟨KCand.fst_pair M.realizers.shape _ sv hu, KCand.snd_pair M.realizers.shape _ su hv⟩

/-! ## Pairing and projections -/

/-- Pairing. -/
theorem ValidTmS.pair {n : Nat} {Γ : Ctx Head n} {A a b : Tm Head n} {B : Tm Head (n + 1)}
    (validSigma : ValidTyS M Γ (.sigma A B)) (validA : ValidTmS M Γ a A)
    (validB : ValidTmS M Γ b (Presentation.inst0 a B)) :
    ValidTmS M Γ (.pair a b) (.sigma A B) := by
  refine ⟨validSigma, fun {_ _ ξ σ σ' ς} e {P} den => ⟨?_, ?_⟩⟩
  · refine DenS.sigma_pair laws den (fun denA => (validA.2 e denA).1) (fun {PB} denB => ?_)
    rw [← subst_inst0] at denB
    exact (validB.2 e denB).1
  · refine DenS.sigma_pair_real laws den
      (fun denA => ⟨denA.refl_left laws.value (validA.2 e denA).1, (validA.2 e denA).2⟩)
      (fun {PB} denB => ?_)
    rw [← subst_inst0] at denB
    obtain ⟨rel, real⟩ := validB.2 e denB
    exact ⟨denB.refl_left laws.value rel, real⟩

/-- First projection. -/
theorem ValidTmS.fst {n : Nat} {Γ : Ctx Head n} {p A : Tm Head n} {B : Tm Head (n + 1)}
    (valid : ValidTmS M Γ p (.sigma A B)) (validA : ValidTyS M Γ A) :
    ValidTmS M Γ (.fst p) A := by
  obtain ⟨validSigma, rel⟩ := valid
  refine ⟨validA, fun {_ _ ξ σ σ' ς} e {PA} den => ?_⟩
  obtain ⟨_, denS, _, _⟩ := validSigma e
  obtain ⟨h, real⟩ := rel e denS
  exact ⟨DenS.sigma_fst laws denS h den, DenS.sigma_fst_real laws denS h real den⟩

/-- Second projection. -/
theorem ValidTmS.snd {n : Nat} {Γ : Ctx Head n} {p A : Tm Head n} {B : Tm Head (n + 1)}
    (valid : ValidTmS M Γ p (.sigma A B)) (validA : ValidTyS M Γ A)
    (validB : ValidTyS M (.snoc Γ A) B) :
    ValidTmS M Γ (.snd p) (Presentation.inst0 (.fst p) B) := by
  have validInst : ValidTyS M Γ (Presentation.inst0 (.fst p) B) :=
    ValidTyS.inst0 validB (ValidTmS.fst laws valid validA)
  obtain ⟨validSigma, rel⟩ := valid
  refine ⟨validInst, fun {_ _ ξ σ σ' ς} e {PB} den => ?_⟩
  obtain ⟨_, denS, _, _⟩ := validSigma e
  obtain ⟨h, real⟩ := rel e denS
  rw [subst_inst0] at den
  exact ⟨DenS.sigma_snd laws denS h den, DenS.sigma_snd_real laws denS h real den⟩

/-! ## Congruences -/

/-- Congruence of pairing. -/
theorem ValidEqS.pair {n : Nat} {Γ : Ctx Head n} {A a a' b b' : Tm Head n} {B : Tm Head (n + 1)}
    (validSigma : ValidTyS M Γ (.sigma A B)) (validB : ValidTyS M (.snoc Γ A) B)
    (eqA : ValidEqS M Γ a a' A) (eqB : ValidEqS M Γ b b' (Presentation.inst0 a B)) :
    ValidEqS M Γ (.pair a b) (.pair a' b') (.sigma A B) := by
  obtain ⟨validLeft, validRight, relAA'⟩ := eqA
  obtain ⟨validB₁, validB₂', relBB'⟩ := eqB
  -- At related valuations, the codomain at the second first component is the
  -- codomain at the first one.
  have codEq : ∀ {m r : Nat} {ξ : World M.reading m} {σ σ' : Sub Head n m}
      {ς : Sub Head n r}, EqSubstS M Γ ξ σ σ' ς → ∀ {P : Pack M.value m},
        DenS M.value ξ (Presentation.subst σ (Presentation.inst0 a' B)) P →
          DenS M.value ξ (Presentation.subst σ (Presentation.inst0 a B)) P := by
    intro m r ξ σ σ' ς e P den
    obtain ⟨_, denS, _, _⟩ := validSigma e
    rw [subst_inst0] at den ⊢
    exact DenS.sigma_cod laws.value denS
      (fun denA => denA.trans laws.value (validRight.2 e denA).1
        (denA.symm laws.value (relAA' e denA))) den
  have validB₂ : ValidTmS M Γ b' (Presentation.inst0 a' B) :=
    ⟨ValidTyS.inst0 validB validRight,
      fun {_ _ _ _ _ _} e {_} den => validB₂'.2 e (codEq e den)⟩
  refine ⟨ValidTmS.pair laws validSigma validLeft validB₁,
    ValidTmS.pair laws validSigma validRight validB₂,
    fun {_ _ ξ σ σ' ς} e {P} den => ?_⟩
  refine DenS.sigma_pair laws den (relAA' e) (fun {PB} denB => ?_)
  rw [← subst_inst0] at denB
  exact relBB' e denB

/-- Congruence of the first projection. -/
theorem ValidEqS.fst {n : Nat} {Γ : Ctx Head n} {p q A : Tm Head n} {B : Tm Head (n + 1)}
    (eq : ValidEqS M Γ p q (.sigma A B)) (validA : ValidTyS M Γ A) :
    ValidEqS M Γ (.fst p) (.fst q) A := by
  obtain ⟨validP, validQ, rel⟩ := eq
  refine ⟨ValidTmS.fst laws validP validA, ValidTmS.fst laws validQ validA,
    fun {_ _ ξ σ σ' ς} e {PA} den => ?_⟩
  obtain ⟨_, denS, _, _⟩ := validP.1 e
  exact DenS.sigma_fst laws denS (rel e denS) den

/-- Congruence of the second projection. -/
theorem ValidEqS.snd {n : Nat} {Γ : Ctx Head n} {p q A : Tm Head n} {B : Tm Head (n + 1)}
    (eq : ValidEqS M Γ p q (.sigma A B)) (validA : ValidTyS M Γ A)
    (validB : ValidTyS M (.snoc Γ A) B) :
    ValidEqS M Γ (.snd p) (.snd q) (Presentation.inst0 (.fst p) B) := by
  obtain ⟨validP, validQ, rel⟩ := eq
  have validSndP := ValidTmS.snd laws validP validA validB
  obtain ⟨_, relSndQ⟩ := ValidTmS.snd laws validQ validA validB
  -- At related valuations, the codomain at the first projection of `p` is the
  -- codomain at the first projection of `q`.
  have codEq : ∀ {m r : Nat} {ξ : World M.reading m} {σ σ' : Sub Head n m}
      {ς : Sub Head n r}, EqSubstS M Γ ξ σ σ' ς → ∀ {P : Pack M.value m},
        DenS M.value ξ (Presentation.subst σ (Presentation.inst0 (.fst p) B)) P →
          DenS M.value ξ (Presentation.subst σ (Presentation.inst0 (.fst q) B)) P := by
    intro m r ξ σ σ' ς e P den
    obtain ⟨_, denS, _, _⟩ := validP.1 e
    have hpq := rel e denS
    have hq := (validQ.2 e denS).1
    rw [subst_inst0] at den ⊢
    exact DenS.sigma_cod laws.value denS
      (fun denA => denA.trans laws.value (DenS.sigma_fst laws denS hpq denA)
        (denA.symm laws.value (DenS.sigma_fst laws denS hq denA))) den
  refine ⟨validSndP, ⟨validSndP.1, fun {_ _ _ _ _ _} e {_} den => relSndQ e (codEq e den)⟩,
    fun {_ _ ξ σ σ' ς} e {PB} den => ?_⟩
  obtain ⟨_, denS, _, _⟩ := validP.1 e
  rw [subst_inst0] at den
  exact DenS.sigma_snd laws denS (rel e denS) den

/-! ## β and η -/

/-- β for the first projection: the first projection of a pair weak-head
reduces to its first component, and the first projection of a pair of realizers
realizes it when the second realizer is strongly normalizing. -/
theorem ValidEqS.betaFst {n : Nat} {Γ : Ctx Head n} {a b A T : Tm Head n}
    (validA : ValidTmS M Γ a A) (validB : ValidTmS M Γ b T) :
    ValidEqS M Γ (.fst (.pair a b)) a A := by
  obtain ⟨validTyA, rel⟩ := validA
  refine ⟨⟨validTyA, fun {_ _ ξ σ σ' ς} e {P} den => ?_⟩, ⟨validTyA, rel⟩,
    fun {_ _ ξ σ σ' ς} e {P} den => ?_⟩
  · obtain ⟨h, real⟩ := rel e den
    have expansive := den.expansive laws.value
    have related : P.rel (Presentation.subst σ (.fst (.pair a b))) (Presentation.subst σ a) :=
      expansive.left (.single (.fstPair _ _)) (den.refl_left laws.value h)
    refine ⟨expansive.left (.single (.fstPair _ _)) (expansive.right (.single (.fstPair _ _)) h),
      ?_⟩
    rw [den.real_eq_of_rel laws.value related]
    exact KCand.fst_pair M.realizers.shape _ (validB.real_sn e) real
  · exact (den.expansive laws.value).left (.single (.fstPair _ _)) (rel e den).1

/-- β for the second projection: the second projection of a pair weak-head
reduces to its second component, and the second projection of a pair of
realizers realizes it when the first realizer is strongly normalizing. -/
theorem ValidEqS.betaSnd {n : Nat} {Γ : Ctx Head n} {a b A : Tm Head n} {B : Tm Head (n + 1)}
    (validA : ValidTmS M Γ a A) (validB : ValidTmS M Γ b (Presentation.inst0 a B)) :
    ValidEqS M Γ (.snd (.pair a b)) b (Presentation.inst0 a B) := by
  obtain ⟨validTyB, rel⟩ := validB
  refine ⟨⟨validTyB, fun {_ _ ξ σ σ' ς} e {P} den => ?_⟩, ⟨validTyB, rel⟩,
    fun {_ _ ξ σ σ' ς} e {P} den => ?_⟩
  · obtain ⟨h, real⟩ := rel e den
    have expansive := den.expansive laws.value
    have related : P.rel (Presentation.subst σ (.snd (.pair a b))) (Presentation.subst σ b) :=
      expansive.left (.single (.sndPair _ _)) (den.refl_left laws.value h)
    refine ⟨expansive.left (.single (.sndPair _ _)) (expansive.right (.single (.sndPair _ _)) h),
      ?_⟩
    rw [den.real_eq_of_rel laws.value related]
    exact KCand.snd_pair M.realizers.shape _ (validA.real_sn e) real
  · exact (den.expansive laws.value).left (.single (.sndPair _ _)) (rel e den).1

/-- η for pairs: pairs are equal when their projections are. -/
theorem ValidEqS.etaSigma {n : Nat} {Γ : Ctx Head n} {p q A : Tm Head n} {B : Tm Head (n + 1)}
    (validP : ValidTmS M Γ p (.sigma A B)) (validQ : ValidTmS M Γ q (.sigma A B))
    (eqFst : ValidEqS M Γ (.fst p) (.fst q) A)
    (eqSnd : ValidEqS M Γ (.snd p) (.snd q) (Presentation.inst0 (.fst p) B)) :
    ValidEqS M Γ p q (.sigma A B) := by
  obtain ⟨_, _, relFst⟩ := eqFst
  obtain ⟨_, _, relSnd⟩ := eqSnd
  refine ⟨validP, validQ, fun {_ _ ξ σ σ' ς} e {P} den => ?_⟩
  obtain ⟨l, Q, rfl, interprets⟩ := ValueSide.DenS.sigma_inv laws.value den
  obtain ⟨vp, _, _⟩ := (validP.2 e den).1
  have domI : DenS M.value ξ (Presentation.subst σ A) (Q.dom (Morph.id ξ)) :=
    ⟨l, interprets.dom_id⟩
  have denB : DenS M.value ξ (Presentation.subst σ (Presentation.inst0 (.fst p) B))
      (Q.cod (Morph.id ξ) vp) := by
    rw [subst_inst0]
    exact ⟨l, interprets.cod_id vp⟩
  exact ⟨vp, relFst e domI, relSnd e denB⟩

end Laws

end ModelSN
end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
