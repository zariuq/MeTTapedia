import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.ModelS.Functions

/-!
# Equality, conversion and inclusion in model S

Validly equal terms of a type form a partial equivalence. A valid term is equal
to itself, and equality is symmetric and transitive: the relation of a
denotation is a partial equivalence, and related valuations relate the
instances of a valid term. Realizers come with the valid terms.

Equal types of a universe have one pack under the first of two related
valuations. Terms and equalities move along them with their values and
realizers.

Inclusion of packs covers the value relation and the realizers of valid values.
It holds between equal types of a universe, and between cumulative universes:
the universe relation grows with the level (`universePack_mono`), and types of
both are realized by the strongly normalizing terms. It composes, and it is
preserved

* by dependent function types with equal domains and included codomains: a
  realizer of a function sends the realizers of valid arguments to realizers
  of the results, and a valid function has valid results, whose realizers the
  inclusion of the codomains carries over;
* by dependent pair types with included domains and codomains: a realizer of a
  valid pair has projections that realize the projections, and a valid pair
  has valid projections, whose realizers the inclusions carry over.

Terms and equalities move along inclusions.

An identity type relates all terms. It is realized by the strongly normalizing
terms that reduce to reflexivity only when its endpoints are related, so,
between equal terms, by all strongly normalizing terms (`DenS.id_real_sn`). Any
two terms whose realizer instances are strongly normalizing are then equal
proofs of it; in particular reflexivity proofs of valid terms are valid, and
reflexivity proofs of equal terms are equal.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Impredicative
namespace ModelS

open Normalization (inst0_rename_subst_liftSub inst0_subst_liftSub)
open UniverseLevel (LevelOrder)
open Consistency (World Morph)
open StrongNormalization
open ValueSide

variable {Head L : Type} [LevelOrder L] {M : SModel Head L}

/-! ## Inclusion of packs and extension of valuations -/

/-- Inclusion of packs: of the value relation, and of the realizers of every
valid value. A type validly below another has its pack included in the other's
under related valuations. -/
def Pack.Le {n : Nat} (P P' : Pack M.value n) : Prop :=
  (∀ {a b : Tm Head n}, P.rel a b → P'.rel a b) ∧
    ∀ {a : Tm Head n}, P.Val a → Incl (P.real a) (P'.real a)

/-- Related valuations extend by related values, with a fresh variable realizing
the new variable. -/
theorem EqSubstS.consVar {n m r : Nat} {Γ : Ctx Head n} {ξ : World M.reading m}
    {σ σ' : Sub Head n m} {ς : Sub Head n r} (eq : EqSubstS M Γ ξ σ σ' ς) {A : Tm Head n}
    {P : Pack M.value m} (den : DenS M.value ξ (Presentation.subst σ A) P) {a a' : Tm Head m}
    (h : P.rel a a') :
    EqSubstS M (.snoc Γ A) ξ (consSub a σ) (consSub a' σ')
      (consSub (.var 0) fun i => Presentation.rename wk (ς i)) :=
  (eq.renameReal wk).cons den h ((P.real a).var_mem (RootShape.spineHeaded M.realizers.shape) 0)

/-! ## Equality is a partial equivalence -/

/-- A valid term is validly equal to itself. -/
theorem ValidEqS.refl {n : Nat} {Γ : Ctx Head n} {a A : Tm Head n}
    (valid : ValidTmS M Γ a A) : ValidEqS M Γ a a A :=
  ⟨valid, valid, fun {_ _ _ _ _ _} e {_} den => (valid.2 e den).1⟩

section Laws

variable (laws : M.Laws)
include laws

/-- Valid equality is symmetric. -/
theorem ValidEqS.symm {n : Nat} {Γ : Ctx Head n} {a b A : Tm Head n}
    (eq : ValidEqS M Γ a b A) : ValidEqS M Γ b a A := by
  obtain ⟨valid₁, valid₂, rel⟩ := eq
  refine ⟨valid₂, valid₁, fun {_ _ _ _ _ _} e {P} den => ?_⟩
  have ha := (valid₁.2 e den).1
  have hb := (valid₂.2 e den).1
  exact den.trans laws.value (den.trans laws.value hb (den.symm laws.value (rel e den))) ha

/-- Valid equality is transitive. -/
theorem ValidEqS.trans {n : Nat} {Γ : Ctx Head n} {a b c A : Tm Head n}
    (eq₁ : ValidEqS M Γ a b A) (eq₂ : ValidEqS M Γ b c A) : ValidEqS M Γ a c A := by
  obtain ⟨valid₁, valid₂, rel₁⟩ := eq₁
  obtain ⟨-, valid₃, rel₂⟩ := eq₂
  refine ⟨valid₁, valid₃, fun {_ _ _ _ _ _} e {P} den => ?_⟩
  have hb := (valid₂.2 e den).1
  exact den.trans laws.value (den.trans laws.value (rel₁ e den) (den.symm laws.value hb))
    (rel₂ e den)

/-! ## Conversion -/

/-- Equal types of a universe have one pack under the first of two related
valuations. -/
theorem ValidEqS.den_left {n : Nat} {Γ : Ctx Head n} {A B : Tm Head n}
    {u : Head} (eq : ValidEqS M Γ A B (.head u)) (hu : M.rules.isUniverse u) {m r : Nat}
    {ξ : World M.reading m} {σ σ' : Sub Head n m} {ς : Sub Head n r}
    (e : EqSubstS M Γ ξ σ σ' ς) :
    ∃ P, DenS M.value ξ (Presentation.subst σ A) P ∧ DenS M.value ξ (Presentation.subst σ B) P := by
  obtain ⟨P, denA, denB'⟩ := ValidEqS.den eq hu e
  obtain ⟨P', denB, denB'', -⟩ := (ValidTmS.validTy eq.2.1 hu) e
  obtain rfl := DenS.deterministic laws.value denB' denB''
  exact ⟨_, denA, denB⟩

/-- A term of a type is a term of every equal type of a universe. -/
theorem ValidTmS.conv {n : Nat} {Γ : Ctx Head n} {t A B : Tm Head n}
    {u : Head} (valid : ValidTmS M Γ t A) (eq : ValidEqS M Γ A B (.head u))
    (hu : M.rules.isUniverse u) : ValidTmS M Γ t B := by
  obtain ⟨-, rel⟩ := valid
  refine ⟨ValidTmS.validTy eq.2.1 hu, fun {_ _ _ _ _ _} e {P} den => ?_⟩
  obtain ⟨_, denA, denB⟩ := ValidEqS.den_left laws eq hu e
  rw [DenS.deterministic laws.value den denB]
  exact rel e denA

/-- Equal terms of a type are equal terms of every equal type of a universe. -/
theorem ValidEqS.conv {n : Nat} {Γ : Ctx Head n} {a b A B : Tm Head n}
    {u : Head} (valid : ValidEqS M Γ a b A) (eq : ValidEqS M Γ A B (.head u))
    (hu : M.rules.isUniverse u) : ValidEqS M Γ a b B := by
  obtain ⟨valid₁, valid₂, rel⟩ := valid
  refine ⟨ValidTmS.conv laws valid₁ eq hu, ValidTmS.conv laws valid₂ eq hu,
    fun {_ _ _ _ _ _} e {P} den => ?_⟩
  obtain ⟨_, denA, denB⟩ := ValidEqS.den_left laws eq hu e
  rw [DenS.deterministic laws.value den denB]
  exact rel e denA

/-! ## Inclusion -/

/-- Equal types of a universe are validly below one another. -/
theorem ValidLeS.ofEq {n : Nat} {Γ : Ctx Head n} {A B : Tm Head n}
    {u : Head} (eq : ValidEqS M Γ A B (.head u)) (hu : M.rules.isUniverse u) :
    ValidLeS M Γ A B := by
  refine ⟨ValidTmS.validTy eq.1 hu, ValidTmS.validTy eq.2.1 hu,
    fun {_ _ _ _ _ _} e {P P'} den den' => ?_⟩
  obtain ⟨_, denA, denB⟩ := ValidEqS.den_left laws eq hu e
  obtain rfl := DenS.deterministic laws.value den denA
  obtain rfl := DenS.deterministic laws.value den' denB
  exact ⟨fun h => h, fun {_} _ {_ _} h => h⟩

/-- A universe is validly below every universe it is cumulative into: the
universe relation grows with the level, and types of both are realized by the
strongly normalizing terms. -/
theorem ValidLeS.univ {n : Nat} {Γ : Ctx Head n} {u v : Head}
    (cumulative : M.rules.cumulative u v) : ValidLeS M Γ (.head u) (.head v) := by
  obtain ⟨hu, hv, le⟩ := M.levels.cumulative_universe cumulative
  refine ⟨ValidTyS.sort hu, ValidTyS.sort hv, fun {_ _ _ _ _ _} _ {P P'} den den' => ?_⟩
  rw [DenS.sort_inv laws hu den, DenS.sort_inv laws hv den']
  exact ⟨fun h => universeAt.mono laws.value le h, fun {_} _ {_ _} h => h⟩

/-- A term of a type is a term of every type validly above it. -/
theorem ValidTmS.below {n : Nat} {Γ : Ctx Head n} {t A B : Tm Head n}
    (valid : ValidTmS M Γ t A) (le : ValidLeS M Γ A B) : ValidTmS M Γ t B := by
  obtain ⟨-, rel⟩ := valid
  obtain ⟨validA, validB, incl⟩ := le
  refine ⟨validB, fun {_ _ _ _ _ _} e {P'} den' => ?_⟩
  obtain ⟨P, den, -, -⟩ := validA e
  obtain ⟨h, real⟩ := rel e den
  obtain ⟨inclRel, inclReal⟩ := incl e den den'
  exact ⟨inclRel h, inclReal (den.refl_left laws.value h) real⟩

/-- Equal terms of a type are equal terms of every type validly above it. -/
theorem ValidEqS.below {n : Nat} {Γ : Ctx Head n} {a b A B : Tm Head n}
    (valid : ValidEqS M Γ a b A) (le : ValidLeS M Γ A B) : ValidEqS M Γ a b B := by
  obtain ⟨valid₁, valid₂, rel⟩ := valid
  refine ⟨ValidTmS.below laws valid₁ le, ValidTmS.below laws valid₂ le,
    fun {_ _ _ _ _ _} e {P'} den' => ?_⟩
  obtain ⟨validA, -, incl⟩ := le
  obtain ⟨P, den, -, -⟩ := validA e
  exact (incl e den den').1 (rel e den)

omit laws in
/-- Valid inclusion is transitive. -/
theorem ValidLeS.trans {n : Nat} {Γ : Ctx Head n} {A B C : Tm Head n}
    (le₁ : ValidLeS M Γ A B) (le₂ : ValidLeS M Γ B C) : ValidLeS M Γ A C := by
  obtain ⟨validA, validB, incl₁⟩ := le₁
  obtain ⟨-, validC, incl₂⟩ := le₂
  refine ⟨validA, validC, fun {_ _ _ _ _ _} e {P P''} den den'' => ?_⟩
  obtain ⟨P', den', -, -⟩ := validB e
  obtain ⟨rel₁, real₁⟩ := incl₁ e den den'
  obtain ⟨rel₂, real₂⟩ := incl₂ e den' den''
  exact ⟨fun h => rel₂ (rel₁ h), fun {_} ha {_ _} h => real₂ (rel₁ ha) (real₁ ha h)⟩

/-- A dependent function type is validly below another with an equal domain of a
universe and a codomain validly above its own. -/
theorem ValidLeS.pi {n : Nat} {Γ : Ctx Head n} {A A' : Tm Head n}
    {B B' : Tm Head (n + 1)} {w : Head} (validPi : ValidTyS M Γ (.pi A B))
    (validPi' : ValidTyS M Γ (.pi A' B')) (eqA : ValidEqS M Γ A A' (.head w))
    (hw : M.rules.isUniverse w) (leB : ValidLeS M (.snoc Γ A) B B') :
    ValidLeS M Γ (.pi A B) (.pi A' B') := by
  obtain ⟨-, -, inclB⟩ := leB
  refine ⟨validPi, validPi', fun {m _ ξ σ σ' _} e {P P'} den den' => ?_⟩
  obtain ⟨l, Q, rfl, QI⟩ := ValueSide.DenS.pi_inv laws.value den
  obtain ⟨l', Q', rfl, QI'⟩ := ValueSide.DenS.pi_inv laws.value den'
  -- The two families have one domain pack at every world reached by a morphism.
  have dom : ∀ {k : Nat} {ξ' : World M.reading k} {ρ : Ren m k} (mor : Morph ξ ξ' ρ),
      Q'.dom mor = Q.dom mor := by
    intro k ξ' ρ mor
    have denA := QI.dom mor
    have denA' := QI'.dom mor
    rw [rename_subst] at denA denA'
    obtain ⟨D, denD, denD'⟩ := ValidEqS.den_left laws eqA hw (EqSubstS.rename laws e mor)
    exact (DenS.deterministic laws.value ⟨l', denA'⟩ denD').trans
      (DenS.deterministic laws.value ⟨l, denA⟩ denD).symm
  -- At a valid argument, the codomain pack of the first family is included in that of
  -- the second.
  have cod : ∀ {k : Nat} {ξ' : World M.reading k} {ρ : Ren m k} (mor : Morph ξ ξ' ρ)
      {a : Tm Head k} (ha : (Q.dom mor).Val a) (ha' : (Q'.dom mor).Val a),
      Pack.Le (Q.cod mor ha) (Q'.cod mor ha') := by
    intro k ξ' ρ mor a ha ha'
    have denA := QI.dom mor
    have codB := QI.cod mor ha
    have codB' := QI'.cod mor ha'
    rw [rename_subst] at denA
    rw [inst0_rename_subst_liftSub] at codB codB'
    exact inclB (EqSubstS.consVar (EqSubstS.rename laws e mor) ⟨l, denA⟩ ha)
      ⟨l, codB⟩ ⟨l', codB'⟩
  refine ⟨fun {f g} h => ?_, fun {f} hf {j t} ht => ?_⟩
  · intro k ξ' ρ mor a b ha' hab'
    have ha : (Q.dom mor).Val a := by
      rw [← dom mor]
      exact ha'
    have hab : (Q.dom mor).rel a b := by
      rw [← dom mor]
      exact hab'
    exact (cod mor ha ha').1 (h mor ha hab)
  · -- A valid function has valid results, whose realizers the codomains carry over.
    have ht' := (PiPack.mem_real Q).mp ht
    refine (PiPack.mem_real Q').mpr ⟨ht'.1, fun {k ξ' ρ} mor {a} ha' {r'} ρr u hu => ?_⟩
    have ha : (Q.dom mor).Val a := by
      rw [← dom mor]
      exact ha'
    have hu' : ((Q.dom mor).real a).mem u := by
      rw [← dom mor]
      exact hu
    exact (cod mor ha ha').2 (hf mor ha ha) (ht'.2 mor ha ρr u hu')

/-- A dependent pair type is validly below another whose domain and codomain are
validly above its own. -/
theorem ValidLeS.sigma {n : Nat} {Γ : Ctx Head n} {A A' : Tm Head n}
    {B B' : Tm Head (n + 1)} (validS : ValidTyS M Γ (.sigma A B))
    (validS' : ValidTyS M Γ (.sigma A' B')) (leA : ValidLeS M Γ A A')
    (leB : ValidLeS M (.snoc Γ A) B B') : ValidLeS M Γ (.sigma A B) (.sigma A' B') := by
  obtain ⟨-, -, inclA⟩ := leA
  obtain ⟨-, -, inclB⟩ := leB
  refine ⟨validS, validS', fun {_ _ ξ σ σ' _} e {P P'} den den' => ?_⟩
  obtain ⟨l, Q, rfl, QI⟩ := ValueSide.DenS.sigma_inv laws.value den
  obtain ⟨l', Q', rfl, QI'⟩ := ValueSide.DenS.sigma_inv laws.value den'
  have denA := QI.dom_id
  have denA' := QI'.dom_id
  obtain ⟨domRel, domReal⟩ := inclA e ⟨l, denA⟩ ⟨l', denA'⟩
  -- At a valid first projection, the codomain pack of the first family is included in
  -- that of the second.
  have cod : ∀ {a : Tm Head _} (ha : (Q.dom (Morph.id ξ)).Val a)
      (ha' : (Q'.dom (Morph.id ξ)).Val a),
      Pack.Le (Q.cod (Morph.id ξ) ha) (Q'.cod (Morph.id ξ) ha') := by
    intro a ha ha'
    have codB := QI.cod_id ha
    have codB' := QI'.cod_id ha'
    rw [inst0_subst_liftSub] at codB codB'
    exact inclB (EqSubstS.consVar e ⟨l, denA⟩ ha) ⟨l, codB⟩ ⟨l', codB'⟩
  refine ⟨?_, ?_⟩
  · rintro p q ⟨hp, hpq, hc⟩
    exact ⟨domRel hp, domRel hpq, (cod hp (domRel hp)).1 hc⟩
  · -- A valid pair has a valid second projection, whose realizers the codomains carry
    -- over.
    intro p hv k t ht
    obtain ⟨hp, _, hc⟩ := hv
    have ht' := (PiPack.mem_pairReal Q).mp ht
    exact (PiPack.mem_pairReal Q').mpr ⟨ht'.1, fun hp' =>
      ⟨domReal hp (ht'.2 hp).1, (cod hp hp').2 hc (ht'.2 hp).2⟩⟩

/-! ## Identity types -/

/-- An identity type between valid terms of a type is a valid type. -/
theorem ValidTyS.ident {n : Nat} {Γ : Ctx Head n} {A a b : Tm Head n}
    (valid₁ : ValidTmS M Γ a A) (valid₂ : ValidTmS M Γ b A) :
    ValidTyS M Γ (.id A a b) := by
  intro _ _ _ σ σ' _ e
  obtain ⟨R, den, den', snA⟩ := valid₁.1 e
  obtain ⟨ha, ra⟩ := valid₁.2 e den
  obtain ⟨hb, rb⟩ := valid₂.2 e den
  -- Related endpoints are related exactly when the other endpoints are.
  have same : R.rel (Presentation.subst σ a) (Presentation.subst σ b) ↔
      R.rel (Presentation.subst σ' a) (Presentation.subst σ' b) :=
    ⟨fun h => den.trans laws.value (den.trans laws.value (den.symm laws.value ha) h) hb,
      fun h => den.trans laws.value (den.trans laws.value ha h) (den.symm laws.value hb)⟩
  refine ⟨_, DenS.ident den (den.refl_left laws.value ha) (den.refl_left laws.value hb), ?_,
    SN.id (RootShape.spineHeaded M.realizers.shape) snA ((R.real _).sn ra) ((R.real _).sn rb)⟩
  have e' : identPack R (Presentation.subst σ a) (Presentation.subst σ b) =
      identPack R (Presentation.subst σ' a) (Presentation.subst σ' b) := by
    unfold identPack
    rw [propext same]
  rw [e']
  exact DenS.ident den' (den.refl_right laws.value ha) (den.refl_right laws.value hb)

/-- Under related valuations, an identity type between equal terms is realized
by the strongly normalizing terms. -/
theorem ValidEqS.ident_real {n : Nat} {Γ : Ctx Head n} {a b A : Tm Head n}
    (eq : ValidEqS M Γ a b A) {m r : Nat} {ξ : World M.reading m} {σ σ' : Sub Head n m}
    {ς : Sub Head n r} (e : EqSubstS M Γ ξ σ σ' ς) {P : Pack M.value m}
    (den : DenS M.value ξ (Presentation.subst σ (.id A a b)) P) (t : Tm Head m) :
    P.real t = M.realizers.sn := by
  obtain ⟨⟨validA, -⟩, ⟨-, rel₂⟩, rel⟩ := eq
  obtain ⟨RA, denA, -, -⟩ := validA e
  exact DenS.id_real_sn laws den denA
    (denA.trans laws.value (rel e denA) (denA.symm laws.value (rel₂ e denA).1)) t

/-- Any two terms whose realizer instances under related valuations are strongly
normalizing are validly equal proofs of an identity between equal terms. -/
theorem ValidEqS.ident_irrelevant {n : Nat} {Γ : Ctx Head n}
    {a b A : Tm Head n} (eq : ValidEqS M Γ a b A) {t u : Tm Head n}
    (sn : ∀ {m r : Nat} {ξ : World M.reading m} {σ σ' : Sub Head n m} {ς : Sub Head n r},
      EqSubstS M Γ ξ σ σ' ς →
        SN M.realizers.rules (Presentation.subst ς t) ∧
          SN M.realizers.rules (Presentation.subst ς u)) :
    ValidEqS M Γ t u (.id A a b) := by
  have validId : ValidTyS M Γ (.id A a b) := ValidTyS.ident laws eq.1 eq.2.1
  refine ⟨⟨validId, fun {_ _ _ _ _ _} e {_} den => ?_⟩,
    ⟨validId, fun {_ _ _ _ _ _} e {_} den => ?_⟩,
    fun {_ _ _ _ _ _} _ {_} den => den.id_rel laws.value _ _⟩
  · rw [ValidEqS.ident_real laws eq e den]
    exact ⟨den.id_rel laws.value _ _, (sn e).1⟩
  · rw [ValidEqS.ident_real laws eq e den]
    exact ⟨den.id_rel laws.value _ _, (sn e).2⟩

/-- Reflexivity proves the identity of a valid term with itself. -/
theorem ValidTmS.refl {n : Nat} {Γ : Ctx Head n} {a A : Tm Head n}
    (valid : ValidTmS M Γ a A) : ValidTmS M Γ (.refl a) (.id A a a) :=
  (ValidEqS.ident_irrelevant laws (ValidEqS.refl valid) (t := .refl a) (u := .refl a)
    fun e =>
      have sn := SN.refl (RootShape.spineHeaded M.realizers.shape) (valid.real_sn e)
      ⟨sn, sn⟩).1

/-- Reflexivity proofs of equal terms are equal. -/
theorem ValidEqS.reflCong {n : Nat} {Γ : Ctx Head n} {a b A : Tm Head n}
    (eq : ValidEqS M Γ a b A) :
    ValidEqS M Γ (.refl a) (.refl b) (.id A a a) :=
  ValidEqS.ident_irrelevant laws (ValidEqS.refl eq.1) fun e =>
    ⟨SN.refl (RootShape.spineHeaded M.realizers.shape) (eq.1.real_sn e),
      SN.refl (RootShape.spineHeaded M.realizers.shape) (eq.2.1.real_sn e)⟩

end Laws

end ModelS
end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
