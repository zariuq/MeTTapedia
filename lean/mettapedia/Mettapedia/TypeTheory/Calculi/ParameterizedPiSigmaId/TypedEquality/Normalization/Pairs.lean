import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.Functions

/-!
# Validity of pairs

A valid dependent pair type has a valid domain and a valid codomain over it. A
reducible pair is a term reducing to a pair whose projections in every world
are reducible; reducible pairs are equal when their projections are, which is
η in the model. From these: validity of pairing, both projections, both β
rules, η and their congruences.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Normalization

open UniverseLevel (LevelOrder)

variable {Head L : Type} [LevelOrder L] {S : Setting Head L}

/-! ## Reducible pairs -/

section Parts

variable {n : Nat} {Δ : Ctx Head n} {dom : Tm Head n} {cod : Tm Head (n + 1)}
variable (laws : S.E.Laws S.R S.roles)
include laws

omit laws in
/-- The codomain of reducible parts is a type in every world. -/
theorem PolyParts.family (parts : PolyParts S Δ dom cod) {m : Nat} {Δ' : Ctx Head m}
    {ρ : Ren n m} (w : World S Δ Δ' ρ) :
    ∃ v, S.R.isUniverse v ∧ Typed S.R (.snoc Δ' (Presentation.rename ρ dom))
      (Presentation.rename (liftRen ρ) cod) (.head v) := by
  obtain ⟨v, hv, typing⟩ := parts.codType
  exact ⟨v, hv, typing.rename (w.1.snoc dom)⟩

/-- A term reducing to a pair whose projections are reducible is a reducible
pair. -/
theorem PolyParts.sigmaRedTm_intro (parts : PolyParts S Δ dom cod)
    (formed : CtxFormed S.R Δ) {t nf : Tm Head n}
    (red : RedTm S.R S.roles Δ t nf (.sigma dom cod)) (isPair : IsPair S.roles nf)
    (first : ∀ {m : Nat} {Δ' : Ctx Head m} {ρ : Ren n m}, World S Δ Δ' ρ →
      (packOf S Δ' (Presentation.rename ρ dom)).redTm (.fst (Presentation.rename ρ nf)))
    (second : ∀ {m : Nat} {Δ' : Ctx Head m} {ρ : Ren n m}, World S Δ Δ' ρ →
      (packOf S Δ' (inst0 (.fst (Presentation.rename ρ nf))
        (Presentation.rename (liftRen ρ) cod))).redTm (.snd (Presentation.rename ρ nf))) :
    SigmaRedTm S (canonicalPoly S Δ dom cod parts.ext) t := by
  have w := World.refl (S := S) formed
  have h₁ := first w
  have h₂ := second w
  simp only [rename_id, liftRen_id] at h₁ h₂
  have c₁ := ((parts.dom_self formed).escape laws |>.redTm h₁).2
  have c₂ := ((parts.cod_self formed h₁).escape laws |>.redTm h₂).2
  exact ⟨nf, red, isPair, laws.convTm_etaSigma parts.domType parts.codType red.target isPair
    red.target isPair c₁ c₂, fun w' => first w', fun w' => second w'⟩

/-- Reducible pairs are equal when their projections are. -/
theorem PolyParts.sigma_eqTm_of_projs (parts : PolyParts S Δ dom cod)
    (formed : CtxFormed S.R Δ) {t t' : Tm Head n}
    (redT : SigmaRedTm S (canonicalPoly S Δ dom cod parts.ext) t)
    (redT' : SigmaRedTm S (canonicalPoly S Δ dom cod parts.ext) t')
    (firsts : ∀ {m : Nat} {Δ' : Ctx Head m} {ρ : Ren n m}, World S Δ Δ' ρ →
      (packOf S Δ' (Presentation.rename ρ dom)).eqTm (.fst (Presentation.rename ρ t))
        (.fst (Presentation.rename ρ t')))
    (seconds : ∀ {m : Nat} {Δ' : Ctx Head m} {ρ : Ren n m}, World S Δ Δ' ρ →
      (packOf S Δ' (inst0 (.fst (Presentation.rename ρ t))
        (Presentation.rename (liftRen ρ) cod))).eqTm (.snd (Presentation.rename ρ t))
        (.snd (Presentation.rename ρ t'))) :
    (sigmaPack S Δ dom cod (canonicalPoly S Δ dom cod parts.ext)).eqTm t t' := by
  obtain ⟨nf, red, isPair, conv, first, second⟩ := redT
  obtain ⟨nf', red', isPair', conv', first', second'⟩ := redT'
  /- The projections of the normal forms, in every world. -/
  have projs : ∀ {m : Nat} {Δ' : Ctx Head m} {ρ : Ren n m} (w : World S Δ Δ' ρ),
      (packOf S Δ' (Presentation.rename ρ dom)).eqTm (.fst (Presentation.rename ρ nf))
        (.fst (Presentation.rename ρ nf')) ∧
      (packOf S Δ' (inst0 (.fst (Presentation.rename ρ nf))
        (Presentation.rename (liftRen ρ) cod))).eqTm (.snd (Presentation.rename ρ nf))
        (.snd (Presentation.rename ρ nf')) := by
    intro m Δ' ρ w
    have rD := parts.domain w
    have eF := (rD.redTm_expand (red.rename w.1).fst (first w)).2
    have eF' := (rD.redTm_expand (red'.rename w.1).fst (first' w)).2
    have fstEq := rD.eqTm_trans laws (rD.eqTm_symm laws eF)
      (rD.eqTm_trans laws (firsts w) eF')
    obtain ⟨hft, hft'⟩ := rD.eqTm_redTm laws (firsts w)
    obtain ⟨v, hv, family⟩ := parts.family w
    have rCt := parts.codomain w hft
    have rCn := parts.codomain w (first w)
    have rCt' := parts.codomain w hft'
    have sameN : packOf S Δ' (inst0 (.fst (Presentation.rename ρ t))
        (Presentation.rename (liftRen ρ) cod)) =
        packOf S Δ' (inst0 (.fst (Presentation.rename ρ nf))
          (Presentation.rename (liftRen ρ) cod)) :=
      rCt.conv laws rCn (parts.ext w hft (first w) eF)
    have sameT' : packOf S Δ' (inst0 (.fst (Presentation.rename ρ t))
        (Presentation.rename (liftRen ρ) cod)) =
        packOf S Δ' (inst0 (.fst (Presentation.rename ρ t'))
          (Presentation.rename (liftRen ρ) cod)) :=
      rCt.conv laws rCt' (parts.ext w hft hft' (firsts w))
    have hsn : (packOf S Δ' (inst0 (.fst (Presentation.rename ρ t))
        (Presentation.rename (liftRen ρ) cod))).redTm (.snd (Presentation.rename ρ nf)) := by
      rw [sameN]; exact second w
    have eS := (rCt.redTm_expand (RedTm.snd family hv (red.rename w.1)) hsn).2
    have hsn' : (packOf S Δ' (inst0 (.fst (Presentation.rename ρ t'))
        (Presentation.rename (liftRen ρ) cod))).redTm (.snd (Presentation.rename ρ nf')) := by
      have hn' := first' w
      have rCn' := parts.codomain w hn'
      have e := (rD.redTm_expand (red'.rename w.1).fst hn').2
      rw [rCt'.conv laws rCn' (parts.ext w hft' hn' e)]
      exact second' w
    have eS' := (rCt'.redTm_expand (RedTm.snd family hv (red'.rename w.1)) hsn').2
    rw [← sameT'] at eS'
    have sndEq := rCt.eqTm_trans laws (rCt.eqTm_symm laws eS)
      (rCt.eqTm_trans laws (seconds w) eS')
    rw [sameN] at sndEq
    exact ⟨fstEq, sndEq⟩
  have p₀ := projs (World.refl formed)
  simp only [rename_id, liftRen_id] at p₀
  have c₁ := (parts.dom_self formed).escape laws |>.eqTm p₀.1
  have hfst := ((parts.dom_self formed).eqTm_redTm laws p₀.1).1
  have c₂ := (parts.cod_self formed hfst).escape laws |>.eqTm p₀.2
  exact ⟨⟨nf, red, isPair, conv, first, second⟩, ⟨nf', red', isPair', conv', first', second'⟩,
    nf, nf', red, red', isPair, isPair',
    laws.convTm_etaSigma parts.domType parts.codType red.target isPair red'.target isPair' c₁ c₂,
    fun w => (projs w).1, fun w _ => (projs w).2⟩

omit laws in
/-- The first projection of a reducible pair. -/
theorem PolyParts.fst_redTm (parts : PolyParts S Δ dom cod) (formed : CtxFormed S.R Δ)
    {p : Tm Head n} (hp : SigmaRedTm S (canonicalPoly S Δ dom cod parts.ext) p) :
    (packOf S Δ dom).redTm (.fst p) := by
  obtain ⟨nf, red, _, _, first, _⟩ := hp
  have h := first (World.refl formed)
  simp only [canonicalPoly_domPack, rename_id] at h
  exact ((parts.dom_self formed).redTm_expand red.fst h).1

/-- The second projection of a reducible pair. -/
theorem PolyParts.snd_redTm (parts : PolyParts S Δ dom cod) (formed : CtxFormed S.R Δ)
    {p : Tm Head n} (hp : SigmaRedTm S (canonicalPoly S Δ dom cod parts.ext) p) :
    (packOf S Δ (inst0 (.fst p) cod)).redTm (.snd p) := by
  have hfst := parts.fst_redTm formed hp
  obtain ⟨nf, red, _, _, first, second⟩ := hp
  have h₁ := first (World.refl formed)
  have h₂ := second (World.refl formed)
  simp only [canonicalPoly_domPack, canonicalPoly_codPack, rename_id, liftRen_id] at h₁ h₂
  have e := ((parts.dom_self formed).redTm_expand red.fst h₁).2
  have rCp := parts.cod_self formed hfst
  have same := rCp.conv laws (parts.cod_self formed h₁) (parts.ext_self formed hfst h₁ e)
  obtain ⟨v, hv, family⟩ := parts.codType
  have h₂' : (packOf S Δ (inst0 (.fst p) cod)).redTm (.snd nf) := by
    rw [same]; exact h₂
  exact (rCp.redTm_expand (RedTm.snd family hv red) h₂').1

/-- Projections of reducibly equal pairs are reducibly equal: the first. -/
theorem PolyParts.fst_eqTm (parts : PolyParts S Δ dom cod) (formed : CtxFormed S.R Δ)
    {p p' : Tm Head n}
    (hpp : (sigmaPack S Δ dom cod (canonicalPoly S Δ dom cod parts.ext)).eqTm p p') :
    (packOf S Δ dom).eqTm (.fst p) (.fst p') := by
  obtain ⟨_, _, nf, nf', red, red', _, _, _, fstEq, _⟩ := hpp
  have h := fstEq (World.refl formed)
  simp only [canonicalPoly_domPack, rename_id] at h
  exact (parts.dom_self formed).eqTm_expand laws red.fst red'.fst h

/-- Projections of reducibly equal pairs are reducibly equal: the second. -/
theorem PolyParts.snd_eqTm (parts : PolyParts S Δ dom cod) (formed : CtxFormed S.R Δ)
    {p p' : Tm Head n}
    (hpp : (sigmaPack S Δ dom cod (canonicalPoly S Δ dom cod parts.ext)).eqTm p p') :
    (packOf S Δ (inst0 (.fst p) cod)).eqTm (.snd p) (.snd p') := by
  have fstPP := parts.fst_eqTm laws formed hpp
  obtain ⟨hp, _, nf, nf', red, red', _, _, _, fstEq, sndEq⟩ := hpp
  have rD := parts.dom_self formed
  have hfst := parts.fst_redTm formed hp
  obtain ⟨_, hfst'⟩ := rD.eqTm_redTm laws fstPP
  have h₁ := fstEq (World.refl formed)
  simp only [canonicalPoly_domPack, rename_id] at h₁
  obtain ⟨hn, _⟩ := rD.eqTm_redTm laws h₁
  have h₂ := sndEq (World.refl formed) (by simpa using hn)
  simp only [canonicalPoly_codPack, rename_id, liftRen_id] at h₂
  have e := (rD.redTm_expand red.fst hn).2
  have rCp := parts.cod_self formed hfst
  have same := rCp.conv laws (parts.cod_self formed hn) (parts.ext_self formed hfst hn e)
  rw [← same] at h₂
  obtain ⟨v, hv, family⟩ := parts.codType
  have typeEq : TypeEq S.R Δ (inst0 (.fst p') cod) (inst0 (.fst p) cod) :=
    (laws.convTy_sound ((rCp.escape laws).eqTy
      (parts.ext_self formed hfst hfst' fstPP))).symm
  exact rCp.eqTm_expand laws (RedTm.snd family hv red) ((RedTm.snd family hv red').conv typeEq) h₂

end Parts

theorem rename_subst_liftSub {n m k : Nat} (ρ : Ren m k) (σ : Sub Head n m)
    (B : Tm Head (n + 1)) :
    Presentation.rename (liftRen ρ) (Presentation.subst (liftSub σ) B) =
      Presentation.subst (liftSub fun i => Presentation.rename ρ (σ i)) B := by
  rw [rename_subst]
  apply subst_ext
  intro i
  exact rename_liftSub ρ σ i

/-! ## Inversion -/

/-- A valid dependent pair type has a valid domain and codomain. -/
theorem ValidTy.sigma_inv (laws : S.E.Laws S.R S.roles) {n : Nat} {Γ : Ctx Head n}
    {A : Tm Head n} {B : Tm Head (n + 1)} (valid : ValidTy S Γ (.sigma A B)) :
    ValidTy S Γ A ∧ ValidTy S (.snoc Γ A) B := by
  have validA : ValidTy S Γ A := by
    refine ⟨fun {m Δ σ} vσ => ?_, fun {m Δ σ σ'} vσ vσ' e P r => ?_⟩
    · obtain ⟨P, rP⟩ := valid.red vσ
      obtain ⟨parts, _, _⟩ := Reducible.sigma_view laws rP
      exact ⟨_, parts.dom_self vσ.formed⟩
    · obtain ⟨Q, rQ⟩ := valid.red vσ
      have eqSigma := valid.ext vσ vσ' e rQ
      obtain ⟨parts, rfl, _⟩ := Reducible.sigma_view laws rQ
      obtain ⟨dom', cod', red', _, domEq, _⟩ := eqSigma
      have shape : Tm.sigma dom' cod' =
          Tm.sigma (Presentation.subst σ' A) (Presentation.subst (liftSub σ') B) :=
        WhRed.eq_of_whnf (sigma_whnf S.shape _ _) red'.red
      obtain ⟨rfl, rfl⟩ := Tm.sigma.inj shape
      have h := domEq (World.refl vσ.formed)
      simp only [canonicalPoly_domPack, rename_id] at h
      rwa [r.eq_packOf laws]
  refine ⟨validA, fun {m Δ τ} vτ => ?_, fun {m Δ τ τ'} vτ vτ' e P r => ?_⟩
  · obtain ⟨tail, PA, rA, h0⟩ := vτ
    obtain ⟨Q, rQ⟩ := valid.red tail
    obtain ⟨parts, _, _⟩ := Reducible.sigma_view laws rQ
    rw [rA.eq_packOf laws] at h0
    have r := parts.cod_self tail.formed h0
    rw [inst0_subst_liftSub, consSub_tailSub] at r
    exact ⟨_, r⟩
  · obtain ⟨tail, PA, rA, h0⟩ := vτ
    obtain ⟨tail', PA', rA', h0'⟩ := vτ'
    obtain ⟨etail, PE, rE, hE⟩ := e
    have e₁ : PA = PE := rA.unique laws rE
    have e₂ : PA = PA' := validA.pack_eq laws tail tail' etail rA rA'
    subst e₁ e₂
    have hA := rA.eq_packOf laws
    have hA' := rA'.eq_packOf laws
    rw [hA] at h0 hE
    rw [hA'] at h0'
    rw [hA] at hA'
    obtain ⟨Q, rQ⟩ := valid.red tail
    have eqSigma := valid.ext tail tail' etail rQ
    obtain ⟨parts, rfl, _⟩ := Reducible.sigma_view laws rQ
    obtain ⟨Q', rQ'⟩ := valid.red tail'
    obtain ⟨parts', _, _⟩ := Reducible.sigma_view laws rQ'
    obtain ⟨dom', cod', red', _, _, codEq⟩ := eqSigma
    have shape : Tm.sigma dom' cod' = Tm.sigma (Presentation.subst (tailSub τ') A)
        (Presentation.subst (liftSub (tailSub τ')) B) :=
      WhRed.eq_of_whnf (sigma_whnf S.shape _ _) red'.red
    obtain ⟨rfl, rfl⟩ := Tm.sigma.inj shape
    have step₁ := codEq (World.refl tail.formed) (a := τ 0) (by simpa using h0)
    simp only [canonicalPoly_codPack, liftRen_id, rename_id] at step₁
    have hA₀ : (packOf S Δ (Presentation.subst (tailSub τ') A)).redTm (τ 0) := by
      rw [← hA']; exact h0
    have hE' : (packOf S Δ (Presentation.subst (tailSub τ') A)).eqTm (τ 0) (τ' 0) := by
      rw [← hA']; exact hE
    have step₂ := parts'.ext_self tail'.formed hA₀ h0' hE'
    have rL := parts.cod_self tail.formed h0
    have rMid := parts'.cod_self tail'.formed hA₀
    have chain := rL.eqTy_trans laws rMid step₁ step₂
    rw [inst0_subst_liftSub, inst0_subst_liftSub, consSub_tailSub, consSub_tailSub] at chain
    rw [r.eq_packOf laws]
    exact chain

/-! ## Projections -/

section Projections

variable (laws : S.E.Laws S.R S.roles)
include laws

/-- The first projection. -/
theorem ValidTm.fst {n : Nat} {Γ : Ctx Head n} {p A : Tm Head n} {B : Tm Head (n + 1)}
    (validP : ValidTm S Γ p (.sigma A B)) : ValidTm S Γ (.fst p) A := by
  refine ⟨(validP.type.sigma_inv laws).1, fun {m Δ σ} vσ P r => ?_,
    fun {m Δ σ σ'} vσ vσ' e P r => ?_⟩
  · obtain ⟨Q, rQ⟩ := validP.type.red vσ
    have hp := validP.red vσ rQ
    obtain ⟨parts, rfl, _⟩ := Reducible.sigma_view laws rQ
    rw [r.eq_packOf laws]
    exact parts.fst_redTm vσ.formed hp
  · obtain ⟨Q, rQ⟩ := validP.type.red vσ
    have hpp := validP.ext vσ vσ' e rQ
    obtain ⟨parts, rfl, _⟩ := Reducible.sigma_view laws rQ
    rw [r.eq_packOf laws]
    exact parts.fst_eqTm laws vσ.formed hpp

/-- The second projection. -/
theorem ValidTm.snd {n : Nat} {Γ : Ctx Head n} {p A : Tm Head n} {B : Tm Head (n + 1)}
    (validP : ValidTm S Γ p (.sigma A B)) : ValidTm S Γ (.snd p) (inst0 (.fst p) B) := by
  refine ⟨(validP.type.sigma_inv laws).2.instantiate (validP.fst laws),
    fun {m Δ σ} vσ P r => ?_, fun {m Δ σ σ'} vσ vσ' e P r => ?_⟩
  · obtain ⟨Q, rQ⟩ := validP.type.red vσ
    have hp := validP.red vσ rQ
    obtain ⟨parts, rfl, _⟩ := Reducible.sigma_view laws rQ
    rw [subst_inst0] at r
    rw [r.eq_packOf laws]
    exact parts.snd_redTm laws vσ.formed hp
  · obtain ⟨Q, rQ⟩ := validP.type.red vσ
    have hpp := validP.ext vσ vσ' e rQ
    obtain ⟨parts, rfl, _⟩ := Reducible.sigma_view laws rQ
    rw [subst_inst0] at r
    rw [r.eq_packOf laws]
    exact parts.snd_eqTm laws vσ.formed hpp

/-- Congruence of the first projection. -/
theorem ValidEq.fst {n : Nat} {Γ : Ctx Head n} {p q A : Tm Head n} {B : Tm Head (n + 1)}
    (equal : ValidEq S Γ p q (.sigma A B)) : ValidEq S Γ (.fst p) (.fst q) A := by
  refine ⟨equal.left.fst laws, equal.right.fst laws, fun {m Δ σ} vσ P r => ?_⟩
  obtain ⟨Q, rQ⟩ := equal.left.type.red vσ
  have hpq := equal.eq vσ rQ
  obtain ⟨parts, rfl, _⟩ := Reducible.sigma_view laws rQ
  rw [r.eq_packOf laws]
  exact parts.fst_eqTm laws vσ.formed hpq

/-- Congruence of the second projection. -/
theorem ValidEq.snd {n : Nat} {Γ : Ctx Head n} {p q A : Tm Head n} {B : Tm Head (n + 1)}
    (equal : ValidEq S Γ p q (.sigma A B)) :
    ValidEq S Γ (.snd p) (.snd q) (inst0 (.fst p) B) := by
  obtain ⟨validTyA, validTyB⟩ := equal.left.type.sigma_inv laws
  have right := (equal.right.snd laws).conv laws
    (ValidTyEq.symm laws (validTyA.instantiate_eq validTyB (equal.fst laws)))
  refine ⟨equal.left.snd laws, right, fun {m Δ σ} vσ P r => ?_⟩
  obtain ⟨Q, rQ⟩ := equal.left.type.red vσ
  have hpq := equal.eq vσ rQ
  obtain ⟨parts, rfl, _⟩ := Reducible.sigma_view laws rQ
  rw [subst_inst0] at r
  rw [r.eq_packOf laws]
  exact parts.snd_eqTm laws vσ.formed hpq

end Projections

/-! ## Pairing -/

section Pairing

variable (laws : S.E.Laws S.R S.roles)
include laws

/-- The projections of a pair of valid components, at a valid substitution:
reducible, and reducibly equal to the components. -/
theorem ValidTm.pair_projs {n m : Nat} {Γ : Ctx Head n} {A a b : Tm Head n}
    {B : Tm Head (n + 1)} {u : Head} (validSigma : ValidTm S Γ (.sigma A B) (.head u))
    (hu : S.R.isUniverse u) (validA : ValidTm S Γ a A) (validB : ValidTm S Γ b (inst0 a B))
    {Δ : Ctx Head m} {σ : Sub Head n m} (vσ : ValidSubst S Γ Δ σ) :
    (packOf S Δ (Presentation.subst σ A)).redTm
        (.fst (.pair (Presentation.subst σ a) (Presentation.subst σ b))) ∧
      (packOf S Δ (Presentation.subst σ A)).eqTm
        (.fst (.pair (Presentation.subst σ a) (Presentation.subst σ b)))
        (Presentation.subst σ a) ∧
      (packOf S Δ (inst0 (.fst (.pair (Presentation.subst σ a) (Presentation.subst σ b)))
        (Presentation.subst (liftSub σ) B))).redTm
        (.snd (.pair (Presentation.subst σ a) (Presentation.subst σ b))) ∧
      (packOf S Δ (inst0 (.fst (.pair (Presentation.subst σ a) (Presentation.subst σ b)))
        (Presentation.subst (liftSub σ) B))).eqTm
        (.snd (.pair (Presentation.subst σ a) (Presentation.subst σ b)))
        (Presentation.subst σ b) := by
  obtain ⟨validTyA, validTyB⟩ := (validSigma.validTy laws hu).sigma_inv laws
  obtain ⟨tSig, _, _⟩ := validSigma.universe_at laws hu vσ
  obtain ⟨PA, rA⟩ := validTyA.red vσ
  have rA' := rA.packOf_self laws
  have ha := validA.red vσ rA'
  have ta := ((rA'.escape laws).redTm ha).1
  obtain ⟨PB, rB⟩ := validB.type.red vσ
  have hb := validB.red vσ rB
  have tb := ((rB.escape laws).redTm hb).1
  rw [subst_inst0] at tb
  obtain ⟨PF, rF⟩ := validTyB.red (vσ.lift laws rA)
  obtain ⟨v, hv, family⟩ := (rF.escape laws).type
  obtain ⟨hF, eF⟩ := rA'.redTm_expand (RedTm.fstPair (roles := S.roles) tSig hu ta tb) ha
  have vτF := vσ.cons rA' hF
  have vτa := vσ.cons rA' ha
  obtain ⟨PC, rC⟩ := validTyB.red vτF
  obtain ⟨PC', rC'⟩ := validTyB.red vτa
  have same : PC = PC' := validTyB.pack_eq laws vτF vτa (vσ.refl.cons rA' eF) rC rC'
  rw [subst_inst0_consSub] at rB
  have e₁ : PB = PC' := rB.unique laws rC'
  have hb' : PC.redTm (Presentation.subst σ b) := by rw [same, ← e₁]; exact hb
  have redS := RedTm.sndPair (roles := S.roles) tSig hu family hv ta tb
  rw [inst0_subst_liftSub] at redS ⊢
  rw [← rC.eq_packOf laws]
  obtain ⟨hS, eS⟩ := rC.redTm_expand redS hb'
  exact ⟨hF, eF, hS, eS⟩

/-- A pair of valid components is reducible at every valid substitution. -/
theorem ValidTm.pair_red {n : Nat} {Γ : Ctx Head n} {A a b : Tm Head n}
    {B : Tm Head (n + 1)} {u : Head} (validSigma : ValidTm S Γ (.sigma A B) (.head u))
    (hu : S.R.isUniverse u) (validA : ValidTm S Γ a A) (validB : ValidTm S Γ b (inst0 a B))
    {m : Nat} {Δ : Ctx Head m} {σ : Sub Head n m} (vσ : ValidSubst S Γ Δ σ) {P : Pack Head m}
    (r : Reducible S Δ (Presentation.subst σ (.sigma A B)) P) :
    P.redTm (Presentation.subst σ (.pair a b)) := by
  obtain ⟨parts, rfl, _⟩ := Reducible.sigma_view laws r
  obtain ⟨tSig, _, _⟩ := validSigma.universe_at laws hu vσ
  obtain ⟨validTyA, _⟩ := (validSigma.validTy laws hu).sigma_inv laws
  have rA := parts.dom_self vσ.formed
  have ta := ((rA.escape laws).redTm (validA.red vσ rA)).1
  obtain ⟨PB, rB⟩ := validB.type.red vσ
  have tb := ((rB.escape laws).redTm (validB.red vσ rB)).1
  rw [subst_inst0] at tb
  refine parts.sigmaRedTm_intro laws vσ.formed (RedTm.refl (.pairIntro tSig hu ta tb))
    (.inl ⟨_, _, rfl⟩) ?_ ?_
  · intro k Δ' ρ w
    have h := (validSigma.pair_projs laws hu validA validB (vσ.weaken laws w)).1
    show (packOf S Δ' (Presentation.rename ρ (Presentation.subst σ A))).redTm
      (.fst (.pair (Presentation.rename ρ (Presentation.subst σ a))
        (Presentation.rename ρ (Presentation.subst σ b))))
    simp only [rename_subst]
    exact h
  · intro k Δ' ρ w
    have h := (validSigma.pair_projs laws hu validA validB (vσ.weaken laws w)).2.2.1
    show (packOf S Δ' (inst0 (.fst (.pair (Presentation.rename ρ (Presentation.subst σ a))
        (Presentation.rename ρ (Presentation.subst σ b))))
        (Presentation.rename (liftRen ρ) (Presentation.subst (liftSub σ) B)))).redTm
      (.snd (.pair (Presentation.rename ρ (Presentation.subst σ a))
        (Presentation.rename ρ (Presentation.subst σ b))))
    rw [rename_subst_liftSub]
    simp only [rename_subst]
    exact h

/-- Pairs of related components are related. -/
theorem ValidTm.pair_rel {n : Nat} {Γ : Ctx Head n} {A a a' b b' : Tm Head n}
    {B : Tm Head (n + 1)} {u : Head} (validSigma : ValidTm S Γ (.sigma A B) (.head u))
    (hu : S.R.isUniverse u) (validA : ValidTm S Γ a A) (validB : ValidTm S Γ b (inst0 a B))
    (validA' : ValidTm S Γ a' A) (validB' : ValidTm S Γ b' (inst0 a' B))
    (relA : ValidRel S Γ a a' A) (relB : ValidRel S Γ b b' (inst0 a B)) :
    ValidRel S Γ (.pair a b) (.pair a' b') (.sigma A B) := by
  intro m Δ σ σ' vσ vσ' e P r
  have validTySigma := validSigma.validTy laws hu
  obtain ⟨validTyA, validTyB⟩ := validTySigma.sigma_inv laws
  obtain ⟨Q', rQ'⟩ := validTySigma.red vσ'
  have samePi : P = Q' := validTySigma.pack_eq laws vσ vσ' e r rQ'
  have hp := validSigma.pair_red laws hu validA validB vσ r
  have hp' : P.redTm (Presentation.subst σ' (.pair a' b')) :=
    samePi ▸ validSigma.pair_red laws hu validA' validB' vσ' rQ'
  obtain ⟨parts, rfl, _⟩ := Reducible.sigma_view laws r
  /- The components at the weakened substitutions. -/
  have comps : ∀ {k : Nat} {Δ' : Ctx Head k} {ρ : Ren m k} (w : World S Δ Δ' ρ),
      (packOf S Δ' (Presentation.subst (fun i => Presentation.rename ρ (σ i)) A)).eqTm
        (.fst (.pair (Presentation.subst (fun i => Presentation.rename ρ (σ i)) a)
          (Presentation.subst (fun i => Presentation.rename ρ (σ i)) b)))
        (.fst (.pair (Presentation.subst (fun i => Presentation.rename ρ (σ' i)) a')
          (Presentation.subst (fun i => Presentation.rename ρ (σ' i)) b'))) ∧
      (packOf S Δ' (inst0 (.fst (.pair (Presentation.subst (fun i => Presentation.rename ρ (σ i)) a)
          (Presentation.subst (fun i => Presentation.rename ρ (σ i)) b)))
          (Presentation.subst (liftSub fun i => Presentation.rename ρ (σ i)) B))).eqTm
        (.snd (.pair (Presentation.subst (fun i => Presentation.rename ρ (σ i)) a)
          (Presentation.subst (fun i => Presentation.rename ρ (σ i)) b)))
        (.snd (.pair (Presentation.subst (fun i => Presentation.rename ρ (σ' i)) a')
          (Presentation.subst (fun i => Presentation.rename ρ (σ' i)) b'))) := by
    intro k Δ' ρ w
    have vρσ := vσ.weaken laws w
    have vρσ' := vσ'.weaken laws w
    have eρ := e.weaken laws w
    obtain ⟨hF, eF, hS, eS⟩ := validSigma.pair_projs laws hu validA validB vρσ
    obtain ⟨hF', eF', hS', eS'⟩ := validSigma.pair_projs laws hu validA' validB' vρσ'
    obtain ⟨PA, rA⟩ := validTyA.red vρσ
    obtain ⟨PA', rA'⟩ := validTyA.red vρσ'
    have sameA : PA = PA' := validTyA.pack_eq laws vρσ vρσ' eρ rA rA'
    have rAo := rA.packOf_self laws
    have eqA : packOf S Δ' (Presentation.subst (fun i => Presentation.rename ρ (σ i)) A) =
        packOf S Δ' (Presentation.subst (fun i => Presentation.rename ρ (σ' i)) A) := by
      rw [← rA.eq_packOf laws, ← rA'.eq_packOf laws, sameA]
    have mA := relA vρσ vρσ' eρ rAo
    rw [← eqA] at eF'
    have firsts := rAo.eqTm_trans laws eF (rAo.eqTm_trans laws mA (rAo.eqTm_symm laws eF'))
    refine ⟨firsts, ?_⟩
    obtain ⟨hFirst, hFirst'⟩ := rAo.eqTm_redTm laws firsts
    have hFirst'' : (packOf S Δ' (Presentation.subst (fun i => Presentation.rename ρ (σ' i)) A)).redTm
        (.fst (.pair (Presentation.subst (fun i => Presentation.rename ρ (σ' i)) a')
          (Presentation.subst (fun i => Presentation.rename ρ (σ' i)) b'))) := by
      rw [← eqA]; exact hFirst'
    have packs := validTyA.pack_eq_cons laws validTyB vρσ vρσ' eρ hFirst hFirst'' firsts
    have packa := validTyA.pack_eq_cons laws validTyB vρσ vρσ (vρσ.refl) hFirst
      ((validA.red vρσ rAo)) eF
    rw [inst0_subst_liftSub] at hS eS hS' eS' ⊢
    rw [← packs] at eS'
    obtain ⟨PB, rB⟩ := validB.type.red vρσ
    have mB := relB vρσ vρσ' eρ rB
    rw [subst_inst0_consSub] at rB
    rw [rB.eq_packOf laws, ← packa] at mB
    obtain ⟨PC, rC⟩ := validTyB.red (vρσ.cons rAo hFirst)
    rw [← rC.eq_packOf laws] at eS eS' mB ⊢
    exact rC.eqTm_trans laws eS (rC.eqTm_trans laws mB (rC.eqTm_symm laws eS'))
  refine parts.sigma_eqTm_of_projs laws vσ.formed hp hp' (fun {k Δ' ρ} w => ?_)
    (fun {k Δ' ρ} w => ?_)
  · show (packOf S Δ' (Presentation.rename ρ (Presentation.subst σ A))).eqTm
      (.fst (.pair (Presentation.rename ρ (Presentation.subst σ a))
        (Presentation.rename ρ (Presentation.subst σ b))))
      (.fst (.pair (Presentation.rename ρ (Presentation.subst σ' a'))
        (Presentation.rename ρ (Presentation.subst σ' b'))))
    simp only [rename_subst]
    exact (comps w).1
  · show (packOf S Δ' (inst0 (.fst (.pair (Presentation.rename ρ (Presentation.subst σ a))
        (Presentation.rename ρ (Presentation.subst σ b))))
        (Presentation.rename (liftRen ρ) (Presentation.subst (liftSub σ) B)))).eqTm
      (.snd (.pair (Presentation.rename ρ (Presentation.subst σ a))
        (Presentation.rename ρ (Presentation.subst σ b))))
      (.snd (.pair (Presentation.rename ρ (Presentation.subst σ' a'))
        (Presentation.rename ρ (Presentation.subst σ' b'))))
    rw [rename_subst_liftSub]
    simp only [rename_subst]
    exact (comps w).2

/-- Pairing. -/
theorem ValidTm.pair {n : Nat} {Γ : Ctx Head n} {A a b : Tm Head n} {B : Tm Head (n + 1)}
    {u : Head} (validSigma : ValidTm S Γ (.sigma A B) (.head u)) (hu : S.R.isUniverse u)
    (validA : ValidTm S Γ a A) (validB : ValidTm S Γ b (inst0 a B)) :
    ValidTm S Γ (.pair a b) (.sigma A B) :=
  ⟨validSigma.validTy laws hu, fun vσ _ r => validSigma.pair_red laws hu validA validB vσ r,
    validSigma.pair_rel laws hu validA validB validA validB validA.rel validB.rel⟩

/-- Congruence of pairing. -/
theorem ValidEq.pair {n : Nat} {Γ : Ctx Head n} {A a a' b b' : Tm Head n}
    {B : Tm Head (n + 1)} {u : Head} (validSigma : ValidTm S Γ (.sigma A B) (.head u))
    (hu : S.R.isUniverse u) (equalA : ValidEq S Γ a a' A)
    (equalB : ValidEq S Γ b b' (inst0 a B)) :
    ValidEq S Γ (.pair a b) (.pair a' b') (.sigma A B) := by
  obtain ⟨validTyA, validTyB⟩ := (validSigma.validTy laws hu).sigma_inv laws
  have validB' := equalB.right.conv laws (validTyA.instantiate_eq validTyB equalA)
  refine ⟨validSigma.pair laws hu equalA.left equalB.left,
    validSigma.pair laws hu equalA.right validB', fun vσ _ r => ?_⟩
  exact validSigma.pair_rel laws hu equalA.left equalB.left equalA.right validB'
    (equalA.rel laws) (equalB.rel laws) vσ vσ vσ.refl r

/-- β for the first projection. -/
theorem ValidEq.betaFst {n : Nat} {Γ : Ctx Head n} {A a b : Tm Head n}
    {B : Tm Head (n + 1)} {u : Head} (validSigma : ValidTm S Γ (.sigma A B) (.head u))
    (hu : S.R.isUniverse u) (validA : ValidTm S Γ a A) (validB : ValidTm S Γ b (inst0 a B)) :
    ValidEq S Γ (.fst (.pair a b)) a A := by
  refine ⟨(validSigma.pair laws hu validA validB).fst laws, validA, fun vσ P r => ?_⟩
  rw [r.eq_packOf laws]
  exact (validSigma.pair_projs laws hu validA validB vσ).2.1

/-- β for the second projection. -/
theorem ValidEq.betaSnd {n : Nat} {Γ : Ctx Head n} {A a b : Tm Head n}
    {B : Tm Head (n + 1)} {u : Head} (validSigma : ValidTm S Γ (.sigma A B) (.head u))
    (hu : S.R.isUniverse u) (validA : ValidTm S Γ a A) (validB : ValidTm S Γ b (inst0 a B)) :
    ValidEq S Γ (.snd (.pair a b)) b (inst0 a B) := by
  obtain ⟨validTyA, validTyB⟩ := (validSigma.validTy laws hu).sigma_inv laws
  have left := ((validSigma.pair laws hu validA validB).snd laws).conv laws
    (validTyA.instantiate_eq validTyB (ValidEq.betaFst laws validSigma hu validA validB))
  refine ⟨left, validB, fun {m Δ σ} vσ P r => ?_⟩
  obtain ⟨hF, eF, _, eS⟩ := validSigma.pair_projs laws hu validA validB vσ
  obtain ⟨PA, rA⟩ := validTyA.red vσ
  have rAo := rA.packOf_self laws
  have packa := validTyA.pack_eq_cons laws validTyB vσ vσ vσ.refl hF (validA.red vσ rAo) eF
  rw [inst0_subst_liftSub, packa] at eS
  rw [subst_inst0_consSub] at r
  rw [r.eq_packOf laws]
  exact eS

/-- η for pairs: pairs are equal when their projections are. -/
theorem ValidEq.etaSigma {n : Nat} {Γ : Ctx Head n} {p q A : Tm Head n} {B : Tm Head (n + 1)}
    (validP : ValidTm S Γ p (.sigma A B)) (validQ : ValidTm S Γ q (.sigma A B))
    (equalFst : ValidEq S Γ (.fst p) (.fst q) A)
    (equalSnd : ValidEq S Γ (.snd p) (.snd q) (inst0 (.fst p) B)) :
    ValidEq S Γ p q (.sigma A B) := by
  refine ⟨validP, validQ, fun {m Δ σ} vσ P r => ?_⟩
  have hp := validP.red vσ r
  have hq := validQ.red vσ r
  obtain ⟨parts, rfl, _⟩ := Reducible.sigma_view laws r
  refine parts.sigma_eqTm_of_projs laws vσ.formed hp hq (fun {k Δ' ρ} w => ?_)
    (fun {k Δ' ρ} w => ?_)
  · have vρσ := vσ.weaken laws w
    obtain ⟨PA, rA⟩ := equalFst.left.type.red vρσ
    have h := equalFst.eq vρσ rA
    rw [rA.eq_packOf laws] at h
    simp only [rename_subst]
    exact h
  · have vρσ := vσ.weaken laws w
    obtain ⟨PB, rB⟩ := equalSnd.left.type.red vρσ
    have h := equalSnd.eq vρσ rB
    rw [rB.eq_packOf laws, subst_inst0] at h
    rw [rename_subst_liftSub]
    simp only [rename_subst]
    exact h

end Pairing



end Normalization
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
