import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.Formation

/-!
# Validity of functions

A valid dependent function type has a valid domain and a valid codomain over
it. A reducible function is a term reducing to a function whose applications
in every world are reducible at the codomain; reducible functions are equal
when their applications are, which is η in the model. From these: validity of
λ-abstraction, application, β, η and their congruences.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Normalization

open UniverseLevel (LevelOrder)

variable {Head L : Type} [LevelOrder L] {S : Setting Head L}

/-- A formed context is a world over itself. -/
theorem World.refl {n : Nat} {Δ : Ctx Head n} (formed : CtxFormed S.R Δ) :
    World S Δ Δ idRen :=
  ⟨CtxRen.id Δ, formed⟩

/-- Extending a formed context by a type is a world over it. -/
theorem World.snoc {n : Nat} {Δ : Ctx Head n} {A : Tm Head n} (formed : CtxFormed S.R Δ)
    (type : IsType S.R Δ A) : World S Δ (.snoc Δ A) wk :=
  ⟨CtxRen.wk Δ A, .snoc formed type⟩

theorem consSub_tailSub {n m : Nat} (τ : Sub Head (n + 1) m) : consSub (τ 0) (tailSub τ) = τ :=
  consSub_eta τ

/-! ## Parts in their own context -/

section Parts

variable {n : Nat} {Δ : Ctx Head n} {dom : Tm Head n} {cod : Tm Head (n + 1)}

theorem PolyParts.dom_self (parts : PolyParts S Δ dom cod) (formed : CtxFormed S.R Δ) :
    Reducible S Δ dom (packOf S Δ dom) := by
  simpa using parts.domain (World.refl formed)

theorem PolyParts.cod_self (parts : PolyParts S Δ dom cod) (formed : CtxFormed S.R Δ)
    {a : Tm Head n} (ha : (packOf S Δ dom).redTm a) :
    Reducible S Δ (inst0 a cod) (packOf S Δ (inst0 a cod)) := by
  simpa using parts.codomain (World.refl formed) (a := a) (by simpa using ha)

theorem PolyParts.ext_self (parts : PolyParts S Δ dom cod) (formed : CtxFormed S.R Δ)
    {a b : Tm Head n} (ha : (packOf S Δ dom).redTm a) (hb : (packOf S Δ dom).redTm b)
    (hab : (packOf S Δ dom).eqTm a b) :
    (packOf S Δ (inst0 a cod)).eqTy (inst0 b cod) := by
  simpa using parts.ext (World.refl formed) (a := a) (b := b) (by simpa using ha)
    (by simpa using hb) (by simpa using hab)

variable (laws : S.E.Laws S.R S.roles)
include laws

/-- A fresh variable of the domain, and the codomain over it. -/
theorem PolyParts.fresh (parts : PolyParts S Δ dom cod) (formed : CtxFormed S.R Δ) :
    World S Δ (.snoc Δ dom) wk ∧
      (packOf S (.snoc Δ dom) (Presentation.rename wk dom)).redTm (.var 0) ∧
        Reducible S (.snoc Δ dom) (inst0 (.var 0) (Presentation.rename (liftRen wk) cod))
          (packOf S (.snoc Δ dom) (inst0 (.var 0) (Presentation.rename (liftRen wk) cod))) := by
  have w := World.snoc formed parts.domType
  have rdom := parts.domain w
  have typing : Typed S.R (.snoc Δ dom) (.var 0) (Presentation.rename wk dom) := .var 0
  have h0 := (rdom.reflects laws).redTm (.var 0) typing (laws.convNe_var 0 typing)
  exact ⟨w, h0, parts.codomain w h0⟩

/-- A term reducing to a function whose applications are reducible, and equal at
equal arguments, is a reducible function. -/
theorem PolyParts.piRedTm_intro (parts : PolyParts S Δ dom cod) (formed : CtxFormed S.R Δ)
    {t nf : Tm Head n} (red : RedTm S.R S.roles Δ t nf (.pi dom cod))
    (isFun : IsFun S.roles nf)
    (apps : ∀ {m : Nat} {Δ' : Ctx Head m} {ρ : Ren n m}, World S Δ Δ' ρ → ∀ {a : Tm Head m},
      (packOf S Δ' (Presentation.rename ρ dom)).redTm a →
      (packOf S Δ' (inst0 a (Presentation.rename (liftRen ρ) cod))).redTm
        (.app (Presentation.rename ρ nf) a))
    (appEqs : ∀ {m : Nat} {Δ' : Ctx Head m} {ρ : Ren n m}, World S Δ Δ' ρ →
      ∀ {a b : Tm Head m}, (packOf S Δ' (Presentation.rename ρ dom)).redTm a →
      (packOf S Δ' (Presentation.rename ρ dom)).redTm b →
      (packOf S Δ' (Presentation.rename ρ dom)).eqTm a b →
      (packOf S Δ' (inst0 a (Presentation.rename (liftRen ρ) cod))).eqTm
        (.app (Presentation.rename ρ nf) a) (.app (Presentation.rename ρ nf) b)) :
    PiRedTm S (canonicalPoly S Δ dom cod parts.ext) t := by
  obtain ⟨w, h0, rcod⟩ := parts.fresh laws formed
  have c0 := ((rcod.escape laws).redTm (apps w h0)).2
  rw [inst0_var_rename_liftRen_wk] at c0
  exact ⟨nf, red, isFun,
    laws.convTm_etaPi parts.domType parts.codType red.target isFun red.target isFun c0,
    fun w' _ ha => apps w' ha, fun w' _ _ ha hb hab => appEqs w' ha hb hab⟩

/-- Reducible functions are equal when their applications are. -/
theorem PolyParts.pi_eqTm_of_apps (parts : PolyParts S Δ dom cod) (formed : CtxFormed S.R Δ)
    {t t' : Tm Head n} (redT : PiRedTm S (canonicalPoly S Δ dom cod parts.ext) t)
    (redT' : PiRedTm S (canonicalPoly S Δ dom cod parts.ext) t')
    (apps : ∀ {m : Nat} {Δ' : Ctx Head m} {ρ : Ren n m}, World S Δ Δ' ρ → ∀ {a : Tm Head m},
      (packOf S Δ' (Presentation.rename ρ dom)).redTm a →
      (packOf S Δ' (inst0 a (Presentation.rename (liftRen ρ) cod))).eqTm
        (.app (Presentation.rename ρ t) a) (.app (Presentation.rename ρ t') a)) :
    (piPack S Δ dom cod (canonicalPoly S Δ dom cod parts.ext)).eqTm t t' := by
  obtain ⟨nf, red, isFun, conv, appsN, appEqsN⟩ := redT
  obtain ⟨nf', red', isFun', conv', appsN', appEqsN'⟩ := redT'
  have pointwise : ∀ {m : Nat} {Δ' : Ctx Head m} {ρ : Ren n m} (w : World S Δ Δ' ρ)
      {a : Tm Head m} (ha : (packOf S Δ' (Presentation.rename ρ dom)).redTm a),
      (packOf S Δ' (inst0 a (Presentation.rename (liftRen ρ) cod))).eqTm
        (.app (Presentation.rename ρ nf) a) (.app (Presentation.rename ρ nf') a) := by
    intro m Δ' ρ w a ha
    have rcod := parts.codomain w ha
    have ta := ((parts.domain w).escape laws |>.redTm ha).1
    have e₁ := (rcod.redTm_expand ((red.rename w.1).app ta) (appsN w ha)).2
    have e₂ := (rcod.redTm_expand ((red'.rename w.1).app ta) (appsN' w ha)).2
    exact rcod.eqTm_trans laws (rcod.eqTm_symm laws e₁)
      (rcod.eqTm_trans laws (apps w ha) e₂)
  obtain ⟨w, h0, rcod⟩ := parts.fresh laws formed
  have c0 := (rcod.escape laws).eqTm (pointwise w h0)
  rw [inst0_var_rename_liftRen_wk] at c0
  exact ⟨⟨nf, red, isFun, conv, appsN, appEqsN⟩, ⟨nf', red', isFun', conv', appsN', appEqsN'⟩,
    nf, nf', red, red', isFun, isFun',
    laws.convTm_etaPi parts.domType parts.codType red.target isFun red'.target isFun' c0,
    fun w' _ ha => pointwise w' ha⟩

/-- Applying a reducible function to a reducible argument. -/
theorem PolyParts.app_redTm (parts : PolyParts S Δ dom cod) (formed : CtxFormed S.R Δ)
    {f a : Tm Head n} (hf : PiRedTm S (canonicalPoly S Δ dom cod parts.ext) f)
    (ha : (packOf S Δ dom).redTm a) : (packOf S Δ (inst0 a cod)).redTm (.app f a) := by
  obtain ⟨nf, red, _, _, apps, _⟩ := hf
  have happ := apps (World.refl formed) (a := a) (by simpa using ha)
  simp only [canonicalPoly_codPack, liftRen_id, rename_id] at happ
  have ta := ((parts.dom_self formed).escape laws |>.redTm ha).1
  exact ((parts.cod_self formed ha).redTm_expand (red.app ta) happ).1

/-- Applying reducibly equal functions to reducibly equal arguments. -/
theorem PolyParts.app_eqTm (parts : PolyParts S Δ dom cod) (formed : CtxFormed S.R Δ)
    {f f' a a' : Tm Head n}
    (hf : (piPack S Δ dom cod (canonicalPoly S Δ dom cod parts.ext)).eqTm f f')
    (ha : (packOf S Δ dom).redTm a) (ha' : (packOf S Δ dom).redTm a')
    (haa : (packOf S Δ dom).eqTm a a') :
    (packOf S Δ (inst0 a cod)).eqTm (.app f a) (.app f' a') := by
  obtain ⟨_, ⟨nf₂, red₂, isFun₂, _, _, appEqs₂⟩, nf, nf', red, red', _, isFun', _, pointwise⟩ := hf
  have same : nf₂ = nf' := RedTm.unique (S := S) red₂ red' (IsFun.whnf isFun₂) (IsFun.whnf isFun')
  subst same
  have rC := parts.cod_self formed ha
  have ta := ((parts.dom_self formed).escape laws |>.redTm ha).1
  have ta' := ((parts.dom_self formed).escape laws |>.redTm ha').1
  have p := pointwise (World.refl formed) (a := a) (by simpa using ha)
  simp only [canonicalPoly_codPack, liftRen_id, rename_id] at p
  obtain ⟨hn, _⟩ := rC.eqTm_redTm laws p
  have e₁ := (rC.redTm_expand (red.app ta) hn).2
  have e₂ := appEqs₂ (World.refl formed) (a := a) (b := a') (by simpa using ha)
    (by simpa using ha') (by simpa using haa)
  simp only [canonicalPoly_codPack, liftRen_id, rename_id] at e₂
  obtain ⟨_, hn'⟩ := rC.eqTm_redTm laws e₂
  have typeEq : TypeEq S.R Δ (inst0 a' cod) (inst0 a cod) :=
    (laws.convTy_sound ((rC.escape laws).eqTy (parts.ext_self formed ha ha' haa))).symm
  have e₃ := (rC.redTm_expand ((red₂.app ta').conv typeEq) hn').2
  exact rC.eqTm_trans laws e₁ (rC.eqTm_trans laws p (rC.eqTm_trans laws e₂ (rC.eqTm_symm laws e₃)))

end Parts

/-! ## Inversion -/

section Inversion

variable (laws : S.E.Laws S.R S.roles)
include laws

/-- A valid dependent function type has a valid domain and codomain. -/
theorem ValidTy.pi_inv {n : Nat} {Γ : Ctx Head n} {A : Tm Head n} {B : Tm Head (n + 1)}
    (valid : ValidTy S Γ (.pi A B)) : ValidTy S Γ A ∧ ValidTy S (.snoc Γ A) B := by
  have validA : ValidTy S Γ A := by
    refine ⟨fun {m Δ σ} vσ => ?_, fun {m Δ σ σ'} vσ vσ' e P r => ?_⟩
    · obtain ⟨P, rP⟩ := valid.red vσ
      obtain ⟨parts, _, _⟩ := Reducible.pi_view laws rP
      exact ⟨_, parts.dom_self vσ.formed⟩
    · obtain ⟨Q, rQ⟩ := valid.red vσ
      have eqPi := valid.ext vσ vσ' e rQ
      obtain ⟨parts, rfl, _⟩ := Reducible.pi_view laws rQ
      obtain ⟨dom', cod', red', _, domEq, _⟩ := eqPi
      have shape : Tm.pi dom' cod' =
          Tm.pi (Presentation.subst σ' A) (Presentation.subst (liftSub σ') B) :=
        WhRed.eq_of_whnf (pi_whnf S.shape _ _) red'.red
      obtain ⟨rfl, rfl⟩ := Tm.pi.inj shape
      have h := domEq (World.refl vσ.formed)
      simp only [canonicalPoly_domPack, rename_id] at h
      rwa [r.eq_packOf laws]
  refine ⟨validA, fun {m Δ τ} vτ => ?_, fun {m Δ τ τ'} vτ vτ' e P r => ?_⟩
  · obtain ⟨tail, PA, rA, h0⟩ := vτ
    obtain ⟨Q, rQ⟩ := valid.red tail
    obtain ⟨parts, _, _⟩ := Reducible.pi_view laws rQ
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
    have eqPi := valid.ext tail tail' etail rQ
    obtain ⟨parts, rfl, _⟩ := Reducible.pi_view laws rQ
    obtain ⟨Q', rQ'⟩ := valid.red tail'
    obtain ⟨parts', _, _⟩ := Reducible.pi_view laws rQ'
    obtain ⟨dom', cod', red', _, _, codEq⟩ := eqPi
    have shape : Tm.pi dom' cod' =
        Tm.pi (Presentation.subst (tailSub τ') A) (Presentation.subst (liftSub (tailSub τ')) B) :=
      WhRed.eq_of_whnf (pi_whnf S.shape _ _) red'.red
    obtain ⟨rfl, rfl⟩ := Tm.pi.inj shape
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

end Inversion

/-! ## Application -/

section Application

variable (laws : S.E.Laws S.R S.roles)
include laws

omit laws in
theorem subst_consSub_app_wk {n m : Nat} (a : Tm Head m) (σ : Sub Head n m) (f : Tm Head n) :
    Presentation.subst (consSub a σ) (.app (Presentation.rename wk f) (.var 0)) =
      .app (Presentation.subst σ f) a := by
  show Tm.app (Presentation.subst (consSub a σ) (Presentation.rename wk f)) (consSub a σ 0) = _
  rw [subst_consSub_rename_wk]
  rfl

omit laws in
/-- Instantiating a valid type at validly equal terms. -/
theorem ValidTy.instantiate_eq {n : Nat} {Γ : Ctx Head n} {A a a' : Tm Head n}
    {B : Tm Head (n + 1)} (validA : ValidTy S Γ A) (validB : ValidTy S (.snoc Γ A) B)
    (equal : ValidEq S Γ a a' A) : ValidTyEq S Γ (inst0 a B) (inst0 a' B) := by
  refine ⟨validB.instantiate equal.left, validB.instantiate equal.right, fun {m Δ σ} vσ P r => ?_⟩
  rw [subst_inst0_consSub] at r ⊢
  obtain ⟨PA, rA⟩ := validA.red vσ
  exact validB.ext (equal.left.extend vσ) (equal.right.extend vσ)
    (vσ.refl.cons rA (equal.eq vσ rA)) r

/-- Application. -/
theorem ValidTm.app {n : Nat} {Γ : Ctx Head n} {g a A : Tm Head n} {B : Tm Head (n + 1)}
    (validG : ValidTm S Γ g (.pi A B)) (validA : ValidTm S Γ a A) :
    ValidTm S Γ (.app g a) (inst0 a B) := by
  obtain ⟨_, validTyB⟩ := validG.type.pi_inv laws
  refine ⟨validTyB.instantiate validA, fun {m Δ σ} vσ P r => ?_, fun {m Δ σ σ'} vσ vσ' e P r => ?_⟩
  · obtain ⟨Q, rQ⟩ := validG.type.red vσ
    have hg := validG.red vσ rQ
    obtain ⟨parts, rfl, _⟩ := Reducible.pi_view laws rQ
    have result := parts.app_redTm laws vσ.formed hg (validA.red vσ (parts.dom_self vσ.formed))
    rw [subst_inst0] at r
    rw [r.eq_packOf laws]
    exact result
  · obtain ⟨Q, rQ⟩ := validG.type.red vσ
    have hgg := validG.ext vσ vσ' e rQ
    obtain ⟨parts, rfl, _⟩ := Reducible.pi_view laws rQ
    have rA := parts.dom_self vσ.formed
    have haa := validA.ext vσ vσ' e rA
    have result := parts.app_eqTm laws vσ.formed hgg (validA.red vσ rA)
      (rA.eqTm_redTm laws haa).2 haa
    rw [subst_inst0] at r
    rw [r.eq_packOf laws]
    exact result

/-- Congruence of application. -/
theorem ValidEq.app {n : Nat} {Γ : Ctx Head n} {g g' a a' A : Tm Head n}
    {B : Tm Head (n + 1)} (equalG : ValidEq S Γ g g' (.pi A B)) (equalA : ValidEq S Γ a a' A) :
    ValidEq S Γ (.app g a) (.app g' a') (inst0 a B) := by
  obtain ⟨validTyA, validTyB⟩ := equalG.left.type.pi_inv laws
  have right := (equalG.right.app laws equalA.right).conv laws
    (ValidTyEq.symm laws (validTyA.instantiate_eq validTyB equalA))
  refine ⟨equalG.left.app laws equalA.left, right, fun {m Δ σ} vσ P r => ?_⟩
  obtain ⟨Q, rQ⟩ := equalG.left.type.red vσ
  have hgg := equalG.eq vσ rQ
  obtain ⟨parts, rfl, _⟩ := Reducible.pi_view laws rQ
  have rA := parts.dom_self vσ.formed
  have haa := equalA.eq vσ rA
  have result := parts.app_eqTm laws vσ.formed hgg (equalA.left.red vσ rA)
    (rA.eqTm_redTm laws haa).2 haa
  rw [subst_inst0] at r
  rw [r.eq_packOf laws]
  exact result

end Application

/-! ## Abstraction -/

section Abstraction

variable (laws : S.E.Laws S.R S.roles)
include laws

/-- The applications of an abstraction with a valid body, at a valid
substitution and in every world: reducible, and equal to the instantiated
body. -/
theorem ValidTm.lam_app {n : Nat} {Γ : Ctx Head n} {A : Tm Head n}
    {body B : Tm Head (n + 1)} {u : Head} (validPi : ValidTm S Γ (.pi A B) (.head u))
    (hu : S.R.isUniverse u) (validBody : ValidTm S (.snoc Γ A) body B) {m : Nat}
    {Δ : Ctx Head m} {σ : Sub Head n m} (vσ : ValidSubst S Γ Δ σ) {k : Nat}
    {Δ' : Ctx Head k} {ρ : Ren m k} (w : World S Δ Δ' ρ) {a : Tm Head k}
    (ha : (packOf S Δ' (Presentation.rename ρ (Presentation.subst σ A))).redTm a) :
    (packOf S Δ' (inst0 a (Presentation.rename (liftRen ρ)
        (Presentation.subst (liftSub σ) B)))).redTm
        (.app (Presentation.rename ρ (Presentation.subst σ (.lam body))) a) ∧
      (packOf S Δ' (inst0 a (Presentation.rename (liftRen ρ)
        (Presentation.subst (liftSub σ) B)))).eqTm
        (.app (Presentation.rename ρ (Presentation.subst σ (.lam body))) a)
        (Presentation.subst (consSub a fun i => Presentation.rename ρ (σ i)) body) := by
  obtain ⟨validTyA, validTyB⟩ := (validPi.validTy laws hu).pi_inv laws
  obtain ⟨tPi, _, _⟩ := validPi.universe_at laws hu vσ
  obtain ⟨PA, rA⟩ := validTyA.red vσ
  have vlift := vσ.lift laws rA
  obtain ⟨PB, rB⟩ := validTyB.red vlift
  have tb := ((rB.escape laws).redTm (validBody.red vlift rB)).1
  obtain ⟨PA', rA', hPA⟩ := ha
  have ta := ((rA'.escape laws).redTm hPA).1
  rw [rename_subst] at rA'
  have vτ := (vσ.weaken laws w).cons rA' hPA
  obtain ⟨PC, rC⟩ := validTyB.red vτ
  have hbody := validBody.red vτ rC
  have red := RedTm.beta (roles := S.roles) (tPi.rename w.1) hu (tb.rename (w.1.snoc _)) ta
  rw [inst0_rename_subst_liftSub, inst0_rename_subst_liftSub] at red
  rw [inst0_rename_subst_liftSub, ← rC.eq_packOf laws]
  exact rC.redTm_expand red hbody

/-- Abstraction. -/
theorem ValidTm.lam {n : Nat} {Γ : Ctx Head n} {A : Tm Head n} {body B : Tm Head (n + 1)}
    {u : Head} (validPi : ValidTm S Γ (.pi A B) (.head u)) (hu : S.R.isUniverse u)
    (validBody : ValidTm S (.snoc Γ A) body B) : ValidTm S Γ (.lam body) (.pi A B) := by
  have validTyPi := validPi.validTy laws hu
  obtain ⟨validTyA, validTyB⟩ := validTyPi.pi_inv laws
  have red : ∀ {m : Nat} {Δ : Ctx Head m} {σ : Sub Head n m}, ValidSubst S Γ Δ σ →
      ∀ {P}, Reducible S Δ (Presentation.subst σ (.pi A B)) P →
        P.redTm (Presentation.subst σ (.lam body)) := by
    intro m Δ σ vσ P r
    obtain ⟨parts, rfl, _⟩ := Reducible.pi_view laws r
    obtain ⟨tPi, _, _⟩ := validPi.universe_at laws hu vσ
    have vlift := vσ.lift laws (parts.dom_self vσ.formed)
    obtain ⟨PB, rB⟩ := validTyB.red vlift
    have tb := ((rB.escape laws).redTm (validBody.red vlift rB)).1
    refine parts.piRedTm_intro laws vσ.formed (RedTm.refl (.lamIntro tPi hu tb))
      (.inl ⟨_, rfl⟩) (fun w _ ha => (validPi.lam_app laws hu validBody vσ w ha).1) ?_
    intro k Δ' ρ w a b ha hb hab
    have ea := (validPi.lam_app laws hu validBody vσ w ha).2
    have eb := (validPi.lam_app laws hu validBody vσ w hb).2
    have rCa := parts.codomain w ha
    have rCb := parts.codomain w hb
    have same := rCa.conv laws rCb (parts.ext w ha hb hab)
    rw [← same] at eb
    obtain ⟨PA, rA, hPA⟩ := ha
    obtain ⟨PA₂, rA₂, hPB⟩ := hb
    obtain ⟨PA₃, rA₃, hPAB⟩ := hab
    have e₂ := rA.unique laws rA₂
    have e₃ := rA.unique laws rA₃
    subst e₂ e₃
    rw [rename_subst] at rA
    have vρσ := vσ.weaken laws w
    have mid := validBody.ext (vρσ.cons rA hPA) (vρσ.cons rA hPB) (vρσ.refl.cons rA hPAB)
      (by rw [← inst0_rename_subst_liftSub a ρ σ B]; exact rCa)
    exact rCa.eqTm_trans laws ea (rCa.eqTm_trans laws mid (rCa.eqTm_symm laws eb))
  refine ⟨validTyPi, red, fun {m Δ σ σ'} vσ vσ' e P r => ?_⟩
  obtain ⟨Q', rQ'⟩ := validTyPi.red vσ'
  have samePi : P = Q' := validTyPi.pack_eq laws vσ vσ' e r rQ'
  have hlam := red vσ r
  have hlam' : P.redTm (Presentation.subst σ' (.lam body)) := samePi ▸ red vσ' rQ'
  obtain ⟨parts, rfl, _⟩ := Reducible.pi_view laws r
  refine parts.pi_eqTm_of_apps laws vσ.formed hlam hlam' ?_
  intro k Δ' ρ w a ha
  have e₁ := (validPi.lam_app laws hu validBody vσ w ha).2
  have vρσ := vσ.weaken laws w
  have vρσ' := vσ'.weaken laws w
  have eρ := e.weaken laws w
  obtain ⟨PA, rA, hPA⟩ := ha
  rw [rename_subst] at rA
  obtain ⟨PA', rA'⟩ := validTyA.red vρσ'
  have sameA : PA = PA' := validTyA.pack_eq laws vρσ vρσ' eρ rA rA'
  subst sameA
  have ha' : (packOf S Δ' (Presentation.rename ρ (Presentation.subst σ' A))).redTm a :=
    ⟨PA, by rw [rename_subst]; exact rA', hPA⟩
  have e₂ := (validPi.lam_app laws hu validBody vσ' w ha').2
  have vτ := vρσ.cons rA hPA
  have vτ' := vρσ'.cons rA' hPA
  have eτ := eρ.cons rA (rA.reflexive.eqTm hPA)
  obtain ⟨PC, rC⟩ := validTyB.red vτ
  obtain ⟨PC', rC'⟩ := validTyB.red vτ'
  have sameC : PC = PC' := validTyB.pack_eq laws vτ vτ' eτ rC rC'
  subst sameC
  have mid := validBody.ext vτ vτ' eτ rC
  rw [inst0_rename_subst_liftSub] at e₁ e₂ ⊢
  rw [← rC.eq_packOf laws] at e₁ ⊢
  rw [← rC'.eq_packOf laws] at e₂
  exact rC.eqTm_trans laws e₁ (rC.eqTm_trans laws mid (rC.eqTm_symm laws e₂))

/-- Congruence of abstraction. -/
theorem ValidEq.lam {n : Nat} {Γ : Ctx Head n} {A : Tm Head n} {body body' B : Tm Head (n + 1)}
    {u : Head} (validPi : ValidTm S Γ (.pi A B) (.head u)) (hu : S.R.isUniverse u)
    (equalBody : ValidEq S (.snoc Γ A) body body' B) :
    ValidEq S Γ (.lam body) (.lam body') (.pi A B) := by
  have left := validPi.lam laws hu equalBody.left
  have right := validPi.lam laws hu equalBody.right
  obtain ⟨_, validTyB⟩ := (validPi.validTy laws hu).pi_inv laws
  refine ⟨left, right, fun {m Δ σ} vσ P r => ?_⟩
  have h₁ := left.red vσ r
  have h₂ := right.red vσ r
  obtain ⟨parts, rfl, _⟩ := Reducible.pi_view laws r
  refine parts.pi_eqTm_of_apps laws vσ.formed h₁ h₂ ?_
  intro k Δ' ρ w a ha
  have e₁ := (validPi.lam_app laws hu equalBody.left vσ w ha).2
  have e₂ := (validPi.lam_app laws hu equalBody.right vσ w ha).2
  obtain ⟨PA, rA, hPA⟩ := ha
  rw [rename_subst] at rA
  have vτ := (vσ.weaken laws w).cons rA hPA
  obtain ⟨PC, rC⟩ := validTyB.red vτ
  have mid := equalBody.eq vτ rC
  rw [inst0_rename_subst_liftSub] at e₁ e₂ ⊢
  rw [← rC.eq_packOf laws] at e₁ e₂ ⊢
  exact rC.eqTm_trans laws e₁ (rC.eqTm_trans laws mid (rC.eqTm_symm laws e₂))

/-- β for functions. -/
theorem ValidEq.beta {n : Nat} {Γ : Ctx Head n} {A a : Tm Head n} {body B : Tm Head (n + 1)}
    {u : Head} (validPi : ValidTm S Γ (.pi A B) (.head u)) (hu : S.R.isUniverse u)
    (validBody : ValidTm S (.snoc Γ A) body B) (validArg : ValidTm S Γ a A) :
    ValidEq S Γ (.app (.lam body) a) (inst0 a body) (inst0 a B) := by
  refine ⟨(validPi.lam laws hu validBody).app laws validArg, validBody.instantiate validArg,
    fun {m Δ σ} vσ P r => ?_⟩
  obtain ⟨validTyA, _⟩ := (validPi.validTy laws hu).pi_inv laws
  obtain ⟨PA, rA⟩ := validTyA.red vσ
  have ha := validArg.red vσ rA
  have result := (validPi.lam_app laws hu validBody vσ (World.refl vσ.formed)
    (a := Presentation.subst σ a) ⟨PA, by rw [rename_id]; exact rA, ha⟩).2
  simp only [liftRen_id, rename_id] at result
  rw [subst_inst0] at r
  rw [r.eq_packOf laws, subst_inst0_consSub]
  exact result

/-- η for functions: functions are equal when their applications to a fresh
variable are. -/
theorem ValidEq.etaPi {n : Nat} {Γ : Ctx Head n} {f g A : Tm Head n} {B : Tm Head (n + 1)}
    (validF : ValidTm S Γ f (.pi A B)) (validG : ValidTm S Γ g (.pi A B))
    (equalApps : ValidEq S (.snoc Γ A) (.app (Presentation.rename wk f) (.var 0))
      (.app (Presentation.rename wk g) (.var 0)) B) :
    ValidEq S Γ f g (.pi A B) := by
  refine ⟨validF, validG, fun {m Δ σ} vσ P r => ?_⟩
  have hf := validF.red vσ r
  have hg := validG.red vσ r
  obtain ⟨parts, rfl, _⟩ := Reducible.pi_view laws r
  refine parts.pi_eqTm_of_apps laws vσ.formed hf hg ?_
  intro k Δ' ρ w a ha
  obtain ⟨PA, rA, hPA⟩ := ha
  rw [rename_subst] at rA
  have vτ := (vσ.weaken laws w).cons rA hPA
  obtain ⟨PB, rB⟩ := equalApps.left.type.red vτ
  have h := equalApps.eq vτ rB
  rw [subst_consSub_app_wk, subst_consSub_app_wk, ← rename_subst, ← rename_subst] at h
  rw [inst0_rename_subst_liftSub, ← rB.eq_packOf laws]
  exact h

end Abstraction


end Normalization
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
