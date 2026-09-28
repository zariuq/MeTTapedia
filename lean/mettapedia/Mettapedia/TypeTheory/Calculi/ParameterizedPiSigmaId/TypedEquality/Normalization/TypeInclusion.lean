import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.Rules

/-!
# Valid types, one usable at the other

`ValidTyLe S Γ A B` is what the subtyping statement `Γ ⊢ A ⊑ B` means in the
model: the statement is derivable, both types are valid, and at every valid
substitution the pack of `A` is included in the pack of `B`, for reducible
terms and for reducibly equal terms. Validity of a term and of an equality
transfers along it; it holds between validly equal types, between universes
by cumulativity, and it composes. The dependent function and pair cases are
the fundamental lemma's, where the codomain's inclusion is available at every
reducible argument.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Normalization

open UniverseLevel (LevelOrder)

variable {Head L : Type} [LevelOrder L] {S : Setting Head L}

/-- Valid types, the first usable at the second. -/
structure ValidTyLe (S : Setting Head L) {n : Nat} (Γ : Ctx Head n) (A B : Tm Head n) :
    Prop where
  below : Below S.R Γ A B
  left : ValidTy S Γ A
  right : ValidTy S Γ B
  redTm : ∀ {m : Nat} {Δ : Ctx Head m} {σ : Sub Head n m}, ValidSubst S Γ Δ σ →
    ∀ {P Q : Pack Head m}, Reducible S Δ (Presentation.subst σ A) P →
      Reducible S Δ (Presentation.subst σ B) Q → ∀ {t : Tm Head m}, P.redTm t → Q.redTm t
  eqTm : ∀ {m : Nat} {Δ : Ctx Head m} {σ : Sub Head n m}, ValidSubst S Γ Δ σ →
    ∀ {P Q : Pack Head m}, Reducible S Δ (Presentation.subst σ A) P →
      Reducible S Δ (Presentation.subst σ B) Q →
      ∀ {t t' : Tm Head m}, P.eqTm t t' → Q.eqTm t t'

/-- Validity at a type transfers to a type it is usable at. -/
theorem ValidTm.below {n : Nat} {Γ : Ctx Head n} {t A B : Tm Head n}
    (valid : ValidTm S Γ t A) (le : ValidTyLe S Γ A B) : ValidTm S Γ t B := by
  refine ⟨le.right, fun {m Δ σ} vσ Q rB => ?_, fun {m Δ σ σ'} vσ vσ' e Q rB => ?_⟩
  · obtain ⟨P, rA⟩ := le.left.red vσ
    exact le.redTm vσ rA rB (valid.red vσ rA)
  · obtain ⟨P, rA⟩ := le.left.red vσ
    exact le.eqTm vσ rA rB (valid.ext vσ vσ' e rA)

/-- A valid equality at a type holds at a type it is usable at. -/
theorem ValidEq.below {n : Nat} {Γ : Ctx Head n} {a b A B : Tm Head n}
    (valid : ValidEq S Γ a b A) (le : ValidTyLe S Γ A B) : ValidEq S Γ a b B := by
  refine ⟨valid.left.below le, valid.right.below le, fun {m Δ σ} vσ Q rB => ?_⟩
  obtain ⟨P, rA⟩ := le.left.red vσ
  exact le.eqTm vσ rA rB (valid.eq vσ rA)

/-- Usability composes. -/
theorem ValidTyLe.trans {n : Nat} {Γ : Ctx Head n} {A B C : Tm Head n}
    (le₁ : ValidTyLe S Γ A B) (le₂ : ValidTyLe S Γ B C) : ValidTyLe S Γ A C := by
  refine ⟨.subTrans le₁.below le₂.below, le₁.left, le₂.right,
    fun {m Δ σ} vσ P Q rA rC t h => ?_, fun {m Δ σ} vσ P Q rA rC t t' h => ?_⟩
  · obtain ⟨M, rB⟩ := le₁.right.red vσ
    exact le₂.redTm vσ rB rC (le₁.redTm vσ rA rB h)
  · obtain ⟨M, rB⟩ := le₁.right.red vσ
    exact le₂.eqTm vσ rB rC (le₁.eqTm vσ rA rB h)

section Laws

variable (laws : S.E.Laws S.R S.roles)
include laws

/-- Validly equal types are usable at each other. -/
theorem ValidTyLe.ofEq {n : Nat} {Γ : Ctx Head n} {A B : Tm Head n}
    (below : Below S.R Γ A B) (equal : ValidTyEq S Γ A B) : ValidTyLe S Γ A B := by
  refine ⟨below, equal.left, equal.right,
    fun {m Δ σ} vσ P Q rA rB t h => ?_, fun {m Δ σ} vσ P Q rA rB t t' h => ?_⟩
  · rwa [← equal.pack_eq laws vσ rA rB]
  · rwa [← equal.pack_eq laws vσ rA rB]

/-- A universe is usable at every universe cumulatively above it. -/
theorem ValidTyLe.univ {n : Nat} {Γ : Ctx Head n} {u v : Head} (c : S.R.cumulative u v) :
    ValidTyLe S Γ (.head u) (.head v) := by
  obtain ⟨hu, hv, _⟩ := S.levels.cumulative_universe c
  refine ⟨.subUniv c, ValidTy.universe hu, ValidTy.universe hv,
    fun {m Δ σ} vσ P Q rP rQ t h => ?_, fun {m Δ σ} vσ P Q rP rQ t t' h => ?_⟩
  · rw [universe_pack laws hu vσ.formed rP] at h
    rw [universe_pack laws hv vσ.formed rQ]
    exact universePack_cumul_redTm laws c h
  · rw [universe_pack laws hu vσ.formed rP] at h
    rw [universe_pack laws hv vσ.formed rQ]
    exact universePack_cumul_eqTm laws c h

end Laws

/-! ## Pack inclusion for dependent function and pair types

At a valid substitution both sides of a usability statement between
dependent function (pair) types are reducible with their canonical packs.
Inclusion of those packs is proved from the parts: equal domain packs and
included codomain packs for functions, included domain and codomain packs for
pairs. The typing and conversion evidence inside a reducible term is retyped
along the usability statement; the weak-head normal form itself is reused. -/

/-- One pack included in another, for reducible terms and reducibly equal
terms. -/
structure PackLe {n : Nat} (P Q : Pack Head n) : Prop where
  redTm : ∀ {t}, P.redTm t → Q.redTm t
  eqTm : ∀ {t u}, P.eqTm t u → Q.eqTm t u

/-- A typed reduction at a type is one at every type the type is usable at. -/
theorem RedTm.below {R : Rules Head} {roles : Roles Head} {n : Nat} {Γ : Ctx Head n}
    {t u A B : Tm Head n} (red : RedTm R roles Γ t u A) (le : Below R Γ A B) :
    RedTm R roles Γ t u B :=
  ⟨red.red, .sub red.source le, .sub red.target le, .subEq red.equal le⟩

/-- Valid substitutions are typed. -/
theorem ValidSubst.substMor (laws : S.E.Laws S.R S.roles) {n m : Nat} {Γ : Ctx Head n}
    {Δ : Ctx Head m} {σ : Sub Head n m} (valid : ValidSubst S Γ Δ σ) : SubstMor S.R Γ Δ σ := by
  intro i
  obtain ⟨P, r, h⟩ := valid.lookup i
  exact ((r.escape laws).redTm h).1

section Parts

variable {n : Nat} {Γ : Ctx Head n} {dom dom₂ : Tm Head n} {cod cod₂ : Tm Head (n + 1)}
  {P : PolyPack S Γ dom cod} {P₂ : PolyPack S Γ dom₂ cod₂}

/-- A dependent function type is usable at one with an equal domain and a
codomain it is usable at: its reducible and reducibly equal terms are terms of
the other. Applications are carried pointwise through the codomain
inclusion. -/
theorem piPack_below (laws : S.E.Laws S.R S.roles)
    (le : Below S.R Γ (.pi dom cod) (.pi dom₂ cod₂))
    (domain : ∀ {m : Nat} {Δ : Ctx Head m} {ρ : Ren n m} (w : World S Γ Δ ρ),
      PackEquiv (P.domPack w) (P₂.domPack w))
    (codomain : ∀ {m : Nat} {Δ : Ctx Head m} {ρ : Ren n m} (w : World S Γ Δ ρ)
      {a : Tm Head m} (ha : (P.domPack w).redTm a) (ha₂ : (P₂.domPack w).redTm a),
      PackLe (P.codPack w ha) (P₂.codPack w ha₂)) :
    PackLe (piPack S Γ dom cod P) (piPack S Γ dom₂ cod₂ P₂) := by
  have redForward : ∀ {t}, PiRedTm S P t → PiRedTm S P₂ t := by
    rintro t ⟨nf, redT, isFun, refl, apps, appEqs⟩
    refine ⟨nf, redT.below le, isFun, laws.convTm_below refl le, ?_, ?_⟩
    · intro m Δ ρ w a ha₂
      have ha := (domain w).redTm.mpr ha₂
      exact (codomain w ha ha₂).redTm (apps w ha)
    · intro m Δ ρ w a b ha₂ hb₂ eq₂
      have ha := (domain w).redTm.mpr ha₂
      exact (codomain w ha ha₂).eqTm
        (appEqs w ha ((domain w).redTm.mpr hb₂) ((domain w).eqTm.mpr eq₂))
  refine ⟨redForward, ?_⟩
  rintro t t' ⟨redT, redT', nf, nf', r, r', isFun, isFun', equal, apps⟩
  refine ⟨redForward redT, redForward redT', nf, nf', r.below le, r'.below le,
    isFun, isFun', laws.convTm_below equal le, ?_⟩
  intro m Δ ρ w a ha₂
  have ha := (domain w).redTm.mpr ha₂
  exact (codomain w ha ha₂).eqTm (apps w ha)

/-- A dependent pair type is usable at one whose domain and codomain it is
usable at. The first projection is carried through the domain inclusion, and
the second through the codomain inclusion at that same first projection. -/
theorem sigmaPack_below (laws : S.E.Laws S.R S.roles)
    (le : Below S.R Γ (.sigma dom cod) (.sigma dom₂ cod₂))
    (domain : ∀ {m : Nat} {Δ : Ctx Head m} {ρ : Ren n m} (w : World S Γ Δ ρ),
      PackLe (P.domPack w) (P₂.domPack w))
    (codomain : ∀ {m : Nat} {Δ : Ctx Head m} {ρ : Ren n m} (w : World S Γ Δ ρ)
      {a : Tm Head m} (ha : (P.domPack w).redTm a) (ha₂ : (P₂.domPack w).redTm a),
      PackLe (P.codPack w ha) (P₂.codPack w ha₂)) :
    PackLe (sigmaPack S Γ dom cod P) (sigmaPack S Γ dom₂ cod₂ P₂) := by
  have redForward : ∀ {t}, SigmaRedTm S P t → SigmaRedTm S P₂ t := by
    rintro t ⟨nf, redT, isPair, refl, first, second⟩
    refine ⟨nf, redT.below le, isPair, laws.convTm_below refl le,
      fun w => (domain w).redTm (first w), ?_⟩
    intro m Δ ρ w
    exact (codomain w (first w) _).redTm (second w)
  refine ⟨redForward, ?_⟩
  rintro t t' ⟨redT, redT', nf, nf', r, r', isPair, isPair', equal, firsts, seconds⟩
  refine ⟨redForward redT, redForward redT', nf, nf', r.below le, r'.below le,
    isPair, isPair', laws.convTm_below equal le, fun w => (domain w).eqTm (firsts w), ?_⟩
  intro m Δ ρ w first₂
  obtain ⟨nf₀, r₀, isPair₀, _, first, _⟩ := redT
  have same : nf₀ = nf := RedTm.unique r₀ r isPair₀.whnf isPair.whnf
  subst same
  exact (codomain w (first w) first₂).eqTm (seconds w (first w))

end Parts

/-! ## Valid usability of dependent function and pair types -/

section Formers

variable (laws : S.E.Laws S.R S.roles)
include laws

/-- The codomain packs of two dependent function or pair types over one
domain, at a valid substitution renamed into a world and extended by a
reducible argument, are included when the codomains are validly usable one at
the other. -/
theorem ValidTyLe.codomain_at {n m k : Nat} {Γ : Ctx Head n} {A : Tm Head n}
    {B B' : Tm Head (n + 1)} (codomain : ValidTyLe S (.snoc Γ A) B B') {Δ : Ctx Head m}
    {σ : Sub Head n m} (vσ : ValidSubst S Γ Δ σ) {Θ : Ctx Head k} {ρ : Ren m k}
    (w : World S Δ Θ ρ) {a : Tm Head k}
    (rA : Reducible S Θ (Presentation.rename ρ (Presentation.subst σ A))
      (packOf S Θ (Presentation.rename ρ (Presentation.subst σ A))))
    (ha : (packOf S Θ (Presentation.rename ρ (Presentation.subst σ A))).redTm a)
    (rB : Reducible S Θ (inst0 a (Presentation.rename (liftRen ρ) (Presentation.subst (liftSub σ) B)))
      (packOf S Θ (inst0 a (Presentation.rename (liftRen ρ) (Presentation.subst (liftSub σ) B)))))
    (rB' : Reducible S Θ (inst0 a (Presentation.rename (liftRen ρ) (Presentation.subst (liftSub σ) B')))
      (packOf S Θ (inst0 a (Presentation.rename (liftRen ρ) (Presentation.subst (liftSub σ) B'))))) :
    PackLe (packOf S Θ (inst0 a (Presentation.rename (liftRen ρ) (Presentation.subst (liftSub σ) B))))
      (packOf S Θ (inst0 a (Presentation.rename (liftRen ρ) (Presentation.subst (liftSub σ) B')))) := by
  have vρσ := vσ.weaken laws w
  rw [rename_subst] at rA ha
  have vx := vρσ.cons rA ha
  rw [inst0_rename_subst_liftSub] at rB rB' ⊢
  rw [inst0_rename_subst_liftSub]
  exact ⟨codomain.redTm vx rB rB', codomain.eqTm vx rB rB'⟩

/-- The dependent function type over a domain is usable at the one over a
validly equal domain whose codomain its codomain is usable at. -/
theorem ValidTyLe.pi {n : Nat} {Γ : Ctx Head n} {A A' : Tm Head n} {B B' : Tm Head (n + 1)}
    (below : Below S.R Γ (.pi A B) (.pi A' B'))
    (validPi : ValidTy S Γ (.pi A B)) (validPi' : ValidTy S Γ (.pi A' B'))
    (domain : ValidTyEq S Γ A A') (codomain : ValidTyLe S (.snoc Γ A) B B') :
    ValidTyLe S Γ (.pi A B) (.pi A' B') := by
  have inclusion : ∀ {m : Nat} {Δ : Ctx Head m} {σ : Sub Head n m}, ValidSubst S Γ Δ σ →
      ∀ {P Q : Pack Head m}, Reducible S Δ (Presentation.subst σ (.pi A B)) P →
        Reducible S Δ (Presentation.subst σ (.pi A' B')) Q → PackLe P Q := by
    intro m Δ σ vσ P Q rP rQ
    have rP' : Reducible S Δ
        (.pi (Presentation.subst σ A) (Presentation.subst (liftSub σ) B)) P := rP
    have rQ' : Reducible S Δ
        (.pi (Presentation.subst σ A') (Presentation.subst (liftSub σ) B')) Q := rQ
    obtain ⟨partsP, rfl, _⟩ := Reducible.pi_view laws rP'
    obtain ⟨partsQ, rfl, _⟩ := Reducible.pi_view laws rQ'
    refine piPack_below laws (Derivable.substitutes below (vσ.substMor laws)) ?_ ?_
    · intro k Θ ρ w
      have vρσ := vσ.weaken laws w
      obtain ⟨PA, rA⟩ := domain.left.red vρσ
      obtain ⟨PA', rA'⟩ := domain.right.red vρσ
      have e := domain.pack_eq laws vρσ rA rA'
      show PackEquiv (packOf S Θ (Presentation.rename ρ (Presentation.subst σ A)))
        (packOf S Θ (Presentation.rename ρ (Presentation.subst σ A')))
      rw [rename_subst, rename_subst, ← rA.eq_packOf laws, ← rA'.eq_packOf laws, e]
      exact PackEquiv.refl _
    · intro k Θ ρ w a ha ha₂
      exact ValidTyLe.codomain_at laws codomain vσ w (partsP.domain w) ha
        (partsP.codomain w ha) (partsQ.codomain w ha₂)
  exact ⟨below, validPi, validPi', fun vσ _ _ rP rQ _ h => (inclusion vσ rP rQ).redTm h,
    fun vσ _ _ rP rQ _ _ h => (inclusion vσ rP rQ).eqTm h⟩

/-- The dependent pair type over a domain is usable at the one over a domain
it is usable at, whose codomain its codomain is usable at. -/
theorem ValidTyLe.sigma {n : Nat} {Γ : Ctx Head n} {A A' : Tm Head n}
    {B B' : Tm Head (n + 1)} (below : Below S.R Γ (.sigma A B) (.sigma A' B'))
    (validSigma : ValidTy S Γ (.sigma A B)) (validSigma' : ValidTy S Γ (.sigma A' B'))
    (domain : ValidTyLe S Γ A A') (codomain : ValidTyLe S (.snoc Γ A) B B') :
    ValidTyLe S Γ (.sigma A B) (.sigma A' B') := by
  have inclusion : ∀ {m : Nat} {Δ : Ctx Head m} {σ : Sub Head n m}, ValidSubst S Γ Δ σ →
      ∀ {P Q : Pack Head m}, Reducible S Δ (Presentation.subst σ (.sigma A B)) P →
        Reducible S Δ (Presentation.subst σ (.sigma A' B')) Q → PackLe P Q := by
    intro m Δ σ vσ P Q rP rQ
    have rP' : Reducible S Δ
        (.sigma (Presentation.subst σ A) (Presentation.subst (liftSub σ) B)) P := rP
    have rQ' : Reducible S Δ
        (.sigma (Presentation.subst σ A') (Presentation.subst (liftSub σ) B')) Q := rQ
    obtain ⟨partsP, rfl, _⟩ := Reducible.sigma_view laws rP'
    obtain ⟨partsQ, rfl, _⟩ := Reducible.sigma_view laws rQ'
    refine sigmaPack_below laws (Derivable.substitutes below (vσ.substMor laws)) ?_ ?_
    · intro k Θ ρ w
      have vρσ := vσ.weaken laws w
      have rA := partsP.domain w
      have rA' := partsQ.domain w
      rw [rename_subst] at rA rA'
      show PackLe (packOf S Θ (Presentation.rename ρ (Presentation.subst σ A)))
        (packOf S Θ (Presentation.rename ρ (Presentation.subst σ A')))
      rw [rename_subst, rename_subst]
      exact ⟨domain.redTm vρσ rA rA', domain.eqTm vρσ rA rA'⟩
    · intro k Θ ρ w a ha ha₂
      exact ValidTyLe.codomain_at laws codomain vσ w (partsP.domain w) ha
        (partsP.codomain w ha) (partsQ.codomain w ha₂)
  exact ⟨below, validSigma, validSigma', fun vσ _ _ rP rQ _ h => (inclusion vσ rP rQ).redTm h,
    fun vσ _ _ rP rQ _ _ h => (inclusion vσ rP rQ).eqTm h⟩

end Formers

end Normalization
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
