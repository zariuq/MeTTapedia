import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.Fundamental
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TelescopeAbstraction

/-!
# Semantic computing constants

A computing constant of arity `k` is declared at the dependent function type
of a telescope `Θ` of length `k` with a body `C`. It is semantic when its full
application to the variables of `Θ` is a valid term of `C` in `Θ`: a function
whose application to a fresh variable is valid is itself valid, and a partial
application of a computing constant is a function in weak-head normal form, so
validity passes from the full application to the constant one argument at a
time.

Validity of the full application is the content specific to each constant:
the computation rule of the eliminator, a recursor, or a definition.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Normalization

open TelescopeAbstraction (closeType applyClosed applyClosed_subst liftClosed_zero)

open UniverseLevel (LevelOrder)

variable {Head L : Type} [LevelOrder L]

/-! ## Applications to telescopes -/

/-- The arguments of an application to a telescope, in telescope order. -/
def telescopeArgs : {n m : Nat} → Ctx Head n → Sub Head n m → List (Tm Head m)
  | _, _, .nil, _ => []
  | _, _, .snoc Θ _, σ => telescopeArgs Θ (tailSub σ) ++ [σ 0]

theorem telescopeArgs_length {n m : Nat} (Θ : Ctx Head n) (σ : Sub Head n m) :
    (telescopeArgs Θ σ).length = n := by
  induction Θ with
  | nil => rfl
  | snoc Θ _ ih => simp [telescopeArgs, ih]

theorem applyClosed_eq_appSpine {n m : Nat} (Θ : Ctx Head n) (σ : Sub Head n m)
    (f : Tm Head m) : applyClosed Θ σ f = appSpine f (telescopeArgs Θ σ) := by
  induction Θ with
  | nil => rfl
  | snoc Θ _ ih =>
      show Tm.app (applyClosed Θ (tailSub σ) f) (σ 0) = _
      rw [ih, telescopeArgs, appSpine_concat]

/-- The application of a closed constant to the variables of a telescope, substituted. -/
theorem subst_applyClosed_const {n m : Nat} (Θ : Ctx Head n) (σ : Sub Head n m) (c : DeclName) :
    Presentation.subst σ (applyClosed Θ ids (liftClosed (.const c))) =
      appSpine (.const c) (telescopeArgs Θ σ) := by
  rw [applyClosed_subst, applyClosed_eq_appSpine]
  rfl

theorem rename_applyClosed {n m k : Nat} (Θ : Ctx Head n) (σ : Sub Head n m) (ρ : Ren m k)
    (f : Tm Head m) :
    Presentation.rename ρ (applyClosed Θ σ f) =
      applyClosed Θ (fun i => Presentation.rename ρ (σ i)) (Presentation.rename ρ f) := by
  rw [← subst_renSub, applyClosed_subst, subst_renSub]
  congr 1
  funext i
  exact subst_renSub ρ (σ i)

variable {R : Rules Head}

theorem SubstMor.tail {n m : Nat} {Θ : Ctx Head n} {A : Tm Head n} {Δ : Ctx Head m}
    {σ : Sub Head (n + 1) m} (typed : SubstMor R (.snoc Θ A) Δ σ) :
    SubstMor R Θ Δ (tailSub σ) := by
  intro i
  have h := typed i.succ
  rwa [Ctx.lookup_snoc_succ, subst_rename_wk] at h

theorem SubstMor.cons {n m : Nat} {Θ : Ctx Head n} {A : Tm Head n} {Δ : Ctx Head m}
    {σ : Sub Head n m} {a : Tm Head m} (typed : SubstMor R Θ Δ σ)
    (head : Typed R Δ a (Presentation.subst σ A)) : SubstMor R (.snoc Θ A) Δ (consSub a σ) := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [Ctx.lookup_snoc_zero, subst_consSub_rename_wk]
    exact head
  · rw [Ctx.lookup_snoc_succ, subst_consSub_rename_wk]
    exact typed j

/-- Applying a function typed at the dependent function type of a telescope to a
typed substitution of the telescope. -/
theorem Typed.telescope_apply {n m : Nat} {Θ : Ctx Head n} {Δ : Ctx Head m}
    {σ : Sub Head n m} {f : Tm Head m} {X : Tm Head n} (typed : SubstMor R Θ Δ σ)
    (function : Typed R Δ f (liftClosed (closeType Θ X))) :
    Typed R Δ (applyClosed Θ σ f) (Presentation.subst σ X) := by
  induction Θ with
  | nil =>
      show Typed R Δ f (Presentation.subst σ X)
      rw [subst_closed]
      exact function
  | @snoc n Θ A ih =>
      have earlier := ih (σ := tailSub σ) (X := .pi A X) (SubstMor.tail typed) function
      have argument := typed 0
      rw [Ctx.lookup_snoc_zero, subst_rename_wk] at argument
      have application := Derivable.appElim earlier argument
      rw [inst0_subst_liftSub, consSub_tailSub] at application
      exact application

/-- A closed typing holds in every context. -/
theorem Typed.liftClosed {m : Nat} {Δ : Ctx Head m} {t T : Tm Head 0}
    (typing : Typed R .nil t T) : Typed R Δ (liftClosed t) (liftClosed T) := by
  have h := typing.substitute (Δ := Δ) (σ := fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
  rwa [subst_closed, subst_closed] at h

variable {S : Setting Head L}

/-! ## Stuck applications -/

/-- Two applications to telescope substitutions with convertible arguments have
convertible head spines. -/
theorem convNe_telescope_apply (laws : S.E.Laws S.R S.roles) {n m : Nat} {Θ : Ctx Head n}
    {Δ : Ctx Head m} {σ τ : Sub Head n m} {f g : Tm Head m} {X : Tm Head n}
    (conv : ∀ i, S.E.convTm Δ (σ i) (τ i) (Presentation.subst σ (Ctx.lookup Θ i)))
    (head : S.E.convNe Δ f g (liftClosed (closeType Θ X))) :
    S.E.convNe Δ (applyClosed Θ σ f) (applyClosed Θ τ g) (Presentation.subst σ X) := by
  induction Θ with
  | nil =>
      show S.E.convNe Δ f g (Presentation.subst σ X)
      rw [subst_closed]
      exact head
  | @snoc n Θ E ih =>
      have conv' : ∀ i, S.E.convTm Δ (tailSub σ i) (tailSub τ i)
          (Presentation.subst (tailSub σ) (Ctx.lookup Θ i)) := by
        intro i
        have h := conv i.succ
        rwa [Ctx.lookup_snoc_succ, subst_rename_wk] at h
      have earlier := ih (σ := tailSub σ) (τ := tailSub τ) (X := .pi E X) conv' head
      have argument := conv 0
      rw [Ctx.lookup_snoc_zero, subst_rename_wk] at argument
      have application := laws.convNe_app earlier argument
      rw [inst0_subst_liftSub, consSub_tailSub] at application
      exact application

/-! ## Valid functions from valid applications -/

/-- The telescope of a valid closed dependent function type is a valid context,
and its body is valid in it. -/
theorem ValidTy.telescope (laws : S.E.Laws S.R S.roles) :
    ∀ {n : Nat} (Θ : Ctx Head n) {X : Tm Head n}, ValidTy S .nil (closeType Θ X) →
      ValidCtx S Θ ∧ ValidTy S Θ X
  | _, .nil, _, valid => ⟨trivial, valid⟩
  | _, .snoc Θ A, X, valid => by
      obtain ⟨validΘ, validPi⟩ := ValidTy.telescope laws Θ (X := .pi A X) valid
      obtain ⟨validA, validX⟩ := validPi.pi_inv laws
      exact ⟨⟨validΘ, validA⟩, validX⟩

/-- A function in weak-head normal form whose application to a fresh variable is
valid is a valid function. -/
theorem ValidTm.of_apps (laws : S.E.Laws S.R S.roles) {n : Nat} {Γ : Ctx Head n}
    {g A : Tm Head n} {B : Tm Head (n + 1)} (validPi : ValidTy S Γ (.pi A B))
    (shape : ∀ {m : Nat} {Δ : Ctx Head m} {σ : Sub Head n m}, ValidSubst S Γ Δ σ →
      Typed S.R Δ (Presentation.subst σ g) (Presentation.subst σ (.pi A B)) ∧
        IsFun S.roles (Presentation.subst σ g))
    (validApp : ValidTm S (.snoc Γ A) (.app (Presentation.rename wk g) (.var 0)) B) :
    ValidTm S Γ g (.pi A B) := by
  obtain ⟨validTyA, validTyB⟩ := validPi.pi_inv laws
  /- The applications of the function in every world are valid applications. -/
  have app_eq : ∀ {m k : Nat} {σ : Sub Head n m} {ρ : Ren m k} {a : Tm Head k},
      Presentation.subst (consSub a fun i => Presentation.rename ρ (σ i))
          (.app (Presentation.rename wk g) (.var 0)) =
        .app (Presentation.rename ρ (Presentation.subst σ g)) a := by
    intro m k σ ρ a
    rw [subst_consSub_app_wk, rename_subst]
  have red : ∀ {m : Nat} {Δ : Ctx Head m} {σ : Sub Head n m}, ValidSubst S Γ Δ σ →
      ∀ {P}, Reducible S Δ (Presentation.subst σ (.pi A B)) P →
        P.redTm (Presentation.subst σ g) := by
    intro m Δ σ vσ P r
    obtain ⟨parts, rfl, _⟩ := Reducible.pi_view laws r
    obtain ⟨typing, isFun⟩ := shape vσ
    refine parts.piRedTm_intro laws vσ.formed (RedTm.refl typing) isFun ?_ ?_
    · intro k Δ' ρ w a ha
      obtain ⟨PA, rA, hPA⟩ := ha
      rw [rename_subst] at rA
      have vτ := (vσ.weaken laws w).cons rA hPA
      obtain ⟨PC, rC⟩ := validTyB.red vτ
      have h := validApp.red vτ rC
      rw [app_eq] at h
      rw [inst0_rename_subst_liftSub, ← rC.eq_packOf laws]
      exact h
    · intro k Δ' ρ w a b ha hb hab
      obtain ⟨PA, rA, hPA⟩ := ha
      obtain ⟨PA₂, rA₂, hPB⟩ := hb
      obtain ⟨PA₃, rA₃, hPAB⟩ := hab
      have e₂ := rA.unique laws rA₂
      have e₃ := rA.unique laws rA₃
      subst e₂ e₃
      rw [rename_subst] at rA
      have vρσ := vσ.weaken laws w
      obtain ⟨PC, rC⟩ := validTyB.red (vρσ.cons rA hPA)
      have h := validApp.ext (vρσ.cons rA hPA) (vρσ.cons rA hPB) (vρσ.refl.cons rA hPAB) rC
      rw [app_eq, app_eq] at h
      rw [inst0_rename_subst_liftSub, ← rC.eq_packOf laws]
      exact h
  refine ⟨validPi, red, fun {m Δ σ σ'} vσ vσ' e P r => ?_⟩
  obtain ⟨Q', rQ'⟩ := validPi.red vσ'
  have samePi : P = Q' := validPi.pack_eq laws vσ vσ' e r rQ'
  have hg := red vσ r
  have hg' : P.redTm (Presentation.subst σ' g) := samePi ▸ red vσ' rQ'
  obtain ⟨parts, rfl, _⟩ := Reducible.pi_view laws r
  refine parts.pi_eqTm_of_apps laws vσ.formed hg hg' ?_
  intro k Δ' ρ w a ha
  have vρσ := vσ.weaken laws w
  have vρσ' := vσ'.weaken laws w
  have eρ := e.weaken laws w
  obtain ⟨PA, rA, hPA⟩ := ha
  rw [rename_subst] at rA
  obtain ⟨PA', rA'⟩ := validTyA.red vρσ'
  have sameA : PA = PA' := validTyA.pack_eq laws vρσ vρσ' eρ rA rA'
  subst sameA
  have vτ := vρσ.cons rA hPA
  have vτ' := vρσ'.cons rA' hPA
  obtain ⟨PC, rC⟩ := validTyB.red vτ
  have h := validApp.ext vτ vτ' (eρ.cons rA (rA.reflexive.eqTm hPA)) rC
  rw [app_eq, app_eq] at h
  rw [inst0_rename_subst_liftSub, ← rC.eq_packOf laws]
  exact h

/-! ## Constants -/

/-- A constant that is valid at its declared type in the empty context is
semantic. -/
theorem SemanticConstant.of_valid {name : DeclName} {type : Tm Head 0}
    (valid : ValidTm S .nil (.const name) type) : SemanticConstant S name type := by
  intro m Δ formed P r
  have vσ : ValidSubst S .nil Δ (fun i => Fin.elim0 i) := formed
  have r' : Reducible S Δ (Presentation.subst (fun i => Fin.elim0 i) type) P := by
    rwa [subst_closed]
  exact valid.red vσ r'

/-- A constructor with `k` fields, or a computing constant of arity `k`, whose
full application to the variables of its telescope is valid is valid at its
declared type, one argument at a time. -/
theorem ValidTm.close_telescope (laws : S.E.Laws S.R S.roles) {name : DeclName} {k : Nat}
    (role : S.roles name = .constructor k ∨ ∃ scrutinee, S.roles name = .computes k scrutinee) :
    ∀ {j : Nat} (Θ : Ctx Head j) (C : Tm Head j), j ≤ k →
      Typed S.R .nil (.const name) (closeType Θ C) →
      ValidTy S .nil (closeType Θ C) →
      ValidTm S Θ (applyClosed Θ ids (.const name)) C →
      ValidTm S .nil (.const name) (closeType Θ C)
  | _, .nil, _, _, _, _, full => full
  | j + 1, .snoc Θ A, C, le, typing, validTy, full => by
      have shift : applyClosed (.snoc Θ A) ids (.const name : Tm Head (j + 1)) =
          .app (Presentation.rename wk (applyClosed Θ ids (.const name))) (.var 0) := by
        rw [rename_applyClosed]
        rfl
      rw [shift] at full
      obtain ⟨_, validPi⟩ := ValidTy.telescope laws Θ (X := .pi A C) validTy
      have closed : ∀ {m : Nat} {Δ : Ctx Head m},
          Typed S.R Δ (.const name) (liftClosed (closeType Θ (.pi A C))) :=
        fun {m} {Δ} => Typed.liftClosed (Δ := Δ) typing
      have shape : ∀ {m : Nat} {Δ : Ctx Head m} {σ : Sub Head j m}, ValidSubst S Θ Δ σ →
          Typed S.R Δ (Presentation.subst σ (applyClosed Θ ids (.const name)))
            (Presentation.subst σ (.pi A C)) ∧
          IsFun S.roles (Presentation.subst σ (applyClosed Θ ids (.const name))) := by
        intro m Δ σ vσ
        have e : Presentation.subst σ (applyClosed Θ ids (.const name)) =
            applyClosed Θ σ (.const name) := by
          rw [applyClosed_subst]
          rfl
        rw [e]
        refine ⟨Typed.telescope_apply (vσ.substMor laws) closed, ?_⟩
        rw [applyClosed_eq_appSpine]
        exact .inr (.inr ⟨name, _, k, role, by rw [telescopeArgs_length]; omega, rfl⟩)
      exact ValidTm.close_telescope laws role Θ (.pi A C) (by omega) typing validTy
        (ValidTm.of_apps laws validPi shape full)

/-- A constructor with `k` fields or a computing constant of arity `k`, declared at
the dependent function type of a telescope of length `k`, is semantic when its
full application is valid in the telescope. -/
theorem SemanticConstant.of_telescope (laws : S.E.Laws S.R S.roles) {name : DeclName}
    {k : Nat} (role : S.roles name = .constructor k ∨ ∃ scrutinee, S.roles name = .computes k scrutinee)
    {Θ : Ctx Head k} {C : Tm Head k} (typing : Typed S.R .nil (.const name) (closeType Θ C))
    (validTy : ValidTy S .nil (closeType Θ C))
    (full : ValidTm S Θ (applyClosed Θ ids (.const name)) C) :
    SemanticConstant S name (closeType Θ C) :=
  SemanticConstant.of_valid
    (ValidTm.close_telescope laws role Θ C (Nat.le_refl k) typing validTy full)

end Normalization
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
