import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.PatternTelescopes

/-!
# Partial applications of computing constants

A constructor or computing constant of arity `K`, declared at the dependent
function type of a telescope, applied to the first `j` arguments of the
telescope is a function in weak-head normal form. It is reducible at the rest
of its type, and reducibly equal to another such application, as soon as its
applications to all remaining arguments are, in every world. This is how a
recursive call, which fixes the arguments up to the scrutinee, is reducible
at the type of the remaining arguments.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Normalization

open TelescopeAbstraction (closeType applyClosed applyClosed_subst liftClosed_zero)

open UniverseLevel (LevelOrder)

variable {Head L : Type} [LevelOrder L] {S : Setting Head L}

/-- The first `j` arguments of a substitution of a telescope of length `j + q`. -/
def dropSub {m : Nat} (j : Nat) : (q : Nat) → Sub Head (j + q) m → Sub Head j m
  | 0, σ => σ
  | q + 1, σ => dropSub j q (tailSub σ)

theorem dropSub_rename {m k : Nat} (j : Nat) (ρ : Ren m k) :
    ∀ (q : Nat) (σ : Sub Head (j + q) m),
      dropSub j q (fun i => Presentation.rename ρ (σ i)) =
        fun i => Presentation.rename ρ (dropSub j q σ i)
  | 0, _ => rfl
  | q + 1, σ => dropSub_rename j ρ q (tailSub σ)

section Partial

variable (laws : S.E.Laws S.R S.roles) {name : DeclName} {K : Nat}
  (role : S.roles name = .constructor K ∨ ∃ scrutinee, S.roles name = .computes K scrutinee)
  (e : (i : Nat) → Tm Head i) (j : Nat)
include laws role

/-- Applications of a constant to the first `j` arguments of its telescope are
reducibly equal at the rest of its type when its applications to all
arguments, in every world, are reducibly equal. -/
theorem partial_eqTm :
    ∀ (q : Nat), j + q ≤ K → ∀ (X : Tm Head (j + q)),
      ValidTy S .nil (closeType (ofEntries e (j + q)) X) →
      (∀ {n : Nat} {Γ : Ctx Head n},
        Typed S.R Γ (.const name) (liftClosed (closeType (ofEntries e (j + q)) X))) →
      ∀ {m : Nat} {Δ : Ctx Head m} {σ₀ σ₀' : Sub Head j m},
      (∀ {k : Nat} {Δ' : Ctx Head k} {ρ : Ren m k}, World S Δ Δ' ρ →
        ∀ {σ₁ σ₁' : Sub Head (j + q) k},
        ValidSubst S (ofEntries e (j + q)) Δ' σ₁ → ValidSubst S (ofEntries e (j + q)) Δ' σ₁' →
        EqSubst S (ofEntries e (j + q)) Δ' σ₁ σ₁' →
        dropSub j q σ₁ = (fun i => Presentation.rename ρ (σ₀ i)) →
        dropSub j q σ₁' = (fun i => Presentation.rename ρ (σ₀' i)) →
        ∀ {P : Pack Head k}, Reducible S Δ' (Presentation.subst σ₁ X) P →
          P.eqTm (applyClosed (ofEntries e (j + q)) σ₁ (.const name))
            (applyClosed (ofEntries e (j + q)) σ₁' (.const name))) →
      ValidSubst S (ofEntries e j) Δ σ₀ → ValidSubst S (ofEntries e j) Δ σ₀' →
      EqSubst S (ofEntries e j) Δ σ₀ σ₀' →
      ∀ {P : Pack Head m}, Reducible S Δ (Presentation.subst σ₀ (piRange e j q X)) P →
        P.eqTm (applyClosed (ofEntries e j) σ₀ (.const name))
          (applyClosed (ofEntries e j) σ₀' (.const name)) := by
  intro q
  induction q with
  | zero =>
      intro _ X _ _ m Δ σ₀ σ₀' full vσ₀ vσ₀' eσ₀ P r
      have w := World.refl (S := S) vσ₀.formed
      have h := full w vσ₀ vσ₀' eσ₀ (by funext i; exact (rename_id (σ₀ i)).symm)
        (by funext i; exact (rename_id (σ₀' i)).symm) r
      exact h
  | succ q ih =>
      intro hK X validType typing m Δ σ₀ σ₀' full vσ₀ vσ₀' eσ₀
      refine ih (by omega) (.pi (e (j + q)) X) validType typing ?_ vσ₀ vσ₀' eσ₀
      intro k Δ' ρ w σ₁ σ₁' v₁ v₁' e₁ d₁ d₁' P r
      obtain ⟨validΘ, validX⟩ := ValidTy.telescope laws (ofEntries e (j + (q + 1))) validType
      have validE : ValidTy S (ofEntries e (j + q)) (e (j + q)) := validΘ.2
      have validPi := (ValidTy.telescope laws (ofEntries e (j + q)) (X := .pi (e (j + q)) X)
        validType).2
      obtain ⟨parts, same, _⟩ := Reducible.pi_view laws r
      rw [same]
      have formed := v₁.formed
      /- The application of a renamed application is the longer application. -/
      have app_eq : ∀ {k' : Nat} {ρ' : Ren k k'} {b : Tm Head k'} (τ : Sub Head (j + q) k),
          Tm.app (Presentation.rename ρ' (applyClosed (ofEntries e (j + q)) τ (.const name))) b =
            applyClosed (ofEntries e (j + (q + 1)))
              (consSub b fun i => Presentation.rename ρ' (τ i)) (.const name) := by
        intro k' ρ' b τ
        rw [rename_applyClosed]
        rfl
      /- The first arguments, in the composed world. -/
      have drop_eq : ∀ {k' : Nat} {ρ' : Ren k k'} {b : Tm Head k'} {τ : Sub Head (j + q) k}
          {σ : Sub Head j m}, dropSub j q τ = (fun i => Presentation.rename ρ (σ i)) →
          dropSub j (q + 1) (consSub b fun i => Presentation.rename ρ' (τ i)) =
            fun i => Presentation.rename (fun x => ρ' (ρ x)) (σ i) := by
        intro k' ρ' b τ σ hτ
        show dropSub j q (fun i => Presentation.rename ρ' (τ i)) = _
        rw [dropSub_rename, hτ]
        funext i
        exact rename_rename ρ ρ' (σ i)
      /- The hypothesis at arguments extended in a world, at the codomain's pack. -/
      have fullAt : ∀ {k' : Nat} {Δ'' : Ctx Head k'} {ρ' : Ren k k'} (w' : World S Δ' Δ'' ρ')
          {b b' : Tm Head k'},
          (packOf S Δ'' (Presentation.rename ρ' (Presentation.subst σ₁ (e (j + q))))).redTm b →
          (packOf S Δ'' (Presentation.rename ρ' (Presentation.subst σ₁ (e (j + q))))).eqTm b b' →
          (packOf S Δ'' (inst0 b (Presentation.rename (liftRen ρ')
              (Presentation.subst (liftSub σ₁) X)))).eqTm
            (Tm.app (Presentation.rename ρ' (applyClosed (ofEntries e (j + q)) σ₁ (.const name))) b)
            (Tm.app (Presentation.rename ρ' (applyClosed (ofEntries e (j + q)) σ₁' (.const name))) b') := by
        intro k' Δ'' ρ' w' b b' hb hbb
        have rDom := parts.domain w'
        have vρσ₁ := v₁.weaken laws w'
        have vρσ₁' := v₁'.weaken laws w'
        have eρ := e₁.weaken laws w'
        have rσ : Reducible S Δ'' (Presentation.subst (fun i => Presentation.rename ρ' (σ₁ i))
            (e (j + q))) (packOf S Δ'' (Presentation.rename ρ' (Presentation.subst σ₁ (e (j + q))))) := by
          rw [← rename_subst]; exact rDom
        obtain ⟨Q', rQ'⟩ := validE.red vρσ₁'
        have same' := validE.pack_eq laws vρσ₁ vρσ₁' eρ rσ rQ'
        have hb' := (rσ.eqTm_redTm laws hbb).2
        have rc := parts.codomain w' hb
        have e₀ : inst0 b (Presentation.rename (liftRen ρ') (Presentation.subst (liftSub σ₁) X)) =
            Presentation.subst (consSub b fun i => Presentation.rename ρ' (σ₁ i)) X := by
          rw [inst0_rename_subst_liftSub]
        rw [e₀] at rc ⊢
        have vb : ValidSubst S (ofEntries e (j + (q + 1))) Δ''
            (consSub b fun i => Presentation.rename ρ' (σ₁ i)) := ⟨vρσ₁, _, rσ, hb⟩
        have vb' : ValidSubst S (ofEntries e (j + (q + 1))) Δ''
            (consSub b' fun i => Presentation.rename ρ' (σ₁' i)) := by
          refine ⟨vρσ₁', Q', rQ', ?_⟩
          rw [← same']
          exact hb'
        have eb : EqSubst S (ofEntries e (j + (q + 1))) Δ''
            (consSub b fun i => Presentation.rename ρ' (σ₁ i))
            (consSub b' fun i => Presentation.rename ρ' (σ₁' i)) := ⟨eρ, _, rσ, hbb⟩
        rw [app_eq σ₁, app_eq σ₁']
        exact full (w.comp w') vb vb' eb (drop_eq d₁) (drop_eq d₁') rc
      /- Codomain packs at reducibly equal arguments are equal. -/
      have codSame : ∀ {k' : Nat} {Δ'' : Ctx Head k'} {ρ' : Ren k k'} (w' : World S Δ' Δ'' ρ')
          {b b' : Tm Head k'},
          (packOf S Δ'' (Presentation.rename ρ' (Presentation.subst σ₁ (e (j + q))))).redTm b →
          (packOf S Δ'' (Presentation.rename ρ' (Presentation.subst σ₁ (e (j + q))))).redTm b' →
          (packOf S Δ'' (Presentation.rename ρ' (Presentation.subst σ₁ (e (j + q))))).eqTm b b' →
          packOf S Δ'' (inst0 b (Presentation.rename (liftRen ρ') (Presentation.subst (liftSub σ₁) X))) =
            packOf S Δ'' (inst0 b' (Presentation.rename (liftRen ρ')
              (Presentation.subst (liftSub σ₁) X))) := by
        intro k' Δ'' ρ' w' b b' hb hb' hbb
        exact (parts.codomain w' hb).conv laws (parts.codomain w' hb') (parts.ext w' hb hb' hbb)
      have typingσ := Typed.telescope_apply (v₁.substMor laws) (typing (Γ := Δ'))
      have typingσ' := Typed.telescope_apply (v₁'.substMor laws) (typing (Γ := Δ'))
      have typeEq : TypeEq S.R Δ' (Presentation.subst σ₁' (.pi (e (j + q)) X))
          (Presentation.subst σ₁ (.pi (e (j + q)) X)) := (validPi.typeEq_at laws v₁ v₁' e₁).symm
      have isFun : ∀ τ : Sub Head (j + q) k,
          IsFun S.roles (applyClosed (ofEntries e (j + q)) τ (.const name)) := by
        intro τ
        rw [applyClosed_eq_appSpine]
        refine .inr (.inr ⟨name, _, K, role, ?_, rfl⟩)
        rw [telescopeArgs_length]
        omega
      have hg := parts.piRedTm_intro laws formed (RedTm.refl typingσ) (isFun σ₁)
        (fun {_ _ _} w' {_} hb => ((parts.codomain w' hb).eqTm_redTm laws
          (fullAt w' hb ((parts.domain w').reflexive.eqTm hb))).1)
        (fun {_ _ _} w' {_ _} ha hb hab => by
          have first := fullAt w' ha hab
          have second := fullAt w' hb ((parts.domain w').reflexive.eqTm hb)
          have rc := parts.codomain w' ha
          rw [← codSame w' ha hb hab] at second
          exact rc.eqTm_trans laws first (rc.eqTm_symm laws second))
      have hg' := parts.piRedTm_intro laws formed
        (RedTm.refl (Typed.convType typingσ' typeEq)) (isFun σ₁')
        (fun {_ _ _} w' {_} hb => ((parts.codomain w' hb).eqTm_redTm laws
          (fullAt w' hb ((parts.domain w').reflexive.eqTm hb))).2)
        (fun {_ _ _} w' {_ _} ha hb hab => by
          have first := fullAt w' ha ((parts.domain w').reflexive.eqTm ha)
          have second := fullAt w' ha hab
          have rc := parts.codomain w' ha
          exact rc.eqTm_trans laws (rc.eqTm_symm laws first) second)
      exact parts.pi_eqTm_of_apps laws formed hg hg'
        (fun {_ _ _} w' {_} hb => fullAt w' hb ((parts.domain w').reflexive.eqTm hb))

end Partial

end Normalization
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
