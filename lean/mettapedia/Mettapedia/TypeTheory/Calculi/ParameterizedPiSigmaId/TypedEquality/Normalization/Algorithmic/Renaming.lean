import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.Algorithmic.Instance

/-!
# Renaming and expanding algorithmic comparisons

A derivation of the algorithmic equality, renamed along a renaming of contexts,
is a derivation of the renamed comparison (`Algorithmic.rename`): typed
reductions, typings, weak-head forms, neutral terms and the shapes the rules
inspect are all stable under renaming, and a comparison under a binder is
renamed along the lifted renaming. The target context need not be formed.

A comparison of terms also stays derivable when both terms are reduced, typed,
from further up (`Algorithmic.terms_expand`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Normalization

variable {Head : Type} {R : Rules Head} {roles : Roles Head}

/-! ## Shapes under renaming -/

theorem SpineType.rename {n m : Nat} {A : Tm Head n} (spine : SpineType R roles A)
    (ρ : Ren n m) : SpineType R roles (Presentation.rename ρ A) := by
  rcases spine with ⟨C, a, b, rfl⟩ | neutral | ⟨T, ctors, role, rfl⟩ | ⟨h, rfl, notUniverse⟩
  · exact .inl ⟨_, _, _, rfl⟩
  · exact .inr (.inl (neutral.rename ρ))
  · exact .inr (.inr (.inl ⟨T, ctors, role, rfl⟩))
  · exact .inr (.inr (.inr ⟨h, rfl, notUniverse⟩))

theorem SpineForm.rename {n m : Nat} {t : Tm Head n} (form : SpineForm roles t) (ρ : Ren n m) :
    SpineForm roles (Presentation.rename ρ t) := by
  rcases form with neutral | ⟨k, arity, args, role, rfl⟩
  · exact .inl (neutral.rename ρ)
  · refine .inr ⟨k, arity, args.map (Presentation.rename ρ), role, ?_⟩
    rw [rename_appSpine]
    rfl

/-! ## Derivations under renaming -/

/-- What renaming gives for an algorithmic statement: the renamed comparison, in
every context the renaming maps into. -/
abbrev AlgorithmicRenamed (R : Rules Head) (roles : Roles Head) :
    AlgorithmicStatement Head → Prop
  | .types Γ A B => ∀ ⦃m : Nat⦄ ⦃Δ : Ctx Head m⦄ ⦃ρ : Ren _ m⦄, CtxRen Γ Δ ρ →
      Algorithmic R roles (.types Δ (Presentation.rename ρ A) (Presentation.rename ρ B))
  | .typesW Γ A B => ∀ ⦃m : Nat⦄ ⦃Δ : Ctx Head m⦄ ⦃ρ : Ren _ m⦄, CtxRen Γ Δ ρ →
      Algorithmic R roles (.typesW Δ (Presentation.rename ρ A) (Presentation.rename ρ B))
  | .terms Γ t u A => ∀ ⦃m : Nat⦄ ⦃Δ : Ctx Head m⦄ ⦃ρ : Ren _ m⦄, CtxRen Γ Δ ρ →
      Algorithmic R roles (.terms Δ (Presentation.rename ρ t) (Presentation.rename ρ u)
        (Presentation.rename ρ A))
  | .termsW Γ t u A => ∀ ⦃m : Nat⦄ ⦃Δ : Ctx Head m⦄ ⦃ρ : Ren _ m⦄, CtxRen Γ Δ ρ →
      Algorithmic R roles (.termsW Δ (Presentation.rename ρ t) (Presentation.rename ρ u)
        (Presentation.rename ρ A))
  | .spines Γ t u A => ∀ ⦃m : Nat⦄ ⦃Δ : Ctx Head m⦄ ⦃ρ : Ren _ m⦄, CtxRen Γ Δ ρ →
      Algorithmic R roles (.spines Δ (Presentation.rename ρ t) (Presentation.rename ρ u)
        (Presentation.rename ρ A))
  | .spinesW Γ t u A => ∀ ⦃m : Nat⦄ ⦃Δ : Ctx Head m⦄ ⦃ρ : Ren _ m⦄, CtxRen Γ Δ ρ →
      Algorithmic R roles (.spinesW Δ (Presentation.rename ρ t) (Presentation.rename ρ u)
        (Presentation.rename ρ A))

/-- **Algorithmic comparisons are stable under renaming**: a derivation, renamed
along a renaming of contexts, derives the renamed comparison. -/
theorem Algorithmic.rename {st : AlgorithmicStatement Head}
    (derivation : Algorithmic R roles st) : AlgorithmicRenamed R roles st := by
  induction derivation with
  | types rA rB fA fB _ ih =>
      intro m Δ ρ cr
      exact .types (rA.rename cr) (rB.rename cr) (fA.rename ρ) (fB.rename ρ) (ih cr)
  | heads same tA tB hu =>
      intro m Δ ρ cr
      exact .heads same (tA.rename cr) (tB.rename cr) hu
  | pi isA _ _ ihA ihB =>
      intro m Δ ρ cr
      exact .pi (isA.rename cr) (ihA cr) (ihB (CtxRen.snoc cr _))
  | sigma isA _ _ ihA ihB =>
      intro m Δ ρ cr
      exact .sigma (isA.rename cr) (ihA cr) (ihB (CtxRen.snoc cr _))
  | id _ _ _ ihA ihx ihy =>
      intro m Δ ρ cr
      exact .id (ihA cr) (ihx cr) (ihy cr)
  | inductiveType role isT =>
      intro m Δ ρ cr
      exact .inductiveType role (isT.rename cr)
  | neutralTypes nA nB hu _ ih =>
      intro m Δ ρ cr
      exact .neutralTypes (nA.rename ρ) (nB.rename ρ) hu (ih cr)
  | terms rA fA rt ru _ ih =>
      intro m Δ ρ cr
      exact .terms (rA.rename cr) (fA.rename ρ) (rt.rename cr) (ru.rename cr) (ih cr)
  | univ hu tt tu _ ih =>
      intro m Δ ρ cr
      exact .univ hu (tt.rename cr) (tu.rename cr) (ih cr)
  | eta isA tf ff tg fg _ ih =>
      intro m Δ ρ cr
      have d := ih (CtxRen.snoc cr _)
      rw [rename_liftRen_appFresh, rename_liftRen_appFresh] at d
      exact .eta (isA.rename cr) (tf.rename cr) (ff.rename ρ) (tg.rename cr) (fg.rename ρ) d
  | sigmaEta tp pp tq pq _ _ ihF ihS =>
      intro m Δ ρ cr
      have d := ihS cr
      rw [rename_inst0] at d
      exact .sigmaEta (tp.rename cr) (pp.rename ρ) (tq.rename cr) (pq.rename ρ) (ihF cr) d
  | refl tx tx' _ ih =>
      intro m Δ ρ cr
      exact .refl (tx.rename cr) (tx'.rename cr) (ih cr)
  | spine sA ft fu tt tu _ ih =>
      intro m Δ ρ cr
      exact .spine (sA.rename ρ) (ft.rename ρ) (fu.rename ρ) (tt.rename cr) (tu.rename cr) (ih cr)
  | var i =>
      intro m Δ ρ cr
      show Algorithmic R roles (.spines Δ (.var (ρ i)) (.var (ρ i))
        (Presentation.rename ρ (Ctx.lookup _ i)))
      rw [← cr i]
      exact .var (ρ i)
  | const declared typing =>
      intro m Δ ρ cr
      have typing' := typing.rename cr
      simp only [Presentation.rename, rename_liftClosed] at typing' ⊢
      exact .const declared typing'
  | app _ _ ihF iha =>
      intro m Δ ρ cr
      rw [rename_inst0]
      exact .app (ihF cr) (iha cr)
  | fst _ ih =>
      intro m Δ ρ cr
      exact .fst (ih cr)
  | snd _ ih =>
      intro m Δ ρ cr
      rw [rename_inst0]
      exact .snd (ih cr)
  | spinesW _ rU fU ih =>
      intro m Δ ρ cr
      exact .spinesW (ih cr) (rU.rename cr) (fU.rename ρ)

/-- Weakening a comparison of terms past one context entry. -/
theorem Algorithmic.weaken_terms {n : Nat} {Γ : Ctx Head n} {t u A X : Tm Head n}
    (derivation : Algorithmic R roles (.terms Γ t u A)) :
    Algorithmic R roles (.terms (.snoc Γ X) (Presentation.rename wk t) (Presentation.rename wk u)
      (Presentation.rename wk A)) :=
  Algorithmic.rename derivation (CtxRen.wk Γ X)

/-! ## Expansion -/

/-- A comparison of terms stays derivable when both terms are reduced, typed,
from further up. -/
theorem Algorithmic.terms_expand {n : Nat} {Γ : Ctx Head n} {t t' u u' A : Tm Head n}
    (rt : RedTm R roles Γ t t' A) (ru : RedTm R roles Γ u u' A)
    (derivation : Algorithmic R roles (.terms Γ t' u' A)) :
    Algorithmic R roles (.terms Γ t u A) := by
  cases derivation with
  | terms rA fA rt' ru' d =>
      exact .terms rA fA (RedTm.trans (rt.conv rA.typeEq) rt')
        (RedTm.trans (ru.conv rA.typeEq) ru') d

end Normalization
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
