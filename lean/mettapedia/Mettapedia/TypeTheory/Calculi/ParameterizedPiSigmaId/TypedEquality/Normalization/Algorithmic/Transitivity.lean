import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.Algorithmic.Symmetry

/-!
# Transitivity of the algorithmic equality

Two derivations that share a middle term compose. Weak-head normal forms are
unique, so both derivations reduce the middle term to the same normal form;
the type directs which comparison both make; and where the second derivation
compares at the type the middle term's head assigns, that type is equal to the
first one's, because the type a spine's head assigns is principal.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Normalization

open UniverseLevel (LevelOrder)

variable {Head L : Type} [LevelOrder L] {S : Setting Head L}

/-! ## Shapes -/

section Shapes

variable {R : Rules Head} {roles : Roles Head} {n : Nat}

theorem SpineType.not_universe {h : Head} (spine : SpineType R roles (.head h : Tm Head n)) :
    ¬ R.isUniverse h := by
  rcases spine with ⟨_, _, _, e⟩ | neutral | ⟨_, _, _, e⟩ | ⟨h', e, notUniverse⟩
  · cases e
  · exact absurd rfl (neutral.not_former.1 h)
  · cases e
  · cases e
    exact notUniverse

theorem SpineType.not_pi {A : Tm Head n} {B : Tm Head (n + 1)} :
    ¬ SpineType R roles (.pi A B) := by
  rintro (⟨_, _, _, e⟩ | neutral | ⟨_, _, _, e⟩ | ⟨_, e, _⟩)
  · cases e
  · exact neutral.not_former.2.1 A B rfl
  · cases e
  · cases e

theorem SpineType.not_sigma {A : Tm Head n} {B : Tm Head (n + 1)} :
    ¬ SpineType R roles (.sigma A B) := by
  rintro (⟨_, _, _, e⟩ | neutral | ⟨_, _, _, e⟩ | ⟨_, e, _⟩)
  · cases e
  · exact neutral.not_former.2.2.1 A B rfl
  · cases e
  · cases e

theorem SpineForm.not_refl {x : Tm Head n} : ¬ SpineForm roles (.refl x) := by
  rintro (neutral | ⟨_, _, _, _, e⟩)
  · exact neutral.ne_refl rfl
  · exact appSpine_const_ne_refl e.symm

theorem Algorithmic.typesW_form {Γ : Ctx Head n} {A B : Tm Head n}
    (derivation : Algorithmic R roles (.typesW Γ A B)) :
    IsTypeForm roles A ∧ IsTypeForm roles B := by
  cases derivation with
  | heads => exact ⟨.inl ⟨_, rfl⟩, .inl ⟨_, rfl⟩⟩
  | pi => exact ⟨.inr (.inl ⟨_, _, rfl⟩), .inr (.inl ⟨_, _, rfl⟩)⟩
  | sigma => exact ⟨.inr (.inr (.inl ⟨_, _, rfl⟩)), .inr (.inr (.inl ⟨_, _, rfl⟩))⟩
  | id => exact ⟨.inr (.inr (.inr (.inl ⟨_, _, _, rfl⟩))), .inr (.inr (.inr (.inl ⟨_, _, _, rfl⟩)))⟩
  | inductiveType role _ =>
      exact ⟨.inr (.inr (.inr (.inr (.inr ⟨_, _, role, rfl⟩)))),
        .inr (.inr (.inr (.inr (.inr ⟨_, _, role, rfl⟩))))⟩
  | neutralTypes nA nB _ _ =>
      exact ⟨.inr (.inr (.inr (.inr (.inl nA)))), .inr (.inr (.inr (.inr (.inl nB))))⟩

end Shapes

theorem SpineForm.whnf {n : Nat} {t : Tm Head n} (form : SpineForm S.roles t) :
    Whnf S.R S.roles t := by
  rcases form with neutral | ⟨k, arity, args, role, rfl⟩
  · exact neutral.whnf S.shape
  · exact canonical_whnf S.shape (.inr ⟨k, arity, args, role, rfl⟩)

theorem Algorithmic.termsW_whnf {n : Nat} {Γ : Ctx Head n} {t u A : Tm Head n}
    (derivation : Algorithmic S.R S.roles (.termsW Γ t u A)) :
    Whnf S.R S.roles t ∧ Whnf S.R S.roles u := by
  cases derivation with
  | univ _ _ _ d => exact ⟨d.typesW_form.1.whnf, d.typesW_form.2.whnf⟩
  | eta _ _ funF _ funG _ => exact ⟨funF.whnf, funG.whnf⟩
  | sigmaEta _ pairP _ pairQ _ _ => exact ⟨pairP.whnf, pairQ.whnf⟩
  | refl => exact ⟨refl_whnf S.shape _, refl_whnf S.shape _⟩
  | spine _ fT fU _ _ _ => exact ⟨fT.whnf, fU.whnf⟩

theorem RedTm.whnf_unique {n : Nat} {Γ : Ctx Head n} {t u u' A B : Tm Head n}
    (first : RedTm S.R S.roles Γ t u A) (second : RedTm S.R S.roles Γ t u' B)
    (normal : Whnf S.R S.roles u) (normal' : Whnf S.R S.roles u') : u = u' :=
  WhRed.whnf_unique S.shape first.red second.red normal normal'

/-! ## Transitivity -/

/-- What composing a derivation with a second one sharing its right side gives. -/
def TransitiveAt (S : Setting Head L) : AlgorithmicStatement Head → Prop
  | .types Γ A B => ∀ {C}, CtxFormed S.R Γ → Algorithmic S.R S.roles (.types Γ B C) →
      Algorithmic S.R S.roles (.types Γ A C)
  | .typesW Γ A B => ∀ {C}, CtxFormed S.R Γ → Algorithmic S.R S.roles (.typesW Γ B C) →
      Algorithmic S.R S.roles (.typesW Γ A C)
  | .terms Γ t u A => ∀ {v}, CtxFormed S.R Γ → Algorithmic S.R S.roles (.terms Γ u v A) →
      Algorithmic S.R S.roles (.terms Γ t v A)
  | .termsW Γ t u A => ∀ {v}, CtxFormed S.R Γ → Algorithmic S.R S.roles (.termsW Γ u v A) →
      Algorithmic S.R S.roles (.termsW Γ t v A)
  | .spines Γ t u U => ∀ {v U'}, CtxFormed S.R Γ → Algorithmic S.R S.roles (.spines Γ u v U') →
      Algorithmic S.R S.roles (.spines Γ t v U)
  | .spinesW Γ t u U => ∀ {v U'}, CtxFormed S.R Γ →
      Algorithmic S.R S.roles (.spinesW Γ u v U') → Algorithmic S.R S.roles (.spinesW Γ t v U)

section Transitivity

variable (facts : FormFacts S.R S.roles)
  (roots : RootPreserving S.R) (heads : HeadPreserving S.R) (algebra : CumulativeAlgebra S.R)
include facts roots heads algebra

/-- Two spines of dependent function type sharing a middle spine have equal
domains: the type the first head assigns is principal for the middle spine. -/
theorem Algorithmic.pi_domains {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ)
    {f g h A A₂ : Tm Head n} {B B₂ : Tm Head (n + 1)}
    (first : Algorithmic S.R S.roles (.spinesW Γ f g (.pi A B)))
    (second : Algorithmic S.R S.roles (.spinesW Γ g h (.pi A₂ B₂))) :
    TypeEq S.R Γ A₂ A := by
  cases first with
  | spinesW d₁ r₁ _ =>
  cases second with
  | spinesW d₂ r₂ _ =>
  obtain ⟨tf, tg, _⟩ := Algorithmic.sound facts roots heads algebra d₁ formed
  obtain ⟨tg', _, _⟩ := Algorithmic.sound facts roots heads algebra d₂ formed
  obtain ⟨_, _, _, _, principal⟩ :=
    Algorithm.sound facts roots heads algebra d₁.refines formed tf tg
  have le := principal tg'
  obtain ⟨u, hu, e⟩ := r₁.typeEq.symm
  have le' : TypeLe S.R Γ (.pi A B) _ := .conv e hu le
  obtain ⟨s, hs, tPi⟩ := r₁.targetType
  have typeT := (TypeEq.isType r₂.typeEq formed).1
  obtain ⟨A', B', eT, eA', _⟩ := Below.pi_source facts (TypeLe.toBelow le' typeT) formed
    (IsType.refl ⟨s, hs, tPi⟩)
  have pis := TypeEq.trans S.levels eT.symm r₂.typeEq
  exact (TypeEq.trans S.levels eA' (TypeEq.pi_injective facts pis formed).1).symm

/-- Derivations of the algorithmic equality compose. -/
theorem Algorithmic.transitive {st : AlgorithmicStatement Head}
    (derivation : Algorithmic S.R S.roles st) : TransitiveAt S st := by
  have conv := fun {st : AlgorithmicStatement Head} (d : Algorithmic S.R S.roles st) =>
    Algorithmic.converts facts roots heads algebra d
  have sound := fun {st : AlgorithmicStatement Head} (d : Algorithmic S.R S.roles st) =>
    Algorithmic.sound facts roots heads algebra d
  induction derivation with
  | types rA rB fA fB _ ih =>
      intro C formed second
      cases second with
      | types rB' rC fB' fC d₂ =>
          obtain rfl := RedTy.unique rB rB' fB.whnf fB'.whnf
          exact .types rA rC fA fC (ih formed d₂)
  | heads same tA _ hu =>
      intro C formed second
      cases second with
      | heads same' _ tC hu' =>
          obtain ⟨w, join⟩ := S.levels.join_exists hu hu'
          obtain ⟨cu, cv⟩ := S.levels.join_upper join
          exact .heads (same.trans S.levels same') (.cumul tA cu) (.cumul tC cv)
            (S.levels.join_level join).1
      | neutralTypes nB _ _ _ => exact absurd rfl (nB.not_former.1 _)
  | pi isA dA _ ihA ihB =>
      intro C formed second
      cases second with
      | pi _ dA' dB' =>
          have eA : TypeEq S.R _ _ _ := sound dA formed
          have formedA : CtxFormed S.R (.snoc _ _) := .snoc formed isA
          exact .pi isA (ihA formed dA')
            (ihB formedA (conv dB' (.snoc (CtxEq.refl _ formed) eA) formedA))
      | neutralTypes nB _ _ _ => exact absurd rfl (nB.not_former.2.1 _ _)
  | sigma isA dA _ ihA ihB =>
      intro C formed second
      cases second with
      | sigma _ dA' dB' =>
          have eA : TypeEq S.R _ _ _ := sound dA formed
          have formedA : CtxFormed S.R (.snoc _ _) := .snoc formed isA
          exact .sigma isA (ihA formed dA')
            (ihB formedA (conv dB' (.snoc (CtxEq.refl _ formed) eA) formedA))
      | neutralTypes nB _ _ _ => exact absurd rfl (nB.not_former.2.2.1 _ _)
  | id dA _ _ ihA ihx ihy =>
      intro C formed second
      cases second with
      | id dA' dx' dy' =>
          have eA : TypeEq S.R _ _ _ := sound dA formed
          exact .id (ihA formed dA')
            (ihx formed (conv dx' (CtxEq.refl _ formed) formed eA.symm))
            (ihy formed (conv dy' (CtxEq.refl _ formed) formed eA.symm))
      | neutralTypes nB _ _ _ => exact absurd rfl (nB.not_former.2.2.2 _ _ _)
  | inductiveType role isT =>
      intro C formed second
      cases second with
      | inductiveType _ _ => exact .inductiveType role isT
      | neutralTypes nB _ _ _ => exact absurd rfl (nB.ne_inductive role)
  | neutralTypes nA nB hu _ ih =>
      intro C formed second
      cases second with
      | heads => exact absurd rfl (nB.not_former.1 _)
      | pi => exact absurd rfl (nB.not_former.2.1 _ _)
      | sigma => exact absurd rfl (nB.not_former.2.2.1 _ _)
      | id => exact absurd rfl (nB.not_former.2.2.2 _ _ _)
      | inductiveType role _ => exact absurd rfl (nB.ne_inductive role)
      | neutralTypes _ nC _ d₂ => exact .neutralTypes nA nC hu (ih formed d₂)
  | terms rA fA rt ru d ih =>
      intro v formed second
      cases second with
      | terms rA₂ fA₂ ru₂ rv d₂ =>
          obtain rfl := RedTy.unique rA rA₂ fA.whnf fA₂.whnf
          obtain rfl := RedTm.whnf_unique ru ru₂ d.termsW_whnf.2 d₂.termsW_whnf.1
          exact .terms rA fA rt rv (ih formed d₂)
  | univ hu tt _ _ ih =>
      intro v formed second
      cases second with
      | univ _ _ tv d₂ => exact .univ hu tt tv (ih formed d₂)
      | spine sA _ _ _ _ _ => exact absurd hu sA.not_universe
  | eta isA tf funF _ _ _ ih =>
      intro v formed second
      cases second with
      | eta _ _ _ tv funV d₂ => exact .eta isA tf funF tv funV (ih (.snoc formed isA) d₂)
      | spine sA _ _ _ _ _ => exact absurd sA SpineType.not_pi
  | sigmaEta tp pairP tq _ d₁ _ ih₁ ih₂ =>
      intro v formed second
      cases second with
      | sigmaEta _ _ tv pairV e₁ e₂ =>
          have eFst : Equal S.R _ _ _ _ := sound d₁ formed
          obtain ⟨s, hs, tSigma⟩ := Typed.isType tp formed
          obtain ⟨_, ⟨w, hw, tB⟩⟩ := IsType.sigma_parts ⟨s, hs, tSigma⟩
          have eSnd := TypeEq.of_instantiateEq tB hw (.fstElim tq) (.symm eFst)
          exact .sigmaEta tp pairP tv pairV (ih₁ formed e₁)
            (ih₂ formed (conv e₂ (CtxEq.refl _ formed) formed eSnd))
      | spine sA _ _ _ _ _ => exact absurd sA SpineType.not_sigma
  | refl tx _ _ ih =>
      intro v formed second
      cases second with
      | refl _ tv d₂ => exact .refl tx tv (ih formed d₂)
      | spine _ fU _ _ _ _ => exact absurd fU SpineForm.not_refl
  | spine sA fT fU tt _ _ ih =>
      intro v formed second
      cases second with
      | univ hu _ _ _ => exact absurd hu sA.not_universe
      | eta => exact absurd sA SpineType.not_pi
      | sigmaEta => exact absurd sA SpineType.not_sigma
      | refl => exact absurd fU SpineForm.not_refl
      | spine _ _ fV _ tv d₂ => exact .spine sA fT fV tt tv (ih formed d₂)
  | var i =>
      intro v U' _ second
      cases second with
      | var => exact .var i
  | const declared typed =>
      intro v U' _ second
      cases second with
      | const => exact .const declared typed
  | app df _ ihf iha =>
      intro v U' formed second
      cases second with
      | app df₂ da₂ =>
          have eA := Algorithmic.pi_domains facts roots heads algebra formed df df₂
          exact .app (ihf formed df₂) (iha formed (conv da₂ (CtxEq.refl _ formed) formed eA))
  | fst _ ih =>
      intro v U' formed second
      cases second with
      | fst d₂ => exact .fst (ih formed d₂)
  | snd _ ih =>
      intro v U' formed second
      cases second with
      | snd d₂ => exact .snd (ih formed d₂)
  | spinesW _ rU fU ih =>
      intro v U' formed second
      cases second with
      | spinesW d₂ _ _ => exact .spinesW (ih formed d₂) rU fU

end Transitivity

end Normalization
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
