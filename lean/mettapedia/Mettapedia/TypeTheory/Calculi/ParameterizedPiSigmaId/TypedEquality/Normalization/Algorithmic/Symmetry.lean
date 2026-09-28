import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.Algorithmic.Conversion

/-!
# Symmetry of the algorithmic equality

Swapping the two sides of a derivation gives a derivation, in any equal
formed context and at any equal type. A swapped spine is compared at the type
its own head assigns, which is equal to the original one: the arguments the
two heads receive are equal.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Normalization

open UniverseLevel (LevelOrder)

variable {Head L : Type} [LevelOrder L] {S : Setting Head L}

/-- What swapping the sides of a derivation gives. -/
def SymmetricAt (S : Setting Head L) : AlgorithmicStatement Head → Prop
  | .types Γ A B => ∀ {Δ}, CtxEq S.R Γ Δ → CtxFormed S.R Δ →
      Algorithmic S.R S.roles (.types Δ B A)
  | .typesW Γ A B => ∀ {Δ}, CtxEq S.R Γ Δ → CtxFormed S.R Δ →
      Algorithmic S.R S.roles (.typesW Δ B A)
  | .terms Γ t u A => ∀ {Δ B}, CtxEq S.R Γ Δ → CtxFormed S.R Δ → TypeEq S.R Δ A B →
      Algorithmic S.R S.roles (.terms Δ u t B)
  | .termsW Γ t u A => ∀ {Δ B}, CtxEq S.R Γ Δ → CtxFormed S.R Δ → TypeEq S.R Δ A B →
      IsTypeForm S.roles B → Algorithmic S.R S.roles (.termsW Δ u t B)
  | .spines Γ t u U => ∀ {Δ}, CtxEq S.R Γ Δ → CtxFormed S.R Δ →
      ∃ U', Algorithmic S.R S.roles (.spines Δ u t U') ∧ TypeEq S.R Δ U U'
  | .spinesW Γ t u U => ∀ {Δ}, CtxEq S.R Γ Δ → CtxFormed S.R Δ →
      ∃ U', Algorithmic S.R S.roles (.spinesW Δ u t U') ∧ TypeEq S.R Δ U U'

section Symmetry

variable (facts : FormFacts S.R S.roles)
  (roots : RootPreserving S.R) (heads : HeadPreserving S.R) (algebra : CumulativeAlgebra S.R)
include facts roots heads algebra

/-- Derivations of the algorithmic equality can be swapped. -/
theorem Algorithmic.symmetric {st : AlgorithmicStatement Head}
    (derivation : Algorithmic S.R S.roles st) : SymmetricAt S st := by
  have conv := fun {st : AlgorithmicStatement Head} (d : Algorithmic S.R S.roles st) =>
    Algorithmic.converts facts roots heads algebra d
  have sound := fun {st : AlgorithmicStatement Head} (d : Algorithmic S.R S.roles st) =>
    Algorithmic.sound facts roots heads algebra d
  induction derivation with
  | types rA rB fA fB _ ih =>
      intro Δ equal formed
      exact .types (rB.stable equal) (rA.stable equal) fB fA (ih equal formed)
  | heads same tA tB hu =>
      intro Δ equal formed
      exact .heads (same.symm S.levels) (Typed.stable tB equal) (Typed.stable tA equal) hu
  | pi isA dA _ ihA ihB =>
      intro Δ equal formed
      have eA : TypeEq S.R Δ _ _ := sound (conv dA equal formed) formed
      have isA' := (TypeEq.isType eA formed).2
      exact .pi isA' (ihA equal formed) (ihB (.snoc equal eA.symm) (.snoc formed isA'))
  | sigma isA dA _ ihA ihB =>
      intro Δ equal formed
      have eA : TypeEq S.R Δ _ _ := sound (conv dA equal formed) formed
      have isA' := (TypeEq.isType eA formed).2
      exact .sigma isA' (ihA equal formed) (ihB (.snoc equal eA.symm) (.snoc formed isA'))
  | id dA _ _ ihA ihx ihy =>
      intro Δ equal formed
      have eA : TypeEq S.R Δ _ _ := sound (conv dA equal formed) formed
      exact .id (ihA equal formed) (ihx equal formed eA) (ihy equal formed eA)
  | inductiveType role isT =>
      intro Δ equal formed
      exact .inductiveType role (isT.stable equal)
  | neutralTypes nA nB hu _ ih =>
      intro Δ equal formed
      obtain ⟨U', d', eU⟩ := ih equal formed
      obtain ⟨u', rfl, same⟩ :=
        (facts.forms eU formed (.inl ⟨_, rfl⟩) d'.spinesW_form).head_left
      exact .neutralTypes nB nA ((HeadSame.level S.levels same).1.mp hu) d'
  | terms rA _ rt ru _ ih =>
      intro Δ B equal formed eAB
      obtain ⟨B', rB, fB⟩ :=
        facts.typeForm ((TypeEq.isType eAB formed).2) formed
      have eA' := TypeEq.trans S.levels (TypeEq.trans S.levels (rA.stable equal).typeEq.symm eAB)
        rB.typeEq
      exact .terms rB fB ((ru.stable equal).conv eA') ((rt.stable equal).conv eA')
        (ih equal formed eA' fB)
  | univ hu tt tu _ ih =>
      intro Δ B equal formed eAB fB
      obtain ⟨h', rfl, same⟩ :=
        (facts.forms eAB formed (.inl ⟨_, rfl⟩) fB).head_left
      exact .univ ((HeadSame.level S.levels same).1.mp hu)
        (Typed.convType (Typed.stable tu equal) eAB) (Typed.convType (Typed.stable tt equal) eAB)
        (ih equal formed)
  | eta _ tf funF tg funG _ ih =>
      intro Δ B equal formed eAB fB
      obtain ⟨A₂, B₂, rfl, eA, eB⟩ :=
        (facts.forms eAB formed (.inr (.inl ⟨_, _, rfl⟩)) fB).pi_left
      have isA₂ := (TypeEq.isType eA formed).2
      have eB₂ := eB.stable (.snoc (CtxEq.refl Δ formed) eA.symm)
      exact .eta isA₂ (Typed.convType (Typed.stable tg equal) eAB) funG
        (Typed.convType (Typed.stable tf equal) eAB) funF
        (ih (.snoc equal eA.symm) (.snoc formed isA₂) eB₂)
  | sigmaEta tp pairP tq pairQ d₁ _ ih₁ ih₂ =>
      intro Δ B equal formed eAB fB
      obtain ⟨A₂, B₂, rfl, eA, eB⟩ :=
        (facts.forms eAB formed (.inr (.inr (.inl ⟨_, _, rfl⟩))) fB).sigma_left
      have tp' := Typed.convType (Typed.stable tp equal) eAB
      have tq' := Typed.convType (Typed.stable tq equal) eAB
      have eFst : Equal S.R Δ _ _ _ := Equal.convType (sound (conv d₁ equal formed (TypeEq.trans S.levels eA eA.symm)) formed)
        eA
      obtain ⟨s, hs, tSigma⟩ := Typed.isType tq' formed
      obtain ⟨_, ⟨v, hv, tB₂⟩⟩ := IsType.sigma_parts ⟨s, hs, tSigma⟩
      have eSnd := TypeEq.trans S.levels
        (TypeEq.instantiate eB (.fstElim (Typed.stable tp equal)))
        (TypeEq.of_instantiateEq tB₂ hv (.fstElim tp') eFst)
      exact .sigmaEta tq' pairQ tp' pairP (ih₁ equal formed eA)
        (ih₂ equal formed eSnd)
  | refl tx tx' _ ih =>
      intro Δ B equal formed eAB fB
      obtain ⟨C', x', y', rfl, eC, _, _⟩ :=
        (facts.forms eAB formed (.inr (.inr (.inr (.inl ⟨_, _, _, rfl⟩)))) fB).id_left
      exact .refl (Typed.convType (Typed.stable tx' equal) eAB)
        (Typed.convType (Typed.stable tx equal) eAB) (ih equal formed eC)
  | spine sA fT fU tt tu _ ih =>
      intro Δ B equal formed eAB fB
      obtain ⟨_, d', _⟩ := ih equal formed
      exact .spine (sA.of_typeEq facts eAB formed fB) fU fT
        (Typed.convType (Typed.stable tu equal) eAB) (Typed.convType (Typed.stable tt equal) eAB) d'
  | var i =>
      intro Δ equal _
      exact ⟨_, .var i, (equal.lookup i).symm⟩
  | const declared typed =>
      intro Δ equal formed
      have typed' := Typed.stable typed equal
      exact ⟨_, .const declared typed', (Typed.isType typed' formed).refl⟩
  | app df da ihf iha =>
      intro Δ equal formed
      obtain ⟨U', d', eU⟩ := ihf equal formed
      obtain ⟨A₂, B₂, rfl, eA, eB⟩ :=
        (facts.forms eU formed (.inr (.inl ⟨_, _, rfl⟩)) d'.spinesW_form).pi_left
      obtain ⟨_, tg, _⟩ := sound d' formed
      obtain ⟨s, hs, tPi⟩ := Typed.isType tg formed
      obtain ⟨_, ⟨v, hv, tB₂⟩⟩ := IsType.pi_parts ⟨s, hs, tPi⟩
      have ta := Typed.stable da.terms_typed.1 equal
      have eab : Equal S.R Δ _ _ _ := Equal.convType (sound (conv da equal formed (TypeEq.trans S.levels eA eA.symm)) formed) eA
      exact ⟨_, .app d' (iha equal formed eA), TypeEq.trans S.levels (TypeEq.instantiate eB ta)
        (TypeEq.of_instantiateEq tB₂ hv (Typed.convType ta eA) eab)⟩
  | fst _ ih =>
      intro Δ equal formed
      obtain ⟨U', d', eU⟩ := ih equal formed
      obtain ⟨A₂, B₂, rfl, eA, _⟩ :=
        (facts.forms eU formed (.inr (.inr (.inl ⟨_, _, rfl⟩)))
          d'.spinesW_form).sigma_left
      exact ⟨_, .fst d', eA⟩
  | snd dp ih =>
      intro Δ equal formed
      obtain ⟨U', d', eU⟩ := ih equal formed
      obtain ⟨A₂, B₂, rfl, eA, eB⟩ :=
        (facts.forms eU formed (.inr (.inr (.inl ⟨_, _, rfl⟩)))
          d'.spinesW_form).sigma_left
      obtain ⟨tq, tp, eqp⟩ := sound d' formed
      obtain ⟨s, hs, tSigma⟩ := Typed.isType tq formed
      obtain ⟨_, ⟨v, hv, tB₂⟩⟩ := IsType.sigma_parts ⟨s, hs, tSigma⟩
      have tfst := Typed.convType (.fstElim tp) eA.symm
      exact ⟨_, .snd d', TypeEq.trans S.levels (TypeEq.instantiate eB tfst)
        (TypeEq.of_instantiateEq tB₂ hv (.fstElim tp) (.symm (.fstCong eqp)))⟩
  | spinesW _ rU _ ih =>
      intro Δ equal formed
      obtain ⟨U'', d', eU⟩ := ih equal formed
      obtain ⟨U''', rU'', fU''⟩ :=
        facts.typeForm ((TypeEq.isType eU formed).2) formed
      exact ⟨U''', .spinesW d' rU'' fU'',
        TypeEq.trans S.levels (TypeEq.trans S.levels (rU.stable equal).typeEq.symm eU)
          rU''.typeEq⟩

end Symmetry

end Normalization
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
