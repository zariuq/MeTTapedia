import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.Algorithmic.Basic

/-!
# Changing the context and the type of an algorithmic comparison

A derivation of the algorithmic equality remains a derivation when its
context is replaced by a formed context of equal types and the type it
compares at by an equal type: the weak-head forms of equal types have the
same former and equal components, so each comparison is made at the new
components. Spines keep their comparison; the type their head assigns is
replaced by an equal one.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Normalization

open UniverseLevel (LevelOrder)

variable {Head L : Type} [LevelOrder L] {S : Setting Head L}

/-- What a derivation gives in an equal formed context, at an equal type. -/
def Converts (S : Setting Head L) : AlgorithmicStatement Head → Prop
  | .types Γ A B => ∀ {Δ}, CtxEq S.R Γ Δ → CtxFormed S.R Δ →
      Algorithmic S.R S.roles (.types Δ A B)
  | .typesW Γ A B => ∀ {Δ}, CtxEq S.R Γ Δ → CtxFormed S.R Δ →
      Algorithmic S.R S.roles (.typesW Δ A B)
  | .terms Γ t u A => ∀ {Δ B}, CtxEq S.R Γ Δ → CtxFormed S.R Δ → TypeEq S.R Δ A B →
      Algorithmic S.R S.roles (.terms Δ t u B)
  | .termsW Γ t u A => ∀ {Δ B}, CtxEq S.R Γ Δ → CtxFormed S.R Δ → TypeEq S.R Δ A B →
      IsTypeForm S.roles B → Algorithmic S.R S.roles (.termsW Δ t u B)
  | .spines Γ t u U => ∀ {Δ}, CtxEq S.R Γ Δ → CtxFormed S.R Δ →
      ∃ U', Algorithmic S.R S.roles (.spines Δ t u U') ∧ TypeEq S.R Δ U U'
  | .spinesW Γ t u U => ∀ {Δ}, CtxEq S.R Γ Δ → CtxFormed S.R Δ →
      ∃ U', Algorithmic S.R S.roles (.spinesW Δ t u U') ∧ TypeEq S.R Δ U U'

section Conversion

variable (facts : FormFacts S.R S.roles)
  (roots : RootPreserving S.R) (heads : HeadPreserving S.R) (algebra : CumulativeAlgebra S.R)
include facts

/-- A type equal to one at which values are compared as spines is one too. -/
theorem SpineType.of_typeEq {n : Nat} {Γ : Ctx Head n} {A B : Tm Head n}
    (spine : SpineType S.R S.roles A) (equal : TypeEq S.R Γ A B) (formed : CtxFormed S.R Γ)
    (form : IsTypeForm S.roles B) : SpineType S.R S.roles B := by
  rcases spine with ⟨C, a, b, rfl⟩ | neutral | ⟨T, ctors, role, rfl⟩ | ⟨h, rfl, notUniverse⟩
  · obtain ⟨C', a', b', rfl, _⟩ :=
      (facts.forms equal formed (.inr (.inr (.inr (.inl ⟨_, _, _, rfl⟩)))) form).id_left
    exact .inl ⟨C', a', b', rfl⟩
  · exact .inr (.inl ((facts.forms equal formed
      (.inr (.inr (.inr (.inr (.inl neutral))))) form).neutral_left neutral))
  · have e := (facts.forms equal formed
      (.inr (.inr (.inr (.inr (.inr ⟨T, ctors, role, rfl⟩))))) form).inductive_left role
    exact .inr (.inr (.inl ⟨T, ctors, role, e⟩))
  · obtain ⟨h', rfl, same⟩ :=
      (facts.forms equal formed (.inl ⟨_, rfl⟩) form).head_left
    exact .inr (.inr (.inr ⟨h', rfl, fun hu => notUniverse ((HeadSame.level S.levels same).1.mpr hu)⟩))

include roots heads algebra

/-- Derivations of the algorithmic equality survive equal contexts and types. -/
theorem Algorithmic.converts {st : AlgorithmicStatement Head}
    (derivation : Algorithmic S.R S.roles st) : Converts S st := by
  induction derivation with
  | types rA rB fA fB _ ih =>
      intro Δ equal formed
      exact .types (rA.stable equal) (rB.stable equal) fA fB (ih equal formed)
  | heads same tA tB hu =>
      intro Δ equal formed
      exact .heads same (Typed.stable tA equal) (Typed.stable tB equal) hu
  | pi isA _ _ ihA ihB =>
      intro Δ equal formed
      have isA' := isA.stable equal
      exact .pi isA' (ihA equal formed) (ihB (equal.snocSame isA) (.snoc formed isA'))
  | sigma isA _ _ ihA ihB =>
      intro Δ equal formed
      have isA' := isA.stable equal
      exact .sigma isA' (ihA equal formed) (ihB (equal.snocSame isA) (.snoc formed isA'))
  | id dA _ _ ihA ihx ihy =>
      intro Δ equal formed
      have isA := dA.types_isType.1.stable equal
      exact .id (ihA equal formed) (ihx equal formed isA.refl) (ihy equal formed isA.refl)
  | inductiveType role isT =>
      intro Δ equal formed
      exact .inductiveType role (isT.stable equal)
  | neutralTypes nA nB hu _ ih =>
      intro Δ equal formed
      obtain ⟨U', d', eU⟩ := ih equal formed
      obtain ⟨u', rfl, same⟩ :=
        (facts.forms eU formed (.inl ⟨_, rfl⟩) d'.spinesW_form).head_left
      exact .neutralTypes nA nB ((HeadSame.level S.levels same).1.mp hu) d'
  | terms rA _ rt ru _ ih =>
      intro Δ B equal formed eAB
      obtain ⟨B', rB, fB⟩ :=
        facts.typeForm ((TypeEq.isType eAB formed).2) formed
      have eA' := TypeEq.trans S.levels (TypeEq.trans S.levels (rA.stable equal).typeEq.symm eAB)
        rB.typeEq
      exact .terms rB fB ((rt.stable equal).conv eA') ((ru.stable equal).conv eA')
        (ih equal formed eA' fB)
  | univ hu tt tu _ ih =>
      intro Δ B equal formed eAB fB
      obtain ⟨h', rfl, same⟩ :=
        (facts.forms eAB formed (.inl ⟨_, rfl⟩) fB).head_left
      exact .univ ((HeadSame.level S.levels same).1.mp hu)
        (Typed.convType (Typed.stable tt equal) eAB) (Typed.convType (Typed.stable tu equal) eAB)
        (ih equal formed)
  | eta _ tf funF tg funG _ ih =>
      intro Δ B equal formed eAB fB
      obtain ⟨A₂, B₂, rfl, eA, eB⟩ :=
        (facts.forms eAB formed (.inr (.inl ⟨_, _, rfl⟩)) fB).pi_left
      have isA₂ := (TypeEq.isType eA formed).2
      have eB₂ := eB.stable (.snoc (CtxEq.refl Δ formed) eA.symm)
      exact .eta isA₂ (Typed.convType (Typed.stable tf equal) eAB) funF
        (Typed.convType (Typed.stable tg equal) eAB) funG
        (ih (.snoc equal eA.symm) (.snoc formed isA₂) eB₂)
  | sigmaEta tp pairP tq pairQ _ _ ih₁ ih₂ =>
      intro Δ B equal formed eAB fB
      obtain ⟨A₂, B₂, rfl, eA, eB⟩ :=
        (facts.forms eAB formed (.inr (.inr (.inl ⟨_, _, rfl⟩))) fB).sigma_left
      have tp' := Typed.stable tp equal
      exact .sigmaEta (Typed.convType tp' eAB) pairP (Typed.convType (Typed.stable tq equal) eAB)
        pairQ (ih₁ equal formed eA) (ih₂ equal formed (TypeEq.instantiate eB (.fstElim tp')))
  | refl tx tx' _ ih =>
      intro Δ B equal formed eAB fB
      obtain ⟨C', x', y', rfl, eC, _, _⟩ :=
        (facts.forms eAB formed (.inr (.inr (.inr (.inl ⟨_, _, _, rfl⟩)))) fB).id_left
      exact .refl (Typed.convType (Typed.stable tx equal) eAB)
        (Typed.convType (Typed.stable tx' equal) eAB) (ih equal formed eC)
  | spine sA fT fU tt tu _ ih =>
      intro Δ B equal formed eAB fB
      obtain ⟨_, d', _⟩ := ih equal formed
      exact .spine (sA.of_typeEq facts eAB formed fB) fT fU
        (Typed.convType (Typed.stable tt equal) eAB) (Typed.convType (Typed.stable tu equal) eAB) d'
  | var i =>
      intro Δ equal _
      exact ⟨_, .var i, (equal.lookup i).symm⟩
  | const declared typed =>
      intro Δ equal formed
      have typed' := Typed.stable typed equal
      exact ⟨_, .const declared typed', (Typed.isType typed' formed).refl⟩
  | app _ da ihf iha =>
      intro Δ equal formed
      obtain ⟨U', d', eU⟩ := ihf equal formed
      obtain ⟨A₂, B₂, rfl, eA, eB⟩ :=
        (facts.forms eU formed (.inr (.inl ⟨_, _, rfl⟩)) d'.spinesW_form).pi_left
      exact ⟨_, .app d' (iha equal formed eA),
        TypeEq.instantiate eB (Typed.stable da.terms_typed.1 equal)⟩
  | fst _ ih =>
      intro Δ equal formed
      obtain ⟨U', d', eU⟩ := ih equal formed
      obtain ⟨A₂, B₂, rfl, eA, _⟩ :=
        (facts.forms eU formed (.inr (.inr (.inl ⟨_, _, rfl⟩)))
          d'.spinesW_form).sigma_left
      exact ⟨_, .fst d', eA⟩
  | snd _ ih =>
      intro Δ equal formed
      obtain ⟨U', d', eU⟩ := ih equal formed
      obtain ⟨A₂, B₂, rfl, eA, eB⟩ :=
        (facts.forms eU formed (.inr (.inr (.inl ⟨_, _, rfl⟩)))
          d'.spinesW_form).sigma_left
      obtain ⟨tp, _, _⟩ := Algorithmic.sound facts roots heads algebra d' formed
      exact ⟨_, .snd d', TypeEq.instantiate eB (Typed.convType (.fstElim tp) eA.symm)⟩
  | spinesW _ rU _ ih =>
      intro Δ equal formed
      obtain ⟨U'', d', eU⟩ := ih equal formed
      obtain ⟨U''', rU'', fU''⟩ :=
        facts.typeForm ((TypeEq.isType eU formed).2) formed
      exact ⟨U''', .spinesW d' rU'' fU'',
        TypeEq.trans S.levels (TypeEq.trans S.levels (rU.stable equal).typeEq.symm eU)
          rU''.typeEq⟩

end Conversion

end Normalization
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
