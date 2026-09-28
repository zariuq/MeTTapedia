import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Conversion.Candidates
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.Constants

/-!
# Inversion of typings from the facts about weak-head forms

A typing derivation ends with the rule of the term's former, followed by a chain
of conversions, universe raises and subtyping steps (`TypeLe`). The facts about
weak-head forms of a realizer side invert such a chain step by step, with no
normalization model:

* a chain from a type equal to a dependent function type ends in a type equal to
  a dependent function type, with an equal domain and a codomain the first
  codomain is usable at (`RealizerSide.typeLe_pi`);
* a chain from a type equal to the type constant of an inductive type ends in a
  type equal to it (`RealizerSide.typeLe_inductive`).

A declared constant applied to a substitution of the telescope of its declared
type is typed only as the declaration says, by the facts alone
(`Normalization.Typed.telescope_inv`). The codomain of a type written over a
telescope is a type in that telescope (`closeType_isType`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Impredicative
namespace Conversion

open Normalization
open UniverseLevel (LevelOrder)
open TelescopeAbstraction (closeType applyClosed)

variable {Head L : Type} [LevelOrder L]

/-- **The codomain of a type written over a telescope is a type in that
telescope**, when the closed type is a term of a universe. -/
theorem closeType_isType {R : Rules Head} :
    ∀ {k : Nat} (Θ : Ctx Head k) {C : Tm Head k} {u : Head},
      Typed R .nil (closeType Θ C) (.head u) → R.isUniverse u → IsType R Θ C
  | _, .nil, _, _, typing, hu => ⟨_, hu, typing⟩
  | _, .snoc Θ _, _, _, typing, hu => by
      obtain ⟨v, w, typeC⟩ := closeType_isType Θ typing hu
      obtain ⟨u₁, v₁, w₁, -, -, tB, hv₁, -, -⟩ := typeC.generation
      exact ⟨v₁, hv₁, tB⟩

namespace RealizerSide

variable {T : RealizerSide Head L} {n : Nat} {Γ : Ctx Head n}

/-- **A chain from a type equal to a dependent function type ends in a type
equal to a dependent function type**, with an equal domain and a codomain the
first codomain is usable at. -/
theorem typeLe_pi (formed : CtxFormed T.R Γ) {X Y : Tm Head n} (le : TypeLe T.R Γ X Y) :
    ∀ {A : Tm Head n} {B : Tm Head (n + 1)}, TypeEq T.R Γ X (.pi A B) →
      ∃ A' B', TypeEq T.R Γ Y (.pi A' B') ∧ TypeEq T.R Γ A A' ∧
        Below T.R (.snoc Γ A) B B' := by
  induction le with
  | refl =>
      intro A B eX
      obtain ⟨typeA, typeB⟩ := IsType.pi_parts (TypeEq.isType eX formed).2
      exact ⟨A, B, eX, IsType.refl typeA, IsType.below_refl typeB⟩
  | conv e hu _ ih =>
      intro A B eX
      exact ih (TypeEq.trans T.levels (TypeEq.symm ⟨_, hu, e⟩) eX)
  | @cumul u v C _ _ _ =>
      intro A B eX
      obtain ⟨_, e, -⟩ :=
        (T.facts.forms eX formed (.inl ⟨u, rfl⟩) (.inr (.inl ⟨A, B, rfl⟩))).head_left
      cases e
  | sub le₀ _ ih =>
      intro A B eX
      obtain ⟨A₁, B₁, e₁, eA₁, leB₁⟩ := Below.pi_source T.facts le₀ formed eX
      obtain ⟨A', B', eY, eA', leB'⟩ := ih e₁
      exact ⟨A', B', eY, TypeEq.trans T.levels eA₁ eA',
        .subTrans leB₁ (Below.ctxConv leB' eA₁.symm)⟩

/-- **A chain from a type equal to the type constant of an inductive type ends
in a type equal to it.** -/
theorem typeLe_inductive (formed : CtxFormed T.R Γ) {I : DeclName}
    {cs : List (DeclName × List (Field Head))} (role : T.roles I = .inductive cs)
    {X Y : Tm Head n} (le : TypeLe T.R Γ X Y) :
    TypeEq T.R Γ X (.const I) → TypeEq T.R Γ Y (.const I) := by
  induction le with
  | refl => exact id
  | conv e hu _ ih =>
      intro eX
      exact ih (TypeEq.trans T.levels (TypeEq.symm ⟨_, hu, e⟩) eX)
  | @cumul u v C _ _ _ =>
      intro eX
      obtain ⟨_, e, -⟩ := (T.facts.forms eX formed (.inl ⟨u, rfl⟩)
        (.inr (.inr (.inr (.inr (.inr ⟨I, cs, role, rfl⟩)))))).head_left
      cases e
  | sub le₀ _ ih =>
      intro eX
      have typeI := (TypeEq.isType eX formed).2
      have e := T.typeEq_of_below formed (RedTy.refl typeI)
        (.inr (.inr (.inr (.inr (.inr ⟨I, cs, role, rfl⟩))))) (fun _ h => nomatch h)
        (fun _ _ h => nomatch h) (fun _ _ h => nomatch h) (.subTrans eX.symm.below le₀)
      exact ih e.symm

end RealizerSide

end Conversion
end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
