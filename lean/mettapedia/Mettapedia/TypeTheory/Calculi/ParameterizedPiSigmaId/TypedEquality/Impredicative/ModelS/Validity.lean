import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.ModelS.Membership
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.Validity

/-!
# Validity in model S

A valuation of a context has three parts: two substitutions into a world of
the value side, which fix the values of the variables and so the packs of the
types, and a substitution into a scope of the realizer side, which gives each
variable a realizer. *Related valuations* send each variable to two related
values of its substituted type, and to a realizer of the first. A denotation's
relation is a partial equivalence, so both values are valid.

Then:

* a type is valid when related valuations give it one pack and a strongly
  normalizing realizer instance;
* a term is valid at a valid type when related valuations give related values
  and a realizer of the first;
* two terms are validly equal when, in addition, related valuations relate the
  one to the other;
* a type is validly below another when, under related valuations, the value
  relation and the realizers of the valid values of the first are included in
  those of the second.

There is no skeleton relation. The universe relation relates types with one
pack and one shape (`ValueSide.universePack`), so a term of a universe is valid
only when related valuations give it instances of one shape at every world
reached by a morphism.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Impredicative
namespace ModelS

open Normalization (tailSub)
open UniverseLevel (LevelOrder)
open Consistency (World)
open StrongNormalization
open ValueSide

variable {Head L : Type} [LevelOrder L] {M : SModel Head L}

variable (M) in
/-- Related valuations of a context: related values of each substituted type, and
a realizer of the first value. -/
def EqSubstS : {n m r : Nat} → Ctx Head n → World M.reading m → Sub Head n m →
    Sub Head n m → Sub Head n r → Prop
  | _, _, _, .nil, _, _, _, _ => True
  | _, _, _, .snoc Γ A, ξ, σ, σ', ς =>
    EqSubstS Γ ξ (tailSub σ) (tailSub σ') (tailSub ς) ∧
      ∃ P, DenS M.value ξ (Presentation.subst (tailSub σ) A) P ∧ P.rel (σ 0) (σ' 0) ∧
        (P.real (σ 0)).mem (ς 0)

variable (M) in
/-- A valid type: related valuations give it one pack and a strongly normalizing
realizer instance. -/
def ValidTyS {n : Nat} (Γ : Ctx Head n) (A : Tm Head n) : Prop :=
  ∀ {m r : Nat} {ξ : World M.reading m} {σ σ' : Sub Head n m} {ς : Sub Head n r},
    EqSubstS M Γ ξ σ σ' ς →
      ∃ P, DenS M.value ξ (Presentation.subst σ A) P ∧
        DenS M.value ξ (Presentation.subst σ' A) P ∧
        SN M.realizers.rules (Presentation.subst ς A)

variable (M) in
/-- A valid context: every entry is a valid type in the context before it. -/
def ValidCtxS : {n : Nat} → Ctx Head n → Prop
  | _, .nil => True
  | _, .snoc Γ A => ValidCtxS Γ ∧ ValidTyS M Γ A

variable (M) in
/-- A valid term at a valid type: related valuations give related values and a
realizer of the first. -/
def ValidTmS {n : Nat} (Γ : Ctx Head n) (t A : Tm Head n) : Prop :=
  ValidTyS M Γ A ∧
  ∀ {m r : Nat} {ξ : World M.reading m} {σ σ' : Sub Head n m} {ς : Sub Head n r},
    EqSubstS M Γ ξ σ σ' ς → ∀ {P}, DenS M.value ξ (Presentation.subst σ A) P →
      P.rel (Presentation.subst σ t) (Presentation.subst σ' t) ∧
        (P.real (Presentation.subst σ t)).mem (Presentation.subst ς t)

variable (M) in
/-- Two valid terms that are validly equal: related valuations relate the one to
the other. -/
def ValidEqS {n : Nat} (Γ : Ctx Head n) (t u A : Tm Head n) : Prop :=
  ValidTmS M Γ t A ∧ ValidTmS M Γ u A ∧
  ∀ {m r : Nat} {ξ : World M.reading m} {σ σ' : Sub Head n m} {ς : Sub Head n r},
    EqSubstS M Γ ξ σ σ' ς → ∀ {P}, DenS M.value ξ (Presentation.subst σ A) P →
      P.rel (Presentation.subst σ t) (Presentation.subst σ' u)

variable (M) in
/-- A valid type validly below another: under related valuations, the value
relation and the realizers of the valid values of the first are included in
those of the second. -/
def ValidLeS {n : Nat} (Γ : Ctx Head n) (A B : Tm Head n) : Prop :=
  ValidTyS M Γ A ∧ ValidTyS M Γ B ∧
  ∀ {m r : Nat} {ξ : World M.reading m} {σ σ' : Sub Head n m} {ς : Sub Head n r},
    EqSubstS M Γ ξ σ σ' ς → ∀ {P P'}, DenS M.value ξ (Presentation.subst σ A) P →
      DenS M.value ξ (Presentation.subst σ B) P' →
        (∀ {a b}, P.rel a b → P'.rel a b) ∧ ∀ {a}, P.Val a → Incl (P.real a) (P'.real a)

end ModelS
end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
