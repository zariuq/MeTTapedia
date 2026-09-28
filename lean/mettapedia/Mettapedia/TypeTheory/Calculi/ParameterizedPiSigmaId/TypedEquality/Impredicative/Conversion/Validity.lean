import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Conversion.Coherence
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.ValueSide.Families
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.Validity

/-!
# Validity in the conversion model

A valuation of a context has two sides. On the value side, two substitutions
into a world fix the values of the variables and so the packs of the types. On
the realizer side, two substitutions into a formed context of the realizer side
fix two realizers of each variable. *Related valuations* (`EqSubstN`) send each
variable to two related values of its substituted type and to two realizers
related, at the realizer instance of its type, by the realizers of the first
value (`NPack.Related`).

Then:

* a type is valid when related valuations give it one pack, and realizer
  instances that the types of some universe relate (`TypesRel`): both typed
  there, related by the generic equality, and reaching weak-head forms of
  types;
* a term is valid at a valid type when related valuations give it related
  values, and realizer instances related by the realizers of the first value
  at the realizer instance of the type;
* two terms are validly equal when, in addition, related valuations relate the
  one to the other, on both sides;
* a type is validly below another when, under related valuations, the
  realizer instance of the first is usable at that of the second, the value
  relation of the first is included in that of the second, and the realizers
  of each valid value of the first, read at the realizer instance of the first,
  are included in its realizers in the second, read at the realizer instance of
  the second.

Realizer types are read only where the candidates are evaluated, and nothing
ties them to the value types: a type variable may take any value type and any
realizer type.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Impredicative
namespace Conversion

open Normalization (tailSub CtxFormed IsType TypeEq)
open UniverseLevel (LevelOrder)
open Consistency (World)

variable {Head L : Type} [LevelOrder L]

/-- Two realizer types related by the types of some universe of the realizer
side: both typed at it, related by the generic equality there, and both
reaching weak-head forms of types. -/
def TypesRel (T : RealizerSide Head L) {m : Nat} (Δ : Ctx Head m) (A A' : Tm Head m) : Prop :=
  ∃ u, T.R.isUniverse u ∧ (ECand.types T).rel Δ (.head u) A A'

variable {M : NModel Head L}

variable (M) in
/-- Related valuations of a context: two related values of each substituted
type, and two realizers related by the realizers of the first value at the
realizer instance of the type, in a formed context of the realizer side. -/
def EqSubstN : {n m r : Nat} → Ctx Head n → World M.reading m → Sub Head n m →
    Sub Head n m → Ctx Head r → Sub Head n r → Sub Head n r → Prop
  | _, _, _, .nil, _, _, _, Δ, _, _ => CtxFormed M.side.R Δ
  | _, m, _, .snoc Γ A, ξ, σ, σ', Δ, ς, ς' =>
    EqSubstN Γ ξ (tailSub σ) (tailSub σ') Δ (tailSub ς) (tailSub ς') ∧
      ∃ P : NPack M m, DenN M ξ (Presentation.subst (tailSub σ) A) P ∧
        P.Related (σ 0) (σ' 0) Δ (Presentation.subst (tailSub ς) A) (ς 0) (ς' 0)

variable (M) in
/-- A valid type: related valuations give it one pack, and realizer instances
related by the types of some universe. -/
def ValidTyN {n : Nat} (Γ : Ctx Head n) (A : Tm Head n) : Prop :=
  ∀ {m r : Nat} {ξ : World M.reading m} {σ σ' : Sub Head n m} {Δ : Ctx Head r}
    {ς ς' : Sub Head n r}, EqSubstN M Γ ξ σ σ' Δ ς ς' →
      ∃ P : NPack M m, DenN M ξ (Presentation.subst σ A) P ∧
        DenN M ξ (Presentation.subst σ' A) P ∧ TypesRel M.side Δ (Presentation.subst ς A) (Presentation.subst ς' A)

variable (M) in
/-- A valid context: every entry is a valid type in the context before it. -/
def ValidCtxN : {n : Nat} → Ctx Head n → Prop
  | _, .nil => True
  | _, .snoc Γ A => ValidCtxN Γ ∧ ValidTyN M Γ A

variable (M) in
/-- A valid term at a valid type: related valuations give related values, and
realizer instances related by the realizers of the first value at the realizer
instance of the type. -/
def ValidTmN {n : Nat} (Γ : Ctx Head n) (t A : Tm Head n) : Prop :=
  ValidTyN M Γ A ∧
  ∀ {m r : Nat} {ξ : World M.reading m} {σ σ' : Sub Head n m} {Δ : Ctx Head r}
    {ς ς' : Sub Head n r}, EqSubstN M Γ ξ σ σ' Δ ς ς' → ∀ {P : NPack M m},
      DenN M ξ (Presentation.subst σ A) P →
        P.Related (Presentation.subst σ t) (Presentation.subst σ' t) Δ
          (Presentation.subst ς A) (Presentation.subst ς t) (Presentation.subst ς' t)

variable (M) in
/-- Two valid terms that are validly equal: related valuations relate the one
to the other, on the value side and on the realizer side. -/
def ValidEqN {n : Nat} (Γ : Ctx Head n) (t u A : Tm Head n) : Prop :=
  ValidTmN M Γ t A ∧ ValidTmN M Γ u A ∧
  ∀ {m r : Nat} {ξ : World M.reading m} {σ σ' : Sub Head n m} {Δ : Ctx Head r}
    {ς ς' : Sub Head n r}, EqSubstN M Γ ξ σ σ' Δ ς ς' → ∀ {P : NPack M m},
      DenN M ξ (Presentation.subst σ A) P →
        P.Related (Presentation.subst σ t) (Presentation.subst σ' u) Δ
          (Presentation.subst ς A) (Presentation.subst ς t) (Presentation.subst ς' u)

variable (M) in
/-- A valid type validly below another: under related valuations, the realizer
instance of the first is usable at that of the second in the realizer side, the
value relation of the first is included in that of the second, and the
realizers of each valid value of the first at the realizer instance of the first
are included in its realizers in the second at the realizer instance of the
second. -/
def ValidLeN {n : Nat} (Γ : Ctx Head n) (A B : Tm Head n) : Prop :=
  ValidTyN M Γ A ∧ ValidTyN M Γ B ∧
  ∀ {m r : Nat} {ξ : World M.reading m} {σ σ' : Sub Head n m} {Δ : Ctx Head r}
    {ς ς' : Sub Head n r}, EqSubstN M Γ ξ σ σ' Δ ς ς' →
      Below M.side.R Δ (Presentation.subst ς A) (Presentation.subst ς B) ∧
      ∀ {P P' : NPack M m},
        DenN M ξ (Presentation.subst σ A) P → DenN M ξ (Presentation.subst σ B) P' →
          (∀ {a b : Tm Head m}, P.rel a b → P'.rel a b) ∧
            ∀ {a : Tm Head m}, P.Val a → ∀ {t t' : Tm Head r},
              (P.real a).rel Δ (Presentation.subst ς A) t t' →
                (P'.real a).rel Δ (Presentation.subst ς B) t t'

end Conversion
end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
