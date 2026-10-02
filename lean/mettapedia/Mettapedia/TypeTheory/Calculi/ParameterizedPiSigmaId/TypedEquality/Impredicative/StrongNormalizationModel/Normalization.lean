import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.StrongNormalizationModel.Structure

/-!
# From validity to strong normalization

A valid term is strongly normalizing, and so is its type. Take the daimon
valuation: every variable is sent to the daimon on both sides of the value
world without generics, and to itself on the realizer side. It is a related
valuation of every valid context, because the daimon is a valid value of every
pack and a variable realizes every value. Under it the realizer instance of a
term is the term itself, which then realizes its value; realizers are
strongly normalizing. The realizer instance of a valid type is strongly
normalizing by the definition of validity.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Impredicative
namespace ModelSN

open UniverseLevel (LevelOrder)
open Consistency (World)
open StrongNormalization

variable {Head L : Type} [LevelOrder L] {M : SNModel Head L}

section Laws

variable (laws : M.Laws)
include laws

/-- The daimon valuation of a valid context. -/
theorem EqSubstS.daimonIds {n : Nat} {Γ : Ctx Head n} (ctx : ValidCtxS M Γ) :
    EqSubstS M Γ (World.closed (S := M.reading)) (fun _ => .const M.star)
      (fun _ => .const M.star) ids :=
  EqSubstS.daimon laws ctx World.closed idRen

/-- A valid type in a valid context is strongly normalizing. -/
theorem ValidTyS.normalizes {n : Nat} {Γ : Ctx Head n} {A : Tm Head n} (ctx : ValidCtxS M Γ)
    (valid : ValidTyS M Γ A) : SN M.realizers.rules A := by
  obtain ⟨_, _, _, sn⟩ := valid (EqSubstS.daimonIds laws ctx)
  rwa [subst_ids] at sn

/-- A valid term in a valid context is strongly normalizing, and so is its
type. -/
theorem ValidTmS.normalizes {n : Nat} {Γ : Ctx Head n} {t A : Tm Head n} (ctx : ValidCtxS M Γ)
    (valid : ValidTmS M Γ t A) : SN M.realizers.rules t ∧ SN M.realizers.rules A := by
  have e := EqSubstS.daimonIds laws ctx
  obtain ⟨P, den, _, _⟩ := valid.1 e
  have real := (valid.2 e den).2
  rw [subst_ids] at real
  exact ⟨KCand.sn _ real, ValidTyS.normalizes laws ctx valid.1⟩

/-- Validly equal terms in a valid context are strongly normalizing, and so is
their type. -/
theorem ValidEqS.normalizes {n : Nat} {Γ : Ctx Head n} {t u A : Tm Head n} (ctx : ValidCtxS M Γ)
    (valid : ValidEqS M Γ t u A) :
    SN M.realizers.rules t ∧ SN M.realizers.rules u ∧ SN M.realizers.rules A :=
  ⟨(valid.1.normalizes laws ctx).1, (valid.2.1.normalizes laws ctx).1,
    (valid.1.normalizes laws ctx).2⟩

/-- Validly included types in a valid context are strongly normalizing. -/
theorem ValidLeS.normalizes {n : Nat} {Γ : Ctx Head n} {A B : Tm Head n} (ctx : ValidCtxS M Γ)
    (valid : ValidLeS M Γ A B) : SN M.realizers.rules A ∧ SN M.realizers.rules B :=
  ⟨ValidTyS.normalizes laws ctx valid.1, ValidTyS.normalizes laws ctx valid.2.1⟩

end Laws

end ModelSN
end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
