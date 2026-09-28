import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Conversion.Candidates
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.Algorithmic.Instance

/-!
# The algorithmic equality respects typed weak-head reduction

The algorithmic comparison of two terms reduces both, typed, to weak-head normal
forms and compares those. A typed weak-head reduct of a compared term reduces to
the same normal form, since weak-head reduction is deterministic and a normal
form ends every reduction of the term (`WhRed.to_whnf`). So the algorithmic
equality relates the reducts of terms it relates (`algorithmic_convTm_reduce`),
the property a realizer side of the conversion model asks of its generic
equality besides its laws.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Impredicative
namespace Conversion

open Normalization
open UniverseLevel (LevelOrder)

variable {Head L : Type} [LevelOrder L] {S : Setting Head L}

/-- A typed weak-head reduct of a term that reduces, typed, to a weak-head normal
form reduces, typed, to that normal form. -/
theorem RedTm.to_whnf {n : Nat} {Γ : Ctx Head n} {t t' w A B : Tm Head n}
    (toNormal : RedTm S.R S.roles Γ t w B) (normal : Whnf S.R S.roles w)
    (red : RedTm S.R S.roles Γ t t' A) (equal : TypeEq S.R Γ A B) :
    RedTm S.R S.roles Γ t' w B :=
  ⟨WhRed.to_whnf S.shape toNormal.red normal red.red, Typed.convType red.target equal,
    toNormal.target, .trans (.symm (Equal.convType red.equal equal)) toNormal.equal⟩

/-- **The algorithmic equality respects typed weak-head reduction** of both
sides. -/
theorem algorithmic_convTm_reduce {n : Nat} {Γ : Ctx Head n} {t t' u u' A : Tm Head n}
    (red : RedTm S.R S.roles Γ t t' A) (red' : RedTm S.R S.roles Γ u u' A)
    (h : (algorithmic S.R S.roles).convTm Γ t u A) :
    (algorithmic S.R S.roles).convTm Γ t' u' A := by
  refine ⟨.trans (.symm red.equal) (.trans h.1 red'.equal), fun m Δ ρ cr formed => ?_⟩
  have d := h.2 cr formed
  cases d with
  | terms rA fA rt ru dW =>
      obtain ⟨nt, nu⟩ := Algorithmic.termsW_whnf (S := S) dW
      exact .terms rA fA (RedTm.to_whnf rt nt (red.rename cr) rA.typeEq)
        (RedTm.to_whnf ru nu (red'.rename cr) rA.typeEq) dW

end Conversion
end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
