import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.StrongNormalizationModel.Fundamental
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Generation

/-!
# Inverting typings in model SN

A typing derivation ends with the rule of its term's former, followed by steps
of conversion, cumulativity and subtyping (`TypeLe`, `Typed.generation`). In a
package sound for model SN each such step is structural inclusion
(`TypeLe.structural`): the two types are the same, or the first is structurally
included in the second.

Structural inclusion inverts at dependent function types (`SLe.pi_right`, in
`ModelSN.Spines`) and at dependent pair types (`SLe.sigma_right`): a type included
in a dependent pair type is hereditarily total there, or is a dependent pair type
whose domain is included in the other's and whose codomains are included at
every valid point of its domain. Together with generation, these read the types
a derivation passes through, without a normalization argument.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Impredicative
namespace ModelSN

open Normalization (WhRed head_whnf pi_whnf sigma_whnf)
open UniverseLevel (LevelOrder)
open Consistency (World)
open ValueSide

variable {Head L : Type} [LevelOrder L] {M : SNModel Head L}

/-! ## Inversion at dependent pair types -/

variable (M) in
/-- The premises of the clause of dependent pair types: included domains, and
codomains included at every valid point of the first domain. -/
def SigmaLe {n : Nat} (ξ : World M.reading n) (A A' : Tm Head n) (B B' : Tm Head (n + 1)) :
    Prop :=
  SLe M ξ A A' ∧ ∀ {D : Pack M.value n}, DenS M.value ξ A D → ∀ {a : Tm Head n}, D.Val a →
    SLe M ξ (inst0 a B) (inst0 a B')

/-- **Inversion at a dependent pair type on the right.** A type included in a
dependent pair type is hereditarily total there, or is a dependent pair type with
an included domain and codomains included at the valid points of its domain. -/
theorem SLe.sigma_right (laws : M.Laws) {n : Nat} {ξ : World M.reading n} {X Y : Tm Head n}
    (le : SLe M ξ X Y) :
    ∀ {A' : Tm Head n} {B' : Tm Head (n + 1)}, WhRed M.rules M.roles Y (.sigma A' B') →
      Shape M.value (DenS M.value) .total ξ Y Y ∨
        ∃ A B, WhRed M.rules M.roles X (.sigma A B) ∧ SigmaLe M ξ A A' B B' := by
  induction le with
  | shape _ _ _ d =>
      intro A' B' red'
      rcases d.pair_sigma_right laws.value red' with ⟨-, tY⟩ | ⟨A, B, red, parts⟩
      · exact .inl tY
      · refine .inr ⟨A, B, red, ?_, fun {D} hD {a} ha => ?_⟩
        · obtain ⟨P, P', hA, hA', same⟩ := parts.domPacks
          exact .shape hA hA' same parts.domShape
        · obtain ⟨C, C', hC, hC', same⟩ := parts.codPacks hD ha
          exact .shape hC hC' same (parts.codShape hD ha)
  | univ _ red'' _ _ =>
      intro A' B' red'
      cases laws.value.unique red'' red' (head_whnf laws.value.shape _)
        (sigma_whnf laws.value.shape _ _)
  | pi _ _ _ red'' =>
      intro A' B' red'
      cases laws.value.unique red'' red' (pi_whnf laws.value.shape _ _)
        (sigma_whnf laws.value.shape _ _)
  | sigma _ _ red red'' dom cod =>
      intro A' B' red'
      cases laws.value.unique red'' red' (sigma_whnf laws.value.shape _ _)
        (sigma_whnf laws.value.shape _ _)
      exact .inr ⟨_, _, red, dom, cod⟩
  | trans first second ih₁ ih₂ =>
      intro A' B' red'
      rcases ih₂ red' with tY | ⟨AM, BM, redM, domM, codM⟩
      · exact .inl tY
      rcases ih₁ redM with tM | ⟨A, B, red, dom, cod⟩
      · exact .inl (second.total laws.value tM)
      refine .inr ⟨A, B, red, .trans dom domM, fun {D} hD {a} ha => ?_⟩
      obtain ⟨-, DM, hDM⟩ := dom.den
      have haM : DM.Val a := dom.rel laws.value hD hDM ha
      exact .trans (cod hD ha) (codM hDM haM)

/-! ## The steps of a derivation not following the syntax -/

/-- **Each step of conversion, cumulativity and subtyping is structural
inclusion** in a package sound for model SN: the two types of the closure are the
same, or the first is structurally included in the second. -/
theorem TypeLe.structural {R : Rules Head} (sound : TypedSoundS R M) {n : Nat}
    {Γ : Ctx Head n} (ctx : ValidCtxSS M Γ) {A B : Tm Head n} (le : TypeLe R Γ A B) :
    A = B ∨ ValidLeStructS M Γ A B := by
  induction le with
  | refl => exact .inl rfl
  | conv e hu _ ih =>
      have first : ValidLeStructS M Γ _ _ :=
        ValidLeStructS.ofEq sound.laws (Derivable.validTS sound e ctx).1 (sound.isUniverse hu)
      rcases ih with rfl | rest
      · exact .inr first
      · exact .inr (first.trans rest)
  | cumul c _ ih =>
      have first : ValidLeStructS M Γ _ _ := ValidLeStructS.univ (sound.cumulative c)
      rcases ih with rfl | rest
      · exact .inr first
      · exact .inr (first.trans rest)
  | sub le' _ ih =>
      have first : ValidLeStructS M Γ _ _ := (Derivable.validTS sound le' ctx).2.2.2
      rcases ih with rfl | rest
      · exact .inr first
      · exact .inr (first.trans rest)

end ModelSN
end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
