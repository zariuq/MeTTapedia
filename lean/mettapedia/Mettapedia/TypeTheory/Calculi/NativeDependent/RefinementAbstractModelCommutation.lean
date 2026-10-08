import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementAbstractConstructorInterpretation
import Mettapedia.TypeTheory.ContextualSumSectionSubstitution

/-!
# Model substitution for checked logical constructors

The model operations act on actual supplied sections. Their separate local
substitution laws earn commutation of each constructor's checked readout.
No commutation law for a complete source evaluator is assumed here.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Abstract

open Mettapedia.TypeTheory.ContextualPredicateModel
open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.ContextualModelTelescopes
open Mettapedia.TypeTheory.ContextualSumComprehension
open Mettapedia.TypeTheory.ContextualProductComparison (selfExtend)
open Mettapedia.TypeTheory.ContextualTypeOperations

universe c s t m p

variable {C : CwfWithTerminal.{c, s, t, m}}

namespace ModelData

attribute [local irreducible] ContextualSumComprehension.normalize
  ContextualSumComprehension.reindexBody

variable (localModel : LocalModel.{c, s, t, m, p} C) {Γ Δ : C.toCwf.Ctx}

theorem product_value_substitute (stable : StrictPiSubstitution localModel.products)
    (σ : C.toCwf.Sub Δ Γ) (A : C.toCwf.Ty Γ) (B : C.toCwf.Ty (C.toCwf.ext Γ A))
    (function : C.toCwf.Tm Γ (localModel.products.pi A B)) :
    Value.substitute (⟨_, function⟩ : Value (C.toCwf) Γ) σ =
      ⟨_, reindexFunction localModel.products stable.1 σ function⟩ :=
  Sigma.ext (stable.1 σ A B) (reindexFunction_heq localModel.products stable.1 σ function).symm

theorem sum_value_substitute (σ : C.toCwf.Sub Δ Γ) (A : C.toCwf.Ty Γ)
    (B : C.toCwf.Ty (C.toCwf.ext Γ A))
    (pair : C.toCwf.Tm Γ (localModel.sums.operations.sigma A B)) :
    Value.substitute (⟨_, pair⟩ : Value (C.toCwf) Γ) σ =
      ⟨_, normalize localModel.sums σ (C.toCwf.tmSub pair σ)⟩ :=
  Sigma.ext (localModel.sums.substitution.1 σ A B) (normalize_heq localModel.sums σ (C.toCwf.tmSub pair σ)).symm

theorem second_value_substitute (σ : C.toCwf.Sub Δ Γ) (A : C.toCwf.Ty Γ)
    (B : C.toCwf.Ty (C.toCwf.ext Γ A)) (first : C.toCwf.Tm Γ A)
    (second : C.toCwf.Tm Γ (C.toCwf.tySub B (selfExtend C.toCwf first))) :
    Value.substitute (⟨_, second⟩ : Value (C.toCwf) Γ) σ =
      ⟨_, reindexPairSecond σ first second⟩ := by
  apply Sigma.ext
  · change C.toCwf.tySub (C.toCwf.tySub B (selfExtend C.toCwf first)) σ = _
    rw [← C.toCwf.tySub_comp, ← selfExtend_substitution σ first, C.toCwf.tySub_comp]
  · exact (reindexPairSecond_heq (C := C.toCwf) σ first second).symm

theorem lambda?_substitution (stable : StrictPiSubstitution localModel.products)
    (σ : C.toCwf.Sub Δ Γ) (A : C.toCwf.Ty Γ) (B : C.toCwf.Ty (C.toCwf.ext Γ A))
    (body : C.toCwf.Tm (C.toCwf.ext Γ A) B) :
    (lambda? localModel A B (some ⟨B, body⟩)).map (fun value => value.substitute σ) =
      lambda? localModel (C.toCwf.tySub A σ) (C.toCwf.tySub B (TypeOver.extensionSubstitution σ A))
        (some ⟨_, C.toCwf.tmSub body (TypeOver.extensionSubstitution σ A)⟩) := by
  rw [lambda?_supplied localModel, lambda?_supplied localModel, Option.map_some]
  exact congrArg some (Sigma.ext (stable.1 σ A B) (stable.2.1 σ body))

theorem application?_substitution (stable : StrictPiSubstitution localModel.products)
    (σ : C.toCwf.Sub Δ Γ) (A : C.toCwf.Ty Γ) (B : C.toCwf.Ty (C.toCwf.ext Γ A))
    (function : C.toCwf.Tm Γ (localModel.products.pi A B)) (argument : C.toCwf.Tm Γ A) :
    (application? localModel A B (some ⟨_, function⟩) (some ⟨_, argument⟩)).map
      (fun value => value.substitute σ) =
      application? localModel (C.toCwf.tySub A σ) (C.toCwf.tySub B (TypeOver.extensionSubstitution σ A))
        (some ⟨_, reindexFunction localModel.products stable.1 σ function⟩)
        (some ⟨_, C.toCwf.tmSub argument σ⟩) := by
  rw [application?_supplied localModel, application?_supplied localModel, Option.map_some]
  apply congrArg some
  apply Sigma.ext
  · change C.toCwf.tySub (C.toCwf.tySub B (selfExtend C.toCwf argument)) σ = _
    rw [← C.toCwf.tySub_comp, ← selfExtend_substitution σ argument, C.toCwf.tySub_comp]
  · exact stable.2.2 σ function argument _ (reindexFunction_heq _ _ _ _).symm

theorem pair?_substitution (σ : C.toCwf.Sub Δ Γ) (A : C.toCwf.Ty Γ)
    (B : C.toCwf.Ty (C.toCwf.ext Γ A)) (first : C.toCwf.Tm Γ A)
    (second : C.toCwf.Tm Γ (C.toCwf.tySub B (selfExtend C.toCwf first))) :
    (pair? localModel A B (some ⟨_, first⟩) (some ⟨_, second⟩)).map
      (fun value => value.substitute σ) =
      pair? localModel (C.toCwf.tySub A σ) (C.toCwf.tySub B (TypeOver.extensionSubstitution σ A))
        (some ⟨_, C.toCwf.tmSub first σ⟩) (some ⟨_, reindexPairSecond σ first second⟩) := by
  rw [pair?_supplied localModel, pair?_supplied localModel, Option.map_some]
  exact congrArg some (Sigma.ext (localModel.sums.substitution.1 σ A B)
    (localModel.sums.substitution.2.1 σ first second _ (reindexPairSecond_heq _ _ _).symm))

theorem first?_substitution (σ : C.toCwf.Sub Δ Γ) (A : C.toCwf.Ty Γ)
    (B : C.toCwf.Ty (C.toCwf.ext Γ A))
    (pair : C.toCwf.Tm Γ (localModel.sums.operations.sigma A B)) :
    (first? localModel A B (some ⟨_, pair⟩)).map (fun value => value.substitute σ) =
      first? localModel (C.toCwf.tySub A σ) (C.toCwf.tySub B (TypeOver.extensionSubstitution σ A))
        (some ⟨_, normalize localModel.sums σ (C.toCwf.tmSub pair σ)⟩) := by
  rw [first?_supplied localModel, first?_supplied localModel, Option.map_some]
  exact congrArg some (Sigma.ext rfl
    (localModel.sums.substitution.2.2 σ pair _ (normalize_heq _ _ _).symm).1)

theorem second?_substitution (σ : C.toCwf.Sub Δ Γ) (A : C.toCwf.Ty Γ)
    (B : C.toCwf.Ty (C.toCwf.ext Γ A))
    (pair : C.toCwf.Tm Γ (localModel.sums.operations.sigma A B)) :
    (second? localModel A B (some ⟨_, pair⟩)).map (fun value => value.substitute σ) =
      second? localModel (C.toCwf.tySub A σ) (C.toCwf.tySub B (TypeOver.extensionSubstitution σ A))
        (some ⟨_, normalize localModel.sums σ (C.toCwf.tmSub pair σ)⟩) := by
  rw [second?_supplied localModel, second?_supplied localModel, Option.map_some]
  apply congrArg some
  have projections := localModel.sums.substitution.2.2 σ pair _ (normalize_heq _ _ _).symm
  apply Sigma.ext
  · change C.toCwf.tySub (C.toCwf.tySub B
      (selfExtend C.toCwf (localModel.sums.operations.fst pair))) σ = _
    rw [← C.toCwf.tySub_comp, ← selfExtend_substitution σ (localModel.sums.operations.fst pair),
      C.toCwf.tySub_comp, eq_of_heq projections.1]
  · exact projections.2

/- The independently defined canonical sum lift also commutes with a
supplied pair section. -/
theorem sumReindex_selfExtend (σ : C.toCwf.Sub Δ Γ) (A : C.toCwf.Ty Γ)
    (B : C.toCwf.Ty (C.toCwf.ext Γ A))
    (pair : C.toCwf.Tm Γ (localModel.sums.operations.sigma A B)) :
    C.toCwf.compS (sumReindex localModel.sums σ A B)
      (selfExtend C.toCwf (normalize localModel.sums σ (C.toCwf.tmSub pair σ))) =
      C.toCwf.compS (selfExtend C.toCwf pair) σ :=
  ContextualSumSectionSubstitution.sumReindex_selfExtend localModel.sums σ A B pair

theorem sumEliminate?_substitution (σ : C.toCwf.Sub Δ Γ) (A : C.toCwf.Ty Γ)
    (B : C.toCwf.Ty (C.toCwf.ext Γ A))
    (M : C.toCwf.Ty (C.toCwf.ext Γ (localModel.sums.operations.sigma A B)))
    (branch : C.toCwf.Tm (C.toCwf.ext (C.toCwf.ext Γ A) B)
      (C.toCwf.tySub M (pack localModel.sums A B)))
    (pair : C.toCwf.Tm Γ (localModel.sums.operations.sigma A B)) :
    (sumEliminate? localModel A B M (some ⟨_, branch⟩) (some ⟨_, pair⟩)).map
      (fun value => value.substitute σ) =
      sumEliminate? localModel (C.toCwf.tySub A σ)
        (C.toCwf.tySub B (TypeOver.extensionSubstitution σ A))
        (C.toCwf.tySub M (sumReindex localModel.sums σ A B))
        (some ⟨_, reindexBody localModel.sums σ A B M branch⟩)
        (some ⟨_, normalize localModel.sums σ (C.toCwf.tmSub pair σ)⟩) := by
  rw [sumEliminate?_supplied localModel A B M branch pair]
  rw [Option.map_some]
  have target := sumEliminate?_supplied localModel
    (C.toCwf.tySub A σ)
    (C.toCwf.tySub B (TypeOver.extensionSubstitution σ A))
    (C.toCwf.tySub M (sumReindex localModel.sums σ A B))
    (reindexBody localModel.sums σ A B M branch)
    (normalize localModel.sums σ (C.toCwf.tmSub pair σ))
  rw [target]
  exact congrArg some
    (ContextualSumSectionSubstitution.eliminated_value_substitution localModel.sums σ A B M branch pair)

/- Converted annotations transport an already checked section; equality
proofs cannot select a different section. -/
theorem check?_conversion {Γ : C.toCwf.Ctx} (result : Option (Value (C.toCwf) Γ))
    {A B : C.toCwf.Ty Γ} (equal : A = B) (value : C.toCwf.Tm Γ A)
    (checked : check? result A = some value) :
    check? result B = some (cast (congrArg (C.toCwf.Tm Γ) equal) value) := by
  cases equal
  exact checked

theorem check?_substitution {Γ Δ : C.toCwf.Ctx} (result : Option (Value (C.toCwf) Γ))
    (A : C.toCwf.Ty Γ) (value : C.toCwf.Tm Γ A)
    (checked : check? result A = some value) (σ : C.toCwf.Sub Δ Γ) :
    check? (result.map (fun actual => actual.substitute σ)) (C.toCwf.tySub A σ) =
      some (C.toCwf.tmSub value σ) := by
  rw [(check?_eq_some_iff _ _ _).mp checked, Option.map_some]
  exact check?_supplied _ _

end ModelData

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Abstract
