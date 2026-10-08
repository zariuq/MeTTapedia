import Mettapedia.TypeTheory.Calculi.NativeDependent.ExternalConstructorInterpretation

/-!
# Model substitution for checked logical constructors

The model operations act on actual supplied sections. Their separate local
substitution laws earn commutation of each constructor's checked readout.
No commutation law for a complete source evaluator is assumed here.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.External

open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.ContextualModelTelescopes
open Mettapedia.TypeTheory.ContextualSumComprehension
open Mettapedia.TypeTheory.ContextualProductComparison (selfExtend)
open Mettapedia.TypeTheory.ContextualTypeOperations

universe u c s t m

variable {S : Symbols.{u}} {C : CwfWithTerminal.{c, s, t, m}}

namespace ModelData

variable (model : ModelData S C) {Γ Δ : C.toCwf.Ctx}

theorem product_value_substitute (stable : StrictPiSubstitution model.products)
    (σ : C.toCwf.Sub Δ Γ) (A : C.toCwf.Ty Γ) (B : C.toCwf.Ty (C.toCwf.ext Γ A))
    (function : C.toCwf.Tm Γ (model.products.pi A B)) :
    Value.substitute (⟨_, function⟩ : Value C.toCwf Γ) σ =
      ⟨_, reindexFunction model.products stable.1 σ function⟩ :=
  Sigma.ext (stable.1 σ A B) (reindexFunction_heq model.products stable.1 σ function).symm

theorem sum_value_substitute (σ : C.toCwf.Sub Δ Γ) (A : C.toCwf.Ty Γ)
    (B : C.toCwf.Ty (C.toCwf.ext Γ A))
    (pair : C.toCwf.Tm Γ (model.sums.operations.sigma A B)) :
    Value.substitute (⟨_, pair⟩ : Value C.toCwf Γ) σ =
      ⟨_, normalize model.sums σ (C.toCwf.tmSub pair σ)⟩ :=
  Sigma.ext (model.sums.substitution.1 σ A B) (normalize_heq _ _ _).symm

theorem second_value_substitute (σ : C.toCwf.Sub Δ Γ) (A : C.toCwf.Ty Γ)
    (B : C.toCwf.Ty (C.toCwf.ext Γ A)) (first : C.toCwf.Tm Γ A)
    (second : C.toCwf.Tm Γ (C.toCwf.tySub B (selfExtend C.toCwf first))) :
    Value.substitute (⟨_, second⟩ : Value C.toCwf Γ) σ =
      ⟨_, reindexPairSecond σ first second⟩ := by
  apply Sigma.ext
  · change C.toCwf.tySub (C.toCwf.tySub B (selfExtend C.toCwf first)) σ = _
    rw [← C.toCwf.tySub_comp, ← selfExtend_substitution σ first, C.toCwf.tySub_comp]
  · exact (reindexPairSecond_heq _ _ _).symm

theorem lambda?_substitution (stable : StrictPiSubstitution model.products)
    (σ : C.toCwf.Sub Δ Γ) (A : C.toCwf.Ty Γ) (B : C.toCwf.Ty (C.toCwf.ext Γ A))
    (body : C.toCwf.Tm (C.toCwf.ext Γ A) B) :
    (model.lambda? A B (some ⟨B, body⟩)).map (fun value => value.substitute σ) =
      model.lambda? (C.toCwf.tySub A σ) (C.toCwf.tySub B (TypeOver.extensionSubstitution σ A))
        (some ⟨_, C.toCwf.tmSub body (TypeOver.extensionSubstitution σ A)⟩) := by
  rw [lambda?_supplied, lambda?_supplied, Option.map_some]
  exact congrArg some (Sigma.ext (stable.1 σ A B) (stable.2.1 σ body))

theorem application?_substitution (stable : StrictPiSubstitution model.products)
    (σ : C.toCwf.Sub Δ Γ) (A : C.toCwf.Ty Γ) (B : C.toCwf.Ty (C.toCwf.ext Γ A))
    (function : C.toCwf.Tm Γ (model.products.pi A B)) (argument : C.toCwf.Tm Γ A) :
    (model.application? A B (some ⟨_, function⟩) (some ⟨_, argument⟩)).map
      (fun value => value.substitute σ) =
      model.application? (C.toCwf.tySub A σ) (C.toCwf.tySub B (TypeOver.extensionSubstitution σ A))
        (some ⟨_, reindexFunction model.products stable.1 σ function⟩)
        (some ⟨_, C.toCwf.tmSub argument σ⟩) := by
  rw [application?_supplied, application?_supplied, Option.map_some]
  apply congrArg some
  apply Sigma.ext
  · change C.toCwf.tySub (C.toCwf.tySub B (selfExtend C.toCwf argument)) σ = _
    rw [← C.toCwf.tySub_comp, ← selfExtend_substitution σ argument, C.toCwf.tySub_comp]
  · exact stable.2.2 σ function argument _ (reindexFunction_heq _ _ _ _).symm

theorem pair?_substitution (σ : C.toCwf.Sub Δ Γ) (A : C.toCwf.Ty Γ)
    (B : C.toCwf.Ty (C.toCwf.ext Γ A)) (first : C.toCwf.Tm Γ A)
    (second : C.toCwf.Tm Γ (C.toCwf.tySub B (selfExtend C.toCwf first))) :
    (model.pair? A B (some ⟨_, first⟩) (some ⟨_, second⟩)).map
      (fun value => value.substitute σ) =
      model.pair? (C.toCwf.tySub A σ) (C.toCwf.tySub B (TypeOver.extensionSubstitution σ A))
        (some ⟨_, C.toCwf.tmSub first σ⟩) (some ⟨_, reindexPairSecond σ first second⟩) := by
  rw [pair?_supplied, pair?_supplied, Option.map_some]
  exact congrArg some (Sigma.ext (model.sums.substitution.1 σ A B)
    (model.sums.substitution.2.1 σ first second _ (reindexPairSecond_heq _ _ _).symm))

theorem first?_substitution (σ : C.toCwf.Sub Δ Γ) (A : C.toCwf.Ty Γ)
    (B : C.toCwf.Ty (C.toCwf.ext Γ A))
    (pair : C.toCwf.Tm Γ (model.sums.operations.sigma A B)) :
    (model.first? A B (some ⟨_, pair⟩)).map (fun value => value.substitute σ) =
      model.first? (C.toCwf.tySub A σ) (C.toCwf.tySub B (TypeOver.extensionSubstitution σ A))
        (some ⟨_, normalize model.sums σ (C.toCwf.tmSub pair σ)⟩) := by
  rw [first?_supplied, first?_supplied, Option.map_some]
  exact congrArg some (Sigma.ext rfl
    (model.sums.substitution.2.2 σ pair _ (normalize_heq _ _ _).symm).1)

theorem second?_substitution (σ : C.toCwf.Sub Δ Γ) (A : C.toCwf.Ty Γ)
    (B : C.toCwf.Ty (C.toCwf.ext Γ A))
    (pair : C.toCwf.Tm Γ (model.sums.operations.sigma A B)) :
    (model.second? A B (some ⟨_, pair⟩)).map (fun value => value.substitute σ) =
      model.second? (C.toCwf.tySub A σ) (C.toCwf.tySub B (TypeOver.extensionSubstitution σ A))
        (some ⟨_, normalize model.sums σ (C.toCwf.tmSub pair σ)⟩) := by
  rw [second?_supplied, second?_supplied, Option.map_some]
  apply congrArg some
  have projections := model.sums.substitution.2.2 σ pair _ (normalize_heq _ _ _).symm
  apply Sigma.ext
  · change C.toCwf.tySub (C.toCwf.tySub B
      (selfExtend C.toCwf (model.sums.operations.fst pair))) σ = _
    rw [← C.toCwf.tySub_comp, ← selfExtend_substitution σ (model.sums.operations.fst pair),
      C.toCwf.tySub_comp, eq_of_heq projections.1]
  · exact projections.2

/-- The independently defined canonical sum lift also commutes with a
supplied pair section. -/
theorem sumReindex_selfExtend (σ : C.toCwf.Sub Δ Γ) (A : C.toCwf.Ty Γ)
    (B : C.toCwf.Ty (C.toCwf.ext Γ A))
    (pair : C.toCwf.Tm Γ (model.sums.operations.sigma A B)) :
    C.toCwf.compS (sumReindex model.sums σ A B)
      (selfExtend C.toCwf (normalize model.sums σ (C.toCwf.tmSub pair σ))) =
      C.toCwf.compS (selfExtend C.toCwf pair) σ := by
  let newSum := model.sums.operations.sigma (C.toCwf.tySub A σ)
    (C.toCwf.tySub B (TypeOver.extensionSubstitution σ A))
  let newPair := normalize model.sums σ (C.toCwf.tmSub pair σ)
  apply TypeOver.substitution_ext
  · rw [← C.toCwf.comp_assoc, sumReindex_base, C.toCwf.comp_assoc, wk_selfExtend,
      C.toCwf.comp_id, ← C.toCwf.comp_assoc, wk_selfExtend, C.toCwf.id_comp]
  · have newTypes : C.toCwf.tySub
        (C.toCwf.tySub (model.sums.operations.sigma A B)
          (C.toCwf.wk (model.sums.operations.sigma A B))) (sumReindex model.sums σ A B) =
        C.toCwf.tySub newSum (C.toCwf.wk newSum) := by
      rw [← C.toCwf.tySub_comp, sumReindex_base, C.toCwf.tySub_comp,
        model.sums.substitution.1]
    have oldTypes : C.toCwf.tySub
        (C.toCwf.tySub (model.sums.operations.sigma A B)
          (C.toCwf.wk (model.sums.operations.sigma A B))) (selfExtend C.toCwf pair) =
        model.sums.operations.sigma A B := by
      rw [← C.toCwf.tySub_comp, wk_selfExtend, C.toCwf.tySub_id]
    have left := (TypeOver.tmSub_comp_heq
      (C.toCwf.vz (model.sums.operations.sigma A B)) (sumReindex model.sums σ A B)
      (selfExtend C.toCwf newPair)).trans
      ((TypeOver.tmSub_heq newTypes (sumReindex_variable model.sums σ A B)
        (selfExtend C.toCwf newPair)).trans
        ((vz_selfExtend newPair).trans (normalize_heq _ _ _)))
    have right := (TypeOver.tmSub_comp_heq
      (C.toCwf.vz (model.sums.operations.sigma A B)) (selfExtend C.toCwf pair) σ).trans
      (TypeOver.tmSub_heq oldTypes (vz_selfExtend pair) σ)
    exact left.trans right.symm

theorem sumEliminate?_substitution (σ : C.toCwf.Sub Δ Γ) (A : C.toCwf.Ty Γ)
    (B : C.toCwf.Ty (C.toCwf.ext Γ A))
    (M : C.toCwf.Ty (C.toCwf.ext Γ (model.sums.operations.sigma A B)))
    (branch : C.toCwf.Tm (C.toCwf.ext (C.toCwf.ext Γ A) B)
      (C.toCwf.tySub M (pack model.sums A B)))
    (pair : C.toCwf.Tm Γ (model.sums.operations.sigma A B)) :
    (model.sumEliminate? A B M (some ⟨_, branch⟩) (some ⟨_, pair⟩)).map
      (fun value => value.substitute σ) =
      model.sumEliminate? (C.toCwf.tySub A σ)
        (C.toCwf.tySub B (TypeOver.extensionSubstitution σ A))
        (C.toCwf.tySub M (sumReindex model.sums σ A B))
        (some ⟨_, reindexBody model.sums σ A B M branch⟩)
        (some ⟨_, normalize model.sums σ (C.toCwf.tmSub pair σ)⟩) := by
  rw [sumEliminate?_supplied, sumEliminate?_supplied, Option.map_some]
  apply congrArg some
  apply Sigma.ext
  · change C.toCwf.tySub (C.toCwf.tySub M (selfExtend C.toCwf pair)) σ = _
    rw [← C.toCwf.tySub_comp, ← model.sumReindex_selfExtend σ A B pair, C.toCwf.tySub_comp]
  · have original := (TypeOver.tmSub_comp_heq (eliminate model.sums A B M branch)
      (selfExtend C.toCwf pair) σ).symm
    rw [← model.sumReindex_selfExtend σ A B pair] at original
    have throughLift := original.trans (TypeOver.tmSub_comp_heq (eliminate model.sums A B M branch)
      (sumReindex model.sums σ A B)
      (selfExtend C.toCwf (normalize model.sums σ (C.toCwf.tmSub pair σ))))
    rw [eliminate_substitution] at throughLift
    exact throughLift

/-- Converted annotations transport an already checked section; equality
proofs cannot select a different section. -/
theorem check?_conversion {Γ : C.toCwf.Ctx} (result : Option (Value C.toCwf Γ))
    {A B : C.toCwf.Ty Γ} (equal : A = B) (value : C.toCwf.Tm Γ A)
    (checked : check? result A = some value) :
    check? result B = some (cast (congrArg (C.toCwf.Tm Γ) equal) value) := by
  cases equal
  exact checked

theorem check?_substitution {Γ Δ : C.toCwf.Ctx} (result : Option (Value C.toCwf Γ))
    (A : C.toCwf.Ty Γ) (value : C.toCwf.Tm Γ A)
    (checked : check? result A = some value) (σ : C.toCwf.Sub Δ Γ) :
    check? (result.map (fun actual => actual.substitute σ)) (C.toCwf.tySub A σ) =
      some (C.toCwf.tmSub value σ) := by
  rw [(check?_eq_some_iff _ _ _).mp checked, Option.map_some]
  exact check?_supplied _ _

end ModelData

end Mettapedia.TypeTheory.Calculi.NativeDependent.External
