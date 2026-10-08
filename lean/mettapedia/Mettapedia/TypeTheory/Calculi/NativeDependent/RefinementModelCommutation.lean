import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementConstructorInterpretation
import Mettapedia.TypeTheory.ContextualSumSectionSubstitution

/-!
# Model substitution for checked logical constructors

The model operations act on actual supplied sections. Their separate local
substitution laws earn commutation of each constructor's checked readout.
No commutation law for a complete source evaluator is assumed here.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement

open _root_.CategoryTheory
open NativeLocalTypeFormers
open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.ContextualModelTelescopes
open Mettapedia.TypeTheory.ContextualSumComprehension
open Mettapedia.TypeTheory.ContextualProductComparison (selfExtend)
open Mettapedia.TypeTheory.ContextualTypeOperations

universe u v

variable {S : Symbols.{v}} {C : Type u} [Category.{u} C]

namespace ModelData

attribute [local irreducible] products sums ContextualSumComprehension.normalize
  ContextualSumComprehension.reindexBody

variable (model : ModelData S C) {Γ Δ : (NativeModel C).toCwf.Ctx}

set_option backward.isDefEq.respectTransparency false in
theorem product_value_substitute (stable : StrictPiSubstitution model.products)
    (σ : (NativeModel C).toCwf.Sub Δ Γ) (A : (NativeModel C).toCwf.Ty Γ) (B : (NativeModel C).toCwf.Ty ((NativeModel C).toCwf.ext Γ A))
    (function : (NativeModel C).toCwf.Tm Γ (model.products.pi A B)) :
    Value.substitute (⟨_, function⟩ : Value ((NativeModel C).toCwf) Γ) σ =
      ⟨_, reindexFunction model.products stable.1 σ function⟩ :=
  Sigma.ext (stable.1 σ A B) (reindexFunction_heq model.products stable.1 σ function).symm

set_option backward.isDefEq.respectTransparency false in
theorem sum_value_substitute (σ : (NativeModel C).toCwf.Sub Δ Γ) (A : (NativeModel C).toCwf.Ty Γ)
    (B : (NativeModel C).toCwf.Ty ((NativeModel C).toCwf.ext Γ A))
    (pair : (NativeModel C).toCwf.Tm Γ (model.sums.operations.sigma A B)) :
    Value.substitute (⟨_, pair⟩ : Value ((NativeModel C).toCwf) Γ) σ =
      ⟨_, normalize model.sums σ ((NativeModel C).toCwf.tmSub pair σ)⟩ :=
  Sigma.ext (model.sums.substitution.1 σ A B) (normalize_heq model.sums σ ((NativeModel C).toCwf.tmSub pair σ)).symm

set_option backward.isDefEq.respectTransparency false in
theorem second_value_substitute (σ : (NativeModel C).toCwf.Sub Δ Γ) (A : (NativeModel C).toCwf.Ty Γ)
    (B : (NativeModel C).toCwf.Ty ((NativeModel C).toCwf.ext Γ A)) (first : (NativeModel C).toCwf.Tm Γ A)
    (second : (NativeModel C).toCwf.Tm Γ ((NativeModel C).toCwf.tySub B (selfExtend (NativeModel C).toCwf first))) :
    Value.substitute (⟨_, second⟩ : Value ((NativeModel C).toCwf) Γ) σ =
      ⟨_, reindexPairSecond σ first second⟩ := by
  apply Sigma.ext
  · change (NativeModel C).toCwf.tySub ((NativeModel C).toCwf.tySub B (selfExtend (NativeModel C).toCwf first)) σ = _
    rw [← (NativeModel C).toCwf.tySub_comp, ← selfExtend_substitution σ first, (NativeModel C).toCwf.tySub_comp]
  · exact (reindexPairSecond_heq (C := (NativeModel C).toCwf) σ first second).symm

set_option backward.isDefEq.respectTransparency false in
theorem lambda?_substitution (stable : StrictPiSubstitution model.products)
    (σ : (NativeModel C).toCwf.Sub Δ Γ) (A : (NativeModel C).toCwf.Ty Γ) (B : (NativeModel C).toCwf.Ty ((NativeModel C).toCwf.ext Γ A))
    (body : (NativeModel C).toCwf.Tm ((NativeModel C).toCwf.ext Γ A) B) :
    (model.lambda? A B (some ⟨B, body⟩)).map (fun value => value.substitute σ) =
      model.lambda? ((NativeModel C).toCwf.tySub A σ) ((NativeModel C).toCwf.tySub B (TypeOver.extensionSubstitution σ A))
        (some ⟨_, (NativeModel C).toCwf.tmSub body (TypeOver.extensionSubstitution σ A)⟩) := by
  rw [lambda?_supplied, lambda?_supplied, Option.map_some]
  exact congrArg some (Sigma.ext (stable.1 σ A B) (stable.2.1 σ body))

set_option backward.isDefEq.respectTransparency false in
theorem application?_substitution (stable : StrictPiSubstitution model.products)
    (σ : (NativeModel C).toCwf.Sub Δ Γ) (A : (NativeModel C).toCwf.Ty Γ) (B : (NativeModel C).toCwf.Ty ((NativeModel C).toCwf.ext Γ A))
    (function : (NativeModel C).toCwf.Tm Γ (model.products.pi A B)) (argument : (NativeModel C).toCwf.Tm Γ A) :
    (model.application? A B (some ⟨_, function⟩) (some ⟨_, argument⟩)).map
      (fun value => value.substitute σ) =
      model.application? ((NativeModel C).toCwf.tySub A σ) ((NativeModel C).toCwf.tySub B (TypeOver.extensionSubstitution σ A))
        (some ⟨_, reindexFunction model.products stable.1 σ function⟩)
        (some ⟨_, (NativeModel C).toCwf.tmSub argument σ⟩) := by
  rw [application?_supplied, application?_supplied, Option.map_some]
  apply congrArg some
  apply Sigma.ext
  · change (NativeModel C).toCwf.tySub ((NativeModel C).toCwf.tySub B (selfExtend (NativeModel C).toCwf argument)) σ = _
    rw [← (NativeModel C).toCwf.tySub_comp, ← selfExtend_substitution σ argument, (NativeModel C).toCwf.tySub_comp]
  · exact stable.2.2 σ function argument _ (reindexFunction_heq _ _ _ _).symm

set_option backward.isDefEq.respectTransparency false in
theorem pair?_substitution (σ : (NativeModel C).toCwf.Sub Δ Γ) (A : (NativeModel C).toCwf.Ty Γ)
    (B : (NativeModel C).toCwf.Ty ((NativeModel C).toCwf.ext Γ A)) (first : (NativeModel C).toCwf.Tm Γ A)
    (second : (NativeModel C).toCwf.Tm Γ ((NativeModel C).toCwf.tySub B (selfExtend (NativeModel C).toCwf first))) :
    (model.pair? A B (some ⟨_, first⟩) (some ⟨_, second⟩)).map
      (fun value => value.substitute σ) =
      model.pair? ((NativeModel C).toCwf.tySub A σ) ((NativeModel C).toCwf.tySub B (TypeOver.extensionSubstitution σ A))
        (some ⟨_, (NativeModel C).toCwf.tmSub first σ⟩) (some ⟨_, reindexPairSecond σ first second⟩) := by
  rw [pair?_supplied, pair?_supplied, Option.map_some]
  exact congrArg some (Sigma.ext (model.sums.substitution.1 σ A B)
    (model.sums.substitution.2.1 σ first second _ (reindexPairSecond_heq _ _ _).symm))

set_option backward.isDefEq.respectTransparency false in
theorem first?_substitution (σ : (NativeModel C).toCwf.Sub Δ Γ) (A : (NativeModel C).toCwf.Ty Γ)
    (B : (NativeModel C).toCwf.Ty ((NativeModel C).toCwf.ext Γ A))
    (pair : (NativeModel C).toCwf.Tm Γ (model.sums.operations.sigma A B)) :
    (model.first? A B (some ⟨_, pair⟩)).map (fun value => value.substitute σ) =
      model.first? ((NativeModel C).toCwf.tySub A σ) ((NativeModel C).toCwf.tySub B (TypeOver.extensionSubstitution σ A))
        (some ⟨_, normalize model.sums σ ((NativeModel C).toCwf.tmSub pair σ)⟩) := by
  rw [first?_supplied, first?_supplied, Option.map_some]
  exact congrArg some (Sigma.ext rfl
    (model.sums.substitution.2.2 σ pair _ (normalize_heq _ _ _).symm).1)

set_option backward.isDefEq.respectTransparency false in
theorem second?_substitution (σ : (NativeModel C).toCwf.Sub Δ Γ) (A : (NativeModel C).toCwf.Ty Γ)
    (B : (NativeModel C).toCwf.Ty ((NativeModel C).toCwf.ext Γ A))
    (pair : (NativeModel C).toCwf.Tm Γ (model.sums.operations.sigma A B)) :
    (model.second? A B (some ⟨_, pair⟩)).map (fun value => value.substitute σ) =
      model.second? ((NativeModel C).toCwf.tySub A σ) ((NativeModel C).toCwf.tySub B (TypeOver.extensionSubstitution σ A))
        (some ⟨_, normalize model.sums σ ((NativeModel C).toCwf.tmSub pair σ)⟩) := by
  rw [second?_supplied, second?_supplied, Option.map_some]
  apply congrArg some
  have projections := model.sums.substitution.2.2 σ pair _ (normalize_heq _ _ _).symm
  apply Sigma.ext
  · change (NativeModel C).toCwf.tySub ((NativeModel C).toCwf.tySub B
      (selfExtend (NativeModel C).toCwf (model.sums.operations.fst pair))) σ = _
    rw [← (NativeModel C).toCwf.tySub_comp, ← selfExtend_substitution σ (model.sums.operations.fst pair),
      (NativeModel C).toCwf.tySub_comp, eq_of_heq projections.1]
  · exact projections.2

/- The independently defined canonical sum lift also commutes with a
supplied pair section. -/
set_option backward.isDefEq.respectTransparency false in
theorem sumReindex_selfExtend (σ : (NativeModel C).toCwf.Sub Δ Γ) (A : (NativeModel C).toCwf.Ty Γ)
    (B : (NativeModel C).toCwf.Ty ((NativeModel C).toCwf.ext Γ A))
    (pair : (NativeModel C).toCwf.Tm Γ (model.sums.operations.sigma A B)) :
    (NativeModel C).toCwf.compS (sumReindex model.sums σ A B)
      (selfExtend (NativeModel C).toCwf (normalize model.sums σ ((NativeModel C).toCwf.tmSub pair σ))) =
      (NativeModel C).toCwf.compS (selfExtend (NativeModel C).toCwf pair) σ :=
  ContextualSumSectionSubstitution.sumReindex_selfExtend model.sums σ A B pair

set_option backward.isDefEq.respectTransparency false in
theorem sumEliminate?_substitution (σ : (NativeModel C).toCwf.Sub Δ Γ) (A : (NativeModel C).toCwf.Ty Γ)
    (B : (NativeModel C).toCwf.Ty ((NativeModel C).toCwf.ext Γ A))
    (M : (NativeModel C).toCwf.Ty ((NativeModel C).toCwf.ext Γ (model.sums.operations.sigma A B)))
    (branch : (NativeModel C).toCwf.Tm ((NativeModel C).toCwf.ext ((NativeModel C).toCwf.ext Γ A) B)
      ((NativeModel C).toCwf.tySub M (pack model.sums A B)))
    (pair : (NativeModel C).toCwf.Tm Γ (model.sums.operations.sigma A B)) :
    (model.sumEliminate? A B M (some ⟨_, branch⟩) (some ⟨_, pair⟩)).map
      (fun value => value.substitute σ) =
      model.sumEliminate? ((NativeModel C).toCwf.tySub A σ)
        ((NativeModel C).toCwf.tySub B (TypeOver.extensionSubstitution σ A))
        ((NativeModel C).toCwf.tySub M (sumReindex model.sums σ A B))
        (some ⟨_, reindexBody model.sums σ A B M branch⟩)
        (some ⟨_, normalize model.sums σ ((NativeModel C).toCwf.tmSub pair σ)⟩) := by
  rw [model.sumEliminate?_supplied A B M branch pair]
  rw [Option.map_some]
  have target := model.sumEliminate?_supplied
    ((NativeModel C).toCwf.tySub A σ)
    ((NativeModel C).toCwf.tySub B (TypeOver.extensionSubstitution σ A))
    ((NativeModel C).toCwf.tySub M (sumReindex model.sums σ A B))
    (reindexBody model.sums σ A B M branch)
    (normalize model.sums σ ((NativeModel C).toCwf.tmSub pair σ))
  rw [target]
  exact congrArg some
    (ContextualSumSectionSubstitution.eliminated_value_substitution model.sums σ A B M branch pair)

/- Converted annotations transport an already checked section; equality
proofs cannot select a different section. -/
set_option backward.isDefEq.respectTransparency false in
theorem check?_conversion {Γ : (NativeModel C).toCwf.Ctx} (result : Option (Value ((NativeModel C).toCwf) Γ))
    {A B : (NativeModel C).toCwf.Ty Γ} (equal : A = B) (value : (NativeModel C).toCwf.Tm Γ A)
    (checked : check? result A = some value) :
    check? result B = some (cast (congrArg ((NativeModel C).toCwf.Tm Γ) equal) value) := by
  cases equal
  exact checked

set_option backward.isDefEq.respectTransparency false in
theorem check?_substitution {Γ Δ : (NativeModel C).toCwf.Ctx} (result : Option (Value ((NativeModel C).toCwf) Γ))
    (A : (NativeModel C).toCwf.Ty Γ) (value : (NativeModel C).toCwf.Tm Γ A)
    (checked : check? result A = some value) (σ : (NativeModel C).toCwf.Sub Δ Γ) :
    check? (result.map (fun actual => actual.substitute σ)) ((NativeModel C).toCwf.tySub A σ) =
      some ((NativeModel C).toCwf.tmSub value σ) := by
  rw [(check?_eq_some_iff _ _ _).mp checked, Option.map_some]
  exact check?_supplied _ _

end ModelData

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement
