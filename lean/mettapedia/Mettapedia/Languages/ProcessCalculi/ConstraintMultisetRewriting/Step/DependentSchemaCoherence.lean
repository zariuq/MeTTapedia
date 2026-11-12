import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentSchemaArguments
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentFullTelescopes

/-!+# Typed schema arguments under reindexing and legal helper exchange

The existing dependent telescope pullbacks supply unique lifts of the new
explicit argument tuples. Independent helper exchange uses the existing
typed swap isomorphism. It is not an equality of raw substitutions and does
not license exchanging a declaration with one on which its type depends.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.Helpers

open _root_.CategoryTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedContextual

variable {Head : Type} {rules : Rules Head}

theorem instantiate_injective {Γ Δ : Context rules} (helpers : Helpers Γ)
    (baseMap : Δ ⟶ Γ) : Function.Injective (helpers.instantiate baseMap) := by
  intro first second same
  have tuples := congrArg (helpers.openingEquiv Δ) same
  rw [helpers.opening_instantiate, helpers.opening_instantiate] at tuples
  exact eq_of_heq (Sigma.mk.inj tuples).2

/-- Every substitution over a specified old environment supplies one tuple
over that very environment, rather than over an existential replacement. -/
theorem arguments_of_morphism {Γ Δ : Context rules} (helpers : Helpers Γ)
    (baseMap : Δ ⟶ Γ) (substitution : Δ ⟶ helpers.frame)
    (overBase : substitution ≫ helpers.weaken = baseMap) :
    ∃ args : helpers.Arguments baseMap, helpers.instantiate baseMap args = substitution := by
  rcases opening : helpers.openingEquiv Δ substitution with ⟨actualBase, args⟩
  have sameBase : actualBase = baseMap := by
    have projected := helpers.opening_base substitution
    rw [opening] at projected
    exact projected.trans overBase
  subst actualBase
  refine ⟨args, ?_⟩
  have inverse := congrArg (helpers.openingEquiv Δ).symm opening
  rw [Equiv.symm_apply_apply, helpers.openingEquiv_symm] at inverse
  exact inverse.symm

/-- The existing telescope pullback lifts each supplied tuple uniquely.
The old environment and every helper value are preserved by its two legs. -/
theorem reindexed_arguments_existUnique {Γ Δ X : Context rules}
    (helpers : Helpers Γ) (substitution : Δ ⟶ Γ) (baseMap : X ⟶ Δ)
    (args : helpers.Arguments (baseMap ≫ substitution)) :
    ∃! lifted : (helpers.reindex substitution).Arguments baseMap,
      (helpers.reindex substitution).instantiate baseMap lifted ≫ Helpers.lift substitution helpers =
        helpers.instantiate (baseMap ≫ substitution) args := by
  let target := helpers.instantiate (baseMap ≫ substitution) args
  have agrees : baseMap ≫ substitution = target ≫ helpers.weaken :=
    (helpers.instantiate_weaken _ args).symm
  let factor := Helpers.into substitution helpers baseMap target agrees
  obtain ⟨lifted, assembles⟩ := (helpers.reindex substitution).arguments_of_morphism baseMap factor
    (Helpers.into_weaken substitution helpers baseMap target agrees)
  refine ⟨lifted, ?_, ?_⟩
  · change (helpers.reindex substitution).instantiate baseMap lifted ≫ Helpers.lift substitution helpers = target
    rw [assembles]
    exact Helpers.into_lift substitution helpers baseMap target agrees
  · intro other sameLift
    apply (helpers.reindex substitution).instantiate_injective baseMap
    have unique := Helpers.into_unique substitution helpers baseMap target agrees
      ((helpers.reindex substitution).instantiate baseMap other)
      ((helpers.reindex substitution).instantiate_weaken baseMap other) sameLift
    exact unique.trans assembles.symm

/-- Substitutions into isomorphic helper targets correspond by the actual
isomorphism, with no quotient on the substitutions. -/
def substitutionIso {Γ Δ X : Context rules} (iso : Γ ≅ Δ) : (X ⟶ Γ) ≃ (X ⟶ Δ) where
  toFun substitution := substitution ≫ iso.hom
  invFun substitution := substitution ≫ iso.inv
  left_inv substitution := by simp
  right_inv substitution := by simp

def assignmentIso {Γ X : Context rules} (first second : Helpers Γ)
    (iso : first.frame ≅ second.frame) :
    (Σ baseMap : X ⟶ Γ, first.Arguments baseMap) ≃
      (Σ baseMap : X ⟶ Γ, second.Arguments baseMap) :=
  (first.openingEquiv X).symm.trans ((substitutionIso iso).trans (second.openingEquiv X))

theorem instantiate_assignmentIso {Γ X : Context rules} (first second : Helpers Γ)
    (iso : first.frame ≅ second.frame) (assignment : Σ baseMap : X ⟶ Γ, first.Arguments baseMap) :
    second.instantiate (first.assignmentIso second iso assignment).1
      (first.assignmentIso second iso assignment).2 =
        first.instantiate assignment.1 assignment.2 ≫ iso.hom := by
  change second.instantiate
      (second.openingEquiv X ((first.openingEquiv X).symm assignment ≫ iso.hom)).1
      (second.openingEquiv X ((first.openingEquiv X).symm assignment ≫ iso.hom)).2 = _
  rw [second.instantiate_opening, first.openingEquiv_symm]

theorem assignmentIso_base {Γ X : Context rules} (first second : Helpers Γ)
    (iso : first.frame ≅ second.frame) (overBase : iso.hom ≫ second.weaken = first.weaken)
    (assignment : Σ baseMap : X ⟶ Γ, first.Arguments baseMap) :
    (first.assignmentIso second iso assignment).1 = assignment.1 := by
  have projected := second.instantiate_weaken
    (first.assignmentIso second iso assignment).1 (first.assignmentIso second iso assignment).2
  rw [instantiate_assignmentIso, Category.assoc, overBase, first.instantiate_weaken] at projected
  exact projected.symm

open ContextualDependentParameterExchange (second context)

/-- The second type was already formed over the old context. It is weakened
under the first helper, which is precisely the independence needed for exchange. -/
abbrev independentPair {Γ : Context rules} (first next : TypeOver Γ) : Helpers Γ :=
  .cons first (.cons (second first next) (.nil _))

theorem independentPair_weaken {Γ : Context rules} (first next : TypeOver Γ) :
    (independentPair first next).weaken = ContextualDependentParameterExchange.base first next := by
  simp only [independentPair, Helpers.weaken]
  rfl

def independentPairIso {Γ : Context rules} (first next : TypeOver Γ) :
    (independentPair first next).frame ≅ (independentPair next first).frame :=
  swapIso first next

def independentSwap {Γ X : Context rules} (first next : TypeOver Γ) :
    (Σ baseMap : X ⟶ Γ, (independentPair first next).Arguments baseMap) ≃
      (Σ baseMap : X ⟶ Γ, (independentPair next first).Arguments baseMap) :=
  (independentPair first next).assignmentIso (independentPair next first) (independentPairIso first next)

theorem independentSwap_preserves_base {Γ X : Context rules} (first next : TypeOver Γ)
    (assignment : Σ baseMap : X ⟶ Γ, (independentPair first next).Arguments baseMap) :
    (independentSwap first next assignment).1 = assignment.1 := by
  apply assignmentIso_base
  rw [independentPair_weaken, independentPair_weaken]
  change ContextualDependentParameterExchange.swap first next ≫
      (projectionHom _ (second next first) ≫ projectionHom Γ next) = _
  rw [← Category.assoc, swap_projection, lower_projection]

theorem independentSwap_twice {Γ X : Context rules} (first next : TypeOver Γ)
    (assignment : Σ baseMap : X ⟶ Γ, (independentPair first next).Arguments baseMap) :
    independentSwap next first (independentSwap first next assignment) = assignment := by
  apply ((independentPair first next).openingEquiv X).symm.injective
  simp only [openingEquiv_symm]
  rw [independentSwap, instantiate_assignmentIso, independentSwap, instantiate_assignmentIso]
  change ((independentPair first next).instantiate assignment.1 assignment.2 ≫
      ContextualDependentParameterExchange.swap first next) ≫
      ContextualDependentParameterExchange.swap next first = _
  exact (substitutionIso (swapIso first next)).left_inv
    (show X ⟶ context first next from
      (independentPair first next).instantiate assignment.1 assignment.2)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.Helpers
