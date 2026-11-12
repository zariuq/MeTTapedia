import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentVariableFactorization
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentEta

/-!
# The rules of pattern unification as universal constructions, in the category of contexts

The category is the category of formed contexts and typed substitutions of the calculus
(`TypedContextual.contextCategory`): a morphism `Δ ⟶ Γ` gives, for every variable of `Γ`, a term over `Δ`. A
**pattern** is a typed inclusion (`Inclusion Γ Δ`): an injective map of variables that is a morphism of contexts, so
the selected variables are closed under the dependency of their declared types.

* **A pattern is cancellable** (`inclusion_cancel`): if two substitutions out of `Γ` agree after the pattern, they
  are equal. In this category the pattern's morphism goes from the larger context to the smaller, so the statement is
  that it is an epimorphism (`inclusion_epi`); read from the arity to the scope, as in the categorical treatments of
  simply typed pattern unification, it is the statement that patterns are monomorphisms.
* **The agreement of two variable maps is their equalizer** (`agreement_equalizer`): a variable map into the
  agreement set of two maps factors, uniquely, through any injective map whose image is that set. This is the
  universal property behind the rule for one unknown under two patterns, at the level of variable maps. For typed
  inclusions the factor is again a typed inclusion when the maps are compatible with the declarations
  (`ContextualDependentVariableFactorization.inclusion`); that the agreement set of two typed patterns is itself a
  formed context is a further condition, which is not proved here.
* **A principal answer is a weak universal solution** (`residual_unique`): the factor of a solution through a
  principal answer exists by definition, and any two factors agree, up to typed equality, on every term of the
  store's frame carried along the answer. The category has equality of substitutions on the nose; the uniqueness
  that a coequalizer asks holds only up to typed equality of the images.

Inversion factors a term through a pattern, uniquely: that is `ContextualDependentTypedInversion.Recovery.unique`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentUniversal

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentTypedInversion ContextualDependentVariableFactorization

variable {Head : Type} {rules : Rules Head}

/-! ## Patterns are cancellable -/

/-- **A pattern is cancellable**: two substitutions that agree after a typed inclusion are equal. -/
theorem inclusion_cancel {Γ Δ Z : Context rules} (inclusion : Inclusion Γ Δ) (first second : Γ ⟶ Z)
    (same : inclusion.hom ≫ first = inclusion.hom ≫ second) : first = second := by
  apply Hom.ext
  funext index
  apply rename_injective inclusion.forward inclusion.injective
  have at_index := congrArg (fun morphism : Δ ⟶ Z => morphism.substitution index) same
  change subst (renSub inclusion.forward) (first.substitution index) =
    subst (renSub inclusion.forward) (second.substitution index) at at_index
  rwa [subst_renSub, subst_renSub] at at_index

/-- **The morphism of a pattern is an epimorphism** of the category of contexts. -/
theorem inclusion_epi {Γ Δ : Context rules} (inclusion : Inclusion Γ Δ) : Epi inclusion.hom :=
  ⟨fun first second same => inclusion_cancel inclusion first second same⟩

/-! ## The agreement of two variable maps is their equalizer -/

/-- **The agreement set is an equalizer of variable maps**: a variable map on which two maps agree factors, uniquely,
through an injective map whose image is the set of variables on which they agree. -/
theorem agreement_equalizer {n k m j : Nat} (left right : Ren k m) (agreement : Ren n k)
    (injective : Function.Injective agreement)
    (image : ∀ index, left index = right index → ∃ prior, agreement prior = index)
    (other : Ren j k) (agrees : ∀ index, left (other index) = right (other index)) :
    ∃ factor : Ren j n, (∀ index, agreement (factor index) = other index) ∧
      ∀ second : Ren j n, (∀ index, agreement (second index) = other index) → second = factor := by
  refine ⟨ContextualDependentVariableFactorization.factor agreement other fun index => image _ (agrees index),
    factor_image agreement other _, fun second isFactor => ?_⟩
  exact factor_unique agreement other _ injective second isFactor

/-- The agreement map equalizes: on its image the two maps agree, when it selects only agreeing variables. -/
theorem agreement_equalizes {n k m : Nat} (left right : Ren k m) (agreement : Ren n k)
    (selects : ∀ prior, left (agreement prior) = right (agreement prior)) :
    (fun prior => left (agreement prior)) = fun prior => right (agreement prior) :=
  funext selects

/-- **Injectivity is needed for the uniqueness of the factor**: through the map that sends two variables to one, the
identity of one variable has two different factors. -/
theorem agreement_needs_injective :
    ∃ first second : Ren 1 2, first ≠ second ∧
      (∀ index, (fun _ : Fin 2 => (0 : Fin 1)) (first index) = (fun index : Fin 1 => index) index) ∧
      (∀ index, (fun _ : Fin 2 => (0 : Fin 1)) (second index) = (fun index : Fin 1 => index) index) := by
  refine ⟨fun _ => 0, fun _ => 1, fun same => ?_, fun index => ?_, fun index => ?_⟩
  · exact absurd (congrFun same 0) (by decide)
  · exact (Fin.fin_one_eq_zero index).symm
  · exact (Fin.fin_one_eq_zero index).symm

/-! ## A principal answer is a weak universal solution -/

variable {L : Type} [UniverseLevel.LevelOrder L] (levels : LevelModel rules L)

/-- **Two factors of one solution through an answer agree on the answer's image**, up to typed equality: the
uniqueness half of the universal property of a principal answer. -/
theorem residual_unique {Γ M Δ : Context rules} (answer : M ⟶ Γ) (solution : Δ ⟶ Γ) (first second : Δ ⟶ M)
    (factorFirst : ∀ term : TotalTerm Γ,
      (ContextualDependentEta.frames levels).E (term.reindex solution) (term.reindex (first ≫ answer)))
    (factorSecond : ∀ term : TotalTerm Γ,
      (ContextualDependentEta.frames levels).E (term.reindex solution) (term.reindex (second ≫ answer)))
    (term : TotalTerm Γ) :
    (ContextualDependentEta.frames levels).E (term.reindex (first ≫ answer)) (term.reindex (second ≫ answer)) :=
  ((ContextualDependentEta.frames levels).equivalence Δ).trans
    (((ContextualDependentEta.frames levels).equivalence Δ).symm (factorFirst term)) (factorSecond term)

end ContextualDependentUniversal
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
