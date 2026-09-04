import Mathlib.CategoryTheory.Functor.FullyFaithful
import Mettapedia.GSLT.Core.ContextualProfileInclusions
import Mettapedia.TypeTheory.ContextualProductComparison
import Mettapedia.TypeTheory.ContextualSumComparison
import Mettapedia.TypeTheory.DependentFunctionComparison

/-!
# Fibrewise fully faithful morphisms of contextual models

A simple and a dependent type theory can coexist without being identified
when the simple theory maps into the dependent theory by a pseudo CwF
morphism whose functor on every type fibre is fully faithful.  Full
faithfulness retains all display maps between translated types.  Properness
is separate: the target may contain types outside the image.

The canonical set-family models realize exactly this pattern.  Constant
families form a fully faithful image, ordinary function and product formers
agree with dependent Pi and Sigma on that image, and genuinely varying
families remain outside it.  Function extensionality is still an independent
axis, so the embedding does not choose an equality discipline.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.FibrewiseFullyFaithfulCwfMorphism

open CategoryTheory
open Mettapedia.GSLT.Core.ContextualLadder

universe u v w w'

/-- A pseudo CwF morphism which is fully faithful on the category of types
and display maps over every source context. -/
structure FibrewiseFullyFaithful
    (source target : CwfWithTerminal.{u, v, w, w'}) where
  morphism : PseudoCwfMorphism source target
  fullyFaithful : ∀ context,
    (morphism.mapTypeFunctor context).FullyFaithful

namespace FibrewiseFullyFaithful

variable {source target : CwfWithTerminal.{u, v, w, w'}}

/-- Full faithfulness reflects equality of display maps in every fibre. -/
theorem map_injective (embedding : FibrewiseFullyFaithful source target)
    {context : source.toCwf.Ctx}
    {first second : TypeOver source.toCwf context}
    {left right : first ⟶ second}
    (sameImage :
      (embedding.morphism.mapTypeFunctor context).map left =
        (embedding.morphism.mapTypeFunctor context).map right) :
    left = right :=
  (embedding.fullyFaithful context).map_injective sameImage

/-- A target type over the translated context is new when it is not in the
object image of the source type fibre. -/
def HasNewTypeAt (embedding : FibrewiseFullyFaithful source target)
    (context : source.toCwf.Ctx) : Prop :=
  ∃ targetType : TypeOver target.toCwf
      (embedding.morphism.base.obj ⟨context⟩).val,
    ¬ ∃ sourceType : TypeOver source.toCwf context,
      embedding.morphism.mapTypeObject sourceType = targetType

/-- Properness means that at some context the fully faithful inclusion does
not exhaust the target type fibre. -/
def Proper (embedding : FibrewiseFullyFaithful source target) : Prop :=
  ∃ context, embedding.HasNewTypeAt context

end FibrewiseFullyFaithful

/-! ## Canonical constant-family embedding -/

open Mettapedia.TypeTheory.ContextualProductComparison
open Mettapedia.TypeTheory.ContextualSumComparison
open Mettapedia.TypeTheory.DependencyExtensionalityOrthogonality

/-- Constant-family inclusion between the canonical set-family contextual
models is fibrewise fully faithful. -/
def setFamilyConstantEmbedding :
    FibrewiseFullyFaithful
      (SimpleFamiliesCwfWithTerminal.{w})
      (familiesCwfWithTerminal.{w}) where
  morphism := simpleToDependentPseudoMorphism
  fullyFaithful := simpleToDependentPseudoMorphism_fibreFullyFaithful

/-- The varying Boolean family witnesses that the fully faithful image is a
proper fragment of the dependent set-family model. -/
theorem setFamilyConstantEmbedding_proper :
    setFamilyConstantEmbedding.{0}.Proper := by
  refine ⟨Bool, ?_⟩
  refine ⟨(⟨Mettapedia.GSLT.Core.ContextualLadder.varyingBoolFamily⟩ :
    TypeOver (familiesCwf.{0}) Bool), ?_⟩
  exact varyingBoolFamily_not_in_pseudoMorphism_image

/-- Constant-family Pi and Sigma agree with the ordinary simple function and
product formers. -/
theorem constant_family_pi_sigma_agree :
    (ContextualProductComparison.simpleToDependent
        ContextualProductComparison.simpleFamiliesFunctions).pi
          (context := PUnit) Bool Nat = (Bool → Nat) ∧
      (ContextualSumComparison.simpleToDependent
        ContextualSumComparison.simpleFamiliesProducts).sigma
          (context := PUnit) Bool Nat = (Bool × Nat) :=
  ⟨ContextualProductComparison.constantFamily_pi_agrees Bool Nat,
    ContextualSumComparison.constantFamily_sigma_agrees Bool Nat⟩

/-- The ambient dependent theory has Pi and Sigma families which are not
equivalent to any constant family. -/
theorem dependent_pi_sigma_are_strictly_more_expressive :
    (¬ ∃ Constant : Type,
      ∀ context : Bool,
        Nonempty
          (((ContextualProductComparison.familiesProducts.pi
            (context := Bool) (constantFamily PUnit)
            (fun point =>
              DependencyExtensionalityOrthogonality.varyingBoolFamily
                point.1)) context) ≃
              Constant)) ∧
    (¬ ∃ Constant : Type,
      ∀ context : Bool,
        Nonempty
          (((ContextualSumComparison.familiesSums.sigma
            (context := Bool) (constantFamily PUnit)
            (fun point =>
              DependencyExtensionalityOrthogonality.varyingBoolFamily
                point.1)) context) ≃
              Constant)) :=
  ⟨ContextualProductComparison.varying_product_not_constant,
    ContextualSumComparison.varying_sum_not_constant⟩

/-- The complete compatibility criterion holds while dependency and
application extensionality remain orthogonal.  Thus a well-behaved simple
fragment inside a dependent theory does not decide whether functions retain
route-sensitive distinctions. -/
theorem constant_fragment_coexists_without_equality_collapse :
    setFamilyConstantEmbedding.{0}.Proper ∧
      (ContextualProductComparison.simpleToDependent
        ContextualProductComparison.simpleFamiliesFunctions).pi
          (context := PUnit) Bool Nat = (Bool → Nat) ∧
      (ContextualSumComparison.simpleToDependent
        ContextualSumComparison.simpleFamiliesProducts).sigma
          (context := PUnit) Bool Nat = (Bool × Nat) ∧
      simpleExtensional.ApplicationExtensional ∧
      simpleRouteSensitive.HasApplicationIndistinguishablePair ∧
      dependentExtensional.ApplicationExtensional ∧
      dependentRouteSensitive.HasApplicationIndistinguishablePair :=
  ⟨setFamilyConstantEmbedding_proper,
    constant_family_pi_sigma_agree.1,
    constant_family_pi_sigma_agree.2,
    simpleExtensional_applicationExtensional,
    simpleRouteSensitive_hasIndistinguishablePair,
    dependentExtensional_applicationExtensional,
    dependentRouteSensitive_hasIndistinguishablePair⟩

/-! ## Axiom audit -/

#print axioms FibrewiseFullyFaithful.map_injective
#print axioms setFamilyConstantEmbedding
#print axioms setFamilyConstantEmbedding_proper
#print axioms constant_family_pi_sigma_agree
#print axioms dependent_pi_sigma_are_strictly_more_expressive
#print axioms constant_fragment_coexists_without_equality_collapse

end Mettapedia.TypeTheory.FibrewiseFullyFaithfulCwfMorphism
