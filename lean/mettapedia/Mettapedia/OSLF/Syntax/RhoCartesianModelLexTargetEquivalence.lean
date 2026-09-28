import Mettapedia.OSLF.Syntax.CartesianModelLexTargetEquivalence
import Mettapedia.OSLF.Syntax.RhoCartesianModelLexTarget
import Mettapedia.OSLF.Syntax.RhoCartesianModelLexPresheafExtension

/-!
# The relative finite-limit universal property for authored rho contexts

The general theorem is instantiated on the actual two-sorted rho context
category. In particular, maps between left-exact rho interpretations are
uniquely determined by, and exist for, maps between their authored
cartesian-context interpretations.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.RhoCartesianModelLexTargetEquivalence

open CategoryTheory CategoryTheory.Limits
open Mettapedia.OSLF.CartesianContextModels
open Mettapedia.OSLF.Binding.RhoCartesianContextModels
open Mettapedia.OSLF.Binding.RhoCartesianModelLexTarget
open Mettapedia.OSLF.Binding.RhoCartesianModelLexPresheafExtension

private instance : HasFiniteProducts Contexts :=
  hasFiniteProducts_of_has_binary_and_terminal

variable (D : Type) [SmallCategory D] [HasFiniteLimits D]

/-- Every small finitely complete target interprets the actual authored
rho context category through the relative finite-limit classifier. -/
noncomputable def rhoTargetLexEquivalence :
    LeftExactTargetInterpretations Contexts D ≌
      CartesianTargetInterpretations Contexts D :=
  cartesianTargetLexEquivalence Contexts D

/-- The explicit extension of the actual rho context Yoneda model agrees
with the functorial inverse supplied by the presheaf-target equivalence. -/
noncomputable def rhoContextYonedaRecoveredIso :
    rhoContextYonedaExtension ≅
      (cartesianPresheafLexEquivalence Contexts Contexts).inverse.obj
        rhoContextYonedaModel := by
  let E := cartesianPresheafLexEquivalence Contexts Contexts
  exact (E.unitIso.app rhoContextYonedaExtension) ≪≫
    E.inverse.mapIso
      ((CartesianTargetInterpretation Contexts (Contextsᵒᵖ ⥤ Type)).isoMk
        rhoContextYonedaRestrictionIso)

/-- The hom-set form of the universal property for actual rho contexts:
each map on authored contexts extends to exactly one map on finite
presentations. -/
theorem rho_map_extension_unique
    (T U : LeftExactTargetInterpretations Contexts D)
    (f : (restrictLeftExactTarget Contexts D).obj T ⟶
      (restrictLeftExactTarget Contexts D).obj U) :
    ∃! g : T ⟶ U, (restrictLeftExactTarget Contexts D).map g = f := by
  let R := restrictLeftExactTarget Contexts D
  obtain ⟨g, hg⟩ := R.map_surjective f
  refine ⟨g, hg, ?_⟩
  intro h hh
  exact R.map_injective (hh.trans hg.symm)

end Mettapedia.OSLF.Binding.RhoCartesianModelLexTargetEquivalence
