import Mettapedia.OSLF.Syntax.CartesianModelLexTargetFullness

/-!
# Relative finite-limit classification in small finitely complete targets

The relative finite-presentation category is generated under finite limits
by the authored cartesian contexts. Restriction is faithful by internal
generation, full by pointwise Set-valued lifting and Yoneda descent, and
essentially surjective by representability of the pointwise extension.
Together these give the universal property on objects and interpretation
maps, with inverse, unit, counit, and triangle coherence supplied by the
resulting categorical equivalence.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.CartesianContextModels

open CategoryTheory CategoryTheory.Limits

variable (C : Type) [SmallCategory C] [HasFiniteProducts C]
variable (D : Type) [SmallCategory D] [HasFiniteLimits D]

/-- Restriction is an equivalence for every small finitely complete target.
The three fields have independent proofs: finite-limit generation,
Yoneda-mediated map lifting, and representable target descent. -/
instance restrictLeftExactTarget_isEquivalence :
    (restrictLeftExactTarget C D).IsEquivalence :=
  ⟨restrictLeftExactTarget_faithful C D,
   restrictLeftExactTarget_full C D,
   restrictLeftExactTarget_essSurj C D⟩

/-- The relative finite-limit universal property, including interpretation
morphisms and all equivalence coherence. -/
noncomputable def cartesianTargetLexEquivalence :
    LeftExactTargetInterpretations C D ≌
      CartesianTargetInterpretations C D :=
  (restrictLeftExactTarget C D).asEquivalence

/-- The explicit Yoneda-descended extension is isomorphic to the inverse
selected by the equivalence. This compares the constructive object-level
extension with the functorial inverse rather than silently replacing it. -/
noncomputable def explicitTargetExtensionIsoInverse
    (F : CartesianTargetInterpretations C D) :
    extendCartesianTargetModel C D F ≅
      (cartesianTargetLexEquivalence C D).inverse.obj F := by
  let E := cartesianTargetLexEquivalence C D
  let explicitRestriction : E.functor.obj (extendCartesianTargetModel C D F) ≅ F :=
    (CartesianTargetInterpretation C D).isoMk
      (extendCartesianTargetModelRestrictionIso C D F)
  exact E.functor.preimageIso
    (explicitRestriction ≪≫ (E.counitIso.app F).symm)

end Mettapedia.OSLF.CartesianContextModels
