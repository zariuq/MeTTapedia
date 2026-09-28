import Mettapedia.OSLF.Syntax.CartesianModelLexTargetEquivalence
import Mettapedia.OSLF.Syntax.CartesianModelLexPresheafFullness
import Mettapedia.OSLF.Syntax.IndexedOperationalModelReindex

/-!
# Relative finite-limit interpretation with conditional-rule algebras

The relative finite-limit equivalence for authored context models lifts
through any functorial presentation of indexed conditional rules. Its maps
preserve the actual algebra actions on individual firing evidence and every
recursive premise input. This states a compatibility law between the
finite-limit and operational layers; it does not yet construct the chosen
function objects or the contextual substitution action required by the
complete Chapter 7 classifier.
-/

set_option autoImplicit false
set_option linter.checkUnivs false

namespace Mettapedia.OSLF.CartesianContextModels

open CategoryTheory CategoryTheory.Limits
open Mettapedia.OSLF.Binding.IndexedRulePresentationCategory
open Mettapedia.OSLF.Binding.IndexedOperationalModelsOver

universe uBase uIndex uShape uPosition

/-- Relative finite-limit extension remains universal after adjoining a
functorially varying proof-relevant algebra of ordered rule constructors.
The inverse uses presentation-isomorphism transport rather than erasing
or quotienting individual firing witnesses. -/
noncomputable def operationalTargetLexEquivalence
    (C : Type) [SmallCategory C] [HasFiniteProducts C]
    (D : Type) [SmallCategory D] [HasFiniteLimits D]
    {Base : Type uBase}
    (P : CartesianTargetInterpretations C D ⥤
      Presentation.{uBase, uIndex, uShape, uPosition} Base) :
    Model (restrictLeftExactTarget C D ⋙ P) ≌ Model P := by
  letI : (restrictLeftExactTarget C D).IsEquivalence :=
    restrictLeftExactTarget_isEquivalence C D
  exact reindexEquivalence P (restrictLeftExactTarget C D)

/-- The classifier comparison leaves the authored base interpretation
unchanged after forgetting the operational rule algebra. -/
theorem operationalTargetLex_forget
    (C : Type) [SmallCategory C] [HasFiniteProducts C]
    (D : Type) [SmallCategory D] [HasFiniteLimits D]
    {Base : Type uBase}
    (P : CartesianTargetInterpretations C D ⥤
      Presentation.{uBase, uIndex, uShape, uPosition} Base) :
    (operationalTargetLexEquivalence C D P).functor ⋙ forget P =
      forget (restrictLeftExactTarget C D ⋙ P) ⋙
        restrictLeftExactTarget C D := by
  rfl

/-- Free rule-tree generation commutes with the same relative finite-limit
comparison, including the action on authored interpretation maps. -/
theorem operationalTargetLex_free
    (C : Type) [SmallCategory C] [HasFiniteProducts C]
    (D : Type) [SmallCategory D] [HasFiniteLimits D]
    {Base : Type uBase}
    (P : CartesianTargetInterpretations C D ⥤
      Presentation.{uBase, uIndex, uShape, uPosition} Base) :
    restrictLeftExactTarget C D ⋙ freeFunctor P =
      freeFunctor (restrictLeftExactTarget C D ⋙ P) ⋙
        (operationalTargetLexEquivalence C D P).functor := by
  rfl

/-- The canonical presheaf target is covered without requiring that the
presheaf category itself be small. -/
noncomputable def operationalPresheafLexEquivalence
    (C : Type) [SmallCategory C] [HasFiniteProducts C]
    (B : Type) [SmallCategory B]
    {Base : Type uBase}
    (P : CartesianTargetInterpretations C (Bᵒᵖ ⥤ Type) ⥤
      Presentation.{uBase, uIndex, uShape, uPosition} Base) :
    Model ((cartesianPresheafLexEquivalence C B).functor ⋙ P) ≌
      Model P := by
  letI : (cartesianPresheafLexEquivalence C B).functor.IsEquivalence :=
    (cartesianPresheafLexEquivalence C B).isEquivalence_functor
  exact reindexEquivalence P
    (cartesianPresheafLexEquivalence C B).functor

end Mettapedia.OSLF.CartesianContextModels
