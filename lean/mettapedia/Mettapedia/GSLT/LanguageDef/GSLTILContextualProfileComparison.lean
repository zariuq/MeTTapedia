import Mettapedia.GSLT.Core.ContextualProfileInclusions
import Mettapedia.GSLT.Core.LooseRelationPredicateTransformers
import Mettapedia.GSLT.LanguageDef.DialectGluingMorphisms

/-!
# Contextual profiles over the operational equipment

The unityped, simply typed, and dependent families profiles share contexts
and substitutions, but have progressively richer type fibres.  This module
places that shared contextual base in the previously selected GSLT-IL
operational equipment.

A substitution is sent to its proof-relevant graph, hence to a represented
loose route.  Existential and universal predicate transport along any
represented route both reduce to ordinary inverse image along its selected
map.  This is exactly the transport used by the semantic predicate
institution.  A genuinely branching loose route separates the two
transports and therefore cannot be replaced by a contextual substitution.

The result identifies a precise role for a unityped profile: it is a common
operational substitution floor and a possible erasure target.  It is not a
claim that richer simple or dependent type fibres, proof occurrences, or
dialect-gluing data can be reconstructed from that floor.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.GSLTIL.ContextualProfileComparison

open CategoryTheory
open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.GSLT.LooseRelationEquipment
open Mettapedia.GSLT.LooseRelationPredicateTransformers

universe u

/-! ## Context substitutions are represented routes -/

/-- The operational route corresponding to a context substitution. -/
def substitutionRoute {Source Target : Type u}
    (substitution : Source → Target) : Loose Source Target :=
  companion substitution

/-- Every context substitution carries the canonical exact representation
of its graph. -/
def substitutionRouteRepresentation {Source Target : Type u}
    (substitution : Source → Target) :
    Representation (substitutionRoute substitution) :=
  Representation.companionSelf substitution

/-- Horizontal composition of substitution graphs is represented by
ordinary substitution composition.  The loose composite still retains its
intermediate context value as evidence. -/
def substitutionRouteCompositionEquiv
    {First Middle Last : Type u}
    (earlier : First → Middle) (later : Middle → Last)
    (source : First) (target : Last) :
    LooseRelationEquipment.comp
        (substitutionRoute earlier) (substitutionRoute later) source target ≃
      substitutionRoute (later ∘ earlier) source target :=
  (Representation.horizontalComp
    (substitutionRouteRepresentation earlier)
    (substitutionRouteRepresentation later)).exact source target

/-- The selected map of a composite substitution route is function
composition, so executing the represented route performs no relational
search. -/
@[simp]
theorem substitutionRouteComposition_map
    {First Middle Last : Type u}
    (earlier : First → Middle) (later : Middle → Last) :
    (Representation.horizontalComp
      (substitutionRouteRepresentation earlier)
      (substitutionRouteRepresentation later)).map =
        later ∘ earlier :=
  rfl

/-- Reindexing a unityped term is pullback of a value-valued observation
along the map selected by the substitution route. -/
theorem unityped_tmSub_eq_represented_pullback
    (Value : Type u) {Source Target : Type u}
    (term : Target → Value) (substitution : Source → Target) :
    (unitypedFamilies Value).tmSub term substitution =
      term ∘ (substitutionRouteRepresentation substitution).map :=
  rfl

/-- Unityped, simply typed, and dependent constant-family terms all perform
the same reindexing on their shared contextual base. -/
theorem profile_reindexing_agrees
    (Value : Type u) {Source Target : Type u}
    (term : Target → Value) (substitution : Source → Target) :
    (unitypedFamilies Value).tmSub term substitution =
        simpleFamilies.tmSub (A := Value) term substitution ∧
      simpleFamilies.tmSub (A := Value) term substitution =
        familiesCwf.tmSub (A := constantFamily Value) term substitution :=
  ⟨rfl, rfl⟩

/-- For a contextual substitution, both loose-route transports agree with
ordinary inverse image. -/
theorem substitution_predicate_transport
    {Source Target : Type u} (substitution : Source → Target)
    (predicate : Set Target) :
    mayPullback (substitutionRoute substitution) predicate =
        Set.preimage substitution predicate ∧
      mustPullback (substitutionRoute substitution) predicate =
        Set.preimage substitution predicate := by
  exact ⟨mayPullback_eq_preimage
      (substitutionRouteRepresentation substitution) predicate,
    mustPullback_eq_preimage
      (substitutionRouteRepresentation substitution) predicate⟩

/-! ## Strict boundaries -/

/-- The shared unityped base does not determine either richer type fibre:
the simple profile already has a type outside the unityped image, and the
dependent profile has a varying family outside the simple image. -/
theorem contextual_type_fibres_are_strict :
    (¬ ∃ A : TypeOver
          (UnitypedFamiliesCwfWithTerminal Bool).toCwf PUnit,
        (unitypedToSimplePseudoMorphism Bool).mapTypeObject A =
          (⟨PEmpty⟩ : TypeOver SimpleFamiliesCwf PUnit)) ∧
      (¬ ∃ A : TypeOver (SimpleFamiliesCwf.{0}) Bool,
        simpleToDependentPseudoMorphism.mapTypeObject A =
          (⟨varyingBoolFamily⟩ : TypeOver (familiesCwf.{0}) Bool)) :=
  ⟨pempty_not_in_unitypedBool_type_image,
    varyingBoolFamily_not_in_pseudoMorphism_image⟩

/-- Sharing a base also does not collapse dialect gluing to one global
symbol action: a compatible cocone may require a piecewise mediator. -/
theorem contextual_base_does_not_discharge_dialect_gluing :
    ∃ (base left right glued target : ValidatedLanguageDef)
      (baseIntoLeft : StructuralMorphism base left)
      (baseIntoRight : StructuralMorphism base right)
      (leftInclusion : StructuralMorphism left glued)
      (rightInclusion : StructuralMorphism right glued)
      (leftMap : StructuralMorphism left target)
      (rightMap : StructuralMorphism right target)
      (mediator : StructuralMorphism glued target),
      glued.language =
          DialectGluing.glue "gluing-base-agreement" base.language
            left.language right.language ∧
        StructuralLanguageDefCategory.Equivalent
            (StructuralMorphism.comp baseIntoLeft leftMap)
            (StructuralMorphism.comp baseIntoRight rightMap) ∧
        leftMap.symbols ≠ rightMap.symbols ∧
        StructuralLanguageDefCategory.Equivalent
            (StructuralMorphism.comp leftInclusion mediator) leftMap ∧
        StructuralLanguageDefCategory.Equivalent
            (StructuralMorphism.comp rightInclusion mediator) rightMap :=
  DialectGluingMorphisms.exists_base_agreeing_cocone_with_piecewise_mediator

#print axioms substitutionRouteCompositionEquiv
#print axioms unityped_tmSub_eq_represented_pullback
#print axioms profile_reindexing_agrees
#print axioms contextual_type_fibres_are_strict
#print axioms contextual_base_does_not_discharge_dialect_gluing

end Mettapedia.GSLT.LanguageDef.GSLTIL.ContextualProfileComparison
