import Mettapedia.TypeTheory.MaterialSets.Hypersets.BareContextualGeneration
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualMaterialTypeFormerEquivalence
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualMaterialSiteEquivalence
import Mettapedia.GSLT.Logic.ObservedGeneratedModelControls

/-!
# Bare contextual family controls and parameter-size obstruction

The uniform bare-member construction interprets an infinite observed
contextual family with a cyclic alternative. Its dependent body varies
with the actual argument. Every present result fibre is inhabited while
the full future product is empty. Actual generated Pi, Sigma and W values
fit their common raised enclosure.

At an inhabited small context the entire parameter space of bare families
cannot be small at the original bound, even though each material member
type has the proved local smallness property. The obstruction does not
claim that an original-bound uniform graph selector is refuted.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.BareContextualFamiliesControls

open _root_.CategoryTheory ContextualGeneratedUniverse BareContextualFamilies ContextualMaterialEquivalence
open Mettapedia.TypeTheory
open Mettapedia.GSLT.ObservedGeneratedModel
open Mettapedia.GSLT.ObservedGeneratedModelControls.Paths
open Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent (compose)

universe u

def constantFamily {C : Type u} [Category.{u} C] (context : LabelledContext C) (X : HSet.{u}) :
    Family.{u, u} context where
  carrier _ := X
  restrict _ := id
  restrict_id _ _ := rfl
  restrict_comp _ _ _ := rfl

theorem bare_family_parameters_not_small {C : Type u} [Category.{u} C]
    (context : LabelledContext C) (point : context.base.Elements) : ¬ Small.{u} (Family.{u, u} context) := by
  intro small
  obtain ⟨Carrier, ⟨equivalence⟩⟩ := small.equiv_small
  let value (index : Carrier) : HSet.{u} := (equivalence.symm index).carrier point
  let edge (first second : Carrier) : Prop := value second ∈ value first
  have lawful : HSet.IsDecoration edge value := by
    intro index member
    constructor
    · intro belongs
      let target := equivalence (constantFamily context member)
      have represented : value target = member := congrArg (fun family : Family.{u, u} context => family.carrier point)
        (equivalence.symm_apply_apply (constantFamily context member))
      refine ⟨target, ?_, represented⟩
      change value target ∈ value index
      rw [represented]
      exact belongs
    · rintro ⟨target, belongs, rfl⟩
      exact belongs
  let whole : HSet.{u} := HSet.range (fun index : Carrier => AccessiblePointedGraph.generated edge index)
  apply HSet.not_exists_universal
  refine ⟨whole, fun member => ?_⟩
  apply HSet.mem_range.mpr
  refine ⟨equivalence (constantFamily context member), ?_⟩
  change HSet.decorate edge (equivalence (constantFamily context member)) = member
  rw [← lawful.eq_decorate]
  exact congrArg (fun family : Family.{u, u} context => family.carrier point)
    (equivalence.symm_apply_apply (constantFamily context member))

theorem local_members_small_parameters_large {C : Type u} [Category.{u} C]
    (context : LabelledContext C) (point : context.base.Elements) :
    (∀ (family : Family.{u, u} context) (location : context.base.Elements),
      Small.{u} (BareContextualFamilies.Members (family.carrier location))) ∧ ¬ Small.{u} (Family.{u, u} context) :=
  ⟨fun family location => (small_congr (Equiv.psigmaEquivSubtype
      (fun value : HSet.{u} => value ∈ family.carrier location))).mp
      (HSet.small_el_constructive (family.carrier location)),
    bare_family_parameters_not_small context point⟩

abbrev sourceContext := context model worldCoding

def bareInput : Family.{0, 0} sourceContext := ofMaterial observedInput

def raisedContext := ContextualSiteLiftMaterial.context sourceContext

def raisedPoint (point : sourceContext.base.Elements) : raisedContext.base.Elements :=
  (PresheafSiteLift.elementsUp sourceContext.base).obj point

def positiveMembers : bareInput.source.sections :=
  ⟨fun point => (observedInput.model point).decode.symm (positiveSection.val point), by
    intro point next step
    exact (observedInput.memberRestriction_encode step (positiveSection.val point)).trans
      (congrArg (observedInput.model next).decode.symm (positiveSection.property step))⟩

def raisedPositive : bareInput.material.family.sections := bareInput.sectionComparison positiveMembers

theorem bare_positive_old_value :
    (bareInput.material.model (raisedPoint (observedPoint model worldCoding oldRaw))).value
      (raisedPositive.val (raisedPoint (observedPoint model worldCoding oldRaw))) = ∅ :=
  (bareInput.section_value positiveMembers _).trans ((congrArg HSet.lift old_section_value).trans HSet.lift_empty)

theorem bare_positive_cyclic_value :
    (bareInput.material.model (raisedPoint (observedPoint model worldCoding newRaw))).value
      (raisedPositive.val (raisedPoint (observedPoint model worldCoding newRaw))) = HSet.quineAtom :=
  (bareInput.section_value positiveMembers _).trans ((congrArg HSet.lift new_section_value).trans HSet.lift_quineAtom)

theorem bare_family_is_nonconstant :
    (bareInput.material.model (raisedPoint (observedPoint model worldCoding oldRaw))).value
      (raisedPositive.val (raisedPoint (observedPoint model worldCoding oldRaw))) ≠
    (bareInput.material.model (raisedPoint (observedPoint model worldCoding newRaw))).value
      (raisedPositive.val (raisedPoint (observedPoint model worldCoding newRaw))) := by
  rw [bare_positive_old_value, bare_positive_cyclic_value]
  exact HSet.empty_ne_quineAtom

def domainComparison : Equivalence bareInput.material (ContextualSiteLiftMaterial.family observedInput) :=
  ofMaterialComparison observedInput

def bodyChange : NatTrans bareInput.material.extension.base
    (ContextualSiteLiftMaterial.context observedInput.extension).base :=
  compose domainComparison.comprehension (PresheafSiteLift.comprehensionFrom sourceContext.base observedInput.family)

def bareBody : Family.{0, 1} bareInput.material.extension :=
  (ofMaterial argumentBody).raised.atRaised_reindex (other := bareInput.material.extension) bodyChange

def bodyComparison : Equivalence bareBody.atRaised
    ((ContextualSiteLiftMaterial.body observedInput argumentBody).reindex
      (other := bareInput.material.extension) domainComparison.comprehension) :=
  (ofEquality ((ofMaterial argumentBody).raised.atRaised_reindex_material (other := bareInput.material.extension) bodyChange)).trans
    (((ofEquality (ofMaterial argumentBody).raised_material).reindex (other := bareInput.material.extension) bodyChange).trans
      (((ofMaterialComparison argumentBody).reindex (other := bareInput.material.extension) bodyChange).trans
        (ofEquality (ContextualUniverseCodes.MaterialFamily.reindex_comp (ContextualSiteLiftMaterial.family argumentBody)
          domainComparison.comprehension (PresheafSiteLift.comprehensionFrom sourceContext.base observedInput.family)).symm)))

def arrows := ContextualSiteLiftMaterial.arrows arrowCoding

def actualPi := bareInput.material.pi bareBody.atRaised arrows

def piComparison : Equivalence actualPi (ContextualSiteLiftMaterial.family (observedInput.pi argumentBody arrowCoding)) :=
  (ContextualMaterialTypeFormerEquivalence.pi domainComparison bodyComparison arrows).trans
    (ContextualMaterialSiteEquivalence.pi observedInput argumentBody arrowCoding)

theorem bare_present_results_inhabited
    (argument : bareInput.material.family.obj (raisedPoint (observedPoint model worldCoding oldRaw))) :
    Nonempty (bareBody.atRaised.family.obj
      ⟨(raisedPoint (observedPoint model worldCoding oldRaw)).1,
        ⟨(raisedPoint (observedPoint model worldCoding oldRaw)).2, argument⟩⟩) := by
  let point := raisedPoint (observedPoint model worldCoding oldRaw)
  let decoded := (domainComparison.fibre point argument).down
  obtain ⟨witness⟩ := initial_results_inhabited decoded
  exact ⟨(bodyComparison.fibre ⟨point.1, ⟨point.2, argument⟩⟩).symm (ULift.up witness)⟩

theorem bare_full_future_product_empty :
    (actualPi.model (raisedPoint (observedPoint model worldCoding oldRaw))).carrier = ∅ :=
  (piComparison.carrier _).trans ((ContextualSiteLiftMaterial.carrier _ _).trans
    ((congrArg HSet.lift dependent_pi_empty_initial).trans HSet.lift_empty))

theorem bare_full_future_product_uninhabited :
    ¬ Nonempty (actualPi.family.obj (raisedPoint (observedPoint model worldCoding oldRaw))) := by
  rintro ⟨function⟩
  have belongs := (actualPi.model _).value_mem function
  rw [bare_full_future_product_empty] at belongs
  exact HSet.notMem_empty _ belongs

def bareInputGenerated : Generation BareContextualGeneration.Seeds BareContextualGeneration.seedModel arrows bareInput.material :=
  (bareInput.raised_material : bareInput.raised.atRaised = bareInput.material) ▸
    BareContextualGeneration.generated arrows bareInput.raised

def bareBodyGenerated : Generation BareContextualGeneration.Seeds BareContextualGeneration.seedModel arrows bareBody.atRaised :=
  BareContextualGeneration.generated arrows bareBody

theorem bare_dependent_types_enclosed (point : raisedContext.base.Elements) :
    HSet.lift (actualPi.model point).carrier ∈
        enclosure BareContextualGeneration.Seeds BareContextualGeneration.seedModel arrows raisedContext point ∧
    HSet.lift ((bareInput.material.sigma bareBody.atRaised).model point).carrier ∈
        enclosure BareContextualGeneration.Seeds BareContextualGeneration.seedModel arrows raisedContext point ∧
    HSet.lift ((bareInput.material.w bareBody.atRaised arrows).model point).carrier ∈
        enclosure BareContextualGeneration.Seeds BareContextualGeneration.seedModel arrows raisedContext point :=
  ⟨generated_mem_enclosure _ _ _ (.pi bareInputGenerated bareBodyGenerated) point,
    generated_mem_enclosure _ _ _ (.sigma bareInputGenerated bareBodyGenerated) point,
    generated_mem_enclosure _ _ _ (.w bareInputGenerated bareBodyGenerated) point⟩

theorem actual_bare_parameter_space_large : ¬ Small.{0} (Family.{0, 0} sourceContext) :=
  bare_family_parameters_not_small sourceContext (observedPoint model worldCoding oldRaw)

end Mettapedia.TypeTheory.MaterialSets.Hypersets.BareContextualFamiliesControls
