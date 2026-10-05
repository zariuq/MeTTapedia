import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualUniverseCodes

/-!
# Carrier-only observations do not transport generated type codes

The actual growing family and the generated unit have equal present carrier
sets. At the target of the real context arrow, only the growing family admits
the cyclic material alternative. The lifted external enclosure therefore
cannot be used as a universe code presheaf merely by forgetting the family.

The positive code action instead uses the actual comprehension projection,
whose fibres contain two distinct material arguments in the enlarged world.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualUniverseCodeControls

open CategoryTheory
open ContextualGeneratedUniverse
open ContextualGeneratedUniverse.Growing
open Mettapedia.TypeTheory.DisplayedPresheafComprehension

theorem unit_carrier (point : context.base.Elements) :
    ((MaterialFamily.unit context).model point).carrier = {∅} := by
  change HSet.mk (AccessiblePointedGraph.singletonGraph AccessiblePointedGraph.empty) = {∅}
  rw [AccessiblePointedGraph.mk_singletonGraph, HSet.mk_empty]

theorem input_old_carrier : (input.model old).carrier = {∅} := by
  apply HSet.ext
  intro value
  constructor
  · intro member
    let term := (input.model old).decode ⟨value, member⟩
    have actual := (input.model old).value_decode ⟨value, member⟩
    have empty : (input.model old).value term = ∅ :=
      (input_value old term).trans
        (Mettapedia.GSLT.ContextualObservedFamilyEnclosure.GrowthControls.FutureArguments.currentArgument_value term)
    exact HSet.mem_singleton.mpr (actual.symm.trans empty)
  · intro member
    have same := HSet.mem_singleton.mp member
    have empty : (input.model old).value (emptySection.val old) = ∅ :=
      emptySection_value Mettapedia.GSLT.ContextualObservedFamilyEnclosure.GrowthControls.FutureArguments.oldRaw
    exact same ▸ empty ▸ (input.model old).value_mem (emptySection.val old)

theorem input_later_ne_unit :
    (input.model later).carrier ≠ ((MaterialFamily.unit context).model later).carrier := by
  intro same
  have member : HSet.quineAtom ∈ (input.model later).carrier :=
    cyclic_leaf_shape ▸ (input.model later).value_mem PowerClassContextualMaterialization.Growing.futureArgument
  have singletonMember : HSet.quineAtom ∈ ({∅} : HSet) :=
    (same.trans (unit_carrier later)) ▸ member
  exact HSet.empty_ne_quineAtom (HSet.mem_singleton.mp singletonMember).symm

/-- This implication is a general commuting-square obstruction; the later
controls instantiate it with constructed generated families. -/
theorem incompatible_square {Source Present Future : Type*}
    (present : Source → Present) (future : Source → Future)
    (left right : Source) (same : present left = present right) (different : future left ≠ future right) :
    ¬ ∃ transport : Present → Future, ∀ source, transport (present source) = future source := by
  rintro ⟨transport, commutes⟩
  exact different ((commutes left).symm.trans ((congrArg transport same).trans (commutes right)))

def inputCode : ContextualUniverseCodes.Code Seeds observedSeedModel arrowCoding context :=
  ContextualUniverseCodes.ofRaw Seeds observedSeedModel arrowCoding ⟨input, inputGenerated⟩

def unitCode : ContextualUniverseCodes.Code Seeds observedSeedModel arrowCoding context :=
  ContextualUniverseCodes.ofRaw Seeds observedSeedModel arrowCoding ⟨MaterialFamily.unit context, Generation.unit context⟩

def carrier (point : context.base.Elements) (code : ContextualUniverseCodes.Code Seeds observedSeedModel arrowCoding context) : HSet :=
  ((ContextualUniverseCodes.decodeFamily Seeds observedSeedModel arrowCoding code).model point).carrier

theorem present_code_carriers_eq : carrier old inputCode = carrier old unitCode :=
  input_old_carrier.trans (unit_carrier old).symm

theorem future_code_carriers_ne : carrier later inputCode ≠ carrier later unitCode :=
  input_later_ne_unit

theorem formed_codes_distinct : inputCode ≠ unitCode := by
  intro same
  exact future_code_carriers_ne (congrArg (carrier later) same)

/-- The two points are joined by the authored growing context arrow. -/
theorem actual_future_arrow : Nonempty (old ⟶ later) :=
  ⟨PowerClassContextualMaterialization.Growing.futureArrow⟩

theorem present_carrier_readout_cannot_transport_future :
    ¬ ∃ transport : HSet → HSet,
      ∀ code : ContextualUniverseCodes.Code Seeds observedSeedModel arrowCoding context,
        transport (carrier old code) = carrier later code :=
  incompatible_square (carrier old) (carrier later) inputCode unitCode
    present_code_carriers_eq future_code_carriers_ne

/-- The universe shift used by the external image enclosure preserves this
obstruction: lifting values does not restore the forgotten code. -/
theorem lifted_present_carrier_readout_cannot_transport_future :
    ¬ ∃ transport : HSet.{1} → HSet.{1},
      ∀ code : ContextualUniverseCodes.Code Seeds observedSeedModel arrowCoding context,
        transport (HSet.lift (carrier old code)) = HSet.lift (carrier later code) := by
  apply incompatible_square (fun code => HSet.lift (carrier old code))
    (fun code => HSet.lift (carrier later code)) inputCode unitCode
    (congrArg HSet.lift present_code_carriers_eq)
  intro same
  exact future_code_carriers_ne (HSet.lift_injective same)

def substitutedInput : ContextualUniverseCodes.Code Seeds observedSeedModel arrowCoding input.extension :=
  ContextualUniverseCodes.reindex Seeds observedSeedModel arrowCoding (PowerClassPresheafProducts.projection input.family) inputCode

def laterComprehension : input.extension.base.Elements :=
  ⟨later.1, ⟨later.2, PowerClassContextualMaterialization.Growing.futureArgument⟩⟩

theorem substituted_input_retains_cyclic_member :
    (((ContextualUniverseCodes.decodeFamily Seeds observedSeedModel arrowCoding substitutedInput).model laterComprehension).value
      PowerClassContextualMaterialization.Growing.futureArgument) = HSet.quineAtom :=
  cyclic_leaf_shape

/-- The code substitution used above is not an identity or an isomorphism
disguised as context extension: its actual projection loses the argument. -/
theorem comprehension_projection_not_injective :
    ¬ Function.Injective ((PowerClassPresheafProducts.projection input.family).app later.1) := by
  intro injective
  let first : TotalAt input.family later.1 := ⟨later.2, PowerClassContextualMaterialization.Growing.futureArgument⟩
  let second : TotalAt input.family later.1 := ⟨later.2, emptySection.val later⟩
  have same := injective (a₁ := first) (a₂ := second) rfl
  have members : PowerClassContextualMaterialization.Growing.futureArgument = emptySection.val later :=
    eq_of_heq ((Sigma.mk.inj_iff.mp same).2)
  have values := congrArg (input.model later).value members
  have empty : (input.model later).value (emptySection.val later) = ∅ :=
    emptySection_value Mettapedia.GSLT.ContextualObservedFamilyEnclosure.GrowthControls.FutureArguments.laterRaw
  exact HSet.empty_ne_quineAtom (empty.symm.trans (values.symm.trans cyclic_leaf_shape))

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualUniverseCodeControls
