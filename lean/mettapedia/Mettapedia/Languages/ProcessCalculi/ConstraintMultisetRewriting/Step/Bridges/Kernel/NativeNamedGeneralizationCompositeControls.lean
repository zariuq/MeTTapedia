import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Kernel.NativeProductClosureControls

/-! The checked conversion from the admitted Boolean definitions is the exact
external premise consumed by the compact named-GEN block. -/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.NativeNamedGeneralizationCompositeControls

open Mettapedia.Languages.OpenTheory Mettapedia.Languages.HOLLight
open NativeNamedGeneralization NativeProductClosureControls

local instance : DecidablePred SourceProfileModels.policy := inferInstance
local instance : DecidablePred emptyAxiomPolicy := fun _ => isFalse id

theorem dependencies_empty (facts : List Theorem)
    (empty : ∀ fact ∈ facts, fact.axioms = ∅) :
    CachedHypothesisList.dependencies facts = ∅ := by
  induction facts with
  | nil => rfl
  | cons fact rest ih =>
      rw [CachedHypothesisList.dependencies, empty fact List.mem_cons_self,
        ih (fun item member => empty item (List.mem_cons_of_mem _ member))]
      exact Finset.empty_union ∅

theorem actual_definition_axioms_empty (index : Nat) (fact : Theorem)
    (found : actualDefinitions.cache[index]? = some fact) : fact.axioms = ∅ := by
  have universalEmpty : universalObject.definitionTheorem.axioms = ∅ :=
    checkConstantDefinition_axioms_empty (Option.some_get _).symm
  have truthEmpty : actualTruth.axioms = ∅ :=
    checkConstantDefinition_axioms_empty (Option.some_get _).symm
  have member : fact = actualUniversalBool ∨ fact = actualTruth := by
    simpa [actualDefinitions, GraphExpansion.start] using Array.mem_of_getElem? found
  rcases member with rfl | rfl
  · exact universalEmpty
  · exact truthEmpty

/-- The actual compiler result, including its axiom provenance, is identified
without evaluating the conversion compiler. -/
theorem actual_conversion_eq_claim : conversion = some conversionClaim := by
  obtain ⟨sources, read⟩ := Option.isSome_iff_exists.mp actual_definition_reads
  obtain ⟨after, root, fact, computed, _, found, closed, conclusion, axioms, _⟩ :=
    functionConversion_checked .prop 0 1 sources read
      (GraphExpansion.start_checked emptyAxiomPolicy [actualUniversalBool, actualTruth])
      ("actual-named-universal", 0)
  have dependencies : CachedHypothesisList.dependencies (sources.entries.map Prod.snd) = ∅ := by
    apply dependencies_empty
    intro item member
    obtain ⟨entry, entryMember, rfl⟩ := List.mem_map.mp member
    exact actual_definition_axioms_empty entry.1 entry.2 (sources.found entry entryMember)
  have identified : fact = conversionClaim := by
    apply Theorem.ext
    · exact axioms.trans dependencies
    · exact Sequent.ext closed conclusion
  simp only [conversion, computed, bind, Option.bind_some, found, identified]

/-- The actual and compact provenance labels both pass the bounded checked
GEN block. The conversion compiler is missing from this comparison. -/
theorem compact_named_gen_actual_origin :
    (namedGenBlock? SourceProfileModels.policy input conversionClaim binder
      ("actual-named-GEN", 1)).isSome =
      compactNamedGen.isSome := by
  decide +kernel

theorem actual_named_gen_checked :
    (namedGenBlock? SourceProfileModels.policy input conversionClaim binder
      ("actual-named-GEN", 1)).isSome = true :=
  compact_named_gen_actual_origin.trans compact_named_gen_checked

/-- This is the complete positive join through the actual definition-derived
conversion and the checked named-GEN block. -/
theorem named_reflexivity_checked : namedReflexivity.isSome = true := by
  obtain ⟨checked, computed⟩ := Option.isSome_iff_exists.mp actual_named_gen_checked
  exact Option.isSome_iff_exists.mpr ⟨⟨conversionClaim, checked⟩, by
    simp only [namedReflexivity, actual_conversion_eq_claim, bind, Option.bind_some, computed,
      pure]⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.NativeNamedGeneralizationCompositeControls
