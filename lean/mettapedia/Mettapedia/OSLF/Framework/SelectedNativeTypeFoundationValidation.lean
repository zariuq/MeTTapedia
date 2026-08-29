import Mettapedia.OSLF.Framework.SelectedNativeTypeFoundation

/-!
# Admission of the selected carrier foundation

The selected foundation is a specialization of the generic sparse
carrier-object calculus. Its validity therefore follows from that generic
construction rather than a duplicate row-by-row validator proof.
-/

namespace Mettapedia.OSLF.Framework

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef

namespace SelectedNativeTypeFoundation

/-- The ordinary language coordinate of the carrier foundation passes the
structural `LanguageDef` validator independently of its inference rules. -/
theorem definition_language_validate {source : ValidatedLanguageDef}
    (demand : Demand source) :
    (definition demand).toLanguageDef.validate = [] := by
  exact CarrierUniverseSignature.language_validate
    (CarrierObjectLanguageDef.validatedCarrierSignature
      (CarrierObjectLanguageDef.Naming.indexed demand.carrierObjects))

/-- Every grounded carrier demand yields one flat calculus accepted by the
ordinary calculus validator. -/
theorem definition_valid {source : ValidatedLanguageDef}
    (demand : Demand source) : (definition demand).isValid = true :=
  CarrierObjectLanguageDef.definition_valid
    (CarrierObjectLanguageDef.Naming.indexed demand.carrierObjects)

/-- Checked carrier foundation with no secondary representation. -/
def validated {source : ValidatedLanguageDef}
    (demand : Demand source) : ValidatedCalculusLanguageDef :=
  ⟨definition demand, definition_valid demand⟩

@[simp]
theorem validate?_eq_some {source : ValidatedLanguageDef}
    (demand : Demand source) : validate? demand = some (validated demand) := by
  simp [validate?, CalculusLanguageDef.validate?, definition_valid, validated]

/-! ## Negative admission control -/

/-- Malformed variant that keeps all generated constructors and inference
rules while deleting every generated carrier declaration. -/
def withoutCarrierTypes {source : ValidatedLanguageDef}
    (demand : Demand source) : CalculusLanguageDef :=
  { definition demand with types := [] }

@[simp]
theorem withoutCarrierTypes_typeNames {source : ValidatedLanguageDef}
    (demand : Demand source) :
    (withoutCarrierTypes demand).toLanguageDef.typeNames = [] := by
  rfl

private theorem universeRule_mem {source : ValidatedLanguageDef}
    (demand : Demand source) {carrier : String}
    (membership : carrier ∈ stableCarrierNames demand) :
    CarrierUniverseSignature.rule .star carrier ∈
      (definition demand).terms := by
  rw [definition_terms]
  unfold CarrierUniverseSignature.termsFor
  exact List.mem_flatMap.mpr ⟨carrier, membership, by simp⟩

/-- If at least one carrier is required, deleting the carrier declarations is
rejected by the ordinary language validator. -/
theorem withoutCarrierTypes_invalid {source : ValidatedLanguageDef}
    (demand : Demand source)
    (nonempty : demand.carrierObjects.objects ≠ []) :
    (withoutCarrierTypes demand).toLanguageDef.validate ≠ [] := by
  intro valid
  have namesNonempty : stableCarrierNames demand ≠ [] := by
    intro namesEmpty
    have lengths := congrArg List.length namesEmpty
    rw [length_stableCarrierNames] at lengths
    simp at lengths
    exact nonempty lengths
  obtain ⟨carrier, carrierMembership⟩ :=
    List.exists_mem_of_ne_nil (stableCarrierNames demand) namesNonempty
  have categoryMembership := LanguageDef.termCategory_mem_of_validate_eq_nil
    (withoutCarrierTypes demand).toLanguageDef valid
    (CarrierUniverseSignature.rule .star carrier)
    (by simpa [withoutCarrierTypes] using
      universeRule_mem demand carrierMembership)
  rw [withoutCarrierTypes_typeNames] at categoryMembership
  simp [CarrierUniverseSignature.rule] at categoryMembership

#print axioms definition_valid
#print axioms definition_language_validate
#print axioms validate?_eq_some
#print axioms withoutCarrierTypes_invalid

end SelectedNativeTypeFoundation

end Mettapedia.OSLF.Framework
