import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.ExecutableWrittenSchemaSelection
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Examples.ExecutableSchemaControls

/-!
# Written-schema equality and priority controls

Distinct written domains can erase to one computation term. Repeated source
slots retain that distinction, and source priority can select a different
entry after erasure. The source receipt and the erased value are consequently
different readouts. Captures instantiated under binders retain their domains
and their free references.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality.Normalization.ExecutableWrittenSchemaControls

open ExecutableWrittenSchemaMatching ExecutableWrittenSchemaSelection

def repeated : ATm Unit 1 := .app (.var 0) (.var 0)
def firstIdentity : ATm Unit 0 := .lamTyped (.const `firstDomain) (.var 0)
def secondIdentity : ATm Unit 0 := .lamTyped (.const `secondDomain) (.var 0)
def differingCaptures : ATm Unit 0 := .app firstIdentity secondIdentity

theorem written_domains_are_distinct : firstIdentity ≠ secondIdentity := by decide +kernel

theorem erasures_agree : firstIdentity.erase = secondIdentity.erase := rfl

theorem repeated_written_capture_refuses :
    run repeated differingCaptures (fun _ => none) = none := by decide +kernel

theorem repeated_erased_capture_matches :
    (ExecutableSchemaMatching.run repeated.erase differingCaptures.erase (fun _ => none)).isSome = true := by
  decide +kernel

theorem repeated_same_written_capture_matches :
    (run repeated (.app firstIdentity firstIdentity) (fun _ => none)).isSome = true := by
  decide +kernel

def ordered : WrittenTable Unit :=
  [⟨1, repeated, .const `sameSource⟩, ⟨1, .var 0, .const `fallback⟩]

theorem written_priority_keeps_the_fallback :
    (first ordered differingCaptures).target? = some (.const `fallback) := by decide +kernel

theorem written_priority_retains_origin :
    (first ordered differingCaptures).position? = some 1 := by decide +kernel

theorem erased_priority_selects_another_entry :
    (ExecutableSchemaSelection.first (eraseTable ordered) differingCaptures.erase).target? =
      some (.const `sameSource) := by decide +kernel

theorem source_priority_does_not_descend_through_erasure :
    (first ordered differingCaptures).target?.map ATm.erase ≠
      (ExecutableSchemaSelection.first (eraseTable ordered) differingCaptures.erase).target? := by
  rw [written_priority_keeps_the_fallback, erased_priority_selects_another_entry]
  decide +kernel

def captureBeneathBinder : WrittenTable Unit :=
  [⟨2, .app (.var 0) (.var 1), .lamTyped (.var 0) (.app (.var 0) (.var 2))⟩]

theorem written_domain_and_free_slot_survive_instantiation :
    (first captureBeneathBinder (.app (.const `domain) (.var 0) : ATm Unit 1)).target? =
      some (.lamTyped (.const `domain) (.app (.var 0) (.var 1))) := by decide +kernel

def missingDomainSlot : WrittenTable Unit :=
  [⟨1, .const `source, .lamTyped (.var 0) (.var 0)⟩]

theorem missing_written_domain_is_a_refusal :
    (first missingDomainSlot (.const `source : ATm Unit 0)).target? = none := by decide +kernel

theorem missing_written_domain_retains_origin :
    (first missingDomainSlot (.const `source : ATm Unit 0)).position? = some 0 := by decide +kernel

end TypedEquality.Normalization.ExecutableWrittenSchemaControls
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
