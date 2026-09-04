import Mettapedia.OSLF.Framework.SelectedNativeTypeContextualCalculus

/-!
# Proof-relevant image of a selected native-type demand

A generated occurrence is represented by an exact position in the authored
demand list.  The position is retained deliberately: equal selected atoms at
different positions remain distinct occurrences and may generate distinct
rule identifiers, provenance, and proof obligations.

This is a representation boundary, not a semantic completeness claim.  It
says exactly which profiled rewrite occurrences were selected for generation.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.SelectedNativeTypeDemand

open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.Framework
open Mettapedia.OSLF.Framework.SelectedNativeTypeContextualCalculus

/-- An exact occurrence position witnessing that `candidate` belongs to one
selected demand.  Distinct positions are not quotiented even when their atoms
are propositionally equal. -/
structure Representation {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (candidate : ProfiledRewriteOccurrence source) where
  slot : Occurrence demand
  occurrenceExact : occurrenceAt demand slot = candidate

/-- Propositional representability is inhabitation of the proof-relevant
occurrence-position witness. -/
def Representable {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (candidate : ProfiledRewriteOccurrence source) : Prop :=
  Nonempty (Representation demand candidate)

/-- The proof-relevant image agrees exactly with ordinary list membership. -/
theorem representable_iff_mem {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (candidate : ProfiledRewriteOccurrence source) :
    Representable demand candidate ↔ candidate ∈ demand.occurrences := by
  constructor
  · rintro ⟨representation⟩
    rw [← representation.occurrenceExact]
    exact List.get_mem demand.occurrences representation.slot
  · intro membership
    obtain ⟨slot, occurrenceExact⟩ := List.mem_iff_get.mp membership
    exact ⟨⟨slot, occurrenceExact⟩⟩

/-- Positive control: every actual selected position represents the atom
stored at that same position. -/
theorem occurrence_representable {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand) :
    Representable demand (occurrenceAt demand slot) :=
  ⟨⟨slot, rfl⟩⟩

/-- Negative control: the empty demand represents no profiled occurrence. -/
theorem empty_not_representable {source : ValidatedLanguageDef}
    (candidate : ProfiledRewriteOccurrence source) :
    ¬ Representable (SelectedNativeTypeDemand.empty source) candidate := by
  rw [representable_iff_mem]
  simp

#print axioms representable_iff_mem
#print axioms occurrence_representable
#print axioms empty_not_representable

end Mettapedia.OSLF.Framework.SelectedNativeTypeDemand
