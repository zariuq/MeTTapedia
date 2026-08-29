import Mettapedia.Languages.Metamath.MM2NormalLabelInventory
import Mettapedia.Languages.Metamath.MM2SourceActionPlan
import Mettapedia.Languages.Metamath.MM2Transformation

/-!
# Agreement between finite label catalogs and positive normal dispatch data

The fallback label scanner is sound only if a catalog hit corresponds to data
that the earlier positive hypothesis or assertion rule could consume.  This
module proves that source-relative agreement at the exact row boundary.

The theorem is independent of a particular proof token.  It starts from one
actual emitted catalog occurrence and recovers an active source hypothesis or
an ordered source assertion together with its exact positive MM2 runtime row.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2NormalLabelLookupAgreement

open Mettapedia.GSLT.FiniteOccurrenceLookup
open Mettapedia.GSLT.LinkedInventoryLoader
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2DataEncoding
open Mettapedia.Languages.Metamath.MM2NormalLabelInventory
open Mettapedia.Languages.Metamath.MM2SourceActionPlan
open Mettapedia.Languages.Metamath.MM2Transformation
open Mettapedia.Languages.Metamath.SourceGSLTState

/-- Source-relative positive MM2 datum for one catalog label. -/
def PositiveDispatchRowFor (scopeOwner : Atom) (state : SourceState)
    (label : String) (row : Atom) : Prop :=
  (∃ hypothesis ∈ state.activeHypotheses,
      hypothesis.label = label ∧
        row = hypothesisLookupRow scopeOwner hypothesis) ∨
    (∃ (position : Nat) (inBounds : position < state.assertions.length),
      state.assertions[position].label = label ∧
        row = assertionHeaderRow scopeOwner position state.assertions[position])

/-- Every semantic catalog entry has an exact positive runtime row in the
same source-state snapshot. -/
theorem normalLabelInventory_entry_has_positive_dispatch_row
    (scopeOwner : Atom) (state : SourceState)
    (entry : Entry String NormalLabelKind)
    (member : entry ∈ normalLabelInventory state) :
    ∃ row ∈ proofRuntimeRows scopeOwner state,
      PositiveDispatchRowFor scopeOwner state entry.key row := by
  rcases normalLabelInventory_member_source state entry member with
      ⟨hypothesis, hypothesisMember, rfl⟩ |
      ⟨assertion, assertionMember, rfl⟩
  · refine ⟨hypothesisLookupRow scopeOwner hypothesis, ?_, ?_⟩
    · apply List.mem_append_left
      exact List.mem_map.mpr ⟨hypothesis, hypothesisMember, rfl⟩
    · exact Or.inl ⟨hypothesis, hypothesisMember, rfl, rfl⟩
  · obtain ⟨position, inBounds, rfl⟩ :=
      List.mem_iff_getElem.mp assertionMember
    let row := assertionHeaderRow scopeOwner position state.assertions[position]
    refine ⟨row, ?_, ?_⟩
    · apply List.mem_append_right
      exact assertionHeaderRow_mem_normalExecutionRows scopeOwner state
        position inBounds
    · exact Or.inr ⟨position, inBounds, rfl, rfl⟩

/-- Every concrete emitted catalog row retains an occurrence whose value has
an exact positive MM2 dispatch row.  This rules out an orphan catalog entry
on the generated source-data route. -/
theorem emitted_normalLabelCandidate_has_positive_dispatch_row
    (scopeOwner proofOwner : Atom) (state : SourceState) (candidate : Atom)
    (member : candidate ∈ normalLabelCandidateRows proofOwner state) :
    ∃ occurrence ∈ (semanticLabelArtifact state).target,
      normalLabelCandidateRow proofOwner occurrence = candidate ∧
        ∃ row ∈ proofRuntimeRows scopeOwner state,
          PositiveDispatchRowFor scopeOwner state occurrence.value.key row := by
  obtain ⟨occurrence, occurrenceMember, encoded⟩ :=
    (mem_normalLabelCandidateRows_iff proofOwner candidate state).mp member
  have valueMember : occurrence.value ∈ normalLabelInventory state :=
    reifiedInventory_target_value_mem (normalLabelInventory state)
      occurrence occurrenceMember
  obtain ⟨row, rowMember, positive⟩ :=
    normalLabelInventory_entry_has_positive_dispatch_row scopeOwner state
      occurrence.value valueMember
  exact ⟨occurrence, occurrenceMember, encoded, row, rowMember, positive⟩

/-- If the finite semantic lookup reports missing, then neither positive
hypothesis rows nor positive assertion headers can carry that label. -/
theorem missing_label_has_no_positive_dispatch_row
    (scopeOwner : Atom) (state : SourceState) (label : String)
    (missing :
      lookup label (normalLabelInventory state) =
        .missing (normalLabelInventory state).length) :
    ∀ row, ¬ PositiveDispatchRowFor scopeOwner state label row := by
  have absent := (normalLabelLookup_missing_iff state label).mp missing
  intro row positive
  rcases positive with ⟨hypothesis, member, equal, _⟩ |
      ⟨position, inBounds, equal, _⟩
  · exact absent.1 hypothesis member equal
  · exact absent.2 state.assertions[position]
      (List.mem_iff_getElem.mpr ⟨position, inBounds, rfl⟩) equal

#print axioms normalLabelInventory_entry_has_positive_dispatch_row
#print axioms emitted_normalLabelCandidate_has_positive_dispatch_row
#print axioms missing_label_has_no_positive_dispatch_row

end Mettapedia.Languages.Metamath.MM2NormalLabelLookupAgreement
