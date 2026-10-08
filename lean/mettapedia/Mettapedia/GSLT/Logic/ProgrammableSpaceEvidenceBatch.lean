import Mettapedia.GSLT.Logic.ProgrammableSpaceEvidenceConsumers
import Mettapedia.GSLT.Logic.ProgrammableSpaceEvidenceReadings

/-!
# Actual receipt batches and dependent sections on their fact support

A current receipt list supplies its own recovery map: find the first occurrence
of a requested supported fact. This map is computed from the authored list;
there is no selected representative or choice principle in the construction.
The observed whole sections are exactly the compatible occurrence sections.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.ProgrammableSpaceEvidence

attribute [local instance] Finite.membership

open Mettapedia.TypeTheory.ExtensionalReadout
open Mettapedia.TypeTheory.DependentFamilyObserverFactorization
open Mettapedia.TypeTheory.DependentFamilySectionDescent

universe u v w
variable {Atom : Type u} {Origin : Type v} [DecidableEq Atom]
variable {source : Source Atom Origin}

abbrev BatchOccurrence (batch : List (Receipt source)) := Fin batch.length
abbrev BatchMember (batch : List (Receipt source)) := {atom : Atom // atom ∈ batchSupport batch}

def batchObservation (batch : List (Receipt source)) (index : BatchOccurrence batch) :
    BatchMember batch :=
  ⟨(batch.get index).fact, (mem_batchSupport batch _).mpr
    ⟨batch.get index, List.get_mem _ _, rfl⟩⟩

def firstOccurrence (batch : List (Receipt source)) (member : BatchMember batch) :
    BatchOccurrence batch :=
  let index := Finite.firstIndex (batch.map Receipt.fact) member.val
    ((Finite.mem_support _ _).mp member.property)
  ⟨index.val, by simpa only [List.length_map] using index.isLt⟩

@[simp] theorem batchObservation_firstOccurrence (batch : List (Receipt source))
    (member : BatchMember batch) : batchObservation batch (firstOccurrence batch member) = member := by
  apply Subtype.ext
  change (batch.get (firstOccurrence batch member)).fact = member.val
  have same := Finite.get_firstIndex (batch.map Receipt.fact) member.val
    ((Finite.mem_support _ _).mp member.property)
  simpa only [List.get_eq_getElem, List.getElem_map, firstOccurrence] using same

def batchReadout (batch : List (Receipt source)) :
    SplitReadout (BatchOccurrence batch) (BatchMember batch) where
  observe := batchObservation batch
  representative := firstOccurrence batch
  observe_representative := batchObservation_firstOccurrence batch

@[simp] theorem batchObservation_eq_iff (batch : List (Receipt source))
    (first second : BatchOccurrence batch) :
    batchObservation batch first = batchObservation batch second ↔
      (batch.get first).fact = (batch.get second).fact := Subtype.ext_iff

variable {family : Receipt source → Type w}

def batchFamily (d : FamilyFactorization Receipt.fact family)
    (batch : List (Receipt source)) :
    FamilyFactorization (batchObservation batch) (fun index => family (batch.get index)) :=
  reindexFamily d batch.get (batchObservation batch) Subtype.val (fun _ => rfl)

/-- This equivalence uses the computed recovery from the actual current batch. -/
def batchSectionEquiv (d : FamilyFactorization Receipt.fact family)
    (batch : List (Receipt source)) :
    (∀ member : BatchMember batch, d.targetFamily member.val) ≃
      {term : ∀ index : BatchOccurrence batch, family (batch.get index) //
        Compatible (batchFamily d batch) term} :=
  sectionEquiv (batchReadout batch) (batchFamily d batch)

theorem compatible_on_batch (d : FamilyFactorization Receipt.fact family)
    (term : ∀ receipt, family receipt) (compatible : Compatible d term)
    (batch : List (Receipt source)) :
    Compatible (batchFamily d batch) (fun index => term (batch.get index)) :=
  compatible_reindex d batch.get (batchObservation batch) Subtype.val (fun _ => rfl)
    term compatible

@[simp] theorem batchSectionEquiv_apply (d : FamilyFactorization Receipt.fact family)
    (batch : List (Receipt source)) (term : ∀ member : BatchMember batch, d.targetFamily member.val)
    (index : BatchOccurrence batch) :
    (batchSectionEquiv d batch term).val index =
      (d.identify (batch.get index)).symm (term (batchObservation batch index)) := rfl

theorem batch_compatible_iff_descends (d : FamilyFactorization Receipt.fact family)
    (batch : List (Receipt source)) (term : ∀ index : BatchOccurrence batch, family (batch.get index)) :
    Compatible (batchFamily d batch) term ↔
      ∃ observed : ∀ member : BatchMember batch, d.targetFamily member.val,
        (batchSectionEquiv d batch observed).val = term := by
  constructor
  · intro compatible
    exact ⟨(batchSectionEquiv d batch).symm ⟨term, compatible⟩,
      congrArg Subtype.val ((batchSectionEquiv d batch).apply_symm_apply ⟨term, compatible⟩)⟩
  · rintro ⟨observed, rfl⟩
    exact (batchSectionEquiv d batch observed).property

end Mettapedia.GSLT.ProgrammableSpaceEvidence
