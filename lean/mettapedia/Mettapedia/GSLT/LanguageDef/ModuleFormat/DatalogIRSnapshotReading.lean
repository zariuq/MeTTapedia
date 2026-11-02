import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRGuardReading
import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRSnapshotRows

/-! Source queries read the exact fact positions of the prepared snapshot.
Comparison signatures and rows remain those of the authored program. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.SnapshotReading

open Mettapedia.Languages.Datalog
open Mettapedia.OSLF.MeTTaIL Syntax

private theorem unique_list {α : Type} (items : List α) (chosen : α)
    (distinct : items.Nodup) (present : chosen ∈ items)
    (only : ∀ item ∈ items, item = chosen) : items = [chosen] := by
  cases items with
  | nil => simp at present
  | cons head rest =>
    have same := only head List.mem_cons_self
    subst head
    have empty : rest = [] := List.eq_nil_iff_forall_not_mem.mpr (by
      intro item member
      have equal := only item (List.mem_cons_of_mem _ member)
      exact (List.nodup_cons.mp distinct).1 (equal ▸ member))
    rw [empty]

theorem fact_signature (prepared : Executable.Prepared) (known : List Pattern) :
    GeneralPremise.signature? (Executable.snapshot prepared known).provider Query.factRelation 1 =
      some ⟨Query.factRelation,[.base "DlStatement"],[.output]⟩ := by
  have empty : (Executable.comparisonSignatures prepared.source).filter (fun signature =>
      signature.relation == Query.factRelation && signature.argumentTypes.length == 1) = [] := by
    simp [Executable.comparisonSignatures,List.filter_map,Function.comp_def]
  simp [GeneralPremise.signature?,Executable.snapshot,empty]

theorem comparison_signature (prepared : Executable.Prepared) (known : List Pattern)
    (operator : ComparisonOperator) (used : operator ∈ Executable.operators prepared.source) :
    GeneralPremise.signature? (Executable.snapshot prepared known).provider (Join.comparisonName operator) 2 =
      some ⟨Join.comparisonName operator,[.base "DlValue",.base "DlValue"],[.input,.input]⟩ := by
  let signatures := (Executable.snapshot prepared known).provider.signatures
  let selected := signatures.filter (fun signature =>
    signature.relation == Join.comparisonName operator && signature.argumentTypes.length == 2)
  have distinct : signatures.Nodup := List.Nodup.of_map _ (Executable.snapshot_signature_keys_nodup prepared known)
  have present : (⟨Join.comparisonName operator,[.base "DlValue",.base "DlValue"],[.input,.input]⟩ : GeneralPremise.Signature)
      ∈ selected := by
    apply List.mem_filter.mpr
    refine ⟨List.mem_cons_of_mem _ (List.mem_map.mpr ⟨operator,used,rfl⟩),by simp⟩
  have unique : ∀ signature ∈ selected,
      signature = ⟨Join.comparisonName operator,[.base "DlValue",.base "DlValue"],[.input,.input]⟩ := by
    intro signature member
    obtain ⟨member,accepted⟩ := List.mem_filter.mp member
    rcases List.mem_cons.mp member with same | member
    · subst signature
      simp at accepted
    · obtain ⟨actual,_,rfl⟩ := List.mem_map.mp member
      have same : actual = operator := Executable.comparisonName_injective (by simpa using accepted)
      subst actual
      rfl
  have filtered := unique_list selected _ (List.Nodup.filter _ distinct) present unique
  change (match selected with
    | [signature] => if signature.modes.length == 2 then some signature else none
    | _ => none) = _
  rw [filtered]
  rfl

theorem fact_row_position (program : Program) (seeds : List GroundFact) (prepared : Executable.Prepared)
    (accepted : Executable.prepare program seeds = .ok prepared) (known : List Pattern)
    (index : Nat) (value : Pattern)
    (row : (Executable.snapshot prepared known).provider.rows[index]? = some ⟨Query.factRelation,[value]⟩) :
    known[index]? = some value := by
  by_cases before : index < known.length
  · have beforeRows : index < (Query.provider known).rows.length := by simpa [Query.provider] using before
    have read : (Query.provider known).rows[index]? = some ⟨Query.factRelation,[value]⟩ := by
      simpa only [Executable.snapshot,List.getElem?_append_left beforeRows] using row
    simpa [Query.provider] using read
  · have afterRows : (Query.provider known).rows.length ≤ index := by simpa [Query.provider] using Nat.le_of_not_gt before
    have member : (⟨Query.factRelation,[value]⟩ : GeneralPremise.ProviderRow) ∈ prepared.staticRows := by
      apply List.mem_of_getElem?
      simpa only [Executable.snapshot,List.getElem?_append_right afterRows] using row
    rw [Executable.prepare_staticRows program seeds prepared accepted] at member
    obtain ⟨operator,_,rows⟩ := List.mem_flatMap.mp member
    obtain ⟨_,_,rows⟩ := List.mem_flatMap.mp rows
    obtain ⟨_,_,formed⟩ := List.mem_filterMap.mp rows
    dsimp only at formed
    split at formed
    · have shape := congrArg (fun row : GeneralPremise.ProviderRow => row.values.length) (Option.some.inj formed)
      simp at shape
    · cases formed

#print axioms fact_signature
#print axioms comparison_signature
#print axioms fact_row_position

end Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.SnapshotReading
