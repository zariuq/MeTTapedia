import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRClosureCanonical

/-! Canonical fact snapshots always pass the existing provider checker.
Fact rows use the authored fact signature; static comparison rows retain
their registered value sorts and the selected source comparison signature. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.ClosureMachine

open Mettapedia.Languages.Datalog
open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted

theorem canonical_closed (program : Program) (seeds : List GroundFact) (prepared : Executable.Prepared)
    (accepted : Executable.prepare program seeds = .ok prepared) (codes : List Pattern)
    (canonical : CanonicalFacts prepared codes) : closed prepared codes = true := by
  have free : (Executable.snapshot prepared codes).free = FreeTypeContext.ofList (Executable.freeTypes prepared.vocabulary) :=
    SourcePlan.plan_free prepared codes
  have grammar : prepared.compiled.terms = Query.baseLanguage.terms := SourcePlan.plan_grammar program seeds prepared accepted codes
  have rows : ∀ row ∈ (Executable.snapshot prepared codes).provider.rows,
      ∃ signature, GeneralPremise.signature? (Executable.snapshot prepared codes).provider row.relation row.values.length = some signature ∧
        GeneralPremise.RowTyped prepared.compiled (Executable.snapshot prepared codes).free [] signature row := by
    intro row member
    rcases List.mem_append.mp member with factRow | comparisonRow
    · obtain ⟨code,present,rfl⟩ := (Query.provider_rows_exact codes row).mp factRow
      obtain ⟨fact,encoded⟩ := canonical code present
      refine ⟨⟨Query.factRelation,[.base "DlStatement"],[.output]⟩,SnapshotReading.fact_signature prepared codes,?_,?_⟩
      · rfl
      · rw [free]
        exact .cons (PhysicalTyping.fact_open prepared.compiled grammar prepared.vocabulary fact code encoded) .nil
    · rw [Executable.prepare_staticRows program seeds prepared accepted] at comparisonRow
      obtain ⟨operator,used,leftRows⟩ := List.mem_flatMap.mp comparisonRow
      obtain ⟨⟨left,index⟩,leftMember,rightRows⟩ := List.mem_flatMap.mp leftRows
      obtain ⟨⟨right,other⟩,rightMember,formed⟩ := List.mem_filterMap.mp rightRows
      dsimp only at formed
      split at formed
      · cases Option.some.inj formed
        have enabled : operator ∈ Executable.operators prepared.source := by
          rw [(Executable.prepare_typed program seeds prepared accepted).1]
          exact used
        refine ⟨⟨Join.comparisonName operator,[.base "DlValue",.base "DlValue"],[.input,.input]⟩,
          SnapshotReading.comparison_signature prepared codes operator enabled,rfl,?_⟩
        rw [free]
        exact .cons (ReferenceTyping.value_open prepared.compiled prepared.vocabulary index
          (List.getElem?_eq_some_iff.mp (List.mk_mem_zipIdx_iff_getElem?.mp leftMember)).1)
          (.cons (ReferenceTyping.value_open prepared.compiled prepared.vocabulary other
            (List.getElem?_eq_some_iff.mp (List.mk_mem_zipIdx_iff_getElem?.mp rightMember)).1) .nil)
      · cases formed
  apply Bool.and_eq_true_iff.mpr
  refine ⟨Bool.and_eq_true_iff.mpr ⟨Executable.snapshot_signature_modes prepared codes,?_⟩,?_⟩
  · exact decide_eq_true (Executable.snapshot_signature_keys_nodup prepared codes)
  · apply List.all_eq_true.mpr
    intro row member
    obtain ⟨signature,found,typed⟩ := rows row member
    simp only [found]
    exact GeneralPremise.checkRow_complete typed

#print axioms canonical_closed

end Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.ClosureMachine
