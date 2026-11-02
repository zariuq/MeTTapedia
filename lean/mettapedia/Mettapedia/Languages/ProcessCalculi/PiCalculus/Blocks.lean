import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationCompleteness
import Mettapedia.Languages.ProcessCalculi.PiCalculus.AuthoredSemantics

/-!
# The π-calculus's restriction blocks

`piCalc` is a calculus with restriction and replication in the sense of the restriction-block theory: its parallel
composition is a bare bag of processes with inaction as unit, `PiNu` binds a name over a process, `PiRep` replicates a
process, its declared laws are exactly those of restriction (inaction, exchange, extrusion) and of replication, and its
other constructors take names and abstractions of processes over names (`piReplicationLanguage`). Its canonical form is
the replication theory's (`canonR`), sound at every sort and complete on object terms.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PiCalculus.Blocks

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.RestrictionBlocks
open Mettapedia.GSLT.LanguageDef.WellSorted (parameterType? UsesBareCollection)
open Mettapedia.Languages.ProcessCalculi.PiCalculus.PiCalcInstance (piCalc piBagPresentation piNameContext)

/-- π's blocks: inaction, restriction, processes and names. -/
abbrev piBlock : Block := ⟨"PiNil", "PiNu", "Proc", "Name", [], []⟩

@[simp] theorem piBlock_unit : piBlock.unit = "PiNil" := rfl
@[simp] theorem piBlock_restrict : piBlock.restrict = "PiNu" := rfl
@[simp] theorem piBlock_proc : piBlock.proc = "Proc" := rfl
@[simp] theorem piBlock_name : piBlock.name = "Name" := rfl
@[simp] theorem piBlock_multisets : piBlock.multisets = [] := rfl
@[simp] theorem piBlock_emptyUnits : piBlock.emptyUnits = [] := rfl

/-- π's blocks with replication: `PiRep` replicates a process. -/
abbrev piRepBlock : ReplicationBlock := ⟨piBlock, "PiRep", true⟩

@[simp] theorem piRepBlock_toBlock : piRepBlock.toBlock = piBlock := rfl
@[simp] theorem piRepBlock_replicate : piRepBlock.replicate = "PiRep" := rfl

/-- π declares exactly the laws of restriction and of replication. -/
theorem piCalc_equations : piCalc.equations = replicationBlockLaws piRepBlock := rfl

/-- **π is a calculus with restriction and replication.** -/
instance piReplicationLanguage : ReplicationLanguage piCalc piRepBlock where
  bag := ⟨piCalc.terms[1], ParallelBag.ofBare (piBagPresentation.asBare rfl), rfl⟩
  equations := rfl
  restrictAuthored := ⟨piCalc.terms[4], List.getElem_mem (by decide), rfl⟩
  restrictShape := by
    intro rule member labelIs
    simp only [piCalc, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
  unitShape := by
    intro rule member labelIs
    simp only [piCalc, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
  multisetShape := by
    intro rule member listed
    simp at listed
  emptyUnitShape := by
    intro label listed
    simp at listed
  emptyUnitAuthored := by
    intro label listed
    simp at listed
  labelsUnique := by decide
  params := by
    intro rule member notBare _ parameter present
    simp only [piCalc, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl
    · simp at present
    · exact absurd ⟨"ps", .hashBag, .base "Proc", rfl⟩ notBare
    all_goals
      simp only [List.mem_cons, List.not_mem_nil, or_false] at present
      rcases present with rfl | rfl <;> simp [parameterType?]
  arrowsAbstract := by
    intro rule member notBare _ parameter present domain sort found
    simp only [piCalc, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl
    · simp at present
    · exact absurd ⟨"ps", .hashBag, .base "Proc", rfl⟩ notBare
    all_goals
      simp only [List.mem_cons, List.not_mem_nil, or_false] at present
      rcases present with rfl | rfl <;> simp_all [parameterType?]
  replicateAuthored := ⟨piCalc.terms[5], List.getElem_mem (by decide), rfl⟩
  replicateShape := by
    intro rule member labelIs
    simp only [piCalc, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
  replicateFresh := by decide

/-- **π's signature is a restriction-block signature.** -/
instance piBlockSignature : BlockSignature piCalc piBlock := piReplicationLanguage.toBlockSignature

/-- π's context of free names is a context of base sorts. -/
theorem piNameContext_base : BaseContext piNameContext [] :=
  ⟨fun _ _ found => ⟨"Name", by simpa [piNameContext] using found.symm⟩, fun _ member => by simp at member⟩

end Mettapedia.Languages.ProcessCalculi.PiCalculus.Blocks
