import Mettapedia.GSLT.LanguageDef.RestrictionBlocks
import Mettapedia.Languages.ProcessCalculi.CCS.LanguageDef

/-!
# CCS's restriction blocks

`ccsCalc` is a calculus with restriction in the sense of the restriction-block theory (`ccsBlockLanguage`): its
parallel composition is a bare bag of processes with inaction as unit, beside one named multiset, the sum of guards,
whose empty instance is inaction; `CNu` binds a name over a process; its declared laws are exactly those of
restriction and of the empty sum; and its guards take names and processes. Its canonical form is the theory's, sound
and complete at every sort, so the static theory of CCS is decided by comparing canonical forms.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.CCS.Blocks

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.RestrictionBlocks
open Mettapedia.GSLT.LanguageDef.WellSorted (FreeTypeContext parameterType? UsesBareCollection)

/-- CCS's blocks: inaction, restriction, processes and names, and the sum as a multiset whose empty instance is
inaction. -/
abbrev ccsBlock : Block := ⟨"CNil", "CNu", "Proc", "Name", ["CSum"], ["CSum"]⟩

@[simp] theorem ccsBlock_unit : ccsBlock.unit = "CNil" := rfl
@[simp] theorem ccsBlock_restrict : ccsBlock.restrict = "CNu" := rfl
@[simp] theorem ccsBlock_proc : ccsBlock.proc = "Proc" := rfl
@[simp] theorem ccsBlock_name : ccsBlock.name = "Name" := rfl
@[simp] theorem ccsBlock_multisets : ccsBlock.multisets = ["CSum"] := rfl
@[simp] theorem ccsBlock_emptyUnits : ccsBlock.emptyUnits = ["CSum"] := rfl

/-- CCS declares exactly the laws of restriction and of the empty sum. -/
theorem ccsCalc_equations : ccsCalc.equations = blockLaws ccsBlock := rfl

/-- Free names have the name sort. -/
def ccsNameContext : FreeTypeContext := fun _ => some (.base "Name")

/-- CCS's context of free names is a context of base sorts. -/
theorem ccsNameContext_base : BaseContext ccsNameContext [] :=
  ⟨fun _ _ found => ⟨"Name", by simpa [ccsNameContext] using found.symm⟩, fun _ member => by simp at member⟩

/-- The sum is a named multiset of guards. -/
theorem sum_namedMultiset : NamedMultiset ccsCalc.terms[2] "Proc" :=
  ⟨rfl, rfl, ⟨"gs", "Guard", rfl, by decide⟩⟩

/-- CCS's parallel composition is a bare bag beside the sum. -/
theorem ccs_parallelBag : ParallelBag ccsCalc ccsCalc.terms[1] "CNil" ["CSum"] where
  bagAuthored := List.getElem_mem (by decide)
  bagShape := ⟨"ps", rfl⟩
  bagAlgebra := rfl
  representedBare := rfl
  unitAuthored := ⟨ccsCalc.terms[0], List.getElem_mem (by decide), rfl, rfl, rfl⟩
  otherParameters := by
    intro rule member notBag
    simp only [ccsCalc, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · left; simp
    · exact absurd rfl notBag
    · exact .inr ⟨by simp, sum_namedMultiset⟩
    all_goals left; simp [TermParam.typeExpr, Mettapedia.GSLT.LanguageDef.BagNormalForm.collectionFree]

/-- **CCS is a calculus with restriction.** -/
instance ccsBlockLanguage : BlockLanguage ccsCalc ccsBlock where
  bag := ⟨ccsCalc.terms[1], ccs_parallelBag, rfl⟩
  equations := rfl
  restrictAuthored := ⟨ccsCalc.terms[3], List.getElem_mem (by decide), rfl⟩
  restrictShape := by
    intro rule member labelIs
    simp only [ccsCalc, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
  unitShape := by
    intro rule member labelIs
    simp only [ccsCalc, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
  multisetShape := by
    intro rule member listed
    simp only [ccsCalc, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp at listed
    exact sum_namedMultiset
  emptyUnitShape := by
    intro label listed
    simp only [List.mem_cons, List.not_mem_nil, or_false] at listed
    subst listed
    refine ⟨by simp, fun rule member labelIs => ?_⟩
    simp only [ccsCalc, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
  emptyUnitAuthored := by
    intro label listed
    simp only [List.mem_cons, List.not_mem_nil, or_false] at listed
    subst listed
    exact ⟨ccsCalc.terms[2], List.getElem_mem (by decide), rfl⟩
  labelsUnique := by decide
  params := by
    intro rule member notBare notMultiset parameter present
    simp only [ccsCalc, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp at present
    · exact absurd ⟨"ps", .hashBag, .base "Proc", rfl⟩ notBare
    · simp at notMultiset
    all_goals
      simp only [List.mem_cons, List.not_mem_nil, or_false] at present
      rcases present with rfl | rfl <;> simp [parameterType?]
  arrowsAbstract := by
    intro rule member notBare notMultiset parameter present domain sort found
    simp only [ccsCalc, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp at present
    · exact absurd ⟨"ps", .hashBag, .base "Proc", rfl⟩ notBare
    · simp at notMultiset
    all_goals
      simp only [List.mem_cons, List.not_mem_nil, or_false] at present
      rcases present with rfl | rfl <;> simp_all [parameterType?]

end Mettapedia.Languages.ProcessCalculi.CCS.Blocks
