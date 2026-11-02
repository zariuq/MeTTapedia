import Mettapedia.Languages.ProcessCalculi.Ambient.Comm
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationReference

/-!
# The core of the ambient calculus with communication

The located form reads the ambient calculus with communication without its laws of paths: its terms and reaction
rules, with the laws of the pure calculus, those of restriction, of replication and the boundary law
(`ambientCoreCalc`). The laws of paths are read before, by the path normal form, which leaves only prefixes by
capability variables, prefixes no law reads.

The core has the signature of the restriction-block theory and of replication (`coreSignature`,
`coreReplicationSignature`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.Ambient.Comm

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.RestrictionBlocks (replicationBlockLaws BlockSignature ReplicationSignature
  ParallelBag)
open Mettapedia.GSLT.LanguageDef.BagNormalForm (BagPresentation)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.Ambient.Full

/-- **The core of the calculus**: the terms and reaction rules of the calculus with communication, and the laws of the
pure calculus, without the laws of paths. -/
def ambientCoreCalc : LanguageDef :=
  { name := "MobileAmbientsCore"
    types := ["Proc", "Name", "Cap"]
    terms := terms ++ commTerms
    equations := replicationBlockLaws ambientRepBlock ++ [ambientBoundary]
    rewrites := [inRule, outRule, openRule, commNameRule, commCapRule, parCongRule, resCongRule, ambCongRule] }

theorem ambientCoreCalc_terms : ambientCoreCalc.terms = ambientCommCalc.terms := rfl

theorem ambientCoreCalc_equations : ambientCoreCalc.equations = ambientNuCalc.equations := rfl

theorem ambientCoreCalc_rewrites : ambientCoreCalc.rewrites = ambientCommCalc.rewrites := rfl

/-- The parallel constructor declares the bag monoid with inaction as its unit. -/
theorem coreBagPresentation : BagPresentation ambientCoreCalc ambientCoreCalc.terms[1] (some "AZero") where
  bagAuthored := List.getElem_mem (by decide)
  bagShape := ⟨"ps", rfl⟩
  bagAlgebra := rfl
  otherParameters := by
    intro rule member different parameter present
    simp only [ambientCoreCalc, terms, commTerms, prefixRule, capRule, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl
    · simp at present
    · exact False.elim (different rfl)
    all_goals
      simp only [List.mem_cons, List.not_mem_nil, or_false] at present
    all_goals rcases present with rfl | rfl <;> rfl
  unitAuthored := by
    intro unit same
    cases Option.some.inj same
    exact ⟨ambientCoreCalc.terms[0], List.getElem_mem (by decide), rfl, rfl, rfl⟩

/-- **The core has the signature of the restriction-block theory**: a bare parallel bag with inaction as unit,
restriction binding a name over a process, and the laws of restriction declared. -/
instance coreSignature : BlockSignature ambientCoreCalc ambientBlock where
  bag := ⟨ambientCoreCalc.terms[1], ParallelBag.ofBare (coreBagPresentation.asBare rfl), rfl⟩
  lawsDeclared := by
    intro law member
    simp only [ambientCoreCalc, replicationBlockLaws]
    exact List.mem_append_left _ (List.mem_append_left _ member)
  restrictAuthored := ⟨ambientCoreCalc.terms[2], List.getElem_mem (by decide), rfl⟩
  restrictShape := by
    intro rule member labelIs
    simp only [ambientCoreCalc, terms, commTerms, prefixRule, capRule, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl <;> simp_all
  unitShape := by
    intro rule member labelIs
    simp only [ambientCoreCalc, terms, commTerms, prefixRule, capRule, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl <;> simp_all
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
    simp only [ambientCoreCalc, terms, commTerms, prefixRule, capRule, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl
    · simp at present
    · exact absurd ⟨"ps", .hashBag, .base "Proc", rfl⟩ notBare
    all_goals
      simp only [List.mem_cons, List.not_mem_nil, or_false] at present
    all_goals rcases present with rfl | rfl <;> simp [parameterType?]
  arrowsAbstract := by
    intro rule member notBare _ parameter present domain sort found
    simp only [ambientCoreCalc, terms, commTerms, prefixRule, capRule, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl
    · simp at present
    · exact absurd ⟨"ps", .hashBag, .base "Proc", rfl⟩ notBare
    all_goals
      simp only [List.mem_cons, List.not_mem_nil, or_false] at present
    all_goals rcases present with rfl | rfl <;> simp_all [parameterType?]

/-- **The core has the signature of replication.** -/
instance coreReplicationSignature : ReplicationSignature ambientCoreCalc ambientRepBlock where
  toBlockSignature := coreSignature
  replicationDeclared := fun _ member =>
    List.mem_append_left _ (List.mem_append_right _ member)
  replicateAuthored := ⟨ambientCoreCalc.terms[3], List.getElem_mem (by decide), rfl⟩
  replicateShape := by
    intro rule member labelIs
    simp only [ambientCoreCalc, terms, commTerms, prefixRule, capRule, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl <;> simp_all
  replicateFresh := by decide

end Mettapedia.Languages.ProcessCalculi.Ambient.Comm
