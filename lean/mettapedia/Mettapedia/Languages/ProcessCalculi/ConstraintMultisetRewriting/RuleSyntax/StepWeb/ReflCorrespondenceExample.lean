import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ReflCorrespondenceForward
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ReflQuotientControls

/-!
# The REFL correspondence at the name frame: the forward simulation applies, under both interfaces

* `pPar_reads_named`, `pPar_reads_closed`: a made row that reads as `for(@(pPar as) <- x) 0 @ Root` reads as the
  represented named listener of `R` when `pPar as` and `predotU R` agree modulo the bag laws, and as the corrected
  listener `listener x R` when `pPar as` and `canonicalBag R` do.
* `refl_forward_example`: the manuscript's redex `for((0) <- @0)0 | for(y <- @0)y`, reflected on `@0` at the root,
  meets every hypothesis of `refl_forward_comm`: the located run exists.
* `example_source_step`: the corrected semantics with canonical REFL steps the source reflection to the listener of
  the COMM reduct; `example_closed`, `example_named`: the hosted made row reads as that listener (closed quotes) and
  as the represented literal listener (named quotes), at every solution.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ReflCorrespondence

open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern)
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus (pFor par pZero pPar nQuote tProc pReflect applyDot demoChan)
open MeTTaOperationsComm (psubst PSubst pvars)
open MeTTaCalculus.Corrected (canonicalBag)
open FiniteProgram (predot)
open ReflQuotient (BagLaws)
open ReflNames (NameLaws nameAction nameLaws_pFor_iff nameLaws_tProc nameLaws_heads nameLaws_psubst)
open ReflLocated (atLoc rootLoc childLoc locatedFrame_name psubst_rootLoc psubst_atLoc_any)
open ReflLocatedStep (psubst_childLoc)
open ReflUniform (predotU)
open Comm.Controls (zeroTerm y unifier unifier_groundPrincipal)
open FiniteProgram.Controls (example_apart)
open ReflQuotient.Controls (yToZero)

/-! ## The two interfaces on a made row -/

/-- **Named quotes**: the made row reads as the represented listener of the reduct as written. -/
theorem pPar_reads_named {σ : PSubst} {made x : Pattern} {as : List Pattern} (R : Pattern)
    (represented : BagLaws (pPar as) (predotU R))
    (reads : NameLaws made (psubst σ (atLoc (pFor (tProc (pPar as)) x pZero) rootLoc))) :
    NameLaws made (psubst σ (atLoc (pFor (tProc (predotU R)) x pZero) rootLoc)) :=
  reads.trans (nameLaws_psubst σ ((locatedFrame_name.atLoc_iff _ _ _ _).mpr
    ⟨nameLaws_pFor_iff.mpr ⟨nameLaws_tProc represented, ReflNames.NameLaws.refl _, ReflNames.NameLaws.refl _⟩,
      ReflNames.NameLaws.refl _⟩))

/-- **Closed quotes**: the made row reads as the corrected listener of the reduct. -/
theorem pPar_reads_closed {σ : PSubst} {made x : Pattern} {as : List Pattern} (R : Pattern)
    (closedQuote : BagLaws (pPar as) (canonicalBag R))
    (reads : NameLaws made (psubst σ (atLoc (pFor (tProc (pPar as)) x pZero) rootLoc))) :
    NameLaws made (psubst σ (atLoc (MeTTaCalculus.Corrected.listener x R) rootLoc)) :=
  reads.trans (nameLaws_psubst σ ((locatedFrame_name.atLoc_iff _ _ _ _).mpr
    ⟨nameLaws_pFor_iff.mpr ⟨nameLaws_tProc closedQuote, ReflNames.NameLaws.refl _, ReflNames.NameLaws.refl _⟩,
      ReflNames.NameLaws.refl _⟩))

/-! ## The manuscript's redex, reflected -/

/-- The source redex: `for((0) <- @0)0 | for(y <- @0)y`. -/
def exampleSource : Pattern := par (pFor zeroTerm demoChan pZero) (pFor y demoChan y)

/-- Its representation, the process the reflection carries. -/
def exampleProcess : Pattern := par (predot (pFor zeroTerm demoChan pZero)) (predot (pFor y demoChan y))

/-- The source reduct of its COMM. -/
def exampleReduct : Pattern := par (applyDot unifier pZero) (applyDot unifier y)

/-- One row: the reflection `@0?(...)` at the root. -/
def exampleRows : ℕ → Pattern := fun _ => atLoc (pReflect demoChan exampleProcess) rootLoc

def exampleConf : Configuration Pattern ℕ := ⟨[], {0}⟩

theorem example_represents : predot (pReflect demoChan exampleSource) = pReflect demoChan exampleProcess := by
  decide +kernel

theorem example_clean : Clean (childLoc rootLoc demoChan exampleProcess) exampleRows exampleConf := by
  intro o _ σ _
  refine ⟨fun m same => ?_, fun m c same => ?_, fun z same => ?_⟩
  · change NameLaws (psubst σ (atLoc (pReflect demoChan exampleProcess) rootLoc)) _ at same
    rw [psubst_atLoc_any] at same
    exact absurd (nameLaws_heads same) (by decide)
  · change NameLaws (psubst σ (atLoc (pReflect demoChan exampleProcess) rootLoc)) _ at same
    rw [psubst_atLoc_any] at same
    exact absurd (nameLaws_heads same) (by decide)
  · change NameLaws (psubst σ (atLoc (pReflect demoChan exampleProcess) rootLoc)) _ at same
    rw [psubst_atLoc_any, psubst_rootLoc, psubst_childLoc, psubst_rootLoc] at same
    exact absurd (nameLaws_heads ((locatedFrame_name.atLoc_iff _ _ _ _).mp same).2) (by decide)

/-- **The forward simulation applies**: REFL of the manuscript's redex at the root is matched by a located run of
the name frame, whose made row reads as `for(@(pPar [predot (applyDot bs 0), predot (applyDot bs y)]) <- @0) 0`. -/
theorem refl_forward_example :
    ∃ (label' : ℕ → Pattern) (C' : Configuration Pattern ℕ) (made : ℕ),
      LocatedRun exampleRows exampleConf label' C' ∧ made ∈ C'.present ∧ 0 ∉ C'.present ∧
      (∀ σ : PSubst, nameAction.Models σ C'.equations →
        NameLaws (psubst σ (label' made)) (psubst σ (atLoc (pFor (tProc (pPar ([] ++ [] ++ [] ++
          [predot (applyDot unifier pZero), predot (applyDot unifier y)]))) demoChan pZero) rootLoc))) ∧
      (∀ o ∈ exampleConf.present, o ≠ 0 → o ∈ C'.present ∧ label' o = exampleRows o) ∧
      (∃ σ₁ : PSubst, nameAction.Models σ₁ C'.equations) :=
  refl_forward_comm exampleRows exampleConf demoChan exampleProcess 0 (fun _ _ => ReflNames.NameLaws.refl _)
    example_clean (by decide) (Splits.split (Splits.leaf _) (Splits.leaf _)) [] [] [] zeroTerm y demoChan pZero y
    rfl unifier unifier_groundPrincipal example_apart (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (σ₀ := yToZero)
    (fun _ member => absurd member List.not_mem_nil) (by decide +kernel)

/-- **The source step** (closed quotes): the corrected semantics with canonical REFL steps the reflection of the
redex to the listener of its COMM reduct. -/
theorem example_source_step :
    MeTTaCalculus.Corrected.CanonicalBagStep MeTTaCalculus.Corrected.conventional
      (pReflect demoChan exampleSource) (MeTTaCalculus.Corrected.listener demoChan exampleReduct) :=
  .reflect demoChan (.comm zeroTerm y demoChan pZero y unifier (Comm.principal_of_groundPrincipal unifier_groundPrincipal)
    example_apart)

/-- **Closed quotes, end to end**: the hosted made row reads as the corrected listener of the reduct. -/
theorem example_closed :
    ∃ (label' : ℕ → Pattern) (C' : Configuration Pattern ℕ) (made : ℕ),
      LocatedRun exampleRows exampleConf label' C' ∧ made ∈ C'.present ∧ 0 ∉ C'.present ∧
      ∀ σ : PSubst, nameAction.Models σ C'.equations →
        NameLaws (psubst σ (label' made))
          (psubst σ (atLoc (MeTTaCalculus.Corrected.listener demoChan exampleReduct) rootLoc)) := by
  obtain ⟨label', C', made, run, inside, gone, reads, -, -⟩ := refl_forward_example
  exact ⟨label', C', made, run, inside, gone, fun σ solved =>
    pPar_reads_closed exampleReduct ((ReflQuotient.bagLaws_iff _ _).mpr (by decide +kernel)) (reads σ solved)⟩

/-- **Named quotes, end to end**: the hosted made row reads as the represented literal listener
`for(@(predotU R) <- @0) 0` of the reduct as written. -/
theorem example_named :
    ∃ (label' : ℕ → Pattern) (C' : Configuration Pattern ℕ) (made : ℕ),
      LocatedRun exampleRows exampleConf label' C' ∧ made ∈ C'.present ∧ 0 ∉ C'.present ∧
      ∀ σ : PSubst, nameAction.Models σ C'.equations →
        NameLaws (psubst σ (label' made))
          (psubst σ (atLoc (pFor (tProc (predotU exampleReduct)) demoChan pZero) rootLoc)) := by
  obtain ⟨label', C', made, run, inside, gone, reads, -, -⟩ := refl_forward_example
  exact ⟨label', C', made, run, inside, gone, fun σ solved =>
    pPar_reads_named exampleReduct ((ReflQuotient.bagLaws_iff _ _).mpr (by decide +kernel)) (reads σ solved)⟩

#print axioms pPar_reads_named
#print axioms pPar_reads_closed
#print axioms example_represents
#print axioms example_clean
#print axioms refl_forward_example
#print axioms example_source_step
#print axioms example_closed
#print axioms example_named

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ReflCorrespondence
