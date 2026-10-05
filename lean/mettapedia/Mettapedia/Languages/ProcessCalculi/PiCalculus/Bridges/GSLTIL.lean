import Mettapedia.Languages.ProcessCalculi.PiCalculus.ReflectionControls
import Mettapedia.GSLT.LanguageDef.GSLTILFibreExecution
import Mettapedia.GSLT.Meredith.GSLT
import Mettapedia.OSLF.Framework.SuccessorFrontier

/-!
# Complete pi frontiers as a qualified command fibre

The existing command language executes pi's occurrence-based internal
relation through the actual authored executor. Query qualification uses both
directions of the independently proved rule comparison. Consequently every
command path from an encoded state has an actual source endpoint, and Boolean
frontier observations agree with the shared operational modalities.

This fibre observes internal execution with syntactic equality. It does not
enumerate equation saturation or present the full named pi static quotient.
The separate native predicates and modalities continue to use that declared
equation relation. No route entries or alternative command rules are added.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PiCalculus.Bridges.GSLTIL

open Mettapedia.GSLT
open Mettapedia.GSLT.Ultrainfinite
open Mettapedia.GSLT.LanguageDef.GSLTIL
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.OSLF.Framework.DerivedModalities
open Mettapedia.OSLF.Framework.SuccessorFrontier
open PiCalcInstance

/-- The independently specified internal occurrence relation, before static
equation saturation, viewed through the shared equality-GSLT construction. -/
abbrev internalTheory : GSLT := equalityGSLT Pattern PiRawStep

/-- The original authored executor at its computed complete context bound. -/
def completeFrontier (source : Pattern) : List Pattern :=
  piCalcReducts (piContextDepth source) source

theorem frontier_qualified (source target : Pattern) :
    target ∈ completeFrontier source ↔ internalTheory.Step source target :=
  (pi_complete_frontier_iff_step source target).trans (pi_step_iff_raw source target)

/-- Qualification forbids both missing source firings and invented command
answers. The encoding is the actual unchanged guest syntax. -/
theorem guest_qualified (source answer : Pattern) :
    answer ∈ completeFrontier source ↔
      ∃ next, internalTheory.Step source next ∧ answer = next := by
  rw [frontier_qualified]
  constructor
  · intro firing
    exact ⟨answer, firing, rfl⟩
  · rintro ⟨next, firing, rfl⟩
    exact firing

def stage : Pattern := .apply "PiInternal" []

abbrev commandTheory : GSLT := FibreExecution.theory stage completeFrontier

/-- This uses the existing authored `at` rule and its arbitrary-target cover. -/
theorem command_cover :
    StepCover internalTheory commandTheory (atPattern stage) :=
  FibreExecution.stepCover internalTheory stage id completeFrontier guest_qualified

theorem command_step_iff (source target : Pattern) :
    commandTheory.Step (atPattern stage source) target ↔
      ∃ next, PiRawStep source next ∧ target = atPattern stage next := by
  rw [FibreExecution.step_at_iff]
  simp only [frontier_qualified, internalTheory, equalityGSLT_step]

/-- The actual endpoint of every command path remains in the selected fibre
and reflects to an internal source path. -/
theorem arbitrary_command_paths_reflect (initial : Pattern) {target : Pattern}
    (path : commandTheory.MultiStep (atPattern stage initial) target) :
    ∃ final, target = atPattern stage final ∧
      Relation.ReflTransGen PiRawStep initial final := by
  obtain ⟨final, same, sourcePath⟩ :=
    FibreExecution.path_reflected internalTheory stage id completeFrontier
      command_cover initial path
  exact ⟨final, same,
    (Meredith.multiStep_iff_reflTransGen internalTheory initial final).mp sourcePath⟩

theorem internal_paths_preserved {initial final : Pattern}
    (path : Relation.ReflTransGen PiRawStep initial final) :
    commandTheory.MultiStep (atPattern stage initial) (atPattern stage final) :=
  FibreExecution.path_preserved internalTheory stage id completeFrontier command_cover
    ((Meredith.multiStep_iff_reflTransGen internalTheory initial final).mpr path)

theorem command_normal_iff (source : Pattern) :
    internalTheory.IsNormalForm source ↔
      commandTheory.IsNormalForm (atPattern stage source) :=
  command_cover.normal_iff source

theorem frontier_any_iff_diamond (test : Pattern → Bool) (source : Pattern) :
    (completeFrontier source).any test = true ↔
      gsltDiamond internalTheory (fun next => test next = true) source :=
  any_iff_diamond internalTheory completeFrontier frontier_qualified test source

theorem frontier_all_iff_forwardBox (test : Pattern → Bool) (source : Pattern) :
    (completeFrontier source).all test = true ↔
      derivedForwardBox (gsltSpan internalTheory) (fun next => test next = true) source :=
  all_iff_forwardBox internalTheory completeFrontier frontier_qualified test source

theorem frontier_nil_iff_normal (source : Pattern) :
    completeFrontier source = [] ↔ internalTheory.IsNormalForm source :=
  nil_iff_normal internalTheory completeFrontier frontier_qualified source

/-- The complete query retains the established atomic substitution invariant. -/
theorem frontier_atomic {depth : Nat} {source target : Pattern}
    (atomic : AtomicPi depth source) (member : target ∈ completeFrontier source) :
    AtomicPi depth target :=
  (frontier_qualified source target).mp member |>.atomic atomic

/-- A compiled restriction example runs through the actual authored command
rule with the bound-name endpoint preserved. -/
theorem restricted_command_runs :
    commandTheory.Step (atPattern stage ReflectionControls.restrictedExchange)
      (atPattern stage ReflectionControls.restrictedResult) := by
  apply command_cover.mapStep
  exact (frontier_qualified _ _).mp (by
    change ReflectionControls.restrictedResult ∈ piCalcReducts
      (piContextDepth ReflectionControls.restrictedExchange) ReflectionControls.restrictedExchange
    rw [ReflectionControls.complete_frontier_preserves_restricted_name.2]
    simp)

/-- A zero-depth sample cannot replace the qualified query, since its empty
frontier omits a checked internal firing. -/
theorem zero_depth_query_not_qualified :
    ¬ ∀ source target,
      target ∈ piCalcReducts 0 source ↔ internalTheory.Step source target := by
  intro qualified
  obtain ⟨empty, firing⟩ := ReflectionControls.zero_depth_misses_a_real_step
  have missed := (qualified _ _).mpr (piRawStep_of_step firing)
  rw [empty] at missed
  exact List.not_mem_nil missed

end Mettapedia.Languages.ProcessCalculi.PiCalculus.Bridges.GSLTIL
