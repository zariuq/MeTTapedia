import Mettapedia.GSLT.Compilation.RootRewritesUnderGrowth
import Mettapedia.GSLT.Compilation.Uniform.ExecutableQueryRules

/-!
# Executable firings in a growing presentation

When a presentation grows by adding rules, any finite run in the colimit can
be executed at one stage. At that stage the executable compilation of the
whole presentation gives exactly the source endpoints. The stage and bound
can depend on the run.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Compilation.Uniform.ExecutableGrowth

open _root_.CategoryTheory
open scoped _root_.CategoryTheory
open Mettapedia.OSLF.MeTTaIL.Syntax (LanguageDef Pattern RewriteRule)
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ComputedConditions
open Mettapedia.GSLT.IndexedOperational.OperationalColimits (inject multiStep_from_stage_iff)
open RootRewritesOnTheStep (sourceSystem)
open RootRewritesUnderGrowth (growing inject_eq_iff)

private theorem path_iff (theory : GSLT) {source target : theory.Term} :
    theory.MultiStep source target ↔ Nonempty (theory.RewritePath source target) := by
  constructor
  · intro run
    induction run with
    | refl state => exact ⟨.nil state⟩
    | step first _ ih =>
        obtain ⟨rest⟩ := ih
        exact ⟨.cons first rest⟩
  · rintro ⟨path⟩
    induction path with
    | nil state => exact .refl state
    | cons first _ ih => exact .step first ih

variable {relEnv : RelationEnv} {stage : ℕ → LanguageDef}
  {grows : ∀ {first later}, first ≤ later → ∀ rule : RewriteRule,
    rule ∈ (stage first).rewrites → rule ∈ (stage later).rewrites}

/-- Colimit reachability agrees with finite execution at a stage of the
growing presentation. The theorem concerns growth of authored rules with a
fixed built-in relations and a carrier valid at each stage. -/
theorem reachable_iff_executable_stage {input : String → ℕ → Bool}
    {schemas : ℕ → List Executable.Schema}
    (compiled : ∀ index, ExecutableQueryRules.compile input (stage index) = .ok (schemas index))
    (moded : ∀ index, QueryPremises.Moded relEnv (stage index) input)
    (dataRows : ∀ index, QueryPremises.DataRows relEnv (stage index))
    {carrier : Pattern → Prop}
    (carried : ∀ index, QueryRulesOnTheStep.DataCarrier relEnv (stage index) carrier)
    {source : Pattern} (valid : carrier source) (target : Pattern) :
    (Mettapedia.GSLT.IndexedOperational.OperationalColimits.theory (growing relEnv stage grows)).MultiStep
        (inject (growing relEnv stage grows) 0 source) (inject (growing relEnv stage grows) 0 target) ↔
      ∃ index steps, target ∈ ExecutableQueryRules.frontier relEnv (stage index) (schemas index) steps source := by
  refine (multiStep_from_stage_iff (growing relEnv stage grows)
    (site := 0) source (inject (growing relEnv stage grows) 0 target)).trans ?_
  constructor
  · rintro ⟨index, _, after, sourceRun, same⟩
    have reaches : after = target := (inject_eq_iff (grows := grows) index after target).mp same
    subst after
    obtain ⟨path⟩ := (path_iff (sourceSystem relEnv (stage index))).mp sourceRun
    exact ⟨index, path.length, (ExecutableQueryRules.mem_frontier (moded index) (dataRows index)
      (carried index) (compiled index) path.length valid target).mpr ⟨path, rfl⟩⟩
  · rintro ⟨index, steps, finished⟩
    obtain ⟨path, _⟩ := (ExecutableQueryRules.mem_frontier (moded index) (dataRows index) (carried index)
      (compiled index) steps valid target).mp finished
    exact ⟨index, homOfLE (Nat.zero_le index), target,
      (path_iff (sourceSystem relEnv (stage index))).mpr ⟨path⟩,
      (inject_eq_iff (grows := grows) index target target).mpr rfl⟩

#print axioms reachable_iff_executable_stage

end Mettapedia.GSLT.Compilation.Uniform.ExecutableGrowth
