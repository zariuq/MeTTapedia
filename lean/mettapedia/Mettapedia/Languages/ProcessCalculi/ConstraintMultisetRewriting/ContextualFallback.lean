import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualStandingEvents

/-!
# Resolved fallback retains a complete negative census at its entry cut

The source judgment requires every primary alternative to be disabled
before the fallback body runs. Compilation constructs a complete rejection
census in the terminating equation fragment, including real countermodels
for failed guards, and compiles the fallback's actual source clause. The
publication retains that census on its original input world.

The fallback's own equations cannot retroactively justify taking its branch.
Its effects may enable a primary after publication. Unfinished source jobs,
allocation refusal and errors are not completed negative observations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFallback

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualConjunctiveQueries ContextualStandingEvents

variable {S : Signature} {atom : S.Srt} {O Query : Type} {Γ : Ctx S}
    [DecidableEq O] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]
    {before : World S atom O Γ}
    (queries : Query → MetaArity (ContextualRuleCode.codeSignature S atom)) [DecidableEq Query]
    (alternatives : List (ContextualSourceCensus.Request before.locals before.current))
    (plan : ContextualPublication.Plan
      (Term (signature (ContextualRuleCode.codeSignature S atom)
        (queryFamily queries before.current.declarations)) Γ atom)) (picked : Selection O)

structure Admitted : Prop where
  no_primary : ∀ request ∈ alternatives, ¬ request.Enabled
  body : ContextualConditionalSourceAdmission.Admitted queries before.locals before.current.declarations
    picked plan.rule before.current.rows before.current.equations before.current.present

structure Compiled : Type 1 where
  census : letI := before.equality
    ContextualSourceCensus.EmptyCensus before.locals before.current
  alternatives : letI := before.equality
    census.alternatives = alternatives
  actual : Clause before queries inferInstance plan picked

namespace Compiled

variable {queries alternatives plan picked}

def publication (compiled : Compiled queries alternatives plan picked) : Publication before :=
  ⟨Query, queries, inferInstance, plan, picked, compiled.actual, some compiled.census⟩

def fuel (compiled : Compiled queries alternatives plan picked) : Nat := by
  letI := before.equality
  exact compiled.actual.firing.fuel

theorem source_admitted (compiled : Compiled queries alternatives plan picked) :
    Admitted queries alternatives plan picked := by
  let _ := before.equality
  refine ⟨?_, compiled.actual.source_admitted⟩
  intro request member
  exact compiled.census.no_primary request (compiled.alternatives.symm ▸ member)

theorem keeps_the_entry_census (compiled : Compiled queries alternatives plan picked) :
    compiled.publication.negative = some compiled.census := rfl

theorem physical_result (compiled : Compiled queries alternatives plan picked) :
    compiled.publication.target.current.present =
      (before.current.present \ picked.taken.toFinset) ∪ picked.made.toFinset := by
  let _ := before.equality
  exact compiled.actual.physical_result

end Compiled

theorem realize
    (patterned : ∀ request ∈ alternatives, ∀ chosen ∈ request.candidates,
      ContextualPatternFragment.ProblemPattern (request.information chosen))
    (source : Admitted queries alternatives plan picked) (fuel : Nat) :
    ∃ compiled : Compiled queries alternatives plan picked, compiled.fuel = fuel := by
  let _ := before.equality
  let census : ContextualSourceCensus.EmptyCensus before.locals before.current :=
    ⟨alternatives, fun request member => (request.certified_empty_iff (patterned request member)).mpr
      (source.no_primary request member)⟩
  obtain ⟨actual, budget⟩ := ContextualConditionalClauses.realize queries before.locals
    (before := before.current) plan picked source.body fuel
  exact ⟨⟨census, rfl, actual⟩, budget⟩

theorem source_iff_compiled
    (patterned : ∀ request ∈ alternatives, ∀ chosen ∈ request.candidates,
      ContextualPatternFragment.ProblemPattern (request.information chosen)) (fuel : Nat) :
    Admitted queries alternatives plan picked ↔
      ∃ compiled : Compiled queries alternatives plan picked, compiled.fuel = fuel :=
  ⟨fun source => realize queries alternatives plan picked patterned source fuel,
    fun ⟨compiled, _⟩ => compiled.source_admitted⟩

theorem an_enabled_primary_excludes_fallback (request : ContextualSourceCensus.Request before.locals before.current)
    (member : request ∈ alternatives) (enabled : request.Enabled) :
    ¬ Nonempty (Compiled queries alternatives plan picked) := by
  rintro ⟨compiled⟩
  exact compiled.source_admitted.no_primary request member enabled

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFallback
