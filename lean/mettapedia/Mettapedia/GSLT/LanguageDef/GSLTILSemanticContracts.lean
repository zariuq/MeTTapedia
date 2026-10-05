import Mettapedia.GSLT.Core.IndexedCommandBlocks
import Mettapedia.GSLT.LanguageDef.GSLTILFibreExecution
import Mettapedia.OSLF.Framework.SuccessorFrontier

/-!
# Execution and observation contracts for authored GSLT commands

The existing command LanguageDef generates a GSLT under its chosen relation
environment. Its root executor is already proved adequate for that authored
step relation. The shared frontier lemmas therefore give exact Boolean
diamond, forward-box and quiescence observations of the same GSLT.

On a qualified guest fibre the Boolean diamond also agrees with the guest's
own step relation through its encoding. The encoding and query remain
explicit; choosing a relation environment supplies no independent guest or
native implementation correctness proof.

The imported completed-block comparison supplies the categorical contract for
the functional indexed fragment. Relational routes, contexts and occurrence
observations retain their existing separate contracts.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.GSLTIL.SemanticContracts

open Mettapedia.GSLT
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.OSLF.Framework.DerivedModalities
open Mettapedia.OSLF.Framework.SuccessorFrontier

/-- The existing root executor, with the same authored command rules and
relation environment as its generated GSLT. -/
abbrev executorFrontier (relations : RelationEnv) (state : Pattern) :=
  rewriteStepWithPremisesUsing relations language state

/-- Every reported root successor is an authored step, and every authored
step is reported. -/
theorem executor_qualified (relations : RelationEnv) (state next : Pattern) :
    next ∈ executorFrontier relations state ↔
      (executionTheory relations).Step state next :=
  (executionTheory_step_iff_mem_executor relations state next).symm

/-- Existential frontier observation is exactly the generated GSLT diamond. -/
theorem executor_any_iff_diamond (relations : RelationEnv)
    (test : Pattern → Bool) (state : Pattern) :
    (executorFrontier relations state).any test = true ↔
      gsltDiamond (executionTheory relations) (fun next => test next = true) state :=
  any_iff_diamond (executionTheory relations) (executorFrontier relations)
    (executor_qualified relations) test state

/-- Universal frontier observation uses the forward box of the same GSLT. -/
theorem executor_all_iff_forwardBox (relations : RelationEnv)
    (test : Pattern → Bool) (state : Pattern) :
    (executorFrontier relations state).all test = true ↔
      derivedForwardBox (gsltSpan (executionTheory relations))
        (fun next => test next = true) state :=
  all_iff_forwardBox (executionTheory relations) (executorFrontier relations)
    (executor_qualified relations) test state

/-- Complete executor exhaustion means an actual normal form. -/
theorem executor_nil_iff_normal (relations : RelationEnv) (state : Pattern) :
    executorFrontier relations state = [] ↔
      (executionTheory relations).IsNormalForm state :=
  nil_iff_normal (executionTheory relations) (executorFrontier relations)
    (executor_qualified relations) state

/-- A guest query's diamond commutes with its qualified encoding. The
encoding may identify states; query qualification still forbids spurious
observations and missing successors. -/
theorem guest_query_any_iff_diamond (source : GSLT)
    (encode : source.Term → Pattern) (successors : Pattern → List Pattern)
    (qualified : ∀ state answer, answer ∈ successors (encode state) ↔
      ∃ next, source.Step state next ∧ answer = encode next)
    (test : Pattern → Bool) (state : source.Term) :
    (successors (encode state)).any test = true ↔
      gsltDiamond source (fun next => test (encode next) = true) state := by
  rw [List.any_eq_true, gsltDiamond_spec]
  constructor
  · rintro ⟨answer, member, satisfied⟩
    obtain ⟨next, step, same⟩ := (qualified state answer).mp member
    exact ⟨next, step, same ▸ satisfied⟩
  · rintro ⟨next, step, satisfied⟩
    exact ⟨encode next, (qualified state (encode next)).mpr ⟨next, step, rfl⟩,
      satisfied⟩

/-- Universal successor observation also commutes with a qualified guest
encoding, using the forward box rather than the predecessor modality. -/
theorem guest_query_all_iff_forwardBox (source : GSLT)
    (encode : source.Term → Pattern) (successors : Pattern → List Pattern)
    (qualified : ∀ state answer, answer ∈ successors (encode state) ↔
      ∃ next, source.Step state next ∧ answer = encode next)
    (test : Pattern → Bool) (state : source.Term) :
    (successors (encode state)).all test = true ↔
      derivedForwardBox (gsltSpan source)
        (fun next => test (encode next) = true) state := by
  rw [List.all_eq_true]
  simp only [derivedForwardBox, ui, pb, Function.comp, gsltSpan]
  constructor
  · intro universal ⟨origin, next, step⟩ same
    change origin = state at same
    subst origin
    exact universal (encode next)
      ((qualified state (encode next)).mpr ⟨next, step, rfl⟩)
  · intro universal answer member
    obtain ⟨next, step, same⟩ := (qualified state answer).mp member
    exact same.symm ▸ universal ⟨state, next, step⟩ rfl

namespace Controls

private def atom (name : String) : Pattern := .apply name []
private def stage : Pattern := atom "frontier-control"
private def ready : Pattern := atom "ready"
private def done : Pattern := atom "done"
private def query (state : Pattern) : List Pattern := if state = ready then [done] else []

/-- An actual execution of the authored at rule has the promised diamond. -/
theorem authored_command_diamond :
    gsltDiamond (FibreExecution.theory stage query)
      (fun result => result = atPattern stage done) (atPattern stage ready) := by
  apply (gsltDiamond_spec (FibreExecution.theory stage query) _ _).mpr
  refine ⟨atPattern stage done, ?_, rfl⟩
  apply (FibreExecution.step_at_iff stage query ready _).mpr
  exact ⟨done, by simp [query], rfl⟩

/-- A query registered at one stage supplies no execution at another stage. -/
theorem unsupported_stage_normal :
    (FibreExecution.theory stage query).IsNormalForm
      (atPattern (atom "unsupported") ready) :=
  FibreExecution.other_stage_normal stage (atom "unsupported") query
    (by simp [stage, atom]) ready

end Controls

end Mettapedia.GSLT.LanguageDef.GSLTIL.SemanticContracts
