import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualWorldClauseResults
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualWorldFrameComparison

/-!
# Actual compiler steps preserve the source-world comparison

The logical source update is compared first with the same update in the
represented world, then with the actual compiler target. The returned
query and exposed caller bindings provide the next environment. The
resulting comparison has exactly the same form as the input comparison.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualWorldComparison

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualConjunctiveQueries

variable {S : Signature} {Public Query Left Right O : Type}
    {exposed : Public → MetaArity S} {lefts : Left → MetaArity S} {rights : Right → MetaArity S}
    {Γ : Ctx S} {sort : S.Srt}
    [DecidableEq Query] [DecidableEq Left] [DecidableEq Right] [DecidableEq O]
    [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]
    {left : ContextualClauseSourceState.World lefts O Γ sort}
    {right : ContextualConditionalExecution.State rights O Γ sort}
    {leftEnv : Assignment exposed left.declarations} {rightEnv : Assignment exposed right.declarations}

def compilerResultEnv (queries : Query → MetaArity S)
    (plan : ContextualPublication.Plan (Term (signature S (queryFamily queries exposed)) Γ sort))
    (picked : Selection O)
    (compiled : ContextualConditionalClauses.Compiled queries rights (before := right)
      (preparedPlan queries rightEnv plan) picked) :
    Assignment (queryFamily queries exposed) compiled.firing.target.declarations :=
  Assignment.compose compiled.continuationEnv (ContextualStoredRows.liftCaptures queries rightEnv)

theorem Equivalent.compiled_step
    (equivalent : Equivalent left leftEnv (nativeWorld rights right) rightEnv)
    (queries : Query → MetaArity S)
    (plan : ContextualPublication.Plan (Term (signature S (queryFamily queries exposed)) Γ sort))
    (picked : Selection O)
    (admitted : ContextualClauseSourceState.Admitted queries lefts left (preparedPlan queries leftEnv plan) picked)
    (compiled : ContextualConditionalClauses.Compiled queries rights (before := right)
      (preparedPlan queries rightEnv plan) picked) :
    Equivalent (ContextualClauseSourceState.target queries lefts left (preparedPlan queries leftEnv plan) picked)
      (resultEnv queries lefts left.declarations leftEnv)
      (nativeWorld _ compiled.firing.target) (compilerResultEnv queries plan picked compiled) := by
  have source := equivalent.step queries plan picked admitted compiled.source_admitted
  have target := (actual_compiler_result (before := nativeWorld rights right) (occupied := right.occupied)
    compiled).restrict (ContextualStoredRows.liftCaptures queries rightEnv)
  exact source.trans target

theorem Equivalent.realize_step
    (equivalent : Equivalent left leftEnv (nativeWorld rights right) rightEnv)
    (queries : Query → MetaArity S)
    (plan : ContextualPublication.Plan (Term (signature S (queryFamily queries exposed)) Γ sort))
    (picked : Selection O)
    (admitted : ContextualClauseSourceState.Admitted queries lefts left (preparedPlan queries leftEnv plan) picked)
    (fuel : Nat) :
    ∃ compiled : ContextualConditionalClauses.Compiled queries rights (before := right)
        (preparedPlan queries rightEnv plan) picked,
      compiled.firing.fuel = fuel ∧
      Equivalent (ContextualClauseSourceState.target queries lefts left (preparedPlan queries leftEnv plan) picked)
        (resultEnv queries lefts left.declarations leftEnv)
        (nativeWorld _ compiled.firing.target) (compilerResultEnv queries plan picked compiled) := by
  have represented := admitted_forward equivalent queries picked plan.rule admitted
  obtain ⟨compiled, budget⟩ := ContextualConditionalClauses.realize queries rights (before := right)
    (preparedPlan queries rightEnv plan) picked represented fuel
  exact ⟨compiled, budget, equivalent.compiled_step queries plan picked admitted compiled⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualWorldComparison
