import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualWorldCompilerSteps

/-!
# Finite authored clause sequences and their independent execution relations

A clause sequence retains the old exposed environment and introduces its
query names for the continuation. Source execution uses the independent
world update. Native execution uses actual solver-backed compiler firings.
Both record the same ordered physical selections and observe the final
returned contextual value with its remaining information.

These sequences are a resolved finite program fragment. They introduce no
textual scope policy, evaluator callback, search-order default or recursion
semantics.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualClauseSequences

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualConjunctiveQueries ContextualWorldComparison

inductive Sequence (S : Signature) (context : Ctx S) (sort : S.Srt) :
    {Public : Type} → (Public → MetaArity S) → Type 1 where
  | finish {Public : Type} {exposed : Public → MetaArity S}
      (value : Term (signature S exposed) context sort) : Sequence S context sort exposed
  | clause {Public Query : Type} {exposed : Public → MetaArity S}
      (queries : Query → MetaArity S) (queryEquality : DecidableEq Query)
      (plan : ContextualPublication.Plan (Term (signature S (queryFamily queries exposed)) context sort))
      (next : Sequence S context sort (queryFamily queries exposed)) : Sequence S context sort exposed

inductive SourceRun (S : Signature) (O : Type) [DecidableEq O] (context : Ctx S) (sort : S.Srt)
    {Output : Type} (outputs : Output → MetaArity S) (pattern : Term (signature S outputs) context sort) :
    {Public Local : Type} → {exposed : Public → MetaArity S} → {locals : Local → MetaArity S} →
      (world : ContextualClauseSourceState.World locals O context sort) → Assignment exposed world.declarations →
      Sequence S context sort exposed → List (Selection O) → Prop where
  | finish {Public Local : Type} {exposed : Public → MetaArity S} {locals : Local → MetaArity S}
      (world : ContextualClauseSourceState.World locals O context sort) (environment : Assignment exposed world.declarations)
      (value : Term (signature S exposed) context sort)
      (answer : ContextualPublication.SourceInstances world.equations (instantiate environment value) outputs pattern) :
      SourceRun S O context sort outputs pattern world environment (.finish value) []
  | clause {Public Local Query : Type} {exposed : Public → MetaArity S} {locals : Local → MetaArity S}
      [localEquality : DecidableEq Local] [queryEquality : DecidableEq Query]
      (world : ContextualClauseSourceState.World locals O context sort) (environment : Assignment exposed world.declarations)
      (queries : Query → MetaArity S)
      (plan : ContextualPublication.Plan (Term (signature S (queryFamily queries exposed)) context sort))
      (next : Sequence S context sort (queryFamily queries exposed)) (picked : Selection O) (trace : List (Selection O))
      (admitted : ContextualClauseSourceState.Admitted queries locals world (preparedPlan queries environment plan) picked)
      (tail : SourceRun S O context sort outputs pattern
        (ContextualClauseSourceState.target queries locals world (preparedPlan queries environment plan) picked)
        (resultEnv queries locals world.declarations environment) next trace) :
      SourceRun S O context sort outputs pattern world environment (.clause queries queryEquality plan next) (picked :: trace)

inductive NativeRun (S : Signature) (O : Type) [DecidableEq O] (context : Ctx S) (sort : S.Srt)
    [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]
    {Output : Type} (outputs : Output → MetaArity S) (pattern : Term (signature S outputs) context sort) :
    {Public Local : Type} → {exposed : Public → MetaArity S} → {locals : Local → MetaArity S} →
      (world : ContextualConditionalExecution.State locals O context sort) → Assignment exposed world.declarations →
      Sequence S context sort exposed → List (Selection O) → Prop where
  | finish {Public Local : Type} {exposed : Public → MetaArity S} {locals : Local → MetaArity S}
      (world : ContextualConditionalExecution.State locals O context sort) (environment : Assignment exposed world.declarations)
      (value : Term (signature S exposed) context sort)
      (answer : ContextualPublication.SourceInstances world.equations (instantiate environment value) outputs pattern) :
      NativeRun S O context sort outputs pattern world environment (.finish value) []
  | clause {Public Local Query : Type} {exposed : Public → MetaArity S} {locals : Local → MetaArity S}
      [localEquality : DecidableEq Local] [queryEquality : DecidableEq Query]
      (world : ContextualConditionalExecution.State locals O context sort) (environment : Assignment exposed world.declarations)
      (queries : Query → MetaArity S)
      (plan : ContextualPublication.Plan (Term (signature S (queryFamily queries exposed)) context sort))
      (next : Sequence S context sort (queryFamily queries exposed)) (picked : Selection O) (trace : List (Selection O))
      (compiled : ContextualConditionalClauses.Compiled queries locals (before := world)
        (preparedPlan queries environment plan) picked)
      (tail : NativeRun S O context sort outputs pattern compiled.firing.target
        (compilerResultEnv queries plan picked compiled) next trace) :
      NativeRun S O context sort outputs pattern world environment (.clause queries queryEquality plan next) (picked :: trace)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualClauseSequences
