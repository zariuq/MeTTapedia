import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualClauseSequences

/-!
# Finite clause programs agree with actual native solver histories

The comparison preserves every authored clause, its ordered physical
selection trace and its final returned contextual value. Each native
step is an actual compiled firing. No complete source evaluator appears
inside a rule or in the native execution relation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualWorldComparison

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualGuardMatching

variable {S : Signature} {Public Left Right O Next : Type}
    {exposed : Public → MetaArity S} {lefts : Left → MetaArity S} {rights : Right → MetaArity S}
    {Γ : Ctx S} {sort : S.Srt}
    {left : ContextualClauseSourceState.World lefts O Γ sort}
    {right : ContextualClauseSourceState.World rights O Γ sort}
    {leftEnv : Assignment exposed left.declarations} {rightEnv : Assignment exposed right.declarations}
    {next : Next → MetaArity S}

theorem Equivalent.forward_instances (equivalent : Equivalent left leftEnv right rightEnv)
    (value : Term (signature S exposed) Γ sort) (pattern : Term (signature S next) Γ sort) :
    ContextualPublication.SourceInstances left.equations (instantiate leftEnv value) next pattern →
      ContextualPublication.SourceInstances right.equations (instantiate rightEnv value) next pattern := by
  rintro ⟨earlier, candidate, model, same⟩
  obtain ⟨later, other, related⟩ := equivalent.forward _ earlier.declarations candidate model
  refine ⟨earlier.trans later, other, related.right_model, ?_⟩
  have values : instantiate other (instantiate rightEnv value) =
      instantiate later.assignment (instantiate candidate (instantiate leftEnv value)) := by
    rw [← Assignment.instantiate_compose, ← related.bindings,
      ← Assignment.compose_associative, Assignment.instantiate_compose, Assignment.instantiate_compose]
  erw [Extension.trans_assignment, Assignment.instantiate_compose]
  exact values.trans (congrArg (instantiate later.assignment) same)

theorem Equivalent.value_instances (equivalent : Equivalent left leftEnv right rightEnv)
    (value : Term (signature S exposed) Γ sort) (pattern : Term (signature S next) Γ sort) :
    ContextualPublication.SourceInstances right.equations (instantiate rightEnv value) next pattern ↔
      ContextualPublication.SourceInstances left.equations (instantiate leftEnv value) next pattern :=
  ⟨equivalent.symm.forward_instances value pattern, equivalent.forward_instances value pattern⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualWorldComparison

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualClauseSequences

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualWorldComparison

variable {S : Signature} {O : Type} [DecidableEq O] {Γ : Ctx S} {sort : S.Srt}
    [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]
    {Output : Type} {outputs : Output → MetaArity S} {pattern : Term (signature S outputs) Γ sort}
    {Public Local : Type} {exposed : Public → MetaArity S} {locals : Local → MetaArity S}
    {sequence : Sequence S Γ sort exposed} {trace : List (Selection O)}

theorem SourceRun.to_native {world : ContextualClauseSourceState.World locals O Γ sort}
    {environment : Assignment exposed world.declarations}
    (run : SourceRun S O Γ sort outputs pattern world environment sequence trace) (fuel : Nat) :
    ∀ {Right : Type} {rights : Right → MetaArity S} [DecidableEq Right]
      (represented : ContextualConditionalExecution.State rights O Γ sort)
      (representedEnv : Assignment exposed represented.declarations),
      Equivalent world environment (nativeWorld rights represented) representedEnv →
        NativeRun S O Γ sort outputs pattern represented representedEnv sequence trace := by
  induction run with
  | finish world environment value answer =>
      intro Right rights rightEquality represented representedEnv equivalent
      exact NativeRun.finish represented representedEnv value ((equivalent.value_instances value pattern).mpr answer)
  | clause world environment queries plan next picked trace admitted tail ih =>
      intro Right rights rightEquality represented representedEnv equivalent
      obtain ⟨compiled, _, after⟩ := equivalent.realize_step queries plan picked admitted fuel
      let _ := compiled.firing.update.equality
      exact NativeRun.clause represented representedEnv queries plan next picked trace compiled
        (ih compiled.firing.target (compilerResultEnv queries plan picked compiled) after)

theorem NativeRun.to_source {represented : ContextualConditionalExecution.State locals O Γ sort}
    {representedEnv : Assignment exposed represented.declarations}
    (run : NativeRun S O Γ sort outputs pattern represented representedEnv sequence trace) :
    ∀ {Left : Type} {lefts : Left → MetaArity S} [DecidableEq Left]
      (world : ContextualClauseSourceState.World lefts O Γ sort)
      (environment : Assignment exposed world.declarations),
      Equivalent world environment (nativeWorld locals represented) representedEnv →
        SourceRun S O Γ sort outputs pattern world environment sequence trace := by
  induction run with
  | finish represented representedEnv value answer =>
      intro Left lefts leftEquality world environment equivalent
      exact SourceRun.finish world environment value ((equivalent.value_instances value pattern).mp answer)
  | clause represented representedEnv queries plan next picked trace compiled tail ih =>
      intro Left lefts leftEquality world environment equivalent
      have admitted := (admitted_iff equivalent queries picked plan.rule).mp compiled.source_admitted
      have after := equivalent.compiled_step queries plan picked admitted compiled
      let _ := world.equality
      exact SourceRun.clause world environment queries plan next picked trace admitted
        (ih (ContextualClauseSourceState.target queries lefts world (preparedPlan queries environment plan) picked)
          (resultEnv queries lefts world.declarations environment) after)

theorem source_iff_native {Left Right : Type} {lefts : Left → MetaArity S} {rights : Right → MetaArity S}
    [DecidableEq Left] [DecidableEq Right]
    (world : ContextualClauseSourceState.World lefts O Γ sort) (environment : Assignment exposed world.declarations)
    (represented : ContextualConditionalExecution.State rights O Γ sort)
    (representedEnv : Assignment exposed represented.declarations)
    (equivalent : Equivalent world environment (nativeWorld rights represented) representedEnv) :
    SourceRun S O Γ sort outputs pattern world environment sequence trace ↔
      NativeRun S O Γ sort outputs pattern represented representedEnv sequence trace :=
  ⟨fun run => run.to_native 1 represented representedEnv equivalent,
    fun run => run.to_source world environment equivalent⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualClauseSequences
