import Mettapedia.GSLT.LanguageDef.ContextualEffectTreeLanguage

/-!
# Exact execution of the authored effect-tree language

The generic contextual executor is compared with the independent ordered
world evaluator. The comparison retains every payload, private state, branch
trace and intent in order. A depth miss is operational non-admission, not a
refutation of a property of the program.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ContextualEffectTreeLanguage

open Mettapedia.GSLT.Dynamics.ContextualEffectHandlers
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution

private def layer (recursive : Pattern → List Pattern) (term : Pattern) : List Pattern :=
  language.rewrites.flatMap fun rewrite =>
    applyRuleUsing (engineBasePremises relationEnv) language recursive rewrite term

private theorem execute_succ (fuel : Nat) (term : Pattern) :
    execute (fuel + 1) term = layer (execute fuel) term := rfl

private theorem layer_pure (recursive : Pattern → List Pattern)
    (answer : Pattern) (state : Bool) (branch : BranchTrace) :
    layer recursive (request (.pure answer) state branch) =
      [completion (runWorldsAt (.pure answer) state branch)] := by
  simp +decide [layer, language, applyRuleUsing, premisesUsing,
    pureRewrite, chooseRewrite, readRewrite, writeRewrite, intentRewrite, rule,
    request, encodeProgram, purePattern, choosePattern, readPattern, writePattern,
    intentPattern, runPattern, donePattern, worldPattern, consPattern, nilPattern,
    metavariable, matchPatternForRule_eq_syntactic, applyBindingsForRule_eq_syntactic, applyRuleBindings,
    matchPattern, matchArgs, mergeBindings, applyBindings,
    completion, encodeWorlds, encodeWorld, encodeList, runWorldsAt]

private theorem layer_write (recursive : Pattern → List Pattern)
    (state nextState : Bool) (next : EffectProgram) (branch : BranchTrace)
    (worlds : Option (List EffectWorld))
    (returned : recursive (request next nextState branch) = worlds.toList.map completion) :
    layer recursive (request (.write nextState next) state branch) =
      worlds.toList.map completion := by
  cases worlds <;>
    simp +decide [layer, language, applyRuleUsing, premisesUsing, premiseStepUsing,
      pureRewrite, chooseRewrite, readRewrite, writeRewrite, intentRewrite, rule,
      request, encodeProgram, purePattern, choosePattern, readPattern, writePattern,
      intentPattern, runPattern, donePattern, worldPattern, consPattern, nilPattern,
      metavariable, matchPatternForRule_eq_syntactic, applyBindingsForRule_eq_syntactic, applyRuleBindings,
      matchPattern, matchArgs, mergeBindings, applyBindings, completion] at returned ⊢
  all_goals simp +decide [returned, matchPattern, matchArgs, mergeBindings]

private theorem layer_read (recursive : Pattern → List Pattern)
    (state : Bool) (next : Bool → EffectProgram) (branch : BranchTrace)
    (worlds : Option (List EffectWorld))
    (returned : recursive (request (next state) state branch) = worlds.toList.map completion) :
    layer recursive (request (.read next) state branch) = worlds.toList.map completion := by
  cases state <;> cases worlds <;>
    simp +decide [layer, language, applyRuleUsing, premisesUsing, premiseStepUsing,
      pureRewrite, chooseRewrite, readRewrite, writeRewrite, intentRewrite, rule,
      request, encodeProgram, purePattern, choosePattern, readPattern, writePattern,
      intentPattern, runPattern, donePattern, worldPattern, consPattern, nilPattern,
      metavariable, encodeBool, matchPatternForRule_eq_syntactic, applyBindingsForRule_eq_syntactic, applyRuleBindings,
      matchPattern, matchArgs, mergeBindings, applyBindings, completion] at returned ⊢
  all_goals simp +decide [returned, matchPattern, matchArgs, mergeBindings]

private theorem layer_intent (recursive : Pattern → List Pattern)
    (state : Bool) (intent : Pattern) (next : EffectProgram) (branch : BranchTrace)
    (worlds : Option (List EffectWorld))
    (returned : recursive (request next state branch) = worlds.toList.map completion) :
    layer recursive (request (.intent intent next) state branch) =
      (worlds.map (List.map (prefixIntent intent))).toList.map completion := by
  cases worlds <;>
    simp +decide [layer, language, applyRuleUsing, premisesUsing, premiseStepUsing,
      pureRewrite, chooseRewrite, readRewrite, writeRewrite, intentRewrite, rule,
      request, encodeProgram, purePattern, choosePattern, readPattern, writePattern,
      intentPattern, runPattern, donePattern, worldPattern, consPattern, nilPattern,
      metavariable, matchPatternForRule_eq_syntactic, applyBindingsForRule_eq_syntactic, applyRuleBindings,
      matchPattern, matchArgs, mergeBindings, applyBindings, completion] at returned ⊢
  all_goals
    simp +decide [returned, matchPattern, matchArgs, mergeBindings, engineBasePremises,
      premiseStepWithEnv, relationQueryStep, builtinRelationTuples, relationEnv,
      prefixRelation, matchRelationArgs, matchRelationArgument, Bindings.lookup,
      applyBindings, prefixIntents?_encodeWorlds]

private theorem layer_choose (recursive : Pattern → List Pattern)
    (state : Bool) (left right : EffectProgram) (branch : BranchTrace)
    (first second : Option (List EffectWorld))
    (returnedLeft : recursive (request left state (false :: branch)) =
      first.toList.map completion)
    (returnedRight : recursive (request right state (true :: branch)) =
      second.toList.map completion) :
    layer recursive (request (.choose left right) state branch) =
      (first.bind fun xs => second.map fun ys => xs ++ ys).toList.map completion := by
  cases first <;> cases second <;>
    simp +decide [layer, language, applyRuleUsing, premisesUsing, premiseStepUsing,
      pureRewrite, chooseRewrite, readRewrite, writeRewrite, intentRewrite, rule,
      request, encodeProgram, purePattern, choosePattern, readPattern, writePattern,
      intentPattern, runPattern, donePattern, worldPattern, consPattern, nilPattern,
      metavariable, matchPatternForRule_eq_syntactic, applyBindingsForRule_eq_syntactic, applyRuleBindings,
      matchPattern, matchArgs, mergeBindings, applyBindings, completion,
      encodeBranch, encodeList, encodeBool] at returnedLeft returnedRight ⊢
  all_goals
    simp +decide [returnedLeft, returnedRight, matchPattern, matchArgs, mergeBindings,
      engineBasePremises, premiseStepWithEnv, relationQueryStep, builtinRelationTuples,
      relationEnv, appendRelation, matchRelationArgs, matchRelationArgument,
      Bindings.lookup, applyBindings, appendLists?_encodeWorlds]

/-- At every depth, a compiled request either has no completion yet or has
the exact complete ordered world list. It never emits a partial prefix. -/
theorem executor_complete_or_empty (fuel : Nat) (program : EffectProgram)
    (state : Bool) (branch : BranchTrace) :
    execute fuel (request program state branch) = [] ∨
      execute fuel (request program state branch) =
        [completion (runWorldsAt program state branch)] := by
  induction fuel generalizing program state branch with
  | zero => exact Or.inl rfl
  | succ fuel ih =>
      rw [execute_succ]
      cases program with
      | pure answer => exact Or.inr (layer_pure _ answer state branch)
      | choose left right =>
          rcases ih left state (false :: branch) with first | first <;>
            rcases ih right state (true :: branch) with second | second
          · exact Or.inl (layer_choose _ state left right branch none none first second)
          · exact Or.inl (layer_choose _ state left right branch none
              (some (runWorldsAt right state (true :: branch))) first second)
          · exact Or.inl (layer_choose _ state left right branch
              (some (runWorldsAt left state (false :: branch))) none first second)
          · exact Or.inr (layer_choose _ state left right branch
              (some (runWorldsAt left state (false :: branch)))
              (some (runWorldsAt right state (true :: branch))) first second)
      | read next =>
          rcases ih (next state) state branch with returned | returned
          · exact Or.inl (layer_read _ state next branch none returned)
          · exact Or.inr (layer_read _ state next branch
              (some (runWorldsAt (next state) state branch)) returned)
      | write nextState next =>
          rcases ih next nextState branch with returned | returned
          · exact Or.inl (layer_write _ state nextState next branch none returned)
          · exact Or.inr (layer_write _ state nextState next branch
              (some (runWorldsAt next nextState branch)) returned)
      | intent intent next =>
          rcases ih next state branch with returned | returned
          · exact Or.inl (layer_intent _ state intent next branch none returned)
          · exact Or.inr (layer_intent _ state intent next branch
              (some (runWorldsAt next state branch)) returned)

/-- An arbitrary target pattern reached from a compiled request is the exact
completion, with no assumed target shape or decoder success. -/
theorem executor_no_invention (fuel : Nat) (program : EffectProgram)
    (state : Bool) (branch : BranchTrace) (target : Pattern)
    (returned : target ∈ execute fuel (request program state branch)) :
    target = completion (runWorldsAt program state branch) := by
  rcases executor_complete_or_empty fuel program state branch with empty | complete
  · rw [empty] at returned
    exact False.elim (List.not_mem_nil returned)
  · simpa only [complete, List.mem_singleton] using returned

/-- The structural depth bound suffices for exact execution. The singleton
contains the entire ordered result list, not one selected world. -/
theorem executor_exact (fuel : Nat) (program : EffectProgram)
    (state : Bool) (branch : BranchTrace) (adequate : depth program ≤ fuel) :
    execute fuel (request program state branch) =
      [completion (runWorldsAt program state branch)] := by
  induction fuel generalizing program state branch with
  | zero => have := depth_positive program; omega
  | succ fuel ih =>
      rw [execute_succ]
      cases program with
      | pure answer => exact layer_pure _ answer state branch
      | choose left right =>
          exact layer_choose _ state left right branch
            (some (runWorldsAt left state (false :: branch)))
            (some (runWorldsAt right state (true :: branch)))
            (ih left state (false :: branch) (by simp only [depth] at adequate; omega))
            (ih right state (true :: branch) (by simp only [depth] at adequate; omega))
      | read next =>
          apply layer_read _ state next branch (some (runWorldsAt (next state) state branch))
          apply ih
          cases state <;> simp only [depth] at adequate <;> omega
      | write nextState next =>
          exact layer_write _ state nextState next branch
            (some (runWorldsAt next nextState branch))
            (ih next nextState branch (by simp only [depth] at adequate; omega))
      | intent intent next =>
          exact layer_intent _ state intent next branch
            (some (runWorldsAt next state branch))
            (ih next state branch (by simp only [depth] at adequate; omega))

/-- The independently inductive authored relation admits exactly the source
completion. Its finite contextual witness is supplied by `depth`. -/
theorem step_request_iff (program : EffectProgram) (state : Bool)
    (branch : BranchTrace) (target : Pattern) :
    Step (engineBasePremises relationEnv) language (request program state branch) target ↔
      target = completion (runWorldsAt program state branch) := by
  rw [← exists_mem_rewriteAt_iff_step]
  constructor
  · rintro ⟨fuel, returned⟩
    exact executor_no_invention fuel program state branch target returned
  · rintro rfl
    refine ⟨depth program, ?_⟩
    change completion (runWorldsAt program state branch) ∈
      execute (depth program) (request program state branch)
    rw [executor_exact _ _ _ _ (Nat.le_refl _)]
    exact List.mem_singleton_self _

theorem theory_step_request_iff (program : EffectProgram) (state : Bool)
    (branch : BranchTrace) (target : Pattern) :
    theory.Step (request program state branch) target ↔
      target = completion (runWorldsAt program state branch) := by
  exact (EquationSemantics.stepModuloEquations_iff_step_of_no_generators
    language_equation_free _ _).trans (step_request_iff program state branch target)

/-- Completed worlds remain inert even when payloads contain executable-looking
syntax. There is no representation-wide contextual reduction rule. -/
theorem completion_inert (fuel : Nat) (worlds : List EffectWorld) :
    execute fuel (completion worlds) = [] := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
      simp +decide [execute, rewriteAt, language, applyRuleUsing,
        pureRewrite, chooseRewrite, readRewrite, writeRewrite, intentRewrite, rule,
        runPattern, donePattern, completion,
        matchPatternForRule_eq_syntactic, matchPattern]

/-! ## Independent behavioral controls -/

namespace Controls

/-- Equal answer values still occupy two ordered worlds with distinct branch
occurrences. The old trace is retained at both leaves. -/
theorem equal_answers_retained (answer : Pattern) (state : Bool) (branch : BranchTrace) :
    execute 2 (request (.choose (.pure answer) (.pure answer)) state branch) =
      [completion
        [⟨false :: branch, answer, state, []⟩,
         ⟨true :: branch, answer, state, []⟩]] :=
  executor_exact _ _ _ _ (by simp [depth])

def probe (answer : Pattern) : EffectProgram :=
  .read fun state => .intent (encodeBool state) (.pure answer)

def isolatedChoice (answer : Pattern) : EffectProgram :=
  .choose (.write true (probe answer)) (probe answer)

/-- The first branch's write affects its own read and intent, but cannot leak
into the sibling world. All internal effects are one declared completion
macrostep, with contextual depth five. -/
theorem nested_effects_single_macrostep (answer : Pattern) (branch : BranchTrace) :
    execute 5 (request (isolatedChoice answer) false branch) =
      [completion
        [⟨false :: branch, answer, true, [encodeBool true]⟩,
         ⟨true :: branch, answer, false, [encodeBool false]⟩]] ∧
    theory.Step (request (isolatedChoice answer) false branch)
      (completion
        [⟨false :: branch, answer, true, [encodeBool true]⟩,
         ⟨true :: branch, answer, false, [encodeBool false]⟩]) := by
  exact ⟨executor_exact _ _ _ _ (by simp [depth, isolatedChoice, probe]),
    (theory_step_request_iff _ _ _ _).mpr rfl⟩

/-- Replacing private alternatives with left-to-right shared-state execution
would invent this second world. The authored backend rejects it. -/
theorem shared_state_leak_rejected (answer : Pattern) (branch : BranchTrace) :
    ¬ theory.Step (request (isolatedChoice answer) false branch)
      (completion
        [⟨false :: branch, answer, true, [encodeBool true]⟩,
         ⟨true :: branch, answer, true, [encodeBool true]⟩]) := by
  rw [theory_step_request_iff]
  intro equal
  have worlds := completion_injective equal
  have states := congrArg (List.map WorldResult.state) worlds
  simp [isolatedChoice, probe, runWorldsAt] at states

def opaqueAnswer : Pattern := .subst (.bvar 0) (.fvar "worlds")

/-- Payload metavariables and explicit substitution nodes are literal data,
including names also used by the implementation's rule schemas. -/
theorem opaque_payloads_untouched :
    execute 2 (request (.intent (.fvar "prefixed") (.pure opaqueAnswer)) false []) =
      [completion [⟨[], opaqueAnswer, false, [.fvar "prefixed"]⟩]] :=
  executor_exact _ _ _ _ (by decide)

/-- A shallow miss becomes an exact completion at the next sufficient depth;
it is not a countermodel or an empty completed answer list. -/
theorem depth_miss_then_completion (answer : Pattern) :
    execute 1 (request (.write true (.pure answer)) false []) = [] ∧
    execute 2 (request (.write true (.pure answer)) false []) =
      [completion [⟨[], answer, true, []⟩]] := by
  constructor
  · rw [execute_succ]
    exact layer_write _ false true (.pure answer) [] none rfl
  · exact executor_exact _ _ _ _ (by simp [depth])

theorem malformed_program_inert (fuel : Nat) (answer : Pattern) :
    execute fuel (runPattern (.apply "effect-pure" [answer, answer])
      (encodeBool false) (encodeBranch [])) = [] := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
      simp +decide [execute, rewriteAt, language, applyRuleUsing,
        pureRewrite, chooseRewrite, readRewrite, writeRewrite, intentRewrite, rule,
        runPattern, purePattern, choosePattern, readPattern, writePattern, intentPattern,
        matchPatternForRule_eq_syntactic, matchPattern, matchArgs]

/-- A genuinely added authored rule, not an alternative definition of the
reference relation. It fabricates empty completions for arbitrary requests. -/
def inventedEmptyRewrite : RewriteRule :=
  rule "effect-invent-empty" ["program", "state", "branch"] []
    (runPattern (metavariable "program") (metavariable "state") (metavariable "branch"))
    (donePattern nilPattern)

def enlargedLanguage : LanguageDef :=
  { language with rewrites := inventedEmptyRewrite :: language.rewrites }

theorem enlargement_preserves_steps {source target : Pattern}
    (step : Step (engineBasePremises relationEnv) language source target) :
    Step (engineBasePremises relationEnv) enlargedLanguage source target :=
  step.mono_rules (fun _ member => List.mem_cons_of_mem _ member)

theorem enlargement_invents_completion (program : EffectProgram)
    (state : Bool) (branch : BranchTrace) :
    Step (engineBasePremises relationEnv) enlargedLanguage
      (request program state branch) (completion []) := by
  apply exists_mem_rewriteAt_iff_step.mp
  refine ⟨1, ?_⟩
  simp only [rewriteAt, List.mem_flatMap]
  refine ⟨inventedEmptyRewrite, List.mem_cons_self, ?_⟩
  simp +decide [applyRuleUsing, premisesUsing, inventedEmptyRewrite, rule,
    request, completion, encodeWorlds, encodeList,
    runPattern, donePattern, metavariable,
    matchPatternForRule_eq_syntactic, applyBindingsForRule_eq_syntactic, applyRuleBindings,
    matchPattern, matchArgs, mergeBindings, nilPattern]

/-- Forward preservation survives the added rule, but exact realization does
not: the new completion is absent from the actual source semantics. -/
theorem preservation_does_not_imply_no_invention (answer : Pattern) :
    (∀ source target,
      Step (engineBasePremises relationEnv) language source target →
        Step (engineBasePremises relationEnv) enlargedLanguage source target) ∧
    Step (engineBasePremises relationEnv) enlargedLanguage
      (request (.pure answer) false []) (completion []) ∧
    ¬ Step (engineBasePremises relationEnv) language
      (request (.pure answer) false []) (completion []) := by
  refine ⟨fun _ _ => enlargement_preserves_steps,
    enlargement_invents_completion _ _ _, ?_⟩
  rw [step_request_iff]
  intro equal
  have impossible := completion_injective equal
  cases impossible

end Controls

#print axioms executor_complete_or_empty
#print axioms executor_no_invention
#print axioms executor_exact
#print axioms step_request_iff
#print axioms theory_step_request_iff
#print axioms completion_inert
#print axioms Controls.nested_effects_single_macrostep
#print axioms Controls.shared_state_leak_rejected
#print axioms Controls.opaque_payloads_untouched
#print axioms Controls.depth_miss_then_completion
#print axioms Controls.malformed_program_inert
#print axioms Controls.preservation_does_not_imply_no_invention

end Mettapedia.GSLT.LanguageDef.ContextualEffectTreeLanguage
