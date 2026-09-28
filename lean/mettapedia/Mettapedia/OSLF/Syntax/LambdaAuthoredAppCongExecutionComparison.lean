import Mettapedia.OSLF.Syntax.LambdaAuthoredFullRuleProfile
import Mettapedia.GSLT.LanguageDef.TypedRootPremiseAssignment

/-!
# Authored application congruence and intrinsic lambda terms

The two application congruence declarations are checked against the actual
scoped matcher and ordered premise interpreter. Their premise outputs retain
the caller's ambient context, and distinct oracle occurrences remain distinct.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.LambdaAuthoredAppCongExecutionComparison

open Mettapedia.OSLF.Binding.LambdaContextualRung
open Mettapedia.OSLF.Binding.LambdaScopedAuthoringComparison
open Mettapedia.OSLF.Binding.LambdaPatternRendering
open Mettapedia.OSLF.Binding.LambdaAuthoredFullRuleProfile
open Mettapedia.OSLF.Binding.LambdaRuleDerivationPolynomial
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.RuleBinding
open Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching
open Mettapedia.OSLF.MeTTaIL.ScopedPremiseExecution
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.GSLT.Examples.ScopedLamCongExecution (betaRule lamCongRule)

private def rootValue {Γ : Ctx sig} (t : Term sig Γ .term) : ContextualValue :=
  { dependencies := [], ambient := Γ.length, body := encodeTerm t }

private theorem recover_root {Γ : Ctx sig} (t : Term sig Γ .term) :
    recoverValue? [] Γ.length 0 [] (encodeTerm t) =
      some (rootValue t) := by
  simpa [rootValue] using
    (Mettapedia.GSLT.LanguageDef.RestAwareTyping.recoverValue?_root_empty
      Γ.length (encodeTerm t) (encodeTerm_scoped t))

private theorem instantiate_root {Γ : Ctx sig} (t : Term sig Γ .term) :
    instantiateValue? (rootValue t) Γ.length 0 [] =
      some (encodeTerm t) := by
  exact recoverValue?_forward [] Γ.length 0 [] (encodeTerm t) _
    (recover_root t)

private def captured {Γ : Ctx sig}
    (function argument : Term sig Γ .term) : Assignment :=
  [("A", rootValue argument), ("F", rootValue function)]

private def completedL {Γ : Ctx sig}
    (function argument target : Term sig Γ .term) : Assignment :=
  ("G", rootValue target) :: captured function argument

private def completedR {Γ : Ctx sig}
    (function argument target : Term sig Γ .term) : Assignment :=
  ("B", rootValue target) :: captured function argument

private theorem left_arguments :
    arguments? appCongLRule appCongLSpec "F" .left [0] = some [] := by
  decide +kernel

private theorem right_arguments :
    arguments? appCongRRule appCongRSpec "A" .left [1] = some [] := by
  decide +kernel

private theorem source_argumentsL :
    arguments? appCongLRule appCongLSpec "F" (.premise 0 0 0) [] =
      some [] := by
  decide +kernel

private theorem source_argumentsR :
    arguments? appCongRRule appCongRSpec "A" (.premise 0 0 0) [] =
      some [] := by
  decide +kernel

private theorem target_argumentsL :
    arguments? appCongLRule appCongLSpec "G" (.premise 0 0 1) [] =
      some [] := by
  decide +kernel

private theorem target_argumentsR :
    arguments? appCongRRule appCongRSpec "B" (.premise 0 0 1) [] =
      some [] := by
  decide +kernel

/-- Both application rules recover the function and argument in the original
ambient context; the second capture is prepended to the assignment. -/
theorem appL_match {Γ : Ctx sig}
    (function argument : Term sig Γ .term) :
    matchRuleAt appCongLRule appCongLSpec Γ.length
      (encodeTerm (appT function argument)) =
      [captured function argument] := by
  simp [matchRuleAt, appCongLRule, matchAt, matchArgsAt,
    appT, encodeTerm, encodeArgs, wrapBinders, capture?, assign, lookup,
    captured, appCongLSpec, arguments?, dependencies?, occurrenceDeclared,
    sitePattern?, occurrenceAt?, recover_root, rootValue]

theorem appR_match {Γ : Ctx sig}
    (function argument : Term sig Γ .term) :
    matchRuleAt appCongRRule appCongRSpec Γ.length
      (encodeTerm (appT function argument)) =
      [captured function argument] := by
  simp [matchRuleAt, appCongRRule, matchAt, matchArgsAt,
    appT, encodeTerm, encodeArgs, wrapBinders, capture?, assign, lookup,
    captured, appCongRSpec, arguments?, dependencies?, occurrenceDeclared,
    sitePattern?, occurrenceAt?, recover_root, rootValue]

/-- The left rule asks for the function step in the caller's context. -/
theorem appL_source {Γ : Ctx sig}
    (function argument : Term sig Γ .term) :
    instantiateAt? appCongLRule appCongLSpec Γ.length
      (.premise 0 0 0) [] 0 (captured function argument)
      appCongLStep.source = some (encodeTerm function) := by
  simp [instantiateAt?, appCongLStep, captured, lookup,
    source_argumentsL, instantiate_root]

/-- The right rule asks for the argument step in the caller's context. -/
theorem appR_source {Γ : Ctx sig}
    (function argument : Term sig Γ .term) :
    instantiateAt? appCongRRule appCongRSpec Γ.length
      (.premise 0 0 0) [] 0 (captured function argument)
      appCongRStep.source = some (encodeTerm argument) := by
  simp [instantiateAt?, appCongRStep, captured, lookup,
    source_argumentsR, instantiate_root]

/-- A selected function target adds a new root value without changing the
function and argument captured from the source. -/
theorem appL_target {Γ : Ctx sig}
    (function argument target : Term sig Γ .term) :
    matchAt appCongLRule appCongLSpec Γ.length
      (.premise 0 0 1) [] 0 (captured function argument)
      appCongLStep.target (encodeTerm target) =
      [completedL function argument target] := by
  have hdeps : dependencies? appCongLSpec "G" = some [] := by
    decide +kernel
  simp [appCongLStep, matchAt, capture?, hdeps,
    target_argumentsL, recover_root, assign, lookup,
    completedL, captured]

theorem appR_target {Γ : Ctx sig}
    (function argument target : Term sig Γ .term) :
    matchAt appCongRRule appCongRSpec Γ.length
      (.premise 0 0 1) [] 0 (captured function argument)
      appCongRStep.target (encodeTerm target) =
      [completedR function argument target] := by
  have hdeps : dependencies? appCongRSpec "B" = some [] := by
    decide +kernel
  simp [appCongRStep, matchAt, capture?, hdeps,
    target_argumentsR, recover_root, assign, lookup,
    completedR, captured]

/-- The two authored right sides reconstruct the corresponding intrinsic
application, including all ambient variables. -/
theorem appL_reduct {Γ : Ctx sig}
    (function argument target : Term sig Γ .term) :
    reduct? appCongLRule appCongLSpec Γ.length
      (completedL function argument target) =
      some (encodeTerm (appT target argument)) := by
  simp [reduct?, instantiateAt?, instantiateArgsAt?,
    appCongLRule, appCongLSpec, arguments?, dependencies?,
    occurrenceDeclared, sitePattern?, occurrenceAt?,
    completedL, captured, lookup, instantiate_root,
    appT, encodeTerm, encodeArgs, wrapBinders]

theorem appR_reduct {Γ : Ctx sig}
    (function argument target : Term sig Γ .term) :
    reduct? appCongRRule appCongRSpec Γ.length
      (completedR function argument target) =
      some (encodeTerm (appT function target)) := by
  simp [reduct?, instantiateAt?, instantiateArgsAt?,
    appCongRRule, appCongRSpec, arguments?, dependencies?,
    occurrenceDeclared, sitePattern?, occurrenceAt?,
    completedR, captured, lookup, instantiate_root,
    appT, encodeTerm, encodeArgs, wrapBinders]

/-- One selected function firing becomes exactly one left-congruence premise
event at the rule root. -/
theorem appL_premise {Evidence : Type} (oracle : StepOracle Evidence)
    {Γ : Ctx sig} (function argument target : Term sig Γ .term)
    (event : Evidence)
    (oracleResult : oracle Γ.length (encodeTerm function) =
      [(event, encodeTerm target)]) :
    stepResults oracle appCongLRule appCongLSpec Γ.length 0 0
      appCongLStep.source appCongLStep.target
      (captured function argument) =
      [(.step 0 0 event, completedL function argument target)] := by
  have hs := encodeTerm_scoped function
  have ht := encodeTerm_scoped target
  simp [stepResults, appL_source, hs, oracleResult, ht, appL_target]

/-- Right congruence makes its oracle request for the argument and keeps its
selected occurrence separately from the function capture. -/
theorem appR_premise {Evidence : Type} (oracle : StepOracle Evidence)
    {Γ : Ctx sig} (function argument target : Term sig Γ .term)
    (event : Evidence)
    (oracleResult : oracle Γ.length (encodeTerm argument) =
      [(event, encodeTerm target)]) :
    stepResults oracle appCongRRule appCongRSpec Γ.length 0 0
      appCongRStep.source appCongRStep.target
      (captured function argument) =
      [(.step 0 0 event, completedR function argument target)] := by
  have hs := encodeTerm_scoped argument
  have ht := encodeTerm_scoped target
  simp [stepResults, appR_source, hs, oracleResult, ht, appR_target]

/-- An admitted application-left rule executes the intrinsic congruence
constructor in every ambient context, keeping the selected event. -/
theorem appL_executes {Evidence : Type} (oracle : StepOracle Evidence)
    {Γ : Ctx sig} (function argument target : Term sig Γ .term)
    (event : Evidence)
    (oracleResult : oracle Γ.length (encodeTerm function) =
      [(event, encodeTerm target)]) :
    applyRuleWithOracle oracle RelationEnv.empty language Γ.length
      appCongLRule (encodeTerm (appT function argument)) =
      [{ captured := captured function argument,
         completed := completedL function argument target,
         history := [.step 0 0 event],
         target := encodeTerm (appT target argument) }] := by
  have hmatch := appL_match function argument
  have hpremise := appL_premise oracle function argument target event oracleResult
  have hreduct := appL_reduct function argument target
  have hscope := encodeTerm_scoped (appT target argument)
  have hbind : appCongLRule.bindings = some appCongLSpec := rfl
  have hpre : appCongLRule.premises = [.scopedStep appCongLStep] := rfl
  have hstep : appCongLStep.isWellScopedAt Γ.length = true := by
    simp [ScopedStepPremise.isWellScopedAt, appCongLStep,
      Pattern.isWellScopedAt]
  have hbinders : appCongLStep.binders.length = 0 := rfl
  simp [applyRuleWithOracle, hbind, appCongL_binding_admitted,
    hmatch, hpre, runPremises, premiseResults, hstep, hbinders,
    hpremise, finish?, hreduct, hscope]

theorem appR_executes {Evidence : Type} (oracle : StepOracle Evidence)
    {Γ : Ctx sig} (function argument target : Term sig Γ .term)
    (event : Evidence)
    (oracleResult : oracle Γ.length (encodeTerm argument) =
      [(event, encodeTerm target)]) :
    applyRuleWithOracle oracle RelationEnv.empty language Γ.length
      appCongRRule (encodeTerm (appT function argument)) =
      [{ captured := captured function argument,
         completed := completedR function argument target,
         history := [.step 0 0 event],
         target := encodeTerm (appT function target) }] := by
  have hmatch := appR_match function argument
  have hpremise := appR_premise oracle function argument target event oracleResult
  have hreduct := appR_reduct function argument target
  have hscope := encodeTerm_scoped (appT function target)
  have hbind : appCongRRule.bindings = some appCongRSpec := rfl
  have hpre : appCongRRule.premises = [.scopedStep appCongRStep] := rfl
  have hstep : appCongRStep.isWellScopedAt Γ.length = true := by
    simp [ScopedStepPremise.isWellScopedAt, appCongRStep,
      Pattern.isWellScopedAt]
  have hbinders : appCongRStep.binders.length = 0 := rfl
  simp [applyRuleWithOracle, hbind, appCongR_binding_admitted,
    hmatch, hpre, runPremises, premiseResults, hstep, hbinders,
    hpremise, finish?, hreduct, hscope]

/-- The concrete rule at index two transports a selected child firing into
the actual four-rule authored interpreter. -/
theorem appL_runtime_firing {Γ : Ctx sig}
    (fuel : Nat) (function argument target : Term sig Γ .term)
    (event : RuleHistory)
    (oracleResult : rewriteAt RelationEnv.empty language fuel Γ.length
      (encodeTerm function) = [(event, encodeTerm target)]) :
    (.fire 2 [.step 0 0 event], encodeTerm (appT target argument)) ∈
      rewriteAt RelationEnv.empty language (fuel + 1) Γ.length
        (encodeTerm (appT function argument)) := by
  apply (mem_rewriteAt_succ_iff RelationEnv.empty language fuel Γ.length
    (encodeTerm (appT function argument))
    (encodeTerm (appT target argument))
    (.fire 2 [.step 0 0 event])).2
  refine ⟨appCongLRule, 2, ?_,
    { captured := captured function argument,
      completed := completedL function argument target,
      history := [.step 0 0 event],
      target := encodeTerm (appT target argument) }, ?_, rfl, rfl⟩
  · simp [language]
  · rw [appL_executes (rewriteAt RelationEnv.empty language fuel)
      function argument target event oracleResult]
    exact List.mem_singleton.mpr rfl

theorem appR_runtime_firing {Γ : Ctx sig}
    (fuel : Nat) (function argument target : Term sig Γ .term)
    (event : RuleHistory)
    (oracleResult : rewriteAt RelationEnv.empty language fuel Γ.length
      (encodeTerm argument) = [(event, encodeTerm target)]) :
    (.fire 3 [.step 0 0 event], encodeTerm (appT function target)) ∈
      rewriteAt RelationEnv.empty language (fuel + 1) Γ.length
        (encodeTerm (appT function argument)) := by
  apply (mem_rewriteAt_succ_iff RelationEnv.empty language fuel Γ.length
    (encodeTerm (appT function argument))
    (encodeTerm (appT function target))
    (.fire 3 [.step 0 0 event])).2
  refine ⟨appCongRRule, 3, ?_,
    { captured := captured function argument,
      completed := completedR function argument target,
      history := [.step 0 0 event],
      target := encodeTerm (appT function target) }, ?_, rfl, rfl⟩
  · simp [language]
  · rw [appR_executes (rewriteAt RelationEnv.empty language fuel)
      function argument target event oracleResult]
    exact List.mem_singleton.mpr rfl

/-- A selected left firing has an intrinsic constructor whenever its
retained premise evidence is a derivation of the child step. -/
theorem appL_firing_has_tree {Evidence : Type} (oracle : StepOracle Evidence)
    {Γ : Ctx sig} (function argument target : Term sig Γ .term)
    (event : Evidence)
    (oracleResult : oracle Γ.length (encodeTerm function) =
      [(event, encodeTerm target)])
    (premise : Derivation function target) :
    ∃ firing ∈ applyRuleWithOracle oracle RelationEnv.empty language Γ.length
        appCongLRule (encodeTerm (appT function argument)),
      firing.target = encodeTerm (appT target argument) ∧
      firing.history = [.step 0 0 event] ∧
      Nonempty (Derivation (appT function argument) (appT target argument)) := by
  let firing : RuleFiring Evidence :=
    { captured := captured function argument,
      completed := completedL function argument target,
      history := [.step 0 0 event],
      target := encodeTerm (appT target argument) }
  refine ⟨firing, ?_, rfl, rfl, ?_⟩
  · rw [appL_executes oracle function argument target event oracleResult]
    exact List.mem_singleton.mpr rfl
  · exact ⟨.roll (.appCongL function target argument) (fun _ => premise)⟩

theorem appR_firing_has_tree {Evidence : Type} (oracle : StepOracle Evidence)
    {Γ : Ctx sig} (function argument target : Term sig Γ .term)
    (event : Evidence)
    (oracleResult : oracle Γ.length (encodeTerm argument) =
      [(event, encodeTerm target)])
    (premise : Derivation argument target) :
    ∃ firing ∈ applyRuleWithOracle oracle RelationEnv.empty language Γ.length
        appCongRRule (encodeTerm (appT function argument)),
      firing.target = encodeTerm (appT function target) ∧
      firing.history = [.step 0 0 event] ∧
      Nonempty (Derivation (appT function argument) (appT function target)) := by
  let firing : RuleFiring Evidence :=
    { captured := captured function argument,
      completed := completedR function argument target,
      history := [.step 0 0 event],
      target := encodeTerm (appT function target) }
  refine ⟨firing, ?_, rfl, rfl, ?_⟩
  · rw [appR_executes oracle function argument target event oracleResult]
    exact List.mem_singleton.mpr rfl
  · exact ⟨.roll (.appCongR function argument target) (fun _ => premise)⟩

/-- A premise cannot move a variable outside its ambient context into the
enclosing application. -/
theorem appL_rejects_escaping_target {Evidence : Type}
    (oracle : StepOracle Evidence) {Γ : Ctx sig}
    (function argument : Term sig Γ .term) (event : Evidence)
    (oracleResult : oracle Γ.length (encodeTerm function) =
      [(event, .bvar Γ.length)]) :
    stepResults oracle appCongLRule appCongLSpec Γ.length 0 0
      appCongLStep.source appCongLStep.target
      (captured function argument) = [] := by
  have hs := encodeTerm_scoped function
  simp [stepResults, appL_source, hs, oracleResult,
    Pattern.isWellScopedAt]

theorem appR_rejects_escaping_target {Evidence : Type}
    (oracle : StepOracle Evidence) {Γ : Ctx sig}
    (function argument : Term sig Γ .term) (event : Evidence)
    (oracleResult : oracle Γ.length (encodeTerm argument) =
      [(event, .bvar Γ.length)]) :
    stepResults oracle appCongRRule appCongRSpec Γ.length 0 0
      appCongRStep.source appCongRStep.target
      (captured function argument) = [] := by
  have hs := encodeTerm_scoped argument
  simp [stepResults, appR_source, hs, oracleResult,
    Pattern.isWellScopedAt]

/-- Repeated equal oracle answers are different firing occurrences. The
selected list ordinal survives even when endpoints and evidence coincide. -/
theorem appL_keeps_duplicate_occurrences {Γ : Ctx sig}
    (oracle : StepOracle Unit)
    (function argument target : Term sig Γ .term)
    (oracleResult : oracle Γ.length (encodeTerm function) =
      [((), encodeTerm target), ((), encodeTerm target)]) :
    stepResults oracle appCongLRule appCongLSpec Γ.length 0 0
      appCongLStep.source appCongLStep.target
      (captured function argument) =
      [(.step 0 0 (), completedL function argument target),
       (.step 0 1 (), completedL function argument target)] := by
  have hs := encodeTerm_scoped function
  have ht := encodeTerm_scoped target
  simp [stepResults, appL_source, hs, oracleResult, ht, appL_target]

theorem appR_keeps_duplicate_occurrences {Γ : Ctx sig}
    (oracle : StepOracle Unit)
    (function argument target : Term sig Γ .term)
    (oracleResult : oracle Γ.length (encodeTerm argument) =
      [((), encodeTerm target), ((), encodeTerm target)]) :
    stepResults oracle appCongRRule appCongRSpec Γ.length 0 0
      appCongRStep.source appCongRStep.target
      (captured function argument) =
      [(.step 0 0 (), completedR function argument target),
       (.step 0 1 (), completedR function argument target)] := by
  have hs := encodeTerm_scoped argument
  have ht := encodeTerm_scoped target
  simp [stepResults, appR_source, hs, oracleResult, ht, appR_target]

/-- At fuel zero no recursive child can satisfy an application congruence
premise, irrespective of the source pattern. -/
private theorem no_oracle_step {Evidence : Type}
    (oracle : StepOracle Evidence)
    (hempty : ∀ depth pattern, oracle depth pattern = [])
    (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient index localDepth : Nat) (source target : Pattern)
    (assignment : Assignment) :
    stepResults oracle rule spec ambient index localDepth
      source target assignment = [] := by
  cases hinst : instantiateAt? rule spec ambient (.premise index 0 0)
      [] localDepth assignment source with
  | none => simp [stepResults, hinst]
  | some instantiated => simp [stepResults, hinst, hempty]

private theorem appL_no_fuel_zero (ambient : Nat) (input : Pattern) :
    applyRuleWithOracle (rewriteAt RelationEnv.empty language 0)
      RelationEnv.empty language ambient appCongLRule input = [] := by
  have hempty : ∀ depth pattern,
      rewriteAt RelationEnv.empty language 0 depth pattern = [] := by
    intro depth pattern
    rfl
  have hrun (assignment : Assignment) :
      runPremises (rewriteAt RelationEnv.empty language 0)
        RelationEnv.empty language appCongLRule appCongLSpec ambient 0
        appCongLRule.premises assignment = [] := by
    simp [appCongLRule, runPremises, premiseResults,
      no_oracle_step _ hempty]
  have hbind : appCongLRule.bindings = some appCongLSpec := rfl
  simp [applyRuleWithOracle, hbind, appCongL_binding_admitted, hrun]

private theorem appR_no_fuel_zero (ambient : Nat) (input : Pattern) :
    applyRuleWithOracle (rewriteAt RelationEnv.empty language 0)
      RelationEnv.empty language ambient appCongRRule input = [] := by
  have hempty : ∀ depth pattern,
      rewriteAt RelationEnv.empty language 0 depth pattern = [] := by
    intro depth pattern
    rfl
  have hrun (assignment : Assignment) :
      runPremises (rewriteAt RelationEnv.empty language 0)
        RelationEnv.empty language appCongRRule appCongRSpec ambient 0
        appCongRRule.premises assignment = [] := by
    simp [appCongRRule, runPremises, premiseResults,
      no_oracle_step _ hempty]
  have hbind : appCongRRule.bindings = some appCongRSpec := rfl
  simp [applyRuleWithOracle, hbind, appCongR_binding_admitted, hrun]

/-- In the full four-rule authored language, a beta redex has exactly its
beta firing at fuel one. Both application-congruence premises have no fuel-zero
child, so neither can invent another answer at this depth. -/
theorem full_beta_one_step {Γ : Ctx sig}
    (body : Term sig (.term :: Γ) .term)
    (argument : Term sig Γ .term) :
    rewriteAt RelationEnv.empty language 1 Γ.length
      (encodeTerm (appT (lamT body) argument)) =
      [(.fire 0 [], encodeTerm (inst body argument))] := by
  have hbeta : applyRuleWithOracle
      (rewriteAt RelationEnv.empty language 0) RelationEnv.empty language
      Γ.length betaRule (encodeTerm (appT (lamT body) argument)) =
      [{ captured := Mettapedia.OSLF.Binding.LambdaAuthoredBetaExecutionComparison.matched
           body argument,
         completed := Mettapedia.OSLF.Binding.LambdaAuthoredBetaExecutionComparison.matched
           body argument,
         history := [], target := encodeTerm (inst body argument) }] := by
    exact Mettapedia.OSLF.Binding.LambdaAuthoredBetaExecutionComparison.authored_beta_executes_intrinsic
      (rewriteAt RelationEnv.empty language 0) body argument
  have hlam : applyRuleWithOracle
      (rewriteAt RelationEnv.empty language 0) RelationEnv.empty language
      Γ.length lamCongRule (encodeTerm (appT (lamT body) argument)) = [] := by
    exact Mettapedia.OSLF.Binding.LambdaAuthoredLamCongExecutionComparison.lamCong_rejects_beta_source
      (rewriteAt RelationEnv.empty language 0) body argument
  have happL := appL_no_fuel_zero Γ.length
    (encodeTerm (appT (lamT body) argument))
  have happR := appR_no_fuel_zero Γ.length
    (encodeTerm (appT (lamT body) argument))
  have hrules : language.rewrites.zipIdx =
      [(betaRule, 0), (lamCongRule, 1),
       (appCongLRule, 2), (appCongRRule, 3)] := rfl
  unfold rewriteAt
  rw [hrules]
  simp only [List.flatMap_cons, List.flatMap_nil]
  rw [hbeta, hlam, happL, happR]
  rfl

/-- Actual bounded execution nests beta in the function position of an
application. Both selected rule indices and the child firing are retained. -/
theorem beta_under_appL {Γ : Ctx sig}
    (body : Term sig (.term :: Γ) .term)
    (argument outer : Term sig Γ .term) :
    (.fire 2 [.step 0 0 (.fire 0 [])],
      encodeTerm (appT (inst body argument) outer)) ∈
      rewriteAt RelationEnv.empty language 2 Γ.length
        (encodeTerm (appT (appT (lamT body) argument) outer)) := by
  exact appL_runtime_firing 1 (appT (lamT body) argument)
    outer (inst body argument) (.fire 0 [])
    (full_beta_one_step body argument)

/-- The same child beta can be selected in the argument position. This is a
different authored rule occurrence and a different retained history. -/
theorem beta_under_appR {Γ : Ctx sig}
    (body : Term sig (.term :: Γ) .term)
    (argument outer : Term sig Γ .term) :
    (.fire 3 [.step 0 0 (.fire 0 [])],
      encodeTerm (appT outer (inst body argument))) ∈
      rewriteAt RelationEnv.empty language 2 Γ.length
        (encodeTerm (appT outer (appT (lamT body) argument))) := by
  exact appR_runtime_firing 1 outer (appT (lamT body) argument)
    (inst body argument) (.fire 0 [])
    (full_beta_one_step body argument)

#print axioms appL_match
#print axioms appR_match
#print axioms appL_executes
#print axioms appR_executes
#print axioms appL_runtime_firing
#print axioms appR_runtime_firing
#print axioms appL_firing_has_tree
#print axioms appR_firing_has_tree
#print axioms appL_rejects_escaping_target
#print axioms appR_rejects_escaping_target
#print axioms appL_keeps_duplicate_occurrences
#print axioms appR_keeps_duplicate_occurrences
#print axioms full_beta_one_step
#print axioms beta_under_appL
#print axioms beta_under_appR

end Mettapedia.OSLF.Binding.LambdaAuthoredAppCongExecutionComparison
