import Mettapedia.OSLF.Syntax.LambdaAuthoredBetaExecutionComparison
import Mettapedia.GSLT.LanguageDef.TypedFullSpineRecovery

/-!
# Authored LamCong at arbitrary intrinsic lambda contexts

The canonical scoped premise runs beneath the enclosing lambda binder. Its
source and target use separate contextual values in that extended context.
The executable rule keeps the oracle occurrence as firing evidence.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.LambdaAuthoredLamCongExecutionComparison

open Mettapedia.OSLF.Binding.LambdaContextualRung
open Mettapedia.OSLF.Binding.LambdaScopedAuthoringComparison
open Mettapedia.OSLF.Binding.LambdaPatternRendering
open Mettapedia.OSLF.Binding.LambdaAuthoredBetaExecutionComparison
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.RuleBinding
open Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching
open Mettapedia.OSLF.MeTTaIL.ScopedPremiseExecution
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.GSLT.Examples.ScopedLamCongExecution

private def termType : TypeExpr := .base "Term"

private def lamSpec : RuleBindingSpec :=
  { dependencies := [("B", [termType]), ("C", [termType])],
    occurrences :=
      [{ «name» := "B", site := .left, path := [0, 0],
         arguments := [.bvar 0] },
       { «name» := "C", site := .right, path := [0, 0],
         arguments := [.bvar 0] },
       { «name» := "B", site := .premise 0 0 0, path := [],
         arguments := [.bvar 0] },
       { «name» := "C", site := .premise 0 0 1, path := [],
         arguments := [.bvar 0] }] }

private def initial {Γ : Ctx sig}
    (body : Term sig (.term :: Γ) .term) : Assignment :=
  [("B", { dependencies := [termType], ambient := Γ.length,
            body := encodeTerm body })]

private def completed {Γ : Ctx sig}
    (body target : Term sig (.term :: Γ) .term) : Assignment :=
  [("C", { dependencies := [termType], ambient := Γ.length,
            body := encodeTerm target }),
   ("B", { dependencies := [termType], ambient := Γ.length,
            body := encodeTerm body })]

private theorem lam_admitted : admittedFor lamCongRule lamSpec = true := by
  decide +kernel

private theorem left_arguments :
    arguments? lamCongRule lamSpec "B" .left [0, 0] =
      some [.bvar 0] := by
  decide +kernel

private theorem source_arguments :
    arguments? lamCongRule lamSpec "B" (.premise 0 0 0) [] =
      some [.bvar 0] := by
  decide +kernel

private theorem target_arguments :
    arguments? lamCongRule lamSpec "C" (.premise 0 0 1) [] =
      some [.bvar 0] := by
  decide +kernel

private theorem right_arguments :
    arguments? lamCongRule lamSpec "C" .right [0, 0] =
      some [.bvar 0] := by
  decide +kernel

private theorem recover_contextual {Γ : Ctx sig}
    (body : Term sig (.term :: Γ) .term) :
    recoverValue? [termType] Γ.length 1 [.bvar 0] (encodeTerm body) =
      some { dependencies := [termType], ambient := Γ.length,
             body := encodeTerm body } := by
  have hscoped : (encodeTerm body).isWellScopedAt (1 + Γ.length) = true := by
    have hs := encodeTerm_scoped body
    change (encodeTerm body).isWellScopedAt (Γ.length + 1) = true at hs
    simpa [Nat.add_comm] using hs
  simpa [Mettapedia.GSLT.LanguageDef.RestAwareTyping.fullSpine] using
    (Mettapedia.GSLT.LanguageDef.RestAwareTyping.recoverValue?_fullSpine
      [termType] (List.replicate Γ.length termType) (encodeTerm body)
      (by simpa using hscoped))

private theorem instantiate_contextual {Γ : Ctx sig}
    (body : Term sig (.term :: Γ) .term) :
    instantiateValue?
      { dependencies := [termType], ambient := Γ.length,
        body := encodeTerm body }
      Γ.length 1 [.bvar 0] = some (encodeTerm body) := by
  exact recoverValue?_forward [termType] Γ.length 1 [.bvar 0]
    (encodeTerm body) _ (recover_contextual body)

/-- Matching the authored lambda source retains the whole body context. -/
theorem lam_match_recovers_intrinsic {Γ : Ctx sig}
    (body : Term sig (.term :: Γ) .term) :
    matchRuleAt lamCongRule lamSpec Γ.length (encodeTerm (lamT body)) =
      [initial body] := by
  simp [matchRuleAt, lamCongRule, matchAt, matchArgsAt,
    lamT, encodeTerm, encodeArgs, wrapBinders, capture?, assign, lookup,
    initial, lamSpec, arguments?, dependencies?, occurrenceDeclared,
    sitePattern?, occurrenceAt?, recover_contextual]

/-- The local source request is exactly the encoded intrinsic body. -/
theorem premise_source_is_body {Γ : Ctx sig}
    (body : Term sig (.term :: Γ) .term) :
    instantiateAt? lamCongRule lamSpec Γ.length (.premise 0 0 0) [] 1
      (initial body) localStep.source = some (encodeTerm body) := by
  simp [instantiateAt?, localStep, initial, lookup,
    source_arguments, instantiate_contextual]

/-- The selected target of a scoped premise is captured with the same
dependency binder and the original ambient context. -/
theorem premise_target_recovers {Γ : Ctx sig}
    (body target : Term sig (.term :: Γ) .term) :
    matchAt lamCongRule lamSpec Γ.length (.premise 0 0 1) [] 1
      (initial body) localStep.target (encodeTerm target) =
        [completed body target] := by
  have hdeps : dependencies? lamSpec "C" = some [termType] := by
    decide +kernel
  have captured : capture? lamCongRule lamSpec Γ.length 1
      (.premise 0 0 1) [] (initial body) "C" (encodeTerm target) =
      some (completed body target) := by
    simp [capture?, hdeps, target_arguments, recover_contextual,
      assign, lookup, initial, completed]
  simpa [localStep, matchAt] using congrArg Option.toList captured

/-- Once the premise supplies its target, the actual authored right-hand
side reconstructs the enclosing lambda at the original ambient context. -/
theorem reduct_is_lam {Γ : Ctx sig}
    (body target : Term sig (.term :: Γ) .term) :
    reduct? lamCongRule lamSpec Γ.length (completed body target) =
      some (encodeTerm (lamT target)) := by
  have inner : instantiateAt? lamCongRule lamSpec Γ.length .right
      [0, 0] 1 (completed body target) (.fvar "C") =
      some (encodeTerm target) := by
    simp [instantiateAt?, completed, lookup, right_arguments,
      instantiate_contextual]
  simp [reduct?, lamCongRule, instantiateAt?, instantiateArgsAt?,
    completed, lookup, lamSpec, arguments?, dependencies?,
    occurrenceDeclared, sitePattern?, occurrenceAt?,
    instantiate_contextual, lamT, encodeTerm, encodeArgs, wrapBinders]

/-- A singleton oracle event at the exact binder-local body request produces
one event at the authored premise. Its ordinal remains visible. -/
theorem scoped_premise_selects_body_step {Evidence : Type}
    (oracle : StepOracle Evidence) {Γ : Ctx sig}
    (body target : Term sig (.term :: Γ) .term)
    (event : Evidence)
    (oracleResult : oracle (1 + Γ.length) (encodeTerm body) =
      [(event, encodeTerm target)]) :
    stepResults oracle lamCongRule lamSpec Γ.length 0 1
      localStep.source localStep.target (initial body) =
        [(.step 0 0 event, completed body target)] := by
  have sourceScoped : (encodeTerm body).isWellScopedAt (1 + Γ.length) = true := by
    have h := encodeTerm_scoped body
    change (encodeTerm body).isWellScopedAt (Γ.length + 1) = true at h
    simpa [Nat.add_comm] using h
  have targetScoped : (encodeTerm target).isWellScopedAt
      (1 + Γ.length) = true := by
    have h := encodeTerm_scoped target
    change (encodeTerm target).isWellScopedAt (Γ.length + 1) = true at h
    simpa [Nat.add_comm] using h
  simp [stepResults, premise_source_is_body, sourceScoped, oracleResult,
    targetScoped, premise_target_recovers]

/-- At every ambient context, one admitted binder-local firing produces
exactly the enclosing lambda with the selected premise event retained. -/
theorem authored_lamCong_executes_intrinsic {Evidence : Type}
    (oracle : StepOracle Evidence) {Γ : Ctx sig}
    (body target : Term sig (.term :: Γ) .term)
    (event : Evidence)
    (oracleResult : oracle (1 + Γ.length) (encodeTerm body) =
      [(event, encodeTerm target)]) :
    applyRuleWithOracle oracle RelationEnv.empty language Γ.length
      lamCongRule (encodeTerm (lamT body)) =
      [{ captured := initial body, completed := completed body target,
         history := [.step 0 0 event], target := encodeTerm (lamT target) }] := by
  have hmatch := lam_match_recovers_intrinsic body
  have hpremise := scoped_premise_selects_body_step oracle body target event
    oracleResult
  have hreduct := reduct_is_lam body target
  have hscope := encodeTerm_scoped (lamT target)
  have hbind : lamCongRule.bindings = some lamSpec := rfl
  have hpre : lamCongRule.premises = [.scopedStep localStep] := rfl
  have hstep : localStep.isWellScopedAt Γ.length = true := by
    simp [ScopedStepPremise.isWellScopedAt, localStep,
      Pattern.isWellScopedAt]
  have hbinders : localStep.binders.length = 1 := rfl
  simp [applyRuleWithOracle, hbind, lam_admitted, hmatch,
    hpre, runPremises, premiseResults, hstep, hbinders,
    hpremise, finish?, hreduct, hscope]

/-- An application-shaped beta source cannot match the lambda-shaped
congruence rule, in any ambient context. -/
theorem lamCong_rejects_beta_source {Evidence : Type}
    (oracle : StepOracle Evidence) {Γ : Ctx sig}
    (body : Term sig (.term :: Γ) .term)
    (argument : Term sig Γ .term) :
    applyRuleWithOracle oracle RelationEnv.empty language Γ.length
      lamCongRule (encodeTerm (appT (lamT body) argument)) = [] := by
  simp [applyRuleWithOracle, lamCongRule, matchRuleAt, matchAt,
    appT, encodeTerm, encodeArgs]

/-- At fuel one, the only authored firing of an intrinsic beta source is
the corresponding beta constructor at rule position zero. -/
theorem authored_beta_only_one_step {Γ : Ctx sig}
    (body : Term sig (.term :: Γ) .term)
    (argument : Term sig Γ .term) :
    rewriteAt RelationEnv.empty language 1 Γ.length
      (encodeTerm (appT (lamT body) argument)) =
        [(.fire 0 [], encodeTerm (inst body argument))] := by
  have hbeta := authored_beta_executes_intrinsic
    (rewriteAt RelationEnv.empty language 0) body argument
  have hother := lamCong_rejects_beta_source
    (rewriteAt RelationEnv.empty language 0) body argument
  have hrules : language.rewrites.zipIdx =
      [(betaRule, 0), (lamCongRule, 1)] := rfl
  unfold rewriteAt
  rw [hrules]
  simp only [List.flatMap_cons, List.flatMap_nil]
  rw [hbeta, hother]
  rfl

/-- The executable authored two-level history realizes beta under a lambda
at every ambient context, preserving the local binder in the result. -/
theorem authored_nested_beta_under_lam {Γ : Ctx sig}
    (inner : Term sig (.term :: .term :: Γ) .term)
    (argument : Term sig (.term :: Γ) .term) :
    (.fire 1 [.step 0 0 (.fire 0 [])],
      encodeTerm (lamT (inst inner argument))) ∈
      rewriteAt RelationEnv.empty language 2 Γ.length
        (encodeTerm (lamT (appT (lamT inner) argument))) := by
  have oracleResult := authored_beta_only_one_step inner argument
  change rewriteAt RelationEnv.empty language 1 (Γ.length + 1)
    (encodeTerm (appT (lamT inner) argument)) =
      [(.fire 0 [], encodeTerm (inst inner argument))] at oracleResult
  have oracleResult' : rewriteAt RelationEnv.empty language 1
      (1 + Γ.length) (encodeTerm (appT (lamT inner) argument)) =
        [(.fire 0 [], encodeTerm (inst inner argument))] := by
    simpa only [Nat.add_comm] using oracleResult
  have outer := authored_lamCong_executes_intrinsic
    (rewriteAt RelationEnv.empty language 1)
      (appT (lamT inner) argument) (inst inner argument)
      (.fire 0 []) oracleResult'
  apply (mem_rewriteAt_succ_iff RelationEnv.empty language 1 Γ.length
    (encodeTerm (lamT (appT (lamT inner) argument)))
    (encodeTerm (lamT (inst inner argument)))
    (.fire 1 [.step 0 0 (.fire 0 [])])).2
  refine ⟨lamCongRule, 1, ?_,
    { captured := initial (appT (lamT inner) argument),
      completed := completed (appT (lamT inner) argument)
        (inst inner argument),
      history := [.step 0 0 (.fire 0 [])],
      target := encodeTerm (lamT (inst inner argument)) }, ?_, rfl, rfl⟩
  · simp [language]
  · rw [outer]
    exact List.mem_singleton.mpr rfl

/-- A local oracle answer outside the binder-extended context is rejected
before its target can become the body of the enclosing lambda. -/
theorem escaping_oracle_result_rejected {Evidence : Type}
    (oracle : StepOracle Evidence) {Γ : Ctx sig}
    (body : Term sig (.term :: Γ) .term) (event : Evidence)
    (oracleResult : oracle (1 + Γ.length) (encodeTerm body) =
      [(event, .bvar (1 + Γ.length))]) :
    stepResults oracle lamCongRule lamSpec Γ.length 0 1
      localStep.source localStep.target (initial body) = [] := by
  have sourceScoped : (encodeTerm body).isWellScopedAt (1 + Γ.length) = true := by
    have h := encodeTerm_scoped body
    change (encodeTerm body).isWellScopedAt (Γ.length + 1) = true at h
    simpa [Nat.add_comm] using h
  simp [stepResults, premise_source_is_body, sourceScoped,
    oracleResult, Pattern.isWellScopedAt]

/-- Two equal target values at distinct oracle positions remain two
different premise events, even in an arbitrary ambient context. -/
theorem duplicate_oracle_results_retained {Γ : Ctx sig}
    (oracle : StepOracle Unit)
    (body target : Term sig (.term :: Γ) .term)
    (oracleResult : oracle (1 + Γ.length) (encodeTerm body) =
      [((), encodeTerm target), ((), encodeTerm target)]) :
    stepResults oracle lamCongRule lamSpec Γ.length 0 1
      localStep.source localStep.target (initial body) =
      [(.step 0 0 (), completed body target),
       (.step 0 1 (), completed body target)] := by
  have sourceScoped : (encodeTerm body).isWellScopedAt (1 + Γ.length) = true := by
    have h := encodeTerm_scoped body
    change (encodeTerm body).isWellScopedAt (Γ.length + 1) = true at h
    simpa [Nat.add_comm] using h
  have targetScoped : (encodeTerm target).isWellScopedAt
      (1 + Γ.length) = true := by
    have h := encodeTerm_scoped target
    change (encodeTerm target).isWellScopedAt (Γ.length + 1) = true at h
    simpa [Nat.add_comm] using h
  simp [stepResults, premise_source_is_body, sourceScoped, oracleResult,
    targetScoped, premise_target_recovers]

/-- The authored nested firing survives every ambient substitution; its
inner beta premise uses the substitution lifted through both lambdas. -/
theorem nested_beta_stable_under_intrinsic_substitution
    {Γ Δ : Ctx sig} (sigma : Sub sig Γ Δ)
    (inner : Term sig (.term :: .term :: Γ) .term)
    (argument : Term sig (.term :: Γ) .term) :
    (.fire 1 [.step 0 0 (.fire 0 [])],
      encodeTerm (bind sigma (lamT (inst inner argument)))) ∈
      rewriteAt RelationEnv.empty language 2 Δ.length
        (encodeTerm (bind sigma
          (lamT (appT (lamT inner) argument)))) := by
  let lifted := liftSub sigma [.term]
  let inner' := bind (liftSub lifted [.term]) inner
  let argument' := bind lifted argument
  have sourceEq :
      bind sigma (lamT (appT (lamT inner) argument)) =
        lamT (appT (lamT inner') argument') := by
    simp [inner', argument', lifted, bind_appT, bind_lamT]
  have targetEq :
      bind sigma (lamT (inst inner argument)) =
        lamT (inst inner' argument') := by
    change lamT (bind lifted (inst inner argument)) =
      lamT (inst (bind (liftSub lifted [.term]) inner)
        (bind lifted argument))
    rw [ContextualLinearSubstitution.bind_inst lifted inner argument]
  rw [sourceEq, targetEq]
  exact authored_nested_beta_under_lam inner' argument'

/-- The same stability law is stated entirely on the canonical authored
pattern side, via the proved lowering/substitution comparison. -/
theorem nested_beta_stable_under_pattern_substitution
    {Γ Δ : Ctx sig} (sigma : Sub sig Γ Δ)
    (inner : Term sig (.term :: .term :: Γ) .term)
    (argument : Term sig (.term :: Γ) .term) :
    (.fire 1 [.step 0 0 (.fire 0 [])],
      Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute
        (Mettapedia.OSLF.Binding.PatternRendering.encodeSub
          LambdaPatternRendering.rendering sigma)
        (encodeTerm (lamT (inst inner argument)))) ∈
      rewriteAt RelationEnv.empty language 2 Δ.length
        (Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute
          (Mettapedia.OSLF.Binding.PatternRendering.encodeSub
            LambdaPatternRendering.rendering sigma)
          (encodeTerm (lamT (appT (lamT inner) argument)))) := by
  simpa only [LambdaPatternRendering.encodeTerm_bind] using
    nested_beta_stable_under_intrinsic_substitution sigma inner argument

#print axioms lam_match_recovers_intrinsic
#print axioms premise_source_is_body
#print axioms premise_target_recovers
#print axioms reduct_is_lam
#print axioms scoped_premise_selects_body_step
#print axioms authored_lamCong_executes_intrinsic
#print axioms authored_beta_only_one_step
#print axioms authored_nested_beta_under_lam
#print axioms escaping_oracle_result_rejected
#print axioms duplicate_oracle_results_retained
#print axioms nested_beta_stable_under_intrinsic_substitution
#print axioms nested_beta_stable_under_pattern_substitution

end Mettapedia.OSLF.Binding.LambdaAuthoredLamCongExecutionComparison
