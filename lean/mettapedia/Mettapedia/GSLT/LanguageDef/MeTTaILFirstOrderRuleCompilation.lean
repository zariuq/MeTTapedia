import Mettapedia.OSLF.MeTTaIL.Engine
import Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep
import Mettapedia.OSLF.MeTTaIL.MatchSpec

/-!
# First-order rule plans for MeTTaIL

This module compiles the first-order fragment of MeTTaIL rewrite rows to an
independent, inspectable plan.  Variables, rigid bound occurrences, and
ordered applications are retained; binders, explicit substitutions, and
collections are rejected rather than silently delegated to a different
matcher.

The plan interpreter is proved equal to the ordinary syntactic matcher,
source-bound relation-premise evaluator, and right-hand-side instantiator.
Unsupported premise forms reject compilation.  This makes the plan suitable
as the next input to a StructuredC lowering without turning a family tag, an
arbitrary premise callback, or a handwritten case number into semantic
authority.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.MeTTaILFirstOrderRuleCompilation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep

/-! ## Independent pattern plans -/

/-- The admitted first-order pattern fragment. -/
inductive PatternPlan where
  | metavariable (name : String)
  | bound (index : Nat)
  | application (constructor : String) (arguments : List PatternPlan)
deriving Repr

mutual
  /-- Structural work of one pattern plan.  Besides proving totality, this is
  the source-size component of later residual-code bounds. -/
  def PatternPlan.work : PatternPlan -> Nat
    | .metavariable _ | .bound _ => 1
    | .application _ arguments => 1 + patternPlansWork arguments

  /-- Structural work of an ordered child vector. -/
  def patternPlansWork : List PatternPlan -> Nat
    | [] => 0
    | plan :: plans => plan.work + patternPlansWork plans
end

@[simp] theorem PatternPlan.work_pos (plan : PatternPlan) : 0 < plan.work := by
  cases plan <;> simp [PatternPlan.work]

mutual
  /-- Compile one pattern, rejecting syntax outside the first-order fragment. -/
  def compilePattern? : Pattern -> Option PatternPlan
    | .fvar name => some (.metavariable name)
    | .bvar index => some (.bound index)
    | .apply constructor arguments => do
        let compiled <- compilePatterns? arguments
        pure (.application constructor compiled)
    | .lambda _ _ | .multiLambda _ _ _ | .subst _ _ | .collection _ _ _ =>
        none

  /-- Compile an ordered pattern row without dropping or reordering entries. -/
  def compilePatterns? : List Pattern -> Option (List PatternPlan)
    | [] => some []
    | pattern :: patterns => do
        let compiled <- compilePattern? pattern
        let tail <- compilePatterns? patterns
        pure (compiled :: tail)
end

mutual
  /-- Erase a compiled plan to its complete source pattern. -/
  def PatternPlan.erase : PatternPlan -> Pattern
    | .metavariable name => .fvar name
    | .bound index => .bvar index
    | .application constructor arguments =>
        .apply constructor (erasePatterns arguments)

  /-- Erase an ordered row of plans. -/
  def erasePatterns : List PatternPlan -> List Pattern
    | [] => []
    | plan :: plans => plan.erase :: erasePatterns plans
end

@[simp] theorem erasePatterns_length (plans : List PatternPlan) :
    (erasePatterns plans).length = plans.length := by
  induction plans with
  | nil => rfl
  | cons plan plans inductionHypothesis =>
      simp [erasePatterns, inductionHypothesis]

mutual
  /-- Successful compilation retains the exact source pattern. -/
  theorem erase_of_compilePattern?
      (source : Pattern) (compiled : PatternPlan)
      (accepted : compilePattern? source = some compiled) :
      compiled.erase = source := by
    cases source with
    | fvar name =>
        simp [compilePattern?] at accepted
        subst compiled
        rfl
    | bvar index =>
        simp [compilePattern?] at accepted
        subst compiled
        rfl
    | apply constructor arguments =>
        simp only [compilePattern?, Option.bind_eq_bind] at accepted
        cases argumentsCompiled : compilePatterns? arguments with
        | none => simp [argumentsCompiled] at accepted
        | some plans =>
            simp [argumentsCompiled] at accepted
            subst compiled
            simp [PatternPlan.erase,
              erasePatterns_of_compilePatterns? arguments plans
                argumentsCompiled]
    | lambda name body => simp [compilePattern?] at accepted
    | multiLambda arity names body => simp [compilePattern?] at accepted
    | subst body replacement => simp [compilePattern?] at accepted
    | collection kind elements rest => simp [compilePattern?] at accepted

  /-- Successful row compilation retains every source occurrence in order. -/
  theorem erasePatterns_of_compilePatterns?
      (sources : List Pattern) (compiled : List PatternPlan)
      (accepted : compilePatterns? sources = some compiled) :
      erasePatterns compiled = sources := by
    cases sources with
    | nil =>
        simp [compilePatterns?] at accepted
        subst compiled
        rfl
    | cons source sources =>
        simp only [compilePatterns?, Option.bind_eq_bind] at accepted
        cases headCompiled : compilePattern? source with
        | none => simp [headCompiled] at accepted
        | some head =>
            cases tailCompiled : compilePatterns? sources with
            | none => simp [headCompiled, tailCompiled] at accepted
            | some tail =>
                simp [headCompiled, tailCompiled] at accepted
                subst compiled
                simp [erasePatterns,
                  erase_of_compilePattern? source head headCompiled,
                  erasePatterns_of_compilePatterns? sources tail tailCompiled]
end

/-! ## Exact plan interpretation -/

mutual
  /-- Execute a compiled plan with the same observable binding carrier as the
  canonical MeTTaIL matcher. -/
  def PatternPlan.run : PatternPlan -> Pattern -> List Bindings
    | .metavariable name, subject => [[(name, subject)]]
    | .bound expected, .bvar actual =>
        if expected == actual then [[]] else []
    | .application expected plans, .apply actual subjects =>
        if expected == actual && plans.length == subjects.length then
          runPlans plans subjects
        else
          []
    | _, _ => []

  /-- Execute an ordered plan row, merging repeated variables exactly as the
  canonical matcher does. -/
  def runPlans : List PatternPlan -> List Pattern -> List Bindings
    | [], [] => [[]]
    | plan :: plans, subject :: subjects =>
        (plan.run subject).flatMap fun headBindings =>
          (runPlans plans subjects).filterMap fun tailBindings =>
            mergeBindings headBindings tailBindings
    | _, _ => []
end

mutual
  /-- Plan execution is extensionally the canonical matcher on the erased
  pattern. -/
  theorem run_eq_matchPattern (plan : PatternPlan) (subject : Pattern) :
      plan.run subject = matchPattern plan.erase subject := by
    cases plan with
    | metavariable name =>
        simp [PatternPlan.run, PatternPlan.erase, matchPattern]
    | bound index =>
        cases subject <;> simp [PatternPlan.run, PatternPlan.erase,
          matchPattern]
    | application constructor plans =>
        cases subject with
        | apply actual subjects =>
            simp only [PatternPlan.run, PatternPlan.erase, matchPattern,
              erasePatterns_length]
            by_cases eligible : constructor == actual &&
                plans.length == subjects.length
            · simpa [eligible] using runPlans_eq_matchArgs plans subjects
            · simp [eligible]
        | _ => simp [PatternPlan.run, PatternPlan.erase, matchPattern]
  termination_by 2 * plan.work
  decreasing_by
    simp [PatternPlan.work]
    omega

  /-- List companion to `run_eq_matchPattern`. -/
  theorem runPlans_eq_matchArgs
      (plans : List PatternPlan) (subjects : List Pattern) :
      runPlans plans subjects = matchArgs (erasePatterns plans) subjects := by
    cases plans with
    | nil => cases subjects <;> simp [runPlans, erasePatterns, matchArgs]
    | cons plan plans =>
        cases subjects with
        | nil => simp [runPlans, erasePatterns, matchArgs]
        | cons subject subjects =>
            simp only [runPlans, erasePatterns, matchArgs]
            rw [run_eq_matchPattern, runPlans_eq_matchArgs]
  termination_by 2 * patternPlansWork plans + 1
  decreasing_by
    all_goals
      have positive := PatternPlan.work_pos plan
      rw [patternPlansWork]
      omega
end

/-- A successfully compiled matcher has exactly the source match result. -/
theorem run_compilePattern?
    (source subject : Pattern) (compiled : PatternPlan)
    (accepted : compilePattern? source = some compiled) :
    compiled.run subject = matchPattern source subject := by
  rw [run_eq_matchPattern,
    erase_of_compilePattern? source compiled accepted]

/-! ## Right-hand-side construction -/

/-- Instantiate a first-order plan from canonical bindings.  Missing bindings
remain visible variables, matching the existing gradual `applyBindings`
operation. -/
def PatternPlan.instantiate (bindings : Bindings) : PatternPlan -> Pattern
  | .metavariable name =>
      match bindings.find? (fun entry => entry.1 == name) with
      | some (_, value) => value
      | none => .fvar name
  | .bound index => .bvar index
  | .application constructor arguments =>
      .apply constructor (arguments.map (instantiate bindings))

mutual
  /-- Plan instantiation is exactly canonical binding application on erasure. -/
  theorem instantiate_eq_applyBindings
      (bindings : Bindings) (plan : PatternPlan) :
      plan.instantiate bindings = applyBindings bindings plan.erase := by
    cases plan with
    | metavariable name =>
        unfold PatternPlan.instantiate PatternPlan.erase applyBindings
        rfl
    | bound index =>
        unfold PatternPlan.instantiate PatternPlan.erase applyBindings
        rfl
    | application constructor arguments =>
        simpa [PatternPlan.instantiate, PatternPlan.erase, applyBindings] using
          congrArg (Pattern.apply constructor)
            (instantiateList_eq_applyBindings bindings arguments)
  termination_by 2 * plan.work
  decreasing_by
    simp [PatternPlan.work]
    omega

  /-- Ordered-list companion to `instantiate_eq_applyBindings`. -/
  theorem instantiateList_eq_applyBindings
      (bindings : Bindings) (plans : List PatternPlan) :
      plans.map (PatternPlan.instantiate bindings) =
        (erasePatterns plans).map (applyBindings bindings) := by
    cases plans with
    | nil => rfl
    | cons plan plans =>
        change plan.instantiate bindings ::
            plans.map (PatternPlan.instantiate bindings) =
          applyBindings bindings plan.erase ::
            (erasePatterns plans).map (applyBindings bindings)
        rw [instantiate_eq_applyBindings, instantiateList_eq_applyBindings]
  termination_by 2 * patternPlansWork plans + 1
  decreasing_by
    all_goals
      have positive := PatternPlan.work_pos plan
      rw [patternPlansWork]
      omega
end

/-! ## Source-bound relation-premise plans -/

/-- A relation query whose ordered arguments are ordinary schema variables.
The source fragment is intentionally narrow: a query cannot smuggle a binder,
freshness test, contextual rewrite, quantified premise, or constructed term
through the residual primitive boundary. -/
structure PremisePlan where
  relation : String
  arguments : List String
deriving DecidableEq, Repr

/-- Compile an ordered row of ordinary schema variables. -/
def compileArgumentNames? : List Pattern -> Option (List String)
  | [] => some []
  | .fvar name :: arguments => do
      let tail <- compileArgumentNames? arguments
      pure (name :: tail)
  | _ => none

/-- Compile exactly the source-bound relation-query fragment. -/
def compilePremise? : Premise -> Option PremisePlan
  | .relationQuery relation arguments => do
      let names <- compileArgumentNames? arguments
      pure { relation, arguments := names }
  | .freshness _ | .congruence _ _ | .forAll _ _ _ => none

/-- Compile a complete authored premise row without dropping or reordering an
occurrence. -/
def compilePremises? : List Premise -> Option (List PremisePlan)
  | [] => some []
  | premise :: premises => do
      let plan <- compilePremise? premise
      let plans <- compilePremises? premises
      pure (plan :: plans)

/-- Reconstruct the complete authored premise represented by a plan. -/
def PremisePlan.erase (plan : PremisePlan) : Premise :=
  .relationQuery plan.relation (plan.arguments.map Pattern.fvar)

/-- Reconstruct an ordered authored premise row. -/
def erasePremisePlans (plans : List PremisePlan) : List Premise :=
  plans.map PremisePlan.erase

private theorem compileArgumentNames?_erase
    (sources : List Pattern) (names : List String)
    (accepted : compileArgumentNames? sources = some names) :
    names.map Pattern.fvar = sources := by
  induction sources generalizing names with
  | nil =>
      simp [compileArgumentNames?] at accepted
      subst names
      rfl
  | cons source sources inductionHypothesis =>
      cases source with
      | fvar name =>
          simp only [compileArgumentNames?, Option.bind_eq_bind] at accepted
          cases tailAccepted : compileArgumentNames? sources with
          | none => simp [tailAccepted] at accepted
          | some tail =>
              simp [tailAccepted] at accepted
              subst names
              simp [inductionHypothesis tail tailAccepted]
      | _ => simp [compileArgumentNames?] at accepted

/-- Successful premise compilation retains its complete source syntax. -/
theorem erase_of_compilePremise?
    (source : Premise) (compiled : PremisePlan)
    (accepted : compilePremise? source = some compiled) :
    compiled.erase = source := by
  cases source with
  | freshness condition => simp [compilePremise?] at accepted
  | congruence left right => simp [compilePremise?] at accepted
  | forAll collection parameter body => simp [compilePremise?] at accepted
  | relationQuery relation arguments =>
      simp only [compilePremise?, Option.bind_eq_bind] at accepted
      cases namesAccepted : compileArgumentNames? arguments with
      | none => simp [namesAccepted] at accepted
      | some names =>
          simp [namesAccepted] at accepted
          subst compiled
          simp [PremisePlan.erase,
            compileArgumentNames?_erase arguments names namesAccepted]

/-- Successful row compilation retains premise order and multiplicity. -/
theorem erasePremisePlans_of_compilePremises?
    (source : List Premise) (compiled : List PremisePlan)
    (accepted : compilePremises? source = some compiled) :
    erasePremisePlans compiled = source := by
  induction source generalizing compiled with
  | nil =>
      simp [compilePremises?] at accepted
      subst compiled
      rfl
  | cons premise premises inductionHypothesis =>
      simp only [compilePremises?, Option.bind_eq_bind] at accepted
      cases headAccepted : compilePremise? premise with
      | none => simp [headAccepted] at accepted
      | some plan =>
          cases tailAccepted : compilePremises? premises with
          | none => simp [headAccepted, tailAccepted] at accepted
          | some plans =>
              simp [headAccepted, tailAccepted] at accepted
              subst compiled
              change plan.erase :: erasePremisePlans plans =
                premise :: premises
              rw [erase_of_compilePremise? premise plan headAccepted,
                inductionHypothesis plans tailAccepted]

/-- Execute one residual relation query.  The only semantic primitive is the
declared finite relation table; matching, merge behavior, builtins, and output
bindings remain fixed by the shared MeTTaIL relation-query semantics. -/
def PremisePlan.run (relations : RelationEnv) (language : LanguageDef)
    (bindings : Bindings) (plan : PremisePlan) : List Bindings :=
  relationQueryStep relations language bindings plan.relation
    (plan.arguments.map Pattern.fvar)

/-- Execute source-bound relation premises in authored order. -/
def runPremisePlans (relations : RelationEnv) (language : LanguageDef) :
    List PremisePlan -> Bindings -> List Bindings
  | [], bindings => [bindings]
  | plan :: plans, bindings =>
      (plan.run relations language bindings).flatMap
        (runPremisePlans relations language plans)

/-- One residual query has exactly the ordinary non-contextual premise
meaning of its erased source. -/
theorem PremisePlan.run_eq_premiseStepUsing
    (relations : RelationEnv) (language : LanguageDef)
    (recursiveStep : Pattern -> List Pattern)
    (bindings : Bindings) (plan : PremisePlan) :
    plan.run relations language bindings =
      premiseStepUsing (engineBasePremises relations) language recursiveStep
        bindings plan.erase := by
  rfl

/-- The residual ordered query program is exactly the authored premise
interpreter. -/
theorem runPremisePlans_eq_premisesUsing
    (relations : RelationEnv) (language : LanguageDef)
    (recursiveStep : Pattern -> List Pattern)
    (plans : List PremisePlan) (bindings : Bindings) :
    runPremisePlans relations language plans bindings =
      premisesUsing (engineBasePremises relations) language recursiveStep
        (erasePremisePlans plans) bindings := by
  induction plans generalizing bindings with
  | nil => rfl
  | cons plan plans inductionHypothesis =>
      simp only [runPremisePlans, erasePremisePlans, List.map_cons,
        premisesUsing]
      rw [PremisePlan.run_eq_premiseStepUsing]
      congr 1
      funext nextBindings
      exact inductionHypothesis nextBindings

/-! ## Complete first-order rewrite-row plans -/

/-- An admitted row preserves the authored administrative fields while
replacing both executable patterns by independent first-order plans. -/
structure RulePlan where
  name : String
  typeContext : List (String × TypeExpr)
  premises : List PremisePlan
  left : PatternPlan
  right : PatternPlan
deriving Repr

/-- Compile one complete rewrite row. -/
def compileRule? (source : RewriteRule) : Option RulePlan := do
  let left <- compilePattern? source.left
  let premises <- compilePremises? source.premises
  let right <- compilePattern? source.right
  pure
    { name := source.name
      typeContext := source.typeContext
      premises
      left
      right }

/-- Reconstruct the complete authored rewrite row represented by a plan. -/
def RulePlan.erase (plan : RulePlan) : RewriteRule :=
  { name := plan.name
    typeContext := plan.typeContext
    premises := erasePremisePlans plan.premises
    left := plan.left.erase
    right := plan.right.erase }

/-- Successful row compilation retains every source field exactly. -/
theorem erase_of_compileRule?
    (source : RewriteRule) (compiled : RulePlan)
    (accepted : compileRule? source = some compiled) :
    compiled.erase = source := by
  unfold compileRule? at accepted
  cases leftCompiled : compilePattern? source.left with
  | none => simp [leftCompiled] at accepted
  | some left =>
      cases premisesCompiled : compilePremises? source.premises with
      | none => simp [leftCompiled, premisesCompiled] at accepted
      | some premises =>
          cases rightCompiled : compilePattern? source.right with
          | none =>
              simp [leftCompiled, premisesCompiled, rightCompiled] at accepted
          | some right =>
              simp [leftCompiled, premisesCompiled, rightCompiled] at accepted
              subst compiled
              cases source
              simp [RulePlan.erase,
                erase_of_compilePattern? _ left leftCompiled,
                erasePremisePlans_of_compilePremises? _ premises
                  premisesCompiled,
                erase_of_compilePattern? _ right rightCompiled]

/-- Interpret a plan using one declared relation environment.  Matching,
ordered premise control, and contractum construction all come from the plan;
the relation table is the sole semantic primitive. -/
def RulePlan.run
    (relations : RelationEnv) (language : LanguageDef)
    (plan : RulePlan) (subject : Pattern) : List Pattern :=
  (plan.left.run subject).flatMap fun initialBindings =>
    (runPremisePlans relations language plan.premises initialBindings).map
      fun finalBindings => plan.right.instantiate finalBindings

/-- Plan interpretation agrees exactly with syntactic matching, authored
premise evaluation, and canonical RHS binding application. -/
theorem run_eq_syntactic
    (relations : RelationEnv) (language : LanguageDef)
    (recursiveStep : Pattern -> List Pattern)
    (plan : RulePlan) (subject : Pattern) :
    plan.run relations language subject =
      (matchPattern plan.left.erase subject).flatMap fun initialBindings =>
        (premisesUsing (engineBasePremises relations) language recursiveStep
          (erasePremisePlans plan.premises) initialBindings).map
          fun finalBindings =>
            applyBindings finalBindings plan.right.erase := by
  simp only [RulePlan.run, run_eq_matchPattern,
    instantiate_eq_applyBindings]
  congr 1
  funext initialBindings
  rw [runPremisePlans_eq_premisesUsing]

/-- A successfully compiled row has exactly the independent syntactic rule
meaning of its source row. -/
theorem run_compileRule?
    (relations : RelationEnv) (language : LanguageDef)
    (recursiveStep : Pattern -> List Pattern)
    (source : RewriteRule) (compiled : RulePlan) (subject : Pattern)
    (accepted : compileRule? source = some compiled) :
    compiled.run relations language subject =
      (matchPattern source.left subject).flatMap fun initialBindings =>
        (premisesUsing (engineBasePremises relations) language recursiveStep
          source.premises
          initialBindings).map fun finalBindings =>
            applyBindings finalBindings source.right := by
  have erased := erase_of_compileRule? source compiled accepted
  subst source
  simpa [RulePlan.erase] using
    run_eq_syntactic relations language recursiveStep compiled subject

/-- Successful compilation preserves the complete source rule interpreter,
including authored premise order and recursive congruence behavior. -/
theorem run_compileRule?_eq_applyRuleUsing
    (relations : RelationEnv) (language : LanguageDef)
    (recursiveStep : Pattern -> List Pattern)
    (source : RewriteRule) (compiled : RulePlan) (subject : Pattern)
    (accepted : compileRule? source = some compiled) :
    compiled.run relations language subject =
      Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep.applyRuleUsing
        RuleInterpretation.syntactic (engineBasePremises relations) language
          recursiveStep source subject :=
  run_compileRule? relations language recursiveStep source compiled subject
    accepted

/-! ## Ordered rule-program compilation -/

/-- Compile a complete authored rewrite list without dropping or reordering
rows. -/
def compileRules? : List RewriteRule -> Option (List RulePlan)
  | [] => some []
  | rule :: rules => do
      let plan <- compileRule? rule
      let plans <- compileRules? rules
      pure (plan :: plans)

/-- Erase a compiled rule program back to its authored rows. -/
def eraseRulePlans (plans : List RulePlan) : List RewriteRule :=
  plans.map RulePlan.erase

/-- Successful program compilation retains every authored row, occurrence,
field, and order exactly. -/
theorem eraseRulePlans_of_compileRules?
    (source : List RewriteRule) (compiled : List RulePlan)
    (accepted : compileRules? source = some compiled) :
    eraseRulePlans compiled = source := by
  induction source generalizing compiled with
  | nil =>
      simp [compileRules?] at accepted
      subst compiled
      rfl
  | cons rule rules inductionHypothesis =>
      simp only [compileRules?, Option.bind_eq_bind] at accepted
      cases headCompiled : compileRule? rule with
      | none => simp [headCompiled] at accepted
      | some plan =>
          cases tailCompiled : compileRules? rules with
          | none => simp [headCompiled, tailCompiled] at accepted
          | some plans =>
              simp [headCompiled, tailCompiled] at accepted
              subst compiled
              change plan.erase :: eraseRulePlans plans = rule :: rules
              rw [erase_of_compileRule? rule plan headCompiled,
                inductionHypothesis plans tailCompiled]

/-- A proof-carrying compiled program for one exact authored rewrite list. -/
structure RuleProgram (source : List RewriteRule) where
  plans : List RulePlan
  erase_eq_source : eraseRulePlans plans = source

/-- Compile and package an authored rewrite list when every row belongs to the
explicit first-order fragment. -/
def compileProgram? (source : List RewriteRule) : Option (RuleProgram source) :=
  match accepted : compileRules? source with
  | none => none
  | some plans =>
      some
        { plans
          erase_eq_source :=
            eraseRulePlans_of_compileRules? source plans accepted }

@[simp] theorem RuleProgram.plans_length
    {source : List RewriteRule} (program : RuleProgram source) :
    program.plans.length = source.length := by
  have lengths := congrArg List.length program.erase_eq_source
  simpa [eraseRulePlans] using lengths

/-- Retrieve the compiled plan for an exact authored occurrence. -/
def RuleProgram.planAt
    {source : List RewriteRule} (program : RuleProgram source)
    (occurrence : Fin source.length) : RulePlan :=
  program.plans[occurrence.val]'(by
    rw [program.plans_length]
    exact occurrence.isLt)

/-- Occurrence lookup commutes with erasure; duplicate rows therefore remain
distinct source occurrences even when their contents happen to coincide. -/
theorem RuleProgram.erase_planAt
    {source : List RewriteRule} (program : RuleProgram source)
    (occurrence : Fin source.length) :
    (program.planAt occurrence).erase = source[occurrence] := by
  have planBound : occurrence.val < program.plans.length := by
    rw [program.plans_length]
    exact occurrence.isLt
  have point := congrArg (fun rules => rules[occurrence.val]?)
    program.erase_eq_source
  rw [eraseRulePlans, List.getElem?_map,
    List.getElem?_eq_getElem planBound,
    List.getElem?_eq_getElem occurrence.isLt] at point
  exact Option.some.inj point

/-! ## Discriminating controls -/

private def repeatedSource : Pattern :=
  .apply "Pair" [.fvar "x", .fvar "x"]

private def repeatedPlan : PatternPlan :=
  .application "Pair" [.metavariable "x", .metavariable "x"]

/-- Repeated-variable consistency remains load-bearing after compilation. -/
example :
    repeatedPlan.run
      (.apply "Pair" [.apply "Left" [], .apply "Right" []]) = [] := by
  decide

/-- The same repeated value is accepted with one canonical binding. -/
example :
    repeatedPlan.run
      (.apply "Pair" [.apply "Left" [], .apply "Left" []]) =
        [[("x", .apply "Left" [])]] := by
  decide

/-- Binder-bearing syntax is outside this first-order backend and is rejected. -/
example : compilePattern? (.lambda (some "x") (.bvar 0)) = none := by
  rfl

/-- The positive fixture is genuinely compiled from its source. -/
example : compilePattern? repeatedSource = some repeatedPlan := by
  rfl

#print axioms erase_of_compilePattern?
#print axioms run_compilePattern?
#print axioms instantiate_eq_applyBindings
#print axioms erase_of_compilePremise?
#print axioms erasePremisePlans_of_compilePremises?
#print axioms runPremisePlans_eq_premisesUsing
#print axioms erase_of_compileRule?
#print axioms run_compileRule?
#print axioms run_compileRule?_eq_applyRuleUsing
#print axioms eraseRulePlans_of_compileRules?
#print axioms RuleProgram.erase_planAt

end Mettapedia.GSLT.LanguageDef.MeTTaILFirstOrderRuleCompilation
