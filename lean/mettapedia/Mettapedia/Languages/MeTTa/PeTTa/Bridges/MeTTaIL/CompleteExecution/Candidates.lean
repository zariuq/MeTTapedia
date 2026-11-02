import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.Decompositions
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.VariantSides
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.ScopedSource
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.DescentHelpers
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompletePlanWire

/-!
# Matching to completion and the predecessors of a term

`gslt:complete:matcher-finish` ticks the scoped matcher until it is complete, as
`finishMatcher`; it stops because every tick lowers the matcher's agenda cost.
`gslt:complete:predecessors` lists the candidate sources of equation instances into a term, as
`Complete.Predecessors.predecessors`: at every position, every match of an equation's right side,
the left side rebuilt from the match, each of its variants put back into the context.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution

open Mettapedia.GSLT.LanguageDef CettaWire InferenceCettaWire
open Mettapedia.OSLF.MeTTaIL Syntax DerivedContexts ScopedRuleMatching RuleBinding
open Mettapedia.OSLF.MeTTaIL.Complete.Inversion (variants)
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Effects (State)
open Eval
open BridgeKit WireKit
open RuleInstantiationExecution.GeneralExecution (matcherRequestTerm matcherStateTerm matcherAnswerTerm)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst)

abbrev requestValue (request : GeneralScopedMatchMachine.Request) : Atom := encoded (matcherRequestTerm request)
abbrev matcherValue (machine : GeneralScopedMatchMachine.State) : Atom := encoded (matcherStateTerm machine)

theorem complete_matcher_start_returns (state : State) (request : GeneralScopedMatchMachine.Request) :
    PureReturns runtime [] state (apply "gslt:rule:scope-matcher-start" [requestValue request]) state
      (matcherValue (GeneralScopedMatchMachine.start request)) := by
  exact descent_matcher_start_returns state request

theorem complete_matcher_tick_returns (state : State) (request : GeneralScopedMatchMachine.Request)
    (machine : GeneralScopedMatchMachine.State) :
    PureReturns runtime [] state (apply "gslt:rule:scope-matcher-tick" [requestValue request, matcherValue machine])
      state (matcherValue (GeneralScopedMatchMachine.tick request machine)) := by
  exact descent_matcher_tick_returns state request machine

theorem complete_matcher_complete_returns (state : State) (machine : GeneralScopedMatchMachine.State) :
    PureReturns runtime [] state (apply "gslt:rule:scope-matcher-complete" [matcherValue machine]) state
      (Effects.boolean (GeneralScopedMatchMachine.complete machine)) := by
  exact descent_matcher_complete_returns state machine

/-- **`gslt:complete:matcher-finish` is `finishMatcher`.** -/
@[metta_head "gslt:complete:matcher-finish"]
theorem matcher_finish_returns (state : State) (request : GeneralScopedMatchMachine.Request)
    (machine : GeneralScopedMatchMachine.State) :
    PureReturns runtime [] state (apply "gslt:complete:matcher-finish" [requestValue request, matcherValue machine])
      state (matcherValue (GeneralEquationJobExecution.finishMatcher request machine)) := by
  have checked := complete_matcher_complete_returns state machine
  by_cases finished : GeneralScopedMatchMachine.complete machine = true
  · rw [GeneralEquationJobExecution.finishMatcher_finished request machine finished]
    metta_call_in completeProof_checked using completeProof_agreement
    metta_eval [checked] with completeProof_checked in completeProof_agreement unfolding [finished]
  · have pending : GeneralScopedMatchMachine.complete machine = false := by simpa using finished
    rw [← GeneralEquationJobExecution.finishMatcher_tick request machine pending]
    have ticked := complete_matcher_tick_returns state request machine
    have later := matcher_finish_returns state request (GeneralScopedMatchMachine.tick request machine)
    metta_call_in completeProof_checked using completeProof_agreement
    metta_eval [checked, ticked, later] with completeProof_checked in completeProof_agreement unfolding [pending]
termination_by GeneralScopedMatchMachine.agendaCost request machine.agenda
decreasing_by exact GeneralScopedMatchMachine.tick_cost (Bool.eq_false_iff.mpr finished)

/-- The answers of the matcher run to completion from its start. -/
def finishedAnswers (request : GeneralScopedMatchMachine.Request) : List GeneralScopedMatchMachine.Answer :=
  (GeneralEquationJobExecution.finishMatcher request (GeneralScopedMatchMachine.start request)).answers

@[metta_head "gslt:complete:matcher-answers"]
theorem matcher_answers_returns (state : State) (request : GeneralScopedMatchMachine.Request) :
    PureReturns runtime [] state (apply "gslt:complete:matcher-answers" [requestValue request]) state
      (encoded (CettaWire.encodeList matcherAnswerTerm (finishedAnswers request))) := by
  metta_call_in completeProof_checked using completeProof_agreement
  metta_eval [complete_matcher_start_returns state request,
      matcher_finish_returns state request (GeneralScopedMatchMachine.start request)]
    with completeProof_checked in completeProof_agreement unfolding [matcherValue, matcherStateTerm, finishedAnswers]

/-- Every rebuilt left side's variants, filled into the context and erased. -/
def candidatesFrom (rule : RewriteRule) (spec : RuleBindingSpec) (ambient : Nat) (context : OneHoleContext)
    (captures : List Assignment) : List Pattern :=
  captures.flatMap fun captured =>
    match instantiateAt? rule spec ambient .left [] 0 captured rule.left with
    | none => []
    | some rebuilt => (variants rule.left rebuilt).map fun source => (context.fill source).eraseBinderMetadata

@[metta_head "gslt:complete:fill-each"]
theorem fill_each_returns (state : State) (context : OneHoleContext) : ∀ sources : List Pattern,
    PureReturns runtime [] state (apply "gslt:complete:fill-each" [contextValue context, patternsValue sources]) state
      (patternsValue (sources.map fun source => (context.fill source).eraseBinderMetadata))
  | [] => by
    metta_call_in completeProof_checked using completeProof_agreement
    metta_eval with completeProof_checked in completeProof_agreement unfolding [patternsValue, encodePatterns]
  | source :: rest => by
    metta_call_in completeProof_checked using completeProof_agreement
    metta_eval [complete_fill_returns state context source, erase_returns state (context.fill source),
        fill_each_returns state context rest] with completeProof_checked in completeProof_agreement
      unfolding [patternsValue, encodePatterns, patternValue]

theorem complete_instantiate_returns (state : State) (rule : RewriteRule) (spec : RuleBindingSpec) (ambient : Nat)
    (site : RulePatternSite) (path : List Nat) (depth : Nat) (assignment : Assignment) (pattern : Pattern) :
    PureReturns runtime [] state
      (apply "gslt:rule:scope-instantiate-at"
        [.symbol "None", encoded (InferenceCettaWire.AuthoredRule.rewriteTerm rule),
         encoded (InferenceCettaWire.AuthoredRule.bindingSpecTerm spec), number ambient,
         encoded (InferenceCettaWire.AuthoredRule.siteTerm site), encoded (CettaWire.encodeList Term.natural path),
         number depth, assignmentValue assignment, encoded (InferenceCettaWire.encodePattern pattern)])
      state (encoded (MatchAutomataBindingExecution.patternOptionTerm
        (instantiateAt? rule spec ambient site path depth assignment pattern))) := by
  exact descent_instantiate_returns state rule spec ambient site path depth assignment pattern

theorem matcher_answer_term' (answer : GeneralScopedMatchMachine.Answer) :
    matcherAnswerTerm answer = .application "ScopedMatcherAnswer"
      [RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm answer.assignment,
        RuleInstantiationExecution.GeneralExecution.traceTerm answer.trace] := rfl

@[metta_head "gslt:complete:candidates-from"]
theorem candidates_from_returns (state : State) (rule : RewriteRule) (spec : RuleBindingSpec) (ambient : Nat)
    (context : OneHoleContext) : ∀ answers : List GeneralScopedMatchMachine.Answer,
    PureReturns runtime [] state
      (apply "gslt:complete:candidates-from" [encoded (InferenceCettaWire.AuthoredRule.rewriteTerm rule),
        encoded (InferenceCettaWire.AuthoredRule.bindingSpecTerm spec), number ambient, contextValue context,
        encoded (CettaWire.encodeList matcherAnswerTerm answers)])
      state (patternsValue (candidatesFrom rule spec ambient context (answers.map (·.assignment))))
  | [] => by
    metta_call_in completeProof_checked using completeProof_agreement
    metta_eval with completeProof_checked in completeProof_agreement unfolding [patternsValue, encodePatterns, candidatesFrom]
  | answer :: rest => by
    have tail := candidates_from_returns state rule spec ambient context rest
    have rebuilt := complete_instantiate_returns state rule spec ambient .left [] 0 answer.assignment rule.left
    cases instantiated : instantiateAt? rule spec ambient .left [] 0 answer.assignment rule.left with
    | none =>
      metta_call_in completeProof_checked using completeProof_agreement
      metta_eval [tail, rebuilt] with completeProof_checked in completeProof_agreement
        unfolding [patternsValue, encodePatterns, candidatesFrom, instantiated, matcher_answer_term',
          InferenceCettaWire.AuthoredRule.rewriteTerm, InferenceCettaWire.AuthoredRule.siteTerm,
          MatchAutomataBindingExecution.patternOptionTerm, List.map_cons, List.flatMap_cons]
    | some built =>
      have sources := variants_returns state rule.left built
      have filled := fill_each_returns state context (variants rule.left built)
      have joined := complete_append_patterns state
        ((variants rule.left built).map fun source => (context.fill source).eraseBinderMetadata)
        (candidatesFrom rule spec ambient context (rest.map (·.assignment)))
      rw [show candidatesFrom rule spec ambient context ((answer :: rest).map (·.assignment)) =
          (variants rule.left built).map (fun source => (context.fill source).eraseBinderMetadata) ++
            candidatesFrom rule spec ambient context (rest.map (·.assignment)) by
        simp [candidatesFrom, instantiated]]
      metta_call_in completeProof_checked using completeProof_agreement
      metta_eval [tail, rebuilt, sources, filled, joined] with completeProof_checked in completeProof_agreement
        unfolding [patternsValue, encodePatterns, instantiated, matcher_answer_term',
          InferenceCettaWire.AuthoredRule.rewriteTerm, InferenceCettaWire.AuthoredRule.siteTerm,
          MatchAutomataBindingExecution.patternOptionTerm, List.map_cons, List.flatMap_cons, VariantsAt]

/-- The request matching an equation's right side, as the MeTTa body builds it. -/
theorem right_request_term (rule : RewriteRule) (spec : RuleBindingSpec) (ambient : Nat) (focus : Pattern) :
    matcherRequestTerm ⟨rule, spec, ambient, .right, [], 0, [], rule.right, focus⟩ =
      .application "ScopedMatcherRequest" [InferenceCettaWire.AuthoredRule.rewriteTerm rule,
        InferenceCettaWire.AuthoredRule.bindingSpecTerm spec, .natural ambient, .symbol "RuleRight", .symbol "LNil",
        .natural 0, .symbol "LNil", InferenceCettaWire.encodePattern rule.right, InferenceCettaWire.encodePattern focus] :=
  rfl

/-- The plan as MeTTa data, with a free-type table. -/
abbrev planValue (plan : GeneralExecutionAdmission.Plan) (table : List (String × TypeExpr)) (bound : List TypeExpr)
    (expected : TypeExpr) : Atom :=
  encoded (CompletePlanWire.planTerm plan table bound expected)

/-- The candidates of the equations at one position. -/
def equationCandidates (ambient : Nat) (context : OneHoleContext) (focus : Pattern)
    (equations : List GeneralExecutionAdmission.EquationPlan) : List Pattern :=
  equations.flatMap fun equation =>
    candidatesFrom equation.rule equation.binding.spec ambient context
      (Complete.Predecessors.rightMatches equation ambient focus)

@[metta_head "gslt:complete:equation-candidates"]
theorem equation_candidates_returns (state : State) (plan : GeneralExecutionAdmission.Plan) (ambient : Nat)
    (context : OneHoleContext) (focus : Pattern) : ∀ pairs : List (GeneralExecutionAdmission.EquationPlan × Nat),
    PureReturns runtime [] state
      (apply "gslt:complete:equation-candidates" [encoded (CettaWire.encodeList (CompletePlanWire.equationDeclarationTerm plan) pairs),
        number ambient, contextValue context, patternValue focus])
      state (patternsValue (equationCandidates ambient context focus (pairs.map Prod.fst)))
  | [] => by
    metta_call_in completeProof_checked using completeProof_agreement
    metta_eval with completeProof_checked in completeProof_agreement unfolding [patternsValue, encodePatterns, equationCandidates]
  | (equation, position) :: rest => by
    have tail := equation_candidates_returns state plan ambient context focus rest
    have answers := matcher_answers_returns state ⟨equation.rule, equation.binding.spec, ambient, .right, [], 0, [],
      equation.rule.right, focus⟩
    have candidates := candidates_from_returns state equation.rule equation.binding.spec ambient context
      (finishedAnswers ⟨equation.rule, equation.binding.spec, ambient, .right, [], 0, [], equation.rule.right, focus⟩)
    have joined := complete_append_patterns state
      (candidatesFrom equation.rule equation.binding.spec ambient context
        (Complete.Predecessors.rightMatches equation ambient focus))
      (equationCandidates ambient context focus (rest.map Prod.fst))
    rw [show equationCandidates ambient context focus (((equation, position) :: rest).map Prod.fst) =
        candidatesFrom equation.rule equation.binding.spec ambient context
          (Complete.Predecessors.rightMatches equation ambient focus) ++
          equationCandidates ambient context focus (rest.map Prod.fst) by
      simp [equationCandidates]]
    metta_call_in completeProof_checked using completeProof_agreement
    metta_eval [tail, answers, candidates, joined] with completeProof_checked in completeProof_agreement
      unfolding [CompletePlanWire.equationDeclarationTerm, InferenceCettaWire.AuthoredRule.rewriteTerm,
        right_request_term, requestValue, Complete.Predecessors.rightMatches, finishedAnswers]

/-- The candidates at every listed position. -/
def positionCandidates (plan : GeneralExecutionAdmission.Plan) (bound : List TypeExpr)
    (decompositions : List (OneHoleContext × Pattern)) : List Pattern :=
  decompositions.flatMap fun (context, focus) =>
    equationCandidates (bound.length + Complete.Predecessors.binderDepth context) context focus plan.equations

theorem zipIdx_map_fst {α : Type} (items : List α) (start : Nat) : (items.zipIdx start).map Prod.fst = items := by
  induction items generalizing start with
  | nil => rfl
  | cons item rest ih => simp [List.zipIdx_cons, ih]

@[metta_head "gslt:complete:predecessors-from"]
theorem predecessors_from_returns (state : State) (plan : GeneralExecutionAdmission.Plan)
    (table : List (String × TypeExpr)) (planBound : List TypeExpr) (expected : TypeExpr) (bound : List TypeExpr) :
    ∀ decompositions : List (OneHoleContext × Pattern),
    PureReturns runtime [] state
      (apply "gslt:complete:predecessors-from" [planValue plan table planBound expected,
        encoded (CettaWire.encodeList InferenceCettaWire.AuthoredRule.typeTerm bound), decompositionsValue decompositions])
      state (patternsValue (positionCandidates plan bound decompositions))
  | [] => by
    metta_call_in completeProof_checked using completeProof_agreement
    metta_eval with completeProof_checked in completeProof_agreement unfolding [patternsValue, encodePatterns, positionCandidates, decompositionsValue]
  | (context, focus) :: rest => by
    have tail := predecessors_from_returns state plan table planBound expected bound rest
    have outer := complete_length_returns InferenceCettaWire.AuthoredRule.typeTerm state bound
    have inner := binder_depth_returns state context
    have here := equation_candidates_returns state plan (bound.length + Complete.Predecessors.binderDepth context)
      context focus plan.equations.zipIdx
    have joined := complete_append_patterns state
      (equationCandidates (bound.length + Complete.Predecessors.binderDepth context) context focus plan.equations)
      (positionCandidates plan bound rest)
    rw [zipIdx_map_fst] at here
    rw [show positionCandidates plan bound ((context, focus) :: rest) =
        equationCandidates (bound.length + Complete.Predecessors.binderDepth context) context focus plan.equations ++
          positionCandidates plan bound rest by simp [positionCandidates]]
    metta_call_in completeProof_checked using completeProof_agreement
    metta_eval [tail, outer, inner, here, joined] with completeProof_checked in completeProof_agreement
      unfolding [planValue, CompletePlanWire.planTerm, decompositionsValue, decompositionTerm, contextValue,
        patternValue]

private theorem equation_list_empty_returns {α : Type} (caller : Subst) (state : State)
    (encode : α → CettaWire.Term) (values : List α)
    (read : applySubst caller (.var "equations") = encoded (CettaWire.encodeList encode values)) :
    PureReturns runtime caller state (apply "==" [.var "equations", .symbol "LNil"]) state
      (Effects.boolean values.isEmpty) := by
  have left := variable_returns runtime caller state "equations"
  rw [read] at left
  have compared := term_equal_returns runtime caller state (.var "equations") (.symbol "LNil")
    (CettaWire.encodeList encode values) (.symbol "LNil") left (Eval.symbol_returns runtime caller state "LNil")
  cases values <;> simpa [CettaWire.encodeList] using compared

/-- **`gslt:complete:predecessors` is `Predecessors.predecessors`.** -/
@[metta_head "gslt:complete:predecessors"]
theorem predecessors_returns (state : State) (plan : GeneralExecutionAdmission.Plan)
    (table : List (String × TypeExpr)) (bound : List TypeExpr) (expected : TypeExpr) (target : Pattern) :
    PureReturns runtime [] state
      (apply "gslt:complete:predecessors" [planValue plan table bound expected, patternValue target])
      state (patternsValue (Complete.Predecessors.predecessors plan bound target)) := by
  cases equations : plan.equations with
  | nil =>
      rw [Complete.Predecessors.predecessors_eq_nil_of_no_equations plan bound target equations]
      metta_call_in completeProof_checked using completeProof_agreement
      metta_eval with completeProof_checked in completeProof_agreement
        unfolding [planValue, CompletePlanWire.planTerm, patternsValue, encodePatterns, equations]
      apply pure_if_returns (value := true)
      · simpa only [List.isEmpty_nil] using
          equation_list_empty_returns _ state (CompletePlanWire.equationDeclarationTerm plan) [] rfl
      · metta_eval with completeProof_checked in completeProof_agreement unfolding [patternsValue, encodePatterns]
  | cons equation rest =>
      have positions := decompositions_returns state target
      have candidates := predecessors_from_returns state plan table bound expected bound
        (Complete.Predecessors.decompositions target)
      rw [show Complete.Predecessors.predecessors plan bound target =
          positionCandidates plan bound (Complete.Predecessors.decompositions target) from rfl]
      metta_call_in completeProof_checked using completeProof_agreement
      metta_eval [positions, candidates] with completeProof_checked in completeProof_agreement
        unfolding [planValue, CompletePlanWire.planTerm, Decomposes, equations]
      apply pure_if_returns (value := false)
      · simpa only [List.isEmpty_cons] using
          equation_list_empty_returns _ state (CompletePlanWire.equationDeclarationTerm plan)
            ((equation, 0) :: rest.zipIdx 1) rfl
      · metta_eval [positions, candidates] with completeProof_checked in completeProof_agreement
          unfolding [planValue, CompletePlanWire.planTerm, Decomposes, equations]

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution

#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.complete_matcher_start_returns
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.complete_matcher_tick_returns
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.complete_matcher_complete_returns
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.matcher_finish_returns
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.matcher_answers_returns
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.fill_each_returns
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.complete_instantiate_returns
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.matcher_answer_term'
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.candidates_from_returns
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.right_request_term
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.equation_candidates_returns
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.zipIdx_map_fst
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.predecessors_from_returns
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.predecessors_returns
