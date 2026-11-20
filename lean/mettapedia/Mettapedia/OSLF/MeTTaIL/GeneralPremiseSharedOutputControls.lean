import Mettapedia.OSLF.MeTTaIL.StructuralDescentCoverage
import Mettapedia.GSLT.LanguageDef.CollectionConsumers
import Mettapedia.GSLT.LanguageDef.CollectionConsumerControls
import Mettapedia.OSLF.Framework.GeneralReferenceAgreement
import Mettapedia.GSLT.LanguageDef.EquationSemantics
import Mettapedia.OSLF.MeTTaIL.CoreLanguageDef
import Mettapedia.OSLF.MeTTaIL.GeneralPremiseCollectionInputTransport
import Mettapedia.OSLF.MeTTaIL.ReferenceStepEquations
import Mettapedia.OSLF.MeTTaIL.Complete.Exhaustion
import Mettapedia.OSLF.MeTTaIL.GeneralExecutionTotalAdmission
import Mettapedia.OSLF.MeTTaIL.GeneralPremiseExecutionCoverage
import Mettapedia.OSLF.MeTTaIL.ReferenceStepExecution
import Mettapedia.OSLF.MeTTaIL.CanonicalBags
import Mettapedia.OSLF.MeTTaIL.RecursiveCollectionHandoff

/-!
# Compiled shared provider outputs and lexical quantification

Provider declarations with identical values remain distinct occurrences.
A later output matches the retained binding rather than replacing it. The
quantified parameter shadows an outer capture only while its body runs;
preexisting outer outputs remain fixed and body outputs stay local. Empty quantification leaves an absent
output absent, and the compiler rejects relying on that output afterwards.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralPremise.SharedOutputControls

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax RuleBinding ScopedRuleMatching Execution GeneralExecutionAdmission

def term : TypeExpr := .base "Term"
def zero : Pattern := .apply "Zero" []
def one : Pattern := .apply "Successor" [zero]

def quantifiedBody : Premise := .relationQuery "share" [.fvar "Y", .fvar "element"]
def quantified : Premise := .forAll "L" "element" quantifiedBody

def rule : RewriteRule where
  name := "shared-provider-output"
  typeContext := [("element", term), ("L", .collection .vec term), ("Y", term)]
  left := .apply "Wrap" [.fvar "element", .collection .vec [] (some "L")]
  right := .apply "Accept" [.fvar "Y", .fvar "element"]
  premises := [.relationQuery "choose" [.fvar "Y"], quantified,
    .relationQuery "confirm" [.fvar "Y"]]

def language : LanguageDef where
  name := "compiled-shared-output-quantification"
  types := ["Term"]
  terms := [
    {label := "Zero", category := "Term", params := [], syntaxPattern := []},
    {label := "Successor", category := "Term", params := [.simple "term" term], syntaxPattern := []},
    {label := "Wrap", category := "Term", params := [
      .simple "outer" term, .simple "elements" (.collection .vec term)], syntaxPattern := []},
    {label := "Accept", category := "Term", params := [
      .simple "answer" term, .simple "outer" term], syntaxPattern := []}]
  equations := []
  rewrites := [rule]

def provider : ProviderSnapshot where
  signatures := [⟨"choose", [term], [.output]⟩,
    ⟨"share", [term, term], [.output, .input]⟩,
    ⟨"confirm", [term], [.output]⟩]
  rows := [⟨"choose", [zero]⟩, ⟨"choose", [zero]⟩,
    ⟨"share", [zero, zero]⟩, ⟨"share", [one, zero]⟩,
    ⟨"confirm", [one]⟩, ⟨"confirm", [zero]⟩]

def snapshot : Snapshot := ⟨language, [], provider⟩
def permissions : Permissions where
  equationIndices := some []
  includeDerivedEquations := false

def admission : GeneralExecutionTotalAdmission.Admission :=
  GeneralExecutionTotalAdmission.compile snapshot permissions

def plan : Plan := admission.execution

def declaration : RulePlan where
  declarationIndex := 0
  authored := rule
  binding := ⟨GeneralRuleBindingInference.inferredSpec rule, .inferredRootInputs⟩

theorem compiled_binding :
    GeneralRuleBindingInference.compile? language rule = some declaration.binding := by cbv

theorem compiled_premises :
    rulePremisesAdmitted language provider (declaration.binding.elaborate rule)
      declaration.binding.spec = true := by cbv

theorem compiled_templates :
    GeneralEquationCanonicalTemplates.checkRule rule = true ∧
      GeneralEquationCanonicalTemplates.checkBinding declaration.binding.spec = true := by decide +kernel

theorem compiled_rules : plan.rules = [declaration] := by
  have selected : selectedRules snapshot permissions = [(rule, 0)] := rfl
  unfold plan admission GeneralExecutionTotalAdmission.compile GeneralExecutionAdmission.compile
    GeneralExecutionAdmission.rules
  rw [selected]
  simp only [List.filterMap_cons, List.filterMap_nil, rulePlan?, Option.bind_eq_bind,
    show snapshot.language = language from rfl, show snapshot.provider = provider from rfl,
    compiled_binding, Option.bind_some, compiled_premises, compiled_templates.1,
    compiled_templates.2, Bool.and_self, ↓reduceIte]
  rfl

def environment : Environment where
  language := {language with rewrites := [declaration.rule]}
  free := snapshot.free
  provider := snapshot.provider
  specifications := [(0, declaration.binding.spec)]
  reflection := permissions.reflection

theorem environment_actual : GeneralPlanEnvironment.environment plan = environment := by
  unfold GeneralPlanEnvironment.environment
  rw [compiled_rules]
  rfl

def source (elements : List Pattern) : Pattern :=
  .apply "Wrap" [one, .collection .vec elements none]

def rootGoal (elements : List Pattern) : Goal := .root [] term (source elements) 0
def rootState (elements : List Pattern) : State environment (rootGoal elements) :=
  run environment (rootGoal elements) 400 (start environment (rootGoal elements))

def rootTarget {executionEnvironment : Environment} (elements : List Pattern) :
    Result executionEnvironment (rootGoal elements) → Pattern
  | .root _ _ _ _ target _ => target

def rootAssignment {executionEnvironment : Environment} (elements : List Pattern) :
    Result executionEnvironment (rootGoal elements) → Assignment
  | .root _ _ completed _ _ _ => completed

def queryRow? : Event → Option Nat
  | .query _ _ row _ => some row
  | _ => none

def queryRows : Event → List Nat
  | .query _ _ row _ => [row]
  | .quantified _ _ _ elements =>
      elements.flatMap fun element => element.2.2.filterMap queryRow?
  | _ => []

def rootRows {executionEnvironment : Environment} (elements : List Pattern) :
    Result executionEnvironment (rootGoal elements) → List Nat
  | .root _ _ _ events _ _ => events.flatMap queryRows

def readBody (assignment : Assignment) (name : String) : Option Pattern :=
  (lookup assignment name).map ContextualValue.body

theorem whole_profile_accepted : admission.complete = true := by cbv

theorem actual_compiled_rule : plan.rules.map RulePlan.declarationIndex = [0] := by
  rw [compiled_rules]
  rfl

theorem root_keeps_duplicate_provider_origins :
    (rootState [zero, zero]).answers.map (rootRows [zero, zero]) =
      [[0, 2, 2, 5], [1, 2, 2, 5]] := by decide +kernel

theorem conflicting_later_rows_do_not_overwrite :
    (rootState [zero, zero]).answers.map (rootTarget [zero, zero]) =
      [.apply "Accept" [zero, one], .apply "Accept" [zero, one]] := by decide +kernel

theorem root_preserves_global_output_and_outer_parameter :
    (rootState [zero, zero]).answers.map (fun answer =>
      (readBody (rootAssignment [zero, zero] answer) "Y",
        readBody (rootAssignment [zero, zero] answer) "element")) =
      [(some zero, some one), (some zero, some one)] := by decide +kernel

theorem root_search_completed :
    complete environment (rootGoal [zero, zero]) (rootState [zero, zero]) = true := by decide +kernel

theorem root_empty_quantification_keeps_only_preexisting_output :
    (rootState []).answers.map (rootRows []) = [[0, 5], [1, 5]] ∧
      (rootState []).answers.map (rootTarget []) =
        [.apply "Accept" [zero, one], .apply "Accept" [zero, one]] := by decide +kernel

/-- The local consumer's declaration and binding plan have an exact compiled
position; no rule-name lookup or fallback is used. -/
def compiledRule : RulePlan := declaration
theorem compiled_rule_selected : plan.rules[0]? = some compiledRule := by
  rw [compiled_rules]
  rfl

def context : Context := ⟨0, compiledRule.rule, compiledRule.binding.spec, [], 1, 0⟩

def captures (elements : List Pattern) : Assignment :=
  [("L", localValue [] (.collection .vec elements none)), ("element", localValue [] one)]

theorem captures_from_actual_root_matching :
    matchRuleAt compiledRule.rule compiledRule.binding.spec 0 (source [zero, zero]) =
      [captures [zero, zero]] := by decide +kernel

def quantifierGoal (elements : List Pattern) : Goal :=
  .premise context quantified (captures elements)

def quantifierState (elements : List Pattern) : State environment (quantifierGoal elements) :=
  run environment (quantifierGoal elements) 200 (start environment (quantifierGoal elements))

def quantifierAssignment (elements : List Pattern) : Result environment (quantifierGoal elements) → Assignment
  | .premise completed _ _ => completed

def quantifierOrigins (elements : List Pattern) : Result environment (quantifierGoal elements) →
    List (Nat × Pattern × List Nat)
  | .premise _ event _ => match event with
    | .quantified _ _ _ entries => entries.map fun entry =>
        (entry.1, entry.2.1, entry.2.2.filterMap queryRow?)
    | _ => []

theorem nonempty_quantification_keeps_body_outputs_local :
    (quantifierState [zero, zero]).answers.map (fun answer =>
      (readBody (quantifierAssignment [zero, zero] answer) "Y",
        readBody (quantifierAssignment [zero, zero] answer) "element")) =
      [(none, some one), (none, some one), (none, some one), (none, some one)] := by decide +kernel

theorem quantified_duplicates_keep_independent_body_origins :
    (quantifierState [zero, zero]).answers.map (quantifierOrigins [zero, zero]) =
      [[(0, zero, [2]), (1, zero, [2])], [(0, zero, [2]), (1, zero, [3])],
        [(0, zero, [3]), (1, zero, [2])], [(0, zero, [3]), (1, zero, [3])]] := by decide +kernel

theorem empty_quantification_cannot_manufacture_a_binding :
    (quantifierState []).answers.map (fun answer =>
      (readBody (quantifierAssignment [] answer) "Y",
        readBody (quantifierAssignment [] answer) "element")) = [(none, some one)] := by decide +kernel

theorem quantifier_search_completed :
    complete environment (quantifierGoal [zero, zero]) (quantifierState [zero, zero]) = true ∧
      complete environment (quantifierGoal []) (quantifierState []) = true := by decide +kernel

def unsafeRule : RewriteRule := {rule with premises := [quantified]}
def unsafeLanguage : LanguageDef := {language with rewrites := [unsafeRule]}
def unsafeSnapshot : Snapshot := {snapshot with language := unsafeLanguage}

theorem empty_capable_output_cannot_supply_required_binding :
    (GeneralExecutionTotalAdmission.compile unsafeSnapshot permissions).complete = false := by cbv

theorem unsafe_rule_retains_actual_flow_obligation :
    GeneralExecutionAdmission.Obligation.rulePremises 0 ∈
      (GeneralExecutionAdmission.compile unsafeSnapshot permissions).obligations := by
  cbv
  exact List.mem_cons_of_mem _ List.mem_cons_self

theorem actual_compiler_executes_shared_output_origins :
    (run (GeneralPlanEnvironment.environment plan) (rootGoal [zero, zero]) 400
      (start (GeneralPlanEnvironment.environment plan) (rootGoal [zero, zero]))).answers.map
      (rootRows [zero, zero]) = [[0, 2, 2, 5], [1, 2, 2, 5]] := by
  rw [environment_actual]
  exact root_keeps_duplicate_provider_origins

#print axioms whole_profile_accepted
#print axioms root_keeps_duplicate_provider_origins
#print axioms nonempty_quantification_keeps_body_outputs_local
#print axioms empty_capable_output_cannot_supply_required_binding

namespace LocalOutputs

/-- The body introduces `Y` locally; the conclusion uses only the enclosing
parameter. Different elements can therefore require different `Y` values. -/
def authoredRule : RewriteRule :=
  {rule with
    name := "independent-quantified-outputs"
    premises := [quantified]
    right := .apply "Accept" [zero, .fvar "element"]}

def authoredLanguage : LanguageDef := {language with rewrites := [authoredRule]}

def selectedLanguage (nested : Bool) : LanguageDef :=
  if nested then {authoredLanguage with rewrites :=
    [{authoredRule with premises := [.forAll "L" "element" quantified]}]}
  else authoredLanguage

def provider (zeroRows : Nat := 1) (oneRow : Bool := true) : ProviderSnapshot where
  signatures := [⟨"share", [term, term], [.output, .input]⟩]
  rows := List.replicate zeroRows ⟨"share", [zero, zero]⟩ ++
    (if oneRow then [⟨"share", [one, one]⟩] else [])

def admission (zeroRows : Nat := 1) (oneRow : Bool := true) (nested : Bool := false) :=
  GeneralExecutionTotalAdmission.compile ⟨selectedLanguage nested, [], provider zeroRows oneRow⟩ permissions

def plan (zeroRows : Nat := 1) (oneRow : Bool := true) (nested : Bool := false) : Plan :=
  (admission zeroRows oneRow nested).execution

def environment (zeroRows : Nat := 1) (oneRow : Bool := true) (nested : Bool := false) : Environment :=
  GeneralPlanEnvironment.environment (plan zeroRows oneRow nested)

def relationEnvironment (zeroRows : Nat := 1) (oneRow : Bool := true) : Engine.RelationEnv where
  tuples := fun relation _ =>
    ((provider zeroRows oneRow).rows.filter (fun row => row.relation == relation)).map (·.values)

def origins : List Event → List (Nat × Pattern × List Nat)
  | [] => []
  | .quantified _ _ _ entries :: rest =>
      entries.map (fun entry => (entry.1, entry.2.1, entry.2.2.filterMap queryRow?)) ++ origins rest
  | _ :: rest => origins rest

def readout {env : Environment} (elements : List Pattern) : Result env (rootGoal elements) →
    Pattern × Option Pattern × Option Pattern × List (Nat × Pattern × List Nat)
  | .root _ _ completed events target _ =>
      (target, readBody completed "Y", readBody completed "element", origins events)

def completeReadout {env : Environment} (elements : List Pattern) : Result env (rootGoal elements) → String
  | .root trace captured completed events target _ => reprStr (trace, captured, completed, events, target)

def controls : IO Unit := do
  for (nested, zeroRows, oneRow, elements, expected) in [
      (false, 1, true, [zero, one], 1), (false, 2, true, [zero, one], 2),
      (false, 1, false, [zero, one], 0), (false, 0, true, [zero, one], 0),
      (false, 0, false, [zero, one], 0), (false, 0, false, [], 1),
      (true, 1, true, [zero, one], 1), (true, 2, true, [zero, one], 4),
      (true, 1, false, [zero, one], 0), (true, 0, false, [], 1)] do
    unless (admission zeroRows oneRow nested).complete do
      throw (IO.userError "Local quantified consumer was not admitted")
    let env := environment zeroRows oneRow nested
    let goal := rootGoal elements
    let whole := run env goal 400 (start env goal)
    let resumed := run env goal 360 (run env goal 40 (start env goal))
    let answers := whole.answers.map (readout elements)
    let reference := ReferenceStep.stepsAt (relationEnvironment zeroRows oneRow)
      (selectedLanguage nested) 1 (source elements)
    unless answers.length == expected && reference.length == expected &&
        decide (complete env goal whole = true) do
      throw (IO.userError "Local quantifier source/reference counts or completion disagree")
    unless answers.map (fun entry => entry.1) == reference.map Prod.snd do
      throw (IO.userError "Local quantified conclusions disagree with the source evaluator")
    unless resumed.answers.map (completeReadout elements) == whole.answers.map (completeReadout elements) do
      throw (IO.userError "Local quantifier resumption changed the complete receipt account")
    unless answers.all (fun entry => entry.1 == .apply "Accept" [zero, one] &&
        entry.2.1 == none && entry.2.2.1 == some one) do
      throw (IO.userError "A quantified output escaped or replaced the outer parameter")
    if !nested && zeroRows == 1 && oneRow && !elements.isEmpty then
      unless answers.map (fun entry => entry.2.2.2) == [[(0, zero, [0]), (1, one, [1])]] do
        throw (IO.userError "Independent quantified body origins were lost")
  IO.println "LocalQuantifierControls: source agreement, independent outputs, lexical scope, negatives and resumption passed"

#eval controls

end LocalOutputs

namespace SetValidation

/-- A direct quantified-premise control. General set admission remains
closed; these checks distinguish validation evidence from derivations. -/
def authoredRule : RewriteRule :=
  {LocalOutputs.authoredRule with
    typeContext := [("L", .collection .hashSet term), ("element", term), ("Y", term)]
    left := .apply "SetWrap" [.collection .hashSet [] (some "L")]
    right := .apply "Accept" [zero, zero]}

def language : LanguageDef :=
  {SharedOutputControls.language with
    terms := SharedOutputControls.language.terms ++
      [{label := "SetWrap", category := "Term",
        params := [.simple "elements" (.collection .hashSet term)], syntaxPattern := []}]
    rewrites := [authoredRule]}

def environment : Environment where
  language := language
  free := fun _ => none
  provider := LocalOutputs.provider 2 false
  specifications := [(0, GeneralRuleBindingInference.inferredSpec authoredRule)]

def context : Context :=
  ⟨0, authoredRule, GeneralRuleBindingInference.inferredSpec authoredRule, [], 0, 0⟩

def assignment (elements : List Pattern) : Assignment :=
  [("L", localValue [] (.collection .hashSet elements none))]

def goal (elements : List Pattern) : Goal := .premise context quantified (assignment elements)

def completed (elements : List Pattern) : State environment (goal elements) :=
  run environment (goal elements) 200 (start environment (goal elements))

theorem equivalent_sets :
    CanonicalBags.canon (.collection .hashSet [zero, zero] none) =
      CanonicalBags.canon (.collection .hashSet [zero] none) :=
  CanonicalBags.BagStep.canon_eq (.members fun _ => by simp)

theorem validation_counts_depend_on_presentation :
    (completed [zero, zero]).answers.length = 4 ∧
      (completed [zero]).answers.length = 2 := by decide +kernel

theorem missing_element_refused :
    (completed [zero, one]).answers = [] := by decide +kernel

theorem validation_searches_complete :
    complete environment (goal [zero, zero]) (completed [zero, zero]) = true ∧
      complete environment (goal [zero]) (completed [zero]) = true ∧
      complete environment (goal [zero, one]) (completed [zero, one]) = true := by decide +kernel

theorem general_set_guard_retained :
    GeneralExecutionAdmission.Obligation.setDecomposition ∈
      (GeneralExecutionAdmission.compile ⟨language, [], environment.provider⟩ permissions).obligations := by
  have rejected : GeneralExecutionAdmission.setDecompositionFree
      ⟨language, [], environment.provider⟩ permissions = false := by cbv
  simp only [GeneralExecutionAdmission.compile, rejected, Bool.false_eq_true, ↓reduceIte]
  exact List.mem_append_right _ List.mem_cons_self

#print axioms validation_counts_depend_on_presentation
#print axioms missing_element_refused
#print axioms general_set_guard_retained

end SetValidation

/-- The original shared-output/quantifier language has no collection algebra
laws: its collection slot is a vector. This is an actual nontrivial
conditional source profile for the literal specialization theorem. -/
theorem shared_output_equation_free : language.isEquationFree = true := by cbv

theorem shared_output_equations_unconditional : ReferenceStep.UnconditionalEquations language := by
  intro equation member
  change equation ∈ [] at member
  cases member

theorem shared_output_internal_policy_iff (relations : Engine.RelationEnv) (source target : Pattern) :
    ReferenceStep.StepWith
        (ReferenceStep.declaredBoundaryPolicy relations language shared_output_equations_unconditional)
        relations language source target ↔ ReferenceStep.Step relations language source target :=
  ReferenceStep.stepWith_declared_iff_of_isEquationFree
    shared_output_equations_unconditional shared_output_equation_free

#print axioms shared_output_equation_free
#print axioms shared_output_equations_unconditional
#print axioms shared_output_internal_policy_iff

end Mettapedia.OSLF.MeTTaIL.GeneralPremise.SharedOutputControls

/-! Ordinary child matching is not invariant under set presentation. This
control states both independent source judgments, at every derivation depth. -/

namespace Mettapedia.OSLF.MeTTaIL.GeneralPremise.SharedOutputControls.ChildPresentation
open _root_.Mettapedia.OSLF.MeTTaIL.Syntax GeneralPremise RuleBinding ScopedRuleMatching StructuralDescent.Scheduled

def term : TypeExpr := .base "Term"
def a : Pattern := .apply "A" []
def b : Pattern := .apply "B" []
def choice (elements : List Pattern) : Pattern := .collection .hashSet elements none
def box (value : Pattern) : Pattern := .apply "Box" [value]

def child : RewriteRule where
  name := "requires-two-matching-positions"
  typeContext := [("X", term)]
  left := choice [.fvar "X", .fvar "X"]
  right := b
  premises := []

def liftRule : RewriteRule where
  name := "conditional-lifting"
  typeContext := [("S", term), ("T", term)]
  left := box (.fvar "S")
  right := box (.fvar "T")
  premises := [.congruence (.fvar "S") (.fvar "T")]

def language : LanguageDef where
  name := "child-presentation-boundary"
  types := ["Term"]
  terms := [{label := "A", category := "Term", params := [], syntaxPattern := []},
    {label := "B", category := "Term", params := [], syntaxPattern := []},
    {label := "Box", category := "Term", params := [.simple "value" term], syntaxPattern := []},
    {label := "Choice", category := "Term", params := [.simple "elements" (.collection .hashSet term)],
      syntaxPattern := [], collectionRepresentation := .bare}]
  equations := []
  rewrites := [child, liftRule]

def environment : Environment where
  language := language
  free := fun _ => none
  provider := {signatures := [], rows := []}
  specifications := [(0, GeneralRuleBindingInference.inferredSpec child),
    (1, GeneralRuleBindingInference.inferredSpec liftRule)]

theorem default_set_guard_refuses :
    GeneralExecutionAdmission.setDecompositionFree
      ⟨language, [], environment.provider⟩
      {equationIndices := some [], includeDerivedEquations := false} = false := by
  decide +kernel

def goal (elements : List Pattern) : Goal := .root 2 [] term (box (choice elements)) 1

def completed (elements : List Pattern) : State environment (goal elements) :=
  run environment (goal elements) 300 (start environment (goal elements))

theorem same_presented_source :
    CanonicalBags.canon (box (choice [a, a])) = CanonicalBags.canon (box (choice [a])) := by
  have same := CanonicalBags.BagStep.canon_eq
    (CanonicalBags.BagStep.members (fun item => by simp) :
      CanonicalBags.BagStep (choice [a, a]) (choice [a]))
  simpa only [box, choice, CanonicalBags.canon_apply, List.map_cons, List.map_nil] using
    congrArg (fun value => Pattern.apply "Box" [value]) same

theorem ordinary_child_search_on_canonical_source :
    (completed [a]).answers.length = 0 := by decide +kernel

theorem ordinary_child_search_on_duplicate_presentation :
    (completed [a, a]).answers.length = 2 := by decide +kernel

theorem both_bounded_searches_complete :
    complete environment (goal [a]) (completed [a]) = true ∧
      complete environment (goal [a, a]) (completed [a, a]) = true := by decide +kernel

/-- No source firing exists at the canonical state, at any derivation depth.
The finite run is uncut, so the generic coverage theorem discharges all depths. -/
theorem canonical_source_has_no_firing
    {trace : List GeneralScopedMatchMachine.BagChoice} {captured completedAssignment : Assignment}
    {history : List Event} {target : Pattern}
    (fired : RootFiring environment [] term (box (choice [a])) 1
      trace captured completedAssignment history target) : False := by
  let wanted : Result environment (goal [a]) :=
    .root trace captured completedAssignment history target fired
  have initial : Complete.Exhaustion.StateCovers (start environment (goal [a])) wanted :=
    Or.inl (Or.inr ⟨_, List.mem_cons_self, wanted, rfl⟩)
  have covered := Complete.Exhaustion.run_covers 300 initial
  change Complete.Exhaustion.StateCovers (completed [a]) wanted at covered
  have emptyAnswers : (completed [a]).answers = [] :=
    List.length_eq_zero_iff.mp ordinary_child_search_on_canonical_source
  have settled : (completed [a]).agenda = [] ∧ (completed [a]).unresolved = [] := by
    simpa only [complete, GeneralPremise.Scheduler.complete, Bool.and_eq_true, List.isEmpty_iff]
      using both_bounded_searches_complete.1
  rcases covered with (found | ⟨task, pending, _⟩) | ⟨index, exhausted⟩
  · rw [emptyAnswers] at found
    exact List.not_mem_nil found
  · rw [settled.1] at pending
    exact List.not_mem_nil pending
  · rw [settled.2] at exhausted
    exact List.not_mem_nil exhausted

theorem duplicate_source_has_firing :
    ∃ trace captured completedAssignment history target,
      RootFiring environment [] term (box (choice [a, a])) 1
        trace captured completedAssignment history target := by
  have nonempty : (completed [a, a]).answers ≠ [] := by
    intro empty
    have count := ordinary_child_search_on_duplicate_presentation
    rw [empty] at count
    cases count
  obtain ⟨answer, _⟩ := List.exists_mem_of_ne_nil _ nonempty
  cases answer with
  | root trace captured completedAssignment history target valid =>
      exact ⟨trace, captured, completedAssignment, history, target, valid⟩

#print axioms default_set_guard_refuses
#print axioms canonical_source_has_no_firing
#print axioms duplicate_source_has_firing

#print axioms same_presented_source
#print axioms ordinary_child_search_on_canonical_source
#print axioms ordinary_child_search_on_duplicate_presentation
#print axioms both_bounded_searches_complete
end Mettapedia.OSLF.MeTTaIL.GeneralPremise.SharedOutputControls.ChildPresentation

namespace Mettapedia.OSLF.MeTTaIL.GeneralPremise.SharedOutputControls.ChildPresentation

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax RuleBinding ScopedRuleMatching
open EquationalScopedMatching
open Mettapedia.GSLT.LanguageDef.WellSorted

def allocationInterpretation := RecursiveCollectionHandoff.matchingInterpretation literalBodyComparison

def presentedElements (duplicates : Bool) : List Pattern := if duplicates then [a, a] else [a]
def childCaptured : Assignment := [("X", localValue [] a)]
def parentCaptured (duplicates : Bool) : Assignment :=
  [("S", localValue [] (choice (presentedElements duplicates)))]
def parentCompleted (duplicates : Bool) : Assignment :=
  ("T", localValue [] b) :: parentCaptured duplicates

/-- Allocation semantics supplies the missing child at either presentation.
This is a source judgment; the ordinary native profile remains guarded. -/
theorem allocation_child_firing (duplicates : Bool) :
    ∃ trace, Interpreted.RootFiring allocationInterpretation environment [] term
      (choice (presentedElements duplicates)) 0 trace childCaptured childCaptured [] b := by
  let spec := GeneralRuleBindingInference.inferredSpec child
  have first : Meaning literalBodyComparison child spec 0 .left [0] 0 [] (.fvar "X") a
      childCaptured := by cbv
  have second : Meaning literalBodyComparison child spec 0 .left [1] 0 childCaptured (.fvar "X") a
      childCaptured := by cbv
  have arguments : ArgumentsMeaning literalBodyComparison child spec 0 .left [] 0 [] 0
      [.fvar "X", .fvar "X"] [a, a] childCaptured := by
    simp only [ArgumentsMeaning]
    exact ⟨childCaptured, first, childCaptured, second, rfl⟩
  have presented : CanonicalBags.Presents .hashSet (presentedElements duplicates) ([a, a] ++ []) := by
    cases duplicates <;> intro item <;> simp [presentedElements]
  have meaning : Meaning literalBodyComparison child spec 0 .left [] 0 [] child.left
      (choice (presentedElements duplicates)) childCaptured := by
    rw [Meaning.eq_def]
    simp only [child, choice, reduceCtorEq, ↓reduceIte, true_and]
    change ∃ values residual middle,
      CanonicalBags.Presents .hashSet (presentedElements duplicates) (values ++ residual) ∧
      ArgumentsMeaning literalBodyComparison child spec 0 .left [] 0 [] 0
        [.fvar "X", .fvar "X"] values middle ∧
      Finished literalBodyComparison child spec 0 .left [] 0 2 none .hashSet middle
        (CanonicalBags.arrange .hashSet residual) childCaptured
    exact ⟨[a, a], [], childCaptured, presented, arguments, by cbv⟩
  obtain ⟨trace, matched⟩ := EquationalScopedReceipts.Meaning.traced meaning
  refine ⟨trace, .fire (by rfl) (by rfl) (by cbv) ?_ matched ?_ .nil (by cbv) ?_⟩
  · apply checkOpenPatternWellSorted_sound
    cases duplicates <;> cbv
  · exact checkTypedAssignment_sound (by cbv)
  · exact checkOpenPatternWellSorted_sound (by cbv)

/-- A conditional parent can use that actual child and bind its target. The
child and target traces are retained in the parent receipt, not erased. -/
theorem allocation_parent_firing (duplicates : Bool) :
    ∃ trace history, Interpreted.RootFiring allocationInterpretation environment [] term
      (box (choice (presentedElements duplicates))) 1 trace
      (parentCaptured duplicates) (parentCompleted duplicates) history (box b) := by
  let spec := GeneralRuleBindingInference.inferredSpec liftRule
  obtain ⟨childTrace, childFired⟩ := allocation_child_firing duplicates
  have captured : EquationalScopedReceipts.Matches literalBodyComparison liftRule spec 0 .left [] 0 []
      liftRule.left (box (choice (presentedElements duplicates))) [] (parentCaptured duplicates) := by
    apply EquationalScopedReceipts.Matches.constructor
    exact .cons (.capture (by cases duplicates <;> cbv)) .nil
  have targetMatched : EquationalScopedReceipts.Matches literalBodyComparison liftRule spec 0
      (.premise 0 0 1) [] 0 (parentCaptured duplicates) (.fvar "T") b []
      (parentCompleted duplicates) := .capture (by cases duplicates <;> cbv)
  have body : Interpreted.PremiseHolds allocationInterpretation environment
      ⟨1, liftRule, spec, [], 0, 0⟩ (.congruence (.fvar "S") (.fvar "T"))
      (parentCaptured duplicates) (parentCompleted duplicates)
      (.child 0 0 0 [] (choice (presentedElements duplicates)) b childTrace []
        childCaptured childCaptured []) := by
    refine .step (by cbv) ?_ childFired targetMatched ?_
    · cases duplicates <;> cbv
    · exact checkTypedAssignment_sound (by cases duplicates <;> cbv)
  refine ⟨[], _, .fire (by rfl) (by rfl) (by cbv) ?_ captured ?_
    (.cons body .nil) ?_ ?_⟩
  · apply checkOpenPatternWellSorted_sound
    cases duplicates <;> cbv
  · exact checkTypedAssignment_sound (by cases duplicates <;> cbv)
  · cases duplicates <;> cbv
  · exact checkOpenPatternWellSorted_sound (by cbv)

theorem allocation_wrong_collection_refused :
    ¬ ∃ trace final, allocationInterpretation.Matches
      ⟨child, GeneralRuleBindingInference.inferredSpec child, 0, .left, [], 0, [], child.left,
        .collection .hashBag [a] none⟩ trace final := by
  rintro ⟨trace, final, matched⟩
  change EquationalScopedReceipts.Matches literalBodyComparison child
    (GeneralRuleBindingInference.inferredSpec child) 0 .left [] 0 [] child.left
      (.collection .hashBag [a] none) trace final at matched
  cases matched

def retainedTargetRule : RewriteRule where
  name := "retained-child-target"
  typeContext := [("S", term), ("T", term)]
  left := .apply "Pair" [.fvar "S", .fvar "T"]
  right := .apply "Pair" [.fvar "S", .fvar "T"]
  premises := [.congruence (.fvar "S") (.fvar "T")]

def heldTarget : Assignment :=
  [("T", localValue [] (choice [a])), ("S", localValue [] (choice [a]))]

def heldTargetRequest (noncanonical : Bool) : RecursiveCollectionMachine.Request :=
  ⟨retainedTargetRule, GeneralRuleBindingInference.inferredSpec retainedTargetRule, 0,
    .premise 0 0 1, [], 0, heldTarget, .fvar "T", choice (presentedElements noncanonical)⟩

/-- A held canonical output distinguishes a raw child reduct from its normal
form. Collection decomposition alone does not normalize this wildcard read. -/
theorem noncanonical_held_target_refused :
    ¬ ∃ trace final, allocationInterpretation.Matches (heldTargetRequest true) trace final := by
  rintro ⟨trace, final, matched⟩
  change EquationalScopedReceipts.Matches literalBodyComparison retainedTargetRule
    (GeneralRuleBindingInference.inferredSpec retainedTargetRule) 0 (.premise 0 0 1) [] 0
    heldTarget (.fvar "T") (choice [a, a]) trace final at matched
  cases matched with
  | capture captured =>
      cbv at captured
      cases captured

theorem canonical_held_target_accepted :
    allocationInterpretation.Matches (heldTargetRequest false) [] heldTarget :=
  EquationalScopedReceipts.Matches.capture (by cbv)

theorem held_target_presentations_equivalent :
    CanonicalBags.Same (heldTargetRequest true).target (heldTargetRequest false).target := by
  change CanonicalBags.canon (choice [a, a]) = CanonicalBags.canon (choice [a])
  exact CanonicalBags.BagStep.canon_eq
    (CanonicalBags.BagStep.members (fun item => by simp) :
      CanonicalBags.BagStep (choice [a, a]) (choice [a]))

#print axioms noncanonical_held_target_refused
#print axioms canonical_held_target_accepted
#print axioms held_target_presentations_equivalent

#print axioms allocation_child_firing
#print axioms allocation_parent_firing
#print axioms allocation_wrong_collection_refused

end Mettapedia.OSLF.MeTTaIL.GeneralPremise.SharedOutputControls.ChildPresentation

namespace Mettapedia.OSLF.MeTTaIL.GeneralPremise.SharedOutputControls.RetainedCollections

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax RuleBinding ScopedRuleMatching
open ChildPresentation
open StructuralDescent.Scheduled

def backend := RecursiveCollectionHandoff.canonicalMatchingExecution

def parentRun (elements : List Pattern) (fuel : Nat) :
    State ChildPresentation.environment (ChildPresentation.goal elements) backend :=
  run ChildPresentation.environment (ChildPresentation.goal elements) fuel
    (start ChildPresentation.environment (ChildPresentation.goal elements) backend)

def parentTargets (elements : List Pattern) : List Pattern :=
  (parentRun elements 300).answers.map fun
    | .root _ _ _ _ target _ => target

#guard parentTargets [a] == [box b]
#guard parentTargets [a, a] == [box b]
#guard parentTargets [] == []
#guard (parentRun [a] 300).work == 40
#guard complete ChildPresentation.environment (ChildPresentation.goal [a]) (parentRun [a] 300)
#guard complete ChildPresentation.environment (ChildPresentation.goal []) (parentRun [] 300)

/-- Earlier output captures are read by the next input through the same
matching interpretation. Both provider values are authored data. -/
def queryRule : RewriteRule :=
  { ChildPresentation.liftRule with
    name := "collection-output-then-input"
    premises := [.relationQuery "produce" [.fvar "T"],
      .relationQuery "consume" [.fvar "T"]] }

def queryEnvironment (present : Bool := true) : Environment where
  language := {ChildPresentation.language with rewrites := [queryRule]}
  free := fun _ => none
  provider := {
    signatures := [⟨"produce", [term], [.output]⟩, ⟨"consume", [term], [.input]⟩]
    rows := if present then [⟨"produce", [choice [a, a]]⟩, ⟨"consume", [choice [a]]⟩]
      else [⟨"produce", [choice [a, a]]⟩] }
  specifications := [(0, GeneralRuleBindingInference.inferredSpec queryRule)]

def queryGoal : Goal := .root 1 [] term (box a) 0

def queryRun (present : Bool) (fuel : Nat) :
    State (queryEnvironment present) queryGoal backend :=
  run (queryEnvironment present) queryGoal fuel
    (start (queryEnvironment present) queryGoal backend)

def queryTargets (present : Bool) : List Pattern :=
  (queryRun present 300).answers.map fun
    | .root _ _ _ _ target _ => target

#guard queryTargets true == [box (choice [a])]
#guard queryTargets false == []
#guard complete (queryEnvironment true) queryGoal (queryRun true 300)
#guard complete (queryEnvironment false) queryGoal (queryRun false 300)

def quantifiedGoal (elements : List Pattern) : Goal :=
  .root 1 [] SharedOutputControls.term
    (.apply "SetWrap" [.collection .hashSet elements none]) 0

def quantifiedEnvironment : Environment :=
  { SetValidation.environment with language :=
      { SetValidation.language with terms := SetValidation.language.terms.map fun declaration =>
          if declaration.label == "SetWrap" then
            { declaration with collectionRepresentation := .wrapped }
          else declaration } }

def quantifiedRun (elements : List Pattern) (fuel : Nat) :
    State quantifiedEnvironment (quantifiedGoal elements) backend :=
  run quantifiedEnvironment (quantifiedGoal elements) fuel
    (start quantifiedEnvironment (quantifiedGoal elements) backend)

-- These count retained validation histories. They do not identify logical
-- derivations or license a derivation-bag observation.
#guard (quantifiedRun [SharedOutputControls.zero] 600).answers.length == 2
#guard (quantifiedRun [SharedOutputControls.zero, SharedOutputControls.zero] 600).answers.length == 2
#guard (quantifiedRun [SharedOutputControls.zero, SharedOutputControls.one] 600).answers.isEmpty
#guard (quantifiedRun [] 600).answers.length == 1
#guard complete quantifiedEnvironment (quantifiedGoal [SharedOutputControls.zero])
  (quantifiedRun [SharedOutputControls.zero] 600)

end Mettapedia.OSLF.MeTTaIL.GeneralPremise.SharedOutputControls.RetainedCollections

/-! Literal provider input equality and declared collection equality have
different meanings. Two inputs read the same retained capture below; neither
query can replace it. A collection interpretation therefore needs its own
provider transport certificate before it can replace the ordinary one. -/

namespace Mettapedia.OSLF.MeTTaIL.GeneralPremise.SharedOutputControls.RetainedCollections.InputBoundary

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax RuleBinding ScopedRuleMatching
open ChildPresentation StructuralDescent.Scheduled

def authoredRule : RewriteRule where
  name := "two-input-readings"
  typeContext := [("T", term)]
  left := box (.fvar "T")
  right := box (.fvar "T")
  premises := [.relationQuery "first" [.fvar "T"], .relationQuery "second" [.fvar "T"]]

def environment : Environment where
  language := {ChildPresentation.language with rewrites := [authoredRule]}
  free := fun _ => none
  provider := {
    signatures := [⟨"first", [term], [.input]⟩, ⟨"second", [term], [.input]⟩]
    rows := [⟨"first", [choice [a, b]]⟩, ⟨"second", [choice [b, a]]⟩] }
  specifications := [(0, GeneralRuleBindingInference.inferredSpec authoredRule)]

def goal : Goal := .root 1 [] term (box (choice [a, b])) 0

def completed (matcher : MatchingExecution) : State environment goal matcher :=
  run environment goal 300 (start environment goal matcher)

theorem equivalent_provider_values :
    CanonicalBags.Same (choice [a, b]) (choice [b, a]) := by
  apply CanonicalBags.BagStep.canon_eq
  exact CanonicalBags.BagStep.members (fun item => by simp [or_comm])

#guard (completed backend).answers.length == 1

theorem literal_input_refuses_conflicting_readings :
    (completed MatchingExecution.ordinary).answers = [] := by decide +kernel

#guard complete environment goal (completed backend)

theorem literal_search_is_complete :
    complete environment goal (completed MatchingExecution.ordinary) = true := by decide +kernel

theorem literal_source_has_no_firing
    {trace : List GeneralScopedMatchMachine.BagChoice} {captured final : Assignment}
    {history : List Event} {target : Pattern}
    (fired : RootFiring environment [] term (box (choice [a, b])) 0
      trace captured final history target) : False := by
  let wanted : Result environment goal := .root trace captured final history target fired
  have initial : Complete.Exhaustion.StateCovers (start environment goal) wanted :=
    Or.inl (Or.inr ⟨_, List.mem_cons_self, wanted, rfl⟩)
  have covered := Complete.Exhaustion.run_covers 300 initial
  change Complete.Exhaustion.StateCovers (completed MatchingExecution.ordinary) wanted at covered
  have settled : (completed MatchingExecution.ordinary).agenda = [] ∧
      (completed MatchingExecution.ordinary).unresolved = [] := by
    simpa only [complete, Scheduler.complete, Bool.and_eq_true, List.isEmpty_iff]
      using literal_search_is_complete
  rcases covered with (found | ⟨task, pending, _⟩) | ⟨index, exhausted⟩
  · rw [literal_input_refuses_conflicting_readings] at found
    exact List.not_mem_nil found
  · rw [settled.1] at pending
    exact List.not_mem_nil pending
  · rw [settled.2] at exhausted
    exact List.not_mem_nil exhausted

#print axioms equivalent_provider_values
#print axioms literal_input_refuses_conflicting_readings
#print axioms literal_search_is_complete
#print axioms literal_source_has_no_firing

end Mettapedia.OSLF.MeTTaIL.GeneralPremise.SharedOutputControls.RetainedCollections.InputBoundary

namespace Mettapedia.OSLF.MeTTaIL.GeneralPremise.SharedOutputControls.RetainedCollections.OutputBoundary

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax
open _root_.Mettapedia.OSLF.MeTTaIL RuleBinding ScopedRuleMatching
open EquationalScopedMatching
open Mettapedia.GSLT.LanguageDef WellSorted EquationSemantics
open ChildPresentation (term a choice)

def source : Pattern := .apply "Start" []
def target : Pattern := .apply "Done" []
def schema : Pattern := choice [a,a]
def rowValue : Pattern := choice [a]
def premise : Premise := .relationQuery "output-boundary" [schema]

def authoredRule : RewriteRule where
  name := "fixed-output-schema"
  typeContext := []
  left := source
  right := target
  premises := [premise]

def language : LanguageDef :=
  { ChildPresentation.language with
    terms := ChildPresentation.language.terms ++
      [{label := "Start", category := "Term", params := [], syntaxPattern := []},
       {label := "Done", category := "Term", params := [], syntaxPattern := []}]
    rewrites := [authoredRule] }

def spec : RuleBindingSpec := GeneralRuleBindingInference.inferredSpec authoredRule

def environment : Environment where
  language := language
  free := fun _ => none
  provider := {
    signatures := [⟨"output-boundary",[term],[.output]⟩]
    rows := [⟨"output-boundary",[rowValue]⟩] }
  specifications := [(0,spec)]

def relations : Engine.RelationEnv where
  tuples := fun relation _ => if relation = "output-boundary" then [[rowValue]] else []

def context : Context := ⟨0,authoredRule,spec,[],0,0⟩

theorem actual_row_canonical : CanonicalBags.canon rowValue = rowValue := by cbv

theorem provider_rows_canonical : CanonicalProviderRows environment.provider := by
  exact (checkCanonicalProviderRows_iff _).mp (by cbv)

theorem mixed_query_guard_accepts_schema :
    checkCanonicalQueryGuard environment.provider context premise = true := by cbv

/-- Actual core lowering retains the duplicate constant output schema. -/
theorem core_lowering_keeps_output_schema :
    (CoreReduction.reduce language).toOption.map
      (fun lowered => lowered.rewrites.map (fun rule => rule.premises)) = some [[premise]] := by cbv

/-- The literal provider always returns the same canonical row. Its output
schema cannot consume two ordinary matching positions from that singleton. -/
theorem literal_query_refused (bindings : Match.Bindings) (evaluatedLanguage : LanguageDef) :
    Engine.premiseStepWithEnv relations evaluatedLanguage bindings premise = [] := by
  simp [premise, schema, rowValue, choice, a, relations, Engine.premiseStepWithEnv,
    Engine.relationQueryStep, Engine.builtinRelationTuples, Engine.matchRelationArgs,
    Engine.matchRelationArgument, Match.matchPattern, Match.matchArgs, Match.matchBag,
    Match.applyBindings]

/-- No literal reference firing exists from any outer presentation. Changing
an outer representative cannot alter the fixed internal provider row/schema. -/
theorem reference_has_no_step {presented result : Pattern} :
    ¬ ReferenceStep.Step relations language presented result := by
  rintro ⟨witness, valid⟩
  cases valid with
  | @rule source index rule initial final witnesses declared matched premises =>
    have ruleEq : rule = authoredRule := by
      have member := List.mem_of_getElem? declared
      simpa only [language, List.mem_singleton] using member
    subst rule
    change ReferenceStep.PremisesValid relations language _ initial [premise] witnesses final at premises
    cases premises with
    | cons held _ =>
      cases held with
      | base _ offered =>
          rw [literal_query_refused] at offered
          exact List.not_mem_nil offered
      | step endpoints _ _ _ => simp [premise, ReferenceStep.stepEndpoints] at endpoints

/-- The full reference relation modulo equations cannot change a fixed
internal provider row or output schema by changing the outer redex. -/
theorem reference_stepModulo_has_no_step {presented result : Pattern} :
    ¬ ReferenceStep.StepModulo relations language presented result := by
  rintro ⟨redex, contractum, before, stepped, after⟩
  exact reference_has_no_step stepped

/-- The original contextual relation also rejects the query at every depth. -/
theorem contextual_has_no_step {presented result : Pattern} :
    ¬ ContextualStep.Step (ContextualStep.engineBasePremises relations) language presented result := by
  rintro ⟨fuel, valid⟩
  cases valid with
  | @rule fuel sourcePattern targetPattern rule initial final member matched premises reduced =>
    have ruleEq : rule = authoredRule := by simpa only [language, List.mem_singleton] using member
    subst rule
    change ContextualStep.PremisesAt _ language _ _ [premise] _ at premises
    cases premises with
    | cons held _ =>
      cases held with
      | relationQuery offered =>
        change _ ∈ Engine.premiseStepWithEnv relations language _ premise at offered
        rw [literal_query_refused] at offered
        exact List.not_mem_nil offered

/-- The contextual StepModulo relation only changes outer terms. Its actual
query boundary stays literal, so equations do not recover this output match. -/
theorem stepModulo_has_no_step {presented result : Pattern} :
    ¬ StepModuloEquations (ContextualStep.engineBasePremises relations) language presented result := by
  rintro ⟨redex,contractum,before,stepped,after⟩
  exact contextual_has_no_step stepped

/-- The actual reduced rule differs only by its checked binding metadata. -/
def loweredLanguage : LanguageDef :=
  (CoreReduction.reduce language).toOption.getD (LanguageDef.empty "lowering-failed")

theorem lowered_rule_table :
    loweredLanguage.rewrites = [{authoredRule with bindings := some spec}] := by cbv

theorem lowered_reference_has_no_step {presented result : Pattern} :
    ¬ ReferenceStep.Step relations loweredLanguage presented result := by
  rintro ⟨witness, valid⟩
  cases valid with
  | @rule sourcePattern index rule initial final witnesses declared matched premises =>
    have ruleEq : rule = {authoredRule with bindings := some spec} := by
      have member := List.mem_of_getElem? declared
      rw [lowered_rule_table] at member
      exact List.mem_singleton.mp member
    subst rule
    change ReferenceStep.PremisesValid relations loweredLanguage _ initial [premise] witnesses final at premises
    cases premises with
    | cons held _ =>
      cases held with
      | base _ offered =>
          rw [literal_query_refused] at offered
          exact List.not_mem_nil offered
      | step endpoints _ _ _ => simp [premise, ReferenceStep.stepEndpoints] at endpoints

theorem lowered_reference_stepModulo_has_no_step {presented result : Pattern} :
    ¬ ReferenceStep.StepModulo relations loweredLanguage presented result := by
  rintro ⟨redex, contractum, before, stepped, after⟩
  exact lowered_reference_has_no_step stepped

theorem lowered_contextual_has_no_step {presented result : Pattern} :
    ¬ ContextualStep.Step (ContextualStep.engineBasePremises relations) loweredLanguage presented result := by
  rintro ⟨fuel, valid⟩
  cases valid with
  | @rule fuel sourcePattern targetPattern rule initial final member matched premises reduced =>
    have ruleEq : rule = {authoredRule with bindings := some spec} := by
      rw [lowered_rule_table] at member
      exact List.mem_singleton.mp member
    subst rule
    change ContextualStep.PremisesAt _ loweredLanguage _ _ [premise] _ at premises
    cases premises with
    | cons held _ =>
      cases held with
      | relationQuery offered =>
        change _ ∈ Engine.premiseStepWithEnv relations loweredLanguage _ premise at offered
        rw [literal_query_refused] at offered
        exact List.not_mem_nil offered

theorem lowered_stepModulo_has_no_step {presented result : Pattern} :
    ¬ StepModuloEquations (ContextualStep.engineBasePremises relations) loweredLanguage presented result := by
  rintro ⟨redex,contractum,before,stepped,after⟩
  exact lowered_contextual_has_no_step stepped

/-- The allocation interpretation selects the same set member twice, then
consumes it. This is an independent decomposition witness for the actual row. -/
theorem canonical_query_matches :
    ∃ trace, RecursiveCollectionHandoff.canonicalMatchingInterpretation.Matches
      ⟨authoredRule,spec,0,.premise 0 0 0,[],0,[],schema,rowValue⟩ trace [] := by
  have atom : Meaning literalBodyComparison authoredRule spec 0 (.premise 0 0 0) [0] 0 [] a a [] := by
    cbv
  have atomAgain : Meaning literalBodyComparison authoredRule spec 0 (.premise 0 0 0) [1] 0 [] a a [] := by
    cbv
  have arguments : ArgumentsMeaning literalBodyComparison authoredRule spec 0 (.premise 0 0 0) [] 0 [] 0
      [a,a] [a,a] [] := by
    simp only [ArgumentsMeaning]
    exact ⟨[],atom,[],atomAgain,rfl⟩
  have meaning : Meaning literalBodyComparison authoredRule spec 0 (.premise 0 0 0) [] 0 [] schema rowValue [] := by
    rw [Meaning.eq_def]
    simp only [schema, rowValue, choice, reduceCtorEq, ↓reduceIte, true_and]
    change ∃ values residual middle,
      CanonicalBags.Presents .hashSet [a] (values ++ residual) ∧
      ArgumentsMeaning literalBodyComparison authoredRule spec 0 (.premise 0 0 0) [] 0 [] 0
        [a,a] values middle ∧
      Finished literalBodyComparison authoredRule spec 0 (.premise 0 0 0) [] 0 2 none .hashSet middle
        (CanonicalBags.arrange .hashSet residual) []
    exact ⟨[a,a],[],[],by intro item; simp,arguments,by cbv⟩
  obtain ⟨trace,matched⟩ := EquationalScopedReceipts.Meaning.traced meaning
  refine ⟨trace,?_⟩
  change EquationalScopedReceipts.Matches literalBodyComparison authoredRule spec 0 (.premise 0 0 0) [] 0 []
    schema (CanonicalBags.canon rowValue) trace []
  rw [actual_row_canonical]
  exact matched

/-- The actual canonical provider row validates the interpreted query, with
its retained provider position and allocation trace. -/
theorem canonical_premise_holds :
    ∃ trace, Interpreted.PremiseHolds RecursiveCollectionHandoff.canonicalMatchingInterpretation environment
      context premise [] [] (.query 0 0 0 [(0,trace)]) := by
  obtain ⟨trace, matched⟩ := canonical_query_matches
  refine ⟨trace,.query (.row (by rfl) (by rfl) (checkRow_sound (by cbv)) ?_
    (checkTypedAssignment_sound (by cbv)))⟩
  exact .output matched .nil

/-- The interpreted source has a real Start→Done firing even though the
original literal reference and StepModulo relations are empty everywhere. -/
theorem canonical_source_fires :
    ∃ trace, Interpreted.RootFiring RecursiveCollectionHandoff.canonicalMatchingInterpretation environment
      [] term source 0 [] [] [] [.query 0 0 0 [(0,trace)]] target := by
  obtain ⟨trace, held⟩ := canonical_premise_holds
  refine ⟨trace,.fire (by rfl) (by rfl) (by cbv) (checkOpenPatternWellSorted_sound (by cbv)) ?_
    (checkTypedAssignment_sound (by cbv)) (.cons held .nil) (by cbv)
    (checkOpenPatternWellSorted_sound (by cbv))⟩
  change EquationalScopedReceipts.Matches literalBodyComparison authoredRule spec 0 .left [] 0 []
    authoredRule.left (CanonicalBags.canon source) [] []
  have sourceCanonical : CanonicalBags.canon source = source := by cbv
  rw [sourceCanonical]
  change EquationalScopedReceipts.Matches literalBodyComparison authoredRule spec 0 .left [] 0 []
    (.apply "Start" []) (.apply "Start" []) [] []
  exact .constructor .nil

/-- This source presentation has no conditional equation evidence. -/
theorem equations_unconditional : ReferenceStep.UnconditionalEquations language := by
  intro equation member
  simp [language,ChildPresentation.language] at member

/-- The declared internal policy uses the original source equivalence. -/
def internalPolicy : ReferenceStep.InternalBoundaryPolicy :=
  ReferenceStep.declaredBoundaryPolicy relations language equations_unconditional

def choiceCarrier : GrammarRule :=
  {label := "Choice",category := "Term",
    params := [.simple "elements" (.collection .hashSet ChildPresentation.term)],
    syntaxPattern := [],collectionRepresentation := .bare}

theorem choiceCarrier_declared : CollectionCarrierRule language choiceCarrier .hashSet :=
  ⟨by simp [language,ChildPresentation.language,choiceCarrier],"elements",ChildPresentation.term,rfl⟩

theorem no_authored_rows : language.equations = [] := rfl
theorem no_algebra : language.hasAlgebraDeclarations = false := by cbv

theorem atom_source_collections : ReferenceStep.SourceCollections language a :=
  .apply (by intro value member; cases member)

theorem choice_source_collections {values : List Pattern}
    (typed : checkHasType language FreeTypeContext.empty [] (choice values) (.base "Term") = true)
    (children : ∀ value ∈ values,ReferenceStep.SourceCollections language value) :
    ReferenceStep.SourceCollections language (choice values) := by
  obtain ⟨index,rule,atIndex,_,dataTyped⟩ := (checkHasType_sound typed).collection_type_origin
  exact .collection (Or.inr ⟨rule,List.mem_iff_getElem?.mpr ⟨index,atIndex⟩,dataTyped⟩) children

theorem row_source_collections : ReferenceStep.SourceCollections language rowValue := by
  apply choice_source_collections (by cbv)
  intro value member
  cases List.mem_singleton.mp member
  exact atom_source_collections

theorem schema_source_collections : ReferenceStep.SourceCollections language schema := by
  apply choice_source_collections (by cbv)
  intro value member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl <;> exact atom_source_collections

def nestedPresentation : Pattern := choice [schema,rowValue]
def nestedCanonical : Pattern := choice [rowValue]

theorem nested_source_collections : ReferenceStep.SourceCollections language nestedPresentation := by
  apply choice_source_collections (by cbv)
  intro value member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact schema_source_collections
  · exact row_source_collections

/-- The actual declared set law, with the concrete grammar and source sort
witness, relates the provider singleton to the duplicate output schema. -/
theorem provider_row_equivalent_schema : ReferenceStep.Equivalent relations language rowValue schema := by
  have sorted : SortedAt language schema choiceCarrier.category :=
    ⟨FreeTypeContext.empty,[],checkHasType_sound (by cbv)⟩
  exact Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _
    (.inContext .hole (Or.inr (.setDedup_of_sorted sorted))))

/-- The ordinary matcher succeeds at the equivalent tuple presentation; the
actual provider request and returned tuple remain visible in the evidence. -/
theorem declared_query_holds :
    ReferenceStep.PresentedQuery (ReferenceStep.equivalentSetoid relations language)
      relations language [] "output-boundary" [schema] [] := by
  refine ⟨[rowValue],by simp [relations,Engine.builtinRelationTuples],
    [schema],.cons provider_row_equivalent_schema .nil,[],?_,by cbv⟩
  decide +kernel

/-- The explicit internal equation policy admits the concrete authored
Start→Done rule. The original literal source relation stays empty. -/
theorem declared_source_fires : ReferenceStep.StepWith internalPolicy relations language source target := by
  have held : ReferenceStep.PremiseValid relations language (ReferenceStep.captureSites authoredRule)
      [] premise (.base []) [] internalPolicy := .equationalQuery declared_query_holds
  have premises : ReferenceStep.PremisesValid relations language (ReferenceStep.captureSites authoredRule)
      [] [premise] [.base []] [] internalPolicy := .equationalCons held (.equationalNil [])
  have result : Match.applyBindingsScoped (ReferenceStep.captureSites authoredRule) [] 0
      authoredRule.right = target := by cbv
  rw [← result]
  exact ⟨.rule 0 [] [.base []],.equationalRule (index := 0) (rule := authoredRule)
    (initial := []) (final := []) (by rfl) (by decide +kernel) premises⟩

theorem declared_stepModulo_fires :
    ReferenceStep.StepModuloWith relations language internalPolicy source target :=
  ⟨source,target,Relation.EqvGen.refl _,declared_source_fires,Relation.EqvGen.refl _⟩

/-- This is a difference between named source policies, not a repair of the
literal StepModulo relation or a new compiler admission. -/
theorem internal_policies_separate :
    ReferenceStep.StepModuloWith relations language internalPolicy source target ∧
      ¬ ReferenceStep.StepModulo relations language source target :=
  ⟨declared_stepModulo_fires,reference_stepModulo_has_no_step⟩

/-- The old literal checker does not gain equational search implicitly. -/
theorem literal_checker_refuses_declared_witness :
    ReferenceStep.checkStep relations language source (.rule 0 [] [.base []]) = none := by cbv

/-- Both levels of this actual set presentation are normalized through the
source's own declared equations. -/
theorem nested_source_equivalent : ReferenceStep.Equivalent relations language nestedPresentation nestedCanonical := by
  have inner : CanonicalBags.Same schema rowValue :=
    (ReferenceStep.equivalent_same no_authored_rows no_algebra provider_row_equivalent_schema).symm
  have inside : CanonicalBags.Same nestedPresentation (choice [rowValue,rowValue]) :=
    CanonicalBags.same_collection_congr .hashSet none (.cons inner (.cons rfl .nil))
  have outer : CanonicalBags.Same (choice [rowValue,rowValue]) nestedCanonical :=
    CanonicalBags.BagStep.canon_eq (.members fun value => by simp)
  exact ReferenceStep.equivalent_of_same nested_source_collections (inside.trans outer)

/-- The ordinary scoped matching presentation recovered from the actual
allocation interpretation is authorized by original source equations. -/
theorem canonical_output_has_declared_source_match :
    ∃ trace presented,ReferenceStep.Equivalent relations language rowValue presented ∧
      GeneralScopedMatch.Matches authoredRule spec 0 (.premise 0 0 0) [] 0 [] schema presented [] ∧
      RecursiveCollectionHandoff.canonicalMatchingInterpretation.Matches
        ⟨authoredRule,spec,0,.premise 0 0 0,[],0,[],schema,rowValue⟩ trace [] := by
  obtain ⟨trace,matched⟩ := canonical_query_matches
  have meaningful : Meaning literalBodyComparison authoredRule spec 0 (.premise 0 0 0) [] 0 []
      schema (CanonicalBags.canon rowValue) [] := by
    change EquationalScopedReceipts.Matches literalBodyComparison authoredRule spec 0 (.premise 0 0 0) [] 0 []
      schema (CanonicalBags.canon rowValue) trace [] at matched
    exact matched.meaning
  obtain ⟨presented,related,ordinary⟩ := canonical_has_source_presentation row_source_collections meaningful
  exact ⟨trace,presented,related,ordinary,matched⟩

theorem actual_increasing_spines : CanonicalBags.IncreasingSpines authoredRule spec := by
  intro key site path arguments found
  change (none : Option (List Pattern)) = some arguments at found
  cases found

/-- This is the existing executable answer support theorem with original
source equivalence replacing intrinsic equality by a proved correspondence. -/
theorem canonical_output_source_support_iff :
    [] ∈ (runAt literalBodyComparison authoredRule spec 0 (.premise 0 0 0) [] 0 [] schema
        (CanonicalBags.canon rowValue)).map CanonicalBags.canonAssignment ↔
      ∃ presented captured,ReferenceStep.Equivalent relations language rowValue presented ∧
        GeneralScopedMatch.Matches authoredRule spec 0 (.premise 0 0 0) [] 0 [] schema presented captured ∧
        [] = CanonicalBags.canonAssignment captured :=
  runAt_source_observation_iff no_authored_rows no_algebra actual_increasing_spines row_source_collections rfl

theorem wrong_collection_kind_not_equivalent :
    ¬ ReferenceStep.Equivalent relations language (.collection .hashBag [a] none) schema := by
  intro related
  have same := ReferenceStep.equivalent_same no_authored_rows no_algebra related
  obtain ⟨items,shape,_⟩ := CanonicalBags.same_collection same
  simp [schema,choice] at shape

theorem undeclared_unit_not_equivalent :
    ¬ ReferenceStep.Equivalent relations language rowValue (choice []) := by
  intro related
  have same := ReferenceStep.equivalent_same no_authored_rows no_algebra related
  have emptyCanonical : CanonicalBags.canon (choice []) = choice [] := by cbv
  unfold CanonicalBags.Same at same
  rw [actual_row_canonical,emptyCanonical] at same
  cases same

theorem cross_constructor_not_equivalent :
    ¬ ReferenceStep.Equivalent relations language rowValue (ChildPresentation.box rowValue) := by
  intro related
  have same := ReferenceStep.equivalent_same no_authored_rows no_algebra related
  obtain ⟨items,shape,_⟩ := CanonicalBags.same_collection same
  simp [ChildPresentation.box] at shape

/-- A named wrapper carries collection-valued data without exposing it as a
base-sort bare carrier. Its declared data type licenses intrinsic kind laws;
wrapper collapse remains independent. -/
def wrappedOnlyLanguage : LanguageDef :=
  {language with terms := language.terms.map fun rule =>
    if rule.label = "Choice" then {rule with collectionRepresentation := .wrapped} else rule}

theorem wrapped_metadata_still_mentions_set :
    CollectionCarrierRule wrappedOnlyLanguage {choiceCarrier with collectionRepresentation := .wrapped} .hashSet :=
  ⟨by decide +kernel,"elements",ChildPresentation.term,rfl⟩

theorem wrapped_no_bare_carriers :
    ∀ rule ∈ wrappedOnlyLanguage.terms,CollectionLaws.bareKind rule = none := by
  have checked : wrappedOnlyLanguage.terms.all (fun rule => CollectionLaws.bareKind rule == none) = true := by cbv
  intro rule member
  exact beq_iff_eq.mp ((List.all_eq_true.mp checked) rule member)

theorem wrapped_row_data_typed : HasType wrappedOnlyLanguage FreeTypeContext.empty [] rowValue
    (.collection .hashSet ChildPresentation.term) := checkHasType_sound (by cbv)

theorem wrapped_term_typed : HasType wrappedOnlyLanguage FreeTypeContext.empty [] (.apply "Choice" [rowValue])
    (.base "Term") := checkHasType_sound (by cbv)

theorem wrapped_row_source_collections : ReferenceStep.SourceCollections wrappedOnlyLanguage rowValue := by
  refine .collection (Or.inr ⟨{choiceCarrier with collectionRepresentation := .wrapped},
    wrapped_metadata_still_mentions_set.authored,?_⟩) ?_
  · exact ⟨.simple "elements" (.collection .hashSet ChildPresentation.term),by simp [choiceCarrier],
      ChildPresentation.term,.here,FreeTypeContext.empty,[],wrapped_row_data_typed⟩
  · intro value member
    cases List.mem_singleton.mp member
    exact .apply (by intro child member; cases member)

/-- Set data remains source-equivalent under a named wrapper even though no
bare carrier can type it at a base sort. -/
theorem wrapped_same_is_source_equivalence :
    CanonicalBags.Same rowValue schema ∧ ReferenceStep.Equivalent relations wrappedOnlyLanguage rowValue schema := by
  have same := ReferenceStep.equivalent_same no_authored_rows no_algebra provider_row_equivalent_schema
  exact ⟨same,ReferenceStep.equivalent_of_same wrapped_row_source_collections same⟩

#print axioms choiceCarrier_declared
#print axioms no_authored_rows
#print axioms no_algebra
#print axioms atom_source_collections
#print axioms choice_source_collections
#print axioms row_source_collections
#print axioms schema_source_collections
#print axioms nested_source_collections
#print axioms nested_source_equivalent
#print axioms canonical_output_has_declared_source_match
#print axioms actual_increasing_spines
#print axioms canonical_output_source_support_iff
#print axioms wrong_collection_kind_not_equivalent
#print axioms undeclared_unit_not_equivalent
#print axioms cross_constructor_not_equivalent
#print axioms wrapped_metadata_still_mentions_set
#print axioms wrapped_no_bare_carriers
#print axioms wrapped_row_data_typed
#print axioms wrapped_term_typed
#print axioms wrapped_row_source_collections
#print axioms wrapped_same_is_source_equivalence

def missingInternalPolicy : ReferenceStep.InternalBoundaryPolicy :=
  ReferenceStep.declaredBoundaryPolicy Engine.RelationEnv.empty language equations_unconditional

/-- Choosing an equivalent output presentation cannot manufacture a missing
provider row. The authored source rule is unchanged. -/
theorem declared_missing_provider_refused {presented result : Pattern} :
    ¬ ReferenceStep.StepWith missingInternalPolicy Engine.RelationEnv.empty language presented result := by
  rintro ⟨witness,valid⟩
  cases valid with
  | @equationalRule theory sourcePattern index rule initial final witnesses declared matched held =>
      have ruleEq : rule = authoredRule := by
        have member := List.mem_of_getElem? declared
        simpa only [language,List.mem_singleton] using member
      subst rule
      change ReferenceStep.PremisesValid Engine.RelationEnv.empty language _ initial [premise] witnesses final
        missingInternalPolicy at held
      cases held with
      | equationalCons head _ =>
          cases head with
          | equationalQuery query =>
              obtain ⟨tuple,provided,_⟩ := query
              simp [Engine.builtinRelationTuples,Engine.RelationEnv.empty] at provided
          | equationalStep endpoints _ _ _ _ _ =>
              simp [premise,ReferenceStep.stepEndpoints] at endpoints

#print axioms declared_missing_provider_refused

#print axioms equations_unconditional
#print axioms provider_row_equivalent_schema
#print axioms declared_query_holds
#print axioms declared_source_fires
#print axioms declared_stepModulo_fires
#print axioms internal_policies_separate
#print axioms literal_checker_refuses_declared_witness

#print axioms actual_row_canonical
#print axioms provider_rows_canonical
#print axioms mixed_query_guard_accepts_schema
#print axioms core_lowering_keeps_output_schema
#print axioms literal_query_refused
#print axioms reference_has_no_step
#print axioms reference_stepModulo_has_no_step
#print axioms contextual_has_no_step
#print axioms stepModulo_has_no_step
#print axioms lowered_rule_table
#print axioms lowered_reference_has_no_step
#print axioms lowered_reference_stepModulo_has_no_step
#print axioms lowered_contextual_has_no_step
#print axioms lowered_stepModulo_has_no_step
#print axioms canonical_query_matches
#print axioms canonical_premise_holds
#print axioms canonical_source_fires

end Mettapedia.OSLF.MeTTaIL.GeneralPremise.SharedOutputControls.RetainedCollections.OutputBoundary

namespace Mettapedia.OSLF.MeTTaIL.GeneralPremise.SharedOutputControls.ReferenceRootControls

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax
open _root_.Mettapedia.OSLF.MeTTaIL RuleBinding ScopedRuleMatching GeneralExecutionAdmission
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.Framework.GeneralCanonicalAgreement
open QuantifiedReference

def start : Pattern := .apply "Start" []
def done : Pattern := .apply "Done" []

def serviceRule : RewriteRule where
  name := "check-every-supplied-member"
  typeContext := [("L",.collection .hashSet term),("element",term),("Y",term)]
  left := start
  right := done
  premises := [.relationQuery "supply" [.fvar "L"],quantified]

def serviceLanguage : LanguageDef :=
  {SharedOutputControls.language with
    name := "finite-supplied-set-validation"
    terms := SharedOutputControls.language.terms ++
      [{label := "Start",category := "Term",params := [],syntaxPattern := []},
       {label := "Done",category := "Term",params := [],syntaxPattern := []},
       {label := "SetData",category := "Term",params := [.simple "values" (.collection .hashSet term)],
        syntaxPattern := [],collectionRepresentation := .wrapped}]
    rewrites := [serviceRule]}

def serviceProvider (elements : List Pattern) : ProviderSnapshot where
  signatures := [⟨"supply",[.collection .hashSet term],[.output]⟩,
    ⟨"share",[term,term],[.output,.input]⟩]
  rows := [⟨"supply",[.collection .hashSet elements none]⟩,
    ⟨"share",[zero,zero]⟩,⟨"share",[zero,zero]⟩]

def serviceSnapshot (elements : List Pattern) : Snapshot :=
  ⟨serviceLanguage,[],serviceProvider elements⟩

def servicePermissions : Permissions := {SharedOutputControls.permissions with sites := .rootOnly}

def serviceAdmission (elements : List Pattern) :=
  GeneralExecutionTotalAdmission.compile (serviceSnapshot elements) servicePermissions

def servicePlan (elements : List Pattern) : Plan := (serviceAdmission elements).execution

def compiledRule : RulePlan :=
  ⟨0,serviceRule,⟨GeneralRuleBindingInference.inferredSpec serviceRule,.inferredRootInputs⟩⟩

def serviceEnvironment (elements : List Pattern) : Environment where
  language := {serviceLanguage with rewrites := [compiledRule.rule]}
  free := fun _ => none
  provider := serviceProvider elements
  specifications := [(0,compiledRule.binding.spec)]

theorem actual_compiled_rule (elements : List Pattern) : (servicePlan elements).rules = [compiledRule] := by cbv

theorem actual_compiled_environment (elements : List Pattern) :
    GeneralPlanEnvironment.environment (servicePlan elements) = serviceEnvironment elements := by
  unfold GeneralPlanEnvironment.environment
  rw [actual_compiled_rule]
  rfl

/-- Both the successful carrier and the missing-member carrier are admitted.
Failure of the latter is a false guard rather than unavailable execution. -/
theorem actual_admission_complete :
    (serviceAdmission [zero,zero]).complete = true ∧
      (serviceAdmission [zero,one]).complete = true := by cbv

/-- This root qualification does not authorize descent inside the data
set. The existing context-coverage obligation remains observable. -/
theorem set_context_obligation_retained :
    GeneralExecutionAdmission.Obligation.setDecomposition ∈
      (GeneralExecutionAdmission.compile (serviceSnapshot [zero,zero]) SharedOutputControls.permissions).obligations := by
  cbv
  exact List.mem_cons_self

theorem service_shapes : ∀ premise ∈ compiledRule.rule.premises,Validation premise := by
  intro premise member
  change premise ∈ [.relationQuery "supply" [.fvar "L"],quantified] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact .query (by decide) (by intro argument member; cases List.mem_singleton.mp member; exact .metavariable _)
  · refine .quantified (.query (by decide) ?_)
    intro argument member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl <;> exact .metavariable _

/-- The generic whole-rule theorem applies to the actual compiled row,
including its elaborated binding specification and declared provider modes. -/
theorem compiled_root_reference_iff {target : Pattern} :
    (∃ trace captured completed history,RootFiring (serviceEnvironment [zero,zero]) [] term start 0
      trace captured completed history target) ↔
    ∃ initial witnesses,ReferenceStep.StepValid
      (providerRelEnv (serviceEnvironment [zero,zero]).provider) (serviceEnvironment [zero,zero]).language start
      (.rule 0 initial witnesses) target := by
  refine root_iff_reference _ (providerRelEnv_reads _) (by cbv) (by cbv) (by rfl) rfl (by cbv) (by cbv)
    (by decide) (GeneralFirstOrderProjection.checkFirstOrder_sound (by cbv))
    (GeneralFirstOrderProjection.checkFirstOrder_sound (by cbv))
    (checkHasType_sound (by cbv)) (checkHasType_sound (by cbv)) service_shapes (by cbv) (by cbv)
    (checkOpenPatternWellSorted_sound (by cbv))

def serviceGoal : Execution.Goal := .root [] term start 0

def serviceState (elements : List Pattern) : Execution.State (serviceEnvironment elements) serviceGoal :=
  Execution.run (serviceEnvironment elements) serviceGoal 400
    (Execution.start (serviceEnvironment elements) serviceGoal)

def serviceTarget {activeEnvironment : Environment} : Execution.Result activeEnvironment serviceGoal → Pattern
  | .root _ _ _ _ target _ => target

def serviceReceipt {activeEnvironment : Environment} : Execution.Result activeEnvironment serviceGoal → String
  | .root trace captured completed history target _ => reprStr (trace,captured,completed,history,target)

def interruptedState : Execution.State (serviceEnvironment [zero,zero]) serviceGoal :=
  Execution.run (serviceEnvironment [zero,zero]) serviceGoal 1
    (Execution.start (serviceEnvironment [zero,zero]) serviceGoal)

theorem interrupted_work_remains :
    Execution.complete (serviceEnvironment [zero,zero]) serviceGoal interruptedState = false := by decide +kernel

theorem interrupted_resume_state :
    Execution.run (serviceEnvironment [zero,zero]) serviceGoal 399 interruptedState = serviceState [zero,zero] :=
  (Execution.run_add (serviceEnvironment [zero,zero]) serviceGoal 1 399
    (Execution.start (serviceEnvironment [zero,zero]) serviceGoal)).symm

theorem interrupted_resume_preserves_receipts :
    (Execution.run (serviceEnvironment [zero,zero]) serviceGoal 399 interruptedState).answers.map serviceReceipt =
      (serviceState [zero,zero]).answers.map serviceReceipt :=
  congrArg (fun state : Execution.State (serviceEnvironment [zero,zero]) serviceGoal =>
    state.answers.map serviceReceipt) interrupted_resume_state

theorem actual_retained_results :
    (serviceState [zero,zero]).answers.map serviceTarget = [done,done,done,done] ∧
      (serviceState [zero,one]).answers.map serviceTarget = [] := by decide +kernel

theorem actual_retained_complete :
    Execution.complete (serviceEnvironment [zero,zero]) serviceGoal (serviceState [zero,zero]) = true ∧
      Execution.complete (serviceEnvironment [zero,one]) serviceGoal (serviceState [zero,one]) = true := by decide +kernel

theorem actual_plan_uses_retained_path :
    (Execution.run (GeneralPlanEnvironment.environment (servicePlan [zero,zero])) serviceGoal 400
      (Execution.start (GeneralPlanEnvironment.environment (servicePlan [zero,zero])) serviceGoal)).answers.map
      serviceTarget = [done,done,done,done] := by
  rw [actual_compiled_environment]
  exact actual_retained_results.1

/-- The independent original source listing is complete at this fuel; this
is not an absence conclusion drawn merely from an interrupted run. -/
theorem reference_listing_complete :
    ReferenceStep.enough (providerRelEnv (serviceEnvironment [zero,zero]).provider)
      (serviceEnvironment [zero,zero]).language 1 start = true ∧
    ReferenceStep.enough (providerRelEnv (serviceEnvironment [zero,one]).provider)
      (serviceEnvironment [zero,one]).language 1 start = true := by decide +kernel

theorem actual_reference_result : ReferenceStep.Step
    (providerRelEnv (serviceEnvironment [zero,zero]).provider) (serviceEnvironment [zero,zero]).language start done := by
  rw [ReferenceStep.step_iff_mem_of_enough reference_listing_complete.1]
  decide +kernel

theorem missing_member_reference_refused {target : Pattern} :
    ¬ ReferenceStep.Step (providerRelEnv (serviceEnvironment [zero,one]).provider)
      (serviceEnvironment [zero,one]).language start target := by
  rw [ReferenceStep.step_iff_mem_of_enough reference_listing_complete.2]
  have empty : ReferenceStep.stepsAt (providerRelEnv (serviceEnvironment [zero,one]).provider)
      (serviceEnvironment [zero,one]).language 1 start = [] := by decide +kernel
  simp only [empty,List.map_nil,List.not_mem_nil,not_false_eq_true]

theorem wrong_conclusion_reference_refused :
    ¬ ReferenceStep.Step (providerRelEnv (serviceEnvironment [zero,zero]).provider)
      (serviceEnvironment [zero,zero]).language start start := by
  rw [ReferenceStep.step_iff_mem_of_enough reference_listing_complete.1]
  decide +kernel

theorem reference_step_has_actual_rule {elements : List Pattern} {target : Pattern} :
    ReferenceStep.Step (providerRelEnv (serviceEnvironment elements).provider)
      (serviceEnvironment elements).language start target ↔
    ∃ initial witnesses,ReferenceStep.StepValid (providerRelEnv (serviceEnvironment elements).provider)
      (serviceEnvironment elements).language start (.rule 0 initial witnesses) target := by
  constructor
  · rintro ⟨witness,valid⟩
    cases valid with
    | @rule _ index rule initial final witnesses declared matched premises =>
        have within := (List.getElem?_eq_some_iff.mp declared).1
        change index < 1 at within
        have indexZero : index = 0 := by omega
        subst index
        exact ⟨initial,witnesses,.rule declared matched premises⟩
  · rintro ⟨initial,witnesses,valid⟩
    exact ⟨.rule 0 initial witnesses,valid⟩

theorem compiled_root_step_iff {target : Pattern} :
    (∃ trace captured completed history,RootFiring (serviceEnvironment [zero,zero]) [] term start 0
      trace captured completed history target) ↔
    ReferenceStep.Step (providerRelEnv (serviceEnvironment [zero,zero]).provider)
      (serviceEnvironment [zero,zero]).language start target :=
  compiled_root_reference_iff.trans reference_step_has_actual_rule.symm

theorem actual_root_fires : ∃ trace captured completed history,
    RootFiring (serviceEnvironment [zero,zero]) [] term start 0 trace captured completed history done :=
  compiled_root_step_iff.mpr actual_reference_result

theorem missing_member_root_refused {trace : List GeneralScopedMatchMachine.BagChoice}
    {captured completed : Assignment} {history : List Event} {target : Pattern} :
    ¬ RootFiring (serviceEnvironment [zero,one]) [] term start 0 trace captured completed history target := by
  intro fired
  obtain ⟨initial,witnesses,reference⟩ := root_toReference _ (providerRelEnv_reads _) (by rfl) rfl (by cbv)
    (GeneralFirstOrderProjection.checkFirstOrder_sound (by cbv))
    (GeneralFirstOrderProjection.checkFirstOrder_sound (by cbv)) service_shapes (by cbv) fired
  exact missing_member_reference_refused ⟨.rule 0 initial witnesses,reference⟩

theorem wrong_conclusion_root_refused {trace : List GeneralScopedMatchMachine.BagChoice}
    {captured completed : Assignment} {history : List Event} :
    ¬ RootFiring (serviceEnvironment [zero,zero]) [] term start 0 trace captured completed history start := by
  intro fired
  exact wrong_conclusion_reference_refused (compiled_root_step_iff.mp ⟨trace,captured,completed,history,fired⟩)

theorem compiled_core : compiledRule.rule.left = serviceRule.left ∧
    compiledRule.rule.right = serviceRule.right ∧ compiledRule.rule.premises = serviceRule.premises := by
  have fields := GeneralRuleBindingInference.elaborate_source compiledRule.binding compiledRule.authored
  exact ⟨fields.2.1,fields.2.2.1,fields.2.2.2⟩

/-- The real binding-plan elaboration changes annotations while preserving
the original reference rule witness and its literal provider premises. -/
theorem compiled_reference_to_authored {elements : List Pattern} {target : Pattern}
    (step : ReferenceStep.Step (providerRelEnv (serviceEnvironment elements).provider)
      (serviceEnvironment elements).language start target) :
    ReferenceStep.Step (providerRelEnv (serviceEnvironment elements).provider) serviceLanguage start target := by
  obtain ⟨initial,witnesses,valid⟩ := reference_step_has_actual_rule.mp step
  cases valid with
  | @rule _ _ actualRule _ final _ declared matched premises =>
      have same : actualRule = compiledRule.rule := Option.some.inj (declared.symm.trans rfl)
      subst actualRule
      have sitesSame : ReferenceStep.captureSites compiledRule.rule = ReferenceStep.captureSites serviceRule := by
        simp only [ReferenceStep.captureSites,compiled_core.1,compiled_core.2.2]
      have originalPremises := premises_reference_language (second := serviceLanguage) _ service_shapes premises
      rw [sitesSame,compiled_core.2.2] at originalPremises
      have originalMatch : initial ∈ ReflectiveCanonical.matchPatternForRule serviceLanguage serviceRule start := by
        simpa only [ReflectiveCanonical.matchPatternForRule_eq_syntactic,compiled_core.1] using matched
      refine ⟨.rule 0 initial witnesses,?_⟩
      rw [sitesSame,compiled_core.2.1]
      exact ReferenceStep.StepValid.rule (rule := serviceRule) rfl originalMatch originalPremises

theorem authored_reference_to_compiled {elements : List Pattern} {target : Pattern}
    (step : ReferenceStep.Step (providerRelEnv (serviceEnvironment elements).provider) serviceLanguage start target) :
    ReferenceStep.Step (providerRelEnv (serviceEnvironment elements).provider)
      (serviceEnvironment elements).language start target := by
  obtain ⟨witness,valid⟩ := step
  cases valid with
  | @rule _ index actualRule initial final witnesses declared matched premises =>
      have within := (List.getElem?_eq_some_iff.mp declared).1
      change index < 1 at within
      have indexZero : index = 0 := by omega
      subst index
      have same : actualRule = serviceRule := Option.some.inj (declared.symm.trans rfl)
      subst actualRule
      have sitesSame : ReferenceStep.captureSites compiledRule.rule = ReferenceStep.captureSites serviceRule := by
        simp only [ReferenceStep.captureSites,compiled_core.1,compiled_core.2.2]
      have originalShapes : ∀ premise ∈ serviceRule.premises,Validation premise := by
        simpa only [compiled_core.2.2] using service_shapes
      have compiledPremises := premises_reference_language
        (second := (serviceEnvironment elements).language) _ originalShapes premises
      rw [← sitesSame,← compiled_core.2.2] at compiledPremises
      have compiledMatch : initial ∈ ReflectiveCanonical.matchPatternForRule
          (serviceEnvironment elements).language compiledRule.rule start := by
        simpa only [ReflectiveCanonical.matchPatternForRule_eq_syntactic,compiled_core.1] using matched
      refine ⟨.rule 0 initial witnesses,?_⟩
      rw [← sitesSame,← compiled_core.2.1]
      exact ReferenceStep.StepValid.rule (rule := compiledRule.rule) rfl compiledMatch compiledPremises

theorem compiled_authored_step_iff {elements : List Pattern} {target : Pattern} :
    ReferenceStep.Step (providerRelEnv (serviceEnvironment elements).provider)
      (serviceEnvironment elements).language start target ↔
    ReferenceStep.Step (providerRelEnv (serviceEnvironment elements).provider) serviceLanguage start target :=
  ⟨compiled_reference_to_authored,authored_reference_to_compiled⟩

theorem authored_root_step_iff {target : Pattern} :
    (∃ trace captured completed history,RootFiring (serviceEnvironment [zero,zero]) [] term start 0
      trace captured completed history target) ↔
    ReferenceStep.Step (providerRelEnv (serviceEnvironment [zero,zero]).provider) serviceLanguage start target :=
  compiled_root_step_iff.trans compiled_authored_step_iff

#print axioms actual_compiled_rule
#print axioms actual_compiled_environment
#print axioms actual_admission_complete
#print axioms set_context_obligation_retained
#print axioms service_shapes
#print axioms compiled_root_reference_iff
#print axioms actual_retained_results
#print axioms interrupted_work_remains
#print axioms interrupted_resume_state
#print axioms interrupted_resume_preserves_receipts
#print axioms actual_retained_complete
#print axioms actual_plan_uses_retained_path
#print axioms reference_listing_complete
#print axioms actual_reference_result
#print axioms missing_member_reference_refused
#print axioms wrong_conclusion_reference_refused
#print axioms reference_step_has_actual_rule
#print axioms compiled_root_step_iff
#print axioms actual_root_fires
#print axioms missing_member_root_refused
#print axioms wrong_conclusion_root_refused
#print axioms compiled_core
#print axioms compiled_reference_to_authored
#print axioms authored_reference_to_compiled
#print axioms compiled_authored_step_iff
#print axioms authored_root_step_iff

end Mettapedia.OSLF.MeTTaIL.GeneralPremise.SharedOutputControls.ReferenceRootControls

namespace Mettapedia.OSLF.MeTTaIL.GeneralPremise.SharedOutputControls.ReferenceRootControls.DirectedControls

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax
open _root_.Mettapedia.OSLF.MeTTaIL RuleBinding ScopedRuleMatching GeneralExecutionAdmission
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.Framework.GeneralCanonicalAgreement
open QuantifiedReference

set_option maxRecDepth 8000
set_option maxHeartbeats 1200000

def lifted (body : Pattern) : Pattern := .apply "Lift" [body]
def allStart : Pattern := .apply "AllStart" []
def allDone : Pattern := .apply "AllDone" []

def liftRule : RewriteRule where
  name := "lift-a-guarded-child"
  typeContext := [("P",term),("Q",term)]
  left := lifted (.fvar "P")
  right := lifted (.fvar "Q")
  premises := [.congruence (.fvar "P") (.fvar "Q")]

def allRule : RewriteRule where
  name := "step-every-supplied-task"
  typeContext := [("T",.collection .hashSet term),("task",term),("answer",term)]
  left := allStart
  right := allDone
  premises := [.relationQuery "tasks" [.fvar "T"],
    .forAll "T" "task" (.congruence (.fvar "task") (.fvar "answer"))]

def directedLanguage : LanguageDef := {serviceLanguage with
  name := "literal-directed-quantified-service"
  terms := serviceLanguage.terms ++
    [{label := "Lift",category := "Term",params := [.simple "body" term],syntaxPattern := []},
     {label := "AllStart",category := "Term",params := [],syntaxPattern := []},
     {label := "AllDone",category := "Term",params := [],syntaxPattern := []}]
  rewrites := [serviceRule,liftRule,allRule]}

def directedProvider (tasks : List Pattern) : ProviderSnapshot :=
  {serviceProvider [zero,zero] with
    signatures := (serviceProvider [zero,zero]).signatures ++
      [⟨"tasks",[.collection .hashSet term],[.output]⟩]
    rows := (serviceProvider [zero,zero]).rows ++ [⟨"tasks",[.collection .hashSet tasks none]⟩]}

def directedSnapshot (tasks : List Pattern) : Snapshot := ⟨directedLanguage,[],directedProvider tasks⟩

def directedAdmission (tasks : List Pattern) :=
  GeneralExecutionTotalAdmission.compile (directedSnapshot tasks) servicePermissions

def directedPlan (tasks : List Pattern) : Plan := (directedAdmission tasks).execution

def serviceCompiled : RulePlan :=
  ⟨0,serviceRule,⟨GeneralRuleBindingInference.inferredSpec serviceRule,.inferredRootInputs⟩⟩
def liftCompiled : RulePlan :=
  ⟨1,liftRule,⟨GeneralRuleBindingInference.inferredSpec liftRule,.inferredRootInputs⟩⟩
def allCompiled : RulePlan :=
  ⟨2,allRule,⟨GeneralRuleBindingInference.inferredSpec allRule,.inferredRootInputs⟩⟩

def directedEnvironment (tasks : List Pattern) : Environment where
  language := {directedLanguage with rewrites := [serviceCompiled.rule,liftCompiled.rule,allCompiled.rule]}
  free := fun _ => none
  provider := directedProvider tasks
  specifications := [(0,serviceCompiled.binding.spec),(1,liftCompiled.binding.spec),(2,allCompiled.binding.spec)]

theorem actual_rules (tasks : List Pattern) :
    (directedPlan tasks).rules = [serviceCompiled,liftCompiled,allCompiled] := by cbv

theorem actual_environment (tasks : List Pattern) :
    GeneralPlanEnvironment.environment (directedPlan tasks) = directedEnvironment tasks := by
  unfold GeneralPlanEnvironment.environment
  rw [actual_rules]
  rfl

theorem unknown_child_head_admission_boundary :
    (directedAdmission [start,start]).complete = false ∧
    (directedAdmission [start,one]).complete = false := by cbv

theorem directed_shapes : ∀ (rulePlan : RulePlan),rulePlan ∈ [serviceCompiled,liftCompiled,allCompiled] →
    ∀ premise ∈ rulePlan.rule.premises,DirectedValidation premise := by
  intro row member premise premiseMember
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · change premise ∈ [.relationQuery "supply" [.fvar "L"],quantified] at premiseMember
    simp only [List.mem_cons,List.not_mem_nil,or_false] at premiseMember
    rcases premiseMember with rfl | rfl
    · exact .query (by decide) (by intro argument member; cases List.mem_singleton.mp member; exact .metavariable _)
    · refine .quantified (.query (by decide) ?_)
      intro argument member
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl <;> exact .metavariable _
  · change premise ∈ ([Premise.congruence (.fvar "P") (.fvar "Q")] : List Premise) at premiseMember
    cases List.mem_singleton.mp premiseMember
    exact .step (.metavariable _) (.metavariable _)
  · change premise ∈ ([Premise.relationQuery "tasks" [.fvar "T"],
      .forAll "T" "task" (.congruence (.fvar "task") (.fvar "answer"))] : List Premise) at premiseMember
    simp only [List.mem_cons,List.not_mem_nil,or_false] at premiseMember
    rcases premiseMember with rfl | rfl
    · exact .query (by decide) (by intro argument member; cases List.mem_singleton.mp member; exact .metavariable _)
    · exact .quantified (.step (.metavariable _) (.metavariable _))

theorem profile_good : DirectedProfile (directedEnvironment [start,start]) := by
  refine ⟨by cbv,by cbv,by rfl,?_⟩
  intro index rule declared
  have branches : index = 0 ∨ index = 1 ∨ index = 2 := by
    have bound := (List.getElem?_eq_some_iff.mp declared).1
    change index < 3 at bound
    omega
  rcases branches with rfl | rfl | rfl
  all_goals
    have selected := Option.some.inj (declared.symm.trans rfl)
    subst rule
    refine ⟨by cbv,by cbv,by decide,
      GeneralFirstOrderProjection.checkFirstOrder_sound (by cbv),
      GeneralFirstOrderProjection.checkFirstOrder_sound (by cbv),?_,?_,?_,by cbv,by cbv⟩
  · exact ⟨"Start",[],rfl⟩
  · exact ⟨term,checkHasType_sound (by cbv),checkHasType_sound (by cbv)⟩
  · exact directed_shapes serviceCompiled (by simp)
  · exact ⟨"Lift",[.fvar "P"],rfl⟩
  · exact ⟨term,checkHasType_sound (by cbv),checkHasType_sound (by cbv)⟩
  · exact directed_shapes liftCompiled (by simp)
  · exact ⟨"AllStart",[],rfl⟩
  · exact ⟨term,checkHasType_sound (by cbv),checkHasType_sound (by cbv)⟩
  · exact directed_shapes allCompiled (by simp)

#print axioms actual_rules
#print axioms actual_environment
#print axioms unknown_child_head_admission_boundary
#print axioms directed_shapes
#print axioms profile_good



/-- Unknown child heads retain the existing rule-order obligation. This
fixture is a source-agreement control, not an admitted native profile. -/
theorem actual_admission_obligation :
    (directedAdmission [start,start]).obligations =
      [.foundation .childStratification] ∧
    (directedAdmission [start,one]).obligations =
      [.foundation .childStratification] := by cbv

/-- The actual annotation pass retains every indexed source rule core. -/
theorem actual_core (tasks : List Pattern) :
    (directedEnvironment tasks).language.rewrites.map ruleCore = directedLanguage.rewrites.map ruleCore := by
  have sourceCore (row : RulePlan) : ruleCore row.rule = ruleCore row.authored := by
    have fields := GeneralRuleBindingInference.elaborate_source row.binding row.authored
    exact congrArg₂ Prod.mk fields.2.1 (congrArg₂ Prod.mk fields.2.2.1 fields.2.2.2)
  change [ruleCore serviceCompiled.rule,ruleCore liftCompiled.rule,ruleCore allCompiled.rule] =
    [ruleCore serviceRule,ruleCore liftRule,ruleCore allRule]
  rw [sourceCore serviceCompiled,sourceCore liftCompiled,sourceCore allCompiled]
  rfl

theorem uniform_directed_checked :
    checkUniformDirectedProfile (directedEnvironment [start,start]) [term] = true := by cbv

theorem uniform_directed_profile : UniformDirectedProfile (fun schema => Mettapedia.OSLF.MeTTaIL.Match.binderFree schema = true)
    (directedEnvironment [start,start]) [term] := UniformDirectedProfile.of_check uniform_directed_checked

/-- Missing child reductions do not invalidate the finite provider/profile
certificate and do not authorize a successful source witness. -/
theorem uniform_directed_missing_checked :
    checkUniformDirectedProfile (directedEnvironment [start,one]) [term] = true := by cbv

#print axioms uniform_directed_checked
#print axioms uniform_directed_profile
#print axioms uniform_directed_missing_checked

/-- This source theorem reaches the authored language through the real
binding-plan annotation pass and preserves its literal internal boundaries. -/
theorem actual_authored_step_iff {source target : Pattern}
    (typed : OpenPatternWellSorted (directedEnvironment [start,start]).language
      (directedEnvironment [start,start]).free [] term source) :
    (∃ index trace captured completed history,RootFiring (directedEnvironment [start,start]) [] term source
      index trace captured completed history target) ↔
    ReferenceStep.Step (providerRelEnv (directedEnvironment [start,start]).provider) directedLanguage source target :=
  (uniform_directed_profile.roots_iff_reference _ (providerRelEnv_reads _) (by simp) typed).trans
    (reference_step_same_core_iff (actual_core _) _)

/-- Every source witness on a Lift application uses the actual lifted rule
ordinal. The other two authored constructor heads cannot match it. -/
theorem lift_ordinal {tasks : List Pattern} {body target : Pattern} {index : Nat} {initial : Match.Bindings}
    {witnesses : List ReferenceStep.Witness}
    (step : ReferenceStep.StepValid (providerRelEnv (directedEnvironment tasks).provider)
      (directedEnvironment tasks).language (lifted body) (.rule index initial witnesses) target) : index = 1 := by
  cases step with
  | @rule _ _ rule _ _ _ declared matched _ =>
      have bound := (List.getElem?_eq_some_iff.mp declared).1
      change index < 3 at bound
      have branches : index = 0 ∨ index = 1 ∨ index = 2 := by omega
      rcases branches with rfl | rfl | rfl
      · have selected := Option.some.inj (declared.symm.trans rfl)
        subst rule
        have noMatch : ReflectiveCanonical.matchPatternForRule (directedEnvironment tasks).language
            serviceCompiled.rule (lifted body) = [] := by cbv
        rw [noMatch] at matched
        cases matched
      · rfl
      · have selected := Option.some.inj (declared.symm.trans rfl)
        subst rule
        have noMatch : ReflectiveCanonical.matchPatternForRule (directedEnvironment tasks).language
            allCompiled.rule (lifted body) = [] := by cbv
        rw [noMatch] at matched
        cases matched

theorem lift_authored_iff {body target : Pattern}
    (typed : OpenPatternWellSorted (directedEnvironment [start,start]).language
      (directedEnvironment [start,start]).free [] term (lifted body)) :
    (∃ trace captured completed history,RootFiring (directedEnvironment [start,start]) [] term (lifted body)
      1 trace captured completed history target) ↔
    ReferenceStep.Step (providerRelEnv (directedEnvironment [start,start]).provider)
      directedLanguage (lifted body) target := by
  rw [← reference_step_same_core_iff (actual_core [start,start])]
  constructor
  · rintro ⟨trace,captured,completed,history,fired⟩
    obtain ⟨initial,witnesses,step⟩ := directed_root_toReference profile_good _ (providerRelEnv_reads _) fired
    exact ⟨.rule 1 initial witnesses,step⟩
  · rintro ⟨witness,step⟩
    cases step with
    | @rule _ index rule initial final witnesses declared matched premises =>
        have valid := ReferenceStep.StepValid.rule declared matched premises
        have ordinal := lift_ordinal valid
        subst index
        exact (directed_root_iff_reference profile_good _ (providerRelEnv_reads _) typed).mpr
          ⟨initial,witnesses,valid⟩

/-- All these independent source listings have checked per-source adequate
fuel. The nested Lift control needs two child derivation levels. -/
theorem reference_enough :
    ReferenceStep.enough (providerRelEnv (directedEnvironment [start,start]).provider)
      directedLanguage 2 (lifted start) = true ∧
    ReferenceStep.enough (providerRelEnv (directedEnvironment [start,start]).provider)
      directedLanguage 2 allStart = true ∧
    ReferenceStep.enough (providerRelEnv (directedEnvironment [start,one]).provider)
      directedLanguage 2 allStart = true ∧
    ReferenceStep.enough (providerRelEnv (directedEnvironment [start,start]).provider)
      directedLanguage 3 (lifted (lifted start)) = true := by decide +kernel

theorem reference_results :
    (ReferenceStep.stepsAt (providerRelEnv (directedEnvironment [start,start]).provider)
      directedLanguage 2 (lifted start)).map (·.2) = List.replicate 4 (lifted done) ∧
    (ReferenceStep.stepsAt (providerRelEnv (directedEnvironment [start,start]).provider)
      directedLanguage 2 allStart).map (·.2) = List.replicate 16 allDone ∧
    ReferenceStep.stepsAt (providerRelEnv (directedEnvironment [start,one]).provider)
      directedLanguage 2 allStart = [] ∧
    (ReferenceStep.stepsAt (providerRelEnv (directedEnvironment [start,start]).provider)
      directedLanguage 3 (lifted (lifted start))).map (·.2) = List.replicate 4 (lifted (lifted done)) := by
  decide +kernel

theorem reference_lift : ReferenceStep.Step (providerRelEnv (directedEnvironment [start,start]).provider)
    directedLanguage (lifted start) (lifted done) := by
  rw [ReferenceStep.step_iff_mem_of_enough reference_enough.1,reference_results.1]
  simp

theorem reference_all : ReferenceStep.Step (providerRelEnv (directedEnvironment [start,start]).provider)
    directedLanguage allStart allDone := by
  rw [ReferenceStep.step_iff_mem_of_enough reference_enough.2.1,reference_results.2.1]
  simp

theorem missing_task_reference_refused {target : Pattern} :
    ¬ ReferenceStep.Step (providerRelEnv (directedEnvironment [start,one]).provider)
      directedLanguage allStart target := by
  rw [ReferenceStep.step_iff_mem_of_enough reference_enough.2.2.1,reference_results.2.2.1]
  simp only [List.map_nil,List.not_mem_nil,not_false_eq_true]

theorem wrong_conclusion_reference_refused :
    ¬ ReferenceStep.Step (providerRelEnv (directedEnvironment [start,start]).provider)
      directedLanguage (lifted start) (lifted zero) := by
  rw [ReferenceStep.step_iff_mem_of_enough reference_enough.1,reference_results.1]
  decide +kernel

theorem nested_lift_reference : ReferenceStep.Step
    (providerRelEnv (directedEnvironment [start,start]).provider)
    directedLanguage (lifted (lifted start)) (lifted (lifted done)) := by
  rw [ReferenceStep.step_iff_mem_of_enough reference_enough.2.2.2,reference_results.2.2.2]
  simp

theorem nested_lift_semantic_root : ∃ trace captured completed history,
    RootFiring (directedEnvironment [start,start]) [] term (lifted (lifted start)) 1
      trace captured completed history (lifted (lifted done)) :=
  (lift_authored_iff (checkOpenPatternWellSorted_sound (by cbv))).mpr nested_lift_reference

def liftGoal (body : Pattern) : Execution.Goal := .root [] term (lifted body) 1

def allGoal : Execution.Goal := .root [] term allStart 2

def runLift (body : Pattern) : Execution.State (directedEnvironment [start,start]) (liftGoal body) :=
  Execution.run (directedEnvironment [start,start]) (liftGoal body) 1200
    (Execution.start (directedEnvironment [start,start]) (liftGoal body))

def runAll (tasks : List Pattern) : Execution.State (directedEnvironment tasks) allGoal :=
  Execution.run (directedEnvironment tasks) allGoal 4000
    (Execution.start (directedEnvironment tasks) allGoal)

def rootTarget {activeEnvironment : Environment} {bound : List TypeExpr} {type : TypeExpr}
    {source : Pattern} {index : Nat} : Execution.Result activeEnvironment (.root bound type source index) → Pattern
  | .root _ _ _ _ target _ => target

theorem retained_direct_children :
    (runLift start).answers.map rootTarget = List.replicate 4 (lifted done) ∧
    (runAll [start,start]).answers.map rootTarget = List.replicate 16 allDone ∧
    (runAll [start,one]).answers.map rootTarget = [] := by decide +kernel

theorem retained_children_complete :
    Execution.complete (directedEnvironment [start,start]) (liftGoal start) (runLift start) = true ∧
    Execution.complete (directedEnvironment [start,start]) allGoal (runAll [start,start]) = true ∧
    Execution.complete (directedEnvironment [start,one]) allGoal (runAll [start,one]) = true := by decide +kernel

/-- Without the refused stratification certificate, a same-ordinal child
cannot be inferred from a completed restricted runner. The independent
source and semantic root above do contain this nested step. -/
theorem unadmitted_nested_lift_runner :
    (runLift (lifted start)).answers.map rootTarget = [] ∧
    Execution.complete (directedEnvironment [start,start]) (liftGoal (lifted start))
      (runLift (lifted start)) = true := by decide +kernel

def interrupted : Execution.State (directedEnvironment [start,start]) allGoal :=
  Execution.run (directedEnvironment [start,start]) allGoal 1
    (Execution.start (directedEnvironment [start,start]) allGoal)

theorem interrupted_pending :
    Execution.complete (directedEnvironment [start,start]) allGoal interrupted = false := by decide +kernel

theorem interrupted_same_full_state :
    Execution.run (directedEnvironment [start,start]) allGoal 3999 interrupted = runAll [start,start] :=
  (Execution.run_add (directedEnvironment [start,start]) allGoal 1 3999
    (Execution.start (directedEnvironment [start,start]) allGoal)).symm

#print axioms actual_admission_obligation
#print axioms actual_core
#print axioms actual_authored_step_iff
#print axioms lift_ordinal
#print axioms lift_authored_iff
#print axioms reference_enough
#print axioms reference_results
#print axioms reference_lift
#print axioms reference_all
#print axioms missing_task_reference_refused
#print axioms wrong_conclusion_reference_refused
#print axioms nested_lift_reference
#print axioms nested_lift_semantic_root
#print axioms retained_direct_children
#print axioms retained_children_complete
#print axioms unadmitted_nested_lift_runner
#print axioms interrupted_pending
#print axioms interrupted_same_full_state

/-- The existing shared scheduler searches all declarations at child calls.
Its explicit recursion depth is distinct from the ordinal-only runner above. -/
def scheduledGoal (depth : Nat) : StructuralDescent.Scheduled.Goal :=
  .root depth [] term (lifted (lifted start)) 1

def scheduledState (depth : Nat) : StructuralDescent.Scheduled.State
    (directedEnvironment [start,start]) (scheduledGoal depth) :=
  StructuralDescent.Scheduled.run (directedEnvironment [start,start]) (scheduledGoal depth) 3000
    (StructuralDescent.Scheduled.start (directedEnvironment [start,start]) (scheduledGoal depth))

def scheduledTarget {depth : Nat} : StructuralDescent.Scheduled.Result
    (directedEnvironment [start,start]) (scheduledGoal depth) → Pattern
  | .root _ _ _ _ target _ => target

theorem scheduled_same_ordinal_child :
    (scheduledState 3).answers.map scheduledTarget = List.replicate 4 (lifted (lifted done)) ∧
      StructuralDescent.Scheduled.complete (directedEnvironment [start,start])
        (scheduledGoal 3) (scheduledState 3) = true := by decide +kernel

/-- Exhausted recursion depth retains an unresolved obligation. It cannot
be read as an empty completed source successor set. -/
theorem exhausted_depth_is_unresolved :
    (scheduledState 2).answers = [] ∧
      (scheduledState 2).agenda = [] ∧
      StructuralDescent.Scheduled.Obligation.depthExhausted 0 ∈ (scheduledState 2).unresolved ∧
      StructuralDescent.Scheduled.complete (directedEnvironment [start,start])
        (scheduledGoal 2) (scheduledState 2) = false := by decide +kernel

theorem scheduled_resume_same_full_state :
    StructuralDescent.Scheduled.run (directedEnvironment [start,start]) (scheduledGoal 3) 2999
      (StructuralDescent.Scheduled.run (directedEnvironment [start,start]) (scheduledGoal 3) 1
        (StructuralDescent.Scheduled.start (directedEnvironment [start,start]) (scheduledGoal 3))) =
      scheduledState 3 :=
  (StructuralDescent.Scheduled.run_add (directedEnvironment [start,start]) (scheduledGoal 3) 1 2999
    (StructuralDescent.Scheduled.start (directedEnvironment [start,start]) (scheduledGoal 3))).symm

/-- Arbitrary provider-generated quantified children do not inherit the
strict subsource property of a captured constructor child. -/
theorem quantified_structural_certificate_refused :
    StructuralDescent.checkEnvironment (directedEnvironment [start,start]) = false := by cbv

/-- The existing structural checker independently qualifies the captured
child shape when the provider-generated child rule is absent. This is not
a replacement for the original three-rule acceptance domain. -/
def capturedChildEnvironment : Environment :=
  {directedEnvironment [start,start] with
    language := {directedLanguage with rewrites := [serviceCompiled.rule,liftCompiled.rule]}
    specifications := [(0,serviceCompiled.binding.spec),(1,liftCompiled.binding.spec)]}

theorem captured_child_structural_certificate : StructuralDescent.checkEnvironment capturedChildEnvironment = true := by
  cbv

/-- Every ordinary source derivation in the captured-child subprofile has
the existing finite source-size depth bound. -/
theorem captured_child_depth_bound (source : Pattern) (bound : List TypeExpr) (type : TypeExpr)
    (answer : StructuralDescent.Execution.RootAnswer capturedChildEnvironment bound type source) :
    answer.requiredDepth ≤ PatternTreeSize.nodes source :=
  StructuralDescent.firing_depth_bound capturedChildEnvironment captured_child_structural_certificate
    source bound type answer

#print axioms scheduled_same_ordinal_child
#print axioms exhausted_depth_is_unresolved
#print axioms scheduled_resume_same_full_state
#print axioms quantified_structural_certificate_refused
#print axioms captured_child_structural_certificate
#print axioms captured_child_depth_bound

/-- The actual directed source still declares set laws through its data
carrier. Literal specialization must not assume this language is equation-free. -/
theorem directed_has_collection_laws : directedLanguage.isEquationFree = false := by cbv

theorem directed_equations_unconditional : ReferenceStep.UnconditionalEquations directedLanguage := by
  intro equation member
  change equation ∈ [] at member
  cases member

def directedInternalPolicy (tasks : List Pattern) : ReferenceStep.InternalBoundaryPolicy :=
  ReferenceStep.declaredBoundaryPolicy (providerRelEnv (directedEnvironment tasks).provider)
    directedLanguage directed_equations_unconditional

/-- Nonempty local quantification with real child evidence specializes to the
explicit policy; no event is replaced by a boolean guard. -/
theorem declared_nonempty_quantified_children :
    ReferenceStep.StepWith (directedInternalPolicy [start,start])
      (providerRelEnv (directedEnvironment [start,start]).provider) directedLanguage allStart allDone :=
  ReferenceStep.stepWith_equational_of_presentation
    (ReferenceStep.equivalentSetoid _ _) reference_all

theorem declared_nested_child :
    ReferenceStep.StepWith (directedInternalPolicy [start,start])
      (providerRelEnv (directedEnvironment [start,start]).provider) directedLanguage
      (lifted (lifted start)) (lifted (lifted done)) :=
  ReferenceStep.stepWith_equational_of_presentation
    (ReferenceStep.equivalentSetoid _ _) nested_lift_reference

#print axioms directed_has_collection_laws
#print axioms directed_equations_unconditional
#print axioms declared_nonempty_quantified_children
#print axioms declared_nested_child

end Mettapedia.OSLF.MeTTaIL.GeneralPremise.SharedOutputControls.ReferenceRootControls.DirectedControls

namespace Mettapedia.OSLF.MeTTaIL.GeneralPremise.SharedOutputControls.RecursiveReadbackControls

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax Match MatchSpec ScopedRuleMatching RuleBinding GeneralFirstOrderProjection
open Mettapedia.GSLT.LanguageDef.WellSorted

def term : TypeExpr := .base "Term"
def atom (label : String) : Pattern := .apply label []

def nestedRule : RewriteRule where
  name := "nested-occurrence-readback"
  typeContext := [("x",term),("inside",.collection .hashSet term),("outside",.collection .hashBag term)]
  left := .apply "Box" [.collection .hashBag
    [.apply "SetData" [.collection .hashSet [.fvar "x"] (some "inside")],.fvar "x"] (some "outside")]
  right := .fvar "x"
  premises := []

def depthRule : RewriteRule where
  name := "same-capture-across-depths"
  typeContext := [("P",term)]
  left := .apply "Pair" [.fvar "P",.lambda none (.fvar "P")]
  right := .fvar "P"
  premises := []

def language : LanguageDef where
  name := "recursive-ordinary-scoped-readback"
  types := ["Term"]
  terms := [
    {label := "A",category := "Term",params := [],syntaxPattern := []},
    {label := "B",category := "Term",params := [],syntaxPattern := []},
    {label := "C",category := "Term",params := [],syntaxPattern := []},
    {label := "Box",category := "Term",params := [.simple "items" (.collection .hashBag term)],syntaxPattern := [],collectionRepresentation := .wrapped},
    {label := "SetData",category := "Term",params := [.simple "items" (.collection .hashSet term)],syntaxPattern := [],collectionRepresentation := .wrapped},
    {label := "Pair",category := "Term",params := [.simple "first" term,.simple "body" (.arrow term term)],syntaxPattern := []}]
  equations := []
  rewrites := [nestedRule,depthRule]

def nestedTarget : Pattern := .apply "Box" [.collection .hashBag
  [.apply "SetData" [.collection .hashSet [atom "A",atom "B"] none],atom "A",atom "C"] none]

def nestedBindings : Bindings :=
  [("outside",.collection .hashBag [atom "C"] none),
   ("inside",.collection .hashSet [atom "B"] none),("x",atom "A")]

def nestedCaptured : Assignment := nestedBindings.map fun entry => (entry.1,rootValue 0 entry.2)

theorem nested_schema_binderFree : binderFree nestedRule.left = true := by cbv

theorem nested_target_typed : OpenPatternWellSorted language FreeTypeContext.empty [] term nestedTarget :=
  ⟨checkHasType_sound (by cbv),by cbv,by cbv,by cbv⟩

theorem nested_raw_match : nestedBindings ∈ matchPattern nestedRule.left nestedTarget := by decide +kernel

theorem nested_scoped_match : GeneralScopedMatch.Matches nestedRule
    (GeneralRuleBindingInference.inferredSpec nestedRule) 0 .left [] 0 []
      nestedRule.left nestedTarget nestedCaptured :=
  GeneralScopedMatch.matchAt_iff.mp (by decide +kernel)

theorem nested_ordinary_to_scoped :
    ∃ final,GeneralScopedMatch.Matches nestedRule (GeneralRuleBindingInference.inferredSpec nestedRule)
        0 .left [] 0 [] nestedRule.left nestedTarget final ∧ ScopedCompatible 0 nestedBindings final := by
  apply binderFree_scoped_of_matchRel nested_schema_binderFree (NameCoherent.left nestedRule)
  · intro name occurs
    simp only [nestedRule,Pattern.freeFvarNames,List.flatMap_cons,List.flatMap_nil,
      List.append_nil,Option.toList_some,List.mem_append,List.mem_cons,
      List.not_mem_nil,or_false] at occurs
    rcases occurs with ((rfl | rfl) | rfl) | rfl <;> cbv
  · exact matchPattern_sound nested_raw_match
  · intro entry member
    simp only [nestedBindings,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl <;> cbv
  · cbv
  · exact nested_target_typed.2.2.1
  · intro entry member; cases member

theorem nested_complete_binding_readback :
    ∃ bindings,bindings ∈ matchPattern nestedRule.left nestedTarget ∧
      BindingAgreement nestedRule.left.freeFvarNames nestedCaptured bindings := by
  apply binderFree_matching_bindingAgreement nested_schema_binderFree nested_scoped_match
  intro name value found
  simp only [nestedCaptured,nestedBindings,List.map_cons,List.map_nil,lookup,List.find?_cons,
    List.find?_nil] at found
  split at found
  · cases Option.some.inj found; exact ⟨rfl,rfl,by cbv⟩
  · split at found
    · cases Option.some.inj found; exact ⟨rfl,rfl,by cbv⟩
    · split at found
      · cases Option.some.inj found; exact ⟨rfl,rfl,by cbv⟩
      · cases found

/-- Ordered source names and actual residual kinds survive both directions;
no equation or intrinsic collection identification is used in these controls. -/
theorem nested_residuals_retained :
    (lookup nestedCaptured "inside").map ContextualValue.body = some (.collection .hashSet [atom "B"] none) ∧
      (lookup nestedCaptured "outside").map ContextualValue.body = some (.collection .hashBag [atom "C"] none) := by cbv

def depthTarget : Pattern := .apply "Pair" [.bvar 0,.lambda none (.bvar 1)]
def depthCaptured : Assignment := [("P",rootValue 1 (.bvar 0))]

theorem depth_source_typed : OpenPatternWellSorted language FreeTypeContext.empty [term] term depthTarget :=
  ⟨checkHasType_sound (by cbv),by cbv,by cbv,by cbv⟩

theorem depth_schema_typed :
    HasType language (FreeTypeContext.ofList depthRule.typeContext) [] depthRule.left term :=
  checkHasType_sound (by cbv)

/-- Scope-correct recovery stores one ambient body for occurrences at
several depths. The ordinary matcher compares their raw local bodies and
rejects this well-typed source. Thus a blanket all-binder projection is false. -/
theorem different_binder_depths_separate_matchers :
    depthCaptured ∈ matchRuleAt depthRule (GeneralRuleBindingInference.inferredSpec depthRule) 1 depthTarget ∧
      matchPattern depthRule.left depthTarget = [] ∧ binderFree depthRule.left = false := by decide +kernel

def openTailSchema : Pattern := .collection .hashBag [] (some "rest")
def openTailSubject : Pattern := .collection .hashBag [atom "A"] (some "open")
def openTailRule : RewriteRule where
  name := "open-tail"
  typeContext := [("rest",.collection .hashBag term)]
  left := openTailSchema
  right := openTailSchema
  premises := []

/-- Ordinary collection matching accepts a raw open-tail presentation, while
the scoped traversal requires an object source with no open collection tail. -/
theorem open_target_tail_requires_eligibility :
    [[("rest",.collection .hashBag [atom "A"] none)]] = matchPattern openTailSchema openTailSubject ∧
      matchRuleAt openTailRule (GeneralRuleBindingInference.inferredSpec openTailRule) 0 openTailSubject = [] ∧
      isObjectPattern openTailSubject = false := by decide +kernel

#print axioms nested_schema_binderFree
#print axioms nested_target_typed
#print axioms nested_raw_match
#print axioms nested_scoped_match
#print axioms nested_ordinary_to_scoped
#print axioms nested_complete_binding_readback
#print axioms nested_residuals_retained
#print axioms depth_source_typed
#print axioms depth_schema_typed
#print axioms different_binder_depths_separate_matchers
#print axioms open_target_tail_requires_eligibility

end Mettapedia.OSLF.MeTTaIL.GeneralPremise.SharedOutputControls.RecursiveReadbackControls


namespace Mettapedia.OSLF.MeTTaIL.GeneralPremise.SharedOutputControls.RecursiveReadbackControls
open _root_.Mettapedia.OSLF.MeTTaIL.Syntax Match ScopedRuleMatching RuleBinding GeneralFirstOrderProjection

def reconstructedRule : RewriteRule := {nestedRule with
  right := .apply "Box" [.collection .hashBag
    [.fvar "x", .apply "SetData" [.collection .hashSet [.fvar "x"] (some "inside")]]
    (some "outside")]}

def reconstructedTarget : Pattern := .apply "Box" [.collection .hashBag
  [atom "A", .apply "SetData" [.collection .hashSet [atom "A", atom "B"] none], atom "C"] none]

theorem nested_captures_root_values : RootValues 0 nestedCaptured := by
  apply matching_rootValues (rule := nestedRule) (spec := GeneralRuleBindingInference.inferredSpec nestedRule)
    (by decide +kernel) (initial := [])
  · intro name value found
    cases found
  · exact nested_scoped_match

theorem nested_collection_instantiation :
    instantiateAt? reconstructedRule (GeneralRuleBindingInference.inferredSpec reconstructedRule)
      0 .right [] 0 nestedCaptured reconstructedRule.right = some reconstructedTarget := by decide +kernel

theorem nested_collection_instantiation_readback :
    applyBindings (ordinary nestedCaptured) reconstructedRule.right = reconstructedTarget :=
  binderFree_instantiation_readout (by decide +kernel) nested_captures_root_values
    nested_collection_instantiation

def wrongRestCaptured : Assignment :=
  [("outside", rootValue 0 (.collection .hashSet [atom "C"] none)),
   ("inside", rootValue 0 (.collection .hashSet [atom "B"] none)),
   ("x", rootValue 0 (atom "A"))]

theorem wrong_rest_kind_refused :
    instantiateAt? reconstructedRule (GeneralRuleBindingInference.inferredSpec reconstructedRule)
      0 .right [] 0 wrongRestCaptured reconstructedRule.right = none := by decide +kernel

theorem binder_instantiation_does_not_read_back_literally :
    instantiateAt? depthRule (GeneralRuleBindingInference.inferredSpec depthRule)
      1 .left [] 0 depthCaptured depthRule.left = some depthTarget ∧
      applyBindings (ordinary depthCaptured) depthRule.left ≠ depthTarget ∧
      binderFree depthRule.left = false := by decide +kernel

#print axioms nested_captures_root_values
#print axioms nested_collection_instantiation
#print axioms nested_collection_instantiation_readback
#print axioms wrong_rest_kind_refused
#print axioms binder_instantiation_does_not_read_back_literally
end Mettapedia.OSLF.MeTTaIL.GeneralPremise.SharedOutputControls.RecursiveReadbackControls

namespace Mettapedia.OSLF.MeTTaIL.GeneralPremise.SharedOutputControls.WrappedKindBoundary

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax
open _root_.Mettapedia.OSLF.MeTTaIL
open Mettapedia.GSLT.LanguageDef WellSorted EquationSemantics
open ChildPresentation (term a b)

/-- The same declared field, varying only its collection type. -/
def wrappedLanguage (kind : CollType) : LanguageDef :=
  {RetainedCollections.OutputBoundary.wrappedOnlyLanguage with
    name := "wrapped-kind-source-boundary"
    terms := RetainedCollections.OutputBoundary.wrappedOnlyLanguage.terms.map fun rule =>
      if rule.label = "Choice" then
        {rule with params := [.simple "elements" (.collection kind term)]} else rule
    rewrites := []}

def wrapped (kind : CollType) (elements : List Pattern) : Pattern :=
  .apply "Choice" [.collection kind elements none]

def fieldRule (kind : CollType) : GrammarRule :=
  {RetainedCollections.OutputBoundary.choiceCarrier with
    params := [.simple "elements" (.collection kind term)],collectionRepresentation := .wrapped}

theorem field_declared (kind : CollType) : fieldRule kind ∈ (wrappedLanguage kind).terms := by
  cases kind <;> decide +kernel

theorem no_authored_equations (kind : CollType) : (wrappedLanguage kind).equations = [] := rfl

theorem no_algebra_declarations (kind : CollType) : (wrappedLanguage kind).hasAlgebraDeclarations = false := by
  cases kind <;> cbv

theorem no_bare_carriers (kind : CollType) :
    ∀ rule ∈ (wrappedLanguage kind).terms,CollectionLaws.bareKind rule = none := by
  have checked : (wrappedLanguage kind).terms.all (fun rule => CollectionLaws.bareKind rule == none) = true := by
    cases kind <;> cbv
  intro rule member
  exact beq_iff_eq.mp ((List.all_eq_true.mp checked) rule member)

theorem wrapped_sources_typed (kind : CollType) :
    OpenPatternWellSorted (wrappedLanguage kind) FreeTypeContext.empty [] term (wrapped kind [a,b]) ∧
      OpenPatternWellSorted (wrappedLanguage kind) FreeTypeContext.empty [] term (wrapped kind [b,a]) := by
  cases kind <;>
    exact ⟨checkOpenPatternWellSorted_sound (by cbv),checkOpenPatternWellSorted_sound (by cbv)⟩

/-- Eligibility retains the field declaration even though its outer
representation is named rather than a bare base-sort collection. -/
theorem wrapped_source_collections (kind : CollType) :
    ReferenceStep.SourceCollections (wrappedLanguage kind) (wrapped kind [a,b]) := by
  refine .apply ?_
  intro value member
  cases List.mem_singleton.mp member
  refine .collection (Or.inr ⟨fieldRule kind,field_declared kind,?_⟩) ?_
  · exact ⟨.simple "elements" (.collection kind term),by simp [fieldRule],term,.here,
      FreeTypeContext.empty,[],checkHasType_sound (by cases kind <;> cbv)⟩
  · intro value member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl <;> exact .apply (by intro child member; cases member)

theorem wrapped_permutation_same {kind : CollType} (unordered : CanonicalBags.Unordered kind = true) :
    CanonicalBags.Same (wrapped kind [a,b]) (wrapped kind [b,a]) := by
  have row : CanonicalBags.BagStep (.collection kind [a,b] none) (.collection kind [b,a] none) :=
    .permute unordered (.swap _ _ [])
  exact CanonicalBags.BagStep.canon_eq (CanonicalBags.BagStep.apply (before := []) (after := []) row)

/-- Permutation is licensed by the field's declared kind, without adding a
bare carrier or an authored equation. -/
theorem wrapped_permutation_source {kind : CollType}
    (unordered : CanonicalBags.Unordered kind = true) (relEnv : Engine.RelationEnv) :
    ReferenceStep.Equivalent relEnv (wrappedLanguage kind) (wrapped kind [a,b]) (wrapped kind [b,a]) :=
  ReferenceStep.equivalent_of_same (wrapped_source_collections kind) (wrapped_permutation_same unordered)

theorem wrapped_set_permutation (relEnv : Engine.RelationEnv) :
    ReferenceStep.Equivalent relEnv (wrappedLanguage .hashSet)
      (wrapped .hashSet [a,b]) (wrapped .hashSet [b,a]) :=
  wrapped_permutation_source (by decide) relEnv

theorem wrapped_bag_permutation (relEnv : Engine.RelationEnv) :
    ReferenceStep.Equivalent relEnv (wrappedLanguage .hashBag)
      (wrapped .hashBag [a,b]) (wrapped .hashBag [b,a]) :=
  wrapped_permutation_source (by decide) relEnv

theorem wrapped_set_duplicate_elimination (relEnv : Engine.RelationEnv) :
    ReferenceStep.Equivalent relEnv (wrappedLanguage .hashSet)
      (wrapped .hashSet [a,a]) (wrapped .hashSet [a]) := by
  have good : ReferenceStep.SourceCollections (wrappedLanguage .hashSet) (wrapped .hashSet [a,a]) := by
    refine .apply ?_
    intro value member
    cases List.mem_singleton.mp member
    refine .collection (Or.inr ⟨fieldRule .hashSet,field_declared _,?_⟩) ?_
    · exact ⟨.simple "elements" (.collection .hashSet term),by simp [fieldRule],term,.here,
        FreeTypeContext.empty,[],checkHasType_sound (by cbv)⟩
    · intro value member
      simp only [List.mem_cons,List.not_mem_nil,or_false,or_self] at member
      subst value
      exact .apply (by intro child member; cases member)
  exact ReferenceStep.equivalent_of_same good (CanonicalBags.BagStep.canon_eq
    (CanonicalBags.BagStep.apply (before := []) (after := []) (.members fun value => by simp)))

/-- Intrinsic laws keep the actual wrapped endpoint type, binder metadata
and scope; they do not license changing its data role. -/
theorem wrapped_permutation_preserves_typing {kind : CollType}
    (unordered : CanonicalBags.Unordered kind = true) (relEnv : Engine.RelationEnv) :
    OpenPatternWellSorted (wrappedLanguage kind) FreeTypeContext.empty [] term (wrapped kind [b,a]) :=
  ReferenceStep.equivalent_openPatternWellSorted (no_authored_equations kind) (no_algebra_declarations kind)
    (wrapped_permutation_source unordered relEnv) (wrapped_sources_typed kind).1

theorem bag_multiplicity_retained (relEnv : Engine.RelationEnv) :
    ¬ ReferenceStep.Equivalent relEnv (wrappedLanguage .hashBag)
      (wrapped .hashBag [a,a]) (wrapped .hashBag [a]) := by
  intro related
  have same := ReferenceStep.equivalent_same (no_authored_equations _) (no_algebra_declarations _) related
  simp only [CanonicalBags.Same,wrapped,CanonicalBags.canon_apply,List.map_cons,List.map_nil,
    Pattern.apply.injEq,List.cons.injEq,and_true,true_and] at same
  rw [CanonicalBags.canon_collection,CanonicalBags.canon_collection] at same
  have lengths := congrArg List.length (Pattern.collection.inj same).2.1
  simp [CanonicalBags.arrange_bag,(PatternLexOrder.sortLex_perm _).length_eq] at lengths

theorem vector_order_retained (relEnv : Engine.RelationEnv) :
    ¬ ReferenceStep.Equivalent relEnv (wrappedLanguage .vec)
      (wrapped .vec [a,b]) (wrapped .vec [b,a]) := by
  intro related
  have same := ReferenceStep.equivalent_same (no_authored_equations _) (no_algebra_declarations _) related
  simp [CanonicalBags.Same,wrapped,CanonicalBags.canon,CanonicalBags.arrange,a,b] at same

theorem undeclared_wrapper_collapse_refused (kind : CollType) (relEnv : Engine.RelationEnv) :
    ¬ ReferenceStep.Equivalent relEnv (wrappedLanguage kind) (wrapped kind [a]) a := by
  intro related
  have same := ReferenceStep.equivalent_same (no_authored_equations _) (no_algebra_declarations _) related
  obtain ⟨arguments,shape,_⟩ := CanonicalBags.same_apply same
  simp [a] at shape

theorem wrong_kind_field_not_typed :
    ¬ HasType (wrappedLanguage .hashSet) FreeTypeContext.empty [] (wrapped .hashBag [a]) term := by
  intro typed
  have accepted := checkHasType_complete_of_object typed (by cbv)
  change false = true at accepted
  cases accepted

/-- The intrinsic source generators still require a closed outer literal.
This does not forbid equations inside a typed element of an open schema. -/
theorem no_kind_generator_on_open_tail (kind : CollType) (values : List Pattern) (tailName : String)
    (target : Pattern) :
    ¬ DerivedInstance (wrappedLanguage kind) (.collection kind values (some tailName)) target := by
  intro law
  cases law

/-- A new, unrelated base sort and carrier do not change old equality. -/
def unrelatedCarrier (kind : CollType) : GrammarRule where
  label := "UnrelatedCarrier"
  category := "Extra"
  params := [.simple "elements" (.collection kind term)]
  syntaxPattern := []
  collectionRepresentation := .bare

def extendedLanguage (kind : CollType) : LanguageDef :=
  {wrappedLanguage kind with
    types := (wrappedLanguage kind).types ++ [TypeDecl.plain "Extra"]
    terms := (wrappedLanguage kind).terms ++ [unrelatedCarrier kind]}

theorem extension_keeps_old_declarations (kind : CollType) :
    (wrappedLanguage kind).terms ⊆ (extendedLanguage kind).terms ∧
      (extendedLanguage kind).equations = (wrappedLanguage kind).equations ∧
      (extendedLanguage kind).rewrites = (wrappedLanguage kind).rewrites :=
  ⟨List.subset_append_left _ _,rfl,rfl⟩

theorem old_terms_still_typed_after_extension (kind : CollType) :
    OpenPatternWellSorted (extendedLanguage kind) FreeTypeContext.empty [] term (wrapped kind [a,b]) ∧
      OpenPatternWellSorted (extendedLanguage kind) FreeTypeContext.empty [] term (wrapped kind [b,a]) := by
  cases kind <;>
    exact ⟨checkOpenPatternWellSorted_sound (by cbv),checkOpenPatternWellSorted_sound (by cbv)⟩

theorem no_new_constructor_in_old_terms (kind : CollType) :
    "UnrelatedCarrier" ∉ ((wrapped kind [a,b]).constructorRefs.map Prod.fst) ∧
      "UnrelatedCarrier" ∉ ((wrapped kind [b,a]).constructorRefs.map Prod.fst) := by cases kind <;> decide +kernel

theorem unrelated_extension_conservative (kind : CollType) (relEnv : Engine.RelationEnv) (target : Pattern) :
    ReferenceStep.Equivalent relEnv (wrappedLanguage kind) (wrapped kind [a,b]) target ↔
      ReferenceStep.Equivalent relEnv (extendedLanguage kind) (wrapped kind [a,b]) target := by
  apply ReferenceStep.equivalent_iff_of_terms_subset (extension_keeps_old_declarations kind).1
    (no_authored_equations kind) (no_algebra_declarations kind) rfl
    (by cases kind <;> cbv) (wrapped_source_collections kind)

def nestedLanguage : LanguageDef :=
  {wrappedLanguage .hashSet with
    name := "nested-wrapped-kind-source-boundary"
    terms := (wrappedLanguage .hashSet).terms.map fun rule =>
      if rule.label = "Choice" then
        {rule with params := [.simple "elements" (.collection .hashSet (.collection .hashSet term))]} else rule}

def nestedFieldRule : GrammarRule :=
  {fieldRule .hashSet with params := [.simple "elements" (.collection .hashSet (.collection .hashSet term))]}

def innerSet (values : List Pattern) : Pattern := .collection .hashSet values none

def nestedSource : Pattern := .apply "Choice" [innerSet [innerSet [a,a],innerSet [b,a]]]
def nestedTarget : Pattern := .apply "Choice" [innerSet [innerSet [a],innerSet [a,b]]]

theorem nested_field_declared : nestedFieldRule ∈ nestedLanguage.terms := by decide +kernel

theorem nested_inner_eligible {values : List Pattern}
    (typed : checkHasType nestedLanguage FreeTypeContext.empty [] (innerSet values)
      (.collection .hashSet term) = true)
    (children : ∀ value ∈ values,ReferenceStep.SourceCollections nestedLanguage value) :
    ReferenceStep.SourceCollections nestedLanguage (innerSet values) := by
  exact .collection (Or.inr ⟨nestedFieldRule,nested_field_declared,
    .simple "elements" (.collection .hashSet (.collection .hashSet term)),by simp [nestedFieldRule],
    term,.element .here,FreeTypeContext.empty,[],checkHasType_sound typed⟩) children

/-- Inner set laws are licensed by the recursively declared element type,
without an unrelated bare carrier or outer flattening law. -/
theorem nested_source_collections : ReferenceStep.SourceCollections nestedLanguage nestedSource := by
  refine .apply ?_
  intro value member
  cases List.mem_singleton.mp member
  refine .collection (Or.inr ⟨nestedFieldRule,nested_field_declared,
    .simple "elements" (.collection .hashSet (.collection .hashSet term)),by simp [nestedFieldRule],
    .collection .hashSet term,.here,FreeTypeContext.empty,[],checkHasType_sound (by cbv)⟩) ?_
  intro value member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · apply nested_inner_eligible (by cbv)
    intro value member
    simp only [List.mem_cons,List.not_mem_nil,or_false,or_self] at member
    subst value
    exact .apply (by intro child member; cases member)
  · apply nested_inner_eligible (by cbv)
    intro value member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl <;> exact .apply (by intro child member; cases member)

theorem nested_source_typed : OpenPatternWellSorted nestedLanguage FreeTypeContext.empty [] term nestedSource :=
  checkOpenPatternWellSorted_sound (by cbv)

theorem nested_source_equivalent (relEnv : Engine.RelationEnv) :
    ReferenceStep.Equivalent relEnv nestedLanguage nestedSource nestedTarget := by
  have left : CanonicalBags.Same (innerSet [a,a]) (innerSet [a]) :=
    CanonicalBags.BagStep.canon_eq (.members fun value => by simp)
  have right : CanonicalBags.Same (innerSet [b,a]) (innerSet [a,b]) :=
    CanonicalBags.BagStep.canon_eq (.permute rfl (.swap _ _ []))
  exact ReferenceStep.equivalent_of_same nested_source_collections
    (CanonicalBags.same_apply_congr "Choice" (.cons
      (CanonicalBags.same_collection_congr .hashSet none (.cons left (.cons right .nil))) .nil))

theorem nested_target_typed (relEnv : Engine.RelationEnv) :
    OpenPatternWellSorted nestedLanguage FreeTypeContext.empty [] term nestedTarget :=
  ReferenceStep.equivalent_openPatternWellSorted rfl (by cbv) (nested_source_equivalent relEnv) nested_source_typed

theorem wrapped_language_valid (kind : CollType) : (wrappedLanguage kind).validate = [] := by cases kind <;> cbv

theorem extended_language_valid (kind : CollType) : (extendedLanguage kind).validate = [] := by cases kind <;> cbv

theorem nested_language_valid : nestedLanguage.validate = [] := by cbv

#print axioms field_declared
#print axioms no_authored_equations
#print axioms no_algebra_declarations
#print axioms no_bare_carriers
#print axioms wrapped_sources_typed
#print axioms wrapped_source_collections
#print axioms wrapped_permutation_same
#print axioms wrapped_permutation_source
#print axioms wrapped_set_permutation
#print axioms wrapped_bag_permutation
#print axioms wrapped_set_duplicate_elimination
#print axioms wrapped_permutation_preserves_typing
#print axioms bag_multiplicity_retained
#print axioms vector_order_retained
#print axioms undeclared_wrapper_collapse_refused
#print axioms wrong_kind_field_not_typed
#print axioms no_kind_generator_on_open_tail
#print axioms extension_keeps_old_declarations
#print axioms old_terms_still_typed_after_extension
#print axioms no_new_constructor_in_old_terms
#print axioms unrelated_extension_conservative
#print axioms nested_field_declared
#print axioms nested_inner_eligible
#print axioms nested_source_collections
#print axioms nested_source_typed
#print axioms nested_source_equivalent
#print axioms nested_target_typed
#print axioms wrapped_language_valid
#print axioms extended_language_valid
#print axioms nested_language_valid

end Mettapedia.OSLF.MeTTaIL.GeneralPremise.SharedOutputControls.WrappedKindBoundary


namespace Mettapedia.OSLF.MeTTaIL.GeneralPremise.SharedOutputControls.RecursiveReferenceControls

open _root_.Mettapedia.OSLF.MeTTaIL
open _root_.Mettapedia.OSLF.MeTTaIL.Syntax Match ScopedRuleMatching RuleBinding GeneralFirstOrderProjection
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.Framework.GeneralCanonicalAgreement QuantifiedReference
open RecursiveReadbackControls (term atom nestedRule nestedTarget)

set_option maxRecDepth 8000
set_option maxHeartbeats 1200000

def childSchema : Pattern := .apply "Box" [.collection .hashBag
  [.apply "SetData" [.collection .hashSet [.fvar "y"] (some "childInside")],.fvar "y"]
  (some "childOutside")]

def childTarget : Pattern := .apply "Box" [.collection .hashBag
  [.apply "SetData" [.collection .hashSet [atom "B",atom "C"] none],atom "B",atom "A"] none]

def childRule : RewriteRule where
  name := "produce-nested-collection"
  typeContext := []
  left := atom "B"
  right := childTarget
  premises := []

def parentRule : RewriteRule where
  name := "query-nested-collection-and-step-every-residual"
  typeContext := nestedRule.typeContext ++
    [("item",term),("y",term),("childInside",.collection .hashSet term),
      ("childOutside",.collection .hashBag term)]
  left := atom "A"
  right := atom "C"
  premises := [.relationQuery "nested" [nestedRule.left],
    .forAll "inside" "item" (.congruence (.fvar "item") childSchema)]

def language : LanguageDef := {RecursiveReadbackControls.language with
  name := "recursive-conditional-source-readback"
  rewrites := [childRule,parentRule]}

def provider (present : Bool) : ProviderSnapshot where
  signatures := [⟨"nested",[term],[.output]⟩]
  rows := if present then [⟨"nested",[nestedTarget]⟩] else []

def environment (present : Bool) : Environment where
  language := language
  free := FreeTypeContext.empty
  provider := provider present
  specifications := [(0,GeneralRuleBindingInference.inferredSpec childRule),
    (1,GeneralRuleBindingInference.inferredSpec parentRule)]

theorem recursive_shapes : ∀ rule ∈ language.rewrites,
    ∀ premise ∈ rule.premises,DirectedValidationWith (fun schema => binderFree schema = true) premise := by
  intro rule member premise occurs
  change rule ∈ [childRule,parentRule] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · change premise ∈ [] at occurs
    cases occurs
  · change premise ∈ ([Premise.relationQuery "nested" [nestedRule.left],
      .forAll "inside" "item" (.congruence (.fvar "item") childSchema)] : List Premise) at occurs
    simp only [List.mem_cons,List.not_mem_nil,or_false] at occurs
    rcases occurs with rfl | rfl
    · refine .query (by decide) ?_
      intro argument member
      cases List.mem_singleton.mp member
      decide +kernel
    · exact .quantified (.step (by decide +kernel) (by decide +kernel))

theorem recursive_profile (present : Bool) :
    DirectedProfileWith (fun schema => binderFree schema = true) (environment present) := by
  refine ⟨by cbv,?_,by rfl,?_⟩
  · cases present <;> cbv
  · intro index rule declared
    have branch : index = 0 ∨ index = 1 := by
      have bounded := (List.getElem?_eq_some_iff.mp declared).1
      change index < 2 at bounded
      omega
    rcases branch with rfl | rfl
    all_goals
      have selected := Option.some.inj (declared.symm.trans rfl)
      subst rule
      refine ⟨by cbv,by cbv,by decide,
        by cbv,by cbv,?_,?_,?_,?_,?_⟩
    · exact ⟨"B",[],rfl⟩
    · exact ⟨term,checkHasType_sound (by cbv),checkHasType_sound (by cbv)⟩
    · exact recursive_shapes childRule (by simp [language])
    · cases present <;> cbv
    · cases present <;> cbv
    · exact ⟨"A",[],rfl⟩
    · exact ⟨term,checkHasType_sound (by cbv),checkHasType_sound (by cbv)⟩
    · exact recursive_shapes parentRule (by simp [language])
    · cases present <;> cbv
    · cases present <;> cbv

/-- The provider output and the child result have collection-shaped schemas;
the historical constructor-only profile does not contain this language. -/
theorem old_firstOrder_profile_refused :
    ¬ DirectedProfile (environment true) := by
  intro profile
  have row := profile.rows (index := 1) (rule := parentRule) rfl
  have shape := row.premises (.relationQuery "nested" [nestedRule.left]) (by simp [parentRule])
  cases shape with
  | query _ shapes =>
    have outer := shapes nestedRule.left (List.mem_singleton_self _)
    cases outer with
    | constructor _ _ children =>
      have impossible := children _ (List.mem_singleton_self _)
      cases impossible

def goal : Execution.Goal := .root [] term (atom "A") 1

def finished (present : Bool) : Execution.State (environment present) goal :=
  Execution.run (environment present) goal 1200 (Execution.start (environment present) goal)

def rootTarget {present : Bool} : Execution.Result (environment present) goal → Pattern
  | .root _ _ _ _ target _ => target

theorem actual_retained_nested_result :
    (finished true).answers.map rootTarget = [atom "C"] ∧
      (finished false).answers.map rootTarget = [] ∧
      Execution.complete (environment true) goal (finished true) = true ∧
      Execution.complete (environment false) goal (finished false) = true := by decide +kernel

/-- This source witness is constructed from the actual retained scheduler
answer by the shared recursive premise induction, not assumed in a profile. -/
theorem retained_nested_reference :
    ReferenceStep.Step (providerRelEnv (provider true)) language (atom "A") (atom "C") := by
  have present : atom "C" ∈ (finished true).answers.map rootTarget := by
    rw [actual_retained_nested_result.1]
    exact List.mem_singleton_self _
  obtain ⟨answer,_,target⟩ := List.mem_map.mp present
  cases answer with
  | root trace captured completed history result valid =>
    change result = atom "C" at target
    subst result
    obtain ⟨bindings,witnesses,source⟩ :=
      directed_root_toReference (recursive_profile true) _ (providerRelEnv_reads _) valid
    exact ⟨.rule 1 bindings witnesses,source⟩

def interrupted : Execution.State (environment true) goal :=
  Execution.run (environment true) goal 1 (Execution.start (environment true) goal)

theorem interrupted_pending : Execution.complete (environment true) goal interrupted = false := by decide +kernel

theorem resumed_full_state :
    Execution.run (environment true) goal 1199 interrupted = finished true :=
  (Execution.run_add (environment true) goal 1 1199 (Execution.start (environment true) goal)).symm

theorem literal_reference_controls :
    ReferenceStep.enough (providerRelEnv (provider true)) language 2 (atom "A") = true ∧
      ReferenceStep.enough (providerRelEnv (provider false)) language 2 (atom "A") = true ∧
      (ReferenceStep.stepsAt (providerRelEnv (provider true)) language 2 (atom "A")).map (·.2) = [atom "C"] ∧
      ReferenceStep.stepsAt (providerRelEnv (provider false)) language 2 (atom "A") = [] := by decide +kernel

theorem missing_provider_reference_refused (target : Pattern) :
    ¬ ReferenceStep.Step (providerRelEnv (provider false)) language (atom "A") target := by
  rw [ReferenceStep.step_iff_mem_of_enough literal_reference_controls.2.1,
    literal_reference_controls.2.2.2]
  simp

theorem wrong_conclusion_reference_refused :
    ¬ ReferenceStep.Step (providerRelEnv (provider true)) language (atom "A") (atom "B") := by
  rw [ReferenceStep.step_iff_mem_of_enough literal_reference_controls.1,
    literal_reference_controls.2.2.1]
  decide +kernel


/-- Ordinary object typing deliberately permits raw tail metadata. Source
capture eligibility therefore needs the separate actual schema-role check. -/
theorem typed_tail_metadata_is_not_capture_eligibility :
    HasType language (FreeTypeContext.ofList [("rest",term)]) []
        (.collection .hashBag [] (some "rest")) (.collection .hashBag term) ∧
      isObjectPattern (.collection .hashBag [] (some "rest")) = false ∧
      SchemaTyping.checkSchemaType [] language (FreeTypeContext.ofList [("rest",term)]) []
        (.collection .hashBag [] (some "rest")) (.collection .hashBag term) = false := by
  exact ⟨.collection (.nil [] term),rfl,by cbv⟩


def untypedRestRule : RewriteRule where
  name := "rest-requires-its-declared-collection-type"
  typeContext := [("rest",term)]
  left := .apply "Box" [.collection .hashBag [] (some "rest")]
  right := atom "C"
  premises := []

def untypedRestLanguage : LanguageDef := {language with rewrites := [untypedRestRule]}

def untypedRestEnvironment : Environment where
  language := untypedRestLanguage
  free := FreeTypeContext.empty
  provider := ⟨[],[],[]⟩
  specifications := [(0,GeneralRuleBindingInference.inferredSpec untypedRestRule)]

def untypedRestSource : Pattern := .apply "Box" [.collection .hashBag [atom "A"] none]

def untypedRestCaptured : Assignment := [("rest",rootValue 0 (.collection .hashBag [atom "A"] none))]

/-- Raw reference matching does not inspect the type context of a captured
rest. The object-typing judgment alone therefore cannot justify the inverse. -/
theorem raw_reference_accepts_untyped_rest :
    HasType untypedRestLanguage (FreeTypeContext.ofList untypedRestRule.typeContext) []
      untypedRestRule.left term ∧
      ReferenceStep.Step (providerRelEnv ⟨[],[],[]⟩) untypedRestLanguage untypedRestSource (atom "C") := by
  refine ⟨?_,?_⟩
  · let box : GrammarRule := {label := "Box",category := "Term",params := [.simple "items" (.collection .hashBag term)],syntaxPattern := [],collectionRepresentation := .wrapped}
    apply HasType.constructor (rule := box)
    · simp [box,untypedRestLanguage,language,RecursiveReadbackControls.language,
      RecursiveReadbackControls.term, Mettapedia.OSLF.MeTTaIL.GeneralPremise.SharedOutputControls.term]
    · simp [UsesBareCollection,box,GrammarRule.bareParams]
    · exact .cons (by trivial) rfl (.collection (.nil [] term)) .nil
  refine ⟨.rule 0 [("rest",.collection .hashBag [atom "A"] none)] [],?_⟩
  exact (ReferenceStep.checkStep_eq_some_iff _ _ _).mp (by decide +kernel)

theorem typed_firing_refuses_untyped_rest {trace : List GeneralScopedMatchMachine.BagChoice}
    {captured completed : Assignment} {history : List Event} {target : Pattern} :
    ¬ RootFiring untypedRestEnvironment [] term untypedRestSource 0 trace captured completed history target := by
  intro fired
  cases fired with
  | @fire _ _ _ _ _ actualRule actualSpec _ _ _ _ declared specified _ _ matching capturedTyped _ _ _ =>
    have sameRule : actualRule = untypedRestRule := Option.some.inj (declared.symm.trans rfl)
    subst actualRule
    have sameSpec : actualSpec = GeneralRuleBindingInference.inferredSpec untypedRestRule :=
      Option.some.inj (specified.symm.trans rfl)
    subst actualSpec
    have retained := GeneralScopedMatch.matchRuleAt_iff.mpr matching.matching
    have candidates : matchRuleAt untypedRestRule (GeneralRuleBindingInference.inferredSpec untypedRestRule)
        0 untypedRestSource = [untypedRestCaptured] := by decide +kernel
    change captured ∈ matchRuleAt untypedRestRule (GeneralRuleBindingInference.inferredSpec untypedRestRule)
      0 untypedRestSource at retained
    rw [candidates] at retained
    have sameCapture : captured = untypedRestCaptured := List.mem_singleton.mp retained
    subst captured
    have checked := checkTypedAssignment_complete capturedTyped
    have rejected : checkTypedAssignment untypedRestEnvironment
        ⟨0,untypedRestRule,GeneralRuleBindingInference.inferredSpec untypedRestRule,[],0,0⟩
        untypedRestCaptured = false := by decide +kernel
    rw [rejected] at checked
    cases checked

#print axioms raw_reference_accepts_untyped_rest
#print axioms typed_firing_refuses_untyped_rest

#print axioms typed_tail_metadata_is_not_capture_eligibility

#print axioms recursive_shapes
#print axioms recursive_profile
#print axioms old_firstOrder_profile_refused
#print axioms actual_retained_nested_result
#print axioms retained_nested_reference
#print axioms interrupted_pending
#print axioms resumed_full_state
#print axioms literal_reference_controls
#print axioms missing_provider_reference_refused
#print axioms wrong_conclusion_reference_refused

end Mettapedia.OSLF.MeTTaIL.GeneralPremise.SharedOutputControls.RecursiveReferenceControls


namespace Mettapedia.OSLF.MeTTaIL.GeneralPremise.SharedOutputControls.BareReferenceControls

open _root_.Mettapedia.OSLF.MeTTaIL
open _root_.Mettapedia.OSLF.MeTTaIL.Syntax Match ScopedRuleMatching RuleBinding GeneralFirstOrderProjection
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.CollectionConsumers
  (petriPlan reachabilityPlan marking graph token edge)
open Mettapedia.OSLF.Framework.GeneralCanonicalAgreement QuantifiedReference

set_option maxRecDepth 8000
set_option maxHeartbeats 1200000

def petriEnvironment : Environment := GeneralPlanEnvironment.environment petriPlan
def graphEnvironment : Environment := GeneralPlanEnvironment.environment reachabilityPlan

theorem petri_forward_profile :
    DirectedForwardProfile (fun schema => binderFree schema = true) petriEnvironment := by
  refine ⟨rfl,?_⟩
  intro index rule declared
  have branch : index = 0 ∨ index = 1 := by
    have bounded := (List.getElem?_eq_some_iff.mp declared).1
    have length : petriEnvironment.language.rewrites.length = 2 := by cbv
    rw [length] at bounded
    omega
  rcases branch with rfl | rfl
  all_goals
    cbv at declared
    cases Option.some.inj declared
    refine ⟨?_,by cbv,by cbv,?_⟩
    · exact ⟨_,by cbv,by cbv,by cbv⟩
    · intro premise member
      change premise ∈ [] at member
      cases member

theorem graph_forward_profile :
    DirectedForwardProfile (fun schema => binderFree schema = true) graphEnvironment := by
  refine ⟨rfl,?_⟩
  intro index rule declared
  have zero : index = 0 := by
    have bounded := (List.getElem?_eq_some_iff.mp declared).1
    have length : graphEnvironment.language.rewrites.length = 1 := by cbv
    rw [length] at bounded
    omega
  subst index
  cbv at declared
  cases Option.some.inj declared
  refine ⟨?_,by cbv,by cbv,?_⟩
  · exact ⟨_,by cbv,by cbv,by cbv⟩
  · intro premise member
    change premise ∈ [] at member
    cases member

/-- The original source rule cores are retained by the actual annotation pass. -/
theorem petri_source_core : petriEnvironment.language.rewrites.map ruleCore =
    Mettapedia.GSLT.LanguageDef.CollectionConsumers.petri.rewrites.map ruleCore := by cbv

theorem graph_source_core : graphEnvironment.language.rewrites.map ruleCore =
    Mettapedia.GSLT.LanguageDef.CollectionConsumers.reachability.rewrites.map ruleCore := by cbv

theorem petri_uniform_checked :
    checkUniformDirectedProfile petriEnvironment [.base "Marking"] = true := by cbv

theorem graph_uniform_checked :
    checkUniformDirectedProfile graphEnvironment [.base "Graph"] = true := by cbv

theorem petri_uniform_profile : UniformDirectedProfile (fun schema => binderFree schema = true)
    petriEnvironment [.base "Marking"] := UniformDirectedProfile.of_check petri_uniform_checked

theorem graph_uniform_profile : UniformDirectedProfile (fun schema => binderFree schema = true)
    graphEnvironment [.base "Graph"] := UniformDirectedProfile.of_check graph_uniform_checked

/-- Every source witness at the authored Marking fibre is covered by one
checked table profile, without a witness-specific eligibility premise. -/
theorem petri_uniform_source_iff {bound : List TypeExpr} {source target : Pattern}
    (sourceTyped : OpenPatternWellSorted petriEnvironment.language petriEnvironment.free bound (.base "Marking") source) :
    (∃ index trace captured completed history,RootFiring petriEnvironment bound (.base "Marking")
      source index trace captured completed history target) ↔
      ReferenceStep.Step (providerRelEnv petriEnvironment.provider)
        Mettapedia.GSLT.LanguageDef.CollectionConsumers.petri source target :=
  (petri_uniform_profile.roots_iff_reference (providerRelEnv petriEnvironment.provider)
    (providerRelEnv_reads _) (by simp) sourceTyped).trans
      (reference_step_same_core_iff petri_source_core _)

/-- Set-valued graph roots use the same derived source eligibility. The
profile fixes Graph rather than inferring a carrier from an empty set. -/
theorem graph_uniform_source_iff {bound : List TypeExpr} {source target : Pattern}
    (sourceTyped : OpenPatternWellSorted graphEnvironment.language graphEnvironment.free bound (.base "Graph") source) :
    (∃ index trace captured completed history,RootFiring graphEnvironment bound (.base "Graph")
      source index trace captured completed history target) ↔
      ReferenceStep.Step (providerRelEnv graphEnvironment.provider)
        Mettapedia.GSLT.LanguageDef.CollectionConsumers.reachability source target :=
  (graph_uniform_profile.roots_iff_reference (providerRelEnv graphEnvironment.provider)
    (providerRelEnv_reads _) (by simp) sourceTyped).trans
      (reference_step_same_core_iff graph_source_core _)

theorem petri_auxiliary_sort_is_not_root_carrier :
    checkUniformDirectedProfile petriEnvironment [.base "Place"] = false := by cbv

#print axioms petri_uniform_checked
#print axioms graph_uniform_checked
#print axioms petri_uniform_profile
#print axioms graph_uniform_profile
#print axioms petri_uniform_source_iff
#print axioms graph_uniform_source_iff
#print axioms petri_auxiliary_sort_is_not_root_carrier

/-- Bare marking roots satisfy the forward source boundary without adding
an application wrapper or requiring a constructor-headed rule schema. -/
theorem petri_source_sound {bound : List TypeExpr} {expected : TypeExpr} {source target : Pattern}
    {index : Nat} {trace : List GeneralScopedMatchMachine.BagChoice}
    {captured completed : Assignment} {history : List Event}
    (fired : RootFiring petriEnvironment bound expected source index trace captured completed history target) :
    ReferenceStep.Step (providerRelEnv petriEnvironment.provider)
      Mettapedia.GSLT.LanguageDef.CollectionConsumers.petri source target := by
  have step := directed_step_toReference_of_forward petri_forward_profile _ (providerRelEnv_reads _)
    ⟨index,trace,captured,completed,history,fired⟩
  exact (reference_step_same_core_iff petri_source_core _).mp step

/-- This is literal source soundness for the actual graph rule. Equational
set-retention branches still require their separate internal-policy bridge. -/
theorem graph_source_sound {bound : List TypeExpr} {expected : TypeExpr} {source target : Pattern}
    {index : Nat} {trace : List GeneralScopedMatchMachine.BagChoice}
    {captured completed : Assignment} {history : List Event}
    (fired : RootFiring graphEnvironment bound expected source index trace captured completed history target) :
    ReferenceStep.Step (providerRelEnv graphEnvironment.provider)
      Mettapedia.GSLT.LanguageDef.CollectionConsumers.reachability source target := by
  have step := directed_step_toReference_of_forward graph_forward_profile _ (providerRelEnv_reads _)
    ⟨index,trace,captured,completed,history,fired⟩
  exact (reference_step_same_core_iff graph_source_core _).mp step



theorem produced_petri_forward_profile :
    DirectedForwardProfile (fun schema => binderFree schema = true)
      Mettapedia.GSLT.LanguageDef.CollectionConsumers.Controls.ProducedCoverage.environment := by
  refine ⟨rfl,?_⟩
  intro index rule declared
  have branch : index = 0 ∨ index = 1 := by
    have bounded := (List.getElem?_eq_some_iff.mp declared).1
    have length : Mettapedia.GSLT.LanguageDef.CollectionConsumers.Controls.ProducedCoverage.environment.language.rewrites.length = 2 := by cbv
    rw [length] at bounded
    omega
  rcases branch with rfl | rfl
  all_goals
    cbv at declared
    cases Option.some.inj declared
    refine ⟨?_,by cbv,by cbv,?_⟩
    · exact ⟨_,by cbv,by cbv,by cbv⟩
    · intro premise member
      change premise ∈ ([Premise.relationQuery "produce" [.fvar "made"]] : List Premise) at member
      cases List.mem_singleton.mp member
      refine .query (by decide) ?_
      intro argument member
      cases List.mem_singleton.mp member
      rfl

/-- The existing guarded Petri consumer supplies an actual retained firing.
Its original match account is read through the primitive source boundary. -/
theorem actual_guarded_petri_reference :
    ReferenceStep.Step
      (providerRelEnv Mettapedia.GSLT.LanguageDef.CollectionConsumers.Controls.ProducedCoverage.environment.provider)
      Mettapedia.GSLT.LanguageDef.CollectionConsumers.Controls.ProducedCoverage.environment.language
      (CollectionMatcherCompatibility.ordinaryTarget
        Mettapedia.GSLT.LanguageDef.CollectionConsumers.Controls.ProducedCoverage.request
        Mettapedia.GSLT.LanguageDef.CollectionConsumers.Controls.ProducedCoverage.receipt)
      (marking [token "C"]) := by
  obtain ⟨trace,fired⟩ := Mettapedia.GSLT.LanguageDef.CollectionConsumers.Controls.ProducedCoverage.source_firing
  exact directed_step_toReference_of_forward produced_petri_forward_profile _ (providerRelEnv_reads _)
    ⟨_,trace,_,_,_,fired⟩

def graphCaptured : Assignment :=
  Mettapedia.GSLT.LanguageDef.CollectionConsumers.Controls.graphFirstFiring.receipt.source.matching.assignment

def graphContext : Context :=
  ⟨Mettapedia.GSLT.LanguageDef.CollectionConsumers.Controls.graphFirstFiring.ordinal,
    Mettapedia.GSLT.LanguageDef.CollectionConsumers.Controls.graphFirstFiring.request.rule,
    Mettapedia.GSLT.LanguageDef.CollectionConsumers.Controls.graphFirstFiring.request.spec,[],0,0⟩

def graphConclusion : Pattern := graph [edge "A" "B",edge "B" "C",edge "A" "C"]

theorem graph_captures_typed : TypedAssignment graphEnvironment graphContext graphCaptured := by
  apply checkTypedAssignment_sound
  cbv


private theorem unconditional_collection_root
    {plan : GeneralExecutionAdmission.Plan} {certificate : CollectionExecutionAdmission.Certificate plan}
    {source : Pattern} {firing : CollectionPlanMachine.Firing} {expected : TypeExpr}
    (authority : CollectionMatcherBackend.HandoffAuthority plan certificate source firing)
    (sourceTyped : OpenPatternWellSorted (GeneralPlanEnvironment.environment plan).language
      (GeneralPlanEnvironment.environment plan).free [] expected source)
    (capturedTyped : TypedAssignment (GeneralPlanEnvironment.environment plan)
      ⟨firing.ordinal,firing.request.rule,firing.request.spec,[],0,0⟩
      firing.receipt.source.matching.assignment)
    (empty : firing.request.rule.premises = [])
    (ordinary : ScopedReflectiveExecution.binderOperation
      (GeneralPlanEnvironment.environment plan).reflection firing.request.rule = Substitution.instantiateBVar)
    (targetTyped : OpenPatternWellSorted (GeneralPlanEnvironment.environment plan).language
      (GeneralPlanEnvironment.environment plan).free [] expected firing.receipt.target) :
    ∃ trace,RootFiring (GeneralPlanEnvironment.environment plan) [] expected
      (CollectionMatcherCompatibility.ordinaryTarget firing.request firing.receipt.source) firing.ordinal trace
      firing.receipt.source.matching.assignment firing.receipt.source.matching.assignment [] firing.receipt.target := by
  obtain ⟨answer,_,same⟩ := CollectionMatcherCompatibility.ordinaryAnswers_complete
    authority.ready.index authority.unordered authority.valid.1
  have matching := (CollectionMatcherBackend.ordinaryRootAnswer firing.request firing.receipt.source
    authority.ready answer).property
  change GeneralScopedMatchMachine.TracedMatches firing.request.rule firing.request.spec 0 .left [] 0 []
    firing.request.rule.left (CollectionMatcherCompatibility.ordinaryTarget firing.request firing.receipt.source)
    answer.val.trace answer.val.assignment at matching
  rw [same] at matching
  refine ⟨answer.val.trace,.fire authority.declared authority.specified authority.admitted
    (authority.source_typed sourceTyped) matching capturedTyped ?_ ?_ targetTyped⟩
  · rw [empty]
    exact .nil
  · rw [ordinary]
    have reduced := authority.valid.2
    rw [authority.ready.ambient] at reduced
    exact reduced

theorem graph_rule_has_no_premises {index : Nat} {rule : RewriteRule}
    (declared : graphEnvironment.language.rewrites[index]? = some rule) : rule.premises = [] := by
  have shapes : graphEnvironment.language.rewrites.map RewriteRule.premises = [[]] := by cbv
  have member := List.mem_map_of_mem (f := RewriteRule.premises) (List.mem_of_getElem? declared)
  rw [shapes] at member
  exact List.mem_singleton.mp member

theorem graph_receipt_target :
    Mettapedia.GSLT.LanguageDef.CollectionConsumers.Controls.graphFirstFiring.receipt.target = graphConclusion := by cbv

theorem graph_root_from_actual_receipt : ∃ trace,
    RootFiring graphEnvironment [] (.base "Graph")
      (CollectionMatcherCompatibility.ordinaryTarget
        Mettapedia.GSLT.LanguageDef.CollectionConsumers.Controls.graphFirstFiring.request
        Mettapedia.GSLT.LanguageDef.CollectionConsumers.Controls.graphFirstFiring.receipt.source)
      Mettapedia.GSLT.LanguageDef.CollectionConsumers.Controls.graphFirstFiring.ordinal trace
      graphCaptured graphCaptured [] graphConclusion := by
  rw [← graph_receipt_target]
  apply unconditional_collection_root
    Mettapedia.GSLT.LanguageDef.CollectionConsumers.Controls.graphFirstAuthority
    Mettapedia.GSLT.LanguageDef.CollectionConsumers.Controls.graphSource_typed graph_captures_typed
  · exact graph_rule_has_no_premises
      Mettapedia.GSLT.LanguageDef.CollectionConsumers.Controls.graphFirstFiring_declared
  · have reflection : (GeneralPlanEnvironment.environment reachabilityPlan).reflection =
        Reflection.ReflectionProfile.empty := by cbv
    rw [reflection]
    rfl
  · rw [graph_receipt_target]
    apply checkOpenPatternWellSorted_sound
    cbv

/-- The graph source witness comes from the retained allocation's actual
ordinary match, preserving the distinction from equational set readouts. -/
theorem actual_graph_reference :
    ReferenceStep.Step (providerRelEnv graphEnvironment.provider)
      Mettapedia.GSLT.LanguageDef.CollectionConsumers.reachability
      (CollectionMatcherCompatibility.ordinaryTarget
        Mettapedia.GSLT.LanguageDef.CollectionConsumers.Controls.graphFirstFiring.request
        Mettapedia.GSLT.LanguageDef.CollectionConsumers.Controls.graphFirstFiring.receipt.source)
      graphConclusion := by
  obtain ⟨trace,fired⟩ := graph_root_from_actual_receipt
  exact graph_source_sound fired

#print axioms produced_petri_forward_profile
#print axioms actual_guarded_petri_reference
#print axioms graph_captures_typed
#print axioms unconditional_collection_root
#print axioms graph_rule_has_no_premises
#print axioms graph_receipt_target
#print axioms graph_root_from_actual_receipt
#print axioms actual_graph_reference

#print axioms petri_forward_profile
#print axioms graph_forward_profile
#print axioms petri_source_core
#print axioms graph_source_core
#print axioms petri_source_sound
#print axioms graph_source_sound

end Mettapedia.OSLF.MeTTaIL.GeneralPremise.SharedOutputControls.BareReferenceControls


namespace Mettapedia.OSLF.MeTTaIL.GeneralPremise.SharedOutputControls.RecursiveReverseControls

open _root_.Mettapedia.OSLF.MeTTaIL
open _root_.Mettapedia.OSLF.MeTTaIL.Syntax Match MatchSpec ScopedRuleMatching RuleBinding GeneralFirstOrderProjection
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.Framework.GeneralCanonicalAgreement QuantifiedReference
open RecursiveReadbackControls (term atom nestedRule nestedTarget nestedBindings)

set_option maxRecDepth 8000
set_option maxHeartbeats 1200000

def explicitSpec : RuleBindingSpec :=
  {GeneralRuleBindingInference.inferredSpec nestedRule with occurrences := [
    ⟨"x",.left,[0,0,0,0],[]⟩,⟨"inside",.left,[0,0,0,1],[]⟩,
    ⟨"x",.left,[0,1],[]⟩,⟨"outside",.left,[0,2],[]⟩,⟨"x",.right,[],[]⟩]}

theorem actual_spec_admitted : admittedFor nestedRule explicitSpec = true ∧
    checkZeroDependencies explicitSpec = true ∧ explicitSpec.occurrences.length = 5 ∧
    explicitSpec ≠ GeneralRuleBindingInference.inferredSpec nestedRule := by decide +kernel

theorem wrong_occurrence_path_refused :
    admittedFor nestedRule {explicitSpec with occurrences := [⟨"x",.left,[999],[]⟩]} = false := by cbv

/-- Capture typing comes from the actual raw witness and retained nested rest
roles. No captured typing table is assumed as a certificate. -/
theorem nested_capture_typing : CapturesTyped RecursiveReadbackControls.language FreeTypeContext.empty []
    nestedRule.typeContext nestedBindings := by
  exact matching_recursive_captures_typed (by cbv)
    (collectionChoiceDeterministic_of_check (by cbv)) RecursiveReadbackControls.nested_schema_binderFree
    (matchPattern_sound RecursiveReadbackControls.nested_raw_match)
    (binderFree_schema_restAware RecursiveReadbackControls.nested_schema_binderFree (domains := []) (by cbv))
    RecursiveReadbackControls.nested_target_typed

/-- The same raw nested match reconstructs the actual admitted scoped table,
with its explicit occurrence rows, typed bodies and exact residual kinds. -/
theorem nested_actual_spec_reverse : ∃ final,
    GeneralScopedMatch.Matches nestedRule explicitSpec 0 .left [] 0 [] nestedRule.left nestedTarget final ∧
      ConditionalEquationExecution.AssignmentTyped RecursiveReadbackControls.language FreeTypeContext.empty []
        nestedRule explicitSpec final ∧ ConditionalEquationExecution.AssignmentObjects final ∧
      ScopedCompatible 0 nestedBindings final := by
  have raw := matchPattern_sound RecursiveReadbackControls.nested_raw_match
  have unique := matchRel_unique_names raw
  have compatible : Compatible nestedBindings nestedBindings := fun _ member => bindings_lookup_of_mem unique member
  have dependencies : ∀ name ∈ nestedRule.left.freeFvarNames,dependencies? explicitSpec name = some [] := by
    intro name member
    obtain ⟨body,read⟩ := raw_matching_defined_recursive raw name member
    obtain ⟨expected,declared,_⟩ := nested_capture_typing (name,body) (raw_lookup_member read)
    exact dependencies_empty_of_admitted actual_spec_admitted.1 actual_spec_admitted.2.1 declared
  obtain ⟨final,matching,retained⟩ := binderFree_scoped_of_matchRel_admitted (initial := []) actual_spec_admitted.1
    RecursiveReadbackControls.nested_schema_binderFree (NameCoherent.left nestedRule) dependencies raw compatible
    RecursiveReadbackControls.nested_target_typed.2.2.2 RecursiveReadbackControls.nested_target_typed.2.2.1
    (by intro _ member; cases member)
  have typing := retained.typed_admitted nested_capture_typing actual_spec_admitted.1 actual_spec_admitted.2.1
  exact ⟨final,matching,typing.1,typing.2,retained⟩

/-- A structured input is checked literally by the ordinary declared mode;
raw reference matching may choose a different bag order. Both sides remain
well-typed closed object values. -/
def inputSchema : Pattern := .collection .hashBag [atom "A",atom "B"] none
def inputRow : Pattern := .collection .hashBag [atom "B",atom "A"] none

def inputRule : RewriteRule where
  name := "literal-collection-input"
  typeContext := []
  left := atom "A"
  right := atom "C"
  premises := [.relationQuery "bag-input" [inputSchema]]

def inputLanguage : LanguageDef := {RecursiveReadbackControls.language with
  name := "literal-structured-input-separator", rewrites := [inputRule]}

def inputProvider : ProviderSnapshot where
  signatures := [⟨"bag-input",[.collection .hashBag term],[.input]⟩]
  rows := [⟨"bag-input",[inputRow]⟩]

def inputEnvironment : Environment where
  language := inputLanguage
  free := FreeTypeContext.empty
  provider := inputProvider
  specifications := [(0,GeneralRuleBindingInference.inferredSpec inputRule)]

theorem input_source_and_provider_checked : inputLanguage.validate = [] ∧
    checkProviderClosed inputLanguage FreeTypeContext.empty inputProvider = true ∧
    rulePremisesAdmitted inputLanguage inputProvider inputRule
      (GeneralRuleBindingInference.inferredSpec inputRule) = true ∧
    Static.checkRule inputLanguage inputProvider inputRule
      (GeneralRuleBindingInference.inferredSpec inputRule) = true := by cbv

theorem input_values_typed : OpenPatternWellSorted inputLanguage FreeTypeContext.empty []
      (.collection .hashBag term) inputSchema ∧
    OpenPatternWellSorted inputLanguage FreeTypeContext.empty [] (.collection .hashBag term) inputRow := by
  constructor <;> apply checkOpenPatternWellSorted_sound <;> cbv

theorem reference_accepts_permuted_input : ReferenceStep.Step (providerRelEnv inputProvider)
    inputLanguage (atom "A") (atom "C") := by
  refine ⟨.rule 0 [] [.base []],?_⟩
  exact (ReferenceStep.checkStep_eq_some_iff _ _ _).mp (by decide +kernel)

theorem instantiate_input_exact (context : Context) (initial : Assignment) :
    instantiateAt? context.rule context.spec context.bound.length (context.site 0) [] 0
      initial inputSchema = some inputSchema := by
  simp only [inputSchema,atom,instantiateAt?,instantiateWith?,instantiateArgsWith?,
    Option.bind_eq_bind,Option.bind_some]

theorem ordinary_input_accepts_same_presentation (context : Context) (initial : Assignment) :
    ordinaryInterpretation.Input ⟨context.rule,context.spec,context.bound.length,
      context.site 0,[],0,initial,inputSchema,inputSchema⟩ := instantiate_input_exact context initial

theorem ordinary_input_refuses_permuted_presentation (context : Context) (initial : Assignment) :
    ¬ ordinaryInterpretation.Input ⟨context.rule,context.spec,context.bound.length,
      context.site 0,[],0,initial,inputSchema,inputRow⟩ := by
  change ¬ instantiateAt? context.rule context.spec context.bound.length (context.site 0) [] 0
    initial inputSchema = some inputRow
  rw [instantiate_input_exact]
  decide +kernel

theorem traced_input_refused (context : Context) (initial final : Assignment)
    (origins : List (Nat × List GeneralScopedMatchMachine.BagChoice)) :
    ¬ TracedArgumentsHold context 0 initial [inputSchema] [inputRow] [.input] final origins := by
  intro held
  cases held with
  | input read _ => exact ordinary_input_refuses_permuted_presentation context initial read

theorem literal_query_refused (context : Context) (initial final : Assignment)
    (rowIndex : Nat) (origins : List (Nat × List GeneralScopedMatchMachine.BagChoice)) :
    ¬ TracedQuery inputEnvironment context "bag-input" [inputSchema] initial rowIndex final origins := by
  intro queried
  cases queried with
  | @row index row actualSignature result actualOrigins rowFound signatureFound sorted arguments finalTyped =>
    have member := List.mem_of_getElem? rowFound
    have same : row = ⟨"bag-input",[inputRow]⟩ := by simpa only [inputEnvironment,inputProvider,List.mem_singleton] using member
    subst row
    have signature : signature? inputEnvironment.provider "bag-input" 1 =
        some ⟨"bag-input",[.collection .hashBag term],[.input]⟩ := by cbv
    have sameSignature := Option.some.inj (signatureFound.symm.trans signature)
    cases sameSignature
    exact traced_input_refused context initial final origins arguments
  | dynamicRow registered _ _ _ _ _ _ _ =>
    change "bag-input" ∈ ([] : List String) at registered
    cases registered

/-- The complete literal typed root semantics rejects the guard although the
original raw reference relation fires. Syntax and static admission alone do
not establish reverse coverage for structured input bags. -/
theorem typed_root_refuses_permuted_input {trace : List GeneralScopedMatchMachine.BagChoice}
    {captured completed : Assignment} {history : List Event} {target : Pattern} :
    ¬ RootFiring inputEnvironment [] term (atom "A") 0 trace captured completed history target := by
  intro fired
  cases fired with
  | @fire _ _ _ _ _ actualRule actualSpec _ _ _ _ declared specified _ _ matching capturedTyped premises _ _ =>
    have sameRule : actualRule = inputRule := Option.some.inj (declared.symm.trans rfl)
    subst actualRule
    cases premises with
    | cons first _ =>
      cases first with
      | query queried => exact literal_query_refused _ _ _ _ _ queried

#print axioms actual_spec_admitted
#print axioms wrong_occurrence_path_refused
#print axioms nested_capture_typing
#print axioms nested_actual_spec_reverse
#print axioms input_source_and_provider_checked
#print axioms input_values_typed
#print axioms reference_accepts_permuted_input
#print axioms instantiate_input_exact
#print axioms ordinary_input_accepts_same_presentation
#print axioms ordinary_input_refuses_permuted_presentation
#print axioms traced_input_refused
#print axioms literal_query_refused
#print axioms typed_root_refuses_permuted_input

end Mettapedia.OSLF.MeTTaIL.GeneralPremise.SharedOutputControls.RecursiveReverseControls


namespace Mettapedia.OSLF.MeTTaIL.GeneralPremise.SharedOutputControls.RecursiveQueryReverseControls

open _root_.Mettapedia.OSLF.MeTTaIL
open _root_.Mettapedia.OSLF.MeTTaIL.Syntax Match MatchSpec ScopedRuleMatching RuleBinding GeneralFirstOrderProjection
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.Framework.GeneralCanonicalAgreement QuantifiedReference
open RecursiveReadbackControls (term atom nestedRule nestedTarget nestedBindings)

set_option maxRecDepth 8000
set_option maxHeartbeats 1200000

def whole : Pattern := .collection .hashBag [atom "A",atom "B"] none

def authoredRule : RewriteRule where
  name := "collection-input-and-nested-output"
  typeContext := nestedRule.typeContext ++ [("whole",.collection .hashBag term)]
  left := .apply "Box" [.collection .hashBag [] (some "whole")]
  right := .fvar "x"
  premises := [.relationQuery "mixed-nested" [.fvar "whole",nestedRule.left]]

def spec : RuleBindingSpec := {GeneralRuleBindingInference.inferredSpec authoredRule with occurrences := [
  ⟨"whole",.left,[0,0],[]⟩,⟨"whole",.premise 0 0 0,[],[]⟩,
  ⟨"x",.premise 0 0 1,[0,0,0,0],[]⟩,⟨"inside",.premise 0 0 1,[0,0,0,1],[]⟩,
  ⟨"x",.premise 0 0 1,[0,1],[]⟩,⟨"outside",.premise 0 0 1,[0,2],[]⟩,⟨"x",.right,[],[]⟩]}

def language : LanguageDef := {RecursiveReadbackControls.language with
  name := "actual-mixed-collection-source-query", rewrites := [authoredRule]}

def signature : Signature := ⟨"mixed-nested",[.collection .hashBag term,term],[.input,.output]⟩

def provider : ProviderSnapshot where
  signatures := [signature]
  rows := [⟨"mixed-nested",[whole,nestedTarget]⟩]

def environment : Environment where
  language := language
  free := FreeTypeContext.empty
  provider := provider
  specifications := [(0,spec)]

def context : Context := ⟨0,authoredRule,spec,[],0,0⟩
def initial : Assignment := [("whole",rootValue 0 whole)]
def rawInitial : Bindings := [("whole",whole)]
def result : Bindings := nestedBindings ++ rawInitial

def source : Pattern := .apply "Box" [whole]

theorem actual_environment_checked : language.validate = [] ∧ admittedFor authoredRule spec = true ∧
    checkZeroDependencies spec = true ∧ checkProviderClosed language FreeTypeContext.empty provider = true ∧
    (premiseFlow language provider authoredRule spec ["whole"]
      (.relationQuery "mixed-nested" [.fvar "whole",nestedRule.left])).supported = true ∧
    Static.checkRule language provider authoredRule spec = true := by cbv

theorem actual_initial_match : GeneralScopedMatch.Matches authoredRule spec 0 .left [] 0 [] authoredRule.left source initial :=
  GeneralScopedMatch.matchAt_iff.mp (by decide +kernel)

theorem actual_initial_typed : TypedAssignment environment context initial :=
  checkTypedAssignment_sound (by cbv)

theorem actual_initial_canonical : CanonicalValues initial := by
  intro name value found
  simp only [initial,lookup,List.find?_cons,List.find?_nil] at found
  split at found
  · cases Option.some.inj found
    cbv
  · cases found

theorem initial_binding_agreement : BindingAgreement ["whole"] initial rawInitial := by
  refine ⟨by decide,by decide,?_,?_,?_⟩
  · intro name
    simp only [initial,List.map_cons,List.map_nil,List.mem_singleton]
  · intro name
    simp only [rawInitial,List.map_cons,List.map_nil,List.mem_singleton]
  · intro name
    simp only [initial,rawInitial,lookup,Bindings.lookup,List.find?_cons,List.find?_nil]
    split <;> rfl

theorem original_mixed_query : result ∈ Engine.premiseStepWithEnv (providerRelEnv provider) language rawInitial
    (.relationQuery "mixed-nested" [.fvar "whole",nestedRule.left]) := by decide +kernel

theorem original_conditional_source : ReferenceStep.Step (providerRelEnv provider) language source (atom "A") := by
  refine ⟨.rule 0 rawInitial [.base result],?_⟩
  exact (ReferenceStep.checkStep_eq_some_iff _ _ _).mp (by decide +kernel)

/-- A collection-valued input and recursively nested output reconstruct the
actual typed source continuation from the original query evidence. Explicit
occurrence rows, root captures and both declared modes are retained. -/
theorem reconstructed_actual_query : ∃ final rowIndex origins,
    TracedQuery environment context "mixed-nested" [.fvar "whole",nestedRule.left] initial rowIndex final origins ∧
      BindingAgreement
        (premiseFlow language provider authoredRule spec ["whole"]
          (.relationQuery "mixed-nested" [.fvar "whole",nestedRule.left])).available final result := by
  apply query_fromReference_bindings_recursive (providerRelEnv provider) (providerRelEnv_reads provider)
    actual_environment_checked.1 (collectionChoiceDeterministic_of_check (by cbv))
    actual_environment_checked.2.2.2.1 actual_environment_checked.2.1 actual_environment_checked.2.2.1
    (by decide) (refinement := Static.initialRefinement authoredRule)
  · intro position schema selected
    cases position with
    | zero =>
      cases Option.some.inj selected
      cbv
    | succ position =>
      cases position with
      | zero => cases Option.some.inj selected; cbv
      | succ position => simp at selected
  · cbv
  · intro selectedSignature found position schema selected input
    have unique : signature? environment.provider "mixed-nested" 2 = some signature := by cbv
    have same := Option.some.inj (found.symm.trans unique)
    subst selectedSignature
    cases position with
    | zero =>
      cases Option.some.inj selected
      exact .metavariable "whole"
    | succ position =>
      cases position <;> simp [signature] at input
  · exact actual_initial_typed
  · exact actual_initial_canonical
  · exact initial_binding_agreement
  · exact actual_environment_checked.2.2.2.2.1
  · cbv
  · exact original_mixed_query

#print axioms actual_environment_checked
#print axioms actual_initial_match
#print axioms actual_initial_typed
#print axioms actual_initial_canonical
#print axioms initial_binding_agreement
#print axioms original_mixed_query
#print axioms original_conditional_source
#print axioms reconstructed_actual_query

end Mettapedia.OSLF.MeTTaIL.GeneralPremise.SharedOutputControls.RecursiveQueryReverseControls


namespace Mettapedia.OSLF.MeTTaIL.GeneralPremise.SharedOutputControls.InstantiationTotalControls

open _root_.Mettapedia.OSLF.MeTTaIL
open _root_.Mettapedia.OSLF.MeTTaIL.Syntax Match ScopedRuleMatching RuleBinding GeneralFirstOrderProjection
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.Framework.GeneralCanonicalAgreement QuantifiedReference
open RecursiveReadbackControls (term atom nestedRule)

set_option maxRecDepth 8000
set_option maxHeartbeats 1200000

/-- Concrete rest evidence is earned by the actual output matcher and retained
through the existing query continuation. The same stored values then justify
nested instantiation, typing, canonical metadata and caller scope together. -/
theorem actual_query_then_total_instantiation : ∃ final rowIndex origins target,
    TracedQuery RecursiveQueryReverseControls.environment RecursiveQueryReverseControls.context "mixed-nested"
      [.fvar "whole",nestedRule.left] RecursiveQueryReverseControls.initial rowIndex final origins ∧
    instantiateAt? RecursiveQueryReverseControls.authoredRule RecursiveQueryReverseControls.spec 0
      (.premise 0 0 1) [] 0 final nestedRule.left = some target ∧
    OpenPatternWellSorted RecursiveQueryReverseControls.language FreeTypeContext.empty [] term target := by
  obtain ⟨final,rowIndex,origins,queried,_⟩ := RecursiveQueryReverseControls.reconstructed_actual_query
  have held : PremiseHolds RecursiveQueryReverseControls.environment RecursiveQueryReverseControls.context
      (.relationQuery "mixed-nested" [.fvar "whole",nestedRule.left]) RecursiveQueryReverseControls.initial final
      (.query 0 0 rowIndex origins) := .query queried
  have initialFacts : Static.InputFacts RecursiveQueryReverseControls.environment RecursiveQueryReverseControls.context
      (Static.initialRefinement RecursiveQueryReverseControls.authoredRule) RecursiveQueryReverseControls.initial :=
    ⟨RecursiveQueryReverseControls.actual_initial_typed,RecursiveQueryReverseControls.actual_initial_canonical,
      Static.initialRefinement_holds RecursiveQueryReverseControls.actual_initial_match⟩
  have after := initialFacts.afterPremise held
  have signatureFound : signature? RecursiveQueryReverseControls.provider "mixed-nested" 2 =
      some RecursiveQueryReverseControls.signature := by cbv
  have names : ∀ name ∈ nestedRule.left.freeFvarNames,name ∈
      (Static.premiseFlow RecursiveQueryReverseControls.language RecursiveQueryReverseControls.provider
        RecursiveQueryReverseControls.authoredRule RecursiveQueryReverseControls.spec 0 0
        (Static.initialRefinement RecursiveQueryReverseControls.authoredRule)
        (.relationQuery "mixed-nested" [.fvar "whole",nestedRule.left])).refinement.available := by
    intro name member
    simp only [Static.premiseFlow, List.length_cons, List.length_nil, signatureFound,
      RecursiveQueryReverseControls.signature, queryOutputNames, List.zip_cons_cons,
      List.zip_nil_left, List.flatMap_cons, List.flatMap_nil, List.nil_append, List.append_nil]
    exact List.mem_append_left _ member
  have rests : ∀ name ∈ restCaptureNames nestedRule.left,name ∈
      (Static.premiseFlow RecursiveQueryReverseControls.language RecursiveQueryReverseControls.provider
        RecursiveQueryReverseControls.authoredRule RecursiveQueryReverseControls.spec 0 0
        (Static.initialRefinement RecursiveQueryReverseControls.authoredRule)
        (.relationQuery "mixed-nested" [.fvar "whole",nestedRule.left])).refinement.finite := by
    intro name member
    simp only [Static.premiseFlow, List.length_cons, List.length_nil, signatureFound,
      RecursiveQueryReverseControls.signature, Static.outputRestNames, List.nil_append, List.append_nil]
    exact List.mem_append_left _ (List.mem_append_left _ member)
  obtain ⟨target,read,sorted⟩ := binderFree_instantiation_total_open
    (operation := Substitution.instantiateBVar) (site := .premise 0 0 1) (path := []) (expected := term)
    RecursiveQueryReverseControls.actual_environment_checked.2.1
    RecursiveQueryReverseControls.actual_environment_checked.2.2.1 after.typed after.canonical
    RecursiveReadbackControls.nested_schema_binderFree
    (nameCoherent_at (by cbv))
    (binderFree_schema_restAware RecursiveReadbackControls.nested_schema_binderFree (domains := []) (by cbv))
    (fun name member => after.represented.1 name (names name member))
    (fun name member => after.represented.2.1 name (rests name member))
  exact ⟨final,rowIndex,origins,target,queried,read,sorted⟩

def abstractRule : RewriteRule where
  name := "a-collection-type-is-not-a-concrete-rest"
  typeContext := [("rest",.collection .hashBag term)]
  left := .collection .hashBag [] (some "rest")
  right := .collection .hashBag [] (some "rest")
  premises := []

def abstractSpec : RuleBindingSpec := GeneralRuleBindingInference.inferredSpec abstractRule

def abstractLanguage : LanguageDef := {RecursiveReadbackControls.language with rewrites := [abstractRule]}

def abstractFree : FreeTypeContext := fun name =>
  if name = "abstract-bag" then some (.collection .hashBag term) else none

def abstractEnvironment : Environment where
  language := abstractLanguage
  free := abstractFree
  provider := ⟨[],[],[]⟩
  specifications := [(0,abstractSpec)]

def abstractContext : Context := ⟨0,abstractRule,abstractSpec,[],0,0⟩

def abstractAssignment : Assignment := [("rest",rootValue 0 (.fvar "abstract-bag"))]

theorem abstract_spec_and_roles : admittedFor abstractRule abstractSpec = true ∧
    checkZeroDependencies abstractSpec = true ∧
    binderFree abstractRule.right = true ∧
    SchemaTyping.checkSchemaType [] abstractLanguage (FreeTypeContext.ofList abstractRule.typeContext) []
      abstractRule.right (.collection .hashBag term) = true := by cbv

theorem abstract_capture_typed : TypedAssignment abstractEnvironment abstractContext abstractAssignment :=
  checkTypedAssignment_sound (by cbv)

theorem abstract_body_open : OpenPatternWellSorted abstractLanguage abstractFree []
    (.collection .hashBag term) (.fvar "abstract-bag") := checkOpenPatternWellSorted_sound (by cbv)

theorem abstract_capture_bound : BoundNames abstractAssignment abstractRule.right.freeFvarNames := by
  intro name member
  have same : name = "rest" := by simpa only [abstractRule,Pattern.freeFvarNames,List.flatMap_nil,List.nil_append,
    Option.toList_some,List.mem_singleton] using member
  subst name
  exact ⟨rootValue 0 (.fvar "abstract-bag"),rfl⟩

theorem abstract_capture_roots : RootValues 0 abstractAssignment :=
  abstract_capture_typed.rootValues abstract_spec_and_roles.2.1

theorem abstract_capture_canonical : CanonicalValues abstractAssignment := by
  intro name value found
  simp only [abstractAssignment,lookup,List.find?_cons,List.find?_nil] at found
  split at found
  · cases Option.some.inj found
    rfl
  · cases found

/-- A typed, scoped object value at a collection type need not be a concrete
collection. That distinction is exactly the retained finite-rest obligation. -/
theorem abstract_rest_not_finite : ¬ FiniteCaptureNames abstractAssignment (restCaptureNames abstractRule.right) := by
  intro finite
  obtain ⟨value,kind,elements,found,concrete⟩ := finite "rest" (by simp only [abstractRule, restCaptureNames,
    List.flatMap_nil, List.nil_append, Option.toList_some, List.mem_singleton])
  have same : value = rootValue 0 (.fvar "abstract-bag") := Option.some.inj (found.symm.trans rfl)
  subst value
  cases concrete

theorem abstract_rest_instantiation_refused :
    instantiateAt? abstractRule abstractSpec 0 .right [] 0 abstractAssignment abstractRule.right = none := by cbv

#print axioms actual_query_then_total_instantiation
#print axioms abstract_spec_and_roles
#print axioms abstract_capture_typed
#print axioms abstract_body_open
#print axioms abstract_capture_bound
#print axioms abstract_capture_roots
#print axioms abstract_capture_canonical
#print axioms abstract_rest_not_finite
#print axioms abstract_rest_instantiation_refused

end Mettapedia.OSLF.MeTTaIL.GeneralPremise.SharedOutputControls.InstantiationTotalControls


namespace Mettapedia.OSLF.MeTTaIL.GeneralPremise.SharedOutputControls.RecursiveValidationReverseControls

open _root_.Mettapedia.OSLF.MeTTaIL
open _root_.Mettapedia.OSLF.MeTTaIL.Syntax Match MatchSpec ScopedRuleMatching RuleBinding GeneralFirstOrderProjection
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.Framework.GeneralCanonicalAgreement QuantifiedReference
open RecursiveReadbackControls (term atom nestedRule nestedTarget nestedBindings)

set_option maxRecDepth 8000
set_option maxHeartbeats 1200000

def body : Premise := .relationQuery "nested-per-member" [.fvar "item",nestedRule.left]
def quantified : Premise := .forAll "whole" "item" body

def authoredRule : RewriteRule := {RecursiveQueryReverseControls.authoredRule with
  name := "nested-output-in-each-finite-member"
  typeContext := RecursiveQueryReverseControls.authoredRule.typeContext ++ [("item",term)]
  right := atom "A"
  premises := [quantified]}

def spec : RuleBindingSpec := {GeneralRuleBindingInference.inferredSpec authoredRule with occurrences := [
  ⟨"whole",.left,[0,0],[]⟩,⟨"item",.premise 0 1 0,[],[]⟩,
  ⟨"x",.premise 0 1 1,[0,0,0,0],[]⟩,⟨"inside",.premise 0 1 1,[0,0,0,1],[]⟩,
  ⟨"x",.premise 0 1 1,[0,1],[]⟩,⟨"outside",.premise 0 1 1,[0,2],[]⟩]}

def language : LanguageDef := {RecursiveReadbackControls.language with
  name := "quantified-recursive-original-query", rewrites := [authoredRule]}

def signature : Signature := ⟨"nested-per-member",[term,term],[.input,.output]⟩

def provider : ProviderSnapshot where
  signatures := [signature]
  rows := [⟨"nested-per-member",[atom "A",nestedTarget]⟩,
    ⟨"nested-per-member",[atom "B",nestedTarget]⟩]

def environment : Environment where
  language := language
  free := FreeTypeContext.empty
  provider := provider
  specifications := [(0,spec)]

def context : Context := ⟨0,authoredRule,spec,[],0,0⟩
def initial : Assignment := RecursiveQueryReverseControls.initial
def rawInitial : Bindings := RecursiveQueryReverseControls.rawInitial
def source : Pattern := RecursiveQueryReverseControls.source

def bodyResult (element : Pattern) : Bindings :=
  nestedBindings ++ ReferenceStep.bindParameter rawInitial "item" element

def witness : ReferenceStep.Witness :=
  .forAll [.base (bodyResult (atom "A")),.base (bodyResult (atom "B"))]

theorem actual_environment_checked : language.validate = [] ∧ admittedFor authoredRule spec = true ∧
    checkZeroDependencies spec = true ∧ checkProviderClosed language FreeTypeContext.empty provider = true ∧
    (premiseFlow language provider authoredRule spec ["whole"] quantified).supported = true ∧
    Static.checkRule language provider authoredRule spec = true := by cbv

theorem actual_initial_match : GeneralScopedMatch.Matches authoredRule spec 0 .left [] 0 [] authoredRule.left source initial :=
  GeneralScopedMatch.matchAt_iff.mp (by decide +kernel)

theorem actual_initial_typed : TypedAssignment environment context initial :=
  checkTypedAssignment_sound (by cbv)

theorem actual_initial_canonical : CanonicalValues initial := RecursiveQueryReverseControls.actual_initial_canonical

theorem initial_binding_agreement : BindingAgreement ["whole"] initial rawInitial :=
  RecursiveQueryReverseControls.initial_binding_agreement

theorem recursive_validation : ValidationWith (fun schema => binderFree schema = true) quantified := by
  apply ValidationWith.quantified
  apply ValidationWith.query (by decide)
  intro schema member
  rcases List.mem_cons.mp member with rfl | member
  · rfl
  · cases List.mem_singleton.mp member
    exact RecursiveReadbackControls.nested_schema_binderFree

theorem literal_input_eligibility : FirstOrderQueryInputs provider quantified := by
  intro selectedSignature found position schema selected input
  have unique : signature? provider "nested-per-member" 2 = some signature := by cbv
  have same := Option.some.inj (found.symm.trans unique)
  subst selectedSignature
  cases position with
  | zero =>
    cases Option.some.inj selected
    exact .metavariable "item"
  | succ position =>
    cases position <;> simp [signature] at input

theorem original_body_A : bodyResult (atom "A") ∈ Engine.premiseStepWithEnv (providerRelEnv provider) language
    (ReferenceStep.bindParameter rawInitial "item" (atom "A")) body := by decide +kernel

theorem original_body_B : bodyResult (atom "B") ∈ Engine.premiseStepWithEnv (providerRelEnv provider) language
    (ReferenceStep.bindParameter rawInitial "item" (atom "B")) body := by decide +kernel

theorem original_quantified : ReferenceStep.PremiseValid (providerRelEnv provider) language
    (ReferenceStep.captureSites authoredRule) rawInitial quantified witness rawInitial := by
  exact .forAll (kind := .hashBag) (elements := [atom "A",atom "B"]) rfl
    (.cons (.base rfl original_body_A) (.cons (.base rfl original_body_B) .nil))

/-- The independent original witness reconstructs the actual typed local
queries. Each member has its own retained event; local outputs do not escape. -/
theorem reconstructed_quantified : ∃ final event,
    PremiseHolds environment context quantified initial final event ∧
    BindingAgreement ["whole"] final rawInitial := by
  have facts : Static.InputFacts environment context (Static.initialRefinement authoredRule) initial :=
    ⟨actual_initial_typed,actual_initial_canonical,Static.initialRefinement_holds actual_initial_match⟩
  obtain ⟨final,event,held,agreement⟩ := validation_fromReference_bindings_recursive (fun _ shape => shape)
    (providerRelEnv provider) (providerRelEnv_reads provider) actual_environment_checked.1
    (collectionChoiceDeterministic_of_check (by cbv)) actual_environment_checked.2.2.2.1
    recursive_validation (ReferenceStep.captureSites authoredRule) actual_environment_checked.2.1
    actual_environment_checked.2.2.1 literal_input_eligibility (by decide +kernel) facts initial_binding_agreement
    (by cbv) actual_environment_checked.2.2.2.2.1 (by cbv) original_quantified
  exact ⟨final,event,held,agreement⟩

/-- The failed local query is an actual original-evaluator negative. A finite
quantifier cannot manufacture the missing provider row for its second member. -/
def missingProvider : ProviderSnapshot := {provider with rows := [⟨"nested-per-member",[atom "A",nestedTarget]⟩]}

theorem missing_B_query_refused : Engine.premiseStepWithEnv (providerRelEnv missingProvider) language
    (ReferenceStep.bindParameter rawInitial "item" (atom "B")) body = [] := by decide +kernel


/-- Every original finite member retains its actual query history, while the
outer store remains unchanged rather than exporting local output captures. -/
theorem reconstructed_history_keeps_local_outputs : ∃ finalA finalB rowA rowB originsA originsB,
    PremiseHolds environment context quantified initial initial
      (.quantified 0 0 .hashBag [(0,atom "A",[.query 0 1 rowA originsA]),
        (1,atom "B",[.query 0 1 rowB originsB])]) ∧
    TracedQuery environment context.quantified "nested-per-member" [.fvar "item",nestedRule.left]
      (bindParameter "item" (localValue [] (atom "A")) initial) rowA finalA originsA ∧
    TracedQuery environment context.quantified "nested-per-member" [.fvar "item",nestedRule.left]
      (bindParameter "item" (localValue [] (atom "B")) initial) rowB finalB originsB ∧
    lookup initial "x" = none := by
  obtain ⟨final,event,held,_⟩ := reconstructed_quantified
  change PremiseHolds environment context (.forAll "whole" "item" body) initial final event at held
  cases held with
  | quantified read validated =>
    have known : finiteCollection? context.bound.length initial "whole" =
        some (.hashBag,[atom "A",atom "B"]) := by cbv
    have same := Option.some.inj (read.symm.trans known)
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj same
    cases validated with
    | cons typedA bodyA tail =>
      cases tail with
      | cons typedB bodyB tail =>
        cases tail
        cases bodyA with
        | query queryA =>
          cases bodyB with
          | query queryB =>
            refine ⟨_,_,_,_,_,_,?_,queryA,queryB,?_⟩
            · exact .quantified known (.cons typedA (.query queryA) (.cons typedB (.query queryB) .nil))
            · rfl

theorem old_firstOrder_validation_refused : ¬ Validation quantified := by
  intro shape
  cases shape with
  | quantified nested =>
    cases nested with
    | query _ schemas =>
      have outer := schemas nestedRule.left (by simp)
      cases outer with
      | constructor _ _ children =>
        have impossible := children _ (List.mem_singleton_self _)
        cases impossible

#print axioms reconstructed_history_keeps_local_outputs
#print axioms old_firstOrder_validation_refused


/-- No reference witness can validate the finite carrier after its required
second provider row has been removed. -/
theorem missing_quantified_refused (evidence : ReferenceStep.Witness) :
    ¬ ReferenceStep.PremiseValid (providerRelEnv missingProvider) language
      (ReferenceStep.captureSites authoredRule) rawInitial quantified evidence rawInitial := by
  intro held
  cases held with
  | base isBase _ => simp [quantified,ReferenceStep.isBase] at isBase
  | step endpoints _ _ _ => simp [quantified,ReferenceStep.stepEndpoints] at endpoints
  | forAll selected bodies =>
    have known : rawInitial.lookup "whole" = some (.collection .hashBag [atom "A",atom "B"] none) := rfl
    have same := Option.some.inj (selected.symm.trans known)
    cases same
    cases bodies with
    | cons _ tail =>
      cases tail with
      | cons second _ =>
        cases second with
        | base _ member =>
          rw [missing_B_query_refused] at member
          cases member
        | step endpoints _ _ _ => simp [body,ReferenceStep.stepEndpoints] at endpoints

#print axioms missing_quantified_refused


/-- The original list witness yields the existing retained chronological list,
not an unordered collection of independently checked endpoint claims. -/
theorem reconstructed_ordered_premises : ∃ final history,
    PremisesHold environment context authoredRule.premises initial final history ∧
    BindingAgreement ["whole"] final rawInitial := by
  have facts : Static.InputFacts environment context (Static.initialRefinement authoredRule) initial :=
    ⟨actual_initial_typed,actual_initial_canonical,Static.initialRefinement_holds actual_initial_match⟩
  have original : ReferenceStep.PremisesValid (providerRelEnv provider) language
      (ReferenceStep.captureSites authoredRule) rawInitial authoredRule.premises [witness] rawInitial :=
    .cons original_quantified (.nil rawInitial)
  apply premises_fromReference_bindings_recursive (fun _ shape => shape) (providerRelEnv provider)
    (providerRelEnv_reads provider) actual_environment_checked.1
    (collectionChoiceDeterministic_of_check (by cbv)) actual_environment_checked.2.2.2.1
    (ReferenceStep.captureSites authoredRule)
  · intro premise member
    have same : premise = quantified := by simpa only [authoredRule,List.mem_singleton] using member
    exact same.symm ▸ recursive_validation
  · intro offset premise selected
    simpa only [context,Nat.zero_add] using selected
  · rfl
  · exact actual_environment_checked.2.1
  · exact actual_environment_checked.2.2.1
  · intro premise member
    have same : premise = quantified := by simpa only [authoredRule,List.mem_singleton] using member
    exact same.symm ▸ literal_input_eligibility
  · decide +kernel
  · exact facts
  · exact initial_binding_agreement
  · cbv
  · cbv
  · exact original

#print axioms reconstructed_ordered_premises

#print axioms actual_environment_checked
#print axioms actual_initial_match
#print axioms actual_initial_typed
#print axioms actual_initial_canonical
#print axioms initial_binding_agreement
#print axioms recursive_validation
#print axioms literal_input_eligibility
#print axioms original_body_A
#print axioms original_body_B
#print axioms original_quantified
#print axioms reconstructed_quantified
#print axioms missing_B_query_refused

end Mettapedia.OSLF.MeTTaIL.GeneralPremise.SharedOutputControls.RecursiveValidationReverseControls


namespace Mettapedia.OSLF.MeTTaIL.GeneralPremise.SharedOutputControls.RecursiveRootReverseControls

open _root_.Mettapedia.OSLF.MeTTaIL
open _root_.Mettapedia.OSLF.MeTTaIL.Syntax Match MatchSpec ScopedRuleMatching RuleBinding GeneralFirstOrderProjection
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.Framework.GeneralCanonicalAgreement QuantifiedReference
open BareReferenceControls (petriEnvironment graphEnvironment petri_source_core graph_source_core)

set_option maxRecDepth 8000
set_option maxHeartbeats 1200000

/-- Every original literal root step at the actual declared Marking fibre
reconstructs a typed firing, including its authored concrete rest. -/
theorem petri_source_complete {bound : List TypeExpr} {source target : Pattern}
    (sourceTyped : OpenPatternWellSorted petriEnvironment.language petriEnvironment.free bound (.base "Marking") source)
    (sourceStep : ReferenceStep.Step (providerRelEnv petriEnvironment.provider) Mettapedia.GSLT.LanguageDef.CollectionConsumers.petri source target) :
    ∃ index trace captured completed history,RootFiring petriEnvironment bound (.base "Marking")
      source index trace captured completed history target := by
  exact (BareReferenceControls.petri_uniform_source_iff sourceTyped).mpr sourceStep

/-- Every original literal root step at the actual declared Graph fibre
reconstructs a typed firing, including its authored concrete rest. -/
theorem graph_source_complete {bound : List TypeExpr} {source target : Pattern}
    (sourceTyped : OpenPatternWellSorted graphEnvironment.language graphEnvironment.free bound (.base "Graph") source)
    (sourceStep : ReferenceStep.Step (providerRelEnv graphEnvironment.provider) Mettapedia.GSLT.LanguageDef.CollectionConsumers.reachability source target) :
    ∃ index trace captured completed history,RootFiring graphEnvironment bound (.base "Graph")
      source index trace captured completed history target := by
  exact (BareReferenceControls.graph_uniform_source_iff sourceTyped).mpr sourceStep

/-- This actual set rule is outside the former constructor-headed inverse
profile; its literal inverse above uses the genuine Graph typing fibre. -/
theorem graph_rule_not_headed {rule : RewriteRule}
    (declared : graphEnvironment.language.rewrites[0]? = some rule) :
    ¬ ∃ label arguments,rule.left = .apply label arguments := by
  rintro ⟨label,arguments,same⟩
  have shape : rule.left = .collection .hashSet
      [.apply "Edge" [.fvar "x",.fvar "y"],.apply "Edge" [.fvar "y",.fvar "z"]] (some "rest") := by
    cbv at declared
    cases Option.some.inj declared
    rfl
  rw [shape] at same
  cases same

#print axioms petri_source_complete
#print axioms graph_source_complete
#print axioms graph_rule_not_headed

end Mettapedia.OSLF.MeTTaIL.GeneralPremise.SharedOutputControls.RecursiveRootReverseControls


namespace Mettapedia.OSLF.MeTTaIL.GeneralPremise.SharedOutputControls.RecursiveValidationReverseControls

open _root_.Mettapedia.OSLF.MeTTaIL
open _root_.Mettapedia.OSLF.MeTTaIL.Syntax Match MatchSpec ScopedRuleMatching RuleBinding GeneralFirstOrderProjection
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.Framework.GeneralCanonicalAgreement QuantifiedReference
open RecursiveReadbackControls (term atom)

/-- The independent original rule witness is the input of root
reconstruction, including its real quantified provider validations. -/
theorem original_quantified_root : ReferenceStep.StepValid (providerRelEnv provider) language source
    (.rule 0 rawInitial [witness]) (atom "A") := by
  exact (ReferenceStep.checkStep_eq_some_iff _ _ _).mp (by decide +kernel)

theorem quantified_uniform_checked : checkUniformDirectedProfile environment [term] = true := by cbv

theorem quantified_uniform_profile : UniformDirectedProfile (fun schema => Mettapedia.OSLF.MeTTaIL.Match.binderFree schema = true)
    environment [term] := UniformDirectedProfile.of_check quantified_uniform_checked

/-- The recursive collection-output/finite-quantifier consumer has uniform
coverage for all its valid source witnesses, without local output leakage. -/
theorem quantified_uniform_source_iff {bound : List TypeExpr} {source target : Pattern}
    (sourceTyped : OpenPatternWellSorted language FreeTypeContext.empty bound term source) :
    (∃ index trace captured completed history,RootFiring environment bound term source
      index trace captured completed history target) ↔
      ReferenceStep.Step (providerRelEnv provider) language source target :=
  quantified_uniform_profile.roots_iff_reference (providerRelEnv provider) (providerRelEnv_reads _)
    (by simp) sourceTyped

#print axioms quantified_uniform_checked
#print axioms quantified_uniform_profile
#print axioms quantified_uniform_source_iff

/-- Recursive output matching and finite local quantification join the actual
root firing with its original authored table and exact source conclusion. -/
theorem quantified_source_root_complete : ∃ trace captured completed history,
    RootFiring environment [] term source 0 trace captured completed history (atom "A") := by
  obtain ⟨index,trace,captured,completed,history,fired⟩ :=
    (quantified_uniform_source_iff (bound := []) (source := source) (target := atom "A")
      (checkOpenPatternWellSorted_sound (by cbv))).mpr
      ⟨_,original_quantified_root⟩
  have zero : index = 0 := by
    have selected : ∃ rule,environment.language.rewrites[index]? = some rule := by
      cases fired with
      | fire declared _ _ _ _ _ _ _ _ => exact ⟨_,declared⟩
    obtain ⟨rule,declared⟩ := selected
    have bound := (List.getElem?_eq_some_iff.mp declared).1
    change index < 1 at bound
    omega
  subst index
  exact ⟨trace,captured,completed,history,fired⟩

#print axioms original_quantified_root
#print axioms quantified_source_root_complete

end Mettapedia.OSLF.MeTTaIL.GeneralPremise.SharedOutputControls.RecursiveValidationReverseControls


namespace Mettapedia.OSLF.MeTTaIL.GeneralPremise.SharedOutputControls.RecursiveReverseControls

/-- The actual structured-input separator fails precisely the explicit
literal-input theorem condition. Source/static validity does not erase it. -/
theorem structured_input_eligibility_refused :
    ¬ Mettapedia.OSLF.Framework.GeneralCanonicalAgreement.QuantifiedReference.FirstOrderQueryInputs
      inputProvider (.relationQuery "bag-input" [inputSchema]) := by
  intro eligible
  have shape := eligible ⟨"bag-input",[.collection .hashBag term],[.input]⟩ (by cbv) 0 inputSchema rfl rfl
  cases shape

#print axioms structured_input_eligibility_refused

end Mettapedia.OSLF.MeTTaIL.GeneralPremise.SharedOutputControls.RecursiveReverseControls


namespace Mettapedia.OSLF.MeTTaIL.GeneralPremise.SharedOutputControls.CallerFibreSeparator

open _root_.Mettapedia.OSLF.MeTTaIL
open _root_.Mettapedia.OSLF.MeTTaIL.Syntax Match ScopedRuleMatching RuleBinding
open Mettapedia.GSLT.LanguageDef.WellSorted

set_option maxRecDepth 8000
set_option maxHeartbeats 1200000

def place : TypeExpr := .base "Place"
def node : TypeExpr := .base "Node"
def rule : RewriteRule where
  name := "rest-role-is-Place"
  typeContext := [("rest",.collection .hashBag place)]
  premises := []
  left := .collection .hashBag [] (some "rest")
  right := .collection .hashBag [.apply "A" []] none

def language : LanguageDef where
  name := "caller-fibre-separator"
  types := ["Place","Node"]
  terms := [{label := "A",category := "Place",params := [],syntaxPattern := []},
    {label := "N",category := "Node",params := [],syntaxPattern := []}]
  equations := []
  rewrites := [rule]

def spec := GeneralRuleBindingInference.inferredSpec rule
def provider : GeneralPremise.ProviderSnapshot := ⟨[],[],[]⟩
def environment : GeneralPremise.Environment where
  language := language
  free := FreeTypeContext.empty
  provider := provider
  specifications := [(0,spec)]

def source : Pattern := .collection .hashBag [] none
def target : Pattern := .collection .hashBag [.apply "A" []] none

theorem actual_syntax_static_and_declared_roles : language.validate = [] ∧
    admittedFor rule spec = true ∧
    GeneralPremise.rulePremisesAdmitted language provider rule spec = true ∧
    GeneralPremise.Static.checkRule language provider rule spec = true ∧
    GeneralPremise.SchemaTyping.checkSchemaType [] language (FreeTypeContext.ofList rule.typeContext) []
      rule.left (.collection .hashBag place) = true ∧
    GeneralPremise.SchemaTyping.checkSchemaType [] language (FreeTypeContext.ofList rule.typeContext) []
      rule.right (.collection .hashBag place) = true := by cbv

theorem empty_source_is_a_typed_Node_bag : OpenPatternWellSorted language FreeTypeContext.empty []
    (.collection .hashBag node) source := checkOpenPatternWellSorted_sound (by cbv)

theorem original_reference_fires : ReferenceStep.Step (Mettapedia.OSLF.Framework.GeneralCanonicalAgreement.providerRelEnv provider) language source target := by
  refine ⟨.rule 0 [("rest",source)] [],?_⟩
  exact (ReferenceStep.checkStep_eq_some_iff _ _ _).mp (by decide +kernel)

theorem target_is_not_a_Node_bag : ¬ OpenPatternWellSorted language FreeTypeContext.empty []
    (.collection .hashBag node) target := by
  intro typed
  have checked := checkOpenPatternWellSorted_complete typed
  have refused : checkOpenPatternWellSorted language FreeTypeContext.empty [] (.collection .hashBag node) target = false := by cbv
  rw [refused] at checked
  cases checked

/-- Even a genuinely typed source does not determine the declaration's
schema fibre. The retained root target must have the actual caller type. -/
theorem typed_root_firing_refused {index : Nat} {trace : List GeneralScopedMatchMachine.BagChoice}
    {captured completed : Assignment} {history : List GeneralPremise.Event} :
    ¬ GeneralPremise.RootFiring environment [] (.collection .hashBag node) source
      index trace captured completed history target := by
  intro fired
  cases fired with
  | fire _ _ _ _ _ _ _ _ targetTyped => exact target_is_not_a_Node_bag targetTyped

#print axioms actual_syntax_static_and_declared_roles
#print axioms empty_source_is_a_typed_Node_bag
#print axioms original_reference_fires
#print axioms target_is_not_a_Node_bag
#print axioms typed_root_firing_refused

end Mettapedia.OSLF.MeTTaIL.GeneralPremise.SharedOutputControls.CallerFibreSeparator


namespace Mettapedia.OSLF.MeTTaIL.GeneralPremise.SharedOutputControls.RecursiveReverseControls
open _root_.Mettapedia.OSLF.MeTTaIL
open _root_.Mettapedia.OSLF.MeTTaIL.Syntax Match RuleBinding ScopedRuleMatching
open Mettapedia.OSLF.Framework.GeneralCanonicalAgreement QuantifiedReference
open RecursiveReadbackControls (term)

/-- The real literal-input separator remains outside the checked profile. -/
theorem structured_input_uniform_profile_refused :
    checkUniformDirectedProfile inputEnvironment [term] = false := by
  cases checked : checkUniformDirectedProfile inputEnvironment [term] with
  | false => rfl
  | true =>
      have profile := UniformDirectedProfile.of_check checked
      obtain ⟨spec,row⟩ := profile.rows (type := term) (by simp)
        (show inputEnvironment.language.rewrites[0]? = some inputRule from rfl)
      exact False.elim (structured_input_eligibility_refused
        (row.inputs _ (List.mem_cons_self ..)))

#print axioms structured_input_uniform_profile_refused
end Mettapedia.OSLF.MeTTaIL.GeneralPremise.SharedOutputControls.RecursiveReverseControls

namespace Mettapedia.OSLF.MeTTaIL.GeneralPremise.SharedOutputControls.CallerFibreSeparator
open _root_.Mettapedia.OSLF.MeTTaIL
open _root_.Mettapedia.OSLF.MeTTaIL.Syntax Match RuleBinding ScopedRuleMatching
open Mettapedia.OSLF.Framework.GeneralCanonicalAgreement QuantifiedReference

/-- A genuine well-typed source at another fibre cannot make this profile
certify the untyped reference result. The original separator is retained. -/
theorem wrong_caller_uniform_profile_refused :
    checkUniformDirectedProfile environment [.collection .hashBag node] = false := by
  cases checked : checkUniformDirectedProfile environment [.collection .hashBag node] with
  | false => rfl
  | true =>
      have profile := UniformDirectedProfile.of_check checked
      obtain ⟨index,trace,captured,completed,history,fired⟩ :=
        (profile.roots_iff_reference (providerRelEnv provider) (providerRelEnv_reads _) (by simp)
          empty_source_is_a_typed_Node_bag).mpr original_reference_fires
      exact False.elim (typed_root_firing_refused fired)

#print axioms wrong_caller_uniform_profile_refused
end Mettapedia.OSLF.MeTTaIL.GeneralPremise.SharedOutputControls.CallerFibreSeparator


set_option autoImplicit false
open scoped Mettapedia.OSLF.MeTTaIL.LanguageDefDSL

namespace Mettapedia.OSLF.MeTTaIL.GeneralPremise.SharedOutputControls.GraphOriginalReference

open _root_.Mettapedia.OSLF.MeTTaIL
open _root_.Mettapedia.OSLF.MeTTaIL.Syntax
open RuleBinding ScopedRuleMatching GeneralPremise CanonicalBags
open Mettapedia.OSLF.Framework.GeneralCanonicalAgreement
open QuantifiedReference GeneralFirstOrderProjection
open Mettapedia.GSLT.LanguageDef.WellSorted

local instance : DecidableEq RecursiveCollectionHandoff.canonicalMatchingExecution.Choice :=
  inferInstanceAs (DecidableEq EquationalScopedReceipts.Event)

open Mettapedia.GSLT.LanguageDef.CollectionConsumers.Controls.Observation.GraphControls

def environment : Environment := GeneralPlanEnvironment.environment twoRoutePlan

theorem actual_four_node_profile_checked :
    checkUniformDirectedProfile environment [.base "Graph"] = true := by cbv

theorem actual_four_node_profile :
    UniformDirectedProfile (fun schema => Match.binderFree schema = true) environment [.base "Graph"] :=
  UniformDirectedProfile.of_check actual_four_node_profile_checked

theorem actual_four_node_source_core : environment.language.rewrites.map ruleCore =
    twoRouteLanguage.rewrites.map ruleCore := by cbv

/-- Every actual source witness at the Graph fibre reconstructs through the
shared recursive inverse with its own initial and final binding lookups. -/
theorem original_step_reconstructs_bindings (relEnv : Engine.RelationEnv)
    {source target : Pattern} {witness : ReferenceStep.Witness}
    (typed : OpenPatternWellSorted twoRouteLanguage FreeTypeContext.empty [] (.base "Graph") source)
    (stepped : ReferenceStep.StepValid relEnv twoRouteLanguage source witness target) :
    ∃ index initial witnesses trace captured completed history,
      witness = .rule index initial witnesses ∧
      RootFiring environment [] (.base "Graph") source index trace captured completed history target ∧
      ∃ (rule : RewriteRule) (spec : RuleBindingSpec) (referenceFinal : Match.Bindings),
        environment.language.rewrites[index]? = some rule ∧ specification? environment index = some spec ∧
        BindingAgreement rule.left.freeFvarNames captured initial ∧
        ReferenceStep.PremisesValid relEnv environment.language (ReferenceStep.captureSites rule)
          initial rule.premises witnesses referenceFinal ∧
        BindingAgreement (premisesFlow environment.language environment.provider rule spec
          rule.left.freeFvarNames rule.premises).available completed referenceFinal := by
  have compiled := reference_step_same_core actual_four_node_source_core.symm relEnv stepped
  have sourceTyped : OpenPatternWellSorted environment.language environment.free [] (.base "Graph") source :=
    (GeneralPlanEnvironment.typing_iff twoRoutePlan [] (.base "Graph") source).mpr typed
  have reads : ReadsProvider relEnv environment.provider := ReadsProvider.empty relEnv
  exact directed_root_fromReference_recursive_with_bindings relEnv reads actual_four_node_profile.valid
    actual_four_node_profile.choices actual_four_node_profile.providerClosed
    (actual_four_node_profile.step_eligible (by simp) compiled) sourceTyped compiled

/-- The existing graph identity read directly on a source witness's bindings.
Only the actual transitive source row can license this key. -/
def referenceLogicalKey (index : Nat) (bindings : Match.Bindings) : LogicalKey EquationalScopedReceipts.Event :=
  ⟨index, 0, ⟨[], [], .base "Graph", []⟩,
    (bindings.lookup "x").map (fun body => canonValue (localValue [] body)),
    (bindings.lookup "y").map (fun body => canonValue (localValue [] body)),
    (bindings.lookup "z").map (fun body => canonValue (localValue [] body)), []⟩

private theorem root_binding_lookup {names : List String} {captured : Assignment} {bindings : Match.Bindings}
    (roots : RootValues 0 captured) (agreement : BindingAgreement names captured bindings) (captureName : String) :
    (ScopedRuleMatching.lookup (canonAssignment captured) captureName).map canonValue =
      (bindings.lookup captureName).map (fun body => canonValue (localValue [] body)) := by
  rw [lookup_canonAssignment]
  cases found : ScopedRuleMatching.lookup captured captureName with
  | none =>
    have absent : bindings.lookup captureName = none := by
      simpa only [found, Option.map_none] using (agreement.lookups captureName).symm
    simp only [Option.map_none, absent]
  | some value =>
    have metadata := roots captureName value found
    have read := agreement.lookups captureName
    simp only [found, Option.map_some] at read
    rw [← read]
    simp only [Option.map_some]
    apply congrArg some
    rcases value with ⟨dependencies, ambient, body⟩
    rcases metadata with ⟨dependenciesEq, ambientEq, _⟩
    dsimp only at dependenciesEq ambientEq
    cases dependenciesEq
    cases ambientEq
    simp only [canonValue, localValue, List.length_nil, canon_idempotent]

def graphRootJob (source : Pattern) : GeneralRuleJobs.Job :=
  ⟨0, twoRoutePlan.rules[0]'(by cbv), GeneralTypedSites.SiteData.here [] (.base "Graph") source⟩

theorem graphRootJob_valid {source : Pattern}
    (typed : OpenPatternWellSorted twoRouteLanguage FreeTypeContext.empty [] (.base "Graph") source) :
    (graphRootJob source).Valid twoRoutePlan [] (.base "Graph") source := by
  have compiled := (GeneralPlanEnvironment.typing_iff twoRoutePlan [] (.base "Graph") source).mpr typed
  refine ⟨by cbv; exact .head _, .here (by rfl) typed.2.2.1 compiled.1⟩

def graphRootReceipt {Choice : Type} (source : Pattern) (trace : List Choice)
    (captured completed : Assignment) (history : List (Event Choice)) (target : Pattern) :
    GeneralRuleJobs.Receipt Choice :=
  ⟨graphRootJob source, trace, captured, completed, history, target, target⟩

/-- A reconstructed root enters the actual rule-job receipt family. Target
and capture checks come from that root, not a completed-outcome field. -/
theorem graphRootReceipt_validIn {Choice : Type} {meaning : MatchingInterpretation Choice}
    {source target : Pattern} {trace : List Choice} {captured completed : Assignment} {history : List (Event Choice)}
    (fired : Interpreted.RootFiring meaning environment [] (.base "Graph") source 0 trace
      captured completed history target) :
    (graphRootReceipt source trace captured completed history target).ValidInWith meaning DynamicProvider.empty
      twoRoutePlan [] (.base "Graph") source := by
  have sourceSorted : OpenPatternWellSorted environment.language environment.free [] (.base "Graph") source := by
    cases fired with
    | fire _ _ _ sorted _ _ _ _ _ => exact sorted
  have targetSorted : OpenPatternWellSorted environment.language environment.free [] (.base "Graph") target := by
    cases fired with
    | fire _ _ _ _ _ _ _ _ sorted => exact sorted
  refine ⟨graphRootJob_valid ((GeneralPlanEnvironment.typing_iff twoRoutePlan [] (.base "Graph") source).mp sourceSorted),
    ?_, rfl, rfl, ?_⟩
  · simpa only [graphRootReceipt, graphRootJob, GeneralTypedSites.SiteData.here,
      GeneralPlanEnvironment.environmentWith_empty, environment] using fired
  · simpa only [graphRootReceipt, environment, GeneralPlanEnvironment.environmentWith_empty,
      GeneralPlanEnvironment.environment] using targetSorted

/-- The source binding key is exactly the already-declared receipt key after
canonical capture normalization; no second derivation identity is selected. -/
theorem graphRootReceipt_key {source target : Pattern} {names : List String} {captured : Assignment}
    {bindings : Match.Bindings} (trace : List EquationalScopedReceipts.Event)
    (roots : RootValues 0 captured) (agreement : BindingAgreement names captured bindings) :
    sourceLogicalKey (graphRootReceipt source trace (canonAssignment captured) (canonAssignment captured) [] target) =
      referenceLogicalKey 0 bindings := by
  have declaration : (twoRoutePlan.rules[0]'(by cbv)).declarationIndex = 0 := by cbv
  simp only [sourceLogicalKey, graphRootReceipt, graphRootJob, logicalSiteShape,
    GeneralTypedSites.SiteData.here, referenceLogicalKey, validationHistoryReadout,
    declaration, root_binding_lookup roots agreement]

private theorem actual_rule_metadata :
    environment.language.rewrites = [actualRule] ∧ specification? environment 0 = some actualSpec ∧
      actualRule.premises = [] ∧ checkZeroDependencies actualSpec = true ∧
      CollectionRootSearch.checkBindingSpines actualSpec = true := by cbv

private theorem graph_root_properties {Choice : Type} {meaning : MatchingInterpretation Choice}
    {source target : Pattern} {index : Nat}
    {trace : List Choice} {captured completed : Assignment} {history : List (Event Choice)}
    (fired : Interpreted.RootFiring meaning environment [] (.base "Graph") source index trace captured completed history target) :
    index = 0 ∧ completed = captured ∧ history = [] ∧ RootValues 0 captured := by
  obtain ⟨rows, actualSpecified, empty, zero, _⟩ := actual_rule_metadata
  cases fired with
  | @fire _ _ _ _ index rule spec trace captured completed history declared specified
      admitted sorted matched captureTyped premises reduced targetTyped =>
    have position := declared
    rw [rows] at position
    cases index with
    | succ index => simp only [List.getElem?_cons_succ, List.getElem?_nil] at position; cases position
    | zero =>
      have sameRule : rule = actualRule := Option.some.inj position.symm
      cases sameRule
      have sameSpec : spec = actualSpec := Option.some.inj (specified.symm.trans actualSpecified)
      cases sameSpec
      rw [empty] at premises
      cases premises
      exact ⟨rfl, rfl, rfl, captureTyped.rootValues zero⟩

/-- An actual literal root supplies a real canonical match and a reduct
transported through the existing instantiation law. Its EqEvent trace is
subsequently consumed unchanged by canonical publication coverage. -/
theorem ordinary_root_canonical_receipt {source target : Pattern}
    {trace : List GeneralScopedMatchMachine.BagChoice} {captured : Assignment}
    (fired : RootFiring environment [] (.base "Graph") source 0 trace captured captured [] target) :
    ∃ (canonicalTrace : List EquationalScopedReceipts.Event) (canonicalTarget : Pattern),
      (graphRootReceipt source canonicalTrace (canonAssignment captured) (canonAssignment captured) [] canonicalTarget).ValidInWith
        RecursiveCollectionHandoff.canonicalMatchingInterpretation DynamicProvider.empty
        twoRoutePlan [] (.base "Graph") source ∧ Same target canonicalTarget := by
  obtain ⟨rows, actualSpecified, empty, _, spines⟩ := actual_rule_metadata
  cases fired with
  | @fire _ _ _ _ _ rule spec _ _ _ _ declared specified admitted sourceSorted matched captureTyped
      premises reduced targetSorted =>
    have declaredActual : environment.language.rewrites[0]? = some actualRule := by rw [rows]; rfl
    have sameRule : rule = actualRule := Option.some.inj (declared.symm.trans declaredActual)
    cases sameRule
    have sameSpec : spec = actualSpec := Option.some.inj (specified.symm.trans actualSpecified)
    cases sameSpec
    have increasing : IncreasingSpines actualRule actualSpec := CollectionRootSearch.checkBindingSpines_sound spines
    have normalized := EquationalScopedMatching.ordinary_canonical increasing matched.matching
    obtain ⟨canonicalTrace, traced⟩ := EquationalScopedReceipts.Meaning.traced normalized
    have canonicalMatched : RecursiveCollectionHandoff.canonicalMatchingInterpretation.Matches
        ⟨actualRule, actualSpec, 0, .left, [], 0, [], actualRule.left, source⟩ canonicalTrace
        (canonAssignment captured) := by
      change EquationalScopedReceipts.Matches literalBodyComparison actualRule actualSpec 0 .left [] 0 []
        actualRule.left (canon source) canonicalTrace (canonAssignment captured)
      simpa only [canonAssignment, List.map_nil, List.length_nil] using traced
    obtain ⟨canonicalTarget, projected, same⟩ := instantiateWith?_same actualRule actualSpec 0
      (ScopedReflectiveExecution.binderOperation environment.reflection actualRule)
      (binderOperation_same environment.reflection actualRule
        ((checkBinderLawsFor_iff [] environment.reflection actualRule).mp (by decide +kernel)))
      actualRule.right .right [] 0
      captured (canonAssignment captured) target (assignSame_canon captured) reduced
    have root : Interpreted.RootFiring RecursiveCollectionHandoff.canonicalMatchingInterpretation environment
        [] (.base "Graph") source 0 canonicalTrace (canonAssignment captured) (canonAssignment captured) [] canonicalTarget :=
      .fire declaredActual actualSpecified admitted sourceSorted canonicalMatched
        (typedAssignment_canon captureTyped) (by rw [empty]; exact .nil) projected
        (openPatternWellSorted_of_eqvGen ((same_iff _ _).mp same) targetSorted)
    exact ⟨canonicalTrace, canonicalTarget, graphRootReceipt_validIn root, same⟩

/-- Each literal original source witness determines its own canonical
receipt key through the shared binding readback. Equal conclusions do not
identify different intermediate bindings. -/
theorem original_step_canonical_key_receipt (relEnv : Engine.RelationEnv)
    {source target : Pattern} {witness : ReferenceStep.Witness}
    (typed : OpenPatternWellSorted twoRouteLanguage FreeTypeContext.empty [] (.base "Graph") source)
    (stepped : ReferenceStep.StepValid relEnv twoRouteLanguage source witness target) :
    ∃ (bindings : Match.Bindings), witness = .rule 0 bindings [] ∧
      ∃ (receipt : GeneralRuleJobs.Receipt EquationalScopedReceipts.Event),
        receipt.ValidInWith RecursiveCollectionHandoff.canonicalMatchingInterpretation DynamicProvider.empty
          twoRoutePlan [] (.base "Graph") source ∧
        sourceLogicalKey receipt = referenceLogicalKey 0 bindings ∧ Same target receipt.target := by
  obtain ⟨index, initial, witnesses, trace, captured, completed, history, witnessed, fired,
    rule, spec, referenceFinal, selected, _, captures, premises, _⟩ :=
    original_step_reconstructs_bindings relEnv typed stepped
  obtain ⟨indexEq, completedEq, historyEq, roots⟩ := graph_root_properties fired
  subst index
  subst completed
  subst history
  have declaredActual : environment.language.rewrites[0]? = some actualRule := by
    rw [actual_rule_metadata.1]; rfl
  have sameRule : rule = actualRule := Option.some.inj (selected.symm.trans declaredActual)
  cases sameRule
  rw [actual_rule_metadata.2.2.1] at premises
  cases premises
  obtain ⟨canonicalTrace, canonicalTarget, valid, same⟩ := ordinary_root_canonical_receipt fired
  refine ⟨initial, witnessed, graphRootReceipt source canonicalTrace
    (canonAssignment captured) (canonAssignment captured) [] canonicalTarget, valid, ?_, same⟩
  exact graphRootReceipt_key canonicalTrace roots captures

/-- The exact source-witness key reaches the existing joint committed
account. The packet and full EqEvent receipt are retained as the pair. -/
theorem original_step_key_eventually_published (relEnv : Engine.RelationEnv)
    {source target : Pattern} {witness : ReferenceStep.Witness}
    (typed : OpenPatternWellSorted twoRouteLanguage FreeTypeContext.empty [] (.base "Graph") source)
    (stepped : ReferenceStep.StepValid relEnv twoRouteLanguage source witness target) :
    ∃ (bindings : Match.Bindings) (work : Nat) (pair : CollectionCommittedObservation.Committed EquationalScopedReceipts.Event),
      witness = .rule 0 bindings [] ∧
      pair ∈ CollectionOccurrenceSearch.committedWith (matcher := RecursiveCollectionHandoff.canonicalMatchingExecution)
        (fun packet => packet.finishCanonical? twoRoutePlan [] (.base "Graph"))
        ((CollectionOccurrenceSearch.canonicalSearch twoRoutePlan [] (.base "Graph") 0).run source work) ∧
      logicalKey pair = referenceLogicalKey 0 bindings := by
  obtain ⟨bindings, witnessed, receipt, valid, observed, _⟩ :=
    original_step_canonical_key_receipt relEnv typed stepped
  obtain ⟨work, pair, published, key⟩ := canonical_two_route_source_key_eventually_published valid
  exact ⟨bindings, work, pair, witnessed, published, key.trans observed⟩

/-- Select the actual literal source match by its intermediate node. -/
def routeBindings (via : String) : Match.Bindings :=
  ((Match.matchPattern actualRule.left twoRouteSource).find?
    (fun bindings => bindings.lookup "y" == some (Mettapedia.GSLT.LanguageDef.CollectionConsumers.token via))).getD []

def routeTarget (via : String) : Pattern :=
  Match.applyBindingsScoped (ReferenceStep.captureSites transitiveAuthoredRule) (routeBindings via) 0
    transitiveAuthoredRule.right

private theorem original_rule_metadata :
    twoRouteLanguage.rewrites[0]? = some transitiveAuthoredRule ∧
      transitiveAuthoredRule.left = actualRule.left ∧ transitiveAuthoredRule.premises = [] := by cbv

theorem two_route_source_typed :
    OpenPatternWellSorted twoRouteLanguage FreeTypeContext.empty [] (.base "Graph") twoRouteSource :=
  checkOpenPatternWellSorted_sound (by cbv)

theorem route_match_B : routeBindings "B" ∈
    ReflectiveCanonical.matchPatternForRule twoRouteLanguage transitiveAuthoredRule twoRouteSource := by
  rw [ReflectiveCanonical.matchPatternForRule_eq_syntactic, original_rule_metadata.2.1]
  unfold routeBindings
  rw [actual_left]
  cbv
  exact .head _

theorem route_match_C : routeBindings "C" ∈
    ReflectiveCanonical.matchPatternForRule twoRouteLanguage transitiveAuthoredRule twoRouteSource := by
  rw [ReflectiveCanonical.matchPatternForRule_eq_syntactic, original_rule_metadata.2.1]
  unfold routeBindings
  rw [actual_left]
  cbv
  exact .tail _ (.head _)

theorem route_step_B (relEnv : Engine.RelationEnv) :
    ReferenceStep.StepValid relEnv twoRouteLanguage twoRouteSource
      (.rule 0 (routeBindings "B") []) (routeTarget "B") := by
  apply ReferenceStep.StepValid.rule original_rule_metadata.1 route_match_B
  rw [original_rule_metadata.2.2]
  exact .nil _

theorem route_step_C (relEnv : Engine.RelationEnv) :
    ReferenceStep.StepValid relEnv twoRouteLanguage twoRouteSource
      (.rule 0 (routeBindings "C") []) (routeTarget "C") := by
  apply ReferenceStep.StepValid.rule original_rule_metadata.1 route_match_C
  rw [original_rule_metadata.2.2]
  exact .nil _

theorem source_routes_distinct : referenceLogicalKey 0 (routeBindings "B") ≠
    referenceLogicalKey 0 (routeBindings "C") := by
  intro same
  have intermediate := congrArg LogicalKey.intermediate same
  unfold referenceLogicalKey routeBindings at intermediate
  rw [actual_left] at intermediate
  cbv at intermediate
  simp at intermediate

theorem source_routes_same_fact :
    logicalEdge? (referenceLogicalKey 0 (routeBindings "B")) = some (Mettapedia.GSLT.LanguageDef.CollectionConsumers.edge "A" "D") ∧
    logicalEdge? (referenceLogicalKey 0 (routeBindings "C")) = some (Mettapedia.GSLT.LanguageDef.CollectionConsumers.edge "A" "D") := by
  unfold referenceLogicalKey routeBindings
  rw [actual_left]
  cbv

/-- No literal transitive match in the actual source uses D as its
intermediate. The fallback is not accepted as an original rule witness. -/
theorem absent_route_refused : routeBindings "D" ∉
    ReflectiveCanonical.matchPatternForRule twoRouteLanguage transitiveAuthoredRule twoRouteSource := by
  rw [ReflectiveCanonical.matchPatternForRule_eq_syntactic, original_rule_metadata.2.1]
  unfold routeBindings
  rw [actual_left]
  cbv
  intro impossible
  cases impossible with
  | tail _ later =>
    cases later with
    | tail _ absent => cases absent

theorem wrong_conclusion_refused (relEnv : Engine.RelationEnv) :
    ¬ ReferenceStep.StepValid relEnv twoRouteLanguage twoRouteSource
      (.rule 0 (routeBindings "B") []) twoRouteSource := by
  intro stepped
  have valid := (ReferenceStep.checkStep_eq_some_iff relEnv twoRouteLanguage _).mpr (route_step_B relEnv)
  have invalid := (ReferenceStep.checkStep_eq_some_iff relEnv twoRouteLanguage _).mpr stepped
  have equal : routeTarget "B" = twoRouteSource := Option.some.inj (valid.symm.trans invalid)
  unfold routeTarget routeBindings at equal
  rw [actual_left] at equal
  cbv at equal
  simp at equal

/-- At any reached node of a settled graph, every actual literal source
witness at an equivalent presentation contributes its own binding key.
Settlement is inherited from the proved finite-carrier and local-drainage
result; it is not inferred from this key projection. -/
theorem original_rule_key_at_settled_node (relEnv : Engine.RelationEnv)
    (source : Pattern) (work : Nat)
    (done : Complete.Settled.settled (CollectionOccurrenceSearch.canonicalSearch twoRoutePlan [] (.base "Graph") 0)
      (Complete.Explore.explore (CollectionOccurrenceSearch.canonicalSearch twoRoutePlan [] (.base "Graph") 0)
        source work) = true)
    (node : Complete.Explore.Node Pattern
      (CollectionOccurrenceSearch.Run twoRoutePlan [] (.base "Graph") RecursiveCollectionHandoff.canonicalMatchingExecution)
      (GeneralRuleJobs.Receipt EquationalScopedReceipts.Event))
    (reached : node ∈ (Complete.Explore.explore
      (CollectionOccurrenceSearch.canonicalSearch twoRoutePlan [] (.base "Graph") 0) source work).nodes)
    {representative target : Pattern} {bindings : Match.Bindings}
    (same : Same node.state representative)
    (typed : OpenPatternWellSorted twoRouteLanguage FreeTypeContext.empty [] (.base "Graph") representative)
    (stepped : ReferenceStep.StepValid relEnv twoRouteLanguage representative (.rule 0 bindings []) target) :
    referenceLogicalKey 0 bindings ∈ CollectionCommittedObservation.committedKeys logicalKey
      ((Complete.Explore.explore (CollectionOccurrenceSearch.canonicalSearch twoRoutePlan [] (.base "Graph") 0)
        source work).nodes.flatMap (fun reached => CollectionOccurrenceSearch.committedWith
          (matcher := RecursiveCollectionHandoff.canonicalMatchingExecution)
          (fun packet => packet.finishCanonical? twoRoutePlan [] (.base "Graph")) reached.run)) := by
  obtain ⟨recovered, witnessed, receipt, valid, observed, _⟩ :=
    original_step_canonical_key_receipt relEnv typed stepped
  have bindingsRead : bindings = recovered := (ReferenceStep.Witness.rule.inj witnessed).2.1
  have account := canonical_two_route_settled_source_key_basis source work done node reached representative same receipt valid
  rw [observed, ← bindingsRead] at account
  exact account

/-- Both independently authored transitive inferences are present together
in one settled full-packet account. Their keys are distinct and both read
out as the same inferred edge. This is a one-step key-basis statement. -/
theorem actual_two_routes_completed_keys (relEnv : Engine.RelationEnv) :
    ∃ work, Complete.Settled.settled (CollectionOccurrenceSearch.canonicalSearch twoRoutePlan [] (.base "Graph") 0)
      (Complete.Explore.explore (CollectionOccurrenceSearch.canonicalSearch twoRoutePlan [] (.base "Graph") 0)
        twoRouteSource work) = true ∧
      let account := (Complete.Explore.explore
        (CollectionOccurrenceSearch.canonicalSearch twoRoutePlan [] (.base "Graph") 0) twoRouteSource work).nodes.flatMap
        (fun reached => CollectionOccurrenceSearch.committedWith
          (matcher := RecursiveCollectionHandoff.canonicalMatchingExecution)
          (fun packet => packet.finishCanonical? twoRoutePlan [] (.base "Graph")) reached.run)
      referenceLogicalKey 0 (routeBindings "B") ∈ CollectionCommittedObservation.committedKeys logicalKey account ∧
      referenceLogicalKey 0 (routeBindings "C") ∈ CollectionCommittedObservation.committedKeys logicalKey account ∧
      referenceLogicalKey 0 (routeBindings "B") ≠ referenceLogicalKey 0 (routeBindings "C") ∧
      logicalEdge? (referenceLogicalKey 0 (routeBindings "B")) = some (Mettapedia.GSLT.LanguageDef.CollectionConsumers.edge "A" "D") ∧
      logicalEdge? (referenceLogicalKey 0 (routeBindings "C")) = some (Mettapedia.GSLT.LanguageDef.CollectionConsumers.edge "A" "D") := by
  obtain ⟨work, done⟩ := canonical_two_route_eventually_settled twoRouteSource
  obtain ⟨node, reached, sourceRead⟩ := (Complete.Explore.explore_good
    (CollectionOccurrenceSearch.canonical_search_lawful twoRoutePlan [] (.base "Graph") 0) twoRouteSource work).source
  have same : Same node.state twoRouteSource := by rw [sourceRead]; rfl
  exact ⟨work, done,
    original_rule_key_at_settled_node relEnv twoRouteSource work done node reached same two_route_source_typed (route_step_B relEnv),
    original_rule_key_at_settled_node relEnv twoRouteSource work done node reached same two_route_source_typed (route_step_C relEnv),
    source_routes_distinct, source_routes_same_fact⟩


/-- The source equation witnesses only move presentations. They do not
supply additional logical derivations: publication is keyed by the actual
literal rule witness's preserved bindings. -/
theorem original_modulo_key_eventually_published (relEnv : Engine.RelationEnv)
    {source target : Pattern}
    (typed : OpenPatternWellSorted twoRouteLanguage FreeTypeContext.empty [] (.base "Graph") source)
    (stepped : ReferenceStep.StepModulo relEnv twoRouteLanguage source target) :
    ∃ (redex contractum : Pattern) (bindings : Match.Bindings) (work : Nat)
        (pair : CollectionCommittedObservation.Committed EquationalScopedReceipts.Event),
      ReferenceStep.Equivalent relEnv twoRouteLanguage source redex ∧
      ReferenceStep.StepValid relEnv twoRouteLanguage redex (.rule 0 bindings []) contractum ∧
      ReferenceStep.Equivalent relEnv twoRouteLanguage contractum target ∧
      pair ∈ CollectionOccurrenceSearch.committedWith (matcher := RecursiveCollectionHandoff.canonicalMatchingExecution)
        (fun packet => packet.finishCanonical? twoRoutePlan [] (.base "Graph"))
        ((CollectionOccurrenceSearch.canonicalSearch twoRoutePlan [] (.base "Graph") 0).run source work) ∧
      logicalKey pair = referenceLogicalKey 0 bindings := by
  obtain ⟨redex, contractum, initial, ⟨witness, literal⟩, final⟩ := stepped
  have noEquations : twoRouteLanguage.equations = [] := by cbv
  have noAlgebra : twoRouteLanguage.hasAlgebraDeclarations = false := by cbv
  have same := ReferenceStep.equivalent_same noEquations noAlgebra initial
  have redexTyped := ReferenceStep.equivalent_openPatternWellSorted noEquations noAlgebra initial typed
  obtain ⟨bindings, work, pair, witnessed, published, key⟩ :=
    original_step_key_eventually_published relEnv redexTyped literal
  rw [witnessed] at literal
  have presentations := CollectionOccurrenceSearch.canonical_committed_run_same
    twoRoutePlan [] (.base "Graph") 0 redex source work same.symm
  rw [presentations] at published
  exact ⟨redex, contractum, bindings, work, pair, initial, literal, final, published, key⟩

#print axioms original_rule_key_at_settled_node
#print axioms actual_two_routes_completed_keys
#print axioms original_step_key_eventually_published
#print axioms two_route_source_typed
#print axioms route_match_B
#print axioms route_match_C
#print axioms route_step_B
#print axioms route_step_C
#print axioms source_routes_distinct
#print axioms source_routes_same_fact
#print axioms absent_route_refused
#print axioms wrong_conclusion_refused
#print axioms actual_four_node_profile_checked
#print axioms actual_four_node_profile
#print axioms actual_four_node_source_core
#print axioms original_step_reconstructs_bindings
#print axioms graphRootJob_valid
#print axioms graphRootReceipt_validIn
#print axioms graphRootReceipt_key
#print axioms original_step_canonical_key_receipt
#print axioms ordinary_root_canonical_receipt
#print axioms original_modulo_key_eventually_published


private theorem root_binding_lookup_raw {names : List String} {captured : Assignment} {bindings : Match.Bindings}
    (roots : RootValues 0 captured) (agreement : BindingAgreement names captured bindings) (captureName : String) :
    (ScopedRuleMatching.lookup captured captureName).map canonValue =
      (bindings.lookup captureName).map (fun body => canonValue (localValue [] body)) := by
  cases found : ScopedRuleMatching.lookup captured captureName with
  | none =>
    have absent : bindings.lookup captureName = none := by
      simpa only [found, Option.map_none] using (agreement.lookups captureName).symm
    simp only [Option.map_none, absent]
  | some value =>
    have metadata := roots captureName value found
    have read := agreement.lookups captureName
    simp only [found, Option.map_some] at read
    rw [← read]
    simp only [Option.map_some]
    apply congrArg some
    rcases value with ⟨dependencies, ambient, body⟩
    rcases metadata with ⟨dependenciesEq, ambientEq, _⟩
    dsimp only at dependenciesEq ambientEq
    cases dependenciesEq
    cases ambientEq
    rfl

private theorem graph_job_exact {source : Pattern} {job : GeneralRuleJobs.Job}
    (valid : job.Valid twoRoutePlan [] (.base "Graph") source) : job = graphRootJob source := by
  let actualDeclaration := twoRoutePlan.rules[0]'(by cbv)
  have rows : twoRoutePlan.rules = [actualDeclaration] := by
    dsimp only [actualDeclaration]
    cbv
  have position : job.ordinal = 0 ∧ job.declaration = actualDeclaration := by
    have member := valid.1
    rw [rows] at member
    change (job.declaration, job.ordinal) ∈ [(actualDeclaration, 0)] at member
    have fields := Prod.mk.inj (List.mem_singleton.mp member)
    exact ⟨fields.2, fields.1⟩
  have generated := GeneralTypedSites.generate_complete valid.2
  have permissions : twoRoutePlan.permissions.sites = .rootOnly := rfl
  rw [permissions, GeneralTypedSites.generate_rootOnly] at generated
  have site : job.site = GeneralTypedSites.SiteData.here [] (.base "Graph") source := by
    split at generated
    · exact List.mem_singleton.mp generated
    · cases generated
  rcases job with ⟨ordinal, declaration, focus⟩
  dsimp only at position site
  rcases position with ⟨rfl, rfl⟩
  cases site
  rfl

/-- The actual canonical root determines a literal original-language
witness with the same captured binding key, including its intermediate. -/
theorem canonical_root_original_key (relEnv : Engine.RelationEnv)
    {source target : Pattern} {trace : List EquationalScopedReceipts.Event} {captured : Assignment}
    (fired : Interpreted.RootFiring RecursiveCollectionHandoff.canonicalMatchingInterpretation environment
      [] (.base "Graph") source 0 trace captured captured [] target) :
    ∃ (redex : Pattern) (bindings : Match.Bindings),
      ReferenceStep.Equivalent relEnv twoRouteLanguage source redex ∧
      OpenPatternWellSorted twoRouteLanguage FreeTypeContext.empty [] (.base "Graph") redex ∧
      ReferenceStep.StepValid relEnv twoRouteLanguage redex (.rule 0 bindings []) target ∧
      sourceLogicalKey (graphRootReceipt source trace captured captured [] target) = referenceLogicalKey 0 bindings := by
  obtain ⟨rows, actualSpecified, _, zero, _⟩ := actual_rule_metadata
  cases fired with
  | @fire _ _ _ _ _ rule spec _ _ _ _ declared specified admitted sourceSorted matched captureTyped
      premises reduced targetSorted =>
    have declaredActual : environment.language.rewrites[0]? = some actualRule := by rw [rows]; rfl
    have sameRule : rule = actualRule := Option.some.inj (declared.symm.trans declaredActual)
    cases sameRule
    have sameSpec : spec = actualSpec := Option.some.inj (specified.symm.trans actualSpecified)
    cases sameSpec
    have roots := captureTyped.rootValues zero
    obtain ⟨redex, bindings, same, step, agreement⟩ := canonical_transitive_primitive_reference_with_bindings
      relEnv twoRouteLanguage _ original_rule_metadata.1 original_rule_metadata.2.1
      (by cbv : transitiveAuthoredRule.right = actualRule.right) original_rule_metadata.2.2 matched roots reduced
    have typed : OpenPatternWellSorted twoRouteLanguage FreeTypeContext.empty [] (.base "Graph") source :=
      (GeneralPlanEnvironment.typing_iff twoRoutePlan [] (.base "Graph") source).mp sourceSorted
    refine ⟨redex, bindings, typed_graph_same_reference_equivalent relEnv twoRouteLanguage
      (fun _ member => member) typed same,
      openPatternWellSorted_of_eqvGen ((same_iff _ _).mp same) typed, step, ?_⟩
    have declaration : (twoRoutePlan.rules[0]'(by cbv)).declarationIndex = 0 := by cbv
    simp only [sourceLogicalKey, graphRootReceipt, graphRootJob, logicalSiteShape,
      GeneralTypedSites.SiteData.here, referenceLogicalKey, validationHistoryReadout,
      declaration, root_binding_lookup_raw roots agreement]

/-- Every valid actual canonical receipt has an original source witness
with exactly its declared graph key. Its full trace and packet remain
available independently of this logical identity projection. -/
theorem canonical_receipt_original_key (relEnv : Engine.RelationEnv) {source : Pattern}
    {receipt : GeneralRuleJobs.Receipt EquationalScopedReceipts.Event}
    (valid : receipt.ValidInWith RecursiveCollectionHandoff.canonicalMatchingInterpretation DynamicProvider.empty
      twoRoutePlan [] (.base "Graph") source) :
    ∃ (redex : Pattern) (bindings : Match.Bindings),
      ReferenceStep.Equivalent relEnv twoRouteLanguage source redex ∧
      OpenPatternWellSorted twoRouteLanguage FreeTypeContext.empty [] (.base "Graph") redex ∧
      ReferenceStep.StepValid relEnv twoRouteLanguage redex (.rule 0 bindings []) receipt.target ∧
      sourceLogicalKey receipt = referenceLogicalKey 0 bindings := by
  have jobRead := graph_job_exact valid.1
  have root : Interpreted.RootFiring RecursiveCollectionHandoff.canonicalMatchingInterpretation environment
      [] (.base "Graph") source 0 receipt.matcherTrace receipt.captured receipt.completed receipt.premiseHistory
      receipt.localTarget := by
    simpa only [jobRead, graphRootJob, GeneralTypedSites.SiteData.here,
      GeneralPlanEnvironment.environmentWith_empty, environment] using valid.2.1
  have targetRead : receipt.target = receipt.localTarget := by
    simpa only [jobRead, graphRootJob, GeneralTypedSites.SiteData.here, DerivedContexts.OneHoleContext.fill]
      using valid.2.2.2.1
  obtain ⟨_, completedRead, historyRead, _⟩ := graph_root_properties root
  rw [completedRead, historyRead] at root
  obtain ⟨redex, bindings, equivalent, typed, step, key⟩ := canonical_root_original_key relEnv root
  refine ⟨redex, bindings, equivalent, typed, ?_, ?_⟩
  · simpa only [targetRead] using step
  · simpa only [sourceLogicalKey, graphRootReceipt, jobRead, completedRead, historyRead] using key

#print axioms canonical_root_original_key
#print axioms canonical_receipt_original_key

/-- Settlement completes the declared one-step source-witness key basis
on the actual typed graph domain. It does not complete unfolded proof
histories or identify them with graph paths. -/
theorem canonical_settled_original_key_iff (relEnv : Engine.RelationEnv)
    (source : Pattern) (work : Nat)
    (done : Complete.Settled.settled (CollectionOccurrenceSearch.canonicalSearch twoRoutePlan [] (.base "Graph") 0)
      (Complete.Explore.explore (CollectionOccurrenceSearch.canonicalSearch twoRoutePlan [] (.base "Graph") 0)
        source work) = true) (key : LogicalKey EquationalScopedReceipts.Event) :
    key ∈ CollectionCommittedObservation.committedKeys logicalKey
      ((Complete.Explore.explore (CollectionOccurrenceSearch.canonicalSearch twoRoutePlan [] (.base "Graph") 0)
        source work).nodes.flatMap (fun reached => CollectionOccurrenceSearch.committedWith
          (matcher := RecursiveCollectionHandoff.canonicalMatchingExecution)
          (fun packet => packet.finishCanonical? twoRoutePlan [] (.base "Graph")) reached.run)) ↔
      ∃ node ∈ (Complete.Explore.explore
        (CollectionOccurrenceSearch.canonicalSearch twoRoutePlan [] (.base "Graph") 0) source work).nodes,
        ∃ (redex target : Pattern) (bindings : Match.Bindings),
          ReferenceStep.Equivalent relEnv twoRouteLanguage node.state redex ∧
          OpenPatternWellSorted twoRouteLanguage FreeTypeContext.empty [] (.base "Graph") redex ∧
          ReferenceStep.StepValid relEnv twoRouteLanguage redex (.rule 0 bindings []) target ∧
          referenceLogicalKey 0 bindings = key := by
  constructor
  · intro observed
    obtain ⟨node, reached, representative, same, receipt, valid, readKey⟩ :=
      canonical_two_route_observed_key_source source work observed
    obtain ⟨redex, bindings, equation, typed, step, keyRead⟩ := canonical_receipt_original_key relEnv valid
    have representativeTyped := canonical_two_route_receipt_source_typed valid
    have toNode := typed_graph_same_reference_equivalent relEnv twoRouteLanguage
      (fun _ member => member) representativeTyped same.symm
    exact ⟨node, reached, redex, receipt.target, bindings,
      Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ toNode) equation,
      typed, step, keyRead.symm.trans readKey⟩
  · rintro ⟨node, reached, redex, target, bindings, equation, typed, step, rfl⟩
    have noEquations : twoRouteLanguage.equations = [] := by cbv
    have noAlgebra : twoRouteLanguage.hasAlgebraDeclarations = false := by cbv
    exact original_rule_key_at_settled_node relEnv source work done node reached
      (ReferenceStep.equivalent_same noEquations noAlgebra equation) typed step

/-- The finite carrier and earned local drainage provide a settled graph;
the source-witness correspondence then certifies its exact declared key
basis independently of any unfolded-history completion policy. -/
theorem canonical_eventually_exact_original_key_basis (relEnv : Engine.RelationEnv) (source : Pattern) :
    ∃ work, Complete.Settled.settled (CollectionOccurrenceSearch.canonicalSearch twoRoutePlan [] (.base "Graph") 0)
      (Complete.Explore.explore (CollectionOccurrenceSearch.canonicalSearch twoRoutePlan [] (.base "Graph") 0)
        source work) = true ∧
      ∀ key : LogicalKey EquationalScopedReceipts.Event,
        key ∈ CollectionCommittedObservation.committedKeys logicalKey
          ((Complete.Explore.explore (CollectionOccurrenceSearch.canonicalSearch twoRoutePlan [] (.base "Graph") 0)
            source work).nodes.flatMap (fun reached => CollectionOccurrenceSearch.committedWith
              (matcher := RecursiveCollectionHandoff.canonicalMatchingExecution)
              (fun packet => packet.finishCanonical? twoRoutePlan [] (.base "Graph")) reached.run)) ↔
          ∃ node ∈ (Complete.Explore.explore
            (CollectionOccurrenceSearch.canonicalSearch twoRoutePlan [] (.base "Graph") 0) source work).nodes,
            ∃ (redex target : Pattern) (bindings : Match.Bindings),
              ReferenceStep.Equivalent relEnv twoRouteLanguage node.state redex ∧
              OpenPatternWellSorted twoRouteLanguage FreeTypeContext.empty [] (.base "Graph") redex ∧
              ReferenceStep.StepValid relEnv twoRouteLanguage redex (.rule 0 bindings []) target ∧
              referenceLogicalKey 0 bindings = key := by
  obtain ⟨work, done⟩ := canonical_two_route_eventually_settled source
  exact ⟨work, done, canonical_settled_original_key_iff relEnv source work done⟩

#print axioms canonical_settled_original_key_iff
#print axioms canonical_eventually_exact_original_key_basis

/-- The fact-set observation forgets logical-key multiplicity while
retaining a genuine typed original source witness for every conclusion. -/
theorem canonical_settled_original_fact_iff (relEnv : Engine.RelationEnv)
    (source : Pattern) (work : Nat)
    (done : Complete.Settled.settled (CollectionOccurrenceSearch.canonicalSearch twoRoutePlan [] (.base "Graph") 0)
      (Complete.Explore.explore (CollectionOccurrenceSearch.canonicalSearch twoRoutePlan [] (.base "Graph") 0)
        source work) = true) (fact : Pattern) :
    fact ∈ ((CollectionCommittedObservation.committedKeys logicalKey
      ((Complete.Explore.explore (CollectionOccurrenceSearch.canonicalSearch twoRoutePlan [] (.base "Graph") 0)
        source work).nodes.flatMap (fun node => CollectionOccurrenceSearch.committedWith
          (matcher := RecursiveCollectionHandoff.canonicalMatchingExecution)
          (fun packet => packet.finishCanonical? twoRoutePlan [] (.base "Graph")) node.run))).val.filterMap
            logicalEdge?).toFinset ↔
      ∃ node ∈ (Complete.Explore.explore
        (CollectionOccurrenceSearch.canonicalSearch twoRoutePlan [] (.base "Graph") 0) source work).nodes,
        ∃ (redex target : Pattern) (bindings : Match.Bindings),
          ReferenceStep.Equivalent relEnv twoRouteLanguage node.state redex ∧
          OpenPatternWellSorted twoRouteLanguage FreeTypeContext.empty [] (.base "Graph") redex ∧
          ReferenceStep.StepValid relEnv twoRouteLanguage redex (.rule 0 bindings []) target ∧
          logicalEdge? (referenceLogicalKey 0 bindings) = some fact := by
  simp only [Multiset.mem_toFinset, Multiset.mem_filterMap, Finset.mem_val]
  constructor
  · rintro ⟨key, observed, read⟩
    obtain ⟨node, reached, redex, target, bindings, equation, typed, step, keyed⟩ :=
      (canonical_settled_original_key_iff relEnv source work done key).mp observed
    have sameRead : logicalEdge? (referenceLogicalKey 0 bindings) = logicalEdge? key :=
      congrArg (fun actualKey : LogicalKey EquationalScopedReceipts.Event => logicalEdge? actualKey) keyed
    exact ⟨node, reached, redex, target, bindings, equation, typed, step, sameRead.trans read⟩
  · rintro ⟨node, reached, redex, target, bindings, equation, typed, step, read⟩
    exact ⟨referenceLogicalKey 0 bindings,
      (canonical_settled_original_key_iff relEnv source work done (referenceLogicalKey 0 bindings)).mpr
        ⟨node, reached, redex, target, bindings, equation, typed, step, rfl⟩, read⟩

#print axioms canonical_settled_original_fact_iff

end Mettapedia.OSLF.MeTTaIL.GeneralPremise.SharedOutputControls.GraphOriginalReference
